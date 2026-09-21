#!/usr/bin/env python3
"""Run the Connect, Patient Read and cancellation tests against a seeded THP box.

Standalone Python 3.10+ runner; no pip packages or previous reports required.
Run from any directory: python3 /path/to/isik-testsuite/scripts/run_thp_tests.py
Exit codes: 0 = passed, 1 = test failures/errors, 2 = setup/build/cleanup failure,
130 = interrupted. Each invocation retains its own reports under .test-reports/thp.
"""

import argparse
import base64
from collections import Counter
from datetime import datetime, timezone
import hashlib
import html
import json
import os
from pathlib import Path
import re
import secrets
import shutil
import signal
import subprocess
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
import uuid
import xml.etree.ElementTree as ET

PROJECT = Path(__file__).resolve().parents[1]
SELECTIONS = {
    "connect": "@Stufe5 and @Connect",
    "patient-read": "@Stufe5 and @Basis and @Patient-Read",
    "cancellation": "@Stufe5 and @Basis and (@Patient-Update-Cancellation or @Patient-Delete-Cancellation)",
}
READ_SCOPES = {
    "patient": [("patient/Patient.rs", "read-patient-scope-allowed"),
                ("patient/*.rs", "read-patient-wildcard-scope-allowed")],
    "user": [("user/Patient.rs", "read-patient-scope-in-user-context-allowed"),
             ("user/*.rs", "read-patient-wildcard-scope-in-user-context-allowed")],
    "system": [("system/Patient.rs", "read-patient-scope-in-system-context-allowed"),
               ("system/*.rs", "read-wildcard-scope-in-system-context-allowed")],
}
REPORT_PATHS = ("site/serenity", "failsafe-reports", "surefire-reports",
                "test-report.zip", "debug-report.zip")


def say(message):
    print(message, flush=True)


def save(path, value):
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


class ApiError(RuntimeError):
    def __init__(self, method, url, status):
        self.status = status
        super().__init__(f"{method} {url}: HTTP {status}")


def request(method, url, *, token=None, data=None, form=None):
    headers = {"Accept": "application/json"}
    body = None
    if token:
        headers["Authorization"] = "Bearer " + token
    if data is not None:
        body = json.dumps(data).encode()
        headers.update({"Content-Type": "application/json", "Prefer": "return=representation"})
    if form is not None:
        body = urllib.parse.urlencode(form).encode()
        headers["Content-Type"] = "application/x-www-form-urlencoded"
    try:
        with urllib.request.urlopen(urllib.request.Request(
            url, data=body, headers=headers, method=method
        ), timeout=20) as response:
            content = response.read()
            return json.loads(content) if content else None
    except urllib.error.HTTPError as error:
        # HTTP bodies and headers can contain credentials; never echo them.
        raise ApiError(method, url, error.code) from None
    except urllib.error.URLError as error:
        raise RuntimeError(f"{method} {url}: {error.reason}") from None


def token_claims(token):
    """Inspect issued claims to catch accidentally overprivileged test tokens."""
    try:
        return json.loads(base64.urlsafe_b64decode(token.split(".")[1] + "==="))
    except (ValueError, IndexError) as error:
        raise RuntimeError("Keycloak did not return a readable JWT access token") from error


def validate_scope(token, kind, scope, context):
    claims = token_claims(token)
    expected = {scope, "launch/" + kind}
    if set(claims.get("scope", "").split()) != expected:
        raise RuntimeError(f"Unexpected scopes for {kind} token; expected {sorted(expected)}")
    for name, value in context.items():
        if claims.get(name) != value:
            raise RuntimeError(f"Unexpected {name} claim in {kind} token")
    forbidden = {"patient", "fhirUser"} - context.keys()
    if any(claims.get(name) for name in forbidden):
        raise RuntimeError(f"Mixed launch contexts in {kind} token")


def reference(value, resource_types):
    path = urllib.parse.urlsplit(value).path.rstrip("/")
    pattern = r"(?:^|/)(" + "|".join(resource_types) + r")/([A-Za-z0-9.-]+)(?:/_history/[^/]+)?$"
    match = re.search(pattern, path)
    if not match or match[2] == "UNLINKED":
        raise RuntimeError(f"Seeded user has an invalid FHIR link: {value!r}; run THP's fhir-init first")
    return match[1] + "/" + match[2]


class Thp:
    def __init__(self, args, work):
        self.args, self.work = args, work
        self.fhir_url = args.base_url.rstrip("/") + "/fhir"
        self.auth_url = (args.keycloak_url or args.base_url.rstrip("/") + "/auth").rstrip("/")
        self.realm = urllib.parse.quote(args.realm, safe="")
        self.admin_token, self.admin_until = None, 0
        self.system_token, self.system_until = None, 0
        self.clients, self.resources, self.added_scopes = [], [], []

    def token(self, realm, **form):
        return request("POST", self.auth_url + f"/realms/{realm}/protocol/openid-connect/token", form=form)

    def admin(self, method, path, data=None):
        if time.monotonic() >= self.admin_until:
            result = self.token(urllib.parse.quote(self.args.admin_realm, safe=""),
                                grant_type="password", client_id="admin-cli",
                                username=self.args.admin_user,
                                password=os.environ.get("THP_ADMIN_PASSWORD", "admin"))
            self.admin_token = result["access_token"]
            self.admin_until = time.monotonic() + result.get("expires_in", 60) - 20
        return request(method, self.auth_url + f"/admin/realms/{self.realm}" + path,
                       token=self.admin_token, data=data)

    def system(self):
        if time.monotonic() >= self.system_until:
            result = self.token(self.realm, grant_type="client_credentials",
                                client_id=self.args.system_client,
                                client_secret=os.environ.get("THP_SYSTEM_CLIENT_SECRET", "password"),
                                scope="system/*.cruds")
            self.system_token = result["access_token"]
            self.system_until = time.monotonic() + result.get("expires_in", 60) - 30
        return self.system_token

    def fhir(self, method, path, data=None):
        return request(method, self.fhir_url + "/" + path, token=self.system(), data=data)

    def record(self):
        save(self.work / "provisioned.json", {"clients": self.clients, "resources": self.resources,
                                              "addedRealmScopes": self.added_scopes})

    def create_patient(self, resource):
        created = self.fhir("POST", "Patient", resource)
        if not created or created.get("resourceType") != "Patient" or not created.get("id"):
            raise RuntimeError("FHIR create did not return a Patient with an ID")
        ref = "Patient/" + created["id"]
        self.resources.append(ref)
        self.record()
        return created["id"]

    def user(self, username):
        users = self.admin("GET", "/users?" + urllib.parse.urlencode({"username": username, "exact": "true"}))
        if len(users) != 1:
            raise RuntimeError(f"Expected one seeded THP user named {username!r}; run THP's fhir-init first")
        return users[0]

    def connect_config(self):
        patient = self.user(self.args.patient_user)
        other = self.user(self.args.other_patient_user)
        practitioner = self.user(self.args.practitioner_user)

        def link(user, attribute, types):
            values = user.get("attributes", {}).get(attribute, [])
            if len(values) != 1:
                raise RuntimeError(f"Seeded user {user['username']} has no unique {attribute} link")
            value = values[0]
            if attribute == "patient" and re.fullmatch(r"[A-Za-z0-9.-]+", value):
                value = "Patient/" + value
            ref = reference(value, types)
            self.fhir("GET", ref)
            return ref

        patient_id = link(patient, "patient", ["Patient"]).split("/")[1]
        other_id = link(other, "patient", ["Patient"]).split("/")[1]
        practitioner_ref = link(practitioner, "fhirUser", ["PractitionerRole", "Practitioner"])
        if patient_id == other_id:
            raise RuntimeError("Connect needs two distinct seeded patients")
        scopes = {s["name"]: s for s in self.admin("GET", "/client-scopes")}
        defaults = {
            "patient": ["launch/patient", "patient_attribute_mapper", "roles", "token_type"],
            "user": ["launch/user", "fhir_user_attribute_mapper", "roles", "token_type"],
            "system": ["service_account", "launch/system", "token_type"],
        }
        for name in {s for names in defaults.values() for s in names}:
            if name not in scopes:
                raise RuntimeError(f"THP realm is missing client scope {name!r}")
        for pairs in READ_SCOPES.values():
            for name, _ in pairs:
                if name not in scopes:
                    if self.args.require_existing_scopes:
                        raise RuntimeError(f"Required read scope {name!r} is absent (--require-existing-scopes)")
                    self.admin("POST", "/client-scopes", {"name": name, "protocol": "openid-connect",
                               "attributes": {"include.in.token.scope": "true",
                                              "display.on.consent.screen": "false"}})
                    owned_scope = {"name": name, "id": None}
                    self.added_scopes.append(owned_scope)
                    self.record()
                    found = self.admin("GET", "/client-scopes")
                    owned_scope["id"] = next(s["id"] for s in found if s["name"] == name)
                    self.record()

        config = {}
        for kind, pairs in READ_SCOPES.items():
            client_name = "isik-run-" + self.work.name + "-" + kind
            secret = secrets.token_urlsafe(32)
            self.admin("POST", "/clients", {
                "clientId": client_name, "enabled": True, "protocol": "openid-connect",
                "clientAuthenticatorType": "client-secret", "secret": secret,
                "publicClient": False, "standardFlowEnabled": False,
                "directAccessGrantsEnabled": kind != "system", "serviceAccountsEnabled": kind == "system",
                "defaultClientScopes": defaults[kind], "optionalClientScopes": [s for s, _ in pairs],
                "attributes": {"access.token.lifespan": "900"},
            })
            owned = {"clientId": client_name, "id": None}
            self.clients.append(owned)
            self.record()
            client = self.admin("GET", "/clients?" + urllib.parse.urlencode({"clientId": client_name}))[0]
            owned["id"] = client["id"]
            self.record()
            if kind == "system":
                account = self.admin("GET", f"/clients/{client['id']}/service-account-user")
                role = self.admin("GET", "/roles/thp-system")
                self.admin("POST", f"/users/{account['id']}/role-mappings/realm", [role])
                account.setdefault("attributes", {})["token_type"] = ["system"]
                self.admin("PUT", f"/users/{account['id']}", account)
            for scope, key in pairs:
                form = {"client_id": client_name, "client_secret": secret, "scope": scope}
                context = {}
                if kind == "system":
                    form["grant_type"] = "client_credentials"
                else:
                    form.update(grant_type="password",
                                username=self.args.patient_user if kind == "patient" else self.args.practitioner_user,
                                password=os.environ.get("THP_PATIENT_PASSWORD" if kind == "patient"
                                                        else "THP_PRACTITIONER_PASSWORD", "password"))
                    context = {"patient": patient_id} if kind == "patient" else {"fhirUser": practitioner_ref}
                token = self.token(self.realm, **form)["access_token"]
                validate_scope(token, kind, scope, context)
                config[key] = token
        for key in ("read-patient-in-context-id", "read-wildcard-patient-in-context-id",
                    "read-patient-in-user-context-id", "read-wildcard-patient-in-user-context-id",
                    "read-patient-in-system-context-id"):
            config[key] = patient_id
        for key in ("read-patient-not-in-context-id", "read-wildcard-patient-not-in-context-id"):
            config[key] = other_id
        return config

    def cleanup(self):
        errors = []
        items = [] if self.args.keep_fixtures else [("FHIR", ref) for ref in reversed(self.resources)]
        items += [("client", client) for client in reversed(self.clients)]
        items += [("scope", scope) for scope in reversed(self.added_scopes)]
        for kind, item in items:
            try:
                if kind == "FHIR":
                    self.fhir("DELETE", item)
                elif kind == "client":
                    client_id = item["id"]
                    if not client_id:
                        found = self.admin("GET", "/clients?" + urllib.parse.urlencode({"clientId": item["clientId"]}))
                        client_id = found[0]["id"] if found else None
                    if client_id:
                        self.admin("DELETE", "/clients/" + client_id)
                else:
                    scope_id = item["id"]
                    if not scope_id:
                        found = [s for s in self.admin("GET", "/client-scopes") if s["name"] == item["name"]]
                        scope_id = found[0]["id"] if found else None
                    if scope_id:
                        self.admin("DELETE", "/client-scopes/" + scope_id)
            except ApiError as error:
                if error.status not in (404, 410):
                    errors.append(str(error))
            except Exception as error:
                errors.append(str(error))
        return errors


def patient_read_fixture(run_id):
    """Synthetic ISiK Patient-Read data, including the required German name/address extensions."""
    def ext(url, value, type_name="String"):
        return {"url": url, "value" + type_name: value}

    hl7 = "http://hl7.org/fhir/StructureDefinition/"
    return {
        "resourceType": "Patient", "active": True, "gender": "male", "birthDate": "1968-05-12",
        "identifier": [
            {"type": {"coding": [{"system": "http://terminology.hl7.org/CodeSystem/v2-0203", "code": "MR"}]},
             "system": "http://testkrankenhaus.de/fhir/sid/Patient", "value": "isik-" + run_id},
            {"type": {"coding": [{"system": "http://fhir.de/CodeSystem/identifier-type-de-basis", "code": "KVZ10"}]},
             "system": "http://fhir.de/sid/gkv/kvid-10", "value": "X485231029"}],
        "name": [{"use": "official", "family": "Graf von und zu Mustermann", "given": ["Max"],
                  "prefix": ["Prof."], "_prefix": [{"extension": [ext(hl7 + "iso21090-EN-qualifier", "AC", "Code")]}],
                  "_family": {"extension": [ext(hl7 + "humanname-own-name", "Mustermann"),
                                            ext(hl7 + "humanname-own-prefix", "von und zu"),
                                            ext("http://fhir.de/StructureDefinition/humanname-namenszusatz", "Graf")]}}],
        "telecom": [{"system": "phone", "value": "030 1234567"}],
        "address": [
            {"type": "both", "city": "Berlin", "postalCode": "10117", "country": "DE",
             "extension": [ext(hl7 + "iso21090-ADXP-precinct", "Mitte")],
             "line": ["Unter den Linden 3", "1. Etage Hinterhaus"],
             "_line": [{"extension": [ext(hl7 + "iso21090-ADXP-streetName", "Unter den Linden"),
                                      ext(hl7 + "iso21090-ADXP-houseNumber", "3")]},
                       {"extension": [ext(hl7 + "iso21090-ADXP-additionalLocator", "1. Etage Hinterhaus")]}]},
            {"type": "postal", "city": "Berlin", "postalCode": "10117", "country": "DE",
             "line": ["Postfach 4711"], "_line": [{"extension": [ext(hl7 + "iso21090-ADXP-postBox", "Postfach 4711")]}]},
        ],
    }


def configuration(thp, selection, folder):
    if selection == "connect":
        data, key, auth = thp.connect_config(), "connect", None
    elif selection == "patient-read":
        data = {"patient-read-id": thp.create_patient(patient_read_fixture(thp.work.name))}
        key, auth = "basis", thp.system()
    else:
        data = {"patient-update-cancellation-identifier-system": "urn:isik-local-test",
                "patient-update-cancellation-identifier-value": thp.work.name}
        fixture_path = thp.args.project / "src/test/resources/features/Stufe5/Basis/fixtures/Patient-Update-Cancellation-Inactive-Fixture.json"
        fixture = fixture_path.read_text()
        for name, value in data.items():
            fixture = fixture.replace("${basis." + name + "}", value)
        patient = json.loads(fixture)
        patient.pop("id")
        patient["active"] = True
        data["patient-update-cancellation-id"] = thp.create_patient(patient)
        patient["name"][0]["family"] = "Storno-Delete-Mustermann"
        patient["identifier"][0]["value"] += "-delete"
        data["patient-delete-id"] = thp.create_patient(patient)
        key, auth = "basis", thp.system()
    # JSON is valid YAML; no PyYAML installation is needed.
    save(folder / "testdata.yaml", data)
    (folder / "src").symlink_to(thp.args.project / "src", target_is_directory=True)
    route = {"from": "http://fhirserver", "to": thp.fhir_url}
    if auth:
        route["authentication"] = {"bearerToken": auth}
    config = {"tigerProxy": {"adminPort": thp.args.proxy_port, "proxyRoutes": [route]},
              "lib": {"activateWorkflowUi": False, "trafficVisualization": True, "runTestsOnStart": True},
              "logging": {"level": {"de.gematik.rbellogger.converter": "WARN"}},
              "additionalConfigurationFiles": [{"filename": str(folder / "testdata.yaml"), "baseKey": key}]}
    save(folder / "tiger.yaml", config)
    return folder / "tiger.yaml"


def junit_results(directory):
    """Use final Failsafe outcomes, including reporting-hook failures missed by Serenity."""
    scenarios = []
    for path in sorted(directory.glob("TEST-*.xml")):
        for case in ET.parse(path).getroot().iter("testcase"):
            skipped = case.find("skipped")
            if skipped is not None and "did not match this scenario" in skipped.get("message", ""):
                continue
            problem = next((c for c in case if c.tag in ("failure", "error", "skipped")), None)
            scenarios.append({"name": case.get("name"), "class": case.get("classname"),
                              "result": problem.tag if problem is not None else "passed",
                              "message": problem.get("message", "") if problem is not None else ""})
    return scenarios


def result_code(maven_code, scenarios):
    if maven_code == 130:
        return 130
    if not scenarios or (maven_code and not any(s["result"] in ("failure", "error") for s in scenarios)):
        return 2
    return 1 if any(s["result"] != "passed" for s in scenarios) else 0


def execute(command, cwd, logfile, timeout):
    """Terminate Maven and its forked JVM together on timeout or interruption."""
    with logfile.open("w") as log:
        process = subprocess.Popen(command, cwd=cwd, stdout=log, stderr=subprocess.STDOUT,
                                   start_new_session=True)
        deadline = time.monotonic() + timeout
        try:
            while True:
                try:
                    return process.wait(timeout=min(30, max(0.01, deadline - time.monotonic())))
                except subprocess.TimeoutExpired:
                    if time.monotonic() >= deadline:
                        raise TimeoutError(f"Command timed out after {timeout}s; see {logfile}")
                    say(f"  Still running; log: {logfile}")
        except (KeyboardInterrupt, TimeoutError):
            os.killpg(process.pid, signal.SIGTERM)
            try:
                process.wait(timeout=10)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
            raise


def run_selection(args, thp, name):
    folder = thp.work / name
    folder.mkdir()
    say(f"Preparing {name}…")
    config = configuration(thp, name, folder)
    command = [args.maven, "-B", "clean", "verify", "-Pstufe5", "-Dtiger.version=" + args.tiger_version,
               "-DTESTS_TO_RUN=" + SELECTIONS[name], "-Dtiger-configuration-yaml=" + str(config)]
    save(folder / "command.json", command)
    say(f"Running {name} (Tiger {args.tiger_version})…")
    # A Maven startup failure can happen before clean executes. Do not attribute
    # the preceding selection's XML or HTML to this run in that case.
    for relative in REPORT_PATHS:
        previous = args.project / "target" / relative
        if previous.is_symlink() or previous.is_file():
            previous.unlink()
        elif previous.is_dir():
            shutil.rmtree(previous)
    code, issue = 2, None
    try:
        code = execute(command, args.project, folder / "execution.log", args.test_timeout)
    except KeyboardInterrupt:
        code, issue = 130, "Interrupted"
    except TimeoutError as error:
        issue = str(error)
    for relative in REPORT_PATHS:
        source, target = args.project / "target" / relative, folder / relative
        if source.is_dir():
            shutil.copytree(source, target)
        elif source.is_file():
            shutil.copy2(source, target)
    scenarios = junit_results(folder / "failsafe-reports")
    result = {"selection": name, "mavenExitCode": code, "exitCode": result_code(code, scenarios),
              "counts": dict(Counter(s["result"] for s in scenarios)), "scenarios": scenarios,
              "unitTests": dict(Counter(s["result"] for s in junit_results(folder / "surefire-reports")))}
    if issue:
        result["issue"] = issue
        result["exitCode"] = 130 if code == 130 else 2
    save(folder / "result.json", result)
    say(f"{name}: {result['counts']} (Maven exit {code})")
    return result


def write_report(work, summary):
    save(work / "summary.json", summary)
    rows, problems = [], []
    for item in summary["runs"]:
        name, counts = item["selection"], item.get("counts", {})
        link = f"{name}/site/serenity/index.html"
        label = f'<a href="{link}">{html.escape(name)}</a>' if (work / link).is_file() else html.escape(name)
        rows.append(f"<tr><td>{label}</td>" + "".join(f"<td>{counts.get(k, 0)}</td>" for k in
                    ("passed", "failure", "error", "skipped")) +
                    f'<td>{item["exitCode"]}</td><td><a href="{name}/execution.log">Log</a></td></tr>')
        if item.get("issue"):
            problems.append(f"{name}: {item['issue']}")
        for scenario in item.get("scenarios", []):
            if scenario["result"] != "passed":
                problems.append(f"{name}: {scenario['name']}: {scenario['message']}")
    problems.extend(summary.get("issues", []))
    counts = Counter()
    for item in summary["runs"]:
        counts.update(item.get("counts", {}))
    document = ('<!doctype html><html lang="en"><meta charset="utf-8"><title>THP ISiK test run</title>'
                '<style>body{font:16px system-ui;margin:3rem;max-width:1100px;color:#183447}'
                'td,th{padding:.7rem;text-align:left;border-bottom:1px solid #ccd7df}'
                'table{border-collapse:collapse}li{margin:.6rem 0;white-space:pre-wrap}</style>'
                '<h1>THP ISiK test run</h1>'
                f'<p>{html.escape(summary["baseUrl"])} · {html.escape(summary["startedAt"])}</p>'
                f'<p>Exit status: {summary["exitCode"]}. '
                f'{counts["passed"]} passed, {counts["failure"]} failed, {counts["error"]} errors, '
                f'{counts["skipped"]} skipped.</p>'
                '<p>Totals use final Maven Failsafe results. Selection links open native Tiger/Serenity reports.</p>'
                '<table><tr><th>Selection</th><th>Passed</th><th>Failed</th><th>Errors</th><th>Skipped</th>'
                '<th>Exit</th><th>Execution log</th></tr>' + ''.join(rows) + '</table>'
                '<h2>Failures and setup issues</h2><ul>' + ''.join('<li>' + html.escape(p) + '</li>' for p in problems)
                + '</ul><p><a href="summary.json">Machine-readable summary</a></p></html>')
    (work / "index.html").write_text(document, encoding="utf-8")


def wait_ready(args, thp):
    deadline = time.monotonic() + args.wait_timeout
    last_error = "not ready"
    while time.monotonic() < deadline:
        try:
            capability = request("GET", thp.fhir_url + "/metadata")
            if capability.get("resourceType") != "CapabilityStatement":
                raise RuntimeError("FHIR metadata is not a CapabilityStatement")
            request("GET", thp.auth_url + f"/realms/{thp.realm}/.well-known/openid-configuration")
            return
        except (RuntimeError, ValueError) as error:
            last_error = str(error)
            say(f"Waiting for THP: {last_error}")
            time.sleep(min(5, max(0, deadline - time.monotonic())))
    raise RuntimeError(f"THP did not become ready within {args.wait_timeout}s: {last_error}")


def arguments(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--base-url", default=os.environ.get("THP_BASE_URL", "http://localhost:8080"))
    parser.add_argument("--keycloak-url", help="Defaults to BASE_URL/auth")
    parser.add_argument("--realm", default="thp")
    parser.add_argument("--admin-realm", default="master")
    parser.add_argument("--admin-user", default=os.environ.get("THP_ADMIN_USER", "admin"))
    parser.add_argument("--system-client", default="postman")
    parser.add_argument("--patient-user", default="patient-1")
    parser.add_argument("--other-patient-user", default="patient-2")
    parser.add_argument("--practitioner-user", default="practitioner-1")
    parser.add_argument("--tests", nargs="+", choices=SELECTIONS, default=list(SELECTIONS))
    parser.add_argument("--project", type=Path, default=PROJECT, help="ISiK test-suite checkout")
    parser.add_argument("--output", type=Path, help="Report parent directory; defaults to PROJECT/.test-reports/thp")
    parser.add_argument("--maven", default="mvn")
    parser.add_argument("--tiger-version", default="4.4.3")
    parser.add_argument("--proxy-port", type=int, default=9011)
    parser.add_argument("--wait-timeout", type=int, default=180)
    parser.add_argument("--test-timeout", type=int, default=900, help="Seconds per Maven invocation")
    parser.add_argument("--compose-file", type=Path, help="Optionally run docker compose up -d before testing")
    parser.add_argument("--compose-project", help="Compose project name, if starting a stack")
    parser.add_argument("--keep-fixtures", action="store_true", help="Retain created patients for debugging")
    parser.add_argument("--require-existing-scopes", action="store_true",
                        help="Fail if a Connect read scope is missing instead of creating it temporarily")
    args = parser.parse_args(argv)
    args.project = args.project.resolve()
    args.output = (args.output or args.project / ".test-reports/thp").resolve()
    target = args.project / "target"
    if args.output == target or target in args.output.parents:
        parser.error("--output must be outside Maven's target directory")
    if len(set(args.tests)) != len(args.tests):
        parser.error("--tests must not contain duplicates")
    if args.wait_timeout <= 0 or args.test_timeout <= 0:
        parser.error("Timeouts must be positive")
    if not (args.project / "pom.xml").is_file() or not (args.project / "src/test").is_dir():
        parser.error("--project must point to the ISiK test-suite checkout")
    return args


def main(argv=None):
    args = arguments(argv)
    os.umask(0o077)  # Configurations and native HTTP reports include bearer tokens.
    if not shutil.which(args.maven):
        raise RuntimeError(f"Maven executable not found: {args.maven}")
    lock = args.project / ".test-reports/.thp-run.lock"
    lock.parent.mkdir(parents=True, exist_ok=True)
    try:
        with lock.open("x") as stream:
            stream.write(str(os.getpid()))
    except FileExistsError:
        raise RuntimeError(f"Another THP runner owns {lock}; check its PID before removing a stale lock") from None
    try:
        args.output.mkdir(parents=True, exist_ok=True)
        run_id = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ") + "-" + uuid.uuid4().hex[:8]
        work = args.output / run_id
        work.mkdir()
        thp = Thp(args, work)
        summary = {"startedAt": datetime.now(timezone.utc).isoformat(), "baseUrl": args.base_url,
                   "project": str(args.project), "tigerVersion": args.tiger_version,
                   "pomSha256": hashlib.sha256((args.project / "pom.xml").read_bytes()).hexdigest(),
                   "runs": [], "issues": [], "exitCode": 0}
        summary["suiteCommit"] = None
        if shutil.which("git"):
            git = subprocess.run(["git", "rev-parse", "HEAD"], cwd=args.project, text=True, capture_output=True)
            summary["suiteCommit"] = git.stdout.strip() if git.returncode == 0 else None
        say(f"Reports: {work / 'index.html'}")
        try:
            if args.compose_file:
                command = ["docker", "compose", "-f", str(args.compose_file.resolve())]
                if args.compose_project:
                    command += ["--project-name", args.compose_project]
                code = execute(command + ["up", "-d"], args.compose_file.resolve().parent,
                               work / "docker-start.log", args.wait_timeout)
                if code:
                    raise RuntimeError(f"Docker Compose startup failed; see {work / 'docker-start.log'}")
            wait_ready(args, thp)
            for name in args.tests:
                try:
                    result = run_selection(args, thp, name)
                except KeyboardInterrupt:
                    raise
                except Exception as error:
                    result = {"selection": name, "counts": {}, "exitCode": 2, "issue": str(error)}
                    say(f"{name}: setup/build error: {error}")
                summary["runs"].append(result)
                summary["exitCode"] = max(summary["exitCode"], result["exitCode"])
                write_report(work, summary)
                if result["exitCode"] == 130:
                    break
        except KeyboardInterrupt:
            summary["exitCode"] = 130
            summary["issues"].append("Interrupted")
        except Exception as error:
            summary["exitCode"] = 2
            summary["issues"].append(str(error))
            say(str(error))
        finally:
            say("Cleaning up temporary test clients and patients…")
            cleanup_errors = thp.cleanup()
            summary["issues"].extend(cleanup_errors)
            if cleanup_errors and summary["exitCode"] != 130:
                summary["exitCode"] = 2
            summary["finishedAt"] = datetime.now(timezone.utc).isoformat()
            summary["fixturesRetained"] = args.keep_fixtures
            write_report(work, summary)
        say(f"Finished with exit {summary['exitCode']}. Report: {work / 'index.html'}")
        return summary["exitCode"]
    finally:
        lock.unlink()


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (RuntimeError, OSError) as error:
        print(f"Error: {error}", file=sys.stderr)
        sys.exit(2)
