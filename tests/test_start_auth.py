from __future__ import annotations

import base64
import importlib.util
import io
import json
import os
import shutil
import stat
import subprocess
import traceback
from email.message import Message
from pathlib import Path
from urllib.error import HTTPError

import pytest
import test_discovery as fixtures

from beejsp import assessment, dashboard, discovery

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("beejsp_start", ROOT / "config/start.py")
if SPEC is None or SPEC.loader is None:
    raise RuntimeError("BeeJSP startup module loader unavailable")
bootstrap = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(bootstrap)

TOKEN = "ghp_" + "TESTONLY" * 5
OTHER = "github_pat_" + "TESTONLY" * 8


@pytest.fixture(autouse=True)
def isolate_credentials(monkeypatch):
    monkeypatch.delenv("GITHUB_TOKEN", raising=False)


def template(root):
    (root / ".env.example").write_bytes((ROOT / ".env.example").read_bytes())


def test_initialization_permissions_preservation_and_missing_key(tmp_path):
    template(tmp_path)
    env = tmp_path / ".env"
    bootstrap.initialize_env(tmp_path)
    assert env.read_bytes() == (ROOT / ".env.example").read_bytes()
    assert stat.S_IMODE(env.stat().st_mode) == 0o600
    configured = f"# preserve comments\nGITHUB_TOKEN='{TOKEN}'\nOTHER=unchanged\n"
    env.write_text(configured)
    env.chmod(0o644)
    bootstrap.initialize_env(tmp_path)
    assert env.read_text() == configured
    assert stat.S_IMODE(env.stat().st_mode) == 0o600
    inode = env.stat().st_ino
    timestamp = env.stat().st_mtime_ns
    bootstrap.initialize_env(tmp_path)
    assert (env.stat().st_ino, env.stat().st_mtime_ns) == (inode, timestamp)
    env.write_bytes(b"OTHER=unchanged")
    bootstrap.initialize_env(tmp_path)
    assert env.read_bytes() == b"OTHER=unchanged\nGITHUB_TOKEN=\n"
    bootstrap.initialize_env(tmp_path)
    assert env.read_bytes().count(b"GITHUB_TOKEN=") == 1


@pytest.mark.parametrize("target", [".env", ".env.example"])
def test_configuration_symlinks_rejected(tmp_path, target):
    template(tmp_path)
    outside = tmp_path / "outside"
    outside.write_text("untouched")
    path = tmp_path / target
    path.unlink(missing_ok=True)
    path.symlink_to(outside)
    with pytest.raises(ValueError, match="symlinks"):
        bootstrap.initialize_env(tmp_path)
    assert outside.read_text() == "untouched"


def test_configuration_hardlinks_and_nonregular_files_rejected(tmp_path):
    template(tmp_path)
    outside = tmp_path / "outside"
    outside.write_text("untouched")
    env = tmp_path / ".env"
    env.hardlink_to(outside)
    before = outside.stat().st_mode
    with pytest.raises(ValueError, match="without links"):
        bootstrap.initialize_env(tmp_path)
    assert outside.read_text() == "untouched" and outside.stat().st_mode == before
    env.unlink()
    env.mkdir()
    with pytest.raises(OSError):
        bootstrap.initialize_env(tmp_path)


def test_environment_precedence_and_data_only_parsing(monkeypatch, tmp_path):
    assert bootstrap.configured_token(f"GITHUB_TOKEN='{TOKEN}' # local\n") == TOKEN
    assert bootstrap.configured_token('GITHUB_TOKEN=""\n') is None
    monkeypatch.setenv("GITHUB_TOKEN", OTHER)
    assert bootstrap.configured_token("GITHUB_TOKEN='broken local value'\n") == OTHER
    monkeypatch.setenv("GITHUB_TOKEN", "")
    assert bootstrap.configured_token(f"GITHUB_TOKEN={TOKEN}\n") == TOKEN
    monkeypatch.delenv("GITHUB_TOKEN")
    side_effect = tmp_path / "executed"
    with pytest.raises(ValueError):
        bootstrap.configured_token(f"GITHUB_TOKEN=$(touch {side_effect})\n")
    assert not side_effect.exists()
    assert (
        bootstrap.configured_token(
            f"UNSUPPORTED=$(touch {side_effect})\nGITHUB_TOKEN={TOKEN}\n"
        )
        == TOKEN
    )
    assert not side_effect.exists()


@pytest.mark.parametrize(
    "value",
    [
        "short",
        " ",
        TOKEN + "\nX: injected",
        TOKEN + "\r",
        TOKEN + " ",
        "Bearer " + TOKEN,
        "ghp_",
        "☃",
        "x" * 4096,
    ],
)
def test_unsafe_tokens_fail_without_echoing_values(value, monkeypatch):
    monkeypatch.setenv("GITHUB_TOKEN", value)
    with pytest.raises(ValueError) as failure:
        bootstrap.configured_token("GITHUB_TOKEN=\n")
    assert str(failure.value) == "invalid GITHUB_TOKEN format"
    if value.strip():
        assert value not in "".join(traceback.format_exception(failure.value))


@pytest.mark.parametrize(
    "value",
    [
        "GITHUB_TOKEN\n",
        "GITHUB_TOKEN='unterminated\n",
        "GITHUB_TOKEN=\nGITHUB_TOKEN=\n",
    ],
)
def test_malformed_supported_configuration_fails(value):
    with pytest.raises(ValueError):
        bootstrap.configured_token(value)


class Response:
    headers = {}

    def __init__(self, payload):
        self.payload = payload

    def __enter__(self):
        return self

    def __exit__(self, *args):
        pass

    def read(self, size):
        return json.dumps(self.payload).encode()


@pytest.mark.parametrize("token", [None, TOKEN])
def test_anonymous_and_authenticated_requests_use_shared_client(monkeypatch, token):
    if token:
        monkeypatch.setenv("GITHUB_TOKEN", token)
    requests = []

    class Opener:
        def open(self, request, timeout):
            requests.append(request)
            address = request.full_url
            if "/commits/" in address:
                return Response({"sha": fixtures.SHA})
            if "/contents/" in address:
                path = (
                    "candidates/README.md"
                    if "/candidates/" in address
                    else "awards/README.md"
                )
                content = (
                    fixtures.CANDIDATES
                    if path.startswith("candidates")
                    else fixtures.AWARDS
                )
                return Response(
                    {
                        "encoding": "base64",
                        "path": path,
                        "content": base64.b64encode(content.encode()).decode(),
                    }
                )
            return Response([])

    monkeypatch.setattr(assessment, "build_opener", lambda _: Opener())
    capture = assessment.capture_github(evidence_version=2)
    records = discovery.capture_records()
    assert capture["acquisition"]["complete"] and records["acquisition"]["complete"]
    assert len(requests) == 5
    assert all(request.get_method() == "GET" for request in requests)
    assert all(
        request.full_url.startswith(
            f"https://api.github.com/repos/{assessment.OFFICIAL_REPOSITORY}/"
        )
        for request in requests
    )
    for request in requests:
        assert request.get_header("Authorization") == (
            f"Bearer {TOKEN}" if token else None
        )
    assert TOKEN not in assessment.render_json(capture) + assessment.render_json(
        records
    )


@pytest.mark.parametrize(
    "address",
    [
        "http://api.github.com/repos/TheJustinSunPrize/awards/pulls",
        "https://api.github.com.evil.test/repos/TheJustinSunPrize/awards/pulls",
        "https://user@api.github.com/repos/TheJustinSunPrize/awards/pulls",
        "https://api.github.com/repos/another/project/pulls",
        "https://api.github.com/repos/TheJustinSunPrize/awards/../../other/pulls",
        "https://api.github.com/repos/TheJustinSunPrize/awards/%2e%2e/pulls",
        "https://api.github.com/repos/TheJustinSunPrize/awards/actions/secrets",
    ],
)
def test_credentials_never_sent_to_unapproved_destinations(monkeypatch, address):
    monkeypatch.setenv("GITHUB_TOKEN", TOKEN)
    monkeypatch.setattr(
        assessment, "build_opener", lambda _: pytest.fail("unapproved request")
    )
    with pytest.raises(ValueError):
        assessment._github_payload(address)


@pytest.mark.parametrize("code", [401, 403, 429])
def test_rejections_fail_closed_without_secret_in_errors(monkeypatch, code):
    monkeypatch.setenv("GITHUB_TOKEN", TOKEN)

    class Opener:
        def open(self, *args, **kwargs):
            raise HTTPError(
                "https://api.github.com/" + TOKEN,
                code,
                "echo " + TOKEN,
                Message(),
                io.BytesIO(TOKEN.encode()),
            )

    monkeypatch.setattr(assessment, "build_opener", lambda _: Opener())
    result = assessment.capture_github(evidence_version=2)
    assert not result["acquisition"]["complete"]
    assert str(code) in result["acquisition"]["error"]
    assert TOKEN not in assessment.render_json(result)
    with pytest.raises(ValueError) as failure:
        assessment._github_payload(
            f"https://api.github.com/repos/{assessment.OFFICIAL_REPOSITORY}/pulls"
        )
    assert TOKEN not in "".join(traceback.format_exception(failure.value))
    assert failure.value.__context__ is None


def test_payload_transport_errors_and_encoded_registers_redact_token(monkeypatch):
    monkeypatch.setenv("GITHUB_TOKEN", TOKEN)

    class Opener:
        def open(self, *args, **kwargs):
            return Response(
                {
                    "message": TOKEN,
                    "encoding": "base64",
                    "content": base64.b64encode(TOKEN.encode()).decode(),
                }
            )

    monkeypatch.setattr(assessment, "build_opener", lambda _: Opener())
    payload, _ = assessment._github_payload(
        f"https://api.github.com/repos/{assessment.OFFICIAL_REPOSITORY}/pulls"
    )
    assert TOKEN not in json.dumps(payload)
    assert TOKEN not in base64.b64decode(payload["content"]).decode()

    class Broken:
        def open(self, *args, **kwargs):
            raise OSError("header Authorization: Bearer " + TOKEN)

    monkeypatch.setattr(assessment, "build_opener", lambda _: Broken())
    result = assessment.capture_github(evidence_version=2)
    assert TOKEN not in assessment.render_json(result)
    assert "[REDACTED]" in result["acquisition"]["error"]


def test_first_launcher_invocation_from_external_directory(tmp_path):
    project = tmp_path / "project"
    (project / "config").mkdir(parents=True)
    for name in ("start.sh", ".env.example", "config/start.py"):
        shutil.copyfile(ROOT / name, project / name)
    (project / "start.sh").chmod(0o755)
    (project / "pyproject.toml").write_text(
        '[project]\nname="bootstrap-test"\nversion="0.0.0"\nrequires-python=">=3.14"\n'
    )
    (project / ".venv").symlink_to(ROOT / ".venv", target_is_directory=True)
    environment = {k: v for k, v in os.environ.items() if k != "GITHUB_TOKEN"} | {
        "UV_OFFLINE": "1"
    }
    result = subprocess.run(
        [str(project / "start.sh"), "--help"],
        cwd=tmp_path,
        env=environment,
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode == 0, result.stderr
    assert (project / ".env").read_bytes() == (ROOT / ".env.example").read_bytes()
    assert stat.S_IMODE((project / ".env").stat().st_mode) == 0o600


def test_template_tracked_secret_variants_ignored():
    result = subprocess.run(
        ["git", "check-ignore", ".env", ".env.local", ".env.example"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode == 0
    assert result.stdout.splitlines() == [".env", ".env.local"]


def test_report_inputs_cannot_publish_credentials_and_previous_snapshot_survives(
    tmp_path, monkeypatch
):
    import test_dashboard as saved_fixtures

    first = saved_fixtures.publish(monkeypatch, tmp_path)
    pointer = (tmp_path / "storage/discovery/current.json").read_bytes()
    saved = saved_fixtures.inputs()
    saved["scanner"]["records"][0]["title"] = "unsafe input " + TOKEN
    saved_fixtures.mock_capture(monkeypatch, saved)
    monkeypatch.setenv("GITHUB_TOKEN", TOKEN)
    with pytest.raises(ValueError) as failure:
        dashboard.refresh(tmp_path)
    assert TOKEN not in str(failure.value)
    assert (tmp_path / "storage/discovery/current.json").read_bytes() == pointer
    assert first.exists()
    assert TOKEN not in (tmp_path / "storage/discovery/refresh-status.json").read_text()


def test_encoded_credentials_cannot_enter_capture_records(monkeypatch):
    monkeypatch.setenv("GITHUB_TOKEN", TOKEN)

    class Opener:
        def open(self, *args, **kwargs):
            return Response({"echo": TOKEN.replace("_", "%5F")})

    monkeypatch.setattr(assessment, "build_opener", lambda _: Opener())
    result = assessment.capture_github(evidence_version=2)
    assert not result["acquisition"]["complete"]
    assert result["acquisition"]["error"] == "credential found in encoded upstream data"
    assert TOKEN not in assessment.render_json(result)
