from __future__ import annotations

import base64
import copy
import csv
import hashlib
import io
import json
import os
import re
import subprocess
from collections import Counter
from pathlib import Path
from typing import cast

import pytest
import test_discovery as fixtures

from beejsp import assessment, dashboard, discovery
from beejsp.scanner import scan_problem_bank

ROOT = Path(__file__).resolve().parents[1]


def awards():
    return {
        "schema_version": 2,
        "acquisition": {
            "repository": assessment.OFFICIAL_REPOSITORY,
            "observed_at": fixtures.WHEN,
            "complete": True,
            "search_scope": "official registers",
            "upstream_commit": fixtures.SHA,
        },
        "records": [],
    }


def inputs():
    return {
        "scanner": fixtures.scanner(),
        "competition": fixtures.competition(),
        "awards": awards(),
        "research": {"schema_version": 2, "candidates": []},
    }


def payload(html):
    match = re.search(r'id="discovery-data">(.*?)</script>', html, re.S)
    assert match is not None
    return json.loads(match.group(1))


def mock_capture(monkeypatch, saved):
    monkeypatch.setattr(
        dashboard.scanner, "scan_problem_bank", lambda _: saved["scanner"]
    )

    def capture(*, evidence_version, kind, page_size):
        assert evidence_version == 2 and kind == "all" and page_size == 50
        return saved["competition"]

    monkeypatch.setattr(dashboard.assessment, "capture_github", capture)
    monkeypatch.setattr(dashboard.discovery, "capture_records", lambda: saved["awards"])


def publish(monkeypatch, root, saved=None):
    saved = saved or inputs()
    mock_capture(monkeypatch, saved)
    storage = root / "storage/discovery"
    storage.mkdir(parents=True, exist_ok=True)
    (storage / "research.json").write_text(json.dumps(saved["research"]))
    return dashboard.refresh(root)


def test_complete_catalog_consistency_determinism_and_counts(monkeypatch):
    saved = inputs()
    saved["scanner"] = scan_problem_bank(ROOT / "docs/vendor/jsp")
    monkeypatch.setattr(
        assessment,
        "_github_payload",
        lambda _: pytest.fail("offline generation used network"),
    )
    reports = dashboard.build_reports(saved)
    assert reports == dashboard.build_reports(copy.deepcopy(saved))
    data = payload(reports["dashboard.html"])
    assert len(saved["scanner"]["records"]) == len(data["rows"]) == 1022
    assert {r["jsp_id"] for r in data["rows"]} == {
        r["jsp_id"] for r in saved["scanner"]["records"]
    }
    for name in ("general", "high-value"):
        result = json.loads(reports[f"{name}.json"])
        csv_rows = list(csv.DictReader(io.StringIO(reports[f"{name}.csv"])))
        json_rows = result["selected"] + result["excluded"]
        assert [r["jsp_id"] for r in csv_rows] == [r["jsp_id"] for r in json_rows]
        assert len(csv_rows) == 1022
        for row in json_rows:
            html_row = next(r for r in data["rows"] if r["jsp_id"] == row["jsp_id"])
            assert html_row["profiles"][name] == {
                k: row.get(k) for k in ("included", "rank", "reasons")
            }
            assert html_row["official"] == row["official"]
        for key in data["counts"]:
            assert data["counts"][key] == dict(
                Counter(r["filters"][key] for r in json_rows)
            )
    assert data["scanner_provenance"] == saved["scanner"]["source"]
    assert data["competition_acquisition"]["observed_at"] == fixtures.WHEN
    assert data["award_acquisition"]["upstream_commit"] == fixtures.SHA
    assert data["scanner_provenance"]["upstream_commit"] != fixtures.SHA


def test_profiles_and_excluded_unknown_candidates_remain_visible():
    saved = inputs()
    saved["research"] = fixtures.research(
        scientific_significance=fixtures.evidence(value="low")
    )
    data = payload(dashboard.build_reports(saved)["dashboard.html"])
    row = next(r for r in data["rows"] if r["jsp_id"] == "JSP-000161")
    assert row["profiles"]["general"]["included"]
    assert not row["profiles"]["high-value"]["included"]
    assert row["profiles"]["high-value"]["reasons"]
    assert row["research"]["difficulty"]["value"] == "unknown"
    assert row["published_amounts"] is None


@pytest.mark.parametrize(
    "version,complete,expected",
    [(1, True, "UNKNOWN"), (2, False, "UNKNOWN"), (2, True, "NONE_IN_SCOPE")],
)
def test_negative_coverage_and_positive_regressions(version, complete, expected):
    saved = inputs()
    saved["competition"]["schema_version"] = version
    saved["competition"]["acquisition"]["complete"] = complete
    saved["competition"]["acquisition"]["scopes"] = {
        "issues": complete,
        "pull_requests": complete,
    }
    data = payload(dashboard.build_reports(saved)["dashboard.html"])
    assert all(r["competition_state"] == expected for r in data["rows"])
    for jsp, number in (
        ("JSP-000161", 1248),
        ("JSP-000475", 1269),
        ("JSP-000089", 5006),
    ):
        saved["competition"]["observations"]["pull_requests"].append(
            fixtures.observation(
                jsp, number, state="closed-unmerged", proof_sources=[fixtures.source()]
            )
        )
    data = payload(dashboard.build_reports(saved)["dashboard.html"])
    assert {
        r["competition_state"] for r in data["rows"] if r["jsp_id"] != "JSP-000001"
    } == {"CONTESTED"}
    assert all(
        r["competition"][0]["proof_sources"][0]["commit"] == fixtures.SHA
        for r in data["rows"]
        if r["competition"]
    )


def test_historical_v1_jsp89_keeps_recorded_observations():
    saved = inputs()
    saved["scanner"] = scan_problem_bank(ROOT / "docs/vendor/jsp")
    saved["competition"] = dict(
        assessment._load_json(ROOT / "docs/evidence/iteration-3/competition.json")
    )
    data = payload(dashboard.build_reports(saved)["dashboard.html"])
    by_id = {r["jsp_id"]: r for r in data["rows"]}
    assert by_id["JSP-000089"]["competition_state"] == "CONTESTED"
    assert by_id["JSP-000161"]["competition_state"] == "UNKNOWN"
    assert by_id["JSP-000475"]["competition_state"] == "UNKNOWN"
    assert data["competition_complete"] is False


def test_review_and_published_award_evidence_separate():
    saved = inputs()
    saved["competition"]["observations"]["pull_requests"] = [
        fixtures.observation(proof_sources=[fixtures.source()])
    ]
    saved["research"] = fixtures.research(fixtures.verified_review())
    records = discovery.normalize_register(
        fixtures.AWARDS, "announced", fixtures.SHA, fixtures.WHEN, "awards/README.md"
    )
    records[0].update(
        official_award_level="Published level",
        published_amount="1234.50",
        currency="USD",
        publication_evidence=fixtures.evidence(
            url=f"{fixtures.ROOT}/blob/{fixtures.SHA}/awards/README.md"
        ),
    )
    saved["awards"]["records"] = records
    data = payload(dashboard.build_reports(saved)["dashboard.html"])
    by_id = {r["jsp_id"]: r for r in data["rows"]}
    assert by_id["JSP-000161"]["competition_state"] == "VERIFIED"
    assert by_id["JSP-000161"]["proof_reviews"][0]["statement_fidelity"] == "exact"
    assert by_id["JSP-000161"]["proof_reviews"][0]["reviewer"]
    assert by_id["JSP-000475"]["published_amounts"][0]["amount"] == "1234.50"
    assert by_id["JSP-000475"]["historical_bounty"].startswith("$1000")
    assert by_id["JSP-000475"]["awards"][0]["role"] == "formalizer"


@pytest.mark.parametrize(
    "bad",
    [
        "javascript:alert(1)",
        "data:text/html,test",
        "file:///tmp/test",
        "http://example.org",
        "https://user:password@example.org",
        "https://github.com\\@evil.test",
        "https://localhost",
        "https://127.0.0.1",
        "https://127.1",
        "https://0177.0.0.1",
        "https://0x7f.0.0.1",
        "https://10.1.2.3",
        "https://example.org/%0aevil",
        "https://example.org:8080",
        "https://example.org/%5cfile",
    ],
)
def test_safe_link_rejects_active_local_and_malformed_destinations(bad):
    assert dashboard.safe_link(bad) is None


def test_safe_html_preserves_hostile_text_and_validated_links():
    saved = inputs()
    hostile = '</script><script>globalThis.injected=true</script><img src=x onerror="alert(1)"> & \u2028'
    saved["scanner"]["records"][0]["title"] = hostile
    saved["scanner"]["records"][0]["official"]["fields"]["Problem description"] = (
        hostile
        + " [bad](javascript:alert) [citation](https://example.org/paper) [relative](../docs/source.md)"
    )
    html = dashboard.build_reports(saved)["dashboard.html"]
    assert hostile not in html
    assert html.count("</script>") == 2
    assert "<script src=" not in html and "fetch(" not in html
    assert "innerHTML" not in html and "eval(" not in html
    data = payload(html)
    row = next(r for r in data["rows"] if r["jsp_id"] == "JSP-000161")
    assert row["title"] == hostile
    assert "https://example.org/paper" in row["links"]
    assert (
        row["catalog_url"]
        == f"{fixtures.ROOT}/blob/{fixtures.SHA}/problems/README.md#JSP-000161"
    )
    assert all(dashboard.safe_link(link) for link in row["links"])
    assert "noopener noreferrer" in html
    assert "connect-src 'none'" in html


@pytest.mark.parametrize(
    "failure",
    [
        "scan",
        "github",
        "scope",
        "awards",
        "research",
        "generation",
        "write",
        "validation",
        "publish",
    ],
)
def test_failed_refresh_preserves_last_valid_snapshot(tmp_path, monkeypatch, failure):
    html = publish(monkeypatch, tmp_path)
    storage = tmp_path / "storage/discovery"
    pointer = (storage / "current.json").read_bytes()
    before = {p.name: p.read_bytes() for p in html.parent.iterdir()}
    saved = inputs()
    mock_capture(monkeypatch, saved)
    if failure == "scan":
        saved["scanner"]["is_complete"] = False
    elif failure == "github":
        saved["competition"]["acquisition"]["complete"] = False
        saved["competition"]["acquisition"]["error"] = "rate limited"
    elif failure == "scope":
        saved["competition"]["acquisition"]["scopes"] = {"issues": True}
    elif failure == "awards":
        saved["awards"]["acquisition"]["complete"] = False
    elif failure == "research":
        (storage / "research.json").write_text('{"schema_version":2,"candidates":[{}]}')
    elif failure == "generation":
        monkeypatch.setattr(
            dashboard,
            "render_html",
            lambda *_: (_ for _ in ()).throw(ValueError("generation failed")),
        )
    elif failure == "write":
        original = Path.write_text

        def write(path, *args, **kwargs):
            if path.name == "general.csv":
                raise OSError("disk full")
            return original(path, *args, **kwargs)

        monkeypatch.setattr(Path, "write_text", write)
    elif failure == "validation":
        monkeypatch.setattr(
            dashboard,
            "_read_snapshot",
            lambda _: (_ for _ in ()).throw(ValueError("invalid stage")),
        )
    else:
        original = os.replace

        def replace(source, target):
            if Path(target).name == "current.json":
                raise OSError("publication failed")
            return original(source, target)

        monkeypatch.setattr(dashboard.os, "replace", replace)
    with pytest.raises((OSError, ValueError)):
        dashboard.refresh(tmp_path)
    assert (storage / "current.json").read_bytes() == pointer
    assert {p.name: p.read_bytes() for p in html.parent.iterdir()} == before
    assert not list(storage.glob(".stage-*"))
    assert not (storage / ".refresh-lock").exists()
    assert (
        json.loads((storage / "refresh-status.json").read_text())["state"] == "failed"
    )


def test_cli_offline_and_failed_refresh_warning(tmp_path, monkeypatch, capsys):
    html = publish(monkeypatch, tmp_path)
    saved = inputs()
    saved["competition"]["acquisition"]["complete"] = False
    mock_capture(monkeypatch, saved)
    assert dashboard.main(["--root", str(tmp_path), "update"]) == 2
    monkeypatch.setattr(
        assessment, "capture_github", lambda **_: pytest.fail("offline network")
    )
    monkeypatch.setattr(
        discovery, "capture_records", lambda: pytest.fail("offline network")
    )
    monkeypatch.setattr(
        dashboard.webbrowser, "open", lambda _: pytest.fail("headless browser")
    )
    monkeypatch.delenv("DISPLAY", raising=False)
    monkeypatch.delenv("WAYLAND_DISPLAY", raising=False)
    assert dashboard.main(["--root", str(tmp_path), "report"]) == 0
    result = capsys.readouterr()
    assert str(html) in result.out and "Headless" in result.out
    assert "latest refresh failed" in result.err
    assert dashboard.main(["--root", str(tmp_path), "inspect", "JSP-000161"]) == 0
    result = capsys.readouterr()
    assert json.loads(result.out)["problem"]["jsp_id"] == "JSP-000161"
    assert "retained historical" in result.err
    assert dashboard.main(["--root", str(tmp_path), "inspect", "JSP-999999"]) == 2
    assert "not in normalized catalog" in capsys.readouterr().err


@pytest.mark.parametrize(
    "jsp", ["JSP-161", "JSP-0001610", "../JSP-000161", "jsp-000161"]
)
def test_invalid_ids_fail_clearly(tmp_path, capsys, jsp):
    assert dashboard.main(["--root", str(tmp_path), "inspect", jsp]) == 2
    assert "invalid JSP identity" in capsys.readouterr().err


def test_missing_saved_evidence(tmp_path, capsys):
    assert dashboard.main(["--root", str(tmp_path), "report"]) == 2
    assert "cannot load" in capsys.readouterr().err


@pytest.mark.parametrize("browser", [True, False, "error"])
def test_graphical_browser_is_optional(monkeypatch, tmp_path, browser):
    monkeypatch.setenv("DISPLAY", ":1")
    calls = []

    def open_browser(uri):
        calls.append(uri)
        if browser == "error":
            raise OSError("browser unavailable")
        return browser

    monkeypatch.setattr(dashboard.webbrowser, "open", open_browser)
    dashboard.open_report(tmp_path / "dashboard.html")
    assert calls == [(tmp_path / "dashboard.html").as_uri()]


@pytest.mark.parametrize(
    "tamper", ["hash", "coherence", "pointer", "symlink", "missing"]
)
def test_saved_artifacts_fail_closed(tmp_path, monkeypatch, tamper):
    html = publish(monkeypatch, tmp_path)
    storage = tmp_path / "storage/discovery"
    if tamper in {"hash", "coherence"}:
        html.write_text("<script>alert(1)</script>")
        if tamper == "coherence":
            manifest = json.loads((html.parent / "manifest.json").read_text())
            manifest["sha256"][html.name] = hashlib.sha256(
                html.read_bytes()
            ).hexdigest()
            (html.parent / "manifest.json").write_text(json.dumps(manifest))
    elif tamper == "pointer":
        (storage / "current.json").write_text('{"snapshot":"../../outside"}')
    elif tamper == "symlink":
        html.unlink()
        html.symlink_to(tmp_path / "outside")
    else:
        (html.parent / "competition.json").unlink()
    with pytest.raises(ValueError):
        dashboard.load_snapshot(tmp_path)


def test_storage_boundary_and_concurrent_refresh(tmp_path, monkeypatch):
    outside = tmp_path / "outside"
    outside.mkdir()
    (tmp_path / "storage").symlink_to(outside)
    with pytest.raises(ValueError, match="symlink"):
        dashboard.refresh(tmp_path)
    assert not list(outside.iterdir())
    (tmp_path / "storage").unlink()
    html = publish(monkeypatch, tmp_path)
    lock = html.parent.parent / ".refresh-lock"
    lock.mkdir()
    with pytest.raises(ValueError, match="another refresh"):
        dashboard.refresh(tmp_path)


def test_reuses_saved_reviewed_research(tmp_path, monkeypatch):
    saved = inputs()
    saved["research"] = fixtures.research(difficulty=fixtures.evidence(value="high"))
    first = publish(monkeypatch, tmp_path, saved)
    (tmp_path / "storage/discovery/research.json").unlink()
    second = dashboard.refresh(tmp_path)
    assert second != first and first.exists()
    _, retained = dashboard.load_snapshot(tmp_path)
    assert retained["research"] == saved["research"]


def test_launcher_dispatch_root_resolution_and_invalid_command(tmp_path):
    executable = tmp_path / "uv"
    executable.write_text(
        "#!/usr/bin/env python3\nimport json,sys\nprint(json.dumps(sys.argv[1:]))\n"
    )
    executable.chmod(0o755)
    environment = {
        **os.environ,
        "PATH": str(tmp_path) + os.pathsep + os.environ["PATH"],
    }
    for command in (["update"], ["report"], ["inspect", "JSP-000161"]):
        result = subprocess.run(
            [str(ROOT / "start.sh"), *command],
            cwd=tmp_path,
            env=environment,
            capture_output=True,
            text=True,
            check=False,
        )
        assert result.returncode == 0
        assert json.loads(result.stdout) == [
            "run",
            "--project",
            str(ROOT),
            "--no-sync",
            "python",
            str(ROOT / "config/start.py"),
            *command,
        ]
    actual = subprocess.run(
        [str(ROOT / "start.sh"), "invalid"],
        cwd=tmp_path,
        capture_output=True,
        text=True,
        check=False,
    )
    assert actual.returncode == 2 and "invalid choice" in actual.stderr


def test_real_launcher_offline_from_external_directory(tmp_path, monkeypatch):
    project = tmp_path / "project"
    project.mkdir()
    html = publish(monkeypatch, project)
    launcher = project / "start.sh"
    launcher.write_bytes((ROOT / "start.sh").read_bytes())
    launcher.chmod(0o755)
    (project / "config").mkdir()
    (project / "config/start.py").write_bytes((ROOT / "config/start.py").read_bytes())
    (project / ".env.example").write_bytes((ROOT / ".env.example").read_bytes())
    (project / "pyproject.toml").write_text(
        '[project]\nname="dashboard-cli-test"\nversion="0.0.0"\nrequires-python=">=3.14"\n'
    )
    (project / ".venv").symlink_to(ROOT / ".venv", target_is_directory=True)
    environment = {
        k: v for k, v in os.environ.items() if k not in {"DISPLAY", "WAYLAND_DISPLAY"}
    } | {"UV_OFFLINE": "1"}
    for arguments in (["report"], ["inspect", "JSP-000161"]):
        result = subprocess.run(
            [str(launcher), *arguments],
            cwd=tmp_path,
            env=environment,
            capture_output=True,
            text=True,
            check=False,
        )
        assert result.returncode == 0, result.stderr
        if arguments[0] == "report":
            assert str(html) in result.stdout and "Headless" in result.stdout
        else:
            assert json.loads(result.stdout)["problem"]["jsp_id"] == "JSP-000161"


def test_generated_artifacts_are_ignored():
    result = subprocess.run(
        [
            "git",
            "check-ignore",
            "storage/discovery/current.json",
            "storage/discovery/snapshot-example/dashboard.html",
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode == 0 and len(result.stdout.splitlines()) == 2


def test_capture_page_size_opt_in_preserves_default(monkeypatch):
    calls = []

    def page(address):
        calls.append(address)
        return [], None

    monkeypatch.setattr(assessment, "_github_page", page)
    assert assessment.capture_github()["acquisition"]["complete"]
    assert all("per_page=100" in address for address in calls)
    calls.clear()
    assert assessment.capture_github(evidence_version=2, page_size=50)["acquisition"][
        "complete"
    ]
    assert all("per_page=50" in address for address in calls)
    for invalid in (0, 101, True, "50"):
        with pytest.raises(ValueError, match="page size"):
            assessment.capture_github(page_size=cast(int, invalid))


@pytest.mark.parametrize("endpoint", ["pulls", "issues"])
def test_current_github_numeric_pagination_stays_on_official_route(
    monkeypatch, endpoint
):
    address = f"https://api.github.com/repos/{assessment.OFFICIAL_REPOSITORY}/{endpoint}?state=all&per_page=50"
    cursor = "&after=Y3Vyc29y%3D" if endpoint == "issues" else ""
    supplied = f"https://api.github.com/repositories/1363788649/{endpoint}?state=all&per_page=50{cursor}&page=2"
    monkeypatch.setattr(
        assessment, "_github_payload", lambda _: ([], f'<{supplied}>; rel="next"')
    )
    _, next_url = assessment._github_page(address)
    assert next_url == address + cursor + "&page=2"
    assert next_url is not None
    assert "/repositories/" not in next_url


@pytest.mark.parametrize(
    "mutation",
    [
        "foreign-host",
        "endpoint",
        "scope",
        "skip-page",
        "cursor-control",
        "cursor-pulls",
    ],
)
def test_numeric_pagination_cannot_expand_capture_authority(monkeypatch, mutation):
    endpoint = "pulls" if mutation == "cursor-pulls" else "issues"
    address = f"https://api.github.com/repos/{assessment.OFFICIAL_REPOSITORY}/{endpoint}?state=all&per_page=50"
    supplied = f"https://api.github.com/repositories/1363788649/{endpoint}?state=all&per_page=50&after=Y3Vyc29y%3D&page=2"
    if mutation == "foreign-host":
        supplied = supplied.replace("api.github.com", "api.github.com.evil.test")
    elif mutation == "endpoint":
        supplied = supplied.replace("/issues?", "/pulls?")
    elif mutation == "scope":
        supplied = supplied.replace("state=all", "state=open")
    elif mutation == "skip-page":
        supplied = supplied.replace("page=2", "page=3")
    elif mutation == "cursor-control":
        supplied = supplied.replace("Y3Vyc29y%3D", "%0Aevil")
    monkeypatch.setattr(
        assessment, "_github_payload", lambda _: ([], f'<{supplied}>; rel="next"')
    )
    with pytest.raises(ValueError):
        assessment._github_page(address)


def test_malformed_public_pin_retains_claim_and_complete_capture(monkeypatch):
    observation = {
        "number": 4565,
        "title": "JSP-000161 Lean proof",
        "state": "open",
        "html_url": f"{fixtures.ROOT}/pull/4565",
        "body": '```json\n[{"repository":"https://github.com/plby/lean-proofs","commit":"short"}]\n```',
    }
    monkeypatch.setattr(
        assessment,
        "_github_page",
        lambda address: ([observation], None) if "/pulls?" in address else ([], None),
    )
    result = assessment.capture_github(evidence_version=2, page_size=50)
    assert result["acquisition"]["complete"] is True
    assert discovery.validate_competition(result)[1] is True
    observed = result["observations"]["pull_requests"][0]
    assert observed["url"] == f"{fixtures.ROOT}/pull/4565"
    assert observed["jsp_ids"] == ["JSP-000161"]
    assert observed["source_metadata_errors"] == ["proof commit must be a full SHA"]
    assert all(source["commit"] is None for source in observed["proof_sources"])
    inspected = discovery.inspect_problem(fixtures.scanner(), result, "JSP-000161")
    assert inspected["problem"]["competition_state"] == "CONTESTED"
    assert inspected["problem"]["competition"][0]["proof_state"] == "unresolved"
    assert "invalid proof-source metadata" in " ".join(
        inspected["problem"]["uncertainty"]
    )


def test_full_refresh_with_invalid_claim_manifest_offline_and_rollback(
    tmp_path, monkeypatch, capsys
):
    bank = scan_problem_bank(ROOT / "docs/vendor/jsp")
    monkeypatch.setattr(dashboard.scanner, "scan_problem_bank", lambda _: bank)
    bad_claim = {
        "number": 4565,
        "title": "JSP-000008 Lean submission",
        "state": "open",
        "html_url": f"{fixtures.ROOT}/pull/4565",
        "body": '```json\n[{"repository":"https://github.com/example/proofs","commit":"short"}]\n```',
    }
    monkeypatch.setattr(
        assessment,
        "_github_page",
        lambda address: ([bad_claim], None) if "/pulls?" in address else ([], None),
    )

    def register(address):
        if "/commits/" in address:
            return {"sha": fixtures.SHA}, ""
        path = (
            "candidates/README.md" if "/candidates/" in address else "awards/README.md"
        )
        content = (
            fixtures.CANDIDATES if path.startswith("candidates") else fixtures.AWARDS
        )
        return {
            "path": path,
            "encoding": "base64",
            "content": base64.b64encode(content.encode()).decode(),
        }, ""

    monkeypatch.setattr(assessment, "_github_payload", register)
    html = dashboard.refresh(tmp_path)
    snapshot, saved = dashboard.load_snapshot(tmp_path)
    assert saved["competition"]["acquisition"]["scopes"] == {
        "pull_requests": True,
        "issues": True,
    }
    assert saved["awards"]["acquisition"]["complete"]
    current = (tmp_path / "storage/discovery/current.json").read_bytes()
    assert json.loads(current)["snapshot"] == snapshot.name
    manifest = json.loads((snapshot / "manifest.json").read_text())
    for name, checksum in manifest["sha256"].items():
        assert hashlib.sha256((snapshot / name).read_bytes()).hexdigest() == checksum
    for name in ("general", "high-value"):
        result = json.loads((snapshot / f"{name}.json").read_text())
        assert len(result["selected"] + result["excluded"]) == 1022
        assert (
            len(
                list(
                    csv.DictReader(io.StringIO((snapshot / f"{name}.csv").read_text()))
                )
            )
            == 1022
        )
    data = payload(html.read_text())
    assert len(data["rows"]) == 1022
    invalid = next(r for r in data["rows"] if r["jsp_id"] == "JSP-000008")
    assert invalid["competition_state"] == "CONTESTED"
    assert invalid["competition"][0]["proof_state"] == "unresolved"

    def failed_page(_):
        raise assessment.AssessmentError("HTTP 403 rate limit exceeded")

    monkeypatch.setattr(assessment, "_github_page", failed_page)
    with pytest.raises(ValueError, match="incomplete GitHub acquisition"):
        dashboard.refresh(tmp_path)
    assert (tmp_path / "storage/discovery/current.json").read_bytes() == current
    for name, checksum in manifest["sha256"].items():
        assert hashlib.sha256((snapshot / name).read_bytes()).hexdigest() == checksum
    monkeypatch.setattr(
        assessment, "_github_payload", lambda _: pytest.fail("offline network")
    )
    monkeypatch.delenv("DISPLAY", raising=False)
    monkeypatch.delenv("WAYLAND_DISPLAY", raising=False)
    assert dashboard.main(["--root", str(tmp_path), "report"]) == 0
    assert "retained historical snapshot" in capsys.readouterr().err
    assert dashboard.main(["--root", str(tmp_path), "inspect", "JSP-000161"]) == 0
    assert json.loads(capsys.readouterr().out)["problem"]["jsp_id"] == "JSP-000161"


def legacy_snapshot(monkeypatch, root):
    legacy = (ROOT / "tests/fixtures/iteration7-dashboard-v1.html").read_text()
    assert (
        hashlib.sha256(legacy.encode()).hexdigest() == dashboard.LEGACY_TEMPLATE_SHA256
    )
    with monkeypatch.context() as context:
        context.setattr(dashboard, "PAGE", legacy)
        html = publish(context, root)
    return html


def test_legacy_snapshot_offline_presentation_preserves_immutable_evidence(
    tmp_path, monkeypatch, capsys
):
    html = legacy_snapshot(monkeypatch, tmp_path)
    pointer = (tmp_path / "storage/discovery/current.json").read_bytes()
    before = {p.name: p.read_bytes() for p in html.parent.iterdir()}
    monkeypatch.setattr(
        assessment, "_github_payload", lambda _: pytest.fail("offline network")
    )
    monkeypatch.delenv("DISPLAY", raising=False)
    monkeypatch.delenv("WAYLAND_DISPLAY", raising=False)
    assert dashboard.main(["--root", str(tmp_path), "report"]) == 0
    output = capsys.readouterr().out
    report = next((tmp_path / "storage/discovery").glob("presentation-*.html"))
    assert str(report) in output
    saved_path, saved = dashboard.load_snapshot(tmp_path)
    assert report.read_text() == dashboard.build_reports(saved)["dashboard.html"]
    assert (
        payload(report.read_text())["competition_acquisition"]["observed_at"]
        == fixtures.WHEN
    )
    assert {p.name: p.read_bytes() for p in html.parent.iterdir()} == before
    assert (tmp_path / "storage/discovery/current.json").read_bytes() == pointer
    assert saved_path == html.parent
    assert dashboard.main(["--root", str(tmp_path), "inspect", "JSP-000161"]) == 0
    assert json.loads(capsys.readouterr().out)["problem"]["jsp_id"] == "JSP-000161"
    assert dashboard.main(["--root", str(tmp_path), "report"]) == 0
    assert len(list((tmp_path / "storage/discovery").glob("presentation-*.html"))) == 1


@pytest.mark.parametrize("mutation", ["script", "payload", "hash", "credential"])
def test_legacy_snapshot_cannot_bypass_integrity_checks(
    tmp_path, monkeypatch, mutation
):
    html = legacy_snapshot(monkeypatch, tmp_path)
    if mutation == "script":
        html.write_text(html.read_text().replace("render();", "alert(1);render();", 1))
    elif mutation == "payload":
        html.write_text(
            html.read_text().replace('"complete":true', '"complete":false', 1)
        )
    elif mutation == "credential":
        token = "ghp_" + "TESTONLY" * 5
        monkeypatch.setenv("GITHUB_TOKEN", token)
        html.write_text(html.read_text().replace("</body>", token + "</body>"))
    else:
        html.write_text("tampered")
    if mutation != "hash":
        manifest_path = html.parent / "manifest.json"
        manifest = json.loads(manifest_path.read_text())
        manifest["sha256"]["dashboard.html"] = hashlib.sha256(
            html.read_bytes()
        ).hexdigest()
        manifest_path.write_text(json.dumps(manifest))
    with pytest.raises(ValueError):
        dashboard.load_snapshot(tmp_path)


@pytest.mark.parametrize("mutation", ["tamper", "symlink", "publish"])
def test_offline_presentation_failure_preserves_snapshot(
    tmp_path, monkeypatch, mutation
):
    html = legacy_snapshot(monkeypatch, tmp_path)
    path, saved = dashboard.load_snapshot(tmp_path)
    pointer = (tmp_path / "storage/discovery/current.json").read_bytes()
    before = {p.name: p.read_bytes() for p in html.parent.iterdir()}
    if mutation == "publish":
        monkeypatch.setattr(
            dashboard.os,
            "replace",
            lambda *_: (_ for _ in ()).throw(OSError("publication failed")),
        )
    else:
        report = dashboard.saved_report(tmp_path, path, saved)
        report.unlink()
        if mutation == "tamper":
            report.write_text("tampered")
        else:
            report.symlink_to(tmp_path / "outside")
    with pytest.raises((ValueError, OSError)):
        dashboard.saved_report(tmp_path, path, saved)
    assert (tmp_path / "storage/discovery/current.json").read_bytes() == pointer
    assert {p.name: p.read_bytes() for p in html.parent.iterdir()} == before


def award_amount_records():
    base = discovery.normalize_register(
        fixtures.AWARDS, "announced", fixtures.SHA, fixtures.WHEN, "awards/README.md"
    )[0]
    publication = fixtures.evidence(url=base["url"])
    candidate = {
        **base,
        "state": "candidate",
        "url": base["url"].replace("/awards/README.md", "/candidates/README.md"),
        "published_amount": "9999",
        "currency": "JPY",
    }
    candidate["publication_evidence"] = fixtures.evidence(url=candidate["url"])
    return [
        {
            **base,
            "published_amount": "1234.50",
            "currency": "USD",
            "publication_evidence": publication,
        },
        {
            **base,
            "role": "solver",
            "published_amount": "250",
            "currency": "EUR",
            "publication_evidence": publication,
        },
        {**base, "recipients": "Additional formalizer"},
        {**base, "jsp_id": "JSP-000161"},
        candidate,
        {**candidate, "jsp_id": "JSP-000089"},
    ]


@pytest.mark.parametrize("complete", [False, True])
def test_award_presentation_retains_only_validated_evidence_and_unknowns(complete):
    saved = inputs()
    saved["awards"]["acquisition"]["complete"] = complete
    saved["awards"]["records"] = award_amount_records()
    saved["scanner"]["records"][0]["official"]["lean_proof"] = {
        "normalized": "Unknown",
        "raw": "Unknown",
    }
    rendered = payload(dashboard.build_reports(saved)["dashboard.html"])
    rows = {r["jsp_id"]: r for r in rendered["rows"]}
    assert rows["JSP-000475"]["filters"]["award_state"] == "announced"
    assert len(rows["JSP-000475"]["awards"]) == 4
    assert {a["currency"] for a in rows["JSP-000475"]["published_amounts"]} == {
        "USD",
        "EUR",
        "JPY",
    }
    assert rows["JSP-000161"]["published_amounts"] is None
    assert rows["JSP-000089"]["filters"]["award_state"] == "candidate"
    assert rows["JSP-000001"]["filters"]["award_state"] == (
        "none_in_scope" if complete else "unknown"
    )
    assert rows["JSP-000161"]["filters"]["lean_status"] == "Unknown"
    assert all(
        dashboard.safe_link(a["url"]) for r in rows.values() for a in r["awards"]
    )


def count_filter_observations():
    result = {"pull_requests": [], "issues": []}
    cases = [(i, i, 11 - i) for i in range(12)] + [(12, 2, 10)]
    for index, prs, issues in cases:
        jsp_id = f"JSP-{index + 1:06d}"
        for category, count in [("pull_requests", prs), ("issues", issues)]:
            for offset in range(count):
                result[category].append(
                    fixtures.observation(
                        jsp_id,
                        80_000 + index * 20 + offset,
                        category=category,
                        submission_kind="lean",
                    )
                )
    return result


@pytest.mark.parametrize("complete", [False, True])
def test_count_fixture_preserves_exact_matches_and_coverage(complete):
    saved = inputs()
    saved["scanner"] = scan_problem_bank(ROOT / "docs/vendor/jsp")
    saved["competition"] = fixtures.competition(complete=complete)
    saved["competition"]["observations"] = count_filter_observations()
    rendered = payload(dashboard.build_reports(saved)["dashboard.html"])
    rows = {r["jsp_id"]: r for r in rendered["rows"]}
    assert len(rows) == 1022
    for count in (0, 1, 9, 10, 11):
        record = rows[f"JSP-{count + 1:06d}"]
        assert sum(o["kind"] == "pull_request" for o in record["competition"]) == count
        assert sum(o["kind"] == "issue" for o in record["competition"]) == 11 - count
    assert rows["JSP-000014"]["competition_state"] == (
        "NONE_IN_SCOPE" if complete else "UNKNOWN"
    )
    assert rendered["competition_complete"] is complete
    assert all(
        dashboard.safe_link(o["url"]) for r in rows.values() for o in r["competition"]
    )


def lifecycle_observations():
    return {
        "pull_requests": [
            fixtures.observation(
                "JSP-000161", 1248, state="open", submission_kind="lean"
            ),
            fixtures.observation(
                "JSP-000161", 1249, state="merged", submission_kind="administrative"
            ),
            fixtures.observation(
                "JSP-000161",
                1250,
                state="closed-unmerged",
                submission_kind="lean",
                proof_sources=[fixtures.source()],
            ),
            fixtures.observation(
                "JSP-000475",
                1269,
                state="closed-unmerged",
                proof_sources=[fixtures.source()],
            ),
            fixtures.observation(
                "JSP-000089", 80_999, state="merged", submission_kind="administrative"
            ),
        ],
        "issues": [
            fixtures.observation(
                "JSP-000161", 33, category="issues", submission_kind="lean"
            )
        ],
    }


@pytest.mark.parametrize("complete", [False, True])
def test_lifecycle_presentation_preserves_claims_reviews_and_git_states(complete):
    saved = inputs()
    saved["competition"] = fixtures.competition(complete=complete)
    saved["competition"]["observations"] = lifecycle_observations()
    saved["research"] = fixtures.research(fixtures.verified_review())
    html_rows = {
        r["jsp_id"]: r
        for r in payload(dashboard.build_reports(saved)["dashboard.html"])["rows"]
    }
    first = html_rows["JSP-000161"]
    assert {
        o["state"] for o in first["competition"] if o["kind"] == "pull_request"
    } == {"open", "merged", "closed-unmerged"}
    administrative = next(o for o in first["competition"] if o["number"] == 1249)
    assert administrative["proof_state"] == "claimed"
    assert administrative["submission_kind"] == "administrative"
    assert html_rows["JSP-000089"]["competition_state"] == (
        "NONE_IN_SCOPE" if complete else "UNKNOWN"
    )
    assert first["competition_state"] == "CONTESTED"
    assert first["proof_reviews"][0]["state"] == "independently_verified"
    assert html_rows["JSP-000475"]["competition"][0]["state"] == "closed-unmerged"
    assert html_rows["JSP-000475"]["competition"][0]["proof_state"] == "source_linked"
