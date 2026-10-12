from __future__ import annotations

import base64
import copy
import csv
import io
import json
import os
import subprocess
import sys
from email.message import Message
from http.client import HTTPMessage
from pathlib import Path
from urllib.error import HTTPError
from urllib.request import Request

import pytest

from beejsp import assessment as old
from beejsp import discovery as new
from beejsp.scanner import scan_problem_bank

WHEN = "2026-10-12T00:00:00Z"
SHA = "a" * 40
ROOT = "https://github.com/TheJustinSunPrize/awards"


def evidence(**kwargs):
    return {
        "url": "https://example.test/review",
        "observed_at": WHEN,
        "rationale": "Reviewed exact source and recorded findings",
        **kwargs,
    }


def scanner():
    source = {"upstream_ref": "main", "upstream_commit": SHA}
    return {
        "schema_version": 1,
        "is_complete": True,
        "source": source,
        "candidate_ids": ["JSP-000161", "JSP-000475"],
        "records": [
            {
                "jsp_id": jsp,
                "title": title,
                "source": source,
                "official": {
                    "current_status": {"normalized": status, "raw": status},
                    "lean_proof": {"normalized": lean, "raw": lean},
                    "fields": {
                        "Mathematical area": "Combinatorics",
                        "Historical bounty": "$1000 third-party historical bounty",
                    },
                },
            }
            for jsp, title, status, lean in [
                ("JSP-000161", "Erdos example", "Solved", "No"),
                ("JSP-000475", "Second example", "Solved", "No"),
                ("JSP-000089", "Historical example", "Solved", "Yes"),
                ("JSP-000001", "Open example", "Open", "No"),
            ]
        ],
    }


def competition(complete=True):
    return {
        "schema_version": 2,
        "acquisition": {
            "repository": old.OFFICIAL_REPOSITORY,
            "observed_at": WHEN,
            "complete": complete,
            "scopes": {"issues": complete, "pull_requests": complete},
            "search_scope": "all repository PRs and Issues",
        },
        "observations": {"pull_requests": [], "issues": []},
    }


def observation(
    jsp="JSP-000161", number=1248, category="pull_requests", state="open", **kwargs
):
    return {
        "number": number,
        "title": jsp + " Lean formalization",
        "jsp_ids": [jsp],
        "url": f"{ROOT}/{'pull' if category == 'pull_requests' else 'issues'}/{number}",
        "state": state,
        **kwargs,
    }


def source():
    return {
        "url": f"https://github.com/plby/lean-proofs/blob/{SHA}/Main.lean",
        "repository": "plby/lean-proofs",
        "commit": SHA,
        "branch": None,
        "file": "Main.lean",
        "theorem": "main",
    }


def research(review=None, **kwargs):
    return {
        "schema_version": 2,
        "candidates": [
            {
                "jsp_id": "JSP-000161",
                "proof_reviews": [review] if review else [],
                **kwargs,
            }
        ],
    }


def row(result, jsp="JSP-000161"):
    return next(
        r for r in result["selected"] + result["excluded"] if r["jsp_id"] == jsp
    )


@pytest.mark.parametrize(
    ("jsp", "number"),
    [("JSP-000161", 1248), ("JSP-000475", 1269), ("JSP-000089", 5006)],
)
def test_regression_claims_contested_even_closed(jsp, number):
    capture = competition()
    capture["observations"]["pull_requests"] = [
        observation(jsp, number, state="closed-unmerged", proof_sources=[source()])
    ]
    result = new.inspect_problem(scanner(), capture, jsp)
    item = result["problem"]
    assert item["competition_state"] == "CONTESTED"
    assert item["decision"] == "REVIEW_REQUIRED"
    assert item["competition"][0]["proof_state"] == "source_linked"
    assert item["competition"][0]["observed_at"] == WHEN
    assert item["competition"][0]["url"] == f"{ROOT}/pull/{number}"
    assert item["official_acceptance"] == "unknown"


def test_all_records_and_unknowns_not_historical_subset():
    result = new.select(scanner(), competition())
    assert len(result["selected"]) == 4
    assert row(result, "JSP-000001")["filters"]["problem_status"] == "Open"
    assert row(result)["published_amounts"] is None
    assert row(result)["research"]["difficulty"] == {"value": "unknown"}
    assert row(result)["historical_bounty"].startswith("$1000")
    assert not any(r["decision"].startswith("GO") for r in result["selected"])


def test_issue_queries_dedupe_aliases_and_conflicting_identity():
    capture = competition()
    items = [
        observation(number=10, category="issues"),
        observation(number=11, category="issues", state="closed"),
        observation(
            number=12, category="issues", jsp_ids=[], title="Erdos example notes"
        ),
        observation("JSP-000475", 13, "issues", title="Erdos example"),
        observation(
            number=14, category="issues", jsp_ids=[], title="Erdos 7", erdos_ids=["7"]
        ),
    ]
    capture["observations"]["issues"] = items + [copy.deepcopy(items[0])]
    findings = research(aliases=[evidence(erdos_id="7")])
    result = new.inspect_problem(
        scanner(), capture, "JSP-000161", research=findings, kind="issue", state="open"
    )
    matches = result["problem"]["competition"]
    assert [i["number"] for i in matches] == [10, 12, 14]
    assert [i["match"] for i in matches] == [
        "exact_jsp_id",
        "supplementary_title",
        "evidence_backed_erdos_alias",
    ]
    closed = new.inspect_problem(
        scanner(), capture, "JSP-000161", kind="issue", state="closed"
    )
    assert [i["number"] for i in closed["problem"]["competition"]] == [11]
    capture["observations"]["issues"][-1]["state"] = "closed"
    with pytest.raises(old.AssessmentError, match="duplicate"):
        new.select(scanner(), capture)


def test_exact_id_collision_and_alias_collision():
    raw = {
        "number": 1,
        "title": "JSP-0001610 and JSP-000475",
        "body": "notJSP-000161",
        "html_url": f"{ROOT}/pull/1",
        "state": "open",
    }
    assert old._normalize_github_observation(raw, "pull_requests")["jsp_ids"] == [
        "JSP-000475"
    ]
    findings = research(aliases=[evidence(erdos_id="7")])
    findings["candidates"].append(
        {"jsp_id": "JSP-000475", "aliases": [evidence(erdos_id="7")]}
    )
    with pytest.raises(old.AssessmentError, match="ambiguous"):
        new.select(scanner(), competition(), research=findings)


@pytest.mark.parametrize("complete", [False, True])
def test_capture_completeness_separate_from_scoped_success(complete):
    capture = competition(complete)
    if complete:
        capture.update(schema_version=2)
        capture["acquisition"]["scopes"] = {"issues": True}
    result = new.select(scanner(), capture)
    assert result["competition_complete"] is False
    assert row(result)["competition_state"] == "UNKNOWN"
    assert "incomplete competition" in " ".join(row(result)["uncertainty"])


@pytest.mark.parametrize(
    "state",
    ["partial", "invalid", "unresolved", "reproduced", "independently_verified"],
)
def test_proof_review_gates_and_states(state):
    review = evidence(
        subject_url=f"{ROOT}/pull/1248", state=state, proof_source=source()
    )
    if state in {"reproduced", "independently_verified"}:
        review.update(build="passed", build_evidence=evidence())
    if state == "independently_verified":
        review.update(
            statement_fidelity="exact",
            axiom_audit="passed",
            placeholders="absent",
            reviewer="Independent verifier",
            statement_evidence=evidence(),
            axiom_evidence=evidence(),
        )
    capture = competition()
    capture["observations"]["pull_requests"] = [observation()]
    item = row(new.select(scanner(), capture, research=research(review)))
    expected = (
        "VERIFIED"
        if state == "independently_verified"
        else "REVIEWED"
        if state in {"partial", "invalid"}
        else "CONTESTED"
    )
    assert item["competition_state"] == expected
    assert item["proof_reviews"][0]["rationale"]
    if state == "independently_verified":
        for key, bad in [
            ("statement_fidelity", "weaker"),
            ("axiom_audit", "unexpected"),
            ("placeholders", "present"),
            ("build", "environmental_failure"),
        ]:
            invalid = {**review, key: bad}
            with pytest.raises(old.AssessmentError):
                new.select(scanner(), capture, research=research(invalid))
    if state == "reproduced":
        assert item["proof_reviews"][0]["statement_fidelity"] == "unknown"


def test_environmental_build_failure_stays_unresolved():
    review = evidence(
        subject_url=f"{ROOT}/pull/1248",
        state="unresolved",
        proof_source=source(),
        build="environmental_failure",
    )
    capture = competition()
    capture["observations"]["pull_requests"] = [observation(state="merged")]
    item = row(new.select(scanner(), capture, research=research(review)))
    assert item["competition_state"] == "CONTESTED"
    assert item["competition"][0]["proof_review"]["build"] == "environmental_failure"
    assert item["official_acceptance"] == "unknown"


def test_profiles_filters_ranking_limits_and_deterministic_csv():
    findings = research(
        difficulty=evidence(value="extreme"),
        scientific_significance=evidence(value="high"),
        prize_potential=evidence(value="high"),
        solution={"kind": "complete", "sources": [evidence()]},
    )
    profile = {
        **new.DEFAULT_PROFILE,
        "limit": 1,
        "problem_status": ["Solved"],
        "lean_status": ["No"],
        "area": ["Combinatorics"],
        "difficulty": ["extreme"],
        "solution_kind": ["complete"],
        "competition_state": ["NONE_IN_SCOPE"],
        "historical_bounty": ["known"],
        "published_amount": ["unknown"],
        "award_state": ["unknown"],
    }
    result = new.select(scanner(), competition(), research=findings, profile=profile)
    assert [r["jsp_id"] for r in result["selected"]] == ["JSP-000161"]
    assert result["selected"][0]["rank"] == 1
    repeat = new.select(scanner(), competition(), research=findings, profile=profile)
    assert old.render_json(result) == old.render_json(repeat)
    assert new.render_csv(result) == new.render_csv(repeat)
    parsed = list(csv.DictReader(io.StringIO(new.render_csv(result))))
    assert parsed[0]["published_amounts"] == "null"
    assert json.loads(parsed[0]["competition_acquisition"])["observed_at"] == WHEN
    assert all(i["reasons"] for i in result["excluded"])
    assert row(
        new.select(
            scanner(), competition(), research=findings, profile=new.HIGH_VALUE_PROFILE
        )
    )["included"]
    with pytest.raises(old.AssessmentError):
        new.select(
            scanner(), competition(), research=research(difficulty={"value": "low"})
        )
    for mutation in [
        {"limit": 0},
        {"difficulty": ["easy"]},
        {"unexpected": True},
        {"area": []},
    ]:
        with pytest.raises(old.AssessmentError):
            new.select(
                scanner(), competition(), profile={**new.DEFAULT_PROFILE, **mutation}
            )


def test_csv_formula_injection_guard():
    bank = scanner()
    bank["records"][0]["title"] = '=WEBSERVICE("https://evil.test")'
    output = new.render_csv(new.select(bank, competition()))
    parsed = list(csv.DictReader(io.StringIO(output)))
    assert next(i for i in parsed if i["jsp_id"] == "JSP-000161")["title"].startswith(
        "'="
    )


def test_capture_v2_sources_predecessors_and_issue_shadows(monkeypatch):
    raw = {
        "number": 1248,
        "title": "JSP-000161",
        "body": f"Lean proof https://github.com/plby/lean-proofs/blob/{SHA}/Main.lean#main replaces {ROOT}/pull/1200; Erdos #7",
        "html_url": f"{ROOT}/pull/1248",
        "state": "closed",
    }
    pages = iter(
        [
            ([raw, copy.deepcopy(raw)], None),
            ([{"pull_request": {}, "number": 1248}], None),
        ]
    )
    monkeypatch.setattr(old, "_github_page", lambda _: next(pages))
    captured = old.capture_github(evidence_version=2)
    assert captured["schema_version"] == 2
    assert captured["acquisition"]["complete"]
    assert len(captured["observations"]["pull_requests"]) == 1
    item = captured["observations"]["pull_requests"][0]
    assert item["proof_sources"][0]["commit"] == SHA
    assert item["proof_sources"][0]["theorem"] == "main"
    assert item["erdos_ids"] == ["7"]
    assert item["linked_submissions"] == [f"{ROOT}/pull/1200"]
    assert not captured["observations"]["issues"]
    new.select(scanner(), captured)


def test_pagination_cycle_page_limit_and_rate_limit(monkeypatch):
    monkeypatch.setattr(old, "_github_page", lambda _: ([], "https://loop"))
    captured = old.capture_github(evidence_version=2)
    assert not captured["acquisition"]["complete"]
    assert "cycle" in captured["acquisition"]["error"]
    monkeypatch.setattr(old, "MAX_GITHUB_PAGES", 1)
    captured = old.capture_github()
    assert not captured["acquisition"]["complete"]

    def rate_limit(_):
        raise HTTPError("https://api.github.com", 403, "rate limited", Message(), None)

    monkeypatch.setattr(old, "_github_page", rate_limit)
    captured = old.capture_github()
    assert not captured["acquisition"]["complete"]
    assert row(new.select(scanner(), captured))["competition_state"] == "UNKNOWN"


def test_scoped_issue_capture(monkeypatch):
    calls = []

    def page(address):
        calls.append(address)
        return [], None

    monkeypatch.setattr(old, "_github_page", page)
    capture = old.capture_github(evidence_version=2, kind="issues")
    assert len(calls) == 1 and "/issues?" in calls[0]
    assert capture["acquisition"]["scopes"] == {"issues": True}
    assert not new.select(scanner(), capture)["competition_complete"]


CANDIDATES = """| Problem ID | Solver review start (UTC) | Mathematical solver | Lean review start (UTC) | Lean formalizer |
| --- | --- | --- | --- | --- |
| [JSP-000161](../problems/example.md#JSP-000161) | 2026-10-01 | Solver | 2026-10-02 | Formalizer |
"""
AWARDS = """| Problem ID | Contribution type | Recipients | Public-review start (UTC) | Public-review end (UTC) |
| --- | --- | --- | --- | --- |
| JSP-000475 | Lean formalization | Formalizer | 2026-09-19 | 2026-10-03 |
"""


def test_official_capture_pinned_registers_and_unknown_amounts(monkeypatch):
    calls = []

    def payload(address):
        calls.append(address)
        if "/commits/" in address:
            return {"sha": SHA}, ""
        path = (
            "candidates/README.md" if "/candidates/" in address else "awards/README.md"
        )
        content = CANDIDATES if path.startswith("candidates") else AWARDS
        return {
            "path": path,
            "encoding": "base64",
            "content": base64.b64encode(content.encode()).decode(),
        }, ""

    monkeypatch.setattr(old, "_github_payload", payload)
    capture = new.capture_records()
    assert capture["acquisition"]["complete"]
    assert all(f"ref={SHA}" in c for c in calls[1:])
    assert [r["role"] for r in capture["records"]].count("formalizer") == 2
    result = new.select(scanner(), competition(), awards=capture)
    assert row(result)["filters"]["award_state"] == "candidate"
    assert row(result, "JSP-000475")["filters"]["award_state"] == "announced"
    assert row(result)["published_amounts"] is None
    assert row(result)["official_acceptance"] == "recorded"
    enriched = copy.deepcopy(capture)
    enriched["records"][0].update(
        official_award_level="Level I",
        published_amount="1000.00",
        currency="USD",
        publication_evidence=evidence(url=f"{ROOT}/blob/{SHA}/awards/README.md"),
    )
    assert new.validate_awards(enriched)[0]
    enriched["records"][0]["published_amount"] = 0
    with pytest.raises(old.AssessmentError):
        new.validate_awards(enriched)


@pytest.mark.parametrize(
    "content",
    [
        "",
        CANDIDATES.replace("Problem ID", "Different header"),
        CANDIDATES.replace("JSP-000161", "JSP-0001610"),
    ],
)
def test_malformed_official_registers_fail(content):
    with pytest.raises(old.AssessmentError):
        new.normalize_register(content, "candidate", SHA, WHEN, "candidates/README.md")


def test_missing_award_register_does_not_infer_absence(monkeypatch):
    def missing(_):
        raise HTTPError("https://api.github.com", 404, "not found", Message(), None)

    monkeypatch.setattr(old, "_github_payload", missing)
    awards = new.capture_records()
    assert not awards["acquisition"]["complete"]
    assert (
        row(new.select(scanner(), competition(), awards=awards))["filters"][
            "award_state"
        ]
        == "unknown"
    )


def test_api_url_redirect_size_and_pagination_security(monkeypatch):
    for address in [
        "file:///tmp/x",
        "https://api.github.com.evil.test/repos/TheJustinSunPrize/awards/pulls",
        "https://user:secret@api.github.com/repos/TheJustinSunPrize/awards/pulls",
    ]:
        with pytest.raises(old.AssessmentError):
            old._github_payload(address)
    with pytest.raises(old.AssessmentError, match="redirect"):
        old._NoRedirect().redirect_request(
            Request("https://api.github.com"),
            io.BytesIO(),
            302,
            "",
            HTTPMessage(),
            "https://evil.test",
        )

    class Response:
        headers = {}

        def __enter__(self):
            return self

        def __exit__(self, *args):
            pass

        def read(self, size):
            return b"x" * size

    class Opener:
        def open(self, *args, **kwargs):
            return Response()

    monkeypatch.setattr(old, "build_opener", lambda _: Opener())
    with pytest.raises(old.AssessmentError, match="size limit"):
        old._github_payload(
            f"https://api.github.com/repos/{old.OFFICIAL_REPOSITORY}/pulls"
        )
    monkeypatch.setattr(
        old, "_github_payload", lambda _: ([], '<https://evil.test/pulls>; rel="next"')
    )
    with pytest.raises(old.AssessmentError, match="pagination"):
        old._github_page(
            f"https://api.github.com/repos/{old.OFFICIAL_REPOSITORY}/pulls"
        )


def test_invalid_saved_sources_fail_closed():
    for changes in [
        {"commit": "short"},
        {"file": "../Main.lean"},
        {"url": "https://user:secret@github.com/plby/lean-proofs"},
        {"url": "https://evil.test/plby/lean-proofs"},
    ]:
        with pytest.raises((old.AssessmentError, ValueError)):
            new.proof_source({**source(), **changes})


def test_cli_offline_profile_and_inspection_and_path_collision(tmp_path, monkeypatch):
    def no_network(*args, **kwargs):
        pytest.fail("offline operation attempted network")

    monkeypatch.setattr(old, "_github_payload", no_network)
    bank_path, competition_path = tmp_path / "bank.json", tmp_path / "competition.json"
    output, tabular = tmp_path / "result.json", tmp_path / "result.csv"
    bank_path.write_text(json.dumps(scanner()))
    competition_path.write_text(json.dumps(competition()))
    profile = tmp_path / "profile.toml"
    profile.write_text(
        'schema_version = 2\nname = "custom"\nlimit = 2\nlean_status = ["No"]\n'
    )
    common = [
        "--scanner",
        str(bank_path),
        "--competition",
        str(competition_path),
        "--output",
        str(output),
        "--csv",
        str(tabular),
    ]
    assert old.main(["select", *common, "--profile", str(profile)]) == 0
    assert len(json.loads(output.read_text())["selected"]) == 2
    assert (
        old.main(
            [
                "inspect",
                *common,
                "--jsp",
                "JSP-000161",
                "--kind",
                "issue",
                "--state",
                "open",
            ]
        )
        == 0
    )
    assert json.loads(output.read_text())["problem"]["jsp_id"] == "JSP-000161"
    before = bank_path.read_bytes()
    with pytest.raises(SystemExit) as failure:
        old.main(
            [
                "select",
                "--scanner",
                str(bank_path),
                "--competition",
                str(competition_path),
                "--output",
                str(bank_path),
            ]
        )
    assert failure.value.code == 2
    assert bank_path.read_bytes() == before


def test_real_vendor_full_catalog_selection():
    bank = scan_problem_bank(Path("docs/vendor/jsp"))
    report = new.select(
        bank, competition(), profile={**new.DEFAULT_PROFILE, "limit": 1000}
    )
    assert len(report["selected"]) + len(report["excluded"]) == len(bank["records"])
    assert old.render_json(report) == old.render_json(
        new.select(bank, competition(), profile={**new.DEFAULT_PROFILE, "limit": 1000})
    )


def test_official_pr_json_source_metadata_regression():
    for jsp, number, theorem_file in [
        ("JSP-000161", 1248, "src/latest/ErdosProblems/Erdos163.lean"),
        ("JSP-000475", 1269, "src/latest/ErdosProblems/Erdos586.lean"),
    ]:
        normalized = observation(jsp, number)
        raw = {
            "body": "## Proof source\n```json\n"
            + json.dumps(
                [
                    {
                        "repository": "https://github.com/plby/lean-proofs",
                        "branch": "main",
                        "commit": "8822f7ddef30fadbd92e1c6ab4ed897af356af5e",
                    }
                ]
            )
            + "\n```\n- Theorem/file: `"
            + theorem_file
            + "`",
            "created_at": WHEN,
        }
        enriched = new.enrich_observation(normalized, raw, WHEN)
        assert len(enriched["proof_sources"]) == 1
        assert (
            enriched["proof_sources"][0]["commit"]
            == "8822f7ddef30fadbd92e1c6ab4ed897af356af5e"
        )
        assert enriched["proof_sources"][0]["branch"] == "main"
        assert enriched["proof_sources"][0]["file"] == theorem_file
        assert enriched["source_timestamps"]["created_at"] == WHEN


def test_saved_iteration_three_reproduces_exactly():
    root = Path("docs/evidence/iteration-3")
    values = {
        name: json.loads((root / f"{name}.json").read_text())
        for name in ("scanner", "research", "competition", "assessment")
    }
    assert (
        old.assess(values["scanner"], values["research"], values["competition"])
        == values["assessment"]
    )
    upgraded = new.select(values["scanner"], values["competition"])
    assert upgraded["competition_complete"] is False
    historical = row(upgraded, "JSP-000089")
    assert historical["competition_state"] == "CONTESTED"
    assert historical["decision"] == "REVIEW_REQUIRED"
    assert "coverage" in " ".join(historical["uncertainty"])


@pytest.mark.parametrize("jsp_id", ["JSP-000161", "JSP-000475"])
def test_saved_iteration_three_cannot_clear_uncovered_problem(jsp_id):
    capture = json.loads(Path("docs/evidence/iteration-3/competition.json").read_text())
    bank = scan_problem_bank(Path("docs/vendor/jsp"))
    assert capture["acquisition"]["complete"] is True
    report = new.inspect_problem(bank, capture, jsp_id)
    assert report["competition_complete"] is False
    assert report["competition_acquisition"] == capture["acquisition"]
    assert report["problem"]["competition"] == []
    assert report["problem"]["competition_state"] == "UNKNOWN"
    assert "legacy v1" in " ".join(report["problem"]["uncertainty"])
    assert "coverage" in " ".join(report["problem"]["uncertainty"])
    repeated = new.inspect_problem(bank, capture, jsp_id)
    assert old.render_json(report) == old.render_json(repeated)
    assert new.render_csv(report) == new.render_csv(repeated)


def test_legacy_scope_prose_cannot_certify_negative_coverage():
    capture = competition()
    capture["schema_version"] = 1
    capture["acquisition"].pop("scopes", None)
    capture["acquisition"]["search_scope"] = "all repository PRs and Issues"
    report = new.select(scanner(), capture)
    assert report["competition_complete"] is False
    assert row(report)["competition_state"] == "UNKNOWN"
    capture["observations"]["pull_requests"] = [observation()]
    positive = new.select(scanner(), capture)
    assert positive["competition_complete"] is False
    assert row(positive)["competition_state"] == "CONTESTED"
    assert row(positive)["competition"][0]["number"] == 1248


def test_complete_version_two_can_establish_negative_coverage():
    capture = competition()
    capture["schema_version"] = 2
    capture["acquisition"]["scopes"] = {"issues": True, "pull_requests": True}
    report = new.select(scanner(), capture)
    assert report["competition_complete"] is True
    assert row(report)["competition_state"] == "NONE_IN_SCOPE"


def test_issue_proof_claim_and_uncertain_title_require_review():
    capture = competition()
    capture["observations"]["issues"] = [
        observation(number=1, category="issues", submission_kind="lean")
    ]
    assert row(new.select(scanner(), capture))["competition_state"] == "CONTESTED"
    capture["observations"]["issues"] = [
        observation(number=1, category="issues", jsp_ids=[], title="Erdos example")
    ]
    assert row(new.select(scanner(), capture))["competition_state"] == "UNKNOWN"


def test_multi_problem_submission_does_not_share_review_decisions():
    capture = competition()
    capture["observations"]["pull_requests"] = [
        observation(jsp_ids=["JSP-000161", "JSP-000475"])
    ]
    review = evidence(subject_url=f"{ROOT}/pull/1248", state="partial")
    result = new.select(scanner(), capture, research=research(review))
    assert row(result)["competition"][0]["proof_state"] == "partial"
    assert row(result, "JSP-000475")["competition"][0]["proof_state"] == "claimed"


@pytest.mark.parametrize(
    "payload",
    [
        {},
        [None],
        [
            {
                "number": 1,
                "title": "JSP-000161",
                "body": 1,
                "html_url": f"{ROOT}/pull/1",
                "state": "open",
            }
        ],
    ],
)
def test_malformed_api_pages_and_records_fail_closed(payload, monkeypatch):
    monkeypatch.setattr(old, "_github_payload", lambda _: (payload, ""))
    captured = old.capture_github(evidence_version=2)
    assert not captured["acquisition"]["complete"]
    assert captured["acquisition"]["error"]
    assert row(new.select(scanner(), captured))["competition_state"] == "UNKNOWN"


def test_pagination_cannot_change_query_scope(monkeypatch):
    monkeypatch.setattr(
        old,
        "_github_payload",
        lambda _: (
            [],
            f'<https://api.github.com/repos/{old.OFFICIAL_REPOSITORY}/pulls?state=open&per_page=100&page=2>; rel="next"',
        ),
    )
    with pytest.raises(old.AssessmentError, match="scope"):
        old._github_page(
            f"https://api.github.com/repos/{old.OFFICIAL_REPOSITORY}/pulls?state=all&per_page=100"
        )


def test_empty_selection_explains_all_exclusions():
    result = new.select(
        scanner(), competition(), profile={**new.DEFAULT_PROFILE, "difficulty": ["low"]}
    )
    assert not result["selected"]
    assert len(result["excluded"]) == 4
    assert all("difficulty=unknown" in r["reasons"][0] for r in result["excluded"])


def test_csv_output_cannot_overwrite_profile(tmp_path):
    bank_path = tmp_path / "bank.json"
    capture_path = tmp_path / "capture.json"
    profile_path = tmp_path / "profile.toml"
    bank_path.write_text(json.dumps(scanner()))
    capture_path.write_text(json.dumps(competition()))
    profile_path.write_text('schema_version = 2\nname = "custom"\nlimit = 2\n')
    original = profile_path.read_bytes()
    with pytest.raises(SystemExit) as failure:
        old.main(
            [
                "select",
                "--scanner",
                str(bank_path),
                "--competition",
                str(capture_path),
                "--profile",
                str(profile_path),
                "--output",
                str(tmp_path / "out.json"),
                "--csv",
                str(profile_path),
            ]
        )
    assert failure.value.code == 2
    assert profile_path.read_bytes() == original
    assert not (tmp_path / "out.json").exists()


def test_published_official_amount_and_level_filters_keep_provenance():
    records = new.normalize_register(AWARDS, "announced", SHA, WHEN, "awards/README.md")
    records[0].update(
        official_award_level="Published Level",
        published_amount="1234.50",
        currency="USD",
        publication_evidence=evidence(url=f"{ROOT}/blob/{SHA}/awards/README.md"),
    )
    awards = {
        "schema_version": 2,
        "acquisition": {
            "repository": old.OFFICIAL_REPOSITORY,
            "observed_at": WHEN,
            "complete": True,
            "search_scope": "official registers",
            "upstream_commit": SHA,
        },
        "records": records,
    }
    profile = {
        **new.DEFAULT_PROFILE,
        "published_amount": ["known"],
        "award_level": ["Published Level"],
        "award_state": ["announced"],
    }
    result = new.select(scanner(), competition(), awards=awards, profile=profile)
    assert [r["jsp_id"] for r in result["selected"]] == ["JSP-000475"]
    assert result["selected"][0]["published_amounts"][0]["amount"] == "1234.50"
    assert result["selected"][0]["awards"][0]["publication_evidence"]["rationale"]
    assert row(result)["published_amounts"] is None


def test_unsupported_solution_and_unreviewed_complete_claim_remain_visible():
    capture = competition()
    capture["observations"]["pull_requests"] = [
        observation(title="JSP-000161 complete Lean proof without supplied sources")
    ]
    findings = research(solution={"kind": "unsupported", "sources": [evidence()]})
    result = new.select(scanner(), capture, research=findings)
    assert row(result)["competition_state"] == "CONTESTED"
    assert row(result)["competition"][0]["proof_state"] == "claimed"
    assert row(result)["solution"]["kind"] == "unsupported"


def verified_review(**kwargs):
    return evidence(
        subject_url=f"{ROOT}/pull/1248",
        state="independently_verified",
        proof_source=source(),
        build="passed",
        build_evidence=evidence(),
        statement_fidelity="exact",
        statement_evidence=evidence(),
        axiom_audit="passed",
        axiom_evidence=evidence(),
        placeholders="absent",
        reviewer="Independent verifier",
        **kwargs,
    )


@pytest.mark.parametrize(
    "subject", [f"{ROOT}/pull/1248", "https://github.com/plby/lean-proofs"]
)
def test_review_of_old_commit_does_not_verify_revised_source_claim(subject):
    captured_source = {
        **source(),
        "url": "https://github.com/plby/lean-proofs",
        "commit": "b" * 40,
    }
    reviewed_source = {**source(), "url": "https://github.com/plby/lean-proofs"}
    review = verified_review()
    review.update(subject_url=subject, proof_source=reviewed_source)
    capture = competition()
    capture["observations"]["pull_requests"] = [
        observation(proof_sources=[captured_source])
    ]
    result = new.select(scanner(), capture, research=research(review))
    assert row(result)["competition_state"] == "CONTESTED"
    assert row(result)["competition"][0]["proof_state"] == "source_linked"
    assert row(result)["proof_reviews"][0]["proof_source"]["commit"] == SHA
    assert any(
        "review" in message and "source" in message
        for message in row(result)["uncertainty"]
    )


def test_source_url_and_declared_pin_cannot_disagree():
    with pytest.raises(old.AssessmentError, match="source"):
        new.proof_source({**source(), "commit": "b" * 40})
    with pytest.raises(old.AssessmentError, match="source"):
        new.proof_source({**source(), "file": "Different.lean"})


def test_environmental_failure_alone_cannot_be_reviewed_as_invalid():
    review = evidence(
        subject_url=f"{ROOT}/pull/1248",
        state="invalid",
        build="environmental_failure",
        rationale="The dependency download was unavailable; no mathematical review was completed",
    )
    with pytest.raises(old.AssessmentError, match="environmental"):
        new.select(scanner(), competition(), research=research(review))


@pytest.mark.parametrize("state", [[], {}])
def test_malformed_state_produces_incomplete_capture(state, monkeypatch):
    raw = {
        "number": 1248,
        "title": "JSP-000161",
        "state": state,
        "html_url": f"{ROOT}/pull/1248",
    }
    monkeypatch.setattr(old, "_github_page", lambda _: ([raw], None))
    captured = old.capture_github(evidence_version=2)
    assert not captured["acquisition"]["complete"]
    assert captured["acquisition"]["error"]


def test_deeply_nested_json_is_rejected_without_crashing_capture(monkeypatch):
    class Response:
        headers = {}

        def __enter__(self):
            return self

        def __exit__(self, *args):
            pass

        def read(self, size):
            return ("[" * 2000 + "]" * 2000).encode()

    class Opener:
        def open(self, *args, **kwargs):
            return Response()

    monkeypatch.setattr(old, "build_opener", lambda _: Opener())
    captured = old.capture_github(evidence_version=2)
    assert not captured["acquisition"]["complete"]
    assert captured["acquisition"]["error"]


def test_pagination_cannot_skip_an_unread_page(monkeypatch):
    monkeypatch.setattr(
        old,
        "_github_payload",
        lambda _: (
            [],
            f'<https://api.github.com/repos/{old.OFFICIAL_REPOSITORY}/pulls?state=all&per_page=100&page=3>; rel="next"',
        ),
    )
    with pytest.raises(old.AssessmentError, match="pagination"):
        old._github_page(
            f"https://api.github.com/repos/{old.OFFICIAL_REPOSITORY}/pulls?state=all&per_page=100"
        )


@pytest.mark.parametrize(
    "state", ["partial", "invalid", "reproduced", "independently_verified"]
)
def test_matching_pinned_review_applies_to_source_linked_claim(state):
    review = verified_review()
    review["state"] = state
    capture = competition()
    capture["observations"]["pull_requests"] = [observation(proof_sources=[source()])]
    result = new.select(scanner(), capture, research=research(review))
    assert row(result)["competition"][0]["proof_state"] == state
    assert row(result)["competition_state"] == (
        "VERIFIED"
        if state == "independently_verified"
        else "CONTESTED"
        if state == "reproduced"
        else "REVIEWED"
    )


@pytest.mark.parametrize(
    "change", [{"file": "Different.lean"}, {"theorem": "different"}, {"commit": None}]
)
def test_different_or_unpinned_source_cannot_inherit_review(change):
    captured_source = {
        **source(),
        "url": "https://github.com/plby/lean-proofs",
        **change,
    }
    capture = competition()
    capture["observations"]["pull_requests"] = [
        observation(proof_sources=[captured_source])
    ]
    assert (
        row(new.select(scanner(), capture, research=research(verified_review())))[
            "competition_state"
        ]
        == "CONTESTED"
    )


def test_environmental_failure_with_reviewed_weaker_statement_is_distinct():
    review = evidence(
        subject_url=f"{ROOT}/pull/1248",
        state="invalid",
        build="environmental_failure",
        statement_fidelity="weaker",
        proof_source=source(),
    )
    capture = competition()
    capture["observations"]["pull_requests"] = [observation(proof_sources=[source()])]
    result = new.select(scanner(), capture, research=research(review))
    assert row(result)["competition_state"] == "REVIEWED"
    assert (
        row(result)["competition"][0]["proof_review"]["statement_fidelity"] == "weaker"
    )


def test_module_cli_reports_validation_error_without_traceback(tmp_path):
    bank = tmp_path / "bank.json"
    captured = tmp_path / "competition.json"
    findings = tmp_path / "research.json"
    output = tmp_path / "selection.json"
    bank.write_text(json.dumps(scanner()))
    captured.write_text(json.dumps(competition()))
    findings.write_text(json.dumps(research(difficulty={"value": "low"})))
    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "beejsp.assessment",
            "select",
            "--scanner",
            str(bank),
            "--competition",
            str(captured),
            "--research",
            str(findings),
            "--output",
            str(output),
        ],
        capture_output=True,
        text=True,
        env={**os.environ, "PYTHONPATH": str(Path("src").resolve())},
    )
    assert result.returncode == 2, result.stderr
    assert "Traceback" not in result.stderr
    assert not output.exists()


def test_module_capture_retains_invalid_proof_metadata_without_losing_coverage(
    tmp_path,
):
    output = tmp_path / "captured.json"
    program = r"""
import json
import runpy
import sys
from unittest.mock import patch
payload = [{"number": 1248, "title": "JSP-000161", "state": "open", "html_url": "https://github.com/TheJustinSunPrize/awards/pull/1248", "body": '```json\n[{"repository": "https://github.com/plby/lean-proofs", "commit": "short"}]\n```'}]
class Response:
    headers = {}
    def __enter__(self):
        return self
    def __exit__(self, *args):
        pass
    def read(self, size):
        return json.dumps(self.payload).encode()
class Opener:
    def open(self, *args, **kwargs):
        response = Response()
        response.payload = payload if "/pulls?" in args[0].full_url else []
        return response
sys.argv = ["assessment", "capture-github", "--evidence-version", "2", "--output", sys.argv[1]]
with patch("urllib.request.build_opener", return_value=Opener()):
    runpy.run_module("beejsp.assessment", run_name="__main__")
"""
    result = subprocess.run(
        [sys.executable, "-c", program, str(output)],
        capture_output=True,
        text=True,
        env={**os.environ, "PYTHONPATH": str(Path("src").resolve())},
    )
    assert result.returncode == 0, result.stderr
    assert "Traceback" not in result.stderr
    capture = json.loads(output.read_text())
    assert capture["acquisition"]["complete"]
    observation = capture["observations"]["pull_requests"][0]
    assert observation["source_metadata_errors"] == ["proof commit must be a full SHA"]
    assert observation["jsp_ids"] == ["JSP-000161"]
    assert observation["url"] == f"{ROOT}/pull/1248"


@pytest.mark.parametrize(
    "metadata",
    [
        {"commit": "short"},
        {"commit": 123},
        {"file": "../Main.lean"},
        {"repository": "javascript:alert(1)"},
        {"repository": "https://foreign.test/proofs"},
    ],
)
def test_invalid_submission_sources_do_not_destroy_api_coverage(metadata, monkeypatch):
    raw = {
        "number": 4565,
        "title": "JSP-000161 proof submission",
        "html_url": f"{ROOT}/pull/4565",
        "state": "open",
        "body": "```json\n"
        + json.dumps(
            [{"repository": "https://github.com/plby/lean-proofs", **metadata}]
        )
        + "\n```",
    }
    calls = []

    def page(address):
        calls.append(address)
        return ([raw], None) if "/pulls?" in address else ([], None)

    monkeypatch.setattr(old, "_github_page", page)
    captured = old.capture_github(evidence_version=2)
    assert len(calls) == 2
    assert captured["acquisition"]["complete"]
    assert captured["acquisition"]["scopes"] == {"pull_requests": True, "issues": True}
    item = row(new.select(scanner(), captured))
    assert item["competition_state"] == "CONTESTED"
    assert item["competition"][0]["proof_state"] == "unresolved"
    assert item["competition"][0]["source_metadata_errors"]
    assert item["competition"][0]["url"] == f"{ROOT}/pull/4565"
    assert item["competition"][0]["jsp_ids"] == ["JSP-000161"]
    assert "invalid proof-source metadata" in " ".join(item["uncertainty"])
    assert all(s["commit"] is None for s in item["competition"][0]["proof_sources"])
    assert (
        row(new.select(scanner(), captured), "JSP-000475")["competition_state"]
        == "NONE_IN_SCOPE"
    )


def test_invalid_metadata_cannot_inherit_pinned_review():
    capture = competition()
    capture["observations"]["pull_requests"] = [
        observation(
            proof_sources=[source()],
            source_metadata_errors=["proof commit must be a full SHA"],
        )
    ]
    result = new.select(scanner(), capture, research=research(verified_review()))
    item = row(result)
    assert item["competition_state"] == "CONTESTED"
    assert item["competition"][0]["proof_state"] == "unresolved"
    assert item["competition"][0]["proof_review"] is None
    assert item["proof_reviews"][0]["state"] == "independently_verified"
    assert not any("does not identify" in message for message in item["uncertainty"])
    capture["observations"]["pull_requests"][0].pop("source_metadata_errors")
    verified = row(new.select(scanner(), capture, research=research(verified_review())))
    assert verified["competition_state"] == "VERIFIED"


def test_saved_issue_with_invalid_proof_metadata_remains_contested():
    capture = competition()
    capture["observations"]["issues"] = [
        observation(
            category="issues",
            submission_kind="unknown",
            source_metadata_errors=["invalid source pin"],
        )
    ]
    item = row(new.select(scanner(), capture))
    assert item["competition_state"] == "CONTESTED"
    assert item["competition"][0]["proof_state"] == "unresolved"


@pytest.mark.parametrize("errors", [[], [123], "invalid", ["x"] * 51])
def test_saved_source_metadata_diagnostics_are_validated(errors):
    capture = competition()
    capture["observations"]["pull_requests"] = [
        observation(source_metadata_errors=errors)
    ]
    with pytest.raises(old.AssessmentError):
        new.select(scanner(), capture)


def test_diagnostics_never_authorize_an_invalid_saved_pin():
    capture = competition()
    capture["observations"]["pull_requests"] = [
        observation(
            proof_sources=[{**source(), "commit": "short"}],
            source_metadata_errors=["invalid pin"],
        )
    ]
    with pytest.raises(old.AssessmentError, match="full SHA"):
        new.select(scanner(), capture)


@pytest.mark.parametrize(
    "body",
    [
        '```json\n[{"repository":"https://github.com/plby/lean-proofs",]\n```',
        '```json\n{"repository":"https://github.com/plby/lean-proofs","commit":"short"}\n```',
        "```json\n"
        + json.dumps([{"repository": "https://github.com/plby/lean-proofs"}] * 21)
        + "\n```",
    ],
)
def test_malformed_proof_declarations_remain_explicit_unresolved_claims(body):
    item = new.enrich_observation(observation(), {"body": body}, WHEN)
    assert item["source_metadata_errors"]
    capture = competition()
    capture["observations"]["pull_requests"] = [item]
    assert row(new.select(scanner(), capture))["competition_state"] == "CONTESTED"


def test_invalid_claim_survives_later_endpoint_failure(monkeypatch):
    raw = {
        "number": 4565,
        "title": "JSP-000161 Lean proof",
        "html_url": f"{ROOT}/pull/4565",
        "state": "open",
        "body": '```json\n[{"repository":"https://github.com/plby/lean-proofs","commit":"short"}]\n```',
    }

    def page(address):
        if "/issues?" in address:
            raise old.AssessmentError("malformed API response")
        return [raw], None

    monkeypatch.setattr(old, "_github_page", page)
    captured = old.capture_github(evidence_version=2)
    assert not captured["acquisition"]["complete"]
    result = new.select(scanner(), captured)
    assert row(result)["competition_state"] == "CONTESTED"
    assert row(result, "JSP-000475")["competition_state"] == "UNKNOWN"


@pytest.mark.parametrize("value", ["No", "Unknown", "Missing"])
def test_status_only_lean_metadata_is_administrative(value):
    normalized = observation(title="docs: update JSP-000161 status metadata")
    item = new.enrich_observation(
        normalized, {"body": f"Current status: Solved\nLean proof: {value}"}, WHEN
    )
    assert item["submission_kind"] == "administrative"
    saved = competition()
    saved["observations"]["pull_requests"] = [item]
    result = row(new.select(scanner(), saved))
    assert result["competition_state"] == "NONE_IN_SCOPE"
    assert result["competition"][0]["url"] == normalized["url"]


@pytest.mark.parametrize(
    "body",
    [
        "Lean proof: Yes",
        "Lean proof: No\nI claim a complete Lean proof.",
        "Lean proof: No\nhttps://github.com/plby/lean-proofs",
        'Lean proof: No\n```json\n[{"repository":"https://github.com/plby/lean-proofs","commit":"short"}]\n```',
    ],
)
def test_status_title_cannot_hide_material_proof_claim(body):
    item = new.enrich_observation(
        observation(title="docs: update JSP-000161 status metadata"),
        {"body": body},
        WHEN,
    )
    assert item["submission_kind"] == "lean"
    saved = competition()
    saved["observations"]["pull_requests"] = [item]
    assert row(new.select(scanner(), saved))["competition_state"] == "CONTESTED"
