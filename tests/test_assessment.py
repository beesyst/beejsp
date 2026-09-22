from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest

import beejsp.assessment as assessment_module
from beejsp.assessment import (
    AssessmentError,
    assess,
    capture_github,
    main,
    match_competition,
    render_json,
    render_report,
)


def _scanner(count: int = 6) -> dict[str, Any]:
    records = []
    for number in range(1, count + 1):
        jsp_id = f"JSP-{number:06d}"
        records.append(
            {
                "jsp_id": jsp_id,
                "title": f"Problem {number}",
                "source": {"upstream_ref": "main", "upstream_commit": "a" * 40},
                "official": {
                    "current_status": {"normalized": "Solved", "raw": "Solved"},
                    "lean_proof": {"normalized": "No", "raw": "No"},
                    "reference_fields": {
                        "Attribution basis": "source" if number == 1 else None,
                        "Historical bounty": None,
                        "Independent verification": None,
                        "Publication details": "paper",
                        "Scholarly recognition": None,
                    },
                },
            }
        )
    return {
        "schema_version": 1,
        "is_complete": True,
        "source": {"upstream_ref": "main", "upstream_commit": "a" * 40},
        "records": records,
        "candidate_ids": [record["jsp_id"] for record in records],
    }


def _research(count: int = 6) -> dict[str, Any]:
    candidates = []
    for number in range(1, count + 1):
        candidates.append(
            {
                "jsp_id": f"JSP-{number:06d}",
                "solution": {
                    "kind": "complete" if number < 6 else "sketch",
                    "sources": [
                        {
                            "title": f"Proof {number}",
                            "url": f"https://example.test/{number}",
                            "date": "2024",
                        }
                    ],
                },
                "formalization": {
                    "search_scope": "manual public source review",
                    "observations": [],
                },
                "estimate": {
                    "complexity": "low" if number == 1 else "medium",
                    "proof_structure": "finite constructive argument",
                    "hardest_boundary": "encode the finite witness",
                    "mathlib_risk": "standard finite-set APIs",
                    "statement_risk": "source notation needs transcription review",
                    "provenance_risk": "publication date is recorded in the source",
                    "process_risk": "live observations are snapshot-scoped",
                    "rationale": ["source is explicit", "scope is bounded"],
                },
                "known_blocker": False,
                "spike_objective": "Formalize the finite witness and its central invariant.",
            }
        )
    return {
        "schema_version": 1,
        "search_scope": "five bounded public source reviews",
        "reviewed_prefix_count": count,
        "candidates": candidates,
    }


def _competition(complete: bool = True) -> dict[str, Any]:
    return {
        "schema_version": 1,
        "acquisition": {
            "repository": "TheJustinSunPrize/awards",
            "observed_at": "2026-09-22T00:00:00Z",
            "complete": complete,
            "search_scope": "all repository PRs and issues",
        },
        "observations": {"pull_requests": [], "issues": []},
    }


def _competition_url(category: str, number: int) -> str:
    endpoint = "pull" if category == "pull_requests" else "issues"
    return f"https://github.com/TheJustinSunPrize/awards/{endpoint}/{number}"


def test_assessment_is_deterministic_and_has_one_primary_four_reserves() -> None:
    first = assess(_scanner(), _research(), _competition())
    second = assess(_scanner(), _research(), _competition())

    assert render_json(first) == render_json(second)
    assert [candidate["decision"] for candidate in first["top5"]] == [
        "primary",
        "reserve",
        "reserve",
        "reserve",
        "reserve",
    ]
    assert len({candidate["jsp_id"] for candidate in first["top5"]}) == 5
    assert first["top5"][0]["jsp_id"] == "JSP-000001"
    assert first["top5"][0]["go_no_go"].startswith("GO:")
    assert first["top5"][0]["known_blocker"] is False
    assert first["top5"][0]["formalization_blocker"] is False
    assert "JSP-000001 score 39 > JSP-000002 score 36" in first["top5"][0]["reason"]
    assert len(first["triage"]["rows"]) == 6
    assert first["rejected"] == [
        {
            "jsp_id": "JSP-000006",
            "decision": "rejected",
            "reason": "outside the deterministic TOP-5 selection boundary",
        }
    ]
    report = render_report(first)
    assert "JSP-000001 — primary" in report
    assert report.count(" — reserve") == 4


@pytest.mark.parametrize(
    ("mutation", "message"),
    [
        (
            lambda scanner: scanner.update(schema_version=2),
            "unsupported scanner schema",
        ),
        (lambda scanner: scanner.update(is_complete=False), "incomplete scanner"),
        (
            lambda scanner: scanner.update(candidate_ids=["JSP-000001", "JSP-000001"]),
            "duplicate scanner candidate",
        ),
        (
            lambda scanner: scanner.update(candidate_ids=["JSP-999999"]),
            "unresolved scanner candidate",
        ),
    ],
)
def test_invalid_scanner_input_fails_closed(mutation, message: str) -> None:
    scanner = _scanner()
    mutation(scanner)

    with pytest.raises(AssessmentError, match=message):
        assess(scanner, _research(), _competition())


def test_research_requires_explicit_evidence_and_estimate_rationale() -> None:
    research = _research()
    research["candidates"][0]["solution"]["sources"] = []

    with pytest.raises(AssessmentError, match="complete solution evidence"):
        assess(_scanner(), research, _competition())

    research = _research()
    research["candidates"][0]["estimate"]["rationale"] = []
    with pytest.raises(AssessmentError, match="rationale"):
        assess(_scanner(), research, _competition())


def test_competition_is_complete_and_exact_id_matching_avoids_collisions() -> None:
    competition = _competition()
    competition["observations"] = {
        "pull_requests": [
            {
                "number": 1,
                "title": "JSP-000001 implementation",
                "jsp_ids": ["JSP-000001"],
                "url": _competition_url("pull_requests", 1),
                "state": "open",
            },
            {
                "number": 2,
                "title": "JSP-0000010 unrelated",
                "jsp_ids": [],
                "url": _competition_url("pull_requests", 2),
                "state": "closed-unmerged",
            },
            {
                "number": 3,
                "title": "Problem 2 notes",
                "jsp_ids": ["JSP-000003"],
                "url": _competition_url("pull_requests", 3),
                "state": "merged",
            },
        ],
        "issues": [
            {
                "number": 4,
                "title": "Problem 2",
                "jsp_ids": [],
                "url": _competition_url("issues", 4),
                "state": "open",
            }
        ],
    }
    matches = match_competition(
        {
            "JSP-000001": "Problem 1",
            "JSP-000002": "Problem 2",
            "JSP-000003": "Problem 3",
        },
        competition,
    )

    assert [item["number"] for item in matches["JSP-000001"]] == [1]
    assert matches["JSP-000002"] == [
        {
            "number": 4,
            "title": "Problem 2",
            "jsp_ids": [],
            "url": _competition_url("issues", 4),
            "state": "open",
            "kind": "issue",
            "match": "supplementary_title",
        }
    ]
    assert matches["JSP-000003"][0]["state"] == "merged"
    with pytest.raises(AssessmentError, match="incomplete live competition"):
        assess(_scanner(), _research(), _competition(complete=False))


def test_title_match_cannot_override_conflicting_exact_identity() -> None:
    competition = _competition()
    competition["observations"] = {
        "pull_requests": [
            {
                "number": 1,
                "title": "Problem 1",
                "jsp_ids": ["JSP-000002"],
                "url": _competition_url("pull_requests", 1),
                "state": "open",
            }
        ],
        "issues": [],
    }

    matches = match_competition(
        {"JSP-000001": "Problem 1", "JSP-000002": "Problem 2"}, competition
    )

    assert matches["JSP-000001"] == []
    assert matches["JSP-000002"][0]["match"] == "exact_jsp_id"


def test_competition_capture_requires_scope_and_normalized_state() -> None:
    competition = _competition()
    del competition["acquisition"]["search_scope"]
    with pytest.raises(AssessmentError, match="competition search_scope"):
        assess(_scanner(), _research(), competition)

    competition = _competition()
    competition["observations"]["issues"] = [
        {
            "number": 1,
            "title": "JSP-000001",
            "url": _competition_url("issues", 1),
            "jsp_ids": [],
            "state": "unknown",
        }
    ]
    with pytest.raises(AssessmentError, match="invalid competition issues state"):
        assess(_scanner(), _research(), competition)

    competition = _competition()
    competition["observations"]["issues"] = [
        {
            "number": 1,
            "title": "JSP-000001",
            "url": _competition_url("issues", 1),
            "jsp_ids": ["JSP-0000010"],
            "state": "open",
        }
    ]
    with pytest.raises(AssessmentError, match="invalid competition issues JSP ID"):
        assess(_scanner(), _research(), competition)

    competition = _competition()
    competition["observations"]["issues"] = [
        {
            "number": 1,
            "title": "JSP-000001",
            "jsp_ids": ["JSP-000001"],
            "body": "JSP-000001",
            "url": _competition_url("issues", 1),
            "state": "open",
        }
    ]
    with pytest.raises(AssessmentError, match="must not retain a raw body"):
        assess(_scanner(), _research(), competition)


@pytest.mark.parametrize("state", ["merged", "closed-unmerged"])
def test_offline_issue_evidence_rejects_pull_request_states(state: str) -> None:
    competition = _competition()
    competition["observations"]["issues"] = [
        {
            "number": 1,
            "title": "JSP-000001",
            "jsp_ids": ["JSP-000001"],
            "url": _competition_url("issues", 1),
            "state": state,
        }
    ]

    with pytest.raises(AssessmentError, match="invalid competition issues state"):
        assess(_scanner(), _research(), competition)


@pytest.mark.parametrize(
    ("category", "url"),
    [
        ("pull_requests", "https://example.test/TheJustinSunPrize/awards/pull/1"),
        ("pull_requests", "https://github.com/another/awards/pull/1"),
        ("pull_requests", _competition_url("issues", 1)),
        ("pull_requests", _competition_url("pull_requests", 2)),
    ],
)
def test_competition_rejects_noncanonical_observation_urls(
    category: str, url: str
) -> None:
    competition = _competition()
    competition["observations"][category] = [
        {
            "number": 1,
            "title": "JSP-000001",
            "jsp_ids": ["JSP-000001"],
            "url": url,
            "state": "open",
        }
    ]

    with pytest.raises(AssessmentError, match="canonical official GitHub URL"):
        assess(_scanner(), _research(), competition)


def test_competition_accepts_canonical_pr_and_closed_issue_urls() -> None:
    competition = _competition()
    competition["observations"] = {
        "pull_requests": [
            {
                "number": 1,
                "title": "JSP-000001",
                "jsp_ids": ["JSP-000001"],
                "url": _competition_url("pull_requests", 1),
                "state": "open",
            }
        ],
        "issues": [
            {
                "number": 2,
                "title": "JSP-000002",
                "jsp_ids": ["JSP-000002"],
                "url": _competition_url("issues", 2),
                "state": "closed",
            }
        ],
    }

    matches = match_competition(
        {"JSP-000001": "Problem 1", "JSP-000002": "Problem 2"}, competition
    )

    assert matches["JSP-000001"][0]["state"] == "open"
    assert matches["JSP-000002"][0]["state"] == "closed"


def test_offline_assessment_rejects_non_official_competition_repository() -> None:
    competition = _competition()
    competition["acquisition"]["repository"] = "owner/repository"

    with pytest.raises(AssessmentError, match="official JSP repository"):
        assess(_scanner(), _research(), competition)


def test_active_competition_is_risk_not_a_blocker() -> None:
    research = _research()
    competition = _competition()
    competition["observations"]["pull_requests"] = [
        {
            "number": 9,
            "title": "JSP-000001 formalization",
            "jsp_ids": ["JSP-000001"],
            "url": _competition_url("pull_requests", 9),
            "state": "open",
        }
    ]

    result = assess(_scanner(), research, competition)
    affected = next(
        candidate for candidate in result["top5"] if candidate["jsp_id"] == "JSP-000001"
    )

    assert affected["deterministic"]["competition_penalty"] == 12
    assert affected["go_no_go"].startswith("GO:")
    assert result["selection_formula"] == (
        "solution evidence quality + complexity signal - known-blocker penalty "
        "- active exact-ID competition penalty - reported external formalization "
        "penalty; JSP ID breaks ties"
    )
    report = render_report(result)
    assert "Problem status:" in report
    assert "Recorded Lean status:" in report
    assert "Competition evidence: pull_request #9 open (exact_jsp_id)" in report
    assert "Iteration 4 bounded spike:" in report
    for candidate in result["top5"]:
        assert f"{candidate['jsp_id']} — {candidate['decision']}" in report


def test_partial_formalization_is_risk_not_a_blocker() -> None:
    research = _research()
    research["candidates"][0]["formalization"]["observations"] = [
        {
            "source": "public partial formalization record",
            "url": "https://example.test/formal",
            "status": "partial",
            "blocking": False,
            "rationale": "The reviewed record is partial and does not cover the exact theorem.",
        }
    ]
    result = assess(_scanner(), research, _competition())
    affected = next(
        candidate for candidate in result["top5"] if candidate["jsp_id"] == "JSP-000001"
    )

    assert affected["deterministic"]["formalization_penalty"] == 12
    assert affected["go_no_go"].startswith("GO:")


def test_explicit_formalization_blocker_is_no_go() -> None:
    research = _research()
    research["candidates"][0]["formalization"]["observations"] = [
        {
            "source": "verified complete formalization record",
            "url": "https://example.test/formal",
            "status": "complete",
            "blocking": True,
            "rationale": "The reviewed record covers the exact theorem.",
            "blocking_rationale": "The reviewed evidence establishes the exact theorem is complete.",
        }
    ]
    result = assess(_scanner(), research, _competition())
    affected = next(
        candidate for candidate in result["top5"] if candidate["jsp_id"] == "JSP-000001"
    )

    assert affected["go_no_go"].startswith("NO-GO:")
    assert affected["decision"] != "primary"
    assert (
        "The reviewed evidence establishes the exact theorem is complete."
        in affected["reason"]
    )
    assert result["top5"][0]["go_no_go"].startswith("GO:")


def test_equal_score_primary_reserve_uses_jsp_id_tie_break_in_reason() -> None:
    research = _research()
    research["candidates"][1]["estimate"]["complexity"] = "low"

    result = assess(_scanner(), research, _competition())

    assert result["top5"][0]["jsp_id"] == "JSP-000001"
    assert (
        "JSP-000001 and JSP-000002 tie at 39; the published JSP-ID tie-break "
        "selected JSP-000001"
    ) in result["top5"][0]["reason"]


def test_higher_scoring_no_go_reserve_is_described_as_non_viable() -> None:
    comparison = assessment_module._primary_reserve_comparisons(
        {
            "jsp_id": "JSP-000001",
            "go_no_go": "GO: reviewed evidence permits a spike",
            "reason": "selected",
            "deterministic": {"selection_score": 10},
        },
        [
            {
                "jsp_id": "JSP-000002",
                "go_no_go": "NO-GO: formalization evidence establishes a blocker",
                "reason": "reviewed evidence establishes that the bounded spike would be pointless: exact theorem complete",
                "deterministic": {"selection_score": 99},
            }
        ],
    )

    assert comparison == (
        "JSP-000002 is non-viable: reviewed evidence establishes that the "
        "bounded spike would be pointless: exact theorem complete"
    )


def test_deterministic_prefix_can_continue_past_initial_review_limit() -> None:
    research = _research(13)
    for candidate in research["candidates"][:12]:
        candidate["formalization"]["observations"] = [
            {
                "source": "verified complete formalization record",
                "url": "https://example.test/formal",
                "status": "complete",
                "blocking": True,
                "rationale": "The reviewed record covers the exact theorem.",
                "blocking_rationale": "The exact theorem is already complete.",
            }
        ]
    research["candidates"][12]["solution"]["kind"] = "complete"

    result = assess(_scanner(13), research, _competition())

    assert result["triage"]["reviewed_prefix_count"] == 13
    assert result["top5"][0]["jsp_id"] == "JSP-000013"
    assert result["top5"][0]["go_no_go"].startswith("GO:")


def test_research_must_be_a_deterministic_triage_prefix() -> None:
    research = _research()
    research["candidates"][0], research["candidates"][1] = (
        research["candidates"][1],
        research["candidates"][0],
    )

    with pytest.raises(AssessmentError, match="deterministic triage prefix"):
        assess(_scanner(), research, _competition())


def test_github_capture_paginates_and_preserves_pr_issue_state(monkeypatch) -> None:
    pages = iter(
        [
            (
                [
                    {
                        "number": 1,
                        "title": "No title match",
                        "body": "JSP-000001",
                        "html_url": _competition_url("pull_requests", 1),
                        "state": "open",
                        "merged_at": None,
                    }
                ],
                "https://next/pulls",
            ),
            (
                [
                    {
                        "number": 2,
                        "title": "JSP-000002",
                        "body": None,
                        "html_url": _competition_url("pull_requests", 2),
                        "state": "closed",
                        "merged_at": "2026-01-01",
                    }
                ],
                None,
            ),
            (
                [
                    {
                        "number": 3,
                        "title": "JSP-000003",
                        "body": None,
                        "html_url": _competition_url("issues", 3),
                        "state": "closed",
                    },
                    {
                        "number": 4,
                        "title": "PR shadow",
                        "body": None,
                        "html_url": _competition_url("issues", 4),
                        "state": "open",
                        "pull_request": {},
                    },
                ],
                None,
            ),
        ]
    )
    monkeypatch.setattr(assessment_module, "_github_page", lambda _: next(pages))

    captured = capture_github()

    assert captured["acquisition"]["complete"] is True
    assert [item["state"] for item in captured["observations"]["pull_requests"]] == [
        "open",
        "merged",
    ]
    assert captured["observations"]["pull_requests"][0]["jsp_ids"] == ["JSP-000001"]
    assert "body" not in captured["observations"]["pull_requests"][0]
    matches = match_competition({"JSP-000001": "Problem 1"}, captured)
    assert matches["JSP-000001"][0]["match"] == "exact_jsp_id"
    assert captured["observations"]["issues"] == [
        {
            "number": 3,
            "title": "JSP-000003",
            "jsp_ids": ["JSP-000003"],
            "url": _competition_url("issues", 3),
            "state": "closed",
        }
    ]


def test_github_capture_fails_closed_on_malformed_response(monkeypatch) -> None:
    def malformed(_: str):
        raise AssessmentError("malformed GitHub response")

    monkeypatch.setattr(assessment_module, "_github_page", malformed)

    captured = capture_github()

    assert captured["acquisition"]["complete"] is False
    assert "malformed GitHub response" in captured["acquisition"]["error"]


def test_github_capture_fails_closed_on_malformed_observation(monkeypatch) -> None:
    monkeypatch.setattr(
        assessment_module,
        "_github_page",
        lambda _: (
            [
                {
                    "number": 1,
                    "title": "",
                    "html_url": "https://example.test",
                    "state": "open",
                }
            ],
            None,
        ),
    )

    captured = capture_github()

    assert captured["acquisition"]["complete"] is False
    assert "GitHub observation title" in captured["acquisition"]["error"]


def test_github_capture_rejects_noncanonical_api_observation_url(monkeypatch) -> None:
    monkeypatch.setattr(
        assessment_module,
        "_github_page",
        lambda _: (
            [
                {
                    "number": 1,
                    "title": "JSP-000001",
                    "html_url": "https://example.test/TheJustinSunPrize/awards/pull/1",
                    "state": "open",
                }
            ],
            None,
        ),
    )

    captured = capture_github()

    assert captured["acquisition"]["complete"] is False
    assert "canonical official GitHub URL" in captured["acquisition"]["error"]


def test_github_capture_rejects_another_repository() -> None:
    with pytest.raises(AssessmentError, match="only the official JSP repository"):
        capture_github("owner/repository")


def test_github_page_rejects_non_github_url() -> None:
    with pytest.raises(AssessmentError, match="invalid GitHub API page URL"):
        assessment_module._github_page("file:///tmp/untrusted.json")


def test_formalization_observations_require_source_and_url() -> None:
    research = _research()
    research["candidates"][0]["formalization"]["observations"] = [{}]

    with pytest.raises(AssessmentError, match="formalization observation source"):
        assess(_scanner(), research, _competition())


def test_cli_assesses_captured_inputs_without_network(tmp_path: Path) -> None:
    scanner = tmp_path / "scanner.json"
    research = tmp_path / "research.json"
    competition = tmp_path / "competition.json"
    output = tmp_path / "assessment.json"
    report = tmp_path / "top5.md"
    for path, value in (
        (scanner, _scanner()),
        (research, _research()),
        (competition, _competition()),
    ):
        path.write_text(json.dumps(value), encoding="utf-8")

    assert (
        main(
            [
                "assess",
                "--scanner",
                str(scanner),
                "--research",
                str(research),
                "--competition",
                str(competition),
                "--output",
                str(output),
                "--report",
                str(report),
            ]
        )
        == 0
    )
    assert (
        json.loads(output.read_text(encoding="utf-8"))["top5"][0]["decision"]
        == "primary"
    )
    assert "Evidence-backed TOP-5" in report.read_text(encoding="utf-8")


@pytest.mark.parametrize("collision", ["report", "scanner"])
def test_cli_rejects_colliding_assessment_paths_without_writing(
    tmp_path: Path, collision: str
) -> None:
    scanner = tmp_path / "scanner.json"
    research = tmp_path / "research.json"
    competition = tmp_path / "competition.json"
    report = tmp_path / "top5.md"
    for path, value in (
        (scanner, _scanner()),
        (research, _research()),
        (competition, _competition()),
    ):
        path.write_text(json.dumps(value), encoding="utf-8")
    output = report if collision == "report" else scanner
    scanner_before = scanner.read_text(encoding="utf-8")

    with pytest.raises(SystemExit) as error:
        main(
            [
                "assess",
                "--scanner",
                str(scanner),
                "--research",
                str(research),
                "--competition",
                str(competition),
                "--output",
                str(output),
                "--report",
                str(report),
            ]
        )

    assert error.value.code == 2
    assert scanner.read_text(encoding="utf-8") == scanner_before
    assert not report.exists()
