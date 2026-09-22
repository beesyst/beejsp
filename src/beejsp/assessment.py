"""Evidence-backed, offline-reproducible candidate assessment for Iteration 3.

This module consumes scanner JSON and captured research/competition JSON.  The
``capture-github`` command is the sole networked operation; assessment and
rendering are deliberately pure operations over saved inputs.
"""

from __future__ import annotations

import argparse
import json
import re
from collections.abc import Mapping, Sequence
from datetime import UTC, datetime
from pathlib import Path
from typing import Any
from urllib.error import HTTPError, URLError
from urllib.parse import urlsplit
from urllib.request import Request, urlopen

SCHEMA_VERSION = 1
SUPPORTED_SCANNER_SCHEMA_VERSION = 1
OFFICIAL_REPOSITORY = "TheJustinSunPrize/awards"
_JSP_ID = re.compile(r"^JSP-\d{6}$")
_JSP_ID_IN_TEXT = re.compile(r"(?<![A-Za-z0-9-])(JSP-\d{6})(?![A-Za-z0-9-])")
_COMMIT = re.compile(r"^[0-9a-f]{40}$", re.IGNORECASE)
_SOLUTION_KINDS = {"complete", "answer", "sketch", "partial", "unsupported", "unknown"}
_COMPLEXITIES = {"low", "medium", "high"}
_FORMALIZATION_STATUSES = {"complete", "partial", "scoped", "activity", "unknown"}
_SELECTION_FORMULA = (
    "solution evidence quality + complexity signal - known-blocker penalty "
    "- active exact-ID competition penalty - reported external formalization "
    "penalty; JSP ID breaks ties"
)


class AssessmentError(ValueError):
    """Raised when captured evidence cannot safely support an assessment."""


def _require_mapping(value: Any, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise AssessmentError(f"{name} must be an object")
    return value


def _require_list(value: Any, name: str) -> list[Any]:
    if not isinstance(value, list):
        raise AssessmentError(f"{name} must be a list")
    return value


def _require_text(value: Any, name: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise AssessmentError(f"{name} must be non-empty text")
    return value


def _validate_scanner(
    scanner: Mapping[str, Any],
) -> tuple[dict[str, Mapping[str, Any]], list[str]]:
    if scanner.get("schema_version") != SUPPORTED_SCANNER_SCHEMA_VERSION:
        raise AssessmentError("unsupported scanner schema version")
    if scanner.get("is_complete") is not True:
        raise AssessmentError("incomplete scanner report cannot be assessed")
    source = _require_mapping(scanner.get("source"), "scanner.source")
    commit = _require_text(source.get("upstream_commit"), "scanner upstream commit")
    _require_text(source.get("upstream_ref"), "scanner upstream ref")
    if not _COMMIT.fullmatch(commit):
        raise AssessmentError("scanner upstream commit must be a 40-character SHA")

    records: dict[str, Mapping[str, Any]] = {}
    for raw_record in _require_list(scanner.get("records"), "scanner.records"):
        record = _require_mapping(raw_record, "scanner record")
        jsp_id = _require_text(record.get("jsp_id"), "scanner record JSP ID")
        if not _JSP_ID.fullmatch(jsp_id):
            raise AssessmentError(f"invalid scanner JSP ID {jsp_id}")
        if jsp_id in records:
            raise AssessmentError(f"duplicate scanner JSP ID {jsp_id}")
        record_source = _require_mapping(record.get("source"), f"source for {jsp_id}")
        if record_source.get("upstream_commit") != commit:
            raise AssessmentError(f"inconsistent upstream commit for {jsp_id}")
        records[jsp_id] = record

    candidate_ids = _require_list(scanner.get("candidate_ids"), "scanner.candidate_ids")
    candidates: list[str] = []
    for value in candidate_ids:
        jsp_id = _require_text(value, "scanner candidate JSP ID")
        if jsp_id in candidates:
            raise AssessmentError(f"duplicate scanner candidate JSP ID {jsp_id}")
        if jsp_id not in records:
            raise AssessmentError(f"unresolved scanner candidate JSP ID {jsp_id}")
        candidates.append(jsp_id)
    return records, candidates


def _triage(
    records: Mapping[str, Mapping[str, Any]], candidates: list[str]
) -> dict[str, Any]:
    """Rank all scanner candidates by transparent record-completeness signals."""

    rows = []
    for jsp_id in candidates:
        fields = _require_mapping(
            _require_mapping(records[jsp_id].get("official"), f"official {jsp_id}").get(
                "reference_fields"
            ),
            f"reference fields {jsp_id}",
        )
        score = sum(bool(fields.get(name)) for name in fields)
        rows.append({"jsp_id": jsp_id, "score": score})
    rows.sort(key=lambda row: (-row["score"], row["jsp_id"]))
    return {
        "formula": "one point for each non-empty scanner reference field; JSP ID breaks ties",
        "initial_review_limit": 12,
        "rows": rows,
    }


def _validate_research(
    research: Mapping[str, Any], candidate_ids: list[str]
) -> dict[str, Mapping[str, Any]]:
    if research.get("schema_version") != SCHEMA_VERSION:
        raise AssessmentError("unsupported research schema version")
    _require_text(research.get("search_scope"), "research search_scope")
    reviewed_prefix_count = research.get("reviewed_prefix_count")
    if (
        not isinstance(reviewed_prefix_count, int)
        or isinstance(reviewed_prefix_count, bool)
        or reviewed_prefix_count < 5
    ):
        raise AssessmentError("research reviewed_prefix_count must be at least five")
    by_id: dict[str, Mapping[str, Any]] = {}
    for raw in _require_list(research.get("candidates"), "research.candidates"):
        item = _require_mapping(raw, "research candidate")
        jsp_id = _require_text(item.get("jsp_id"), "research JSP ID")
        if jsp_id not in candidate_ids:
            raise AssessmentError(
                f"research JSP ID is not a scanner candidate: {jsp_id}"
            )
        if jsp_id in by_id:
            raise AssessmentError(f"duplicate research JSP ID {jsp_id}")
        solution = _require_mapping(item.get("solution"), f"solution for {jsp_id}")
        kind = solution.get("kind")
        if kind not in _SOLUTION_KINDS:
            raise AssessmentError(f"invalid solution evidence kind for {jsp_id}")
        sources = _require_list(
            solution.get("sources"), f"solution sources for {jsp_id}"
        )
        if kind == "complete" and not sources:
            raise AssessmentError(
                f"complete solution evidence needs a source for {jsp_id}"
            )
        for source in sources:
            source = _require_mapping(source, f"solution source for {jsp_id}")
            _require_text(source.get("title"), f"solution source title for {jsp_id}")
            _require_text(source.get("url"), f"solution source URL for {jsp_id}")
        formalization = _require_mapping(
            item.get("formalization"), f"formalization for {jsp_id}"
        )
        _require_text(
            formalization.get("search_scope"), f"formalization scope for {jsp_id}"
        )
        _require_list(
            formalization.get("observations"),
            f"formalization observations for {jsp_id}",
        )
        for observation in formalization["observations"]:
            observation = _require_mapping(
                observation, f"formalization observation for {jsp_id}"
            )
            _require_text(
                observation.get("source"),
                f"formalization observation source for {jsp_id}",
            )
            _require_text(
                observation.get("url"),
                f"formalization observation URL for {jsp_id}",
            )
            if observation.get("status") not in _FORMALIZATION_STATUSES:
                raise AssessmentError(
                    f"invalid formalization observation status for {jsp_id}"
                )
            if not isinstance(observation.get("blocking"), bool):
                raise AssessmentError(
                    f"formalization observation blocking must be boolean for {jsp_id}"
                )
            _require_text(
                observation.get("rationale"),
                f"formalization observation rationale for {jsp_id}",
            )
            if observation["blocking"]:
                _require_text(
                    observation.get("blocking_rationale"),
                    f"formalization blocker rationale for {jsp_id}",
                )
        estimate = _require_mapping(item.get("estimate"), f"estimate for {jsp_id}")
        if estimate.get("complexity") not in _COMPLEXITIES:
            raise AssessmentError(f"invalid estimate complexity for {jsp_id}")
        for key in (
            "proof_structure",
            "hardest_boundary",
            "mathlib_risk",
            "statement_risk",
            "provenance_risk",
            "process_risk",
        ):
            _require_text(estimate.get(key), f"estimate {key} for {jsp_id}")
        if not _require_list(
            estimate.get("rationale"), f"estimate rationale for {jsp_id}"
        ):
            raise AssessmentError(f"estimate rationale must not be empty for {jsp_id}")
        if not isinstance(item.get("known_blocker"), bool):
            raise AssessmentError(f"known_blocker must be boolean for {jsp_id}")
        by_id[jsp_id] = item
    if len(by_id) < 5:
        raise AssessmentError(
            "at least five researched candidates are required for TOP-5"
        )
    if len(by_id) != reviewed_prefix_count:
        raise AssessmentError(
            "research reviewed_prefix_count must match the researched candidate count"
        )
    return by_id


def _validate_competition(competition: Mapping[str, Any]) -> None:
    if competition.get("schema_version") != SCHEMA_VERSION:
        raise AssessmentError("unsupported competition schema version")
    acquisition = _require_mapping(
        competition.get("acquisition"), "competition.acquisition"
    )
    if acquisition.get("repository") != OFFICIAL_REPOSITORY:
        raise AssessmentError(
            "competition repository must be the official JSP repository"
        )
    _require_text(acquisition.get("observed_at"), "competition observed_at")
    if acquisition.get("complete") is not True:
        raise AssessmentError(
            "incomplete live competition evidence cannot support TOP-5"
        )
    _require_text(acquisition.get("search_scope"), "competition search_scope")
    observations = _require_mapping(
        competition.get("observations"), "competition.observations"
    )
    for key in ("pull_requests", "issues"):
        for observation in _require_list(observations.get(key), f"competition {key}"):
            observation = _require_mapping(
                observation, f"competition {key} observation"
            )
            if "body" in observation:
                raise AssessmentError(
                    f"competition {key} observation must not retain a raw body"
                )
            number = observation.get("number")
            if not isinstance(number, int) or isinstance(number, bool) or number <= 0:
                raise AssessmentError(f"competition {key} number must be positive")
            _require_text(observation.get("title"), f"competition {key} title")
            _validate_observation_url(
                _require_text(observation.get("url"), f"competition {key} URL"),
                key,
                number,
            )
            jsp_ids = _require_list(
                observation.get("jsp_ids"), f"competition {key} JSP IDs"
            )
            if len(jsp_ids) != len(set(jsp_ids)):
                raise AssessmentError(f"duplicate competition {key} JSP ID")
            for jsp_id in jsp_ids:
                if not isinstance(jsp_id, str) or not _JSP_ID.fullmatch(jsp_id):
                    raise AssessmentError(f"invalid competition {key} JSP ID")
            valid_states = (
                {"open", "closed-unmerged", "merged"}
                if key == "pull_requests"
                else {"open", "closed"}
            )
            if observation.get("state") not in valid_states:
                raise AssessmentError(f"invalid competition {key} state")


def _canonical_observation_url(category: str, number: int) -> str:
    endpoint = "pull" if category == "pull_requests" else "issues"
    return f"https://github.com/{OFFICIAL_REPOSITORY}/{endpoint}/{number}"


def _validate_observation_url(url: str, category: str, number: int) -> None:
    if url != _canonical_observation_url(category, number):
        raise AssessmentError(
            f"competition {category} URL must be the canonical official GitHub URL"
        )


def match_competition(
    candidate_titles: Mapping[str, str], competition: Mapping[str, Any]
) -> dict[str, list[dict[str, Any]]]:
    """Match a saved GitHub capture without treating a title as an identity."""

    _validate_competition(competition)
    matched = {jsp_id: [] for jsp_id in candidate_titles}
    observations = _require_mapping(
        competition["observations"], "competition.observations"
    )
    for category in ("pull_requests", "issues"):
        for raw in observations[category]:
            observation = dict(_require_mapping(raw, "competition observation"))
            exact_ids = set(observation["jsp_ids"])
            for jsp_id, title in candidate_titles.items():
                exact = jsp_id in exact_ids
                title_match = bool(
                    title and title.casefold() in observation["title"].casefold()
                )
                if exact or (title_match and not exact_ids):
                    observation["kind"] = category[:-1]
                    observation["match"] = (
                        "exact_jsp_id" if exact else "supplementary_title"
                    )
                    matched[jsp_id].append(observation)
    for values in matched.values():
        values.sort(key=lambda item: (item["kind"], item.get("number", 0), item["url"]))
    return matched


def _primary_reserve_comparisons(
    primary: Mapping[str, Any], reserves: Sequence[Mapping[str, Any]]
) -> str:
    """Explain every primary/reserve comparison using the actual selection rule."""

    primary_score = primary["deterministic"]["selection_score"]
    comparisons = []
    for reserve in reserves:
        reserve_score = reserve["deterministic"]["selection_score"]
        if reserve["go_no_go"].startswith("NO-GO:"):
            comparisons.append(
                f"{reserve['jsp_id']} is non-viable: {reserve['reason']}"
            )
        elif primary_score > reserve_score:
            comparisons.append(
                f"{primary['jsp_id']} score {primary_score} > "
                f"{reserve['jsp_id']} score {reserve_score}"
            )
        elif primary_score == reserve_score:
            comparisons.append(
                f"{primary['jsp_id']} and {reserve['jsp_id']} tie at "
                f"{primary_score}; the published JSP-ID tie-break selected "
                f"{primary['jsp_id']}"
            )
        else:
            raise AssessmentError(
                "a viable reserve cannot outrank the selected primary"
            )
    return "; ".join(comparisons)


def assess(
    scanner: Mapping[str, Any],
    research: Mapping[str, Any],
    competition: Mapping[str, Any],
) -> dict[str, Any]:
    """Create a deterministic assessment from previously captured JSON inputs."""

    records, candidate_ids = _validate_scanner(scanner)
    research_by_id = _validate_research(research, candidate_ids)
    _validate_competition(competition)
    triage = _triage(records, candidate_ids)
    reviewed_ids = list(research_by_id)
    expected_prefix = [row["jsp_id"] for row in triage["rows"][: len(reviewed_ids)]]
    if reviewed_ids != expected_prefix:
        raise AssessmentError(
            "research candidates must form a deterministic triage prefix"
        )
    triage["reviewed_prefix_count"] = len(reviewed_ids)
    triage["reviewed_ids"] = reviewed_ids
    titles = {jsp_id: str(records[jsp_id]["title"]) for jsp_id in research_by_id}
    competition_by_id = match_competition(titles, competition)
    quality = {
        "complete": 30,
        "answer": 16,
        "sketch": 10,
        "partial": 6,
        "unsupported": 2,
        "unknown": 0,
    }
    complexity = {"low": 9, "medium": 6, "high": 3}
    candidates = []
    for jsp_id, evidence in research_by_id.items():
        estimate = evidence["estimate"]
        competition_evidence = competition_by_id[jsp_id]
        active_competition = any(
            item["match"] == "exact_jsp_id" and item["state"] == "open"
            for item in competition_evidence
        )
        reported_formalization = bool(evidence["formalization"]["observations"])
        formalization_blocker = any(
            observation["blocking"]
            for observation in evidence["formalization"]["observations"]
        )
        competition_penalty = 12 if active_competition else 0
        formalization_penalty = 12 if reported_formalization else 0
        score = (
            quality[evidence["solution"]["kind"]] + complexity[estimate["complexity"]]
        )
        score -= 100 if evidence["known_blocker"] else 0
        score -= competition_penalty + formalization_penalty
        candidate = {
            "jsp_id": jsp_id,
            "official": records[jsp_id]["official"],
            "source": records[jsp_id]["source"],
            "title": records[jsp_id]["title"],
            "solution": evidence["solution"],
            "formalization": evidence["formalization"],
            "estimate": estimate,
            "known_blocker": evidence["known_blocker"],
            "formalization_blocker": formalization_blocker,
            "competition": competition_evidence,
            "deterministic": {
                "selection_score": score,
                "competition_penalty": competition_penalty,
                "formalization_penalty": formalization_penalty,
            },
        }
        if formalization_blocker or evidence["known_blocker"]:
            signals = []
            if evidence["known_blocker"]:
                signals.append("known blocker")
            if formalization_blocker:
                signals.append("formalization evidence establishes a blocker")
            candidate["go_no_go"] = "NO-GO: " + " and ".join(signals)
            blocker_rationales = [
                observation["blocking_rationale"]
                for observation in evidence["formalization"]["observations"]
                if observation["blocking"]
            ]
            candidate["reason"] = (
                "reviewed evidence establishes that the bounded spike would be pointless"
                + (": " + "; ".join(blocker_rationales) if blocker_rationales else "")
            )
        else:
            candidate["go_no_go"] = (
                "GO: no reviewed evidence establishes an Iteration 4 blocker"
            )
            candidate["reason"] = (
                "selected by published deterministic score; captured competition and "
                "formalization evidence remain explicit risk penalties"
            )
        candidates.append(candidate)
    candidates.sort(
        key=lambda item: (-item["deterministic"]["selection_score"], item["jsp_id"])
    )
    viable = [item for item in candidates if item["go_no_go"].startswith("GO:")]
    if not viable:
        raise AssessmentError("no viable primary candidate after bounded review")
    primary = viable[0]
    if primary["solution"]["kind"] != "complete":
        raise AssessmentError(
            "primary requires complete mathematical solution evidence"
        )
    selectable = [item for item in candidates if not item["known_blocker"]]
    top = [primary] + [item for item in selectable if item is not primary][:4]
    if len(top) < 5:
        raise AssessmentError("fewer than five non-blocked candidates are available")
    for index, item in enumerate(top):
        item["decision"] = "primary" if index == 0 else "reserve"
    primary["reason"] += "; primary-vs-reserve: " + _primary_reserve_comparisons(
        primary, top[1:]
    )
    if not _require_text(
        research_by_id[top[0]["jsp_id"]].get("spike_objective"),
        "primary spike objective",
    ):
        raise AssertionError("unreachable")
    rejected = []
    for item in candidates:
        if item in top:
            continue
        rejected.append(
            {
                "jsp_id": item["jsp_id"],
                "decision": "rejected",
                "reason": "outside the deterministic TOP-5 selection boundary",
            }
        )
    return {
        "schema_version": SCHEMA_VERSION,
        "scanner_provenance": scanner["source"],
        "research_search_scope": research["search_scope"],
        "competition_acquisition": competition["acquisition"],
        "triage": triage,
        "selection_formula": _SELECTION_FORMULA,
        "top5": top,
        "rejected": rejected,
        "primary_spike_objective": research_by_id[top[0]["jsp_id"]]["spike_objective"],
    }


def render_json(assessment: Mapping[str, Any]) -> str:
    """Serialize an assessment canonically for reproducible review."""

    return json.dumps(assessment, ensure_ascii=False, indent=2, sort_keys=True) + "\n"


def render_report(assessment: Mapping[str, Any]) -> str:
    """Render the same decisions as the machine-readable assessment."""

    lines = [
        "# Evidence-backed TOP-5",
        "",
        f"Scanner commit: {assessment['scanner_provenance']['upstream_commit']}",
        f"Competition observation: {assessment['competition_acquisition']['observed_at']}",
        "",
    ]
    for index, candidate in enumerate(assessment["top5"], start=1):
        lines.extend(
            [
                f"## {index}. {candidate['jsp_id']} — {candidate['decision']}",
                candidate["title"],
                f"Problem status: {candidate['official']['current_status']['raw']}",
                f"Recorded Lean status: {candidate['official']['lean_proof']['raw']}",
                f"Solution evidence: {candidate['solution']['kind']}",
                "Mathematical sources: "
                + (
                    "; ".join(
                        f"{source['title']} ({source['url']})"
                        for source in candidate["solution"]["sources"]
                    )
                    or "explicit uncertainty"
                ),
                "Competition evidence: "
                + (
                    "; ".join(
                        f"{item['kind']} #{item['number']} {item['state']} ({item['match']})"
                        for item in candidate["competition"]
                    )
                    or "none in captured scope"
                ),
                "Formalization evidence: "
                + (
                    "; ".join(
                        f"{item['source']} [{item['status']}; "
                        f"{'blocking' if item['blocking'] else 'risk only'}: "
                        f"{item['rationale']}] ({item['url']})"
                        for item in candidate["formalization"]["observations"]
                    )
                    or "none found within: "
                    + candidate["formalization"]["search_scope"]
                ),
                f"Complexity: {candidate['estimate']['complexity']}",
                f"Mathlib/domain risk: {candidate['estimate']['mathlib_risk']}",
                f"Statement risk: {candidate['estimate']['statement_risk']}",
                f"Provenance/date risk: {candidate['estimate']['provenance_risk']}",
                f"Submission/process risk: {candidate['estimate']['process_risk']}",
                f"Selection score: {candidate['deterministic']['selection_score']}",
                f"Decision: {candidate['go_no_go']}",
                f"Reason: {candidate['reason']}",
                "",
            ]
        )
        if candidate["decision"] == "primary":
            lines.extend(
                [
                    f"Iteration 4 bounded spike: {assessment['primary_spike_objective']}",
                    "",
                ]
            )
    return "\n".join(lines)


def _github_page(url: str) -> tuple[list[dict[str, Any]], str | None]:
    parts = urlsplit(url)
    if (
        parts.scheme != "https"
        or parts.netloc != "api.github.com"
        or not parts.path.startswith(f"/repos/{OFFICIAL_REPOSITORY}/")
    ):
        raise AssessmentError("invalid GitHub API page URL")
    request = Request(  # noqa: S310 - URL is validated against the fixed public API above
        url,
        headers={
            "Accept": "application/vnd.github+json",
            "User-Agent": "beejsp-iteration-3",
        },
    )
    with urlopen(request, timeout=20) as response:  # noqa: S310 - fixed public GitHub API origin
        payload = json.loads(response.read().decode("utf-8"))
        if not isinstance(payload, list):
            raise AssessmentError("malformed GitHub response: expected list")
        link = response.headers.get("Link", "")
    next_url = next(
        (
            part.split(";")[0].strip()[1:-1]
            for part in link.split(",")
            if 'rel="next"' in part
        ),
        None,
    )
    if next_url:
        next_parts = urlsplit(next_url)
        current_parts = urlsplit(url)
        if (
            next_parts.scheme != "https"
            or next_parts.netloc != "api.github.com"
            or next_parts.path != current_parts.path
        ):
            raise AssessmentError("malformed GitHub pagination link")
    return payload, next_url


def _normalize_github_observation(item: Any, category: str) -> dict[str, Any]:
    item = _require_mapping(item, "GitHub observation")
    number = item.get("number")
    if not isinstance(number, int) or isinstance(number, bool) or number <= 0:
        raise AssessmentError("malformed GitHub response: invalid observation number")
    state = item.get("state")
    if state not in {"open", "closed"}:
        raise AssessmentError("malformed GitHub response: invalid observation state")
    title = _require_text(item.get("title"), "GitHub observation title")
    body = item.get("body") if isinstance(item.get("body"), str) else ""
    normalized_state = (
        "merged"
        if category == "pull_requests" and item.get("merged_at")
        else "closed-unmerged"
        if category == "pull_requests" and state == "closed"
        else "closed"
        if category == "issues" and state == "closed"
        else "open"
    )
    url = _require_text(item.get("html_url"), "GitHub observation URL")
    _validate_observation_url(url, category, number)
    return {
        "number": number,
        "title": title,
        "jsp_ids": sorted(set(_JSP_ID_IN_TEXT.findall(f"{title}\n{body}"))),
        "url": url,
        "state": normalized_state,
    }


def capture_github(repository: str = OFFICIAL_REPOSITORY) -> dict[str, Any]:
    """Capture bounded, public, read-only PR and Issue evidence from GitHub."""

    if repository != OFFICIAL_REPOSITORY:
        raise AssessmentError("only the official JSP repository is supported")
    observed_at = datetime.now(UTC).isoformat().replace("+00:00", "Z")
    result: dict[str, list[dict[str, Any]]] = {"pull_requests": [], "issues": []}
    try:
        for endpoint, destination in (("pulls", "pull_requests"), ("issues", "issues")):
            next_url: str | None = (
                f"https://api.github.com/repos/{repository}/{endpoint}?state=all&per_page=100"
            )
            while next_url:
                page, next_url = _github_page(next_url)
                for raw_item in page:
                    item = _require_mapping(raw_item, "GitHub observation")
                    if endpoint == "issues" and "pull_request" in item:
                        continue
                    result[destination].append(
                        _normalize_github_observation(item, destination)
                    )
    except (
        AssessmentError,
        HTTPError,
        URLError,
        TimeoutError,
        json.JSONDecodeError,
    ) as error:
        return {
            "schema_version": SCHEMA_VERSION,
            "acquisition": {
                "repository": repository,
                "observed_at": observed_at,
                "complete": False,
                "error": str(error),
            },
            "observations": result,
        }
    return {
        "schema_version": SCHEMA_VERSION,
        "acquisition": {
            "repository": repository,
            "observed_at": observed_at,
            "complete": True,
            "search_scope": "all repository pull requests and issues via paginated public GitHub API",
        },
        "observations": result,
    }


def _load_json(path: Path) -> Mapping[str, Any]:
    try:
        return _require_mapping(json.loads(path.read_text(encoding="utf-8")), str(path))
    except (OSError, json.JSONDecodeError) as error:
        raise AssessmentError(f"cannot load {path}: {error}") from error


def _validate_assessment_paths(
    scanner: Path, research: Path, competition: Path, output: Path, report: Path
) -> None:
    inputs = {path.resolve() for path in (scanner, research, competition)}
    output_path = output.resolve()
    report_path = report.resolve()
    if output_path == report_path or output_path in inputs or report_path in inputs:
        raise AssessmentError("assessment input and output paths must be distinct")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    capture = commands.add_parser(
        "capture-github", help="capture public GitHub evidence"
    )
    capture.add_argument("--output", type=Path, required=True)
    assess_parser = commands.add_parser(
        "assess", help="render TOP-5 from captured inputs"
    )
    assess_parser.add_argument("--scanner", type=Path, required=True)
    assess_parser.add_argument("--research", type=Path, required=True)
    assess_parser.add_argument("--competition", type=Path, required=True)
    assess_parser.add_argument("--output", type=Path, required=True)
    assess_parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args(argv)
    try:
        if args.command == "capture-github":
            captured = capture_github()
            args.output.write_text(render_json(captured), encoding="utf-8")
            return 0 if captured["acquisition"]["complete"] else 2
        _validate_assessment_paths(
            args.scanner,
            args.research,
            args.competition,
            args.output,
            args.report,
        )
        result = assess(
            _load_json(args.scanner),
            _load_json(args.research),
            _load_json(args.competition),
        )
        args.output.write_text(render_json(result), encoding="utf-8")
        args.report.write_text(render_report(result), encoding="utf-8")
        return 0
    except AssessmentError as error:
        parser.error(str(error))
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
