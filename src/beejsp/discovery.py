from __future__ import annotations

import base64
import csv
import io
import json
import re
import tomllib
from collections.abc import Mapping
from datetime import UTC, date, datetime
from pathlib import Path
from typing import Any
from urllib.parse import unquote, urlsplit

from beejsp import assessment as legacy

Error = legacy.AssessmentError
DIFFICULTIES = {"low", "medium", "high", "extreme", "unknown"}
QUALITIES = {"low", "medium", "high", "unknown"}
COMPETITION_STATES = {"CONTESTED", "REVIEWED", "VERIFIED", "NONE_IN_SCOPE", "UNKNOWN"}
PROOF_STATES = {
    "claimed",
    "source_linked",
    "partial",
    "invalid",
    "reproduced",
    "independently_verified",
    "unresolved",
}
SUBMISSION_KINDS = {"lean", "mathematical", "administrative", "other", "unknown"}
_REPOSITORY = re.compile(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+\Z")
_ERDOS = re.compile(r"(?i)\bErd[oöő]s(?:\s+problem)?\s*#?\s*(\d{1,6})(?!\d)")
_SOURCE = re.compile(
    r"https://github\.com/([A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+)(?:/blob/([^\s/)]+)/(\S+?\.lean)(?:#([A-Za-z0-9_.-]+))?)?(?=[\s)\]>.,]|$)"
)
DEFAULT_PROFILE = {"schema_version": 2, "name": "general", "limit": 20}
HIGH_VALUE_PROFILE = {
    "schema_version": 2,
    "name": "high-value",
    "limit": 20,
    "scientific_significance": ["high", "unknown"],
    "prize_potential": ["high", "unknown"],
}
FILTERS = {
    "problem_status": {"Solved", "Open", "Unknown", "Missing"},
    "lean_status": {"Yes", "No", "Unknown", "Missing"},
    "difficulty": DIFFICULTIES,
    "competition_state": COMPETITION_STATES,
    "solution_kind": legacy._SOLUTION_KINDS,
    "scientific_significance": QUALITIES,
    "prize_potential": QUALITIES,
    "award_state": {"candidate", "announced", "none_in_scope", "unknown"},
    "published_amount": {"known", "unknown"},
    "historical_bounty": {"known", "unknown"},
    "area": None,
    "award_level": None,
}


def text(value: Any, name: str) -> str:
    result = legacy._require_text(value, name)
    if len(result) > 4096 or any(ord(c) < 32 and c not in "\n\t" for c in result):
        raise Error(f"{name} exceeds text bounds or contains control characters")
    return result


def timestamp(value: Any) -> str:
    value = text(value, "observed_at")
    try:
        parsed = datetime.fromisoformat(value.replace("Z", "+00:00"))
        if parsed.tzinfo is None:
            raise ValueError
    except ValueError as error:
        raise Error("observed_at must be an ISO timestamp with timezone") from error
    return value


def review_date(value: Any) -> str | None:
    if value is None or value == "":
        return None
    value = text(value, "public review date")
    if re.fullmatch(r"\d{4}-\d{2}-\d{2}", value):
        try:
            date.fromisoformat(value)
        except ValueError as error:
            raise Error("invalid public review date") from error
        return value
    return timestamp(value)


def url(value: Any) -> str:
    value = text(value, "source URL")
    try:
        parts = urlsplit(value)
        port = parts.port
    except ValueError as error:
        raise Error("malformed source URL") from error
    if (
        parts.scheme != "https"
        or not parts.hostname
        or parts.username
        or parts.password
        or port not in {None, 443}
    ):
        raise Error("source URL must be public HTTPS without credentials")
    if any(c.isspace() for c in value):
        raise Error("source URL contains whitespace")
    return value


def identity(value: Any) -> str:
    if not isinstance(value, str) or not legacy._JSP_ID.fullmatch(value):
        raise Error("invalid JSP identity")
    return value


def evidence(value: Any) -> dict[str, Any]:
    value = dict(legacy._require_mapping(value, "evidence"))
    return {
        "url": url(value.get("url")),
        "observed_at": timestamp(value.get("observed_at")),
        "rationale": text(value.get("rationale"), "evidence rationale"),
    }


def proof_source(value: Any) -> dict[str, Any]:
    value = dict(legacy._require_mapping(value, "proof source"))
    if set(value) - {"url", "repository", "branch", "commit", "file", "theorem"}:
        raise Error("unknown proof source field")
    source_url = url(value.get("url"))
    repository = text(value.get("repository"), "proof repository")
    if (
        not _REPOSITORY.fullmatch(repository)
        or source_url != f"https://github.com/{repository}"
        and not source_url.startswith(f"https://github.com/{repository}/")
    ):
        raise Error("proof source must identify its GitHub repository")
    result: dict[str, str | None] = {
        "url": source_url,
        "repository": repository,
    }
    for key in ("branch", "commit", "file", "theorem"):
        item = value.get(key)
        if item is None:
            result[key] = None
            continue
        item = text(item, f"proof {key}")
        if key == "commit" and not legacy._COMMIT.fullmatch(item):
            raise Error("proof commit must be a full SHA")
        if key == "file" and (
            item.startswith("/") or ".." in item.split("/") or "\\" in item
        ):
            raise Error("invalid proof file path")
        result[key] = item
    path = urlsplit(source_url).path
    prefix = f"/{repository}/blob/"
    if path.startswith(prefix):
        revision, separator, file = path[len(prefix) :].partition("/")
        if not separator or not file:
            raise Error("invalid proof source blob URL")
        file = unquote(file)
        revision = unquote(revision)
        if result["file"] is not None and result["file"] != file:
            raise Error("proof source URL and declared file disagree")
        if legacy._COMMIT.fullmatch(revision):
            if (
                result["commit"] is not None
                and result["commit"].lower() != revision.lower()
            ):
                raise Error("proof source URL and declared commit disagree")
        elif result["branch"] is not None and result["branch"] != revision:
            raise Error("proof source URL and declared branch disagree")
    return result


def enrich_observation(
    normalized: dict[str, Any], raw: Mapping[str, Any], observed_at: str
) -> dict[str, Any]:
    """Extract references, never infer mathematical verification from prose."""
    content = f"{normalized['title']}\n{raw.get('body') or ''}"
    sources = []
    source_errors = []

    def add_source(value: Any) -> None:
        try:
            sources.append(proof_source(value))
        except Error as error:
            source_errors.append(str(error))

    file_match = re.search(r"(?im)^-?\s*Theorem/file:\s*`([^`]+)`", content)
    for block in re.findall(r"```json\s*([\s\S]*?)```", content):
        try:
            declared = json.loads(block)
        except (json.JSONDecodeError, RecursionError):
            if '"repository"' in block:
                source_errors.append("malformed proof-source JSON")
            continue
        if not isinstance(declared, list):
            if '"repository"' in block:
                source_errors.append("proof-source JSON must be a list")
            continue
        if len(declared) > 20:
            source_errors.append("proof source declaration exceeds record limit")
            declared = declared[:20]
        for entry in declared:
            if not isinstance(entry, dict) or "repository" not in entry:
                continue
            try:
                repository_url = url(entry["repository"])
                parts = urlsplit(repository_url)
                if parts.netloc != "github.com":
                    raise Error("declared proof repository must be on GitHub")
            except Error as error:
                source_errors.append(str(error))
                continue
            add_source(
                {
                    "url": repository_url,
                    "repository": parts.path.strip("/"),
                    "branch": entry.get("branch"),
                    "commit": entry.get("commit"),
                    "file": entry.get("file")
                    or (file_match[1] if file_match else None),
                    "theorem": entry.get("theorem"),
                }
            )
    for match in _SOURCE.finditer(content):
        repository, revision, file, theorem = match.groups()
        if repository == legacy.OFFICIAL_REPOSITORY or any(
            s["repository"] == repository and not revision for s in sources
        ):
            continue
        add_source(
            {
                "url": match.group(0),
                "repository": repository,
                "commit": revision
                if revision and legacy._COMMIT.fullmatch(revision)
                else None,
                "branch": revision
                if revision and not legacy._COMMIT.fullmatch(revision)
                else None,
                "file": unquote(file) if file else None,
                "theorem": theorem,
            }
        )
    if len(sources) > 50:
        source_errors.append("proof references exceed record limit")
        sources = sources[:50]
    sources = list({legacy.render_json(s): s for s in sources}.values())
    lowered = content.casefold()
    substantive = re.sub(
        r"(?im)^\s*(?:[-*]\s*)?(?:\*\*)?Lean proof(?:\*\*)?:\s*(?:No|Unknown|Missing)\s*$",
        "",
        content,
    )
    status_only = bool(
        re.search(
            r"(?i)^(?:docs|catalog)(?:\([^)]*\))?:.*\b(?:status|metadata|formatting|typo)\b",
            normalized["title"],
        )
        and not sources
        and not source_errors
        and not re.search(r"(?i)\blean\b|formaliz|\bproof\b", substantive)
    )
    submission_kind = (
        "administrative"
        if status_only
        else "lean"
        if sources or source_errors or re.search(r"\blean\b|formaliz", lowered)
        else "administrative"
        if re.search(r"\btypo\b|catalog update|\bformatting\b", lowered)
        else "mathematical"
        if "mathematical solution" in lowered
        else "unknown"
    )
    predecessors = sorted(
        set(
            re.findall(
                rf"https://github\.com/{legacy.OFFICIAL_REPOSITORY}/pull/[1-9]\d*(?!\d)",
                content,
            )
        )
    )
    return {
        **normalized,
        "observed_at": timestamp(observed_at),
        "source_timestamps": {
            key: timestamp(raw[key]) if raw.get(key) else None
            for key in ("created_at", "updated_at", "closed_at", "merged_at")
        },
        "erdos_ids": sorted({str(int(number)) for number in _ERDOS.findall(content)}),
        "submission_kind": submission_kind,
        "proof_sources": sorted(sources, key=legacy.render_json),
        "linked_submissions": predecessors,
        **(
            {"source_metadata_errors": sorted(set(source_errors))[:50]}
            if source_errors
            else {}
        ),
    }


def validate_competition(value: Mapping[str, Any]) -> tuple[dict[str, Any], bool]:
    """Reuse v1 identity/state validation while retaining incomplete observations."""
    version = value.get("schema_version")
    if (
        not isinstance(version, int)
        or isinstance(version, bool)
        or version not in {1, 2}
    ):
        raise Error("unsupported competition schema version")
    acquisition = dict(legacy._require_mapping(value.get("acquisition"), "acquisition"))
    timestamp(acquisition.get("observed_at"))
    if not isinstance(acquisition.get("complete"), bool):
        raise Error("competition completeness must be boolean")
    # Version 1 failed captures omitted search_scope. They are explicitly unknown.
    scope = acquisition.get("search_scope", "failed legacy capture")
    text(scope, "competition search scope")
    if version == 2:
        scopes = legacy._require_mapping(acquisition.get("scopes"), "capture scopes")
        if set(scopes) - {"issues", "pull_requests"} or any(
            not isinstance(v, bool) for v in scopes.values()
        ):
            raise Error("invalid capture scopes")
        if (
            acquisition["complete"]
            and not scopes
            or acquisition["complete"]
            and not all(scopes.values())
        ):
            raise Error("contradictory capture completeness")
        complete = acquisition["complete"] and all(
            scopes.get(k) is True for k in ("issues", "pull_requests")
        )
    else:
        # V1 may retain only a reviewed subset after complete API acquisition.
        # Its prose scope cannot certify coverage for negative findings.
        complete = False
    normalized = {
        "schema_version": 1,
        "acquisition": {**acquisition, "complete": True, "search_scope": scope},
        "observations": value.get("observations"),
    }
    legacy._validate_competition(normalized)
    observations = {"issues": [], "pull_requests": []}
    seen = {}
    for category in observations:
        for raw in normalized["observations"][category]:
            item = dict(raw)
            if set(item) - {
                "number",
                "title",
                "jsp_ids",
                "url",
                "state",
                "observed_at",
                "source_timestamps",
                "submission_kind",
                "erdos_ids",
                "proof_sources",
                "linked_submissions",
                "source_metadata_errors",
            }:
                raise Error("unknown competition observation field")
            text(item["title"], "observation title")
            item["observed_at"] = timestamp(
                item.get("observed_at", acquisition["observed_at"])
            )
            source_times = legacy._require_mapping(
                item.get("source_timestamps", {}), "source timestamps"
            )
            if set(source_times) - {
                "created_at",
                "updated_at",
                "closed_at",
                "merged_at",
            }:
                raise Error("invalid source timestamp field")
            item["source_timestamps"] = {
                key: timestamp(value) if value else None
                for key, value in source_times.items()
            }
            item["submission_kind"] = item.get("submission_kind", "unknown")
            if (
                not isinstance(item["submission_kind"], str)
                or item["submission_kind"] not in SUBMISSION_KINDS
            ):
                raise Error("invalid submission kind")
            aliases = legacy._require_list(item.get("erdos_ids", []), "Erdos IDs")
            if any(
                not isinstance(a, str) or not re.fullmatch(r"0|[1-9]\d{0,5}", a)
                for a in aliases
            ):
                raise Error("invalid Erdos ID")
            item["erdos_ids"] = sorted(set(aliases))
            item["proof_sources"] = [
                proof_source(s)
                for s in legacy._require_list(
                    item.get("proof_sources", []), "proof sources"
                )
            ]
            if "source_metadata_errors" in item:
                errors = legacy._require_list(
                    item["source_metadata_errors"], "proof source metadata errors"
                )
                if not 1 <= len(errors) <= 50:
                    raise Error("invalid proof source metadata error count")
                item["source_metadata_errors"] = sorted(
                    {text(error, "proof source metadata error") for error in errors}
                )
            links = legacy._require_list(
                item.get("linked_submissions", []), "linked submissions"
            )
            for link in links:
                if not isinstance(link, str) or not re.fullmatch(
                    rf"https://github\.com/{legacy.OFFICIAL_REPOSITORY}/pull/[1-9]\d*",
                    link,
                ):
                    raise Error("invalid linked submission URL")
            item["linked_submissions"] = sorted(set(links))
            key = (category, item["number"])
            if key in seen:
                if seen[key] != item:
                    raise Error("conflicting duplicate competition observation")
                continue
            seen[key] = item
            observations[category].append(item)
    return {**normalized, "observations": observations}, complete


def validate_research(
    value: Mapping[str, Any] | None, records: Mapping[str, Any]
) -> dict[str, Any]:
    if value is None:
        return {}
    if value.get("schema_version") != 2:
        raise Error(
            "selection research requires schema_version 2; legacy assess remains version 1"
        )
    result = {}
    alias_owners = {}
    for raw in legacy._require_list(value.get("candidates"), "research candidates"):
        raw = dict(legacy._require_mapping(raw, "research candidate"))
        if set(raw) - {
            "jsp_id",
            "difficulty",
            "scientific_significance",
            "prize_potential",
            "solution",
            "aliases",
            "proof_reviews",
        }:
            raise Error("unknown research candidate field")
        jsp_id = identity(raw.get("jsp_id"))
        if jsp_id not in records or jsp_id in result:
            raise Error("duplicate or unresolved research identity")
        item: dict[str, Any] = {"jsp_id": jsp_id}
        for key, valid in (
            ("difficulty", DIFFICULTIES),
            ("scientific_significance", QUALITIES),
            ("prize_potential", QUALITIES),
        ):
            estimate = legacy._require_mapping(raw.get(key, {"value": "unknown"}), key)
            if (
                not isinstance(estimate.get("value"), str)
                or estimate["value"] not in valid
            ):
                raise Error(f"invalid {key}")
            item[key] = {"value": estimate["value"]}
            if estimate["value"] != "unknown":
                item[key].update(evidence(estimate))
        solution = legacy._require_mapping(
            raw.get("solution", {"kind": "unknown", "sources": []}), "solution"
        )
        if (
            not isinstance(solution.get("kind"), str)
            or solution["kind"] not in legacy._SOLUTION_KINDS
        ):
            raise Error("invalid solution kind")
        sources = [
            evidence(s)
            for s in legacy._require_list(solution.get("sources"), "solution sources")
        ]
        if solution["kind"] != "unknown" and not sources:
            raise Error("solution kind requires evidence")
        item["solution"] = {
            "kind": solution["kind"],
            "sources": sorted(sources, key=legacy.render_json),
        }
        item["aliases"] = []
        for alias in legacy._require_list(raw.get("aliases", []), "aliases"):
            alias = legacy._require_mapping(alias, "alias")
            number = alias.get("erdos_id")
            if not isinstance(number, str) or not re.fullmatch(
                r"0|[1-9]\d{0,5}", number
            ):
                raise Error("invalid alias Erdos ID")
            if number in alias_owners and alias_owners[number] != jsp_id:
                raise Error("ambiguous Erdos alias identity")
            alias_owners[number] = jsp_id
            item["aliases"].append({"erdos_id": number, **evidence(alias)})
        item["proof_reviews"] = []
        review_urls = set()
        for review in legacy._require_list(
            raw.get("proof_reviews", []), "proof reviews"
        ):
            review = dict(legacy._require_mapping(review, "proof review"))
            state = review.get("state")
            if not isinstance(state, str) or state not in PROOF_STATES:
                raise Error("invalid proof review state")
            subject = url(review.get("subject_url"))
            if subject in review_urls:
                raise Error("duplicate proof review subject")
            review_urls.add(subject)
            checked = {**evidence(review), "subject_url": subject, "state": state}
            source = review.get("proof_source")
            checked["proof_source"] = proof_source(source) if source else None
            build = review.get("build", "unknown")
            fidelity = review.get("statement_fidelity", "unknown")
            axioms = review.get("axiom_audit", "unknown")
            placeholders = review.get("placeholders", "unknown")
            if (
                not all(
                    isinstance(v, str) for v in (build, fidelity, axioms, placeholders)
                )
                or build not in {"passed", "failed", "environmental_failure", "unknown"}
                or fidelity not in {"exact", "weaker", "unknown"}
                or axioms not in {"passed", "unexpected", "unknown"}
                or placeholders not in {"absent", "present", "unknown"}
            ):
                raise Error("invalid proof verification findings")
            checked.update(
                build=build,
                statement_fidelity=fidelity,
                axiom_audit=axioms,
                placeholders=placeholders,
            )
            if (
                state == "invalid"
                and build == "environmental_failure"
                and not (
                    fidelity == "weaker"
                    or axioms == "unexpected"
                    or placeholders == "present"
                )
            ):
                raise Error(
                    "environmental build failure alone cannot establish proof invalidity"
                )
            if state in {"reproduced", "independently_verified"}:
                if (
                    not checked["proof_source"]
                    or not checked["proof_source"]["commit"]
                    or not checked["proof_source"]["file"]
                    or build != "passed"
                ):
                    raise Error(
                        "reproduction requires pinned source and passed build evidence"
                    )
                checked["build_evidence"] = evidence(review.get("build_evidence"))
            if state == "independently_verified":
                if (
                    fidelity != "exact"
                    or axioms != "passed"
                    or placeholders != "absent"
                ):
                    raise Error(
                        "independent verification requires exact statement, axiom audit and no placeholders"
                    )
                checked["reviewer"] = text(
                    review.get("reviewer"), "independent reviewer"
                )
                checked["statement_evidence"] = evidence(
                    review.get("statement_evidence")
                )
                checked["axiom_evidence"] = evidence(review.get("axiom_evidence"))
            item["proof_reviews"].append(checked)
        item["proof_reviews"].sort(key=legacy.render_json)
        item["aliases"].sort(key=legacy.render_json)
        result[jsp_id] = item
    return result


def validate_profile(value: Mapping[str, Any]) -> dict[str, Any]:
    if value.get("schema_version") != 2 or set(value) - {
        "schema_version",
        "name",
        "limit",
        *FILTERS,
    }:
        raise Error("unsupported profile contract or unknown field")
    name = text(value.get("name"), "profile name")
    limit = value.get("limit")
    if not isinstance(limit, int) or isinstance(limit, bool) or not 1 <= limit <= 1000:
        raise Error("profile limit must be from 1 to 1000")
    result = {"schema_version": 2, "name": name, "limit": limit}
    for key, valid in FILTERS.items():
        if key not in value:
            continue
        values = legacy._require_list(value[key], f"profile {key}")
        if not values:
            raise Error("profile filters must not be empty")
        for item in values:
            text(item, f"profile {key}")
            if valid is not None and item not in valid:
                raise Error(f"invalid profile {key} value")
        result[key] = sorted(set(values))
    return result


def normalize_register(
    content: str, category: str, commit: str, observed_at: str, path: str
) -> list[dict[str, Any]]:
    """Normalize the documented official register tables; fail on layout drift."""
    expected = (
        [
            "Problem ID",
            "Solver review start (UTC)",
            "Mathematical solver",
            "Lean review start (UTC)",
            "Lean formalizer",
        ]
        if category == "candidate"
        else [
            "Problem ID",
            "Contribution type",
            "Recipients",
            "Public-review start (UTC)",
            "Public-review end (UTC)",
        ]
    )
    rows = []
    header = None
    for line in content.splitlines():
        if not line.startswith("|"):
            continue
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        if cells[0] == "Problem ID":
            header = cells
            if header != expected:
                raise Error("unsupported official register columns")
            continue
        if cells[0].startswith("---"):
            continue
        if header is None:
            raise Error("official register has data without a header")
        ids = legacy._JSP_ID_IN_TEXT.findall(cells[0])
        if len(cells) != len(header) or not ids or len(set(ids)) != 1:
            raise Error("malformed official register row")
        base = {
            "jsp_id": identity(ids[0]),
            "state": category if category == "candidate" else "announced",
            "url": f"https://github.com/{legacy.OFFICIAL_REPOSITORY}/blob/{commit}/{path}",
            "observed_at": observed_at,
            "upstream_commit": commit,
            "official_award_level": None,
            "published_amount": None,
            "currency": None,
        }
        if category == "candidate":
            for role, start, recipient in (
                ("solver", cells[1], cells[2]),
                ("formalizer", cells[3], cells[4]),
            ):
                if start and not start.startswith("["):
                    if not re.fullmatch(r"\d{4}-\d{2}-\d{2}(?:T\S+)?", start):
                        raise Error("malformed candidate review date")
                    rows.append(
                        {
                            **base,
                            "role": role,
                            "recipients": text(recipient, "candidate recipients"),
                            "review_start": review_date(start),
                            "review_end": None,
                        }
                    )
        else:
            role = {
                "Lean formalization": "formalizer",
                "Mathematical solution": "solver",
            }.get(cells[1])
            if role is None:
                raise Error("unknown award contribution type")
            rows.append(
                {
                    **base,
                    "role": role,
                    "recipients": text(cells[2], "award recipients"),
                    "review_start": review_date(cells[3]),
                    "review_end": review_date(cells[4]),
                }
            )
    if header is None:
        raise Error("official register table missing")
    return rows


def capture_records() -> dict[str, Any]:
    """Read fixed official registers at one resolved commit; never use vendor freshness."""
    observed_at = datetime.now(UTC).isoformat().replace("+00:00", "Z")
    result = {
        "schema_version": 2,
        "acquisition": {
            "repository": legacy.OFFICIAL_REPOSITORY,
            "observed_at": observed_at,
            "complete": False,
            "search_scope": "candidates/README.md and awards/README.md at one resolved commit",
        },
        "records": [],
    }
    try:
        commit_data, _ = legacy._github_payload(
            f"https://api.github.com/repos/{legacy.OFFICIAL_REPOSITORY}/commits/main"
        )
        commit = legacy._require_mapping(commit_data, "official commit").get("sha")
        if not isinstance(commit, str) or not legacy._COMMIT.fullmatch(commit):
            raise Error("invalid official register commit")
        result["acquisition"]["upstream_commit"] = commit
        for directory, category in (
            ("candidates", "candidate"),
            ("awards", "announced"),
        ):
            path = f"{directory}/README.md"
            data, _ = legacy._github_payload(
                f"https://api.github.com/repos/{legacy.OFFICIAL_REPOSITORY}/contents/{path}?ref={commit}"
            )
            data = legacy._require_mapping(data, "official register")
            if data.get("encoding") != "base64" or data.get("path") != path:
                raise Error("malformed official register response")
            encoded = legacy._require_text(data.get("content"), "register content")
            content = base64.b64decode("".join(encoded.split()), validate=True).decode(
                "utf-8"
            )
            result["records"].extend(
                normalize_register(content, category, commit, observed_at, path)
            )
        result["acquisition"]["complete"] = True
        result["records"].sort(key=legacy.render_json)
    except (ValueError, OSError, TimeoutError) as error:
        result["acquisition"]["error"] = str(error)[:4096]
    return result


def validate_awards(
    value: Mapping[str, Any] | None,
) -> tuple[list[dict[str, Any]], Mapping[str, Any] | None]:
    if value is None:
        return [], None
    if value.get("schema_version") != 2:
        raise Error("unsupported award schema version")
    acquisition = legacy._require_mapping(value.get("acquisition"), "award acquisition")
    if acquisition.get("repository") != legacy.OFFICIAL_REPOSITORY or not isinstance(
        acquisition.get("complete"), bool
    ):
        raise Error("invalid official award acquisition")
    timestamp(acquisition.get("observed_at"))
    text(acquisition.get("search_scope"), "award scope")
    commit = acquisition.get("upstream_commit")
    if commit is not None and (
        not isinstance(commit, str) or not legacy._COMMIT.fullmatch(commit)
    ):
        raise Error("invalid award commit")
    if acquisition["complete"] and commit is None:
        raise Error("complete award capture requires pinned commit")
    records = []
    seen = set()
    for raw in legacy._require_list(value.get("records"), "award records"):
        item = dict(legacy._require_mapping(raw, "award record"))
        if set(item) - {
            "jsp_id",
            "role",
            "state",
            "recipients",
            "review_start",
            "review_end",
            "url",
            "observed_at",
            "upstream_commit",
            "official_award_level",
            "published_amount",
            "currency",
            "publication_evidence",
        }:
            raise Error("unknown official award record field")
        identity(item.get("jsp_id"))
        if (
            not isinstance(item.get("role"), str)
            or not isinstance(item.get("state"), str)
            or item["role"] not in {"solver", "formalizer"}
            or item["state"] not in {"candidate", "announced"}
        ):
            raise Error("invalid official award role or state")
        directory = "candidates" if item["state"] == "candidate" else "awards"
        source = url(item.get("url"))
        if item.get("upstream_commit") != commit or not source.startswith(
            f"https://github.com/{legacy.OFFICIAL_REPOSITORY}/blob/{commit}/{directory}/"
        ):
            raise Error("award record requires pinned official source")
        timestamp(item.get("observed_at"))
        text(item.get("recipients"), "award recipients")
        item["review_start"] = review_date(item.get("review_start"))
        item["review_end"] = review_date(item.get("review_end"))
        level = item.get("official_award_level")
        if level is not None:
            text(level, "official award level")
        amount = item.get("published_amount")
        # Amounts are decimal strings. Never infer from a bounty or a level.
        if amount is not None and (
            not isinstance(amount, str)
            or not re.fullmatch(r"\d+(?:\.\d{1,2})?", amount)
            or not isinstance(item.get("currency"), str)
            or not re.fullmatch(r"[A-Z]{3}", item["currency"])
        ):
            raise Error("published amount requires a decimal string and currency")
        if amount is not None or level is not None:
            item["publication_evidence"] = evidence(item.get("publication_evidence"))
            if not item["publication_evidence"]["url"].startswith(
                f"https://github.com/{legacy.OFFICIAL_REPOSITORY}/"
            ):
                raise Error("published award details require official evidence")
        if amount is None and item.get("currency") is not None:
            raise Error("unknown amount must have unknown currency")
        serialized = legacy.render_json(item)
        if serialized not in seen:
            seen.add(serialized)
            records.append(item)
    return sorted(records, key=legacy.render_json), acquisition


def _review_applies(review: Mapping[str, Any], observation: Mapping[str, Any]) -> bool:
    """A mutable submission/repository URL cannot identify a reviewed revision."""
    sources = observation["proof_sources"]
    reviewed = review["proof_source"]
    linked = review["subject_url"] == observation["url"] or any(
        review["subject_url"] == source["url"] for source in sources
    )
    matching_pin = reviewed is not None and any(
        source["repository"] == reviewed["repository"]
        and source["commit"] is not None
        and reviewed["commit"] is not None
        and source["commit"].lower() == reviewed["commit"].lower()
        and source["file"] is not None
        and source["file"] == reviewed["file"]
        and (source["theorem"] is None or source["theorem"] == reviewed["theorem"])
        for source in sources
    )
    linked |= bool(
        reviewed and review["subject_url"] == reviewed["url"] and matching_pin
    )
    if not linked:
        return False
    if sources and review["state"] in {
        "partial",
        "invalid",
        "reproduced",
        "independently_verified",
    }:
        return matching_pin
    return True


def select(
    scanner: Mapping[str, Any],
    competition: Mapping[str, Any],
    *,
    research: Mapping[str, Any] | None = None,
    awards: Mapping[str, Any] | None = None,
    profile: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    """Screen every normalized record; ranking never grants mathematical GO."""
    records, _ = legacy._validate_scanner(scanner)
    profile = validate_profile(profile if profile is not None else DEFAULT_PROFILE)
    research_by_id = validate_research(research, records)
    normalized, complete = validate_competition(competition)
    matched = legacy.match_competition(
        {i: text(r.get("title"), "catalog title") for i, r in records.items()},
        normalized,
    )
    award_records, award_acquisition = validate_awards(awards)
    rows = []
    for jsp_id, record in sorted(records.items()):
        findings = research_by_id.get(jsp_id, {})
        aliases = {a["erdos_id"] for a in findings.get("aliases", [])}
        observations = [dict(item) for item in matched[jsp_id]]
        for category in ("pull_requests", "issues"):
            for raw in normalized["observations"][category]:
                if not raw["jsp_ids"] and aliases.intersection(raw["erdos_ids"]):
                    item = {
                        **raw,
                        "kind": category[:-1],
                        "match": "evidence_backed_erdos_alias",
                        "alias_evidence": findings["aliases"],
                    }
                    observations = [
                        v
                        for v in observations
                        if not (
                            v["kind"] == item["kind"] and v["number"] == item["number"]
                        )
                    ] + [item]
        observations.sort(key=lambda v: (v["kind"], v["number"]))
        reviews = findings.get("proof_reviews", [])
        proof_states = []
        contested = False
        unmatched_reviews = False
        for item in observations:
            invalid_sources = bool(item.get("source_metadata_errors"))
            review = next(
                (r for r in reviews if _review_applies(r, item)),
                None,
            )
            if invalid_sources:
                review = None
            if (
                not invalid_sources
                and review is None
                and any(
                    r["subject_url"] == item["url"]
                    or any(r["subject_url"] == s["url"] for s in item["proof_sources"])
                    for r in reviews
                )
            ):
                unmatched_reviews = True
            state = (
                "unresolved"
                if invalid_sources
                else review["state"]
                if review
                else "source_linked"
                if item["proof_sources"]
                else "claimed"
            )
            item["proof_state"] = state
            item["proof_review"] = review
            if item["match"] != "supplementary_title" and (
                invalid_sources
                or item["submission_kind"] == "lean"
                or item["kind"] == "pull_request"
                and item["submission_kind"] == "unknown"
            ):
                proof_states.append(state)
                if state not in {"partial", "invalid", "independently_verified"}:
                    contested = True
        # Reviewed external sources need not have a GitHub submission.
        proof_states.extend(r["state"] for r in reviews)
        contested |= any(
            s in {"claimed", "source_linked", "reproduced", "unresolved"}
            for s in proof_states
        )
        competition_state = (
            "CONTESTED"
            if contested
            else "VERIFIED"
            if "independently_verified" in proof_states
            else "UNKNOWN"
            if not complete
            or any(
                i["match"] == "supplementary_title"
                or i["kind"] == "issue"
                and i["submission_kind"] == "unknown"
                for i in observations
            )
            else "REVIEWED"
            if proof_states
            else "NONE_IN_SCOPE"
        )
        official = legacy._require_mapping(record.get("official"), "official record")
        status = legacy._require_mapping(
            official.get("current_status"), "problem status"
        ).get("normalized")
        lean_status = legacy._require_mapping(
            official.get("lean_proof"), "Lean status"
        ).get("normalized")
        if (
            not isinstance(status, str)
            or not isinstance(lean_status, str)
            or status not in FILTERS["problem_status"]
            or lean_status not in FILTERS["lean_status"]
        ):
            raise Error("invalid normalized catalog statuses")
        fields = legacy._require_mapping(official.get("fields", {}), "official fields")
        area = fields.get("Mathematical area") or "unknown"
        text(area, "mathematical area")
        bounty = (
            fields.get("Historical bounty")
            or official.get("reference_fields", {}).get("Historical bounty")
            or None
        )
        if bounty is not None:
            text(bounty, "historical bounty")
        relevant_awards = [a for a in award_records if a["jsp_id"] == jsp_id]
        award_state = (
            "announced"
            if any(a["state"] == "announced" for a in relevant_awards)
            else "candidate"
            if relevant_awards
            else "none_in_scope"
            if award_acquisition and award_acquisition["complete"]
            else "unknown"
        )
        official_acceptance = any(a["role"] == "formalizer" for a in relevant_awards)
        estimates = {
            key: findings.get(key, {"value": "unknown"})
            for key in ("difficulty", "scientific_significance", "prize_potential")
        }
        solution = findings.get("solution", {"kind": "unknown", "sources": []})
        values = {
            "problem_status": status,
            "lean_status": lean_status,
            "area": area,
            "competition_state": competition_state,
            "award_state": award_state,
            "solution_kind": solution["kind"],
            "historical_bounty": "known"
            if bounty
            and bounty.casefold()
            not in {"none", "unknown", "n/a", "—", "not applicable"}
            else "unknown",
            "published_amount": "known"
            if any(a.get("published_amount") is not None for a in relevant_awards)
            else "unknown",
            **{k: v["value"] for k, v in estimates.items()},
        }
        exclusion = [
            f"{key}={values[key]} does not match {profile[key]}"
            for key in FILTERS
            if key in profile
            and key != "award_level"
            and values[key] not in profile[key]
        ]
        levels = sorted(
            {
                a["official_award_level"]
                for a in relevant_awards
                if a.get("official_award_level") is not None
            }
        )
        if "award_level" in profile and not set(levels or ["unknown"]).intersection(
            profile["award_level"]
        ):
            exclusion.append("official award level does not match profile")
        components = {
            "scientific_significance": {"high": 6, "medium": 3, "low": 1, "unknown": 0}[
                estimates["scientific_significance"]["value"]
            ],
            "prize_potential": {"high": 3, "medium": 2, "low": 1, "unknown": 0}[
                estimates["prize_potential"]["value"]
            ],
            "difficulty": {
                "low": 4,
                "medium": 3,
                "high": 2,
                "extreme": 1,
                "unknown": 0,
            }[estimates["difficulty"]["value"]],
        }
        uncertainty = [
            f"{key} unknown" for key, val in values.items() if val == "unknown"
        ]
        if not complete:
            uncertainty.append(
                "incomplete competition capture; absence cannot be established"
            )
        if competition["schema_version"] == 1:
            uncertainty.append(
                "legacy v1 evidence does not establish per-problem coverage; absence cannot be established"
            )
        if contested:
            uncertainty.append(
                "unresolved competing proof; mathematical review required"
            )
        uncertainty.extend(
            f"invalid proof-source metadata in {item['url']}: "
            + "; ".join(item["source_metadata_errors"])
            for item in observations
            if item.get("source_metadata_errors")
        )
        if unmatched_reviews:
            uncertainty.append(
                "saved review does not identify the captured proof source pin; claim remains unresolved"
            )
        if any(i["match"] == "supplementary_title" for i in observations):
            uncertainty.append(
                "supplementary title match is not authoritative identity"
            )
        rows.append(
            {
                "jsp_id": jsp_id,
                "title": record["title"],
                "official": official,
                "source": record["source"],
                "filters": values,
                "research": estimates,
                "solution": solution,
                "competition": observations,
                "competition_state": competition_state,
                "proof_reviews": reviews,
                "official_acceptance": "recorded" if official_acceptance else "unknown",
                "awards": relevant_awards,
                "historical_bounty": bounty,
                "official_award_levels": levels,
                "published_amounts": [
                    {
                        "amount": a["published_amount"],
                        "currency": a["currency"],
                        "url": a["url"],
                    }
                    for a in relevant_awards
                    if a.get("published_amount") is not None
                ]
                or None,
                "score_components": components,
                "score": sum(components.values()),
                "decision": "REVIEW_REQUIRED",
                "uncertainty": uncertainty,
                "included": not exclusion,
                "reasons": exclusion or ["matches every configured profile filter"],
                "ranking_reason": "scientific significance + qualitative prize potential + difficulty preference; JSP ID breaks ties; unknown contributes no prioritization signal",
            }
        )
    rows.sort(key=lambda r: (-r["score"], r["jsp_id"]))
    selected = [r for r in rows if r["included"]][: profile["limit"]]
    for rank, row in enumerate(selected, 1):
        row["rank"] = rank
    for row in rows:
        if row["included"] and "rank" not in row:
            row["included"] = False
            row["reasons"] = [
                "outside configured result limit after deterministic ranking"
            ]
    return {
        "schema_version": 2,
        "report_kind": "selection",
        "profile": profile,
        "scanner_provenance": scanner["source"],
        "competition_acquisition": competition["acquisition"],
        "competition_complete": complete,
        "award_acquisition": award_acquisition,
        "selected": selected,
        "excluded": [r for r in rows if not r["included"]],
    }


def inspect_problem(
    scanner: Mapping[str, Any],
    competition: Mapping[str, Any],
    jsp_id: str,
    *,
    kind: str = "all",
    state: str = "all",
    **kwargs: Any,
) -> dict[str, Any]:
    identity(jsp_id)
    result = select(
        scanner, competition, profile={**DEFAULT_PROFILE, "limit": 1000}, **kwargs
    )
    row = next(
        (r for r in result["selected"] + result["excluded"] if r["jsp_id"] == jsp_id),
        None,
    )
    if row is None:
        raise Error("requested JSP ID not in normalized catalog")
    if kind not in {"all", "issue", "pull_request"} or state not in {
        "all",
        "open",
        "closed",
        "closed-unmerged",
        "merged",
    }:
        raise Error("invalid inspection kind or state")
    row["included"] = True
    row.pop("rank", None)
    row["reasons"] = ["requested exact JSP identity"]
    row["competition"] = [
        i
        for i in row["competition"]
        if (kind == "all" or i["kind"] == kind)
        and (state == "all" or i["state"] == state)
    ]
    return {
        k: v for k, v in result.items() if k not in {"selected", "excluded", "profile"}
    } | {
        "report_kind": "inspection",
        "query": {"jsp_id": jsp_id, "kind": kind, "state": state},
        "problem": row,
    }


def render_csv(result: Mapping[str, Any]) -> str:
    fields = [
        "jsp_id",
        "title",
        "included",
        "rank",
        "competition_state",
        "decision",
        "score",
        "filters",
        "research",
        "solution",
        "competition",
        "proof_reviews",
        "official_acceptance",
        "historical_bounty",
        "official_award_levels",
        "published_amounts",
        "awards",
        "source",
        "uncertainty",
        "reasons",
        "ranking_reason",
        "competition_acquisition",
        "award_acquisition",
    ]
    output = io.StringIO(newline="")
    writer = csv.DictWriter(output, fieldnames=fields, lineterminator="\n")
    writer.writeheader()
    rows = (
        [result["problem"]]
        if "problem" in result
        else result["selected"] + result["excluded"]
    )
    for row in rows:
        values = {}
        for key in fields:
            value = result.get(key) if key.endswith("_acquisition") else row.get(key)
            if isinstance(value, (dict, list)) or value is None:
                value = json.dumps(
                    value, sort_keys=True, ensure_ascii=False, separators=(",", ":")
                )
            elif isinstance(value, str) and (
                value.startswith(("\t", "\r", "\n"))
                or value.lstrip().startswith(("=", "+", "-", "@"))
            ):
                value = "'" + value
            values[key] = value
        writer.writerow(values)
    return output.getvalue()


def add_commands(commands: Any) -> None:
    capture = commands.add_parser(
        "capture-records", help="capture pinned official candidate/award registers"
    )
    capture.add_argument("--output", type=Path, required=True)
    for name in ("select", "inspect"):
        parser = commands.add_parser(
            name, help="process validated saved evidence offline"
        )
        for field in ("scanner", "competition"):
            parser.add_argument(f"--{field}", type=Path, required=True)
        for field in ("research", "awards"):
            parser.add_argument(f"--{field}", type=Path)
        parser.add_argument("--output", type=Path, required=True)
        parser.add_argument("--csv", type=Path)
        if name == "select":
            parser.add_argument(
                "--profile",
                default="general",
                help="general, high-value, or a TOML path",
            )
        else:
            parser.add_argument("--jsp", required=True)
            parser.add_argument(
                "--kind", choices=("all", "issue", "pull_request"), default="all"
            )
            parser.add_argument(
                "--state",
                choices=("all", "open", "closed", "closed-unmerged", "merged"),
                default="all",
            )


def run_command(args: Any) -> int:
    if args.command == "capture-records":
        result = capture_records()
        args.output.write_text(legacy.render_json(result), encoding="utf-8")
        return 0 if result["acquisition"]["complete"] else 2
    inputs = [args.scanner, args.competition, args.research, args.awards]
    profile = None
    if args.command == "select":
        if args.profile in {"general", "high-value"}:
            profile = (
                DEFAULT_PROFILE if args.profile == "general" else HIGH_VALUE_PROFILE
            )
        else:
            path = Path(args.profile)
            inputs.append(path)
            try:
                profile = tomllib.loads(path.read_text(encoding="utf-8"))
            except (ValueError, OSError) as error:
                raise Error(f"cannot read profile: {error}") from error
    outputs = [p.resolve() for p in (args.output, args.csv) if p is not None]
    if len(outputs) != len(set(outputs)) or set(outputs).intersection(
        p.resolve() for p in inputs if p is not None
    ):
        raise Error("selection input and output paths must be distinct")
    kwargs = {
        "research": legacy._load_json(args.research) if args.research else None,
        "awards": legacy._load_json(args.awards) if args.awards else None,
    }
    scanner = legacy._load_json(args.scanner)
    competition = legacy._load_json(args.competition)
    result = (
        select(scanner, competition, profile=profile, **kwargs)
        if args.command == "select"
        else inspect_problem(
            scanner, competition, args.jsp, kind=args.kind, state=args.state, **kwargs
        )
    )
    machine, tabular = legacy.render_json(result), render_csv(result)
    args.output.write_text(machine, encoding="utf-8")
    if args.csv:
        args.csv.write_text(tabular, encoding="utf-8")
    return 0
