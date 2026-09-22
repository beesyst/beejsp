"""Deterministic ingestion of the managed JSP problem-bank snapshot.

The scanner consumes the pinned Markdown reference as data.  It neither reads
live GitHub state nor performs network I/O.  Its JSON output intentionally
keeps raw official values alongside normalized values and BeeJSP-derived
candidate information.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections.abc import Iterable, Sequence
from pathlib import Path
from typing import Any

SCHEMA_VERSION = 1
_IDENTITY_RE = re.compile(r"^JSP-\d{6}$")
_HEADING_RE = re.compile(r"^## (JSP-\d{6}) · (.+)$", re.MULTILINE)
_ANY_HEADING_RE = re.compile(r"^## (.+)$", re.MULTILINE)
_ANCHOR_RE = re.compile(r'<a id="([^"]+)"></a>')
_TABLE_ROW_RE = re.compile(r"^\|\s*(.*?)\s*\|\s*(.*?)\s*\|\s*$")
_TABLE_DIVIDER_RE = re.compile(r"^\|\s*-+\s*\|\s*-+\s*\|\s*$")
_COMMIT_RE = re.compile(r"^[0-9a-f]{40}$", re.IGNORECASE)

_REFERENCE_FIELDS = (
    "Attribution basis",
    "Historical bounty",
    "Independent verification",
    "Publication details",
    "Scholarly recognition",
)


def _diagnostic(source: str, reason: str) -> dict[str, str]:
    return {"level": "error", "reason": reason, "source": source}


def _normalized_value(raw: str | None, values: Iterable[str]) -> str:
    """Return a known leading official value, Missing, or Unknown.

    Catalog values often add qualifications after the status, for example
    ``Solved<br>Proof contributors: ...``.  The raw value remains in output;
    only the leading status becomes a stable classifier.
    """

    if raw is None:
        return "Missing"
    leading = raw.lstrip(" *_`")
    for value in values:
        if re.match(
            rf"{re.escape(value)}(?=$|\s|<|—|-|:|\()",
            leading,
            re.IGNORECASE,
        ):
            return value
    return "Unknown"


def _value(raw: str | None, values: Iterable[str]) -> dict[str, str | None]:
    return {"normalized": _normalized_value(raw, values), "raw": raw}


def _read_provenance(
    vendor_root: Path, diagnostics: list[dict[str, str]]
) -> tuple[str | None, str | None]:
    values: list[str | None] = []
    for filename in ("UPSTREAM_REF", "UPSTREAM_COMMIT"):
        path = vendor_root / filename
        try:
            value = path.read_text(encoding="utf-8").strip()
        except FileNotFoundError:
            diagnostics.append(_diagnostic(filename, "missing vendor provenance"))
            value = None
        if not value:
            diagnostics.append(_diagnostic(filename, "empty vendor provenance"))
            value = None
        values.append(value)
    upstream_ref, upstream_commit = values
    if upstream_commit is not None and not _COMMIT_RE.fullmatch(upstream_commit):
        diagnostics.append(
            _diagnostic("UPSTREAM_COMMIT", "must contain a 40-character commit SHA")
        )
    return upstream_ref, upstream_commit


def _parse_index_metadata(
    vendor_root: Path, diagnostics: list[dict[str, str]]
) -> dict[str, dict[str, str | None]]:
    """Read only index-only claim data; catalog records remain authoritative."""

    index_path = vendor_root / "problems" / "README.md"
    source_path = "problems/README.md"
    try:
        lines = index_path.read_text(encoding="utf-8").splitlines()
    except FileNotFoundError:
        diagnostics.append(_diagnostic(source_path, "missing problem index"))
        return {}

    metadata: dict[str, dict[str, str | None]] = {}
    for number, line in enumerate(lines, start=1):
        if not line.startswith("| JSP-"):
            continue
        cells = [cell.strip() for cell in line.strip().strip("|").split("|")]
        source = f"{source_path}:{number}"
        if len(cells) != 7 or not _IDENTITY_RE.fullmatch(cells[0]):
            diagnostics.append(_diagnostic(source, "malformed problem-index row"))
            continue
        jsp_id = cells[0]
        if jsp_id in metadata:
            diagnostics.append(
                _diagnostic(source, f"duplicate JSP ID {jsp_id} in index")
            )
            continue
        metadata[jsp_id] = {
            "lean_claim_status": cells[6] or None,
            "solver_claim_status": cells[5] or None,
        }
    return metadata


def _parse_table(
    body: str, source_path: str, start_line: int, diagnostics: list[dict[str, str]]
) -> dict[str, str] | None:
    lines = body.splitlines()
    first_content = next(
        (index for index, line in enumerate(lines) if line.strip()), None
    )
    if first_content is None:
        diagnostics.append(
            _diagnostic(f"{source_path}:{start_line}", "missing field table")
        )
        return None
    if lines[first_content].strip() != "| Field | Content |":
        diagnostics.append(
            _diagnostic(f"{source_path}:{start_line}", "missing field table")
        )
        return None
    divider_index = first_content + 1
    if divider_index >= len(lines) or not _TABLE_DIVIDER_RE.fullmatch(
        lines[divider_index].strip()
    ):
        diagnostics.append(
            _diagnostic(
                f"{source_path}:{start_line + divider_index}",
                "malformed field-table divider",
            )
        )
        return None

    fields: dict[str, str] = {}
    row_count = 0
    for offset, line in enumerate(lines[divider_index + 1 :], start=divider_index + 2):
        if not line.startswith("|"):
            break
        row = _TABLE_ROW_RE.fullmatch(line.strip())
        if row is None:
            diagnostics.append(
                _diagnostic(
                    f"{source_path}:{start_line + offset}", "malformed field-table row"
                )
            )
            return None
        field, content = (part.strip() for part in row.groups())
        if not field:
            diagnostics.append(
                _diagnostic(f"{source_path}:{start_line + offset}", "empty field name")
            )
            return None
        if field in fields:
            diagnostics.append(
                _diagnostic(
                    f"{source_path}:{start_line + offset}", f"duplicate field {field}"
                )
            )
            return None
        fields[field] = content
        row_count += 1
    if row_count == 0:
        diagnostics.append(
            _diagnostic(f"{source_path}:{start_line}", "empty field table")
        )
        return None
    return fields


def _parse_catalog(
    catalog_path: Path,
    vendor_root: Path,
    upstream_ref: str | None,
    upstream_commit: str | None,
    index_metadata: dict[str, dict[str, str | None]],
    diagnostics: list[dict[str, str]],
) -> list[dict[str, Any]]:
    text = catalog_path.read_text(encoding="utf-8")
    source_path = catalog_path.relative_to(vendor_root).as_posix()
    headings = list(_ANY_HEADING_RE.finditer(text))
    records: list[dict[str, Any]] = []

    for index, heading in enumerate(headings):
        line_number = text.count("\n", 0, heading.start()) + 1
        parsed_heading = _HEADING_RE.fullmatch(heading.group(0))
        if parsed_heading is None:
            diagnostics.append(
                _diagnostic(f"{source_path}:{line_number}", "malformed problem heading")
            )
            continue
        jsp_id, title = parsed_heading.groups()
        end = headings[index + 1].start() if index + 1 < len(headings) else len(text)
        body = text[heading.end() : end]

        preceding_start = headings[index - 1].end() if index else 0
        anchors = list(_ANCHOR_RE.finditer(text[preceding_start : heading.start()]))
        anchor_id = anchors[-1].group(1) if anchors else None
        if anchor_id != jsp_id:
            diagnostics.append(
                _diagnostic(
                    f"{source_path}:{line_number}",
                    f"heading identity {jsp_id} does not match preceding anchor",
                )
            )
            continue

        fields = _parse_table(body, source_path, line_number, diagnostics)
        if fields is None:
            continue
        for required in ("Current status", "Lean proof"):
            if required not in fields:
                diagnostics.append(
                    _diagnostic(
                        f"{source_path}:{line_number}",
                        f"missing required field {required}",
                    )
                )
        if "Current status" not in fields or "Lean proof" not in fields:
            continue

        claim = index_metadata.get(jsp_id, {})
        current_status = _value(fields.get("Current status"), ("Solved", "Open"))
        lean_proof = _value(fields.get("Lean proof"), ("Yes", "No"))
        eligibility_raw = fields.get("Eligible to claim")
        record = {
            "derived": {
                "is_solved_without_recorded_lean_proof": (
                    current_status["normalized"] == "Solved"
                    and lean_proof["normalized"] == "No"
                )
            },
            "jsp_id": jsp_id,
            "official": {
                "claim_metadata": {
                    "lean_claim_status": _value(
                        claim.get("lean_claim_status"),
                        ("Claimed", "Unclaimed", "Unavailable"),
                    ),
                    "solver_claim_status": _value(
                        claim.get("solver_claim_status"),
                        ("Claimed", "Unclaimed", "Unavailable"),
                    ),
                },
                "current_status": current_status,
                "eligibility": _value(
                    eligibility_raw, ("Yes", "No", "Pending verification")
                ),
                "fields": fields,
                "lean_proof": lean_proof,
                "reference_fields": {
                    field: fields.get(field) for field in _REFERENCE_FIELDS
                },
            },
            "source": {
                "catalog_path": source_path,
                "upstream_commit": upstream_commit,
                "upstream_ref": upstream_ref,
            },
            "title": title,
        }
        records.append(record)
    return records


def scan_problem_bank(vendor_root: str | Path) -> dict[str, Any]:
    """Return the canonical scan report for one managed JSP snapshot.

    A report always exposes diagnostics.  When malformed identities, malformed
    records, or duplicate IDs occur, ``is_complete`` is false and candidate IDs
    are deliberately withheld so consumers cannot mistake a partial scan for a
    valid candidate set.
    """

    root = Path(vendor_root)
    diagnostics: list[dict[str, str]] = []
    upstream_ref, upstream_commit = _read_provenance(root, diagnostics)
    index_metadata = _parse_index_metadata(root, diagnostics)
    problems_dir = root / "problems"
    catalog_paths = sorted(
        problems_dir.glob("catalog-*.md"), key=lambda path: path.name
    )
    if not catalog_paths:
        diagnostics.append(_diagnostic("problems", "no catalog-*.md files discovered"))

    records: list[dict[str, Any]] = []
    for catalog_path in catalog_paths:
        records.extend(
            _parse_catalog(
                catalog_path,
                root,
                upstream_ref,
                upstream_commit,
                index_metadata,
                diagnostics,
            )
        )

    unique_records: list[dict[str, Any]] = []
    first_sources: dict[str, str] = {}
    for record in records:
        jsp_id = record["jsp_id"]
        source = record["source"]["catalog_path"]
        if jsp_id in first_sources:
            diagnostics.append(
                _diagnostic(
                    source,
                    f"duplicate JSP ID {jsp_id}; first seen in {first_sources[jsp_id]}",
                )
            )
            continue
        first_sources[jsp_id] = source
        unique_records.append(record)

    unique_records.sort(key=lambda record: record["jsp_id"])
    diagnostics.sort(
        key=lambda diagnostic: (diagnostic["source"], diagnostic["reason"])
    )
    is_complete = not any(diagnostic["level"] == "error" for diagnostic in diagnostics)
    candidate_ids = [
        record["jsp_id"]
        for record in unique_records
        if record["derived"]["is_solved_without_recorded_lean_proof"]
    ]
    if not is_complete:
        candidate_ids = []

    return {
        "candidate_ids": candidate_ids,
        "catalog_paths": [path.relative_to(root).as_posix() for path in catalog_paths],
        "diagnostics": diagnostics,
        "is_complete": is_complete,
        "records": unique_records,
        "schema_version": SCHEMA_VERSION,
        "source": {
            "upstream_commit": upstream_commit,
            "upstream_ref": upstream_ref,
        },
    }


def render_json(report: dict[str, Any]) -> str:
    """Serialize a report canonically for reproducible machine consumption."""

    return json.dumps(report, ensure_ascii=False, indent=2, sort_keys=True) + "\n"


def render_summary(report: dict[str, Any]) -> str:
    """Render a concise, intentionally unranked human summary."""

    state = "complete" if report["is_complete"] else "incomplete"
    return (
        "\n".join(
            (
                f"Problem-bank scan: {state}",
                f"Catalogs discovered: {len(report['catalog_paths'])}",
                f"Normalized records: {len(report['records'])}",
                f"Solved with recorded Lean proof No: {len(report['candidate_ids'])}",
                f"Diagnostics: {len(report['diagnostics'])}",
            )
        )
        + "\n"
    )


def main(argv: Sequence[str] | None = None) -> int:
    """Write canonical JSON to stdout (or --output) and a summary to stderr."""

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--vendor-root",
        default="docs/vendor/jsp",
        help="managed JSP snapshot root (default: docs/vendor/jsp)",
    )
    parser.add_argument("--output", type=Path, help="write machine-readable JSON here")
    parser.add_argument("--summary", type=Path, help="write the human summary here")
    args = parser.parse_args(argv)

    report = scan_problem_bank(args.vendor_root)
    machine_output = render_json(report)
    summary = render_summary(report)
    if args.output is None:
        sys.stdout.write(machine_output)
    else:
        args.output.write_text(machine_output, encoding="utf-8")
    if args.summary is None:
        sys.stderr.write(summary)
    else:
        args.summary.write_text(summary, encoding="utf-8")
    return 0 if report["is_complete"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
