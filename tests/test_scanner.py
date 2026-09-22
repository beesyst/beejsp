from __future__ import annotations

import json
import re
from pathlib import Path

from beejsp.scanner import main, render_json, render_summary, scan_problem_bank


def _write_snapshot(root: Path, catalog_text: str, index_rows: str = "") -> Path:
    problems = root / "problems"
    problems.mkdir(parents=True)
    (root / "UPSTREAM_REF").write_text("main\n", encoding="utf-8")
    (root / "UPSTREAM_COMMIT").write_text("a" * 40 + "\n", encoding="utf-8")
    (problems / "README.md").write_text(index_rows, encoding="utf-8")
    (problems / "catalog-0001-0002.md").write_text(catalog_text, encoding="utf-8")
    return root


def _record(
    jsp_id: str = "JSP-000001",
    title: str = "Example problem",
    status: str = "Solved<br>Proof contributors: Ada.",
    lean: str = "No — related work exists.",
    optional: str = "",
) -> str:
    return f'''<a id="{jsp_id}"></a>

## {jsp_id} · {title}

| Field | Content |
| --- | --- |
| Date proposed | 2020 |
| Mathematical area | Combinatorics |
| Problem description | An example. |
| Current status | {status} |
| Lean proof | {lean} |
| Eligible to claim | No |
| Publication details | [Source](https://example.test) |
{optional}'''


def _index_row(jsp_id: str = "JSP-000001") -> str:
    return (
        f"| {jsp_id} | [Example](catalog-0001-0002.md#{jsp_id}) | Solved | No | "
        "No | Unavailable | Unavailable |\n"
    )


def test_qualified_fields_preserve_raw_content_and_normalize(tmp_path: Path) -> None:
    root = _write_snapshot(tmp_path, _record(), _index_row())

    report = scan_problem_bank(root)

    assert report["is_complete"]
    assert report["candidate_ids"] == ["JSP-000001"]
    record = report["records"][0]
    assert record["official"]["current_status"] == {
        "normalized": "Solved",
        "raw": "Solved<br>Proof contributors: Ada.",
    }
    assert record["official"]["lean_proof"] == {
        "normalized": "No",
        "raw": "No — related work exists.",
    }
    assert (
        record["official"]["claim_metadata"]["solver_claim_status"]["raw"]
        == "Unavailable"
    )
    assert record["official"]["reference_fields"]["Independent verification"] is None
    assert record["source"] == {
        "catalog_path": "problems/catalog-0001-0002.md",
        "upstream_commit": "a" * 40,
        "upstream_ref": "main",
    }


def test_unknown_or_missing_statuses_never_become_candidates(tmp_path: Path) -> None:
    unknown = _record(
        status="Contested — review pending.", lean="Unknown proof state.", optional=""
    )
    root = _write_snapshot(tmp_path, unknown, _index_row())

    report = scan_problem_bank(root)

    record = report["records"][0]
    assert record["official"]["current_status"]["normalized"] == "Unknown"
    assert record["official"]["lean_proof"]["normalized"] == "Unknown"
    assert report["candidate_ids"] == []


def test_index_supplies_claims_without_replacing_detailed_record_data(
    tmp_path: Path,
) -> None:
    index = _index_row().replace("| Solved | No |", "| Open | Yes |")
    root = _write_snapshot(tmp_path, _record(), index)

    report = scan_problem_bank(root)

    record = report["records"][0]
    assert report["candidate_ids"] == ["JSP-000001"]
    assert record["official"]["eligibility"]["raw"] == "No"
    assert record["official"]["claim_metadata"] == {
        "lean_claim_status": {"normalized": "Unavailable", "raw": "Unavailable"},
        "solver_claim_status": {"normalized": "Unavailable", "raw": "Unavailable"},
    }


def test_duplicate_id_is_diagnostic_and_invalidates_candidate_set(
    tmp_path: Path,
) -> None:
    catalog = _record() + "\n" + _record(title="Repeated problem")
    root = _write_snapshot(tmp_path, catalog, _index_row())

    report = scan_problem_bank(root)

    assert not report["is_complete"]
    assert report["candidate_ids"] == []
    assert len(report["records"]) == 1
    assert any(
        "duplicate JSP ID JSP-000001" in item["reason"]
        for item in report["diagnostics"]
    )


def test_malformed_heading_anchor_and_table_are_explicit(tmp_path: Path) -> None:
    malformed = """<a id="JSP-000001"></a>

## JSP-000001 Example problem

| Field | Content |
| --- | --- |
| Current status | Solved |
| Lean proof | No |
"""
    root = _write_snapshot(tmp_path, malformed)

    report = scan_problem_bank(root)

    assert not report["is_complete"]
    assert report["records"] == []
    assert report["candidate_ids"] == []
    assert report["diagnostics"] == [
        {
            "level": "error",
            "reason": "malformed problem heading",
            "source": "problems/catalog-0001-0002.md:3",
        }
    ]


def test_mismatched_anchor_and_malformed_table_are_explicit(tmp_path: Path) -> None:
    bad_anchor = _record().replace('<a id="JSP-000001"></a>', '<a id="JSP-000002"></a>')
    root = _write_snapshot(tmp_path / "anchor", bad_anchor, _index_row())
    anchor_report = scan_problem_bank(root)

    assert not anchor_report["is_complete"]
    assert anchor_report["records"] == []
    assert (
        "does not match preceding anchor" in anchor_report["diagnostics"][0]["reason"]
    )

    bad_table = _record().replace("| --- | --- |", "| --- |")
    root = _write_snapshot(tmp_path / "table", bad_table, _index_row())
    table_report = scan_problem_bank(root)

    assert not table_report["is_complete"]
    assert table_report["records"] == []
    assert table_report["diagnostics"][0]["reason"] == "malformed field-table divider"


def test_canonical_serialization_and_summary_are_deterministic(tmp_path: Path) -> None:
    catalog = _record("JSP-000002", "Second") + "\n" + _record("JSP-000001", "First")
    index = _index_row("JSP-000002") + _index_row("JSP-000001")
    root = _write_snapshot(tmp_path, catalog, index)

    first = scan_problem_bank(root)
    second = scan_problem_bank(root)

    assert [record["jsp_id"] for record in first["records"]] == [
        "JSP-000001",
        "JSP-000002",
    ]
    assert first["candidate_ids"] == ["JSP-000001", "JSP-000002"]
    assert render_json(first) == render_json(second)
    assert json.loads(render_json(first))["schema_version"] == 1
    summary = render_summary(first)
    assert "rank" not in summary.lower()
    assert "Solved with recorded Lean proof No: 2" in summary


def test_complete_pinned_snapshot_is_valid_and_dynamic() -> None:
    vendor_root = Path("docs/vendor/jsp")
    catalog_paths = sorted(
        (vendor_root / "problems").glob("catalog-*.md"), key=lambda path: path.name
    )
    expected_ids_by_catalog = {
        catalog_path.relative_to(vendor_root).as_posix(): re.findall(
            r"^## (JSP-\d{6}) · .+$",
            catalog_path.read_text(encoding="utf-8"),
            flags=re.MULTILINE,
        )
        for catalog_path in catalog_paths
    }
    report = scan_problem_bank(vendor_root)

    assert report["is_complete"]
    assert report["catalog_paths"] == list(expected_ids_by_catalog)
    assert [record["jsp_id"] for record in report["records"]] == sorted(
        jsp_id for jsp_ids in expected_ids_by_catalog.values() for jsp_id in jsp_ids
    )
    final_catalog = report["catalog_paths"][-1]
    assert [
        record["jsp_id"]
        for record in report["records"]
        if record["source"]["catalog_path"] == final_catalog
    ] == expected_ids_by_catalog[final_catalog]
    assert report["candidate_ids"]


def test_cli_writes_separate_machine_and_human_outputs(tmp_path: Path) -> None:
    root = _write_snapshot(tmp_path / "snapshot", _record(), _index_row())
    output = tmp_path / "report.json"
    summary = tmp_path / "summary.txt"

    assert (
        main(
            [
                "--vendor-root",
                str(root),
                "--output",
                str(output),
                "--summary",
                str(summary),
            ]
        )
        == 0
    )

    assert json.loads(output.read_text(encoding="utf-8"))["candidate_ids"] == [
        "JSP-000001"
    ]
    assert summary.read_text(encoding="utf-8") == render_summary(
        scan_problem_bank(root)
    )
