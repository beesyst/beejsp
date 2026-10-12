from __future__ import annotations

import argparse
import hashlib
import ipaddress
import json
import os
import re
import shutil
import sys
import tempfile
import uuid
import webbrowser
from collections import Counter
from collections.abc import Mapping, Sequence
from datetime import UTC, datetime
from pathlib import Path
from typing import Any
from urllib.parse import unquote, urljoin, urlsplit

from beejsp import assessment, discovery, scanner
from beejsp._dashboard_view import PAGE

Error = assessment.AssessmentError
INPUTS = ("scanner", "competition", "awards", "research")
OUTPUTS = (
    "general.json",
    "general.csv",
    "high-value.json",
    "high-value.csv",
    "dashboard.html",
)
LEGACY_TEMPLATE_SHA256 = (
    "9e9ec08d2ccd8a079c26e98f9c2a39a88fa5499bef2f9e599e635ffdc80a80a9"
)
SNAPSHOT_NAME = re.compile(r"snapshot-[0-9a-f]{32}\Z")


def _check_credential(content: str) -> None:
    token = assessment.validate_github_token(os.environ.get("GITHUB_TOKEN"))
    if token and token in content:
        raise Error(
            "credential found in report input; refusing artifact publication or display"
        )


def safe_link(value: str) -> str | None:
    try:
        discovery.url(value)
        decoded = unquote(value)
        if "\\" in decoded or any(ord(c) < 33 or ord(c) == 127 for c in decoded):
            return None
        host = urlsplit(value).hostname or ""
        if "." not in host or host.endswith((".localhost", ".local")):
            return None
        try:
            if not ipaddress.ip_address(host).is_global:
                return None
        except ValueError:
            if not re.fullmatch(
                r"(?:[A-Za-z0-9](?:[A-Za-z0-9-]{0,61}[A-Za-z0-9])?\.)+"
                r"(?:[A-Za-z]{2,63}|xn--[A-Za-z0-9-]+)",
                host,
            ):
                return None
    except ValueError:
        return None
    return value


def _links(value: Any, base: str) -> list[str]:
    links: set[str] = set()
    if isinstance(value, Mapping):
        for item in value.values():
            links.update(_links(item, base))
    elif isinstance(value, list):
        for item in value:
            links.update(_links(item, base))
    elif isinstance(value, str):
        candidates = re.findall(r"https://[^\s<>\"'\])]+", value)
        candidates += [urljoin(base, u) for u in re.findall(r"\]\(([^\s)]+)\)", value)]
        for candidate in candidates:
            link = safe_link(candidate.rstrip(".,;"))
            if link:
                links.add(link)
    return sorted(links)


def render_html(general: Mapping[str, Any], high_value: Mapping[str, Any]) -> str:
    rows = sorted(general["selected"] + general["excluded"], key=lambda r: r["jsp_id"])
    high_rows = {
        r["jsp_id"]: r for r in high_value["selected"] + high_value["excluded"]
    }
    details = []
    for row in rows:
        source = row["source"]
        path = source.get("catalog_path", "problems/README.md")
        catalog = (
            f"https://github.com/{assessment.OFFICIAL_REPOSITORY}/blob/"
            f"{source['upstream_commit']}/{path}#{row['jsp_id']}"
        )
        proof_states = sorted(
            {i["proof_state"] for i in row["competition"]}
            | {i["state"] for i in row["proof_reviews"]}
        ) or ["unknown"]
        details.append(
            {
                **row,
                "proof_states": proof_states,
                "catalog_url": safe_link(catalog),
                "links": _links(row, catalog)
                + ([catalog] if safe_link(catalog) else []),
                "profiles": {
                    "general": {k: row.get(k) for k in ("included", "rank", "reasons")},
                    "high-value": {
                        k: high_rows[row["jsp_id"]].get(k)
                        for k in ("included", "rank", "reasons")
                    },
                },
            }
        )
    counts = {
        key: dict(sorted(Counter(row["filters"][key] for row in rows).items()))
        for key in ("problem_status", "lean_status", "competition_state", "award_state")
    }
    payload = {
        "rows": details,
        "counts": counts,
        "selected": {
            "general": len(general["selected"]),
            "high-value": len(high_value["selected"]),
        },
        "scanner_provenance": general["scanner_provenance"],
        "competition_acquisition": general["competition_acquisition"],
        "competition_complete": general["competition_complete"],
        "award_acquisition": general["award_acquisition"],
    }

    encoded = json.dumps(
        payload, ensure_ascii=True, sort_keys=True, separators=(",", ":")
    )
    for char, escaped in (("&", "\\u0026"), ("<", "\\u003c"), (">", "\\u003e")):
        encoded = encoded.replace(char, escaped)
    return PAGE.replace("__DISCOVERY_DATA__", encoded)


def build_reports(inputs: Mapping[str, Any]) -> dict[str, str]:
    kwargs = {"research": inputs["research"], "awards": inputs["awards"]}
    general = discovery.select(inputs["scanner"], inputs["competition"], **kwargs)
    high = discovery.select(
        inputs["scanner"],
        inputs["competition"],
        profile=discovery.HIGH_VALUE_PROFILE,
        **kwargs,
    )
    return {
        "general.json": assessment.render_json(general),
        "general.csv": discovery.render_csv(general),
        "high-value.json": assessment.render_json(high),
        "high-value.csv": discovery.render_csv(high),
        "dashboard.html": render_html(general, high),
    }


def _storage(root: Path) -> Path:
    path = root / "storage" / "discovery"
    for item in (root / "storage", path):
        if item.is_symlink():
            raise Error("discovery storage must not be a symlink")
    return path


def _atomic_json(path: Path, value: Mapping[str, Any]) -> None:
    with tempfile.NamedTemporaryFile(
        mode="w", encoding="utf-8", dir=path.parent, delete=False
    ) as stream:
        temporary = Path(stream.name)
        try:
            stream.write(assessment.render_json(value))
            stream.flush()
            os.fsync(stream.fileno())
        except BaseException:
            temporary.unlink(missing_ok=True)
            raise
    try:
        os.replace(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)


def _read_snapshot(path: Path) -> dict[str, Any]:
    if path.is_symlink() or not path.is_dir():
        raise Error("missing saved snapshot; run ./start.sh update")
    manifest_path = path / "manifest.json"
    if manifest_path.is_symlink():
        raise Error("snapshot manifest must not be a symlink")
    manifest = assessment._load_json(manifest_path)
    hashes = assessment._require_mapping(manifest.get("sha256"), "snapshot hashes")
    expected = {f"{name}.json" for name in INPUTS} | set(OUTPUTS)
    if manifest.get("schema_version") != 1 or set(hashes) != expected:
        raise Error("invalid snapshot manifest")
    for name in sorted(expected):
        artifact = path / name
        if (
            artifact.is_symlink()
            or not artifact.is_file()
            or artifact.stat().st_size > 32_000_000
        ):
            raise Error(f"missing or unsafe saved artifact: {name}")
        if (
            hashlib.sha256(artifact.read_bytes()).hexdigest()
            != manifest["sha256"][name]
        ):
            raise Error(f"saved artifact integrity failure: {name}")
        _check_credential(artifact.read_text(encoding="utf-8"))
    inputs = {name: assessment._load_json(path / f"{name}.json") for name in INPUTS}

    for name, content in build_reports(inputs).items():
        saved = (path / name).read_text(encoding="utf-8")
        if name == "dashboard.html" and saved != content:
            pattern = r'(<script type="application/json" id="discovery-data">)(.*?)(</script>)'
            found = re.search(pattern, saved, re.S)
            generated = re.search(pattern, content, re.S)
            if found is not None and generated is not None:
                template = (
                    saved[: found.start(2)]
                    + "__DISCOVERY_DATA__"
                    + saved[found.end(2) :]
                )
                if (
                    hashlib.sha256(template.encode()).hexdigest()
                    == LEGACY_TEMPLATE_SHA256
                    and found[2] == generated[2]
                ):
                    continue
        if saved != content:
            raise Error(f"saved presentation disagrees with evidence: {name}")
    return inputs


def load_snapshot(root: Path) -> tuple[Path, dict[str, Any]]:
    storage = _storage(root)
    pointer = storage / "current.json"
    if pointer.is_symlink():
        raise Error("snapshot pointer must not be a symlink")
    current = assessment._load_json(pointer)
    name = current.get("snapshot")
    if not isinstance(name, str) or not SNAPSHOT_NAME.fullmatch(name):
        raise Error("invalid saved snapshot pointer")
    path = storage / name
    return path, _read_snapshot(path)


def saved_report(root: Path, path: Path, inputs: Mapping[str, Any]) -> Path:
    content = build_reports(inputs)["dashboard.html"]
    _check_credential(content)
    original = path / "dashboard.html"
    if original.read_text(encoding="utf-8") == content:
        return original
    destination = (
        _storage(root)
        / f"presentation-{hashlib.sha256(content.encode()).hexdigest()}.html"
    )
    if destination.is_symlink():
        raise Error("saved presentation must not be a symlink")
    if destination.exists():
        if (
            not destination.is_file()
            or destination.stat().st_size > 32_000_000
            or destination.read_text(encoding="utf-8") != content
        ):
            raise Error("saved presentation integrity failure")
        return destination
    temporary: Path | None = None
    try:
        with tempfile.NamedTemporaryFile(
            mode="w", encoding="utf-8", dir=destination.parent, delete=False
        ) as stream:
            temporary = Path(stream.name)
            stream.write(content)
            stream.flush()
            os.fsync(stream.fileno())
        if temporary.read_text(encoding="utf-8") != content:
            raise Error("saved presentation write verification failed")
        os.replace(temporary, destination)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)
    return destination


def refresh(root: Path) -> Path:
    storage = _storage(root)
    storage.mkdir(parents=True, exist_ok=True)
    lock = storage / ".refresh-lock"
    try:
        lock.mkdir()
    except FileExistsError as error:
        raise Error("another refresh is active (.refresh-lock exists)") from error
    stage: Path | None = None
    try:
        research_path = storage / "research.json"
        if research_path.exists():
            if research_path.is_symlink():
                raise Error("research input must not be a symlink")
            research = assessment._load_json(research_path)
        elif (storage / "current.json").exists():
            _, retained = load_snapshot(root)
            research = retained["research"]
        else:
            research = {"schema_version": 2, "candidates": []}
        bank = scanner.scan_problem_bank(root / "docs/vendor/jsp")
        assessment._validate_scanner(bank)
        competition = assessment.capture_github(
            evidence_version=2, kind="all", page_size=50
        )
        _, complete = discovery.validate_competition(competition)
        if competition["schema_version"] != 2 or not complete:
            raise Error(
                "incomplete GitHub acquisition: "
                + competition["acquisition"].get(
                    "error", "both endpoint scopes are required"
                )
            )
        awards = discovery.capture_records()
        _, acquisition = discovery.validate_awards(awards)
        if not acquisition or not acquisition["complete"]:
            raise Error(
                "incomplete official register acquisition: "
                + awards["acquisition"].get("error", "missing coverage")
            )
        inputs = {
            "scanner": bank,
            "competition": competition,
            "awards": awards,
            "research": research,
        }
        artifacts = {
            f"{name}.json": assessment.render_json(value)
            for name, value in inputs.items()
        }
        artifacts.update(build_reports(inputs))
        for content in artifacts.values():
            _check_credential(content)
        stage = Path(tempfile.mkdtemp(prefix=".stage-", dir=storage))
        for name, content in artifacts.items():
            (stage / name).write_text(content, encoding="utf-8")
        manifest = {
            "schema_version": 1,
            "sha256": {
                name: hashlib.sha256(content.encode("utf-8")).hexdigest()
                for name, content in artifacts.items()
            },
        }
        (stage / "manifest.json").write_text(
            assessment.render_json(manifest), encoding="utf-8"
        )
        _read_snapshot(stage)
        destination = storage / f"snapshot-{uuid.uuid4().hex}"
        stage.rename(destination)
        stage = destination

        _atomic_json(
            storage / "refresh-status.json",
            {"state": "validated", "snapshot": destination.name},
        )
        _atomic_json(storage / "current.json", {"snapshot": destination.name})
        stage = None
        return destination / "dashboard.html"
    except (OSError, ValueError) as error:
        try:
            _atomic_json(
                storage / "refresh-status.json",
                {
                    "state": "failed",
                    "attempted_at": datetime.now(UTC).isoformat(),
                    "error": str(error)[:4096],
                },
            )
        except OSError:
            pass
        raise
    finally:
        if stage is not None:
            shutil.rmtree(stage)
        lock.rmdir()


def _warnings(root: Path, inputs: Mapping[str, Any]) -> None:
    print(
        "Saved evidence only; capture timestamps are not a freshness guarantee.",
        file=sys.stderr,
    )
    print("Vendor: " + inputs["scanner"]["source"]["upstream_commit"], file=sys.stderr)
    for name in ("competition", "awards"):
        acquisition = inputs[name]["acquisition"]
        print(
            f"{name}: {acquisition['observed_at']} complete={acquisition['complete']}",
            file=sys.stderr,
        )
    status_path = _storage(root) / "refresh-status.json"
    if status_path.exists():
        status = assessment._load_json(status_path)
        _check_credential(assessment.render_json(status))
        if status.get("state") == "failed":
            print(
                f"WARNING: latest refresh failed; retained historical snapshot: {status.get('error')}",
                file=sys.stderr,
            )


def open_report(path: Path) -> None:
    print(f"Dashboard: {path}")
    if sys.platform not in {"darwin", "win32"} and not (
        os.environ.get("DISPLAY") or os.environ.get("WAYLAND_DISPLAY")
    ):
        print("Headless session: open this HTML file on a graphical desktop.")
        return
    try:
        if not webbrowser.open(path.resolve().as_uri()):
            print("Browser unavailable; open the printed HTML path manually.")
    except (OSError, webbrowser.Error):
        print("Browser unavailable; open the printed HTML path manually.")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--root",
        type=Path,
        required=True,
        help="repository root (provided by start.sh)",
    )
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("update", help="capture public evidence and publish reports")
    commands.add_parser("report", help="open saved dashboard offline")
    inspect = commands.add_parser("inspect", help="inspect saved evidence offline")
    inspect.add_argument("jsp_id")
    args = parser.parse_args(argv)
    root = args.root.resolve()
    try:
        if args.command == "update":
            open_report(refresh(root))
        else:
            if args.command == "inspect":
                discovery.identity(args.jsp_id)
            path, inputs = load_snapshot(root)
            _warnings(root, inputs)
            if args.command == "report":
                open_report(saved_report(root, path, inputs))
            else:
                result = discovery.inspect_problem(
                    inputs["scanner"],
                    inputs["competition"],
                    args.jsp_id,
                    research=inputs["research"],
                    awards=inputs["awards"],
                )
                sys.stdout.write(assessment.render_json(result))
        return 0
    except (OSError, ValueError) as error:
        print(
            f"Discovery failed: {error}. Last valid snapshot was retained; use report or inspect if available.",
            file=sys.stderr,
        )
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
