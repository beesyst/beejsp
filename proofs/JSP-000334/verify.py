import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time
import tomllib

ROOT = Path(__file__).resolve().parent
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
LOGS = Path(tempfile.mkdtemp(prefix="beejsp-000334-verify-", dir="/tmp"))
RESULTS = []
ENV = os.environ.copy()
ENV.pop("LEAN_PATH", None)
ENV.pop("LEAN_SRC_PATH", None)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(label, command, env=None):
    log = LOGS / (label + ".log")
    start = time.monotonic()
    with log.open("w") as stream:
        code = subprocess.run(
            command,
            cwd=ROOT,
            env=ENV if env is None else env,
            stdout=stream,
            stderr=subprocess.STDOUT,
        ).returncode
    result = {
        "label": label,
        "command": command,
        "cwd": str(ROOT),
        "exit": code,
        "seconds": time.monotonic() - start,
        "log": str(log),
        "sha256": sha(log),
    }
    (LOGS / (label + ".json")).write_text(json.dumps(result, indent=2) + "\n")
    if code:
        raise RuntimeError(f"{label}: exit {code}; {log}")
    return result


def code_only(text):
    result = []
    index = 0
    depth = 0
    while index < len(text):
        pair = text[index : index + 2]
        if pair == "/-":
            depth += 1
            result.append(" ")
            index += 2
        elif depth and pair == "-/":
            depth -= 1
            index += 2
        elif depth:
            result.append("\n" if text[index] == "\n" else " ")
            index += 1
        elif pair == "--":
            end = text.find("\n", index)
            index = len(text) if end < 0 else end
        elif text[index] == '"':
            result.append(" ")
            index += 1
            while index < len(text):
                if text[index] == "\\":
                    index += 2
                elif text[index] == '"':
                    index += 1
                    break
                else:
                    index += 1
        else:
            result.append(text[index])
            index += 1
    if depth:
        raise RuntimeError("Unclosed Lean comment")
    return "".join(result)


def imports(path):
    return re.findall(r"^\s*import\s+(\S+)", code_only(path.read_text()), re.M)


def local_path(module):
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*", module):
        raise RuntimeError(f"Invalid local module: {module}")
    path = ROOT / (module.replace(".", "/") + ".lean")
    if path.is_symlink() or not path.resolve().is_relative_to(ROOT):
        raise RuntimeError(f"Local module escapes proof root: {module}")
    return path


def source_path(name):
    relative = Path(name)
    if relative.is_absolute() or ".." in relative.parts:
        raise RuntimeError(f"Invalid verification source: {name}")
    path = ROOT / relative
    if path.is_symlink() or not path.resolve().is_relative_to(ROOT):
        raise RuntimeError(f"Verification source escapes proof root: {name}")
    return path


def axioms(path):
    text = path.read_text()
    lists = re.findall(r"depends on axioms: \[([^\]]*)\]", text)
    found = {a.strip() for row in lists for a in row.split(",") if a.strip()}
    if not found <= STANDARD:
        raise RuntimeError(f"Unexpected axioms in {path}: {found - STANDARD}")
    return len(lists) + text.count("does not depend on any axioms")


def axiom_digest(path):
    text = path.read_text()
    entries = {
        name: sorted(a.strip() for a in row.split(",") if a.strip())
        for name, row in re.findall(r"'(.+)' depends on axioms: \[([^\]]*)\]", text)
    }
    entries.update(
        {name: [] for name in re.findall(r"'(.+)' does not depend on any axioms", text)}
    )
    data = json.dumps(entries, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(data).hexdigest()


def main():
    print(f"Verification logs: {LOGS}", flush=True)
    if (ROOT / "lean-toolchain").read_text().strip() != "leanprover/lean4:v4.19.0":
        raise RuntimeError("Unexpected Lean toolchain")
    version = run("lean-version", ["lean", "--version"])
    if "version 4.19.0" not in Path(version["log"]).read_text():
        raise RuntimeError("Actual compiler differs from pinned Lean")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    config = tomllib.loads((ROOT / "lakefile.toml").read_text())
    if config["require"][0]["rev"] != "c44e0c8ee63ca166450922a373c7409c5d26b00b":
        raise RuntimeError("Unexpected Mathlib revision")
    pins = []
    for package in manifest["packages"]:
        name = package["name"]
        if not re.fullmatch(r"[A-Za-z0-9_]+", name):
            raise RuntimeError("Invalid dependency name")
        path = ROOT / ".lake/packages" / name
        head = subprocess.check_output(
            ["git", "-C", str(path), "rev-parse", "HEAD"], text=True
        ).strip()
        dirty = subprocess.check_output(
            ["git", "--no-optional-locks", "-C", str(path), "status", "--porcelain"],
            text=True,
        )
        if head != package["rev"] or dirty:
            raise RuntimeError(f"Dependency pin/cleanliness failure: {name}")
        pins.append({"name": name, "revision": head})
    (LOGS / "dependency-pins.json").write_text(json.dumps(pins, indent=2) + "\n")
    pending = ["SubspaceBridge.NewmanCompletion"]
    closure = {}
    while pending:
        module = pending.pop()
        if module in closure:
            continue
        path = local_path(module)
        if not path.is_file():
            continue
        text = code_only(path.read_text())
        forbidden = re.search(
            r"\b(sorry|admit|axiom|native_decide|unsafe|partial|extern|implemented_by|"
            r"run_cmd|elab|initialize|run_tac|setEnv|addDecl|trustLevel|skipKernel)\b"
            r"|decide\s*\+\s*native|debug\.skipKernelTC|#eval",
            text,
        )
        if forbidden:
            raise RuntimeError(f"Forbidden shortcut in {module}: {forbidden.group()}")
        closure[module] = sha(path)
        pending.extend(imports(path))
    if len(closure) != 608:
        raise RuntimeError(f"Unexpected principal source closure: {len(closure)}")
    (LOGS / "principal-source-closure.json").write_text(
        json.dumps(closure, indent=2) + "\n"
    )
    checks = json.loads((ROOT / "verification/portable-suite.json").read_text())
    helper_modules = set()
    production_modules = set()
    for check in checks:
        source = source_path(check["source"])
        if (
            type(check.get("expected_axiom_observations")) is not int
            or check["expected_axiom_observations"] < 0
            or not re.fullmatch(
                r"[0-9a-f]{64}", check.get("expected_axiom_map_sha256", "")
            )
        ):
            raise RuntimeError(f"Missing or invalid axiom baseline: {check['source']}")
        if sha(source) != check["sha256"]:
            raise RuntimeError(f"Verification input changed: {check['source']}")
        for module in imports(source):
            if module.startswith("verification."):
                helper_modules.add(module)
            elif local_path(module).is_file():
                production_modules.add(module)
    RESULTS.append(run("default-build", ["lake", "build"]))
    RESULTS.append(
        run("principal-build", ["lake", "build", "SubspaceBridge.NewmanCompletion"])
    )
    RESULTS.append(
        run("historical-imports", ["lake", "build", *sorted(production_modules)])
    )
    lean_path = subprocess.check_output(
        ["lake", "env", "printenv", "LEAN_PATH"], cwd=ROOT, env=ENV, text=True
    ).strip()
    ENV["LEAN_PATH"] = str(LOGS / "objects") + os.pathsep + lean_path
    done = set()

    def build_helper(module):
        if module in done:
            return
        source = local_path(module)
        for dependency in imports(source):
            if dependency.startswith("verification."):
                build_helper(dependency)
        target = LOGS / "objects" / (module.replace(".", "/") + ".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        RESULTS.append(
            run(
                "helper-" + module,
                ["lean", "-o", str(target), str(source)],
                ENV,
            )
        )
        done.add(module)

    for module in sorted(helper_modules):
        build_helper(module)
    for name in ["PortableEndpoint", "PortableClosure"]:
        source = ROOT / "verification" / (name + ".lean")
        result = run(name, ["lean", str(source)], ENV)
        RESULTS.append(result)
        if name == "PortableEndpoint" and axioms(Path(result["log"])) != 5:
            raise RuntimeError("Missing endpoint axiom observations")
        if name == "PortableClosure":
            text = Path(result["log"]).read_text()
            data = json.loads(text[text.index("{") :])
            if set(data["axioms"]) != STANDARD or not data["nodes"]:
                raise RuntimeError("Unexpected principal dependency axiom closure")
            (LOGS / "axiom-summary.json").write_text(
                json.dumps(
                    {"axioms": sorted(data["axioms"]), "constants": len(data["nodes"])},
                    indent=2,
                )
                + "\n"
            )

    def replay(item):
        index, check = item
        source = source_path(check["source"])
        target = LOGS / f"challenge-{index:03d}.lean"
        target.write_bytes(source.read_bytes())
        result = run(f"challenge-{index:03d}", ["lean", "-j1", str(target)], ENV)
        result["source"] = check["source"]
        result["purpose"] = check["purpose"]
        result["axiom_observations"] = axioms(Path(result["log"]))
        result["axiom_map_sha256"] = axiom_digest(Path(result["log"]))
        if (
            result["axiom_observations"] != check["expected_axiom_observations"]
            or result["axiom_map_sha256"] != check["expected_axiom_map_sha256"]
        ):
            raise RuntimeError(f"Historical axiom map changed: {check['source']}")
        if check["source"] == "Audit.lean" and result["axiom_observations"] != 2295:
            raise RuntimeError("Incomplete historical Audit output")
        if "#print axioms" in source.read_text() and not result["axiom_observations"]:
            raise RuntimeError(f"Missing axiom output: {source}")
        return result

    errors = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=3) as executor:
        futures = {executor.submit(replay, item): item for item in enumerate(checks)}
        for future in concurrent.futures.as_completed(futures):
            try:
                result = future.result()
                RESULTS.append(result)
                print(f"PASS {result['source']}", flush=True)
            except Exception as error:
                errors.append(str(error))
                print(f"FAIL {error}", flush=True)
    (LOGS / "results.json").write_text(json.dumps(RESULTS, indent=2) + "\n")
    if errors:
        raise RuntimeError("\n".join(errors))
    print(f"PASS {len(checks)} replay inputs; complete logs: {LOGS}", flush=True)


if __name__ == "__main__":
    try:
        main()
    except Exception as error:
        (LOGS / "failure.txt").write_text(str(error) + "\n")
        print(f"FAIL: {error}; logs: {LOGS}", flush=True)
        raise SystemExit(1)
