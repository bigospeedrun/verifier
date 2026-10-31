#!/usr/bin/env python3
"""Rebuild the pinned H4 exact-repair theorem and check its stated scope."""

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile
import tempfile
import urllib.request

HERE = Path(__file__).resolve().parent
BASE = "49533557838fde36981606aa2098374b09ea8649"
SOURCE = "0d43f182f2ee12e27419ac4d5e32fd2d9b68ab43"
REPO = "https://github.com/erebos-labs/ordered-matrix-removal-4x4"
ALLOWED = {"propext", "Quot.sound", "Classical.choice"}
CACHE_MODULES = [
    "Mathlib.Analysis.SpecificLimits.Normed",
    "Mathlib.Analysis.SpecialFunctions.Pow.Real",
    "Mathlib.Tactic.Linarith", "Mathlib.Tactic.Ring",
    "Mathlib.Tactic.FieldSimp", "Mathlib.Tactic.NormNum",
]


def run(args, cwd):
    result = subprocess.run(args, cwd=cwd, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, check=False)
    if result.returncode:
        raise RuntimeError(f"{' '.join(map(str,args))} failed ({result.returncode}):\n"
                           + result.stdout[-5000:])
    return result.stdout


def sha(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def check_package():
    data = json.loads((HERE / "MANIFEST.json").read_text())
    assert data["algorithm"] == "sha256"
    for name, expected in data["sha256"].items():
        assert sha(HERE / name) == expected, name


def check_source(source):
    pins = json.loads((HERE / "data/source-files.json").read_text())
    assert pins["commit"] == SOURCE and pins["repository"] == REPO
    assert run(["git", "rev-parse", "HEAD"], source).strip() == SOURCE
    for name, expected in pins["sha256"].items():
        assert sha(source / name) == expected, f"source mismatch: {name}"
    run([sys.executable, "checkers/verify_release.py"], source)
    return len(pins["sha256"])


def prepare_dependencies(source):
    record = json.loads((source / "DEPENDENCIES.json").read_text())
    tooling = source / "tooling"
    tooling.mkdir(exist_ok=True)
    mathlib_dir = tooling / "mathlib4-pinned"
    if not mathlib_dir.exists():
        archive = tooling / "mathlib4-pinned.tar.gz"
        if not archive.exists():
            print("Downloading pinned Mathlib source...", flush=True)
            with urllib.request.urlopen(record["mathlib"]["url"], timeout=120) as resp, archive.open("wb") as out:
                shutil.copyfileobj(resp, out)
        assert sha(archive) == record["mathlib"]["archive_sha256"]
        with tarfile.open(archive, "r:gz") as bundle:
            for item in bundle.getmembers():
                path = Path(item.name)
                assert not path.is_absolute() and ".." not in path.parts
            staging = tooling / "mathlib-staging"
            staging.mkdir(exist_ok=False)
            bundle.extractall(staging, filter="data")
        roots = list(staging.iterdir())
        assert len(roots) == 1 and roots[0].is_dir()
        roots[0].rename(mathlib_dir)
        staging.rmdir()
    for name, expected in record["mathlib"]["files"].items():
        assert sha(mathlib_dir / name) == expected, f"Mathlib source mismatch: {name}"
    packages = source / ".lake/packages"
    packages.mkdir(parents=True, exist_ok=True)
    for dep in record["dependencies"]:
        checkout = packages / dep["name"]
        if not checkout.exists():
            run(["git", "clone", "--quiet", dep["url"], str(checkout)], source)
            run(["git", "checkout", "--quiet", dep["rev"]], checkout)
        assert run(["git", "rev-parse", "HEAD"], checkout).strip() == dep["rev"]
        for name, expected in dep["tracked_files"].items():
            assert sha(checkout / name) == expected, f"{dep['name']} source mismatch: {name}"
    return record["mathlib"]["commit"]


def verify(source, reuse_build):
    checked = check_source(source)
    mathlib_commit = prepare_dependencies(source)
    version = run(["lake", "env", "lean", "--version"], source).strip()
    assert "version 4.34.1," in version, version
    print(version, flush=True)
    modules = sorted((source / "OrderedMatrixRemoval4").glob("*.lean"))
    modules.append(source / "OrderedMatrixRemoval4.lean")
    output = source / ".lake/build/lib/lean"
    if reuse_build:
        for path in modules:
            assert (output / path.relative_to(source).with_suffix(".olean")).exists(), path
        print(f"Reusing {len(modules)} project modules from a complete local rebuild", flush=True)
    else:
        print("Downloading pinned Mathlib build cache...", flush=True)
        run(["lake", "exe", "cache", "get", *CACHE_MODULES], source)
        print(f"Compiling {len(modules)} project modules...", flush=True)
        run([sys.executable, "checkers/rebuild_bounded.py"], source)
    scope = run(["lake", "env", "lean", str(HERE / "code/Scope.lean")], source)
    assert "AUDIT_SCOPE=passed" in scope, scope
    lines = [line for line in scope.splitlines() if line.startswith("AUDIT_AXIOMS=")]
    assert len(lines) == 1, scope
    axioms = set(filter(None, lines[0].split("=", 1)[1].split(",")))
    assert axioms <= ALLOWED, axioms
    print("Scope probe passed; transitive axioms:", sorted(axioms), flush=True)
    checker = output / "checkers/ExpectedTerminalStatement.olean"
    checker.parent.mkdir(parents=True, exist_ok=True)
    run(["lake", "env", "lean", "checkers/ExpectedTerminalStatement.lean",
         "-o", str(checker)], source)
    run(["lake", "env", "leanchecker", "-v", "OrderedMatrixRemoval4.TerminalAnchorCount"], source)
    run(["lake", "env", "leanchecker", "-v", "checkers.ExpectedTerminalStatement"], source)
    print("Kernel replay passed: capstone and semantic checker", flush=True)
    report = {
        "base_commit": BASE,
        "source_commit": SOURCE,
        "source_files_checked": checked,
        "mathlib_commit": mathlib_commit,
        "lean_version": version,
        "capstone": "OrderedMatrixRemoval4.Host.TerminalAnchorRepair.exact_minimum",
        "axioms": sorted(axioms),
        "project_modules_compiled": len(modules),
        "modules_kernel_replayed": 2,
        "build_mode": "reused_local" if reuse_build else "fresh_compile",
        "scope_probe": "passed",
        "build": "passed",
    }
    print(json.dumps(report, indent=2))
    return report


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, help="existing checkout at pinned commit")
    parser.add_argument("--reuse-build", action="store_true",
                        help="reuse a previous complete local source rebuild")
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    check_package()
    if args.source:
        report = verify(args.source.resolve(), args.reuse_build)
    else:
        assert not args.reuse_build
        with tempfile.TemporaryDirectory(prefix="h4-repair-audit-") as temp:
            source = Path(temp) / "source"
            run(["git", "clone", "--quiet", REPO, str(source)], Path(temp))
            run(["git", "checkout", "--quiet", SOURCE], source)
            report = verify(source, False)
    if args.report:
        args.report.write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
