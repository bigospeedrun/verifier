#!/usr/bin/env python3
"""Replay the pinned all-length Fourier C588 Lean proof on a local host."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
SOURCE = "0e61af6ce0ef712494c93c902baefa314ef7e23c"
REPO = "https://github.com/shea256/fourier-transform-below-nlogn.git"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def run(args, cwd, env=None):
    result = subprocess.run(args, cwd=cwd, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError(f"{' '.join(map(str, args))} failed ({result.returncode}):\n"
                           + result.stdout[-6000:])
    return result.stdout


def sha(path):
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def check_package():
    manifest = json.loads((HERE / "MANIFEST.json").read_text())
    assert manifest["algorithm"] == "sha256"
    files = {str(p.relative_to(HERE)): p for p in HERE.rglob("*") if p.is_file()}
    files.pop("MANIFEST.json")
    assert set(files) == set(manifest["sha256"])
    for name, path in files.items():
        assert not path.is_symlink() and sha(path) == manifest["sha256"][name], name


def clone_exact(dest):
    run(["git", "init", "--quiet", str(dest)], dest.parent)
    run(["git", "remote", "add", "origin", REPO], dest)
    run(["git", "fetch", "--quiet", "--depth=1", "origin", SOURCE], dest)
    run(["git", "checkout", "--quiet", "--detach", "FETCH_HEAD"], dest)


def check_source(source):
    record = json.loads((HERE / "data/source.json").read_text())
    assert record["commit"] == SOURCE
    assert run(["git", "rev-parse", "HEAD"], source).strip() == SOURCE
    assert not run(["git", "status", "--porcelain"], source).strip()
    names = sorted(filter(None, subprocess.check_output(
        ["git", "ls-files", "-z"], cwd=source).split(b"\0")))
    digest = hashlib.sha256()
    total = 0
    for raw in names:
        path = source / os.fsdecode(raw)
        assert path.is_file() and not path.is_symlink(), path
        digest.update(raw + b"\0" + bytes.fromhex(sha(path)))
        total += path.stat().st_size
    assert len(names) == record["tracked_files"]
    assert total == record["tracked_bytes"]
    assert digest.hexdigest() == record["aggregate_sha256"]
    for name, expected in record["key_files_sha256"].items():
        assert sha(source / name) == expected, name
    assert (source / "lean/complex588/lean-toolchain").read_text().strip() == "leanprover/lean4:v4.34.1"
    return len(names)


def check_dependencies(workspace):
    packages = json.loads((workspace / "lake-manifest.json").read_text())["packages"]
    checked = 0
    for p in packages:
        if p["type"] != "git":
            continue
        head = run(["git", "rev-parse", "HEAD"], workspace / ".lake/packages" / p["name"]).strip()
        assert head == p["rev"], p["name"]
        checked += 1
    return checked


def check_logs(logs):
    axioms = (logs / "axioms.log").read_text()
    positive = (logs / "compare-fourier.log").read_text()
    negative = (logs / "compare-negative.log").read_text()
    assert axioms.count("[propext, Classical.choice, Quot.sound]") == 3
    assert "sorryAx" not in axioms
    assert "RESULT: PASS" in positive
    assert "definition body differs" in negative and "decimalExponentC588" in negative
    return {"source_axiom_checks": 3, "positive_comparator": "PASS",
            "stronger_negative_control": "rejected"}


def verify(source, reuse_logs):
    source_count = check_source(source)
    workspace = source / "lean/complex588"
    version = run(["lean", "--version"], workspace).strip()
    assert "version 4.34.1," in version, version
    if reuse_logs:
        logs = reuse_logs.resolve()
        assert logs.is_dir()
        mode = "existing_local_build"
        log_check = check_logs(logs)
    else:
        with tempfile.TemporaryDirectory(prefix="fourier-c588-logs-") as tmp:
            logs = Path(tmp)
            env = os.environ.copy()
            env["PYTHON"] = "python3.12"
            env.setdefault("LEAN_NUM_THREADS", "1")
            output = run(["bash", "scripts/build_and_check.sh", str(logs)], workspace, env)
            assert "ALL CHECKS PASSED" in output, output[-2000:]
            log_check = check_logs(logs)
        mode = "fresh_local_build"
    dependencies = check_dependencies(workspace)
    scope = run(["lake", "env", "lean", str(HERE / "code/Scope.lean")], workspace)
    assert "AUDIT_SCOPE=passed" in scope, scope
    axiom_lines = [x for x in scope.splitlines() if x.startswith("AUDIT_AXIOMS_")]
    assert len(axiom_lines) == 3, scope
    for line in axiom_lines:
        assert set(filter(None, line.split("=", 1)[1].split(","))) <= ALLOWED, line
    run(["lake", "env", "leanchecker", "-v", "Work.FourierC588.Main"], workspace)
    return {"source_commit": SOURCE, "lean_version": version,
            "source_files_checked": source_count, "dependency_git_heads_checked": dependencies,
            "theorems": ["OAI.PowerSaving.transform_mainC588",
                         "OAI.PowerSaving.convolution_mainC588"],
            "scope_probe": "passed", "kernel_module_replayed": "Work.FourierC588.Main",
            "build": "passed", "build_mode": mode, **log_check}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, help="existing pinned checkout")
    parser.add_argument("--reuse-logs", type=Path, help="logs from a completed local build")
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    check_package()
    if args.source:
        report = verify(args.source.resolve(), args.reuse_logs)
    else:
        assert not args.reuse_logs
        with tempfile.TemporaryDirectory(prefix="fourier-c588-source-") as tmp:
            source = Path(tmp) / "source"
            clone_exact(source)
            report = verify(source, None)
    if args.report:
        args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
