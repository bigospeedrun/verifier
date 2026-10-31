#!/usr/bin/env python3
"""Rebuild the pinned finite-order Hecke 7/8 theorem with local Lean 4.34.1."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
SOURCE = "adc7f1241b42e322a6451854ab7e4b4c146bf78a"
REPO = "https://github.com/openai/math.git"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def run(args, cwd):
    result = subprocess.run(args, cwd=cwd, text=True,
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
    assert (source / "lean/lean-toolchain").read_text().strip() == "leanprover/lean4:v4.34.1"
    return len(names)


def check_dependencies(workspace):
    packages = json.loads((workspace / "lake-manifest.json").read_text())["packages"]
    checked = 0
    for p in packages:
        if p["type"] != "git":
            continue
        directory = p["name"].strip("«»")
        head = run(["git", "rev-parse", "HEAD"], workspace / ".lake/packages" / directory).strip()
        assert head == p["rev"], p["name"]
        checked += 1
    return checked


def verify(source, reuse_build):
    source_count = check_source(source)
    workspace = source / "lean"
    version = run(["lean", "--version"], workspace).strip()
    assert "version 4.34.1," in version, version
    if not reuse_build:
        run(["lake", "update"], workspace)
        run(["lake", "exe", "cache", "get"], workspace)
    run(["lake", "build", "OAI.NumberTheory.DirichletL.Hecke.Nonvanishing"], workspace)
    dependencies = check_dependencies(workspace)
    scope = run(["lake", "env", "lean", str(HERE / "code/Scope.lean")], workspace)
    assert "AUDIT_SCOPE=passed" in scope, scope
    lines = [x for x in scope.splitlines() if x.startswith("AUDIT_AXIOMS=")]
    assert len(lines) == 1, scope
    axioms = set(filter(None, lines[0].split("=", 1)[1].split(",")))
    assert axioms <= ALLOWED, axioms
    run(["lake", "env", "leanchecker", "-v", "OAI.NumberTheory.DirichletL.Hecke.Nonvanishing"], workspace)
    return {"source_commit": SOURCE, "lean_version": version,
            "source_files_checked": source_count, "dependency_git_heads_checked": dependencies,
            "main_theorem": "OAI.SevenEighths.HeckeFamily.LFunction_ne_zero_of_seven_eighths_lt_re",
            "scope_probe": "passed", "axioms": sorted(axioms),
            "kernel_module_replayed": "OAI.NumberTheory.DirichletL.Hecke.Nonvanishing",
            "build": "passed", "build_mode": "reused_local" if reuse_build else "fresh_local"}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, help="existing pinned checkout")
    parser.add_argument("--reuse-build", action="store_true")
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    check_package()
    if args.source:
        report = verify(args.source.resolve(), args.reuse_build)
    else:
        assert not args.reuse_build
        with tempfile.TemporaryDirectory(prefix="hecke-seven-eighths-source-") as tmp:
            source = Path(tmp) / "source"
            clone_exact(source)
            report = verify(source, False)
    if args.report:
        args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
