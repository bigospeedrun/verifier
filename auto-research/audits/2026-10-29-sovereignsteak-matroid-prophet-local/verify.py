#!/usr/bin/env python3
"""Rebuild the pinned one-sample matroid prophet inequality locally."""

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
    comparator = (source / "lean/ComparatorChallenges/MatroidProphet.lean").read_text()
    model = (source / "lean/OAI/Probability/MatroidProphet/Model.lean").read_text()
    comparator_defs = comparator[comparator.index("abbrev Weights"):
                                 comparator.index("theorem one_sample")]
    model_defs = model[model.index("abbrev Weights"):
                       model.index("end MatroidProphet")]
    assert comparator_defs.rstrip() == model_defs.rstrip(), "comparator/model definitions differ"
    assert (source / "lean/lean-toolchain").read_text().strip() == "leanprover/lean4:v4.34.1"
    return len(names)


def check_dependencies(workspace):
    packages = json.loads((workspace / "lake-manifest.json").read_text())["packages"]
    overlay = json.loads((HERE / "data/dependency-overlay.json").read_text())
    assert overlay["algorithm"] == "sha256"
    assert set(overlay["packages"]) == {p["name"].strip("«»") for p in packages if p["type"] == "git"}
    checked = 0
    changed = 0
    for p in packages:
        if p["type"] != "git":
            continue
        directory = p["name"].strip("«»")
        checkout = workspace / ".lake/packages" / directory
        head = run(["git", "rev-parse", "HEAD"], checkout).strip()
        assert head == p["rev"], p["name"]
        expected = overlay["packages"][directory]
        assert expected["rev"] == head, directory
        status = subprocess.check_output(
            ["git", "status", "--porcelain", "-z", "--untracked-files=all"],
            cwd=checkout)
        files = {}
        for entry in filter(None, status.split(b"\0")):
            code = entry[:2].decode("ascii")
            assert code in {" M", "??"}, (directory, entry)
            name = os.fsdecode(entry[3:])
            path = checkout / name
            assert path.is_file() and not path.is_symlink(), path
            files[name] = {"status": code, "sha256": sha(path)}
        assert files == expected["changed_files"], directory
        checked += 1
        changed += len(files)
    return checked, changed


def verify(source, reuse_build):
    source_count = check_source(source)
    workspace = source / "lean"
    version = run(["lean", "--version"], workspace).strip()
    assert "version 4.34.1," in version, version
    if not reuse_build:
        run(["lake", "update"], workspace)
        run(["lake", "exe", "cache", "get"], workspace)
    modules = ["OAI.Probability.MatroidProphet.Main"]
    run(["lake", "build", *modules], workspace)
    dependencies, changed_dependency_files = check_dependencies(workspace)
    scope = run(["lake", "env", "lean", str(HERE / "code/Scope.lean")], workspace)
    assert "AUDIT_SCOPE=passed" in scope, scope
    lines = [x for x in scope.splitlines() if x.startswith("AUDIT_AXIOMS_")]
    assert len(lines) == 1, scope
    axioms = {}
    for line in lines:
        name, values = line.split("=", 1)
        found = set(filter(None, values.split(",")))
        assert found <= ALLOWED, found
        axioms[name.removeprefix("AUDIT_AXIOMS_")] = sorted(found)
    for module in modules:
        run(["lake", "env", "leanchecker", "-v", module], workspace)
    return {"source_commit": SOURCE, "lean_version": version,
            "comparator_model_definitions": "exact_match",
            "source_files_checked": source_count, "dependency_git_heads_checked": dependencies,
            "dependency_overlay_files_checked": changed_dependency_files,
            "theorems": ["OAI.MatroidProphet.one_sample"],
            "scope_probe": "passed", "axioms": axioms,
            "kernel_modules_replayed": modules,
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
        with tempfile.TemporaryDirectory(prefix="matroid-prophet-source-") as tmp:
            source = Path(tmp) / "source"
            clone_exact(source)
            report = verify(source, False)
    if args.report:
        args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
