#!/usr/bin/env python3
"""Rebuild and scope-check the pinned Liu/de Bruijn–Newman Lean theorem."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
BASE = "49533557838fde36981606aa2098374b09ea8649"
SOURCE = "afd94c7ddf8bea3a3b8bb2e95657cccae463993c"
ARDA = "2b1be6c5023d69aa7c9bc70ee843bdaa1bf383db"
OAI = "adc7f1241b42e322a6451854ab7e4b4c146bf78a"
LIU = "7d10420de90efa2f082a06a342fc7accbd57ab37"
MATHLIB = "d13f23b723b8a846827a245b89c10fc7d3f11612"
REPO = "https://github.com/DrMurphyIsIn/qrh-debruijn-newman.git"
ALLOWED = {"propext", "Quot.sound", "Classical.choice"}
TARGETS = ["ArdaLiuBridge", "ArdaDBNLiu", "AxiomGuardLiuBridge",
           "ArdaDBNLiuChallenge", "ArdaDBNLiuChallengeTampered"]


def run(args, cwd, env=None):
    result = subprocess.run(args, cwd=cwd, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError(f"{' '.join(map(str,args))} failed ({result.returncode}):\n"
                           + result.stdout[-6000:])
    return result.stdout


def sha(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def package_check():
    manifest = json.loads((HERE / "MANIFEST.json").read_text())
    assert manifest["algorithm"] == "sha256"
    for name, expected in manifest["sha256"].items():
        assert sha(HERE / name) == expected, name


def clone_exact(repo, commit, dest):
    run(["git", "init", "--quiet", str(dest)], dest.parent)
    run(["git", "remote", "add", "origin", repo], dest)
    run(["git", "fetch", "--quiet", "--depth=1", "origin", commit], dest)
    run(["git", "checkout", "--quiet", "--detach", commit], dest)
    assert run(["git", "rev-parse", "HEAD"], dest).strip() == commit


def prepare_compat(root):
    """Supply the few GNU utility names used by the publisher's shell recipe."""
    compat = root / "compat"
    compat.mkdir()
    (compat / "python3").symlink_to(sys.executable)
    shasum = compat / "shasum"
    shasum.write_text(f"#!{sys.executable}\n" + '''
import hashlib, pathlib, sys
assert sys.argv[1:5] == ["-a", "256", "-c", "--quiet"]
ok = True
for line in pathlib.Path(sys.argv[5]).read_text().splitlines():
    expected, name = line.split(None, 1)
    path = pathlib.Path(name.lstrip("*").strip())
    if not path.exists() or hashlib.sha256(path.read_bytes()).hexdigest() != expected:
        print(f"checksum failed: {path}", file=sys.stderr)
        ok = False
sys.exit(0 if ok else 1)
''')
    shasum.chmod(0o755)
    patch = compat / "patch"
    patch.write_text("#!/bin/sh\n"
                     "if [ \"$#\" -eq 2 ] && [ \"$1\" = '-p1' ] && "
                     "[ \"$2\" = '--no-backup-if-mismatch' ]; then\n"
                     "  exec /usr/bin/patch -p1\nfi\nexec /usr/bin/patch \"$@\"\n")
    patch.chmod(0o755)
    os.environ["PATH"] = str(compat) + os.pathsep + os.environ["PATH"]


def source_check(source):
    pins = json.loads((HERE / "data/source-files.json").read_text())
    assert pins["commit"] == SOURCE
    assert run(["git", "rev-parse", "HEAD"], source).strip() == SOURCE
    for name, expected in pins["sha256"].items():
        assert sha(source / name) == expected, f"source mismatch: {name}"
    return len(pins["sha256"])


def dependency_check(source, arda, oai_git, liu_git, workspace):
    assert run(["git", "rev-parse", "HEAD"], arda).strip() == ARDA
    assert run(["git", "rev-parse", "HEAD"], oai_git).strip() == OAI
    assert run(["git", "rev-parse", "HEAD"], liu_git).strip() == LIU
    island = arda / "telperion/examples/liu_dbn_bridge"
    judge = arda / "telperion/missions/judge/liu_dbn_bridge"
    run(["diff", "-rq", "-x", "work", str(source / "lean/liu"), str(island)], source)
    run(["diff", "-rq", str(source / "lean/judge_liu"), str(judge)], source)
    for name in ("RH_zeta_zero_free_liu", "RH_dbn_real_zeros_of_liu_unconditional",
                 "RH_dbn_real_zeros_ge_2811857"):
        assert (source / "provenance/registry" / f"{name}.toml").read_bytes() == (
            arda / "telperion/missions/rh/nodes" / f"{name}.toml").read_bytes()
    closure = json.loads((liu_git / "upstream/closure_manifest.json").read_text())
    assert closure["commit"] == OAI and len(closure["modules"]) == 2925
    for name, rec in closure["modules"].items():
        rel = rec["path"]
        assert rel.startswith("vendor/")
        assert sha(workspace / rel[len("vendor/"):]) == rec["sha256"], name
    checksums = (island / "liu_sources.sha256").read_text().splitlines()
    for line in checksums:
        expected, name = line.split(None, 1)
        assert sha(liu_git / name.lstrip("*").strip()) == expected, name
    original = json.loads((oai_git / "lean/lake-manifest.json").read_text())
    actual = json.loads((workspace / "lake-manifest.json").read_text())
    orig_pins = {item["name"]: item.get("rev") for item in original["packages"]}
    actual_pins = {item["name"]: item.get("rev") for item in actual["packages"]}
    assert orig_pins == actual_pins and actual_pins["mathlib"] == MATHLIB
    assert (workspace / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.34.1"
    return len(closure["modules"]), len(checksums), len(actual_pins)


def checked_package_heads(workspace):
    manifest = json.loads((workspace / "lake-manifest.json").read_text())
    patched = 0
    for item in manifest["packages"]:
        name = item["name"].strip("«»")
        checkout = workspace / ".lake/packages" / name
        assert checkout.is_dir(), f"missing dependency: {name}"
        assert run(["git", "rev-parse", "HEAD"], checkout).strip() == item["rev"], name
        patch = workspace / "patches" / f"{name}-lean4341.patch"
        if patch.exists():
            run(["git", "apply", "--reverse", "--check", str(patch)], checkout)
            patched += 1
    return len(manifest["packages"]), patched


def checked_key_files(workspace):
    pins = json.loads((HERE / "data/materialized-key-files.json").read_text())
    for name, expected in pins["sha256"].items():
        assert sha(workspace / name) == expected, f"materialized file mismatch: {name}"
    return len(pins["sha256"])


def verify(source, arda, oai_git, liu_git, workspace, reuse_build):
    source_count = source_check(source)
    closure_count, liu_count, package_count = dependency_check(
        source, arda, oai_git, liu_git, workspace)
    version = run(["lake", "env", "lean", "--version"], workspace).strip()
    assert "version 4.34.1," in version, version
    print(version, flush=True)
    if not reuse_build:
        print("Resolving pinned dependencies and Mathlib cache...", flush=True)
        run(["lake", "update"], workspace)
        run(["lake", "exe", "cache", "get"], workspace)
    print("Checking five Lean targets...", flush=True)
    run(["lake", "build", *TARGETS], workspace)
    checked_packages, patched = checked_package_heads(workspace)
    assert checked_packages == package_count
    key_count = checked_key_files(workspace)
    guard = run(["lake", "env", "lean", "AxiomGuardLiuBridge.lean"], workspace)
    assert "sorryAx" not in guard, guard
    scope = run(["lake", "env", "lean", str(HERE / "code/Scope.lean")], workspace)
    assert "AUDIT_SCOPE=passed" in scope, scope
    axioms = {}
    for label in ("MAIN", "RATIONAL", "LIU"):
        lines = [s for s in scope.splitlines() if s.startswith(f"AUDIT_AXIOMS_{label}=")]
        assert len(lines) == 1, scope
        found = set(filter(None, lines[0].split("=", 1)[1].split(",")))
        assert found <= ALLOWED, found
        axioms[label.lower()] = sorted(found)
    print("Scope and axiom checks passed:", axioms, flush=True)
    run(["lake", "env", "leanchecker", "-v", "ArdaDBNLiu"], workspace)
    print("Kernel replay passed: ArdaDBNLiu", flush=True)
    report = {
        "base_commit": BASE,
        "source_commit": SOURCE,
        "arda_commit": ARDA,
        "openai_commit": OAI,
        "liu_commit": LIU,
        "mathlib_commit": MATHLIB,
        "lean_version": version,
        "source_files_checked": source_count,
        "openai_closure_files_checked": closure_count,
        "liu_source_files_checked": liu_count,
        "dependency_packages_pinned": package_count,
        "compatibility_patches_verified": patched,
        "materialized_key_files_checked": key_count,
        "lake_targets_checked": TARGETS,
        "capstone": "dbn_real_zeros_ge_2811857",
        "axioms": axioms,
        "kernel_module_replayed": "ArdaDBNLiu",
        "build_mode": "reused_local" if reuse_build else "fresh_compile",
        "scope_probe": "passed",
        "build": "passed",
    }
    print(json.dumps(report, indent=2))
    return report


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, help="existing pinned source checkout")
    parser.add_argument("--arda", type=Path, help="existing pinned Arda checkout")
    parser.add_argument("--oai-git", type=Path, help="existing pinned OpenAI checkout")
    parser.add_argument("--liu-git", type=Path, help="existing pinned Liu checkout")
    parser.add_argument("--workspace", type=Path, help="materialized Lean workspace")
    parser.add_argument("--reuse-build", action="store_true")
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    package_check()
    if args.source:
        assert all((args.arda, args.oai_git, args.liu_git, args.workspace))
        report = verify(args.source.resolve(), args.arda.resolve(),
                        args.oai_git.resolve(), args.liu_git.resolve(),
                        args.workspace.resolve(), args.reuse_build)
    else:
        assert not any((args.arda, args.oai_git, args.liu_git, args.workspace, args.reuse_build))
        with tempfile.TemporaryDirectory(prefix="dbn-liu-audit-") as tmp:
            root = Path(tmp)
            prepare_compat(root)
            source, arda, oai, liu = (root / name for name in ("source", "arda", "oai", "liu"))
            clone_exact(REPO, SOURCE, source)
            run(["git", "clone", "--quiet", "--depth=1", "--branch", "qrh-liu-v1.1.0",
                 "https://github.com/DrMurphyIsIn/Arda.git", str(arda)], root)
            clone_exact("https://github.com/openai/math.git", OAI, oai)
            clone_exact("https://github.com/liubaiying101/Slightly-improved-zero-free-half-planes-for-the-quasi-Riemann-hypothesis.git",
                        LIU, liu)
            workspace = arda / "telperion/examples/liu_dbn_bridge/work/oai"
            print("Materializing pinned Lean workspace...", flush=True)
            env = os.environ.copy()
            env["OAI_GIT"] = str(oai)
            run(["bash", str(arda / "telperion/examples/liu_dbn_bridge/liu_materialize.sh"),
                 "--from-local", str(oai / "lean"), "--liu-local", str(liu)], root, env)
            report = verify(source, arda, oai, liu, workspace, False)
    if args.report:
        args.report.write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
