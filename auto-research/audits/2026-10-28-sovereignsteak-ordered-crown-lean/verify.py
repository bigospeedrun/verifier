#!/usr/bin/env python3
"""Independently rebuild and kernel-check the pinned ordered-crown Lean claim."""

import argparse
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile

BASE = "49533557838fde36981606aa2098374b09ea8649"
SOURCE = "35f5784da66428f27e568ede22a9f1163403fa9a"
REPO = "https://github.com/shea256/ordered-binary-matrix-removal.git"
PINS = {
    "formal/OrderedRemoval/Crown/Model.lean": "7063ddaab7ac090a7a27f62001abf12d417d7869de27a1afded34b51fc324be3",
    "formal/OrderedRemoval/Crown/Complete.lean": "5199f242f9c8e203323e635e74ad33cd6b50df64cdef092650b052f887df64d8",
    "formal/OrderedRemoval/Model.lean": "1fa8211ce68801b690d85faefea98efb7eba3598ccf4d4e9f4ca7067df528644",
    "formal/lakefile.toml": "4fb7ab5a685ff624279b673cdb70f0fc27d4d2f285bc5e183e21e5f3390915b2",
    "formal/lake-manifest.json": "c1ae45156cf8ce00629518514bcbc658602841fdf7eb3fbf786e0ba3ab009b52",
    "formal/lean-toolchain": "d5edba4e4b8faad9c1baeadb265716d20d03be4d1a2647dc5e35b0c0325bea7b",
}
ALLOWED = {"propext", "Quot.sound", "Classical.choice"}
HERE = Path(__file__).resolve().parent


def run(args, cwd, *, capture=True):
    p = subprocess.run(args, cwd=cwd, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, check=False)
    if p.returncode:
        raise RuntimeError(f"{' '.join(args)} failed ({p.returncode}):\n{p.stdout[-4000:]}")
    return p.stdout if capture else ""


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_package():
    manifest = json.loads((HERE / "MANIFEST.json").read_text())
    assert manifest["algorithm"] == "sha256"
    for name, digest in manifest["sha256"].items():
        assert sha(HERE / name) == digest, name


def project_sources(formal):
    paths = [formal / "OrderedRemoval.lean"] + sorted(
        (formal / "OrderedRemoval").rglob("*.lean"))
    return {".".join(p.relative_to(formal).with_suffix("").parts): p
            for p in paths}


def compile_project(formal, sources):
    dependencies = {}
    for module, path in sources.items():
        imports = re.findall(r"^import\s+(\S+)", path.read_text(), re.M)
        dependencies[module] = set(imports) & sources.keys()
    done, running = set(), {}
    pending = set(sources)
    output_root = formal / ".lake" / "build" / "lib" / "lean"

    def compile_one(module):
        target = output_root / (module.replace(".", "/") + ".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        run(["lake", "env", "lean", str(sources[module]), "-o", str(target)], formal)
        return module

    with ThreadPoolExecutor(max_workers=32) as pool:
        while pending or running:
            ready = sorted(m for m in pending if dependencies[m] <= done)
            for module in ready[:max(0, 32 - len(running))]:
                pending.remove(module)
                running[pool.submit(compile_one, module)] = module
            assert running, f"import cycle or missing project dependency: {pending}"
            finished, _ = wait(running, return_when=FIRST_COMPLETED)
            for future in finished:
                module = running.pop(future)
                future.result()
                done.add(module)
                if len(done) % 20 == 0 or len(done) == len(sources):
                    print(f"Lean compilation: {len(done)}/{len(sources)} modules", flush=True)


def verify(source, reuse_build=False):
    all_sources = json.loads((HERE / "data" / "source-files.json").read_text())
    assert all_sources["commit"] == SOURCE
    for name, digest in all_sources["sha256"].items():
        assert sha(source / name) == digest, f"tracked source mismatch: {name}"
    for name, digest in PINS.items():
        assert sha(source / name) == digest, f"source pin mismatch: {name}"
    if (source / ".git").exists():
        assert run(["git", "rev-parse", "HEAD"], source).strip() == SOURCE

    formal = source / "formal"
    if not reuse_build:
        run(["lake", "update"], formal)
    version = run(["lake", "env", "lean", "--version"], formal).strip()
    assert "version 4.34.1," in version, version
    print(version, flush=True)
    sources = project_sources(formal)
    if reuse_build:
        output_root = formal / ".lake" / "build" / "lib" / "lean"
        assert all((output_root / (m.replace(".", "/") + ".olean")).exists()
                   for m in sources), "a project OLean is missing"
        print(f"Reusing {len(sources)} project modules from the previous complete compile", flush=True)
    else:
        print("Fetching pinned Mathlib build cache...", flush=True)
        run(["lake", "exe", "cache", "get"], formal)
        # Force extraction: an interrupted earlier build can leave a trace file
        # without its OLean, which the cache's ordinary extraction skips.
        run(["lake", "exe", "cache", "unpack!"], formal)
        print(f"Compiling {len(sources)} project modules...", flush=True)
        compile_project(formal, sources)

    probe = run(["lake", "env", "lean", str(HERE / "code" / "Scope.lean")], formal)
    assert "AUDIT_SCOPE=passed" in probe, probe
    axiom_lines = [line for line in probe.splitlines() if line.startswith("AUDIT_AXIOMS=")]
    assert len(axiom_lines) == 1, probe
    axioms = set(filter(None, axiom_lines[0].split("=", 1)[1].split(",")))
    assert axioms <= ALLOWED, axioms
    print("Scope probe passed; transitive axioms:", sorted(axioms), flush=True)

    # Recheck the capstone proof term in its imported environment. This does
    # not replay every Mathlib or project dependency into an empty environment.
    modules = ["OrderedRemoval.Crown.Complete"]
    for index, module in enumerate(modules, 1):
        run(["lake", "env", "leanchecker", "-v", module], formal)
        print(f"Kernel replay: {index}/{len(modules)} capstone module", flush=True)
    report = {
        "base_commit": BASE,
        "source_commit": SOURCE,
        "lean_version": version,
        "source_sha256": PINS,
        "capstone": "OrderedRemoval.Crown.no_polynomial_removal_bound",
        "axioms": sorted(axioms),
        "modules_kernel_replayed": len(modules),
        "project_modules_compiled": len(sources),
        "tracked_source_files_checked": len(all_sources["sha256"]),
        "build_mode": "reused_local" if reuse_build else "fresh_compile",
        "scope_probe": "passed",
        "build": "passed",
    }
    print(json.dumps(report, indent=2))
    return report


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, help="existing checkout at the pinned commit")
    parser.add_argument("--report", type=Path, help="write JSON result to this path")
    parser.add_argument("--reuse-build", action="store_true",
                        help="reuse a previous complete local compile after changing only this probe")
    args = parser.parse_args()
    check_package()
    if args.source:
        report = verify(args.source.resolve(), args.reuse_build)
    else:
        assert not args.reuse_build, "--reuse-build requires --source"
        with tempfile.TemporaryDirectory(prefix="ordered-crown-audit-") as td:
            source = Path(td) / "source"
            run(["git", "clone", "--quiet", REPO, str(source)], Path(td))
            run(["git", "checkout", "--quiet", SOURCE], source)
            report = verify(source)
    if args.report:
        args.report.write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
