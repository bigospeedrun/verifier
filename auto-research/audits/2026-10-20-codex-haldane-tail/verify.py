"""Replay a pinned conditional Haldane certificate without network access."""

import argparse
import difflib
from fractions import Fraction as Q
from hashlib import sha256
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def integrity():
    manifest = json.loads((ROOT / "MANIFEST.json").read_text())
    require(manifest["algorithm"] == "sha256", "Digest algorithm changed")
    files = {str(p.relative_to(ROOT)) for p in ROOT.rglob("*")
             if p.is_file() and p != ROOT / "MANIFEST.json"}
    require(files == set(manifest["sha256"]), "Package file set changed")
    for name, expected in manifest["sha256"].items():
        path = ROOT / name
        require(not path.is_symlink(), "Package contains a symlink")
        require(not path.stat().st_mode & 0o111, "Package contains an executable file")
        require(digest(path) == expected, f"Package hash mismatch: {name}")
    pins = json.loads((ROOT / "SOURCE-PINS.json").read_text())
    for name, expected in pins["files_sha256"].items():
        require(digest(ROOT / "upstream" / name) == expected,
                f"Pinned source mismatch: {name}")
    original = (ROOT / "upstream/verify_quarter_refinement.py").read_text()
    modified = (ROOT / "code/verify_quarter_tightened.py").read_text()
    patch = "".join(difflib.unified_diff(original.splitlines(True), modified.splitlines(True),
                                       fromfile="a/verify_quarter_refinement.py",
                                       tofile="b/verify_quarter_refinement.py", n=0))
    require(patch == (ROOT / "code/quarter-tightening.patch").read_text(),
            "Recorded patch differs from checker changes")


def replay(work, baseline=False):
    if not baseline:
        shutil.copyfile(ROOT / "code/verify_quarter_tightened.py",
                        work / "verify_quarter_refinement.py")
    env = os.environ.copy()
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    env.pop("PYTHONOPTIMIZE", None)
    completed = subprocess.run([sys.executable, "-B", "verify_quarter_refinement.py"],
                               cwd=work, env=env, text=True, capture_output=True)
    print(completed.stdout, end="", flush=True)
    require(completed.returncode == 0, "Checker failed:\n" + completed.stderr)
    result = json.loads((work / "independent_results/quarter_refinement.json").read_text())
    require(result["success"] is True and len(result["checks"]) == 381,
            "Unexpected check count or result")
    require(all(c["passed"] is True for c in result["checks"]), "A check did not pass")
    return result


def independently_check_tail(work, result):
    # Reuse only the directed exponential enclosure from the pinned arithmetic.
    # The following comparisons independently inspect the generated final row.
    sys.path.insert(0, str(work))
    spec = importlib.util.spec_from_file_location("tightened", work / "verify_quarter_refinement.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    tail = result["tail"]
    p, q = Q(result["rows"][-1]["p"]), Q(result["rows"][-1]["q"])
    w, beta = Q(tail["w0"]), Q(tail["beta0"])
    require(tail["n0"] == 21504 and beta == 12544 and tail["start"] == 32256,
            "Reference scale changed")
    require(Q(tail["C"]) == Q(tail["B"]) == Q(201, 100), "Tail constants changed")
    require(p ** 3 <= w ** 2 / 1000000 and q <= w <= Q(1, 1000000),
            "Stronger initial invariant failed")
    exponential = module.exp_upper(beta * Q(1517, 10000))
    require(exponential * Q(201, 100) * w < 1, "Tail rate comparison failed")
    require(exponential * Q(201, 100) * w / (1 - Q(201, 100) * w) < 1,
            "Tail prefactor comparison failed")
    old_accepts = (exponential * 6 * w < 1 and
                   exponential * Q(15, 2) * w / (1 - Q(15, 2) * w) < 1)
    require(not old_accepts, "Old tail unexpectedly accepts the stronger target")
    print("PASS: old tail rejects 0.1517, strengthened tail accepts it.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline", action="store_true",
                        help="Also replay the unmodified 0.1515 certificate")
    options = parser.parse_args()
    integrity()
    with tempfile.TemporaryDirectory(prefix="speedrun-haldane-") as temporary:
        work = Path(temporary) / "source"
        shutil.copytree(ROOT / "upstream", work)
        if options.baseline:
            print("Replaying the unmodified 0.1515 certificate...", flush=True)
            replay(work, baseline=True)
        print("Replaying the 0.1517 certificate...", flush=True)
        result = replay(work)
        expected = json.loads((ROOT / "evidence/quarter_refinement.json").read_text())
        require(result == expected, "Generated certificate differs from the recorded evidence")
        require("1517/10000" in result["statement"], "Wrong target in certificate")
        independently_check_tail(work, result)
    print("PASS: 381 exact checks, complete finite cover, and strengthened infinite tail.")
    print("CONDITIONAL: gamma_L > 1517/10000 for every integer L >= 24, J=1.")


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, OSError, ValueError, KeyError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        sys.exit(1)
