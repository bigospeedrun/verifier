"""Offline package validation; pass --live to also query the recorded GitHub run."""

import hashlib
import json
from pathlib import Path
import re
import sys
import urllib.request


PACKAGE = Path(__file__).resolve().parent
REPO = PACKAGE.parents[2]
BASE = "1e009d7adeb43a1ddffe8b8148be4bebba69e720"
SOURCE = "50672b810873d8371b2b6bdd0057bb6cb2e3da24"
MATHLIB = "065356127b1dc0016f66b7283ce0ce2c4055aa55"
TOOLCHAIN = "leanprover/lean4:v4.35.0-rc2"


def require(ok, message):
    if not ok:
        raise ValueError(message)


def read_json(path):
    return json.loads(path.read_text())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_hashes(root, entries):
    for name, expected in entries.items():
        relative = Path(name)
        require(not relative.is_absolute() and ".." not in relative.parts,
                f"unsafe manifest path: {name}")
        path = root / relative
        require(path.is_file() and not path.is_symlink(), f"not a plain file: {path}")
        require(not path.stat().st_mode & 0o111, f"executable file: {path}")
        require(sha(path) == expected, f"hash mismatch: {path}")


def without_comments(text):
    # Lean block comments can nest. The delivered Lean has no string literals.
    out = []
    i = depth = 0
    while i < len(text):
        pair = text[i:i + 2]
        if pair == "/-":
            depth += 1
            i += 2
        elif depth and pair == "-/":
            depth -= 1
            i += 2
            out.append(" ")
        elif depth:
            i += 1
        elif pair == "--":
            end = text.find("\n", i)
            i = len(text) if end == -1 else end
        else:
            out.append(text[i])
            i += 1
    require(depth == 0, "unclosed Lean block comment")
    return "".join(out)


def main():
    require(sys.argv[1:] in ([], ["--live"]), "usage: python3 verify.py [--live]")
    manifest = read_json(PACKAGE / "MANIFEST.json")
    require(manifest["algorithm"] == "sha256", "unsupported manifest algorithm")
    actual = set()
    for path in PACKAGE.rglob("*"):
        require(not path.is_symlink(), f"symlink in package: {path}")
        require(path.is_file() or path.is_dir(), f"not a plain file or directory: {path}")
        if path.is_file() and path != PACKAGE / "MANIFEST.json":
            actual.add(path.relative_to(PACKAGE).as_posix())
    require(actual == set(manifest["sha256"]), "package manifest coverage mismatch")
    check_hashes(PACKAGE, manifest["sha256"])
    targets = read_json(PACKAGE / "data/TARGETS.json")
    require(targets["algorithm"] == "sha256", "unsupported target hash algorithm")
    require(set(targets["sha256"]) == {
        "challenges/catalan/Statement.lean", "challenges/catalan/README.md",
        "challenges/catalan/LICENSE"}, "unexpected challenge file set")
    check_hashes(REPO, targets["sha256"])
    print(f"PASS: {len(actual)} package files and 3 challenge files match SHA-256")

    result = read_json(PACKAGE / "RESULT.json")
    require(result["base_commit"] == BASE and result["track"] == "lean-statements"
            and result["status"] == "statement", "result metadata mismatch")
    sources = read_json(PACKAGE / "data/SOURCES.json")
    require(sources["commit"] == SOURCE and sources["mathlib_commit"] == MATHLIB
            and sources["lean_toolchain"] == TOOLCHAIN, "source pin mismatch")
    check_hashes(PACKAGE, {k: v["sha256"] for k, v in sources["files"].items()})
    require(sha(REPO / "challenges/catalan/LICENSE") == sources["license_sha256"],
            "source license mismatch")
    upstream = read_json(PACKAGE / "data/source-lake-manifest.json")
    require(next(p["rev"] for p in upstream["packages"] if p["name"] == "mathlib")
            == MATHLIB, "upstream Mathlib pin mismatch")
    runner = (PACKAGE / "code/verify-lean.sh").read_text()
    require(MATHLIB in runner and TOOLCHAIN in runner, "runner dependency pins mismatch")
    template = (PACKAGE / "data/Challenge.lean").read_text()
    require(len(re.findall(r"\bsorry\b", without_comments(template))) == 9,
            "unexpected source template holes")
    for path in [REPO / "challenges/catalan/Statement.lean", PACKAGE / "code/Validation.lean"]:
        lean = without_comments(path.read_text())
        require(not re.search(r"\b(sorry|admit|axiom|unsafe|native_decide|implemented_by|run_tac)\b",
                              lean), f"unpermitted token: {path}")
        require(not re.search(r"\bimport\s+.*Challenge", lean), "source template imported")
    print("PASS: source pins, reference-only template, and no proof holes in delivered Lean")

    receipt = read_json(PACKAGE / "evidence/lean-check.json")
    require(receipt["conclusion"] == "success", "recorded Lean check did not pass")
    require(receipt["repository"] == "1337isnot1337/verifier", "unexpected runner repository")
    require(re.fullmatch(r"[0-9a-f]{40}", receipt["head_sha"]) is not None,
            "run commit is not pinned")
    check_hashes(REPO, receipt["tested_files_sha256"])
    require(set(receipt["tested_files_sha256"]) == {
        "challenges/catalan/Statement.lean",
        str((PACKAGE / "code/Validation.lean").relative_to(REPO)),
        str((PACKAGE / "code/verify-lean.sh").relative_to(REPO)),
        str((PACKAGE / "code/check-catalan.yml").relative_to(REPO)),
    }, "incomplete tested-source list")
    report = (PACKAGE / "evidence/axioms.txt").read_text()
    expected_theorems = ["source_740_shape", "source_740_implies_bound", "bound_mono",
                         "zero_has_upperBound_one", "no_bound_zero"]
    for name in expected_theorems:
        require("CatalanStatementValidation." + name in report,
                f"missing axiom report: {name}")
    require("sorryAx" not in report, "sorryAx in recorded axiom report")
    for axiom_list in re.findall(r"depends on axioms:\s*\[([^\]]*)\]", report):
        axioms = {a.strip() for a in axiom_list.split(",") if a.strip()}
        require(axioms <= {"propext", "Quot.sound", "Classical.choice"},
                f"unexpected recorded axioms: {axioms}")
    print("PASS: recorded Lean success and five allowed-axiom reports match the tested sources")

    if sys.argv[1:] == ["--live"]:
        url = ("https://api.github.com/repos/" + receipt["repository"]
               + "/actions/runs/" + str(receipt["run_id"]))
        request = urllib.request.Request(url, headers={"User-Agent": "catalan-statement-package"})
        with urllib.request.urlopen(request, timeout=30) as response:
            run = json.load(response)
        require(run["head_sha"] == receipt["head_sha"]
                and run["conclusion"] == "success"
                and run["status"] == "completed", "live GitHub run mismatch")
        print("PASS: live GitHub Actions run confirms recorded commit and success")

    print("PASS: package integrity and recorded Lean source correspondence")
    print("LIMIT: this does not rerun Lean or Comparator and does not prove a Catalan bound")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, KeyError) as error:
        print("FAIL:", error, file=sys.stderr)
        sys.exit(1)
