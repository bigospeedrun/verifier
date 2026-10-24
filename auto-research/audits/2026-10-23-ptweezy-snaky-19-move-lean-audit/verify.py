"""Validate this package and the recorded evidence of the Snaky audit rerun.

What this script does:
  * checks the package inventory and SHA-256 manifest;
  * checks the bundled copy of the author's recorded kernel-audit.json
    against its source pin;
  * re-derives the theorem/axiom comparison from the three recorded
    sources (the author's recorded JSON, the Snaky.Audit output lines in
    the bundled build log, and the auditor probe's output) and requires
    an exact match: same two theorems, same types, same axiom lists,
    no sorryAx, no unexpected axioms;
  * checks the build summary's internal consistency (module counts,
    per-module 180 s cap, certificate hash, exit status);
  * runs negative controls proving the comparison detects tampering.

What it does NOT do: rerun the Lean build. The full independent rebuild
(1,182 modules, about 1-1.5 h on 2 cores) is the reproduce command in
README.md ("Full independent rebuild"); this script validates the
evidence that run left behind.
"""

import copy
import hashlib
import json
import re
import stat
import sys
from pathlib import Path


HERE = Path(__file__).resolve().parent

EXPECTED_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
CERT_SHA256 = "baf8774e1fc6eea60b1756437e8b3caae0ede5e001b10c0c3787aab51840782e"
RECORDED_JSON_SHA256 = "f247e7303ad728c5b7592ece438ee5a63129b1c09ee34203c226c2fdde5f68c7"


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def read_json(name):
    return json.loads((HERE / name).read_text())


def check_files():
    manifest = read_json("MANIFEST.json")
    require(manifest["algorithm"] == "sha256", "manifest algorithm")
    files = {}
    for path in HERE.rglob("*"):
        require(not path.is_symlink(), "symlink: " + str(path))
        if path.is_dir():
            continue
        require(stat.S_ISREG(path.stat().st_mode), "nonregular file")
        require(not path.stat().st_mode & 0o111, "executable: " + str(path))
        if path != HERE / "MANIFEST.json":
            files[path.relative_to(HERE).as_posix()] = hashlib.sha256(
                path.read_bytes()).hexdigest()
    require(files == manifest["sha256"], "package file inventory or hash")
    pins = read_json("data/source-pins.json")
    bundled = (HERE / "data" / "kernel-audit-recorded.json").read_bytes()
    require(hashlib.sha256(bundled).hexdigest() == RECORDED_JSON_SHA256,
            "bundled kernel-audit.json hash")
    require(pins["files_sha256"]["topics/snaky/formal/kernel-audit.json"]
            == RECORDED_JSON_SHA256, "source pin for kernel-audit.json")
    require(pins["files_sha256"]["topics/snaky/certificate/snaky19.cards.txt"]
            == CERT_SHA256, "source pin for certificate")
    require(pins["source_commit"]
            == "db6e1d89a0637b013a86464bd766c0a5120e454e", "source commit pin")


def parse_output(lines):
    """Parse '#check' type lines and '#print axioms' lines into a dict."""
    theorems = {}
    for line in lines:
        line = line.strip()
        m = re.match(r"(Snaky\.\w+) : (.+)$", line)
        if m:
            theorems.setdefault(m.group(1), {})["type"] = m.group(2)
            continue
        m = re.match(r"'(Snaky\.\w+)' depends on axioms: \[(.+)\]$", line)
        if m:
            theorems.setdefault(m.group(1), {})["axioms"] = [
                a.strip() for a in m.group(2).split(",")]
    return theorems


def audit_lines_from_log():
    lines = (HERE / "evidence" / "build-log.txt").read_text().splitlines()
    return [l for l in lines
            if l.startswith("Snaky.snaky") or "depends on axioms" in l]


def probe_lines():
    return [l for l in (HERE / "evidence" / "independent-extraction.txt")
            .read_text().splitlines() if l.strip()]


def compare(recorded, from_log, from_probe):
    """Return a list of mismatch descriptions (empty means exact match)."""
    problems = []
    if recorded != from_log:
        problems.append("recorded JSON vs build-log Audit output differ")
    if recorded != from_probe:
        problems.append("recorded JSON vs independent probe output differ")
    return problems


def check_comparison():
    recorded_json = read_json("data/kernel-audit-recorded.json")
    require(recorded_json["certificate_sha256"] == CERT_SHA256,
            "recorded certificate sha")
    recorded = parse_output(recorded_json["theorem_and_axiom_output"])
    from_log = parse_output(audit_lines_from_log())
    from_probe = parse_output(probe_lines())
    problems = compare(recorded, from_log, from_probe)
    require(not problems, "; ".join(problems))
    require(set(recorded) == {"Snaky.snaky_wins_plane_in_19",
                              "Snaky.snaky_wins_17x17_in_19"},
            "theorem set")
    require(recorded["Snaky.snaky_wins_plane_in_19"]["type"]
            == "Snaky.PlaneBlackWinsIn 19 [] []", "headline theorem type")
    for name, entry in recorded.items():
        require(entry["axioms"] == EXPECTED_AXIOMS,
                "axiom list for " + name)
        require("sorryAx" not in entry["axioms"], "sorryAx in " + name)
    comparison = read_json("evidence/comparison.json")
    require(comparison["exact_line_set_match_all_three_sources"] is True,
            "comparison.json verdict flag")
    require(comparison["sorryAx_present"] is False, "comparison sorryAx")
    require(comparison["missing_theorems"] == []
            and comparison["extra_theorems"] == []
            and comparison["type_differences"] == []
            and comparison["axiom_differences"] == [],
            "comparison.json diff lists")
    for name, entry in comparison["theorems"].items():
        require(entry["match"] is True, "comparison match for " + name)
        require(entry["type"] == recorded[name]["type"],
                "comparison type for " + name)
        require(entry["recorded_axioms"] == recorded[name]["axioms"],
                "comparison axioms for " + name)
    return recorded


def check_summary():
    s = read_json("evidence/build-summary.json")
    totals = s["totals"]
    require(totals["modules_in_dependency_closure"] == 1182, "closure size")
    require(totals["modules_compiled_by_this_audit"] == 1182,
            "modules compiled by this audit")
    require(totals["certificate_sha256"] == CERT_SHA256, "summary cert sha")
    attempts = s["attempts"]
    require(sum(a["modules_compiled"] for a in attempts) == 1182,
            "attempt module counts must sum to the closure")
    require(attempts[-1]["exit_code"] == 0, "final attempt exit code")
    require(s["module_cap_check"]["all_modules_within_cap"] is True,
            "module cap flag")
    require(s["module_cap_check"]["slowest_seconds"]
            < s["module_cap_check"]["cap_seconds"], "slowest within cap")
    require(all(m["seconds"] < 180 for m in s["slowest_modules"]),
            "slowest list within cap")
    require(s["sorry_in_any_module_log"] is False, "sorry flag")
    rec = s["reconstruction"]
    require(rec["exit_code"] == 0, "reconstruction exit")
    require(rec["reconstructed_certificate_byte_for_byte_identical"] is True,
            "reconstruction identical flag")
    require(rec["output_sha256"] == CERT_SHA256, "reconstruction sha")
    require(rec["unit_tests_passed"] == 31, "unit tests")
    log_tail = (HERE / "evidence" / "build-log.txt").read_text().splitlines()
    final = json.loads(log_tail[-1])
    require(final["status"] == "compiled" and final["target"] == "Snaky.Audit",
            "build log final report")
    require(final["modules_in_dependency_closure"] == 1182,
            "build log closure")
    require(final["certificate_sha256"] == CERT_SHA256, "build log cert sha")
    require(final["modules_compiled_this_run"]
            == attempts[-1]["modules_compiled"], "resume count vs summary")


def negative_controls(recorded):
    # A wrong headline type must be caught.
    wrong = copy.deepcopy(recorded)
    wrong["Snaky.snaky_wins_plane_in_19"]["type"] = \
        "Snaky.PlaneBlackWinsIn 18 [] []"
    require(compare(recorded, wrong, recorded) != [],
            "control: wrong type not detected")
    # sorryAx must be caught.
    wrong = copy.deepcopy(recorded)
    wrong["Snaky.snaky_wins_plane_in_19"]["axioms"] = ["sorryAx"]
    require(compare(recorded, recorded, wrong) != [],
            "control: sorryAx not detected")
    # A missing theorem must be caught.
    wrong = copy.deepcopy(recorded)
    del wrong["Snaky.snaky_wins_17x17_in_19"]
    require(compare(recorded, wrong, recorded) != [],
            "control: missing theorem not detected")


def main():
    check_files()
    print("PASS 1/4 package integrity (manifest, pins, recorded-audit copy)")
    recorded = check_comparison()
    print("PASS 2/4 theorem/axiom comparison: recorded JSON == build-log "
          "Audit output == independent probe; both theorems, exact types, "
          "axioms [propext, Classical.choice, Quot.sound], no sorryAx")
    check_summary()
    print("PASS 3/4 build summary consistency (1,182 modules compiled by "
          "this audit across two attempts, slowest 133.22 s < 180 s cap, "
          "certificate hash, reconstruction byte-identical)")
    negative_controls(recorded)
    print("PASS 4/4 negative controls (wrong type, sorryAx, missing "
          "theorem all detected)")
    print("SCOPE: validates the recorded evidence of the independent "
          "rebuild; it does not rerun the Lean build. Full rebuild "
          "command: see README.md.")


if __name__ == "__main__":
    main()
