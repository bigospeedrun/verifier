"""Independently recompute the Sidorenko residual finite maximum.

This verifies the finite computation behind the Claimed bound C <= 189 for
the nondirect residual constant: it rebuilds the allowed pair graph from
the bundled faces and cut bits, re-derives the degree sequence and the
closed form, and exhausts all 8,192 supports and 55,173 relaxed defect-one
strata in exact integer arithmetic, plus the defect >= 2 ratio bound in
exact fractions.  It does not prove the source's sequential counting
argument, the orbit-counting transfer, or the Sidorenko counterexample.
"""

import copy
import hashlib
import importlib.util
import json
import stat
import sys
from pathlib import Path


HERE = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def read_json(name):
    return json.loads((HERE / name).read_text())


def load_engine():
    spec = importlib.util.spec_from_file_location(
        "sidorenko_audit", HERE / "code" / "sidorenko_audit.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


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
    bundled = (HERE / "data" / "baseline-faces-bits.json").read_bytes()
    require(hashlib.sha256(bundled).hexdigest()
            == pins["bundled_input"]["sha256"], "bundled input pin")


COMPARE_KEYS = [
    "allowed_edges", "allowed_degrees", "surface_pairs", "euler",
    "vertex_bound_sum", "sum_deg_sq", "base_remainder", "pair_excess_max",
    "closed_form_remainder", "all_support_masks",
    "supports_without_isolates", "relaxed_defect_one_cases",
    "refined_remainder", "maximizers", "higher_defect_ratio_max",
    "higher_defect_ratio_attained_at", "higher_defect_ratio_extension_max",
    "strata_table_sha256", "support_rows",
]


def mismatches(result, evidence):
    return [k for k in COMPARE_KEYS if result[k] != evidence[k]]


def negative_controls(engine, data, evidence, result):
    # A wrong expected maximum must be caught by the comparison.
    wrong = copy.deepcopy(evidence)
    wrong["refined_remainder"] = 190
    require(mismatches(result, wrong) != [],
            "control: wrong expected maximum 190 not detected")

    # Flipping one cut bit (with the redundant separations record updated
    # to match, so the input stays internally consistent) describes a
    # different complex and must change the allowed graph.
    flipped = copy.deepcopy(data)
    bits = list(flipped["bits"])
    bits[0] = ("1" if bits[0][0] == "0" else "0") + bits[0][1:]
    flipped["bits"] = bits
    pair_faces = {}
    for idx, face in enumerate(flipped["faces"]):
        for a, b in ((face[0], face[1]), (face[0], face[2]),
                     (face[1], face[2])):
            pair_faces.setdefault((a, b), []).append(idx)
    flipped["pair_separations"] = [
        [list(pair), engine.hamming(bits[i], bits[j])]
        for pair, (i, j) in sorted(pair_faces.items())]
    graph = engine.load_and_check_inputs(flipped)
    require(graph["allowed_edges"] != evidence["allowed_edges"],
            "control: flipped cut bit leaves the allowed graph unchanged")

    # Dropping a face breaks the closed-surface consistency checks.
    broken = copy.deepcopy(data)
    broken["faces"] = broken["faces"][:-1]
    broken["bits"] = broken["bits"][:-1]
    try:
        engine.load_and_check_inputs(broken)
    except ValueError:
        pass
    else:
        raise ArithmeticError("control: dropped face not detected")

    # The stratum machinery must be sensitive to the graph: path vs
    # triangle on three vertices give different case counts.
    path = engine.stratum_max_for_graph([(0, 1), (1, 2)], 3)
    triangle = engine.stratum_max_for_graph([(0, 1), (0, 2), (1, 2)], 3)
    require(path["relaxed_defect_one_cases"]
            != triangle["relaxed_defect_one_cases"],
            "control: stratum count insensitive to the graph")


def main():
    check_files()
    engine = load_engine()
    data = read_json("data/baseline-faces-bits.json")
    evidence = read_json("evidence/audit-results.json")
    result = engine.run_audit(data)
    bad = mismatches(result, evidence)
    require(not bad, "recomputation disagrees with evidence: %s" % bad)
    negative_controls(engine, data, evidence, result)

    deg = result["allowed_degrees"]
    print("PASS: input complex consistent (13 points, 22 faces, closed "
          "surface, Euler characteristic 2, separations agree)")
    print("PASS: allowed graph rebuilt: %d pairs, degrees %s, connected"
          % (len(result["allowed_edges"]), tuple(deg)))
    print("PASS: closed form %d - %d + floor(%d/2) = %d"
          % (result["sum_deg_sq"], 3 * len(result["allowed_edges"]),
             result["pair_excess_max"], result["closed_form_remainder"]))
    print("PASS: %d supports scanned, %d without isolates, %d relaxed "
          "defect-one strata exhausted"
          % (result["all_support_masks"],
             result["supports_without_isolates"],
             result["relaxed_defect_one_cases"]))
    print("PASS: finite maximum %d attained only on the full support "
          "(spans %s), matching the closed form"
          % (result["refined_remainder"],
             [r["span"] for r in result["maximizers"]]))
    print("PASS: allocation agreement (dynamic program = greedy = dual "
          "certificate on %d distinct problems; brute force on %d of them "
          "plus %d random small instances)"
          % (result["method_agreement"]["distinct_triple_checked"],
             result["method_agreement"]["bruteforce_checked"],
             result["random_allocation_bruteforce_checks"]))
    print("PASS: defect >= 2 ratio bound %s exactly (author's grid and "
          "extension to d <= 100000)"
          % result["higher_defect_ratio_max"])
    print("PASS: negative controls (wrong bound 190, flipped cut bit, "
          "dropped face, changed graph)")
    print("SCOPE: finite computation only; the sequential counting "
          "argument, the orbit-counting transfer and the counterexample "
          "theorem remain outside, and the evidence level remains Claimed")


if __name__ == "__main__":
    sys.exit(main())
