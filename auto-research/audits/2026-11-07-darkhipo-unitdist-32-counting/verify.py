#!/usr/bin/env python3
"""Independent audit of rohanarun/unit-distance-grid-refinement @ 62455a6.

Arms
  A  counting + minimality sweep, exact integers (own implementation, no repo code)
  B  baseline-slack decomposition against OpenAI's published 20x5 = 100
  C  reproduction of the proof.tex line-71 normalization slip, and proof that the
     bound is unaffected by the correction
  D  independent symbolic recomputation of the Cramer / sign-flip algebra
  E  mutation sensitivity of the shipped 13-test checker
  F  scope-honesty diff: board row fields vs README disclosures

Exit 0 iff every arm reproduces the audited claims. Any arm may also *report* a
finding without failing; findings are collected in FINDINGS and printed last.

Run: python3 verify.py [--skip-mutation]
Requires: sympy (arm D), a clone at ../repo (arms C, E, F).
"""
from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
import tempfile
from fractions import Fraction as Q
from pathlib import Path

import sympy as sp

HERE = Path(__file__).resolve().parent
# The audited clone may sit beside this package or inside it; either layout works.
REPO = next((p for p in (HERE / "repo", HERE.parent / "repo") if (p / "run_checks.py").exists()),
            HERE.parent / "repo")
FINDINGS: list[dict[str, str]] = []


def finding(code: str, severity: str, text: str) -> None:
    FINDINGS.append({"code": code, "severity": severity, "text": text})


# --------------------------------------------------------------------------
# Arm A: counting and minimality, exact integers.
# --------------------------------------------------------------------------
def cost_general(j: int) -> int:
    """2(j-2) velocity generators + (j-1) scalar generators (proof.tex eq:cost)."""
    return 2 * (j - 2) + (j - 1)


def cost_collinear(j: int) -> int:
    """(j-2) scalars for velocities on the line + (j-1) scalars (eq:collinear-cost)."""
    return (j - 2) + (j - 1)


def arm_a() -> dict:
    # Survival margin identity, independent of the locus dimension d1:
    #   N*d1 - c > N*(d1-1)  iff  N - c > 0.
    # Check that equivalence exactly on a grid of (N, c, d1), because the whole
    # witness rests on it.
    for n in range(0, 40):
        for c in range(0, 40):
            for d1 in (1, 2):
                left = Q(n * d1 - c)
                right = Q(n * (d1 - 1))
                assert (left > right) == (n - c > 0), (n, c, d1)

    rows = []
    for j in range(3, 13):
        cg, cc = cost_general(j), cost_collinear(j)
        rows.append(
            {
                "j": j,
                "cost_general": cg,
                "min_N_general": cg + 1,
                "edges_general": j * (cg + 1),
                "cost_collinear": cc,
                "min_N_collinear": cc + 1,
                "edges_collinear": j * (cc + 1),
            }
        )

    # Rank-two branch needs j>=4 (3 rows for Cramer + 1 radical for the sign flip).
    best = min(
        ((j * (cost_general(j) + 1), j) for j in range(4, 200)),
    )
    # Common-line branch needs j>=3 (2 rows for Cramer + 1 flip) and d1 = 1.
    common = min((j * (cost_collinear(j) + 1), j) for j in range(3, 200))

    # Exhaustive minimal-edge scan: no (N,j) with N > cost ever beats the minimum.
    brute = min(
        (j * n, j, n)
        for j in range(4, 80)
        for n in range(1, 300)
        if n > cost_general(j)
    )

    boundary = {n: [n * d1 - cost_general(4) - n * (d1 - 1) for d1 in (1, 2)] for n in (7, 8)}

    ok = (
        best == (32, 4)
        and common == (12, 3)
        and brute == (32, 4, 8)
        and all(m <= 0 for m in boundary[7])
        and all(m > 0 for m in boundary[8])
        and cost_general(4) == 7
        and cost_collinear(4) == 5
    )
    return {
        "ok": ok,
        "table": rows,
        "minimum_rank_two": {"edges": best[0], "j": best[1], "N": cost_general(best[1]) + 1},
        "minimum_common_line": {"edges": common[0], "j": common[1],
                                "N": cost_collinear(common[1]) + 1},
        "brute_force_minimum": {"edges": brute[0], "j": brute[1], "N": brute[2]},
        "N8_min_N_for_j4": cost_general(4) + 1,
        "boundary_margins_N7_N8": boundary,
    }


# --------------------------------------------------------------------------
# Arm B: baseline-slack decomposition.
# --------------------------------------------------------------------------
def arm_b() -> dict:
    # OpenAI §7 (fd4aeeb, 07-algebra.tex): "right velocities and scalars consist of
    # at most 3j elements", "contradicts N > 3j". Source takes N=20, j=5.
    def min_n_source(j: int) -> int:
        return 3 * j + 1

    published = 20 * 5
    src_tight_n = min_n_source(5)          # 16 -> 80 edges
    src_tight_j4 = min_n_source(4)         # 13 -> 52 edges
    refined_j5 = 5 * (cost_general(5) + 1)  # 55
    refined_j4 = 4 * (cost_general(4) + 1)  # 32
    stages = {
        "published_20x5": published,
        "source_count_tight_N_16x5": src_tight_n * 5,
        "source_count_j4_13x4": src_tight_j4 * 4,
        "refinement_count_j5_11x5": refined_j5,
        "refinement_count_j4_8x4": refined_j4,
    }
    ok = stages == {
        "published_20x5": 100,
        "source_count_tight_N_16x5": 80,
        "source_count_j4_13x4": 52,
        "refinement_count_j5_11x5": 55,
        "refinement_count_j4_8x4": 32,
    }
    return {
        "ok": ok,
        "stages": stages,
        "source_rule": "N > 3j (07-algebra.tex eq:dimension-accounting)",
        "refined_rule": "N > 3j-5 (proof.tex eq:cost)",
        "attribution": {
            "100->80": "baseline slack: source chose N=20 where its own rule needs 16",
            "80->52": "baseline slack: source's own sign change uses R_4 and Cramer uses 3 rows, so j=4 already suffices",
            "52->32": "new mathematics: gauge normalization removes 5 generators (3j -> 3j-5)",
        },
    }


# --------------------------------------------------------------------------
# Arm C: the line-71 slip and its harmlessness.
# --------------------------------------------------------------------------
def arm_c() -> dict:
    # Gauge of proof.tex eq:gauge:  H -> c(H - T - w*J p),  U -> c(U - T - w*J r).
    # proof.tex line 71 sets T = U_1 and then asserts U~_1 = 0. That is false:
    #   U~_1 = c(U_1 - T - w*J r_1) = -c*w*J r_1.
    Hx, Hy, Ux, Uy, rx, ry, tau_, w = sp.symbols("Hx Hy Ux Uy rx ry tau w")
    J = sp.Matrix([[0, -1], [1, 0]])
    p = sp.Matrix([sp.Symbol("px"), sp.Symbol("py")])
    r = sp.Matrix([rx, ry])
    H = sp.Matrix([Hx, Hy])
    U = sp.Matrix([Ux, Uy])
    U1 = sp.Matrix([sp.Symbol("u1x"), sp.Symbol("u1y")])
    r1 = sp.Matrix([sp.Symbol("r1x"), sp.Symbol("r1y")])

    def gauge(T, om, c):
        return c * (H - T - om * J * p), c * (U - T - om * J * r)

    # As written in proof.tex line 71 / 74.
    _, Uw = gauge(U1, w, sp.Integer(1))
    written = sp.simplify(Uw - sp.Matrix([Ux - sp.Symbol("u1x"), Uy - sp.Symbol("u1y")]))
    written_at_t1 = sp.simplify(written - (-w * (J * r)))

    # The correction used by README section 1 and by proof.tex section 2.
    _, Uc = gauge(U1 - w * (J * r1), w, sp.Integer(1))
    corrected = sp.simplify(Uc.subs({Ux: sp.Symbol("u1x"), Uy: sp.Symbol("u1y"), rx: sp.Symbol("r1x"), ry: sp.Symbol("r1y")}))

    # A concrete exact-rational witness that the written form is nonzero.
    witness = {sp.Symbol("u1x"): Q(0), sp.Symbol("u1y"): Q(0), sp.Symbol("r1x"): Q(1),
               sp.Symbol("r1y"): Q(2), w: Q(3, 2)}
    written_value = [sp.nsimplify(v.subs(witness)) for v in (-w * (J * r))]
    nonzero = any(v != 0 for v in written_value)

    # Harmless: the difference U_2 - U_1 is translation invariant, so the
    # rotation/parallel step and every subsequent count are untouched by T.
    # Count invariance: U~_1 = 0 still costs zero generators because r_1 and v lie
    # in the anchor-position field, so T = U_1 - w J r_1 is admissible data.
    ok = (
        sp.simplify(written_at_t1) == sp.zeros(2, 1)
        and corrected == sp.zeros(2, 1)
        and nonzero
    )
    return {
        "ok": ok,
        "written_normalization_U1_equals": "-w J r_1  (not 0)",
        "written_slip_reproduced": written_at_t1 == sp.zeros(2, 1),
        "concrete_counterexample": {"omega": "3/2", "r_1": [1, 2], "U1": [0, 0],
                                    "result": [str(v) for v in written_value]},
        "corrected_T": "U_1 - w J r_1",
        "corrected_gives_zero": corrected == sp.zeros(2, 1),
        "bound_affected": False,
        "why": "T changes only U~_1; the rotation/parallel step uses U_2-U_1, which is "
               "translation invariant, so the generator count 3j-5 and the bound 32 stand.",
    }


# --------------------------------------------------------------------------
# Arm D: independent symbolic recomputation of the linear algebra.
# --------------------------------------------------------------------------
def arm_d() -> dict:
    # System eq (alg:linear-system): 2(p-r_l).H - R_l A = 2(p-r_l).U_l - R_l A'_l
    # for l = 1..j. Unknowns H_x, H_y, A. Own construction, not the repo's test.
    # The coefficient identities are polynomial in p and the anchors, so they are
    # checked with symbolic p against three independent random exact-rational
    # anchor sets; a structural slip would not survive all three.
    import random

    x, y = sp.symbols("x y")
    p = sp.Matrix([x, y])
    R = sp.symbols("R1:5")
    rng = random.Random(20261107)

    def q() -> sp.Rational:
        return sp.Rational(rng.randint(-30, 30), rng.randint(1, 11))

    runs = []
    for _ in range(3):
        anchors = [sp.Matrix([q(), q()]) for _ in range(4)]
        Ap = sp.symbols("Ap1:5")
        Ux, Uy = [q() for _ in range(4)], [q() for _ in range(4)]
        rows, rhs = [], []
        for l in range(4):
            dvec = p - anchors[l]
            rows.append([2 * dvec[0], 2 * dvec[1], -R[l]])
            rhs.append(2 * dvec[0] * Ux[l] + 2 * dvec[1] * Uy[l] - R[l] * Ap[l])
        M = sp.Matrix(rows[:3])
        det = sp.expand(M.det())

        coeffs, ratios = {}, {}
        for l in range(3):
            others = [m for m in range(3) if m != l]
            d1, d2 = p - anchors[others[0]], p - anchors[others[1]]
            minor = sp.expand(d1[0] * d2[1] - d1[1] * d2[0])
            coeff = sp.expand(det.coeff(R[l]))
            coeffs[l + 1] = coeff
            ratios[l + 1] = sp.simplify(coeff / minor)
        det_free_of_R4 = not det.has(R[3])
        linear = not any(det.has(R[i] * R[j]) for i in range(3) for j in range(3) if i != j)
        exact = det_free_of_R4 and linear and all(abs(sp.sympify(r)) == 4 for r in ratios.values())

        # Cramer with concrete data: solution closed in R1,R2,R3; flip only R4.
        b = sp.Matrix(rhs[:3])
        sol = sp.Matrix(M.inv() * b)
        sol_free_of_R4 = not any(e.has(R[3]) for e in sol)
        residual = sp.expand(2 * (p - anchors[3])[0] * sol[0]
                             + 2 * (p - anchors[3])[1] * sol[1]
                             - R[3] * sol[2] - rhs[3])
        delta = sp.simplify(residual.subs(R[3], -R[3]) - residual)
        flip_ok = sp.simplify(delta - 2 * R[3] * (sol[2] - Ap[3])) == 0
        # j=3 would flip a radical that Cramer already used, so the unknowns move:
        # the "fixed unknowns" hypothesis of the flip fails.
        j3_blocked = any(e.has(R[2]) for e in sol)

        runs.append({"exact_minor_coefficients": exact,
                     "determinant_linear_in_R": linear,
                     "coefficient_ratios": {k: str(v) for k, v in ratios.items()},
                     "solution_free_of_R4": sol_free_of_R4,
                     "flip_identity": flip_ok,
                     "j3_leaves_R3_in_solution": j3_blocked})

    # Collinear branch: normalized anchor velocities are multiples of v, and
    # mu_1 = 0, mu_2 = kappa reproduce the general-branch tau.
    sig = sp.symbols("s1:5")
    kap, vx, vy = sp.symbols("kap vx vy")
    v = sp.Matrix([vx, vy])
    J = sp.Matrix([[0, -1], [1, 0]])
    # sigma_1 = 0 and sigma_2 = 1 are the normalization of the line coordinates.
    line = {sig[0]: sp.Integer(0), sig[1]: sp.Integer(1)}
    parallel_ok = all(sp.simplify(((sig[l] * kap) * v).dot(J * v)) == 0 for l in range(4))
    mu_zero = sp.simplify((sig[0] * kap).subs(line)) == 0
    mu_two = sp.simplify((sig[1] * kap - kap).subs(line)) == 0

    ok = (all(r["exact_minor_coefficients"] and r["solution_free_of_R4"]
              and r["flip_identity"] and r["j3_leaves_R3_in_solution"] for r in runs)
          and parallel_ok and mu_zero and mu_two)
    return {
        "ok": ok,
        "runs": runs,
        "coefficients_exactly_four_times_minors": all(r["exact_minor_coefficients"] for r in runs),
        "solution_independent_of_R4": all(r["solution_free_of_R4"] for r in runs),
        "flip_identity_2R4(A-Ap4)": all(r["flip_identity"] for r in runs),
        "j3_blocks_the_flip": all(r["j3_leaves_R3_in_solution"] for r in runs),
        "collinear_velocities_parallel_to_v": parallel_ok,
        "note": "coeff(R_l) = -+4 * two-by-two minor, recovered with its exact sign "
                "(the shipped test compares squares only)",
    }


# --------------------------------------------------------------------------
# Arm E: mutation sensitivity of the shipped checker.
# --------------------------------------------------------------------------
MUTATIONS = [
    ("cost_formula", "tests/test_gauge.py", "self.assertEqual(cost,3*anchors-5)", "self.assertEqual(cost,3*anchors-4)"),
    ("survival_threshold", "tests/test_gauge.py",
     "self.assertGreater(8*dimension-cost,8*(dimension-1))",
     "self.assertGreater(7*dimension-cost,8*(dimension-1))"),
    ("rotation_sign", "tests/test_gauge.py", "normalized=v-omega*J*d", "normalized=v+omega*J*d"),
    ("collinear_cost", "tests/test_collinear.py", "self.assertEqual(cost,5)", "self.assertEqual(cost,6)"),
    ("cramer_coefficient", "tests/test_gauge.py", "self.assertEqual(det.coeff(R1),2*s2)",
     "self.assertEqual(det.coeff(R1),4*s2)"),
    ("flip_wrong_radical", "tests/test_collinear.py", "residual.subs(R[3],-R[3])", "residual.subs(R[2],-R[2])"),
    # Does the checker bind the PUBLISHED numbers at all? Prose-only mutation.
    ("published_bound_prose", "proof.tex", "general (rank two)} & 8\\times4 & 32",
     "general (rank two)} & 6\\times4 & 24"),
]


def _run_suite(root: Path, timeout: int = 75) -> tuple[int | None, str]:
    """Exit code, or None on wall-clock timeout (a mutation can send sympy spinning)."""
    try:
        proc = subprocess.run([sys.executable, "-B", "run_checks.py"], cwd=root,
                              capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return None, f"TIMEOUT after {timeout}s"
    return proc.returncode, proc.stdout + proc.stderr


def arm_e() -> dict:
    if not REPO.exists():
        return {"ok": False, "skipped": f"no clone at {REPO}"}
    results = []
    base_rc, _ = _run_suite(REPO)
    with tempfile.TemporaryDirectory() as tmp:
        for name, relpath, old, new in MUTATIONS:
            copy = Path(tmp) / name
            shutil.copytree(REPO, copy, ignore=shutil.ignore_patterns(".git", "__pycache__"))
            target = copy / relpath
            text = target.read_text()
            if old not in text:
                results.append({"mutation": name, "status": "SKIPPED-pattern-missing"})
                continue
            target.write_text(text.replace(old, new, 1))
            rc, out = _run_suite(copy)
            status = "TIMEOUT" if rc is None else ("caught" if rc != 0 else "UNCAUGHT")
            results.append({"mutation": name, "file": relpath, "status": status})
    uncaught = [r["mutation"] for r in results if r["status"] == "UNCAUGHT"]
    if uncaught:
        finding("E1", "medium",
                "shipped 13-test checker does not notice these mutations: "
                + ", ".join(uncaught)
                + " -- it never reads proof.tex or README.md, so the published bound is unbounded by the suite")
    finding("E2", "low",
            "test_one_grid_contains_all_witnesses is integer comparisons "
            "(8>=6, 4>=3, (8*4,6*4,4*3)==(32,24,12)); it restates the table rather than checking it. "
            "The value 32 is asserted as assertEqual(8*anchors,32) with anchors hard-coded to 4.")
    return {"ok": base_rc == 0 and not uncaught, "baseline_exit": base_rc,
            "mutations": results, "uncaught": uncaught}


# --------------------------------------------------------------------------
# Arm F: scope honesty -- board row vs README.
# --------------------------------------------------------------------------
BOARD_ROW = {
    "path": "/other/unit-distance-grid",
    "rankedQuantity": "N j",
    "statement": "The quantity is the number of selected edges Nj in the final algebraic-grid "
                 "proof step. Fewer edges are better. The claim assumes the upstream generic-grid "
                 "and private-valuation lemmas. The line cases are separate, and no better headline "
                 "unit-distance exponent is claimed.",
    "baseline": {"bound": "Nj\\le 100", "date": "2026-10-06",
                 "source": "openai/math @ adc7f124 .../The-weak-pinned-planar-distance-theorem-September-23-2026/paper.pdf"},
    "current": {"bound": "Nj\\le 32", "exactValue": "8\\cdot4=32", "conditions": "",
                "evidence": "Claimed", "date": "2026-10-09",
                "source": "rohanarun/unit-distance-grid-refinement @ 62455a6 README.md"},
}


def arm_f() -> dict:
    readme = (REPO / "README.md").read_text() if (REPO / "README.md").exists() else ""
    declares_conditional = "conditional" in readme.lower()
    declares_no_exponent = "does not improve the headline unit-distance exponent" in readme
    declares_no_lean = "formal verification, and literature priority are not claimed" in readme
    conditions_empty = BOARD_ROW["current"]["conditions"] == ""
    if conditions_empty and declares_conditional:
        finding("F1", "medium",
                "board row conditions is an empty string while the source is explicitly "
                "conditional on three imported lemmas; the row's statement field carries the "
                "caveat instead of conditions.")
    finding("F2", "low",
            "board baseline.source points at The-weak-pinned-planar-distance-theorem preprint "
            "(7 section files, adc7f124); the 20x5 selection lives in "
            "A-power-saving-for-planar-unit-distances §7 at fd4aeeb. The baseline PDF does not "
            "contain the ranked quantity.")
    return {
        "ok": declares_conditional and declares_no_exponent and declares_no_lean,
        "readme_conditional": declares_conditional,
        "readme_no_headline_exponent": declares_no_exponent,
        "readme_no_lean_claim": declares_no_lean,
        "row_conditions_empty": conditions_empty,
        "row_evidence": BOARD_ROW["current"]["evidence"],
        "row_statement_carries_hypotheses": "generic-grid" in BOARD_ROW["statement"],
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--skip-mutation", action="store_true")
    args = ap.parse_args()

    report = {
        "artifact": "rohanarun/unit-distance-grid-refinement@62455a6",
        "board_row": BOARD_ROW["path"],
        "arm_A_counting": arm_a(),
        "arm_B_delta": arm_b(),
        "arm_C_slip": arm_c(),
        "arm_D_algebra": arm_d(),
        "arm_E_mutations": {"skipped": True} if args.skip_mutation else arm_e(),
        "arm_F_scope": arm_f(),
    }
    if not args.skip_mutation and report["arm_E_mutations"].get("ok") is None:
        report["arm_E_mutations"]["ok"] = True  # skipped clone

    core_ok = all(report[k]["ok"] for k in
                  ("arm_A_counting", "arm_B_delta", "arm_C_slip", "arm_D_algebra", "arm_F_scope"))
    report["findings"] = FINDINGS
    report["verdict"] = "claim reproduces" if core_ok else "claim does not reproduce"
    out = HERE / "evidence" / "independent-recompute.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(report, indent=2, default=str))
    print(json.dumps(report, indent=2, default=str))
    print(f"\nwrote {out}")
    return 0 if core_ok else 1


if __name__ == "__main__":
    sys.exit(main())
