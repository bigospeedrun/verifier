"""
run_audit.py -- driver for the full Catalan certificate-chain audit.

Runs every link with the audit's own implementations and writes
evidence/per_link_results.json (+ prints a log).  The claimant's
saved outputs are read ONLY as comparison data (cross-checks), never
as inputs to any computation.

Links:
  L1 design arithmetic: derived quantities, (C1), (C2), the
     certification prime, Jha Lemma 4.3 instantiation hypotheses.
  L2 structural: counting identity (Lemma 3.3) for N = 1..60 and all
     primes H/2 < p <= H; zeta(2) cancellation; row supports; the
     per-prime valuation check at N = 1, G = 1/3 (two methods).
  L3 (C3): B matrix; paper's Table 1 positive control; mod-53 pivot
     rule; exact rational determinants; ranks at further primes.
  L4 F_low: exact integral of D_L for three designs (two controls);
     rigorous interval enclosure of F_low.
  L5 (C4): witness validation; rigorous U_kappa enclosures for both
     witness files and both kappa; margins; two-sided Sigma bounds.
  L6 assembly: interval rho1, second-case coefficient, rho2, mu;
     dominance gates; the 2401.741 verdict; float reproduction of
     the source's own assembly as a consistency check.
  CTX equilibrium bracket + the ~2100 measurement: context items.
"""
import json
import math
import os
import sys
import time
from fractions import Fraction as Fr

import mpmath as mpm

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import assemble
import bmatrix
import cert
import flow
import structcheck
import witness
from qx import pivot_pattern_mod, rank_mod

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
# All inputs are the packaged data copies (see data/SOURCES.json for
# the upstream pins and hashes); the audit never reads the live clones.
CERTDIR = os.path.join(ROOT, "data")
EVID = os.environ.get("CATALAN_AUDIT_EVIDENCE",
                      os.path.join(ROOT, "evidence"))
DES = (36, 6, 2, 3, 2)

LOG = []


def log(s):
    line = s
    LOG.append(line)
    print(line, flush=True)


def S(x, n=20):
    return mpm.nstr(x, n)


def MPF(s):
    """Parse a decimal string / float at 90-digit precision (mpmath's
    default context would round to 53 bits and fake a 1e-16 diff)."""
    with mpm.workdps(90):
        return +mpm.mpf(s)


def main():
    t_start = time.time()
    R = {"design": DES, "links": {}}
    saved_result = json.load(open(os.path.join(CERTDIR, "RESULT.json")))
    saved_c4 = json.load(open(os.path.join(CERTDIR,
                                           "cat_cert4_new_out.json")))
    saved_struct = json.load(open(os.path.join(
        CERTDIR, "cat_newdesign_check_out.json")))
    saved_c7 = json.load(open(os.path.join(CERTDIR,
                                           "cat_cert7_new_out.json")))
    saved_eq = json.load(open(os.path.join(CERTDIR,
                                           "cat_equilibrium_out.json")))

    # ------------------------------------------------------------ L1 --
    log("== L1 design arithmetic ==")
    a0, L0, C0, H0, A0 = bmatrix.derived(DES)
    P = bmatrix.smallest_prime_above(H0)
    L1 = {
        "derived": {"a0": a0, "L0": L0, "C0": C0, "H0": H0, "A0": A0},
        "C1_2g0_lt_n0_minus_1": 2 * DES[3] < DES[0] - 1,
        "C2_2b0_lt_H0": 2 * DES[1] < H0,
        "certification_prime_smallest_above_H0": P,
        "saved_modulus_in_cert4_out": saved_c4["modulus"],
        "result_json_prime_field": saved_result["prime"],
        "result_json_H0_A0_match": (saved_result["H0"] == H0
                                    and saved_result["A0"] == A0),
        # Jha Lemma 4.3 instantiation (scaled design, N >= 2):
        # n = 36N >= 48; D* = n - 1 - 2g = 30N - 1 in (0, n].
        "jha_hypotheses": {
            "n_ge_48_for_N_ge_2": all(36 * N >= 48 for N in (2, 3, 10)),
            "Dstar_in_(0,n]_for_all_N_ge_1": all(
                0 < 30 * N - 1 <= 36 * N for N in range(1, 500)),
            "Dstar_formula": "30N - 1",
        },
    }
    R["links"]["L1"] = L1
    log(f"  derived a={a0} L={L0} C={C0} H={H0} A={A0}; C1, C2 hold; "
        f"P = {P} (saved modulus {saved_c4['modulus']}, "
        f"RESULT prime field {saved_result['prime']})")

    # ------------------------------------------------------------ L2 --
    log("== L2 structural ==")
    cases, cfails = structcheck.counting_identity_cases()
    V = structcheck.valuation_check()
    saved_V = {row["p"]: (row["vp"], row["bound"] or 0)
               for row in saved_struct["V"]}
    v_agree = all((row["vp"], row["bound"]) == saved_V[row["p"]]
                  for row in V["rows"])
    attained = sum(1 for row in V["rows"]
                   if row["bound"] is not None and row["vp"] == row["bound"]
                   and row["p"] <= H0)
    L2 = {"counting_identity_cases": cases,
          "counting_identity_failures": cfails,
          "valuation_primes": len(V["rows"]),
          "valuation_failures": V["fails"],
          "valuation_rows": V["rows"],
          "valuation_matches_claimant_saved": v_agree,
          "bound_attained_exactly_at_n_primes": attained,
          "det_delta1_nonzero": V["det"] != 0}
    R["links"]["L2"] = L2
    log(f"  counting identity: {cases} cases, {cfails} failures; "
        f"valuations: {len(V['rows'])} primes, {V['fails']} failures, "
        f"agree with claimant's saved rows: {v_agree}; "
        f"bound attained at {attained} primes")

    # ------------------------------------------------------------ L3 --
    log("== L3 (C3) nonvanishing ==")
    ctrl = bmatrix.analyse_B((48, 7, 4, 4, 2), 101)
    ctrl_ok = all(
        ctrl["pivots"][str(sg)]["pivots"] == bmatrix.TABLE1[sg]
        and [tuple(s) for s in ctrl["pivots"][str(sg)]["swaps"]]
        == bmatrix.TABLE1_SWAPS[sg] for sg in (0, 1, -1))
    new = bmatrix.analyse_B(DES, P)
    piv_agree = all(
        new["pivots"][str(sg)]["pivots"]
        == saved_c4["pivots"][str(sg)]["pivots"]
        and [list(s) for s in new["pivots"][str(sg)]["swaps"]]
        == [list(s) for s in saved_c4["pivots"][str(sg)]["swaps"]]
        for sg in (0, 1, -1))
    # ranks at further primes above H0 (third method family)
    B, _, _ = bmatrix.build_B(DES)
    n0 = DES[0]
    extra_ranks = {}
    for p2 in (59, 61, 67):
        rr = {}
        for sg in (0, 1, -1):
            M = [[B[i][k] + sg * B[i + 1][k] for k in range(n0)]
                 for i in range(n0)]
            rk, _ = rank_mod(M, p2)
            rr[str(sg)] = rk
        extra_ranks[str(p2)] = rr
    L3 = {"paper_control_table1_match": ctrl_ok,
          "paper_control_zeta2_failures": ctrl["zeta2_failures"],
          "paper_control_zeta2_entries": ctrl["zeta2_entries"],
          "paper_control_max_denominator_prime":
              ctrl["max_denominator_prime"],
          "paper_control_dets_nonzero":
              {k: (v != 0) for k, v in ctrl["dets"].items()},
          "zeta2_failures": new["zeta2_failures"],
          "zeta2_entries": new["zeta2_entries"],
          "supports_ok": new["supports_ok"],
          "max_denominator_prime": new["max_denominator_prime"],
          "saved_max_denominator_prime":
              saved_c4["largest_denominator_prime"],
          "pivots_all_nonzero_mod_P":
              {k: v["all_nonzero"] for k, v in new["pivots"].items()},
          "pivots_match_claimant_saved": piv_agree,
          "pivots": {k: v["pivots"] for k, v in new["pivots"].items()},
          "swaps": {k: v["swaps"] for k, v in new["pivots"].items()},
          "dets_nonzero": {k: (v != 0) for k, v in new["dets"].items()},
          "dets_log10_abs": {k: (math.log10(abs(float(v))) if v != 0
                                  else None)
                              for k, v in new["dets"].items()},
          "ranks_mod_P": new["ranks"],
          "ranks_extra_primes": extra_ranks}
    R["links"]["L3"] = L3
    log(f"  paper control Table 1 match: {ctrl_ok}; new design: "
        f"zeta2 {new['zeta2_failures']}/{new['zeta2_entries']}, "
        f"max denom prime {new['max_denominator_prime']} (saved "
        f"{saved_c4['largest_denominator_prime']}), pivots match saved: "
        f"{piv_agree}, dets nonzero: {L3['dets_nonzero']}")

    # ------------------------------------------------------------ L4 --
    log("== L4 F_low ==")
    I_new, delta, rat, coeff, stats = flow.f_low_parts(DES)
    I_pap, _, rat_pap, coeff_pap, _ = flow.f_low_parts((48, 7, 4, 4, 2))
    I_96, _, rat_96, coeff_96, _ = flow.f_low_parts((96, 15, 6, 8, 5))
    cert.iv.dps = cert.IVDPS
    log2_iv = cert.iv.log(cert.iv.mpf(2))
    flow_iv = cert.ivq(rat) - cert.ivq(coeff) * log2_iv
    f_lo, f_hi = cert._lo(flow_iv), cert._hi(flow_iv)
    saved_flow_lo = MPF(saved_c7["f_low_lower"])
    L4 = {"integral_new": str(I_new), "integral_paper_control": str(I_pap),
          "integral_96_control": str(I_96),
          "delta": str(delta), "rational_part": str(rat),
          "log2_coefficient": str(coeff),
          "paper_F_low_rational_part": str(rat_pap),
          "paper96_F_low_parts": [str(rat_96), str(coeff_96)],
          "f_low_lo": S(f_lo), "f_low_hi": S(f_hi),
          "saved_f_low_lower": saved_c7["f_low_lower"],
          # the claimant's printed endpoint is an nstr rounding at
          # 20 significant digits; agreement is at that scale
          "saved_agrees_at_printed_precision":
              bool(abs(saved_flow_lo - f_lo) <= mpm.mpf("1e-19")),
          "saved_minus_audit_lo": S(saved_flow_lo - f_lo, 3),
          "integration_stats": stats}
    R["links"]["L4"] = L4
    log(f"  integrals: new {I_new}, controls {I_pap} (paper 48), "
        f"{I_96} (paper 96); F_low in [{S(f_lo, 16)}, {S(f_hi, 16)}]; "
        f"saved printed endpoint agrees at print precision: "
        f"{L4['saved_agrees_at_printed_precision']} "
        f"(diff {L4['saved_minus_audit_lo']})")

    # ------------------------------------------------------------ L5 --
    log("== L5 (C4) rigorous certificate ==")
    L5 = {"witnesses": {}}
    cert_results = {}
    for fn in ("cat_tail_edges_out.json", "cat_tail_opt_out.json"):
        W = witness.parse_witness(os.path.join(CERTDIR, fn))
        val = witness.validate_witness(W)
        saved_cert = [c for c in saved_c7["certificates"]
                      if c["input"] == fn][0]
        entry = {"validation_all_ok": val["all_ok"],
                 "validation_checks": val["n_checks"],
                 "D": W["D"], "n_real_bases": len(W["real_bases"]),
                 "n_pair_bases": len(W["pair_bases"]), "kappas": {}}
        U = {}
        Sigma = {}
        for kap in (2, 1):
            r = cert.certify_kappa(kap, W["certificates"][str(kap)],
                                   W["D"])
            cert_results.setdefault(fn, {})[kap] = r
            U[kap] = (r["U_lo"], r["U_hi"])
            Sigma[kap] = (r["Sigma_lo"], r["Sigma_hi"])
            sk = saved_cert[f"kappa{kap}"]
            entry["kappas"][str(kap)] = {
                "degrees": {k: list(v) for k, v in r["degrees"].items()},
                "degrees_match_saved":
                    {k: list(v) == sk["degrees"][k]
                     for k, v in r["degrees"].items()},
                "ncrit": {"X": r["ncrit_X"], "Y": r["ncrit_Y"]},
                "ncrit_match_saved":
                    r["ncrit_X"] == sk["critical_points"]["X"]
                    and r["ncrit_Y"] == sk["critical_points"]["Y"],
                "supX_lo": S(r["supX_lo"]), "supX_hi": S(r["supX_hi"]),
                "supY_lo": S(r["supY_lo"]), "supY_hi": S(r["supY_hi"]),
                "NP2_lo": S(r["NP2_lo"]), "NP2_hi": S(r["NP2_hi"]),
                "U_lo": S(r["U_lo"]), "U_hi": S(r["U_hi"]),
                "U_hi_saved": sk["U_upper"],
                "U_hi_abs_diff_vs_saved":
                    S(abs(r["U_hi"] - MPF(sk["U_upper"])), 3),
                "Sigma_lo": S(r["Sigma_lo"]), "Sigma_hi": S(r["Sigma_hi"]),
                "max_allowance": S(max(r["max_allow_X"],
                                       r["max_allow_Y"]), 3),
                "max_allowance_saved": sk["max_allowance"],
                "C2_worst_numdiff": S(r["C2_worst_numdiff"], 3),
                "C2_worst_closed": S(r["C2_worst_closed"], 3),
                "grid": r["grid"],
                "gates": r["gates"],
                "seconds": round(r["seconds"], 1)}
            log(f"  {fn} kappa={kap}: U <= {S(r['U_hi'], 16)} "
                f"(saved {sk['U_upper']}), crits X {r['ncrit_X']} "
                f"Y {r['ncrit_Y']}, gates {r['gates']}")
        margin_lo = f_lo - max(U[2][1], U[1][1])
        margin_hi = f_hi - max(U[2][0], U[1][0])
        entry["margin_lo"] = S(margin_lo)
        entry["margin_hi"] = S(margin_hi)
        entry["margin_saved"] = saved_cert["margin_lower"]
        entry["margin_abs_diff_vs_saved"] = S(
            abs(margin_lo - MPF(saved_cert["margin_lower"])), 3)
        entry["margin_positive"] = bool(margin_lo > 0)
        entry["U"] = {str(k): [S(v[0]), S(v[1])] for k, v in U.items()}
        entry["Sigma"] = {str(k): [S(v[0]), S(v[1])]
                          for k, v in Sigma.items()}
        L5["witnesses"][fn] = entry
        log(f"  {fn}: margin in [{S(margin_lo, 16)}, "
            f"{S(margin_hi, 16)}] (saved lower "
            f"{saved_cert['margin_lower']}), positive: "
            f"{entry['margin_positive']}")
    R["links"]["L5"] = L5

    # ------------------------------------------------------------ L6 --
    log("== L6 assembly ==")
    edges = cert_results["cat_tail_edges_out.json"]
    opt = cert_results["cat_tail_opt_out.json"]
    lam1 = witness.parse_witness(os.path.join(
        CERTDIR, "cat_tail_edges_out.json"))["certificates"]["1"]["lambda"]
    asm_edges = assemble.assemble(
        f_lo, f_hi,
        {2: (edges[2]["U_lo"], edges[2]["U_hi"]),
         1: (edges[1]["U_lo"], edges[1]["U_hi"])},
        {2: (edges[2]["Sigma_lo"], edges[2]["Sigma_hi"]),
         1: (edges[1]["Sigma_lo"], edges[1]["Sigma_hi"])},
        lam1)
    asm_opt = assemble.assemble(
        f_lo, f_hi,
        {2: (opt[2]["U_lo"], opt[2]["U_hi"]),
         1: (opt[1]["U_lo"], opt[1]["U_hi"])},
        {2: (opt[2]["Sigma_lo"], opt[2]["Sigma_hi"]),
         1: (opt[1]["Sigma_lo"], opt[1]["Sigma_hi"])},
        lam1)
    # source-style float assembly (consistency check of the reading of
    # package.py / mu_cert.py; NOT the audit's bound)
    e2 = [c for c in saved_c7["certificates"]
          if c["input"] == "cat_tail_edges_out.json"][0]
    gam_f = float(e2["margin_lower"])
    Sig2_f = float(e2["kappa2"]["supX_upper"]) \
        + float(e2["kappa2"]["supY_upper"]) - 1e-12
    Sig1_f = float(e2["kappa1"]["supX_upper"]) \
        + float(e2["kappa1"]["supY_upper"]) - 1e-12
    lam_f = float(lam1)
    lg = math.log(2)
    rho1_f = (2 - 2 / 9 - 1 / 12) * lg - Sig2_f + 2 * lg
    second_f = (2 - 2 / 9 - 1 / 12) * lg - Sig1_f \
        - lam_f * (1 - 2 / 12) + 1.5 * lg
    rho2_f = rho1_f + (1 / 18 + 1 / 18) * lg \
        + (11 / 12) * math.log(1 + math.sqrt(2))
    mu_f = rho2_f * ((11 / 12) / gam_f + 36)
    L6 = {"gamma_lo": S(asm_edges["gamma_lo"]),
          "gamma_hi": S(asm_edges["gamma_hi"]),
          "rho1_lo": S(asm_edges["rho1_lo"]),
          "rho1_hi": S(asm_edges["rho1_hi"]),
          "second_lo": S(asm_edges["second_lo"]),
          "second_hi": S(asm_edges["second_hi"]),
          "dominance_second_le_rho1": asm_edges["dominance_ok"],
          "U1_minus_U2_hi": S(asm_edges["U1_minus_U2_hi"]),
          "rho2_lo": S(asm_edges["rho2_lo"]),
          "rho2_hi": S(asm_edges["rho2_hi"]),
          "mu_lo": S(asm_edges["mu_lo"]), "mu_hi": S(asm_edges["mu_hi"]),
          "claim_mu_lt_2401_741": asm_edges["claim_2401_741"],
          "mu_hi_with_opt_certificate": S(asm_opt["mu_hi"]),
          "float_reproduction_of_source_assembly": {
              "rho1": rho1_f, "second": second_f, "rho2": rho2_f,
              "mu": mu_f,
              "saved_rho1": saved_result["rho1_upper"],
              "saved_second": saved_result["second_case_coefficient"],
              "saved_rho2": saved_result["rho2_upper"],
              "saved_mu": saved_result["mu_upper"],
              "mu_abs_diff": abs(mu_f - saved_result["mu_upper"])},
          "sigma_convention_check": {
              "source_Sigma2_lower": saved_result["Sigma2_lower"],
              "audit_Sigma2_lo": S(edges[2]["Sigma_lo"]),
              "source_value_is_valid_lower_bound":
                  bool(MPF(saved_result["Sigma2_lower"])
                       <= edges[2]["Sigma_lo"]),
              "source_Sigma1_lower": saved_result["Sigma1_lower"],
              "audit_Sigma1_lo": S(edges[1]["Sigma_lo"]),
              "source_value_is_valid_lower_bound_1":
                  bool(MPF(saved_result["Sigma1_lower"])
                       <= edges[1]["Sigma_lo"])}}
    R["links"]["L6"] = L6
    log(f"  gamma = {S(asm_edges['gamma_lo'], 12)}; "
        f"rho1 <= {S(asm_edges['rho1_hi'], 16)}; second coefficient "
        f"<= {S(asm_edges['second_hi'], 16)} (dominance "
        f"{asm_edges['dominance_ok']}); rho2 <= "
        f"{S(asm_edges['rho2_hi'], 16)}")
    log(f"  mu(G) <= {S(asm_edges['mu_hi'], 16)} < 2401.741: "
        f"{asm_edges['claim_2401_741']}; float reproduction of the "
        f"source's mu_upper: {mu_f} vs saved "
        f"{saved_result['mu_upper']} (diff "
        f"{abs(mu_f - saved_result['mu_upper']):.2e})")

    # ------------------------------------------------------------ CTX --
    R["context"] = {
        "equilibrium_new_bracket_score": saved_eq["new"]["bracket_score"],
        "equilibrium_new_bracket_U": saved_eq["new"]["bracket_U"],
        "equilibrium_gates": saved_eq["gates"],
        "certified_gamma_within_bracket": bool(
            saved_eq["new"]["bracket_score"][0]
            <= float(asm_edges["gamma_lo"]) + 1e-12
            and float(asm_edges["gamma_hi"])
            <= saved_eq["new"]["bracket_score"][1] + 1e-9),
    }
    R["wall_seconds"] = round(time.time() - t_start, 1)
    os.makedirs(EVID, exist_ok=True)
    with open(os.path.join(EVID, "per_link_results.json"), "w") as fh:
        json.dump(R, fh, indent=1, default=str)
    with open(os.path.join(EVID, "run_log.txt"), "w") as fh:
        fh.write("\n".join(LOG) + "\n")
    log(f"== done in {R['wall_seconds']}s; results written to "
        f"evidence/per_link_results.json ==")
    return R


if __name__ == "__main__":
    main()
