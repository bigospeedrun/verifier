"""Independently re-derive the Catalan certificate chain behind
mu(G) < 2401.741.

This verifies the full finite-certificate chain for the design
(36, 6, 2, 3, 2): design arithmetic and conditions (C1)-(C2), the
structural counting identity (6,174 cases) and the 23-prime valuation
table (two methods), (C3) nonvanishing (paper's pivot rule, exact
rational determinants, modular ranks; the paper's Table 1 as a
positive control), the exact loss integral 4825/2 and the F_low
enclosure, the (C4) rigorous real-place certificate for both witness
files, and the final assembly in interval arithmetic giving
mu(G) <= 2401.7409911295751174 < 2401.741.  It does not prove the
written theorems (general design theorem, minor bound, exponent
theorem), which are taken as given, and it supplies no Lean proof.
"""

import copy
import hashlib
import importlib.util
import json
import os
import stat
import sys
import tempfile
from fractions import Fraction as Fr
from pathlib import Path


HERE = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def read_json(*parts):
    return json.loads(HERE.joinpath(*parts).read_text())


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
    require(files == manifest["sha256"],
            "package file inventory or hash")
    pins = read_json("data", "SOURCES.json")
    for name, digest in pins["sha256"].items():
        bundled = (HERE / "data" / name).read_bytes()
        require(hashlib.sha256(bundled).hexdigest() == digest,
                "bundled input pin: " + name)


def load_module(name, *parts):
    spec = importlib.util.spec_from_file_location(
        name, HERE.joinpath(*parts))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def canon(R):
    return json.loads(json.dumps(R, default=str))


def headline(R):
    """The comparable headline values of an audit result dict (the
    fresh run's live dict or the packaged evidence JSON)."""
    L = R["links"]
    H = {"L1": L["L1"], "L2_cases": L["L2"]["counting_identity_cases"],
         "L2_fails": L["L2"]["counting_identity_failures"],
         "L2_rows": L["L2"]["valuation_rows"],
         "L2_agree": L["L2"]["valuation_matches_claimant_saved"],
         "L3": {k: L["L3"][k] for k in (
             "paper_control_table1_match", "zeta2_failures",
             "zeta2_entries", "max_denominator_prime",
             "pivots_all_nonzero_mod_P", "pivots_match_claimant_saved",
             "dets_nonzero", "ranks_extra_primes", "pivots")},
         "L4": {k: L["L4"][k] for k in (
             "integral_new", "integral_paper_control",
             "integral_96_control", "f_low_lo", "f_low_hi",
             "saved_agrees_at_printed_precision")},
         "L5": {}, "L6": L["L6"], "context": R["context"]}
    for fn, e in L["L5"]["witnesses"].items():
        d = {"validation_all_ok": e["validation_all_ok"],
             "margin_lo": e["margin_lo"], "margin_hi": e["margin_hi"],
             "margin_positive": e["margin_positive"], "kappas": {}}
        for kap, kk in e["kappas"].items():
            d["kappas"][kap] = {
                "degrees_match_saved": kk["degrees_match_saved"],
                "ncrit_match_saved": kk["ncrit_match_saved"],
                "U_lo": kk["U_lo"], "U_hi": kk["U_hi"],
                "Sigma_lo": kk["Sigma_lo"],
                "gates": kk["gates"]}
        H["L5"][fn] = d
    return H


def negative_controls(mods, fresh):
    run_audit, witness, cert, flow, bmatrix = mods
    edges_path = HERE / "data" / "cat_tail_edges_out.json"

    # A wrong expected bound must be caught by the comparison.
    wrong = copy.deepcopy(fresh)
    wrong["links"]["L6"]["mu_hi"] = "2401.75"
    require(headline(wrong) != headline(fresh),
            "control: wrong expected bound not detected")

    # Tampering lambda^(2) away from 0 breaks witness validation.
    doc = json.loads(edges_path.read_text())
    doc["kappa2"]["lambda"] = "1"
    with tempfile.TemporaryDirectory() as td:
        p = Path(td) / "tampered.json"
        p.write_text(json.dumps(doc))
        W = witness.parse_witness(str(p))
    require(not witness.validate_witness(W)["all_ok"],
            "control: tampered lambda^(2) not detected")

    # Tampering one witness coefficient changes the certified U_2.
    doc = json.loads(edges_path.read_text())
    c0 = doc["kappa2"]["cp"][0]
    doc["kappa2"]["cp"][0] = c0[:-1] + ("1" if c0[-1] != "1" else "2")
    with tempfile.TemporaryDirectory() as td:
        p = Path(td) / "tampered.json"
        p.write_text(json.dumps(doc))
        Wt = witness.parse_witness(str(p))
    rt = cert.certify_kappa(2, Wt["certificates"]["2"], Wt["D"],
                            grid_check=False, c2_check=False)
    import mpmath as mpm
    ev_u = fresh["links"]["L5"]["witnesses"][
        "cat_tail_edges_out.json"]["kappas"]["2"]["U_hi"]
    require(mpm.nstr(rt["U_hi"], 20) != ev_u,
            "control: tampered witness coefficient leaves U_2 unchanged")

    # The loss integrator is design-sensitive and its controls exact.
    alt, _ = flow.integrate_D((36, 6, 2, 3, 3))
    require(alt != Fr(4825, 2),
            "control: wrong-design integral equals 4825/2")
    require(flow.integrate_D((48, 7, 4, 4, 2))[0] == Fr(8609, 2),
            "control: paper integral control")
    require(flow.integrate_D((96, 15, 6, 8, 5))[0] == Fr(17114),
            "control: 96-design integral control")

    # Tampering one entry of B changes the (C3) evidence.
    B, _, _ = bmatrix.build_B((36, 6, 2, 3, 2))
    Bt = [row[:] for row in B]
    Bt[0][0] += 1
    from qx import det_bareiss, pivot_pattern_mod
    M = [[B[i][k] for k in range(36)] for i in range(36)]
    Mt = [[Bt[i][k] for k in range(36)] for i in range(36)]
    sw0, pv0 = pivot_pattern_mod(M, 53)
    swt, pvt = pivot_pattern_mod(Mt, 53)
    require(pv0 != pvt or det_bareiss(M) != det_bareiss(Mt),
            "control: tampered B entry not detected")


def main():
    check_files()
    tmp = tempfile.TemporaryDirectory()
    os.environ["CATALAN_AUDIT_EVIDENCE"] = tmp.name
    run_audit = load_module("run_audit", "code", "run_audit.py")
    witness = load_module("witness", "code", "witness.py")
    cert = load_module("cert", "code", "cert.py")
    flow = load_module("flow", "code", "flow.py")
    bmatrix = load_module("bmatrix", "code", "bmatrix.py")
    fresh = canon(run_audit.main())
    evidence = read_json("evidence", "per_link_results.json")
    require(headline(fresh) == headline(evidence),
            "recomputation disagrees with the packaged evidence")
    L6 = fresh["links"]["L6"]
    require(L6["claim_mu_lt_2401_741"] is True, "headline claim")
    require(L6["dominance_second_le_rho1"] is True, "dominance")
    negative_controls((run_audit, witness, cert, flow, bmatrix), fresh)

    L2 = fresh["links"]["L2"]
    L3 = fresh["links"]["L3"]
    L4 = fresh["links"]["L4"]
    print("PASS: package integrity (manifest, data pins) and no "
          "symlinks or executables")
    print("PASS: L1 design arithmetic: (C1), (C2), prime 53, "
          "Jha hypotheses")
    print("PASS: L2 structural: counting identity %d cases, %d "
          "failures; %d valuation primes, two methods, bound "
          "attained at %d primes"
          % (L2["counting_identity_cases"],
             L2["counting_identity_failures"],
             L2["valuation_primes"],
             L2["bound_attained_exactly_at_n_primes"]))
    print("PASS: L3 (C3): Table 1 control exact (144 pivots); "
          "zeta(2) 0/%d; denominator primes <= %d < 53; pivots, "
          "exact determinants and ranks all nonzero/full"
          % (L3["zeta2_entries"], L3["max_denominator_prime"]))
    print("PASS: L4: integral %s exactly (controls %s, %s); F_low "
          "enclosed" % (L4["integral_new"],
                         L4["integral_paper_control"],
                         L4["integral_96_control"]))
    for fn, e in fresh["links"]["L5"]["witnesses"].items():
        print("PASS: L5 (C4) %s: witnesses valid; margins rigorous, "
              "gamma >= %s > 0" % (fn, e["margin_lo"]))
    print("PASS: L6 assembly: rho1 <= %s; second case <= %s "
          "(dominance); mu(G) <= %s < 2401.741"
          % (L6["rho1_hi"], L6["second_hi"], L6["mu_hi"]))
    print("PASS: negative controls (wrong bound, tampered "
          "lambda^(2), tampered witness coefficient, wrong-design "
          "integral, tampered B entry)")
    print("SCOPE: finite/numerical chain only; the written "
          "theorems are taken as given, the ~2100 figure and the "
          "equilibrium ceiling are measured-only context, and the "
          "evidence level remains Claimed")


if __name__ == "__main__":
    sys.exit(main())
