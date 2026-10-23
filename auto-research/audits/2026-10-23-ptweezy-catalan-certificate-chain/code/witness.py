"""
witness.py -- parse and validate the two tail-witness files
(cat_tail_edges_out.json, cat_tail_opt_out.json) of the pinned
fringewidth package.

File format (as consumed by the claimant's certifier): each file holds
  design, D, denominator, real_bases (rationals), pair_bases
  ([re, im] rational pairs), and for kappa in {2, 1} a flat list of
  exact-rational strings cp / cv plus lambda.  The list layout is:
      [ l_1 .. l_D | r_z for each real base | (a, b) for each pair ],
  where a pair with coefficients (a, b) at base z contributes the two
  conjugate terms r_z = (a - ib)/2 at z and conj(r_z) at conj(z).
  The expanded (z, r_z) term list therefore has
  len(real_bases) + 2*len(pair_bases) entries, and each sequence has
  D + that many coefficients in total.

The witnesses are exact-rational DATA consumed by the rigorous
certificate (link L5); their generation by float optimisation is not
soundness-bearing.  What soundness rests on, and what is checked here:
  * the design header equals the audited design (36,6,2,3,2);
  * every tail base satisfies |z| < 1 exactly (admissibility in the
    sense of def:upper: |u_k| <= c r^k for some r < 1), pair bases are
    genuinely non-real, and the expanded term list is closed under
    conjugation (the sequences are real);
  * lambda^(2) = 0 exactly (Lambda_2 = {0}) and lambda^(1) >= 0
    (Lambda_1 = [0, infty));
  * coefficient counts and the common denominator 10^20.
"""
import json
from fractions import Fraction as Fr

from qx import GQ

DESIGN = (36, 6, 2, 3, 2)


def expand_sequence(coeffs, D, real_bases, pair_bases):
    """(finite l_1..l_D, [(z, r_z)] with conjugates expanded)."""
    l = list(coeffs[:D])
    terms = []
    idx = D
    for z in real_bases:
        terms.append((GQ(z), GQ(coeffs[idx])))
        idx += 1
    for zr, zi in pair_bases:
        a, b = coeffs[idx], coeffs[idx + 1]
        idx += 2
        z = GQ(zr, zi)
        r = GQ(a / 2, -b / 2)
        terms.append((z, r))
        terms.append((z.conj(), r.conj()))
    assert idx == len(coeffs), "coefficient list length mismatch"
    return l, terms


def parse_witness(path):
    with open(path) as fh:
        W = json.load(fh)
    out = {"path": path, "design": tuple(W["design"]), "D": W["D"],
           "denominator": W["denominator"],
           "real_bases": [Fr(z) for z in W["real_bases"]],
           "pair_bases": [(Fr(a), Fr(b)) for a, b in W["pair_bases"]],
           "certificates": {}}
    for kap in ("2", "1"):
        C = W[f"kappa{kap}"]
        cert = {"lambda": Fr(C["lambda"]), "grid_value": C["value"],
                "sequences": {}}
        for nm, key in (("p", "cp"), ("v", "cv")):
            coeffs = [Fr(s) for s in C[key]]
            l, terms = expand_sequence(coeffs, W["D"], out["real_bases"],
                                       out["pair_bases"])
            cert["sequences"][nm] = {"coeffs": coeffs, "finite": l,
                                     "terms": terms,
                                     "n_coeffs": len(coeffs)}
        out["certificates"][kap] = cert
    return out


def validate_witness(W):
    checks = []

    def chk(name, ok):
        checks.append((name, bool(ok)))

    chk("design_match", W["design"] == DESIGN)
    chk("denominator_is_1e20", W["denominator"] == 10 ** 20)
    n_terms = len(W["real_bases"]) + 2 * len(W["pair_bases"])
    for z in W["real_bases"]:
        chk("real_base_in_unit_disk", z * z < 1)
    for zr, zi in W["pair_bases"]:
        chk("pair_base_in_unit_disk", zr * zr + zi * zi < 1)
        chk("pair_base_nonreal", zi != 0)
    for kap, cert in W["certificates"].items():
        lam = cert["lambda"]
        if kap == "2":
            chk("lambda2_is_zero", lam == 0)
        else:
            chk("lambda1_nonneg", lam >= 0)
        for nm, S in cert["sequences"].items():
            chk(f"{nm}{kap}_coeff_count",
                S["n_coeffs"] == W["D"] + n_terms)
            chk(f"{nm}{kap}_finite_len", len(S["finite"]) == W["D"])
            chk(f"{nm}{kap}_term_count", len(S["terms"]) == n_terms)
            # conjugation closure of the expanded term multiset
            terms = S["terms"]
            chk(f"{nm}{kap}_conjugate_closed",
                all(any(t2[0] == z.conj() and t2[1] == r.conj()
                        for t2 in terms) for z, r in terms))
            dens = {x.denominator for x in S["coeffs"]}
            dens |= {z.denominator for z in W["real_bases"]}
            for zr, zi in W["pair_bases"]:
                dens.add(zr.denominator)
                dens.add(zi.denominator)
            chk(f"{nm}{kap}_denominators_divide_1e20",
                all(10 ** 20 % d == 0 for d in dens))
    return {"checks": checks,
            "all_ok": all(ok for _, ok in checks),
            "n_checks": len(checks),
            "n_failed": sum(1 for _, ok in checks if not ok)}


if __name__ == "__main__":
    import os
    base = os.path.expanduser(
        "~/workspace/bigospeedrun/catalan-audit/catalan-exponent/"
        "certificates/cert_36_6_2_3_2")
    for fn in ("cat_tail_edges_out.json", "cat_tail_opt_out.json"):
        W = parse_witness(os.path.join(base, fn))
        v = validate_witness(W)
        print(fn, "design", W["design"], "D", W["D"],
              "bases:", len(W["real_bases"]), "real +",
              len(W["pair_bases"]), "pairs; all_ok:", v["all_ok"],
              f"({v['n_checks'] - v['n_failed']}/{v['n_checks']} checks)")
        for kap, cert in W["certificates"].items():
            print("  kappa", kap, "lambda", cert["lambda"],
                  {nm: S["n_coeffs"] for nm, S in
                   cert["sequences"].items()})
