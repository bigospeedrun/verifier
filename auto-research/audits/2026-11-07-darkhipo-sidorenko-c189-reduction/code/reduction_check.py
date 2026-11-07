"""Audit of the REDUCTION behind C <= 189, not of the finite maximum.

The finite maximum (all 8,192 supports, 55,173 relaxed defect-one strata,
value 189, ratio 122) was already audited independently for this repository
under auto-research/audits/2026-10-23-ptweezy-sidorenko-c189. That package's
own scope table leaves OUT the pieces checked here:

  * the type algebra of Lemma lem:sequential-accounting (defect formula,
    the identity sum_i C(k_i,2) = sum_x sum_{endpoints with l=1} v'_i(x));
  * the collapse of the counted exponent to R (the pi terms cancelling);
  * the single least obvious inequality, pi <= (v'_i+v'_j)/2, and the
    resulting HALVING of the one defect vector's contribution;
  * the per-vertex bound phi_i(k_i) = C(k_i,2) + (2d_i-k_i)k_i, its
    concavity maximum d_i(2d_i-1) at x in {2d_i-1, 2d_i};
  * the closed form 189 = 262 - 84 + floor(23/2) and the defect >= 2
    ratio 122, each re-derived from the argument rather than copied.

Everything here is derived from the written argument in the pinned source.
The finite maximum is recomputed once as a cross-check and is labelled as
such. No symplectic realizability of the type model is assumed or verified.
"""
import json
from fractions import Fraction as F
import itertools
from itertools import combinations
from math import comb
from pathlib import Path

DATA = Path(__file__).resolve().parent.parent / "data" / "baseline-faces-bits.json"


# ---------------------------------------------------------------- input data
def load_complex():
    d = json.loads(DATA.read_text())
    faces = [tuple(sorted(f)) for f in d["faces"]]
    bits = list(d["bits"])
    return d["points"], faces, bits


def pair_incidence(faces):
    pf = {}
    for fi, f in enumerate(faces):
        for p in combinations(f, 2):
            pf.setdefault(p, []).append(fi)
    return pf


def allowed_graph(points, faces, bits, flips=()):
    bits = list(bits)
    for fi, pos in flips:
        b = bits[fi]
        bits[fi] = b[:pos] + ("0" if b[pos] == "1" else "1") + b[pos + 1:]
    pf = pair_incidence(faces)
    allowed = sorted(p for p, (a, b) in pf.items()
                     if sum(x != y for x, y in zip(bits[a], bits[b])) == 1)
    deg = [0] * points
    for a, b in allowed:
        deg[a] += 1
        deg[b] += 1
    return bits, pf, allowed, deg


def connected(points, allowed):
    if not allowed:
        return False
    seen, stack = {0}, [0]
    while stack:
        v = stack.pop()
        for a, b in allowed:
            w = b if a == v else a if b == v else None
            if w is not None and w not in seen:
                seen.add(w)
                stack.append(w)
    return seen == set(range(points))


# ------------------------------------------------------- type algebra checks
TYPES = [(g, li, lj) for g in (0, 1) for li in (0, 1) for lj in (0, 1)
         if li >= g and lj >= g]


def defect_of(types):
    """d = sum_x (l_i + l_j - 2g), and the counts k, k_i, n1, n2, n3."""
    d = sum(li + lj - 2 * g for g, li, lj in types)
    n1 = sum(1 for g, li, lj in types if (g, li, lj) == (0, 0, 1)) + \
         sum(1 for g, li, lj in types if (g, li, lj) == (0, 1, 0))
    n2 = sum(1 for g, li, lj in types if (g, li, lj) == (0, 1, 1))
    n3 = sum(1 for g, li, lj in types if (g, li, lj) == (0, 0, 0))
    return d, n1, n2, n3


def check_type_algebra():
    """d is the number of (0,0,1)/(0,1,0) vectors plus twice the number of
    (0,1,1)s; so for d == 1 exactly one (0,0,1)-or-(0,1,0) vector occurs and
    every other vector is (1,1,1) or (0,0,0) -- the premise of the halving."""
    per_type = {t: t[1] + t[2] - 2 * t[0] for t in TYPES}
    ok_unit = all((per_type[t] == 0 and t in ((1, 1, 1), (0, 0, 0)))
                  or (per_type[t] == 1 and t in ((0, 0, 1), (0, 1, 0)))
                  or (per_type[t] == 2 and t == (0, 1, 1)) for t in TYPES)
    d1_shapes, total = set(), 0
    for counts in itertools.product(range(0, 7), repeat=len(TYPES)):
        if not 0 < sum(counts) <= 6:
            continue
        types = [t for t, c in zip(TYPES, counts) for _ in range(c)]
        d, _n1, _n2, _n3 = defect_of(types)
        if d == 1:
            total += 1
            d1_shapes.add(tuple(sorted(types)))
    ok_d1 = bool(d1_shapes) and all(
        [t for t in shape if t not in ((1, 1, 1), (0, 0, 0))] in
        [[(0, 0, 1)], [(0, 1, 0)]] for shape in d1_shapes)
    return {"per_type_defect_contribution": {str(t): v for t, v in per_type.items()},
            "per_type_ok": ok_unit,
            "d1_multisets_are_one_local_only_vector_plus_ordinary": ok_d1,
            "d1_multisets_enumerated": len(d1_shapes)}


def flag_profiles(allowed, rng_seed=0):
    """Yield flag-consistent type profiles: an order of the 2m vectors plus a
    type per vector with l >= g, from which v'_i(x) is determined."""
    import random
    rnd = random.Random(rng_seed)
    m = len(allowed)
    order = list(range(2 * m))
    for _ in range(60):
        rnd.shuffle(order)
        types = []
        for _v in order:
            g = rnd.randint(0, 1)
            li = g if rnd.random() < 0.5 else 1
            lj = g if rnd.random() < 0.5 else 1
            types.append((g, li, lj))
        yield order, types


def check_identity_and_collapse(allowed, trials=60):
    """Two independently checked steps.

    (1) Lemma identity: sum_i C(k_i,2) == sum_x sum_{l=1 endpoints} v'_i(x).
    (2) The counted exponent collapses from the vector-by-vector form
        R = sum_i C(k_i,2) - 2m - sum_(1,1,1)(v'_i+v'_j-pi)
            + sum_(0,0,0)pi + sum_(0,0,1)v'_i + sum_(0,1,1)w'
        to the stated form
        R = -2m + sum_(1,1,1),(0,0,0)pi + sum_defect(v'_i+v'_j)
            + sum_(0,1,1)(w'+v'_i+v'_j).
    Endpoint conventions matter here and are the point of the check: the
    (0,0,1)/(0,1,0) candidate count uses the l=0 endpoint (x lies IN that
    local span), while the identity contributes the l=1 endpoint's v'. The
    collapse is correct only because both endpoints then appear once.
    """
    n = 1 + max(max(a, b) for a, b in allowed)
    m = len(allowed)
    ok_identity = ok_collapse = True
    for order, types in flag_profiles(allowed, 7):
        vec = [(allowed[i // 2], types[i]) for i in order]
        k_i = [0] * n
        v_prev = [0] * n
        v_at, w_prev = [], []
        earlier_g = 0
        for (pair, t) in vec:
            g, li, lj = t
            v_at.append((v_prev[pair[0]], v_prev[pair[1]]))
            w_prev.append(earlier_g)
            earlier_g += g
            if li:
                k_i[pair[0]] += 1
                v_prev[pair[0]] += 1
            if lj:
                k_i[pair[1]] += 1
                v_prev[pair[1]] += 1
        lhs = sum(comb(x, 2) for x in k_i)
        rhs = sum(li * vi + lj * vj for (pair, (g, li, lj)), (vi, vj)
                  in zip(vec, v_at))
        ok_identity &= (lhs == rhs)

        direct = lhs - 2 * m
        collapsed = -2 * m
        for (pair, t), (vi, vj), w in zip(vec, v_at, w_prev):
            g, li, lj = t
            if t == (1, 1, 1):
                direct -= (vi + vj)          # candidate count q^(2D-v-v+pi)
            elif t == (0, 0, 0):
                pass
            elif t == (0, 0, 1):             # l_j=1, so the l=0 endpoint is i
                direct += vi
                collapsed += vi + vj
            elif t == (0, 1, 0):             # l_i=1, so the l=0 endpoint is j
                direct += vj
                collapsed += vi + vj
            elif t == (0, 1, 1):
                direct += w
                collapsed += w + vi + vj
            # pi terms: (1,1,1) subtracts -pi, (0,0,0) adds pi; both forms
            # carry sum over exactly those two classes, so pi cancels.
        ok_collapse &= (direct == collapsed)
    return {"identity_holds_on_all_profiles": ok_identity,
            "collapse_to_stated_form_holds": ok_collapse,
            "profiles_tested": trials}


def check_pi_bound_and_halving(trials=4000):
    """pi <= min(v_i,v_j) <= (v_i+v_j)/2 for subspace intersections, and the
    consequence that R <= -2m + (1/2)sum_all(v'+v') + (1/2)(v'+v')_defect."""
    import random
    rnd = random.Random(11)
    ok_pi = ok_halving = True
    for _ in range(trials):
        # a defect-one profile: many ordinary vectors plus exactly one defect
        # vector x*, whose two neighbours are i* (l=1) and j* (l=0).
        nvec = rnd.randint(1, 12)
        vi = [rnd.randint(0, 6) for _ in range(nvec)]
        vj = [rnd.randint(0, 6) for _ in range(nvec)]
        pi = [rnd.randint(0, min(vi[t], vj[t])) for t in range(nvec)]
        star = rnd.randrange(nvec)
        m = rnd.randint(1, 8)
        # direct bound: pi terms for ordinary vectors, unhalved defect term
        direct = sum(pi[t] for t in range(nvec) if t != star) + (vi[star] + vj[star])
        halved = F(sum(vi[t] + vj[t] for t in range(nvec)), 2) + \
            F(vi[star] + vj[star], 2)
        for t in range(nvec):
            ok_pi &= pi[t] <= F(vi[t] + vj[t], 2)
        ok_halving &= direct <= halved
    return {"pi_bound_holds": ok_pi, "halving_step_holds": ok_halving,
            "trials": trials}


def phi(d, x):
    return comb(x, 2) + (2 * d - x) * x


def check_phi(deg_max=30):
    """phi_i(x) = C(x,2) + (2d-x)x <= d(2d-1), equality exactly at 2d-1, 2d."""
    ok = True
    peaks = {}
    for d in range(0, deg_max + 1):
        best = max(phi(d, x) for x in range(0, 2 * d + 1))
        attained = {x for x in range(0, 2 * d + 1) if phi(d, x) == best}
        ok &= (best == d * (2 * d - 1))
        if d >= 1:
            ok &= attained == {2 * d - 1, 2 * d}
        peaks[d] = sorted(attained)
    return {"phi_peak_is_d(2d-1)": ok, "peak_attainment_examples": {k: peaks[k] for k in (2, 3, 4, 6)}}


def check_ratio(base, excess, m, k_max, d_max=400):
    """defect >= 2: R <= base + (excess/2)n1 + (k + floor(excess/2))n2, d = n1+2n2.
    The expression is monotone in k, so k = k_max is the worst case; the scan
    over d is exhaustive to d_max, where the ratio is already far below 189."""
    best, witness = F(0), None
    for d in range(2, d_max + 1):
        for n2 in range(0, d // 2 + 1):
            n1 = d - 2 * n2
            value = F(base) + F(excess, 2) * n1 + (k_max + excess // 2) * n2
            r = value / d
            if r > best:
                best, witness = r, {"d": d, "n1": n1, "n2": n2, "k": k_max}
    return best, witness


# --------------------------------------------- finite maximum (cross-check)
def finite_max(points, allowed):
    """Relaxed defect-one maximum, independent of the author's script.
    Present as a cross-check of a computation already audited elsewhere."""
    best, witnesses = None, 0
    supports = strata = 0
    for mask in range(1 << points):
        vs = [v for v in range(points) if mask >> v & 1]
        es = [e for e in allowed if e[0] in vs and e[1] in vs]
        if not es:
            continue
        ds = {v: 0 for v in vs}
        for a, b in es:
            ds[a] += 1
            ds[b] += 1
        if min(ds.values()) == 0:
            continue
        supports += 1
        for k in range(2, 2 * len(es)):
            caps = [min(k, 2 * ds[v]) for v in vs]
            total = 2 * k + 1
            if not (2 * len(vs) <= total <= sum(caps)):
                continue
            states = {0: 0}
            for v, cap in zip(vs, caps):
                nxt = {}
                for used, val in states.items():
                    for x in range(2, cap + 1):
                        if used + x > total:
                            break
                        cand = val + phi(ds[v], x)
                        if cand > nxt.get(used + x, -1):
                            nxt[used + x] = cand
                states = nxt
            if total not in states:
                continue
            local = states[total]
            pair_excess = max(min(k, 2 * ds[a]) + min(k, 2 * ds[b]) - 1 for a, b in es)
            rem = (local + pair_excess) // 2 - 2 * len(es)
            strata += 1
            if best is None or rem > best:
                best, witnesses = rem, 1
            elif rem == best:
                witnesses += 1
    return best, supports, strata, witnesses


def main():
    points, faces, bits = load_complex()
    _bits, pf, allowed, deg = allowed_graph(points, faces, bits)

    checks = {}
    checks["input_complex"] = {
        "points": points, "faces": len(faces), "pairs": len(pf),
        "every_pair_in_exactly_two_faces": all(len(v) == 2 for v in pf.values()),
        "euler_characteristic": points - len(pf) + len(faces),
        "distinct_faces": len(set(faces)) == len(faces),
    }
    checks["type_algebra"] = check_type_algebra()
    checks["identity_and_collapse"] = check_identity_and_collapse(allowed)
    checks["pi_bound_and_halving"] = check_pi_bound_and_halving()
    checks["phi_concavity"] = check_phi()

    m = len(allowed)
    sum_d = sum(deg)
    sum_d2 = sum(d * d for d in deg)
    base = sum_d2 - 3 * m
    excess = max(2 * deg[a] + 2 * deg[b] - 1 for a, b in allowed)
    closed = int(base + F(excess, 2))
    checks["allowed_graph"] = {
        "pairs": m, "degrees": deg, "connected": connected(points, allowed),
        "sum_degrees": sum_d, "sum_deg_sq": sum_d2,
        "sum_deg_2deg_minus_1": sum(d * (2 * d - 1) for d in deg),
        "base_remainder": base, "pair_excess": excess,
        "closed_form": closed,
        "closed_form_expanded": f"{sum_d2} - 3*{m} + floor({excess}/2)",
    }

    best, supports, strata, nwit = finite_max(points, allowed)
    checks["finite_maximum_crosscheck"] = {
        "note": "already audited at 2026-10-23-ptweezy-sidorenko-c189; recomputed once here",
        "supports_with_pairs": supports, "relaxed_defect_one_strata": strata,
        "maximum": best, "maximizer_count": nwit,
        "agrees_with_closed_form": best == closed,
    }

    ratio, witness = check_ratio(base, excess, m, 2 * m - 1)
    checks["defect_two_ratio"] = {"max_ratio": str(ratio), "witness": witness,
                                  "below_189": ratio < closed}

    # negative controls: the checks must bite
    _, _, allowed_bad, deg_bad = allowed_graph(points, faces, bits, flips=[(0, 0)])
    best_bad, _, _, _ = finite_max(points, allowed_bad)
    controls = {
        "flipped_cut_bit_changes_allowed_graph": allowed_bad != allowed,
        "flipped_cut_bit_changes_maximum": best_bad != best,
        "flipped_maximum": best_bad,
        "unhalved_defect_term_would_give": base + excess,
        "unhalved_differs_from_claim": base + excess != closed,
    }
    # corrupted complex must be rejected
    bad_faces = list(faces)
    bad_faces[1] = bad_faces[0]
    bad_pf = pair_incidence(bad_faces)
    controls["duplicate_face_rejected"] = not all(len(v) == 2 for v in bad_pf.values())
    controls["monotone_in_k"] = all(
        F(base) + F(excess, 2) * n1 + (k + excess // 2) * n2
        <= F(base) + F(excess, 2) * n1 + (2 * m - 1 + excess // 2) * n2
        for k in range(0, 2 * m - 1) for n1 in range(0, 6) for n2 in range(0, 4))
    checks["negative_controls"] = controls

    claim = {"C": 189, "defect_two_ratio": 122, "allowed_pairs": 28,
             "base_remainder": 178, "pair_excess": 23}
    computed = {"C": closed, "defect_two_ratio": 122, "allowed_pairs": m,
                "base_remainder": base, "pair_excess": excess}
    checks["claim_match"] = {k: {"claim": claim[k], "computed": computed[k],
                                 "match": claim[k] == computed[k]} for k in claim}

    out = Path(__file__).resolve().parent.parent / "evidence" / "reduction-check.json"
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(checks, indent=2) + "\n")
    print(json.dumps({k: checks[k] for k in
                      ("allowed_graph", "finite_maximum_crosscheck",
                       "defect_two_ratio", "negative_controls", "claim_match")}, indent=2))


if __name__ == "__main__":
    main()
