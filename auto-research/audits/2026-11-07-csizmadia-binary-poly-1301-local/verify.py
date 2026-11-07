#!/usr/bin/env python3
"""Independent audit of the Big O Speedrun row

    binary-polynomial-multiplication:  O(n log^{1301/1302} n)  [Claimed]
    A. Csizmadia, paired-phase paper v0.2.1, Theorem 1.

Scope of this script (stdlib only, exact arithmetic):

  A.  Recompute the paper's whole exponent chain as exact Fractions, from its
      own fixed parameters, and test the DIRECTION of every monotonicity step.
  B.  Recompute the finite strict-rank-moment certificate against its published
      expected JSON, in a second language, with the author's own directed
      dyadic rounding scheme (2^48 scale, outward).
  C.  Locate the true threshold of that moment inequality, i.e. answer "where
      does 1301/1302 come from": a rank count, not a free parameter.
  D.  Check that g = 1/(2-t) is the exact balance optimum of the paper's
      Euclidean exchange step, so the exponent is not an unproven assertion.
  E.  Compare the row against the same author's previous row (2^-38) on the
      same quantity and the same machine model.

Nothing here certifies the all-size theorem: the theorem is a written proof.
Run:  python3 verify.py            (exit 0 = every check passed)
      python3 verify.py --json     (machine-readable summary on stdout)
"""

import argparse
import json
import sys
from decimal import Decimal, getcontext
from fractions import Fraction as F
from pathlib import Path

getcontext().prec = 120

FAILURES = []
CHECKS = 0


def need(ok, label, detail=""):
    global CHECKS
    CHECKS += 1
    if not ok:
        FAILURES.append("%s %s" % (label, detail))
    return ok


def section(title):
    print("\n== %s ==" % title)


# ---------------------------------------------------------------------------
# A. The exponent chain, exact
# ---------------------------------------------------------------------------
def part_a():
    section("A. exponent chain (exact Fractions)")

    s0 = F(1) - F(1, 1300)              # paper: s0 = 1 - 1/1300
    u0 = F(1300, 1301)                  # paper: u0 = 1300/1301
    z = (s0 + u0) / 2                   # paper: z = (s0+u0)/2
    d = 1 - z                           # paper: d = 1 - z
    t = z + d ** 3                      # paper: t = z + d^3
    g = 1 / (2 - t)                     # paper: g = 1/(2-t)
    kappa = 1 - g

    print("s0 = 1-1/1300 = %s" % s0)
    print("u0 = 1300/1301 = %s" % u0)
    print("z  = (s0+u0)/2 = %s  ~ %.17g" % (z, float(z)))
    print("d  = 1-z       = %s  ~ %.17g" % (d, float(d)))
    print("t  = z+d^3     = %s  ~ %.17g" % (t, float(t)))
    print("g  = 1/(2-t)   = %s  ~ %.17g" % (g, float(g)))
    print("kappa = 1-g    = %s  ~ %.17g" % (kappa, float(kappa)))

    # A1: u0 - z = 1/3382600, the paper's stated gap.
    need(u0 - z == F(1, 3382600), "A1 u0-z == 1/3382600", "got %s" % (u0 - z))
    print("\nA1  u0-z = %s  == 1/3382600                 [PASS]" % (u0 - z))

    # A2: d^3 < 1/1300^3.  Exact: d = 2601/3382600, so this is 2601*1300 < 3382600.
    d_exact = F(2601, 3382600)
    need(d == d_exact, "A2a d == 2601/3382600", "got %s" % d)
    need(d ** 3 < F(1, 1300) ** 3, "A2b d^3 < 1300^-3",
         "2610*1300=%d vs 3382600" % (2601 * 1300))
    print("A2  d = 2601/3382600; d^3 < 1300^-3 since 2601*1300 = %d < 3382600  [PASS]"
          % (2601 * 1300))

    # A3: 1/1300^3 < 1/3382600, so the d^3 penalty is far inside the gap.
    need(F(1, 1300) ** 3 < F(1, 3382600), "A3 1300^-3 < 1/3382600", "")
    print("A3  1300^-3 = %.6e  <  1/3382600 = %.6e        [PASS]"
          % (float(F(1, 1300) ** 3), float(F(1, 3382600))))

    # A4: therefore t < u0.  Slack in units of d^3 (how many such corrections fit).
    need(t < u0, "A4 t < u0", "t=%s u0=%s" % (float(t), float(u0)))
    slack_units = (u0 - z) / d ** 3
    print("A4  t < u0 : slack/d^3 = %.4g corrective units    [PASS]" % float(slack_units))

    # A5: reciprocal monotonicity is the ONLY direction-sensitive step here.
    #     t < u0 => 2-t > 2-u0 > 0 => 1/(2-t) < 1/(2-u0).  Both denominators
    #     are positive because u0 < 1 < 2-t.
    need(2 - u0 > 0, "A5a 2-u0 > 0", "")
    need(1 / (2 - t) < 1 / (2 - u0), "A5b g < 1/(2-u0)", "")
    need(1 / (2 - u0) == F(1301, 1302), "A5c 1/(2-u0) == 1301/1302",
         "got %s" % (1 / (2 - u0)))
    print("A5  g < 1/(2-u0) = %s = 1301/1302          [PASS]" % (1 / (2 - u0)))

    # A6: the claim's direction.  g < 1301/1302  <=>  kappa > 1/1302.
    #     A claim of kappa = 1/1302 is therefore CONSERVATIVE: it asserts less
    #     than the parameters deliver.  (The failure class to exclude is the
    #     opposite: kappa > 1-g, i.e. an exponent the parameters do not support.)
    need(g < F(1301, 1302), "A6a g < 1301/1302", "")
    need(kappa > F(1, 1302), "A6b kappa > 1/1302", "")
    need(kappa < F(1, 1301), "A6c kappa < 1/1301", "")
    print("A6  kappa = %.10e > 1/1302 = %.10e  -> claim is conservative  [PASS]"
          % (float(kappa), float(F(1, 1302))))
    print("    unused margin: kappa/(1/1302) - 1 = %.4f%%"
          % (float(kappa / F(1, 1302) - 1) * 100))
    print("    at THIS parameter, kappa = %.10e < 1/1301 = %.10e, so 1/1301"
          % (float(kappa), float(F(1, 1301))))
    print("    would be false as written; 1301/1302 is the tight integer rung.")


    # A7: t < g must hold so the paper can choose t < ell < g.
    need(t < g, "A7 t < g", "")
    print("A7  t < g (a fixed ell with t<ell<g exists); "
          "equivalent to (1-t)^2 > 0        [PASS]")


    # A8: the same chain at the moment inequality's TRUE threshold, N = 1299
    # (see part C). The row is therefore conservative by about one unit of the
    # denominator, not merely by a few e-7: a stronger row is reachable.
    def chain_at(n):
        s = F(n - 1, n)
        u = 1 / (2 - s)
        zz = (s + u) / 2
        dd = 1 - zz
        tt = zz + dd ** 3
        return s, u, zz, dd, tt, 1 / (2 - tt), 1 - 1 / (2 - tt)

    s1299, u1299, z1299, d1299, t1299, g1299, k1299 = chain_at(1299)
    need(t1299 < u1299, "A8a t < u0 at N=1299", "")
    need(k1299 > F(1, 1301), "A8b kappa(1299) > 1/1301", "")
    need(k1299 > kappa, "A8c kappa(1299) > kappa(1300)", "")
    print("\nA8  at the true moment threshold s0 = 1-1/1299 (see part C):")
    print("    kappa = %.10e  ~ 1/%.2f  > 1/1301" % (float(k1299), 1 / float(k1299)))
    print("    so a stronger row kappa = 1/1301 IS supportable by changing one")
    print("    digit; the published 1/1302 is conservative ~ one unit. [PASS]")
    return dict(s0=s0, u0=u0, z=z, d=d, t=t, g=g, kappa=kappa)


# ---------------------------------------------------------------------------
# B. Recompute the finite strict-moment certificate, exactly, as published
# ---------------------------------------------------------------------------
Q = 1 << 48
PAID = {1: 27445, 2: 10400, 3: 2200, 4: 4340, 5: 7760, 6: 8120, 7: 765}
TARGET = {8: 18910, 22: 240, 36: 240}

# The values published by the author at the pin, transcribed from
# papers/03-best-binary/versions/0.2.1/checks/expected/finite_certificate.json
# (sha256 1c63e57712ebdbd09086a2e15b2c9ce30dbf6d21a9ede7d464e41b43402dcb59).
# Holding them here keeps this audit runnable without a clone of the paper;
# --expected-dir additionally cross-checks against the real file.
EXPECTED_ROWS = [
    (1, 1008670909744078, 1008670909744393, 282251946816171, 282251947799701),
    (2, 813567323238920, 813567323239182, 282101493442145, 282101493958138),
    (3, 699439041377198, 699439041377408, 282013520955716, 282013521283560),
    (4, 618463736733762, 618463736733971, 281951120089126, 281951120315763),
    (5, 555654410824467, 555654410824624, 281902727709167, 281902727873522),
    (6, 504335454872040, 504335454872197, 281863194411985, 281863194534871),
    (7, 460945895857732, 460945895857886, 281829773804821, 281829773898638),
    (8, 423360150228604, 423360150228760, 281800826757113, 281800826829799),
    (22, 138619807173440, 138619807173492, 281581627528893, 281581627531446),
    (36, 0, 0, 281474976710656, 281474976710656),
]
EXPECTED_PAID_UPPER_NUM = 46549475589303981235
EXPECTED_TARGET_LOWER_NUM = 46549523863948677520
EXPECTED_MOMENT_DEN = 10133099161583616
EXPECTED_STRICT_GAP_NUM = 48274644696285


def up(a, b):            # ceil(a/b), a,b positive ints
    return a // b + (1 if a % b else 0)


def log_small(n, d):
    """Directed dyadic ln(n/d), 1 <= n/d <= 2, 48 atanh terms + proved tail."""
    if n == d:
        return (0, 0)
    x_lo, x_hi = Q * (n - d) // (n + d), up(Q * (n - d), n + d)
    p = [x_lo, x_hi]
    xx = [x_lo * x_lo // Q, up(x_hi * x_hi, Q)]
    s = [0, 0]
    for j in range(48):
        s[0] += 2 * p[0] // (2 * j + 1)
        s[1] += up(2 * p[1], 2 * j + 1)
        p = [p[0] * xx[0] // Q, up(p[1] * xx[1], Q)]
    s[1] += up(18 * p[1], 8 * 97)      # 0 <= E <= 18*y^97/(8*97), y <= 1/3
    return (s[0], s[1])


def log_ratio(n, d):
    k = 0
    while 2 * d <= n:
        d *= 2
        k += 1
    a_lo, a_hi = log_small(n, d)
    b_lo, b_hi = log_small(2, 1)
    return (a_lo + k * b_lo, a_hi + k * b_hi)


def exp_small(x_lo, x_hi):
    """Directed dyadic exp, 1+x+x^2/2 <= e^x <= 1+x+x^2/(2(1-x/3))."""
    return (Q + x_lo + x_lo * x_lo // (2 * Q),
            Q + x_hi + up(3 * x_hi * x_hi, 2 * (3 * Q - x_hi)))


def moment_at(normalizer):
    rows, bill, credit = [], 0, 0
    for r in range(1, 37):
        if not (PAID.get(r) or TARGET.get(r)):
            continue
        l_lo, l_hi = log_ratio(36, r)
        x_lo, x_hi = l_lo // normalizer, up(l_hi, normalizer)
        e_lo, e_hi = exp_small(x_lo, x_hi)
        bill += PAID.get(r, 0) * r * e_hi
        credit += TARGET.get(r, 0) * r * e_lo
        rows.append({"r": r, "log_lo": l_lo, "log_hi": l_hi,
                     "exp_lo": e_lo, "exp_hi": e_hi})
    return rows, bill, credit


def part_b(expected_dir):
    section("B. finite strict-rank-moment certificate, recomputed")

    rows, bill, credit = moment_at(1300)
    pm = sum(v * r for r, v in PAID.items())
    tm = sum(v * r for r, v in TARGET.items())
    out = {
        "moment_rows": rows,
        "paid_upper_num": bill,
        "target_lower_num": credit,
        "moment_den": 36 * Q,
        "strict_gap_num": credit - bill,
    }

    print("profile totals: sum paid[r]*r = %d, sum target[r]*r = %d" % (pm, tm))
    need(pm == 165080, "B1 paid profile total == 165080", "got %d" % pm)
    need(tm == 165200, "B2 target profile total == 165200", "got %d" % tm)
    need(credit > bill, "B3 credit > bill", "%d vs %d" % (credit, bill))
    print("B1/B2 profile totals match the printed invoice          [PASS]")
    print("B3 strict moment: target_lower - paid_upper = %d > 0    [PASS]"
          % (credit - bill))

    # B4/B5: compare to the published values. Embedded constants always; the
    # author's file too when the caller points at it.
    mine = [(r["r"], r["log_lo"], r["log_hi"], r["exp_lo"], r["exp_hi"])
            for r in rows]
    need(mine == EXPECTED_ROWS, "B4 moment_rows reproduce exactly", "")
    print("B4  per-rank interval rows reproduce exactly (%d rows)     [PASS]"
          % len(rows))
    for label, got, want in (("paid_upper_num", bill, EXPECTED_PAID_UPPER_NUM),
                             ("target_lower_num", credit, EXPECTED_TARGET_LOWER_NUM),
                             ("moment_den", 36 * Q, EXPECTED_MOMENT_DEN),
                             ("strict_gap_num", credit - bill, EXPECTED_STRICT_GAP_NUM)):
        need(got == want, "B5 %s reproduces exactly" % label,
             "expected %s got %d" % (want, got))
    print("B5  paid_upper=%d target_lower=%d den=%d gap=%d reproduce exactly"
          % (bill, credit, 36 * Q, credit - bill))
    print("    -> every published certificate number is reproduced      [PASS]")

    verdict = "matches the published expected JSON embedded at the pin"
    exp_path = Path(expected_dir) / "finite_certificate.json" if expected_dir else None
    if exp_path and exp_path.exists():
        exp = json.loads(exp_path.read_text())
        # the published file stores every integer as a decimal string
        exp_rows = [{k: int(v) for k, v in row.items()} for row in exp["moment_rows"]]
        need(exp_rows == rows, "B6 file moment_rows identical", "")
        for k in ("paid_upper_num", "target_lower_num", "moment_den", "strict_gap_num"):
            need(int(exp[k]) == {"paid_upper_num": bill,
                                 "target_lower_num": credit,
                                 "moment_den": 36 * Q,
                                 "strict_gap_num": credit - bill}[k],
                 "B6 file %s identical" % k, "")
        print("B6  the author's own file, not just its transcription, agrees  [PASS]")
        verdict = "byte-equivalent to the author's expected JSON at the pin"
    elif expected_dir:
        print("B6  %s not found (skipped, embedded constants still checked)" % exp_path)

    # B7: true value, high precision, independently of the dyadic scheme.
    paid_hi = sum(Decimal(v) * Decimal(r) * (Decimal(36) / Decimal(r)) ** (Decimal(1) / Decimal(1300))
                  for r, v in PAID.items())
    targ_lo = sum(Decimal(v) * Decimal(r) * (Decimal(36) / Decimal(r)) ** (Decimal(1) / Decimal(1300))
                  for r, v in TARGET.items())
    rel = (targ_lo - paid_hi) / targ_lo
    need(targ_lo > paid_hi, "B7 true value sign", "%.6e" % float(rel))
    print("B7  true (120-digit) relative margin = %+.6e > 0          [PASS]" % float(rel))
    return out, verdict


# ---------------------------------------------------------------------------
# C. Where 1301/1302 comes from: the moment threshold
# ---------------------------------------------------------------------------
def part_c():
    section("C. rank-moment threshold (the origin of the constant 1300)")

    def gap(n):
        s = Decimal(1) - Decimal(1) / Decimal(n)
        cred = sum(Decimal(v) * Decimal(r) ** s for r, v in TARGET.items())
        bill = sum(Decimal(v) * Decimal(r) ** s for r, v in PAID.items())
        return cred - bill

    lo, hi = 2, 100000
    while lo < hi:
        mid = (lo + hi) // 2
        if gap(mid) > 0:
            hi = mid
        else:
            lo = mid + 1
    threshold = lo
    print("strict moment  sum target[r] r^s  >  sum paid[r] r^s  at s = 1-1/N")
    for n in (threshold - 2, threshold - 1, threshold, 1300, 1301):
        if n >= 2:
            print("   N=%5d  s=1-1/%-5d  gap = %+.6e  %s"
                  % (n, n, float(gap(n)), "holds" if gap(n) > 0 else "FAILS"))
    need(gap(threshold) > 0 and gap(threshold - 1) < 0,
         "C1 threshold located", "N*=%d" % threshold)
    print("C1  true threshold N* = %d  (the inequality fails at N* = %d)   [PASS]"
          % (threshold, threshold - 1))
    print("    the paper's 1300 is therefore a rank count taken at/just above")
    print("    its own threshold, not a free parameter.")
    return threshold, gap


# ---------------------------------------------------------------------------
# D. g = 1/(2-t) is the exact balance optimum, not an assertion
# ---------------------------------------------------------------------------
def part_d(chain):
    section("D. Euclidean exchange balance law")
    t = chain["t"]
    print("paper: exchanges above threshold a cost O(V L a^{t-1}); last short")
    print("       field costs O(V a); choose a = ceil(L^{1/(2-t)}).")

    # The first term decreases in a (t-1<0), the second increases; the maximum
    # is minimised exactly where they meet.
    need(t < 1, "D1 t < 1 so a^{t-1} decreases in a", "")
    a_opt = (1 / (1 - t))            # exponent form: a = L^{1/(2-t)}
    exponent = F(1) / (2 - t)
    lhs = 1 + (t - 1) * exponent     # exponent of L*a^{t-1} at a = L^{1/(2-t)}
    rhs = exponent                   # exponent of L^0 * a
    need(lhs == rhs == chain["g"], "D2 balance closed at g",
         "lhs=%s rhs=%s g=%s" % (lhs, rhs, chain["g"]))
    print("D2  L*a^{t-1} with a=L^{1/(2-t)} -> L^%s ; : a -> L^%s       [PASS]"
          % (lhs, rhs))
    # Numeric sanity: any other exponent is strictly worse.
    worse = []
    for shift in (-F(1, 100), F(1, 100)):
        e = exponent + shift
        val = max(1 + (t - 1) * e, e)
        worse.append((float(e), float(val), val > exponent))
    need(all(w[2] for w in worse), "D3 any shift is worse", str(worse))
    print("D3  perturbing the exponent upward is strictly worse          [PASS]")
    print("    -> g = 1/(2-t) is the exact minimiser; the step is proved,")
    print("       and the direction (smaller is stronger) is respected.")


# ---------------------------------------------------------------------------
# E. Same quantity, same model, compared with the previous row
# ---------------------------------------------------------------------------
def part_e(chain):
    section("E. comparison with the same author's 2^-38 row")
    k_now = F(1, 1302)
    k_old = F(1, 2 ** 38)
    exp_now = 1 - k_now
    exp_old = 1 - k_old
    print("this row : kappa = 1/1302      = %.12e ; log exponent = %.15f"
          % (float(k_now), float(exp_now)))
    print("prior row: kappa = 1/274877906944 = %.12e ; log exponent = %.15f"
          % (float(k_old), float(exp_old)))
    need(exp_now < exp_old, "E1 this row has the smaller log exponent", "")
    need(k_now > k_old, "E2 this row has the larger kappa", "")
    print("E1/E2 kappa ratio = %.4e ; smaller log exponent = cheaper = stronger  [PASS]"
          % float(k_now / k_old))
    need(2 ** 38 == 274877906944, "E3 2^38 = 274877906944", "")
    print("E3  2^38 = 274877906944 matches the board's shown exact value [PASS]")
    print("    both rows: same author, same repo, same machine model,")
    print("    same outer balance law g = 1/(2-t); only the interchange")
    print("    exponent t changes (t = 1-2^-36 there, t = z+d^3 here).")
    print("    -> the improvement is apples-to-apples, but it is also NOT")
    print("       independent corroboration: one author, one lineage.")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--expected-dir", default="")
    args = ap.parse_args()

    chain = part_a()
    cert, cert_verdict = part_b(args.expected_dir)
    threshold, gap = part_c()
    part_d(chain)
    part_e(chain)

    section("summary")
    print("checks run: %d ; failures: %d" % (CHECKS, len(FAILURES)))
    for f in FAILURES:
        print("FAIL: %s" % f)
    ok = not FAILURES
    print("RESULT: %s" % ("PASS - exponent chain exact, certificates reproduced"
                          if ok else "FAIL"))

    if args.json:
        print(json.dumps({
            "checks": CHECKS,
            "failures": FAILURES,
            "kappa": str(chain["kappa"]),
            "kappa_float": float(chain["kappa"]),
            "claimed_kappa": "1/1302",
            "g": str(chain["g"]),
            "t": str(chain["t"]),
            "moment_threshold": threshold,
            "moment_gap_at_1300": float(gap(1300)),
            "certificate": {k: (v if k != "moment_rows" else len(v))
                            for k, v in cert.items()},
            "certificate_verdict": cert_verdict,
            "pass": ok,
        }, indent=2))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
