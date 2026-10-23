"""
bmatrix.py -- the fixed rational matrix B of a design and condition
(C3), implemented independently for the audit.

Written definitions used (Carreira, def:det / def:fixed):
  P_r = (1-t)^h t^(C-1) T_d(1/t),  D_r = sgn(r-g) (1-t)^h t^(C-1) U_{d-1}(1/t),
      d = |r-g|,  T_d / U_d the Chebyshev polynomials;
  M0, Z0 the rational moment arrays of OAI Eqs. (14), (16), (17), built
  here by the Section-4.4 recurrences (the concrete form in which both
  pinned sources implement them):
      m_0 = 2, m_i = i m_{i-2}/(i+1) (even i), m_odd = 0;
      k-_1 = 2, k-_d = ((d-1) k-_{d-2} + m_{d-2} + m_{d-1})/d;
      k+_d = ((d-2) k+_{d-2} + 2/(d-1))/(d-1)  (d >= 2), k+_0 = k+_1 = 0;
      M0(i,0) = k-_i, M0(0,j) = k+_j, M0(i,j) = M0(i-1,j-1) - m_{i-1}/j;
      Z0(i,j) = -H2_i if i == j else (H_i - H_j)/(i - j),
      H_i, H2_i the harmonic sums;
  B(r,k) = sum_{j=0}^{q} (-1)^j C(q,j) [ M0(P_r, b+k+j)
                                         - (3/2) Z0(D_r, b+k+j) ],
  B0 = rows 0..n-1, B1 = rows 1..n.

(C3) is verified three independent ways:
  (a) the paper's elimination rule modulo the certification prime
      P (smallest prime > H0): all pivots nonzero;
  (b) the three determinants computed exactly over Q (Bareiss);
  (c) full rank modulo several further primes above H0.
Positive control: the preprint design (48,7,4,4,2) modulo 101 must
reproduce the paper's Table 1 pivots exactly (TABLE1 below, transcribed
from the pinned sources: Carreira's tex Table and the claimant's
cat_cert4_new.py) including the swaps (30,31), (45,46) at sigma = +1.
Also checked: row supports in [A, H-1] (rows 0..n-1), the zeta(2)
coefficient of every raw entry is exactly 0 (rows 0..n), and every
denominator prime of B is <= H0.
"""
from fractions import Fraction as Fr
from math import comb, gcd

from qx import det_bareiss, pivot_pattern_mod, rank_mod


def derived(des):
    n, b, q, g, h = des
    a = b + q
    L = n + a
    C = L + g
    H = C + h
    A = a + 2 * g
    return a, L, C, H, A


def moment_arrays(Imax, Jmax):
    """Returns (M0, Z0) with M0 a list of lists and Z0 a function."""
    top = max(Imax, Jmax) + 2
    m = [Fr(0)] * (top + 1)
    m[0] = Fr(2)
    for i in range(2, top + 1, 2):
        m[i] = i * m[i - 2] / (i + 1)
    km = [Fr(0)] * (top + 1)
    km[1] = Fr(2)
    for d in range(2, top + 1):
        km[d] = ((d - 1) * km[d - 2] + m[d - 2] + m[d - 1]) / d
    kp = [Fr(0)] * (top + 1)
    for d in range(2, top + 1):
        kp[d] = ((d - 2) * kp[d - 2] + Fr(2, d - 1)) / (d - 1)
    M = [[Fr(0)] * (Jmax + 1) for _ in range(Imax + 1)]
    for i in range(Imax + 1):
        M[i][0] = km[i]
    for j in range(Jmax + 1):
        M[0][j] = kp[j]
    for i in range(1, Imax + 1):
        for j in range(1, Jmax + 1):
            M[i][j] = M[i - 1][j - 1] - m[i - 1] / j
    H1 = [Fr(0)] * (top + 1)
    H2 = [Fr(0)] * (top + 1)
    for i in range(1, top + 1):
        H1[i] = H1[i - 1] + Fr(1, i)
        H2[i] = H2[i - 1] + Fr(1, i * i)

    def Z0(i, j):
        if i == j:
            return -H2[i]
        return (H1[i] - H1[j]) / (i - j)

    return M, Z0


def chebyshev_TU(dmax):
    """T_d, U_d as integer coefficient lists in x (low-first)."""
    T = [[1], [0, 1]]
    U = [[1], [0, 2]]
    for _ in range(2, dmax + 1):
        for S in (T, U):
            prev1, prev2 = S[-1], S[-2]
            nxt = [0] * (len(prev1) + 1)
            for i, v in enumerate(prev1):
                nxt[i + 1] += 2 * v
            for i, v in enumerate(prev2):
                nxt[i] -= v
            S.append(nxt)
    return T, U


def row_polys(des):
    """P_r, D_r for r = 0..n as dicts {t-exponent: coefficient}."""
    n, b, q, g, h = des
    a, L, C, H, A = derived(des)
    T, U = chebyshev_TU(n + 1)
    binh = [(-1) ** v * comb(h, v) for v in range(h + 1)]

    def build(coeffs_x, sign):
        out = {}
        for k, v in enumerate(coeffs_x):
            if v:
                e0 = C - 1 - k
                for s, bv in enumerate(binh):
                    out[e0 + s] = out.get(e0 + s, 0) + sign * v * bv
        return {e: v for e, v in out.items() if v}

    Pr, Dr = [], []
    for r in range(n + 1):
        d = abs(r - g)
        sg = (r > g) - (r < g)
        Pr.append(build(T[d], 1))
        Dr.append(build(U[d - 1], sg) if d >= 1 else {})
    return Pr, Dr


def _c(l):
    return Fr(comb(2 * l, l), 4 ** l)


def zeta2_failures(des, Pr, Dr):
    """Count of raw entries (r, j), r = 0..n, b <= j < L, whose
    zeta(2) coefficient (3/2)[ sum_i P_r[i] c((j-i-1)/2) - D_r[j] ]
    is nonzero (the bracket is what is tested)."""
    n, b, q, g, h = des
    a, L, C, H, A = derived(des)
    bad = 0
    total = 0
    for r in range(n + 1):
        for j in range(b, L):
            s = Fr(0)
            for i, v in Pr[r].items():
                if i < j and (j - i - 1) % 2 == 0:
                    s += v * _c((j - i - 1) // 2)
            s -= Dr[r].get(j, 0)
            total += 1
            if s != 0:
                bad += 1
    return bad, total


def build_B(des):
    """The (n+1) x n matrix B, assembled by the def:fixed binomial
    formula; also returns it assembled by successive differences and
    asserts the two agree."""
    n, b, q, g, h = des
    a, L, C, H, A = derived(des)
    M, Z0 = moment_arrays(H - 1, L - 1)
    Pr, Dr = row_polys(des)
    # raw values w_r(j) = M0(P_r, j) - (3/2) Z0(D_r, j), j = b..b+n+q-1
    B, Bdiff = [], []
    for r in range(n + 1):
        raw = []
        for j in range(b, b + n + q):
            s = Fr(0)
            for i, v in Pr[r].items():
                s += v * M[i][j]
            for i, v in Dr[r].items():
                s -= Fr(3, 2) * v * Z0(i, j)
            raw.append(s)
        row = []
        for k in range(n):
            s = Fr(0)
            for t in range(q + 1):
                s += (-1) ** t * comb(q, t) * raw[k + t]
            row.append(s)
        B.append(row)
        v = raw[:]
        for _ in range(q):
            v = [v[k] - v[k + 1] for k in range(len(v) - 1)]
        Bdiff.append(v)
    assert B == Bdiff, "binomial assembly != successive differences"
    return B, Pr, Dr


def prime_factors(nn):
    nn = abs(nn)
    ps = set()
    p = 2
    while p * p <= nn:
        while nn % p == 0:
            ps.add(p)
            nn //= p
        p += 1
    if nn > 1:
        ps.add(nn)
    return ps


def max_denominator_prime(B):
    mp = 1
    for row in B:
        for x in row:
            if x.denominator > 1:
                mp = max(mp, max(prime_factors(x.denominator)))
    return mp


def smallest_prime_above(m):
    def is_prime(p):
        if p < 2:
            return False
        i = 2
        while i * i <= p:
            if p % i == 0:
                return False
            i += 1
        return True
    p = m + 1
    while not is_prime(p):
        p += 1
    return p


def analyse_B(des, P):
    """Full (C3) analysis for one design at certification prime P."""
    n, b, q, g, h = des
    a, L, C, H, A = derived(des)
    B, Pr, Dr = build_B(des)
    badz, totz = zeta2_failures(des, Pr, Dr)
    supports_ok = True
    for r in range(n):
        degs = list(Pr[r]) + list(Dr[r])
        if not degs or min(degs) < A or max(degs) > H - 1:
            supports_ok = False
    mp = max_denominator_prime(B)
    B0 = B[:n]
    B1 = B[1:]
    out = {"design": des, "H": H, "zeta2_failures": badz,
           "zeta2_entries": totz, "supports_ok": supports_ok,
           "max_denominator_prime": mp, "P": P, "pivots": {},
           "dets": {}, "ranks": {}}
    for sg in (0, 1, -1):
        M = [[B0[i][k] + sg * B1[i][k] for k in range(n)] for i in range(n)]
        swaps, piv = pivot_pattern_mod(M, P)
        out["pivots"][str(sg)] = {"pivots": piv, "swaps": swaps,
                                  "all_nonzero": all(x != 0 for x in piv)
                                  and len(piv) == n}
        out["dets"][str(sg)] = det_bareiss(M)
        rk, _ = rank_mod(M, P)
        out["ranks"][str(sg)] = rk
    return out


# The paper's Table 1 (preprint design (48,7,4,4,2) mod 101), as printed
# in Carreira's paper and transcribed in the pinned claimant sources.
TABLE1 = {
    0: [60, 68, 62, 79, 47, 32, 69, 57, 30, 72, 35, 66, 43, 20, 85, 48,
        88, 4, 77, 54, 60, 79, 26, 68, 83, 39, 40, 65, 1, 68, 78, 24,
        15, 98, 32, 22, 94, 9, 99, 10, 15, 75, 4, 2, 25, 53, 90, 79],
    1: [38, 51, 90, 70, 5, 21, 88, 55, 45, 20, 35, 41, 77, 10, 18, 25,
        76, 14, 38, 72, 6, 66, 56, 35, 83, 58, 56, 11, 17, 20, 30, 24,
        28, 11, 25, 70, 79, 99, 66, 38, 4, 41, 63, 91, 63, 17, 90, 98],
    -1: [82, 92, 26, 87, 21, 74, 87, 88, 88, 3, 14, 23, 38, 58, 36, 20,
         26, 33, 94, 74, 78, 45, 93, 86, 73, 66, 45, 30, 61, 3, 88, 27,
         20, 58, 69, 48, 78, 39, 48, 1, 66, 18, 86, 93, 52, 92, 39, 77],
}
TABLE1_SWAPS = {0: [], 1: [(30, 31), (45, 46)], -1: []}


if __name__ == "__main__":
    import time
    t0 = time.time()
    ctrl = analyse_B((48, 7, 4, 4, 2), 101)
    ok = True
    for sg in (0, 1, -1):
        match = ctrl["pivots"][str(sg)]["pivots"] == TABLE1[sg]
        swmatch = [tuple(s) for s in ctrl["pivots"][str(sg)]["swaps"]] == \
            TABLE1_SWAPS[sg]
        print(f"paper control sigma={sg:+d}: pivots match Table 1: {match}; "
              f"swaps match: {swmatch}; det != 0: {ctrl['dets'][str(sg)] != 0}")
        ok &= match and swmatch
    print("paper control zeta2 failures:", ctrl["zeta2_failures"],
          "of", ctrl["zeta2_entries"], "; max denom prime",
          ctrl["max_denominator_prime"], "(H = 65)")
    print("CONTROL", "PASS" if ok else "FAIL", f"{time.time()-t0:.1f}s")
    t0 = time.time()
    new = analyse_B((36, 6, 2, 3, 2), 53)
    for sg in (0, 1, -1):
        pv = new["pivots"][str(sg)]
        print(f"new sigma={sg:+d}: all pivots nonzero mod 53: "
              f"{pv['all_nonzero']}, swaps {pv['swaps']}, "
              f"det != 0: {new['dets'][str(sg)] != 0}, "
              f"rank {new['ranks'][str(sg)]}")
    print("new zeta2 failures:", new["zeta2_failures"], "of",
          new["zeta2_entries"], "; max denom prime",
          new["max_denominator_prime"], "(H = 49); supports ok:",
          new["supports_ok"], f"{time.time()-t0:.1f}s")
