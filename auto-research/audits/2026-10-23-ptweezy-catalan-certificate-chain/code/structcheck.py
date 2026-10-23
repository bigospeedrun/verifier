"""
struct.py -- structural link (L2): the counting identity of Lemma 3.3
and the end-to-end per-prime valuation check at N = 1.

Counting identity (checked for the scaled designs N = 1..60 and every
prime H/2 < p <= H, all in exact integer arithmetic):
    K = L - p, J = H - p,
    R0 = pos(K) + pos(J - b) - pos(min(A, K) - b),
    R  = pos(K) + pos(K - A) + pos(J - max(b, K)),
    R0 == R.

Valuation check (the claimant's gate V; an exact finite mechanism
check at N = 1 with the hypothetical value G = 1/3):
    Delta_1 = Frat + (1/3) FG   (36 x 36, exact rationals),
    Frat(r,k) = sum_t (-1)^t C(q,t) raw_rat(r, b+k+t),
    raw_rat(r,j) = M0(P_r, j) - (3/2) Z0(D_r, j),
    FG(r,k)   = sum_t (-1)^t C(q,t) * 4 * sum_{i >= j', (i-j') even}
                P_r[i] c((i-j')/2),   j' = b+k+t,
  for every prime 2 sqrt(H0) < p < H0 + 60 (p not dividing 3):
    p <= H0:  -v_p(det Delta_1) <= D_L(p)   (D_L of the unit design),
    p >  H0:  v_p(det Delta_1) >= 0.
The valuation is computed by TWO independent methods and required to
agree: (1) the exact determinant (integer Bareiss) followed by exact
p-division of numerator and denominator; (2) p-adic Gaussian
elimination over Z/p^K with full pivoting.
"""
from fractions import Fraction as Fr
from math import comb

from bmatrix import derived, moment_arrays, row_polys
from flow import D_of_x
from qx import vp_frac

DES = (36, 6, 2, 3, 2)


def _pos(y):
    return y if y > 0 else 0


def primes_upto(m):
    s = [True] * (m + 1)
    s[0] = s[1] = False
    for i in range(2, int(m ** 0.5) + 1):
        if s[i]:
            for j in range(i * i, m + 1, i):
                s[j] = False
    return [i for i in range(m + 1) if s[i]]


def counting_identity_cases():
    """All (N, p) cases of the Lemma-3.3 identity; returns
    (n_cases, n_failures)."""
    cases = 0
    fails = 0
    for N in range(1, 61):
        desN = tuple(x * N for x in DES)
        n, b, q, g, h = desN
        a, L, C, H, A = derived(desN)
        for p in primes_upto(H):
            if 2 * p <= H:
                continue
            K, J = L - p, H - p
            Bp = _pos(min(A, K) - b)
            R0 = _pos(K) + _pos(J - b) - Bp
            R = _pos(K) + _pos(K - A) + _pos(J - max(b, K))
            cases += 1
            if R0 != R:
                fails += 1
    return cases, fails


def _c(l):
    return Fr(comb(2 * l, l), 4 ** l)


def build_delta1():
    """Delta_1 = Frat + (1/3) FG for the unit design, exact."""
    n, b, q, g, h = DES
    a, L, C, H, A = derived(DES)
    M, Z0 = moment_arrays(H - 1, L - 1)
    Pr, Dr = row_polys(DES)
    Frat, FG = [], []
    for r in range(n):
        raw_rat, raw_G = [], []
        for j in range(b, b + n + q):
            s = Fr(0)
            for i, v in Pr[r].items():
                s += v * M[i][j]
            for i, v in Dr[r].items():
                s -= Fr(3, 2) * v * Z0(i, j)
            raw_rat.append(s)
            sG = Fr(0)
            for i, v in Pr[r].items():
                if i >= j and (i - j) % 2 == 0:
                    sG += v * _c((i - j) // 2)
            raw_G.append(4 * sG)
        Frat.append([sum((-1) ** t * comb(q, t) * raw_rat[k + t]
                          for t in range(q + 1)) for k in range(n)])
        FG.append([sum((-1) ** t * comb(q, t) * raw_G[k + t]
                        for t in range(q + 1)) for k in range(n)])
    G = Fr(1, 3)
    return [[Frat[r][k] + G * FG[r][k] for k in range(n)]
            for r in range(n)]


def det_int_bareiss(M):
    """Exact determinant of an integer matrix (Bareiss)."""
    n = len(M)
    A = [row[:] for row in M]
    sign = 1
    prev = 1
    for k in range(n - 1):
        if A[k][k] == 0:
            sw = -1
            for i in range(k + 1, n):
                if A[i][k] != 0:
                    sw = i
                    break
            if sw < 0:
                return 0
            A[k], A[sw] = A[sw], A[k]
            sign = -sign
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                A[i][j] = (A[i][j] * A[k][k] - A[i][k] * A[k][j]) // prev
            A[i][k] = 0
        prev = A[k][k]
        if prev == 0:
            return 0
    return sign * A[n - 1][n - 1]


def det_exact(Mq):
    """Exact determinant of a rational matrix via row scaling to an
    integer matrix plus integer Bareiss."""
    from math import gcd
    scale = Fr(1)
    A = []
    for row in Mq:
        l = 1
        for x in row:
            l = l * x.denominator // gcd(l, x.denominator)
        A.append([int(x * l) for x in row])
        scale /= l
    return det_int_bareiss(A) * scale


def vp_det_padic(Mq, p):
    """v_p(det Mq) by p-adic elimination over Z/p^K (independent of
    det_exact): clear a common p-power so all entries are p-integral,
    then full-pivot elimination tracking pivot valuations."""
    n = len(Mq)
    s = -min(min(vp_frac(x, p) if x != 0 else 0 for x in row)
             for row in Mq)
    s = max(s, 0)
    K = n * s + 3 * n + 20
    MOD = p ** K
    A = []
    for row in Mq:
        rr = []
        for x in row:
            if x == 0:
                rr.append(0)
                continue
            num, den = x.numerator * p ** s, x.denominator
            while den % p == 0:
                den //= p
                num //= p
            rr.append(num * pow(den, -1, MOD) % MOD)
        A.append(rr)

    def val(x):
        if x == 0:
            return K
        v = 0
        while x % p == 0:
            x //= p
            v += 1
        return v

    tot = 0
    for step in range(n):
        best = (K + 1, None, None)
        for i in range(step, n):
            for j in range(step, n):
                x = A[i][j]
                if x:
                    v = val(x)
                    if v < best[0]:
                        best = (v, i, j)
                        if v == 0:
                            break
            if best[0] == 0:
                break
        v, bi, bj = best
        if bi is None:
            return tot + (n - step) * K - n * s, True
        A[step], A[bi] = A[bi], A[step]
        for row in A:
            row[step], row[bj] = row[bj], row[step]
        tot += v
        piv = A[step][step]
        uinv = pow(piv // p ** v, -1, MOD)
        prow = A[step]
        for i in range(step + 1, n):
            x = A[i][step]
            if x:
                f = (x // p ** v) * uinv % MOD
                Ai = A[i]
                A[i] = [(Ai[k] - f * prow[k]) % MOD for k in range(n)]
    return tot - n * s, False


def valuation_check():
    """The full V check; returns per-prime rows and gate results."""
    n0, b0, q0, g0, h0 = DES
    a0, L0, C0, H0, A0 = derived(DES)
    D1 = build_delta1()
    det = det_exact(D1)
    assert det != 0
    rows = []
    fails = 0
    for p in primes_upto(H0 + 60):
        if p == 2 or p * p <= 4 * H0 or p == 3:
            continue
        v1 = vp_frac(det, p)
        v2, capped = vp_det_padic(D1, p)
        agree = (v1 == v2) and not capped
        if p <= H0:
            bound = -int(D_of_x(Fr(p), DES))
            ok = v1 >= bound
            rows.append({"p": p, "vp": v1, "vp_padic": v2,
                         "bound": bound, "ok": ok, "agree": agree})
        else:
            ok = v1 >= 0
            rows.append({"p": p, "vp": v1, "vp_padic": v2,
                         "bound": 0, "ok": ok, "agree": agree})
        if not (ok and agree):
            fails += 1
    return {"det": det, "rows": rows, "fails": fails}


if __name__ == "__main__":
    import time
    t0 = time.time()
    cases, fails = counting_identity_cases()
    print(f"counting identity: {cases} cases, {fails} failures "
          f"({time.time()-t0:.1f}s)")
    t0 = time.time()
    V = valuation_check()
    print(f"valuation check: det != 0, {len(V['rows'])} primes, "
          f"{V['fails']} failures ({time.time()-t0:.1f}s)")
    for r in V["rows"]:
        print("  p={p:4d} v_p={vp:4d} bound={bound:4d} ok={ok} "
              "methods agree={agree}".format(**r))
