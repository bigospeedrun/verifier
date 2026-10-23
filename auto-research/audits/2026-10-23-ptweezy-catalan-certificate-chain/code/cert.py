"""
cert.py -- the rigorous real-place certificate (link L5), implemented
independently for the audit.  This is the audit's analogue of the
claimant's cat_cert7_new.py, rebuilt from the written definitions
(Carreira, def:upper and prop:c4's proof sketch):

  U_kappa = (-1 + alpha + gamma_g) log 2 + kappa ||p||_*^2
            + (1/2) ||v||_*^2 + sup X + sup Y,
  X(x) = (alpha + 2 gamma_g) log|x| + 2 eta log(1-x)
         - (kappa/2 + alpha + eta + gamma_g) log(1+x^2)
         + lambda (2 gamma_g - 2x^2/(1+x^2)) - 2 kappa T(p, x) - S(v, x),
  Y(s) = beta log s + gamma_q log(1-s) + 2 T(v, s),
  u_k = l_k (k <= D) + sum_z r_z z^k,
  T(u,x) = sum_k u_k T_k(x)/k,  S(u,x) = sum_k u_k x^k/k,
  ||u||_*^2 = sum_k u_k^2/k,
with the closed forms
  T(u,x) = sum_k l_k T_k(x)/k - (1/2) sum_z r_z Log(1 - 2xz + z^2),
  S(u,x) = sum_k l_k x^k/k - sum_z r_z Log(1 - xz),
  ||u||_*^2 = sum_{k<=D} (l_k^2 + 2 l_k t_k)/k
              - sum_{z,z'} r_z r_z' Log(1 - z z'),  t_k = sum_z r_z z^k.

Method (certification standard):
  * X' = A_X/Q_X, Y' = A_Y/Q_Y are built in exact Gaussian-rational
    polynomial arithmetic; every division is exact and the imaginary
    parts cancel identically (asserted).
  * All real roots of A_X in (-1,0) and (0,1) and of A_Y in (0,1) are
    isolated by Descartes' rule of signs with bisection (VCA) in exact
    integer arithmetic and refined by exact sign bisection to brackets
    of width <= 2^-50, each with a strict sign change.
  * X -> -inf at 0 and 1 and Y -> -inf at 0 and 1 (the log coefficients
    alpha + 2 gamma_g, 2 eta, beta, gamma_q are positive and all other
    terms are bounded on the closed interval), so
    sup X = max(X(-1), stationary values), sup Y = max(stationary
    values).
  * Values are enclosed with mpmath interval arithmetic at 60 digits.
    TWO-SIDED sup enclosures are produced: the upper side by the
    mean-value allowance  X <= X(lo) + w * sup|X'|  on each bracket
    (X' enclosed by interval evaluation of its closed form, itself
    checked against A_X/Q_X), the lower side by the pointwise values
    at the bracket left ends and at -1.  This is what the final
    assembly needs: U_kappa from the upper sides, and lower bounds
    Sigma_kappa = sup X + sup Y from the lower sides -- with no
    rounding fudge anywhere.
  * Controls: A/Q against mpmath numerical differentiation of the
    closed forms and against the closed-form derivatives; a dense
    float grid (numpy) against the certified suprema.
"""
import math
import time
from fractions import Fraction as Fr

import mpmath as mpm

from qx import GQ, padd, psub, pmul, pscale, pdiv_exact, peval_fr, \
    shift_int, to_int_poly, var01

DES = (36, 6, 2, 3, 2)
_n0, _b0, _q0, _g0, _h0 = DES
ALPHA = Fr(_b0 + _q0, _n0)
BETA = Fr(_b0, _n0)
GQ_ = Fr(_q0, _n0)
GG = Fr(_g0, _n0)
ETA = Fr(_h0, _n0)

BRACKET_BITS = 50
IVDPS = 60


# ------------------------------------------------------------ exact ----
def _chebU_gq(nmax):
    """Chebyshev U_k over Q(i), k = 0..nmax (coefficient lists)."""
    U = [[GQ(1)], [GQ(0), GQ(2)]]
    for _ in range(2, nmax + 1):
        U.append(psub(pmul([GQ(0), GQ(2)], U[-1]), U[-2]))
    return U


def build_numerators(kap, cert, D):
    """Exact (A_X, Q_X, A_Y, Q_Y) as Fraction polynomials for one
    kappa and one witness certificate (dict from witness.py)."""
    lp = cert["sequences"]["p"]["finite"]
    lv = cert["sequences"]["v"]["finite"]
    tp = cert["sequences"]["p"]["terms"]
    tv = cert["sequences"]["v"]["terms"]
    lam = cert["lambda"]
    UP = _chebU_gq(D + 1)
    X1 = [GQ(0), GQ(1)]            # x
    OMX = [GQ(1), GQ(-1)]          # 1 - x
    OPX2 = [GQ(1), GQ(0), GQ(1)]   # 1 + x^2

    def quad(z):
        return [GQ(1) + z * z, GQ(-2) * z]

    def lin(z):
        return [GQ(1), -z]

    QX = pmul(X1, OMX)
    for _ in range(3 - kap):
        QX = pmul(QX, OPX2)
    for z, _ in tp:
        QX = pmul(QX, quad(z))
    for z, _ in tv:
        QX = pmul(QX, lin(z))
    A = pscale(pdiv_exact(QX, X1), GQ(ALPHA + 2 * GG))
    A = padd(A, pscale(pdiv_exact(QX, OMX), GQ(-2 * ETA)))
    A = padd(A, pscale(pmul(X1, pdiv_exact(QX, OPX2)),
                       GQ(-(kap + 2 * ALPHA + 2 * ETA + 2 * GG))))
    if lam != 0:
        A = padd(A, pscale(pmul(X1, pdiv_exact(
            pdiv_exact(QX, OPX2), OPX2)), GQ(-4 * lam)))
    polyt = [GQ(0)]
    for k, l in enumerate(lp, start=1):
        polyt = padd(polyt, pscale(UP[k - 1], GQ(l)))
    A = padd(A, pscale(pmul(polyt, QX), GQ(-2 * kap)))
    for z, r in tp:
        A = padd(A, pscale(pdiv_exact(QX, quad(z)), GQ(-2 * kap) * r * z))
    polyh = [GQ(l) for l in lv]
    A = padd(A, pscale(pmul(polyh, QX), GQ(-1)))
    for z, r in tv:
        A = padd(A, pscale(pdiv_exact(QX, lin(z)), -(r * z)))
    QY = pmul(X1, OMX)
    for z, _ in tv:
        QY = pmul(QY, quad(z))
    Bp = pscale(pdiv_exact(QY, X1), GQ(BETA))
    Bp = padd(Bp, pscale(pdiv_exact(QY, OMX), GQ(-GQ_)))
    polytv = [GQ(0)]
    for k, l in enumerate(lv, start=1):
        polytv = padd(polytv, pscale(UP[k - 1], GQ(l)))
    Bp = padd(Bp, pscale(pmul(polytv, QY), GQ(2)))
    for z, r in tv:
        Bp = padd(Bp, pscale(pdiv_exact(QY, quad(z)), GQ(2) * r * z))
    out = {}
    for name, P, Q in (("X", A, QX), ("Y", Bp, QY)):
        assert all(c.im == 0 for c in P), f"imaginary part in A_{name}"
        assert all(c.im == 0 for c in Q), f"imaginary part in Q_{name}"
        out[name] = ([c.re for c in P], [c.re for c in Q])
    return out


# ------------------------------------------------- root isolation ------
def _isolate01(c0):
    """Isolating intervals for the roots of the integer polynomial c0
    (low-first coefficients) in the OPEN interval (0,1), by Descartes
    variations with dyadic bisection.  Returns a sorted list of
    (lo, hi) Fraction pairs; exact roots appear as lo == hi."""
    out = []
    stack = [(list(c0), Fr(0), Fr(1))]
    while stack:
        c, lo, w = stack.pop()
        # strip factors y (roots at the left end): only interior
        # bisection points count as roots of the open interval
        while len(c) > 1 and c[0] == 0:
            if lo != 0:
                out.append((lo, lo))
            c = c[1:]
        if len(c) <= 1:
            continue
        v = var01(c)
        if v == 0:
            continue
        if v == 1:
            out.append((lo, lo + w))
            continue
        d = len(c) - 1
        left = [c[i] << (d - i) for i in range(d + 1)]   # 2^d P(lo + (w/2) y)
        right = shift_int(left, 1)                       # 2^d P(lo + w/2 + (w/2) y)
        mid = lo + w / 2
        if right[0] == 0:
            out.append((mid, mid))
            right = right[1:]
        stack.append((left, lo, w / 2))
        stack.append((right, mid, w / 2))
    return sorted(out)


def isolate_on(Pint, a):
    """Isolating intervals for the roots of Pint in (a, a+1), a an
    integer (-1 or 0)."""
    c = shift_int(Pint, a)
    ivs = _isolate01(c)
    return [(lo + a, hi + a) for lo, hi in ivs]


def _sgn_at(Pint, x):
    num, den = x.numerator, x.denominator
    d = len(Pint) - 1
    acc = 0
    for i in range(d + 1):
        acc += Pint[i] * num ** i * den ** (d - i)
    return (acc > 0) - (acc < 0)


def refine(Pint, lo, hi, bits=BRACKET_BITS):
    """Refine an isolating interval to width <= 2^-bits with a strict
    sign change; returns (lo, hi, ok).  Degenerate (exact-root)
    intervals pass through."""
    if lo == hi:
        return lo, hi, _sgn_at(Pint, lo) == 0
    slo, shi = _sgn_at(Pint, lo), _sgn_at(Pint, hi)
    if slo * shi >= 0:
        return lo, hi, False
    target = Fr(1, 2 ** bits)
    while hi - lo > target:
        mid = (lo + hi) / 2
        sm = _sgn_at(Pint, mid)
        if sm == 0:
            return mid, mid, True
        if sm == slo:
            lo = mid
        else:
            hi = mid
    return lo, hi, True


# ------------------------------------------------ interval values ------
iv = mpm.iv


def ivq(q):
    """Interval containing the rational q (converted at the current
    interval precision)."""
    q = Fr(q)
    return iv.mpf(q.numerator) / q.denominator


def _hi(v):
    with mpm.workdps(IVDPS + 30):
        return +mpm.mpf(v.b)


def _lo(v):
    with mpm.workdps(IVDPS + 30):
        return +mpm.mpf(v.a)


def _width(v):
    with mpm.workdps(IVDPS + 30):
        return mpm.mpf(v.b) - mpm.mpf(v.a)


class IC:
    """Complex interval: pair of real mpmath intervals."""
    __slots__ = ("re", "im")

    def __init__(self, re, im=None):
        self.re = re
        self.im = iv.mpf(0) if im is None else im

    def __add__(self, o):
        return IC(self.re + o.re, self.im + o.im)

    def __mul__(self, o):
        return IC(self.re * o.re - self.im * o.im,
                  self.re * o.im + self.im * o.re)

    def inv(self):
        d = self.re * self.re + self.im * self.im
        return IC(self.re / d, -self.im / d)

    def log(self):
        return IC(iv.log(self.re * self.re + self.im * self.im) / 2,
                  iv.atan2(self.im, self.re))


def _icq(z):
    return IC(ivq(z.re), ivq(z.im))


LOG2_IV = None


def make_funcs(kap, cert):
    """Interval-valued closed forms X, Y, dX, dY and the norm constant
    NP2 = kappa*||p||_*^2 + ||v||_*^2/2 for one kappa."""
    lp = cert["sequences"]["p"]["finite"]
    lv = cert["sequences"]["v"]["finite"]
    tp = cert["sequences"]["p"]["terms"]
    tv = cert["sequences"]["v"]["terms"]
    lpi = [ivq(l) for l in lp]
    lvi = [ivq(l) for l in lv]
    tpi = [(_icq(z), _icq(r)) for z, r in tp]
    tvi = [(_icq(z), _icq(r)) for z, r in tv]
    lam = ivq(cert["lambda"])
    al, be, gq, gg, et = (ivq(q) for q in (ALPHA, BETA, GQ_, GG, ETA))
    one = iv.mpf(1)
    two = iv.mpf(2)
    half = one / 2

    def T(l, terms, x):
        t0, t1 = one, x
        s = iv.mpf(0)
        for k in range(1, len(l) + 1):
            s += l[k - 1] * t1 / k
            t0, t1 = t1, 2 * x * t1 - t0
        for z, r in terms:
            w = IC(one) + IC(-2 * x) * z + z * z
            s += -half * (r * w.log()).re
        return s

    def S(l, terms, x):
        s = iv.mpf(0)
        xp = one
        for k in range(1, len(l) + 1):
            xp = xp * x
            s += l[k - 1] * xp / k
        for z, r in terms:
            w = IC(one) + IC(-x) * z
            s += -(r * w.log()).re
        return s

    def X(x):
        W = (al + 2 * gg) * iv.log(abs(x)) + 2 * et * iv.log(1 - x) \
            - (iv.mpf(kap) / 2 + al + et + gg) * iv.log(1 + x * x)
        return W + lam * (2 * gg - 2 * x * x / (1 + x * x)) \
            - 2 * kap * T(lpi, tpi, x) - S(lvi, tvi, x)

    def Y(x):
        return be * iv.log(x) + gq * iv.log(1 - x) + 2 * T(lvi, tvi, x)

    def dT(l, terms, x):
        u0, u1 = one, 2 * x
        s = l[0] * u0 if l else iv.mpf(0)
        for k in range(2, len(l) + 1):
            s += l[k - 1] * u1
            u0, u1 = u1, 2 * x * u1 - u0
        for z, r in terms:
            w = IC(one) + IC(-2 * x) * z + z * z
            s += (r * z * w.inv()).re
        return s

    def dS(l, terms, x):
        s = iv.mpf(0)
        xp = one
        for k in range(1, len(l) + 1):
            s += l[k - 1] * xp
            xp = xp * x
        for z, r in terms:
            w = IC(one) + IC(-x) * z
            s += (r * z * w.inv()).re
        return s

    def dX(x):
        return (al + 2 * gg) / x - 2 * et / (1 - x) \
            - (iv.mpf(kap) / 2 + al + et + gg) * 2 * x / (1 + x * x) \
            - lam * 4 * x / ((1 + x * x) * (1 + x * x)) \
            - 2 * kap * dT(lpi, tpi, x) - dS(lvi, tvi, x)

    def dY(x):
        return be / x - gq / (1 - x) + 2 * dT(lvi, tvi, x)

    def norm2(l, terms):
        s = iv.mpf(0)
        for k in range(1, len(l) + 1):
            tk = IC(iv.mpf(0))
            for z, r in terms:
                zk = IC(one)
                for _ in range(k):
                    zk = zk * z
                tk = tk + r * zk
            s += (l[k - 1] * l[k - 1] + 2 * l[k - 1] * tk.re) / k
        for z, r in terms:
            for zz, rr in terms:
                w = IC(one) + IC(-one) * (z * zz)
                s += -((r * rr) * w.log()).re
        return s

    NP2 = kap * norm2(lpi, tpi) + norm2(lvi, tvi) / 2
    return X, Y, dX, dY, NP2


# ------------------------------------------------------- certifying ----
def _sup_enclosure(Pint, F, dF, ranges, endpoint_minus1):
    """Two-sided enclosure of sup F on the union of the open ranges
    (plus the point -1 for X).  Returns (sup_lo, sup_hi, n_crit,
    max_allowance, max_width, all_refine_ok) with mpf endpoints."""
    sup_lo = None
    sup_hi = None
    n_crit = 0
    max_allow = mpm.mpf(0)
    max_width = mpm.mpf(0)
    ok_all = True

    def consider_point(x_iv, allowance):
        nonlocal sup_lo, sup_hi, max_width
        v = F(x_iv)
        max_width = max(max_width, _width(v))
        lo_v = _lo(v)
        hi_v = _hi(v) + _hi(allowance)
        sup_lo = lo_v if sup_lo is None else max(sup_lo, lo_v)
        sup_hi = hi_v if sup_hi is None else max(sup_hi, hi_v)

    if endpoint_minus1:
        consider_point(iv.mpf(-1), iv.mpf(0))
    for a, b in ranges:
        for blo, bhi in isolate_on(Pint, a):
            blo, bhi, ok = refine(Pint, blo, bhi)
            ok_all = ok_all and ok
            n_crit += 1
            w = bhi - blo
            if w == 0:
                consider_point(ivq(blo), iv.mpf(0))
            else:
                d = dF(iv.mpf([ivq(blo).a, ivq(bhi).b]))
                allow = ivq(w) * iv.mpf(max(abs(d.a), abs(d.b)))
                max_allow = max(max_allow, _hi(allow))
                consider_point(ivq(blo), allow)
    return sup_lo, sup_hi, n_crit, max_allow, max_width, ok_all


def certify_kappa(kap, cert, D, grid_check=True, c2_check=True):
    """Full rigorous certificate for one (witness, kappa).  Returns a
    result dict of mpf endpoints / strings plus gate booleans."""
    t0 = time.time()
    NUM = build_numerators(kap, cert, D)
    degs = {k: (len(NUM[k][0]) - 1, len(NUM[k][1]) - 1) for k in NUM}
    iv.dps = IVDPS
    mpm.mp.dps = IVDPS + 30
    X, Y, dX, dY, NP2 = make_funcs(kap, cert)
    log2 = iv.log(iv.mpf(2))
    res = {"kappa": kap, "degrees": degs, "gates": {}}
    sup = {}
    for name, F, dF, ranges, ep in (
            ("X", X, dX, [(-1, 0), (0, 1)], True),
            ("Y", Y, dY, [(0, 1)], False)):
        Pint, _ = to_int_poly(NUM[name][0])
        lo_, hi_, nc, allow, width, ok = _sup_enclosure(
            Pint, F, dF, ranges, ep)
        sup[name] = (lo_, hi_)
        res[f"sup{name}_lo"] = lo_
        res[f"sup{name}_hi"] = hi_
        res[f"ncrit_{name}"] = nc
        res[f"max_allow_{name}"] = allow
        res[f"max_width_{name}"] = width
        res["gates"][f"C3_{name}"] = ok
    res["NP2_lo"] = _lo(NP2)
    res["NP2_hi"] = _hi(NP2)
    res["NP2_width"] = _width(NP2)
    # U interval: (-1+alpha+gg) log2 + NP2 + supX + supY, endpoints
    # combined with directed rounding at elevated precision.
    with mpm.workdps(IVDPS + 30):
        _c = -1 + ALPHA + GG  # exact rational, negative
        c = mpm.mpf(_c.numerator) / _c.denominator
        l2lo, l2hi = _lo(log2), _hi(log2)
        Ulo = c * l2hi + res["NP2_lo"] + sup["X"][0] + sup["Y"][0]
        Uhi = c * l2lo + res["NP2_hi"] + sup["X"][1] + sup["Y"][1]
    res["U_lo"] = Ulo
    res["U_hi"] = Uhi
    res["Sigma_lo"] = sup["X"][0] + sup["Y"][0]
    res["Sigma_hi"] = sup["X"][1] + sup["Y"][1]
    res["gates"]["C4_widths"] = bool(
        res["max_width_X"] < mpm.mpf("1e-30")
        and res["max_width_Y"] < mpm.mpf("1e-30")
        and res["NP2_width"] < mpm.mpf("1e-30"))
    res["gates"]["C4_allowances"] = bool(
        res["max_allow_X"] < mpm.mpf("1e-9")
        and res["max_allow_Y"] < mpm.mpf("1e-9"))
    if grid_check:
        res["grid"] = _grid_control(kap, cert, sup)
        res["gates"]["C5_grid"] = bool(res["grid"]["ok"])
    if c2_check:
        w1, w2 = derivative_check(kap, cert, NUM)
        res["C2_worst_numdiff"] = w1
        res["C2_worst_closed"] = w2
        res["gates"]["C2_numdiff"] = bool(w1 < mpm.mpf("1e-25"))
        res["gates"]["C2_closed"] = bool(w2 < mpm.mpf("1e-35"))
    res["seconds"] = time.time() - t0
    return res


def _grid_control(kap, cert, sup):
    """Dense float grid (numpy) vs the certified suprema."""
    import numpy as np
    lp = cert["sequences"]["p"]["finite"]
    lv = cert["sequences"]["v"]["finite"]
    tp = cert["sequences"]["p"]["terms"]
    tv = cert["sequences"]["v"]["terms"]
    lam = float(cert["lambda"])
    al, be, gq, gg, et = (float(t) for t in (ALPHA, BETA, GQ_, GG, ETA))

    def Tf(l, terms, x):
        t0, t1 = np.ones_like(x), x.copy()
        s = np.zeros_like(x)
        for k in range(1, len(l) + 1):
            s += float(l[k - 1]) * t1 / k
            t0, t1 = t1, 2 * x * t1 - t0
        for z, r in terms:
            zc = complex(float(z.re), float(z.im))
            rc = complex(float(r.re), float(r.im))
            s += (-0.5 * rc * np.log(1 - 2 * x * zc + zc * zc + 0j)).real
        return s

    def Sf(l, terms, x):
        s = np.zeros_like(x)
        for k in range(1, len(l) + 1):
            s += float(l[k - 1]) * x ** k / k
        for z, r in terms:
            zc = complex(float(z.re), float(z.im))
            rc = complex(float(r.re), float(r.im))
            s += (-rc * np.log(1 - x * zc + 0j)).real
        return s

    N = 200000
    xs = np.cos(np.linspace(0, np.pi, N + 2)[1:-1])
    xs = xs[np.abs(xs) > 1e-7]
    ss = (1 - np.cos(np.linspace(0, np.pi, N + 2)[1:-1])) / 2
    Xg = (al + 2 * gg) * np.log(np.abs(xs)) + 2 * et * np.log(1 - xs) \
        - (kap / 2 + al + et + gg) * np.log(1 + xs * xs) \
        + lam * (2 * gg - 2 * xs * xs / (1 + xs * xs)) \
        - 2 * kap * Tf(lp, tp, xs) - Sf(lv, tv, xs)
    Yg = be * np.log(ss) + gq * np.log(1 - ss) + 2 * Tf(lv, tv, ss)
    gx, gy = float(Xg.max()), float(Yg.max())
    ok = (gx <= float(sup["X"][1]) + 1e-12
          and float(sup["X"][1]) <= gx + 1e-6
          and gy <= float(sup["Y"][1]) + 1e-12
          and float(sup["Y"][1]) <= gy + 1e-6)
    return {"grid_max_X": gx, "grid_max_Y": gy, "ok": ok}


# ------------------------------------------------- C2 cross-check ------
def _plain_funcs(kap, cert):
    """Plain (non-interval) high-precision closed forms X, Y, dX, dY,
    written independently of the interval versions above; used only
    for the C2 derivative cross-checks."""
    lp = cert["sequences"]["p"]["finite"]
    lv = cert["sequences"]["v"]["finite"]
    tp = cert["sequences"]["p"]["terms"]
    tv = cert["sequences"]["v"]["terms"]
    lam = mpm.mpf(cert["lambda"].numerator) / cert["lambda"].denominator

    def q2m(q):
        return mpm.mpf(q.numerator) / q.denominator

    def z2m(z):
        return mpm.mpc(q2m(z.re), q2m(z.im))

    al, be, gq, gg, et = (q2m(t) for t in (ALPHA, BETA, GQ_, GG, ETA))
    tpz = [(z2m(z), z2m(r)) for z, r in tp]
    tvz = [(z2m(z), z2m(r)) for z, r in tv]
    lpf = [q2m(l) for l in lp]
    lvf = [q2m(l) for l in lv]

    def T(l, terms, x):
        t0, t1 = mpm.mpf(1), x
        s = mpm.mpf(0)
        for k in range(1, len(l) + 1):
            s += l[k - 1] * t1 / k
            t0, t1 = t1, 2 * x * t1 - t0
        for z, r in terms:
            s += (-r * mpm.log(1 - 2 * x * z + z * z) / 2).real
        return s

    def S(l, terms, x):
        s = mpm.mpf(0)
        for k in range(1, len(l) + 1):
            s += l[k - 1] * x ** k / k
        for z, r in terms:
            s += (-r * mpm.log(1 - x * z)).real
        return s

    def X(x):
        return (al + 2 * gg) * mpm.log(abs(x)) + 2 * et * mpm.log(1 - x) \
            - (kap / 2 + al + et + gg) * mpm.log(1 + x * x) \
            + lam * (2 * gg - 2 * x * x / (1 + x * x)) \
            - 2 * kap * T(lpf, tpz, x) - S(lvf, tvz, x)

    def Y(x):
        return be * mpm.log(x) + gq * mpm.log(1 - x) + 2 * T(lvf, tvz, x)

    def dT(l, terms, x):
        u0, u1 = mpm.mpf(1), 2 * x
        s = l[0] * u0 if l else mpm.mpf(0)
        for k in range(2, len(l) + 1):
            s += l[k - 1] * u1
            u0, u1 = u1, 2 * x * u1 - u0
        for z, r in terms:
            s += (r * z / (1 - 2 * x * z + z * z)).real
        return s

    def dS(l, terms, x):
        s = mpm.mpf(0)
        for k in range(1, len(l) + 1):
            s += l[k - 1] * x ** (k - 1)
        for z, r in terms:
            s += (r * z / (1 - x * z)).real
        return s

    def dX(x):
        return (al + 2 * gg) / x - 2 * et / (1 - x) \
            - (kap / 2 + al + et + gg) * 2 * x / (1 + x * x) \
            - lam * 4 * x / (1 + x * x) ** 2 \
            - 2 * kap * dT(lpf, tpz, x) - dS(lvf, tvz, x)

    def dY(x):
        return be / x - gq / (1 - x) + 2 * dT(lvf, tvz, x)

    return X, Y, dX, dY


def derivative_check(kap, cert, NUM):
    """C2: exact A/Q against (i) mpmath numerical differentiation of
    the closed forms, (ii) the closed-form derivatives, at 5 points
    per function.  Returns (worst_rel_numdiff, worst_rel_closed)."""
    X, Y, dX, dY = _plain_funcs(kap, cert)
    worst1 = mpm.mpf(0)
    worst2 = mpm.mpf(0)
    with mpm.workdps(150):
        Xh, Yh, dXh, dYh = _plain_funcs(kap, cert)
        pts = {"X": ["-0.73", "-0.21", "0.17", "0.52", "0.91"],
               "Y": ["0.07", "0.33", "0.5", "0.68", "0.97"]}
        F = {"X": Xh, "Y": Yh}
        dF = {"X": dXh, "Y": dYh}
        for name in ("X", "Y"):
            P, Q = NUM[name]
            for st in pts[name]:
                x = Fr(st)
                e = peval_fr(P, x) / peval_fr(Q, x)
                exact = mpm.mpf(e.numerator) / e.denominator
                xm = mpm.mpf(x.numerator) / x.denominator
                with mpm.workdps(40):
                    num = mpm.diff(lambda t: F[name](t), xm)
                rel1 = abs(exact - num) / max(abs(num), mpm.mpf(1))
                cf = dF[name](xm)
                rel2 = abs(exact - cf) / max(abs(cf), mpm.mpf(1))
                worst1 = max(worst1, rel1)
                worst2 = max(worst2, rel2)
    return worst1, worst2
