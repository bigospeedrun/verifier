"""
flow.py -- exact integral of the loss function D_L and the lower
constant F_low, for a design (n0, b0, q0, g0, h0).

Definitions (Carreira, def:loss and the F_low display):
  a = b+q, L = n+a, C = L+g, H = C+h, A = a+2g  (unit design values)
  d0(x)  = pos( min(x, L-x, A) - max(b, H-2x) )
  Rl(x)  = pos(K) + pos(K-A) + pos(J - max(b, K)),   K = L-x, J = H-x
  Sl(x)  = pos( min(A, K) - b ) + pos( min(b, J) - max(0, K) )
  D_L(x) = 2n - pos(d0(x) - q)          for 0 <= x <= H/2
         = min(2n, n + Rl, 2 Rl + Sl)   for H/2 < x <= H
  F_low  = -(1/n^2) * int_0^H D_L  - (1/2 + d/2 + d^2/8) * log 2,
           d = (q+g+h)/n.

Independent integration method (not the claimant's recursive sampler):
  D_L is built from a finite set of atomic linear forms.  All pairwise
  crossings of those forms (and their q-shifts, which is where the
  d0 = q level set comes from) split [0, H] into elementary intervals
  on which every comparison inside the definition has constant sign.
  On each elementary interval the branch structure is determined by
  exact evaluation at the midpoint, the exact linear form of D_L is
  constructed, the interval is split once more at the crossings of the
  (at most three) candidate linear forms, and each final piece is
  integrated in closed form.  Every piece is verified by exact
  evaluation of D_L at three interior points against the linear form.
"""
from fractions import Fraction as Fr

import qx  # noqa: F401  (keeps sys.path handling uniform)


def derived(des):
    n, b, q, g, h = des
    a = b + q
    L = n + a
    C = L + g
    H = C + h
    A = a + 2 * g
    return a, L, C, H, A


def _pos(y):
    return y if y > 0 else Fr(0)


def D_of_x(x, des):
    """Exact D_L(x) for rational x (direct transcription of def:loss)."""
    n, b, q, g, h = des
    a, L, C, H, A = derived(des)
    x = Fr(x)
    if 2 * x <= H:
        d0 = _pos(min(x, L - x, Fr(A)) - max(Fr(b), H - 2 * x))
        return 2 * n - _pos(d0 - q)
    K, J = L - x, H - x
    R = _pos(K) + _pos(K - A) + _pos(J - max(Fr(b), K))
    S = _pos(min(Fr(A), K) - b) + _pos(min(Fr(b), J) - max(Fr(0), K))
    return min(Fr(2 * n), n + R, 2 * R + S)


def _atomic_forms(des):
    """All linear forms (slope, intercept) compared anywhere in D_L,
    plus their q-shifts.  A form is value = slope*x + intercept."""
    n, b, q, g, h = des
    a, L, C, H, A = derived(des)
    F = [(1, 0),      # x
         (-1, L),     # L - x = K
         (0, A),      # A
         (0, b),      # b
         (-2, H),     # H - 2x
         (-1, L - A),  # K - A
         (-1, H),     # J = H - x
         (-1, H - b),  # J - b
         (-1, L - b),  # K - b
         (0, 0)]      # 0
    F = F + [(s, c - q) for (s, c) in F]  # q-shifted copies (level sets)
    return F


def _crossings(forms, lo, hi):
    pts = {Fr(lo), Fr(hi)}
    for i in range(len(forms)):
        for j in range(i + 1, len(forms)):
            s1, c1 = forms[i]
            s2, c2 = forms[j]
            if s1 != s2:
                x = Fr(c2 - c1, s1 - s2)
                if lo <= x <= hi:
                    pts.add(x)
    return sorted(pts)


def _lin(slope, intercept):
    return (Fr(slope), Fr(intercept))


def _lin_eval(f, x):
    return f[0] * x + f[1]


def _lin_add(f1, f2):
    return (f1[0] + f2[0], f1[1] + f2[1])


def _lin_sub(f1, f2):
    return (f1[0] - f2[0], f1[1] - f2[1])


def _lin_scale(f, s):
    return (f[0] * s, f[1] * s)


def _branch_forms(mid, des):
    """Exact linear forms of d0, Rl, Sl on an elementary interval whose
    branch structure is read off at the rational midpoint `mid`."""
    n, b, q, g, h = des
    a, L, C, H, A = derived(des)
    X = _lin(1, 0)
    ZERO = _lin(0, 0)

    def val(f):
        return _lin_eval(f, mid)

    def pick_min(forms):
        return min(forms, key=val)

    def pick_max(forms):
        return max(forms, key=val)

    def posf(f):
        return f if val(f) > 0 else ZERO

    Lf = _lin(-1, L)          # K = L - x
    Jf = _lin(-1, H)          # J = H - x
    Af = _lin(0, A)
    bf = _lin(0, b)
    # d0
    mn = pick_min([X, Lf, Af])
    mx = pick_max([bf, _lin(-2, H)])
    d0 = posf(_lin_sub(mn, mx))
    # Rl
    R = _lin_add(_lin_add(posf(Lf), posf(_lin_sub(Lf, Af))),
                 posf(_lin_sub(Jf, pick_max([bf, Lf]))))
    # Sl
    S = _lin_add(posf(_lin_sub(pick_min([Af, Lf]), bf)),
                 posf(_lin_sub(pick_min([bf, Jf]),
                               pick_max([ZERO, Lf]))))
    return d0, R, S


def integrate_D(des):
    """Exact integral of D_L over [0, H]; returns (Fraction, stats)."""
    n, b, q, g, h = des
    a, L, C, H, A = derived(des)
    forms = _atomic_forms(des)
    total = Fr(0)
    pieces = 0
    checked = 0
    # elementary intervals, split at H/2 (the branch point)
    cuts = _crossings(forms, 0, H)
    if Fr(H, 2) not in cuts:
        cuts = sorted(cuts + [Fr(H, 2)])
    for lo, hi in zip(cuts, cuts[1:]):
        if lo == hi:
            continue
        mid = (lo + hi) / 2
        d0, R, S = _branch_forms(mid, des)
        if 2 * mid <= H:
            cands = [(_lin(0, 2 * n), "2n"),
                     (_lin_sub(_lin(0, 2 * n), _lin_sub(d0, _lin(0, q))),
                      "2n-(d0-q)")]
            # D = 2n - pos(d0 - q): candidates 2n and 2n-(d0-q)
            cand_forms = [_lin(0, 2 * n),
                          _lin_sub(_lin(0, 2 * n), _lin_sub(d0, _lin(0, q)))]
        else:
            cand_forms = [_lin(0, 2 * n),
                          _lin_add(_lin(0, n), R),
                          _lin_add(_lin_scale(R, 2), S)]
        # split at mutual crossings of the candidates
        sub = {lo, hi}
        for i in range(len(cand_forms)):
            for j in range(i + 1, len(cand_forms)):
                s1, c1 = cand_forms[i]
                s2, c2 = cand_forms[j]
                if s1 != s2:
                    x = (c2 - c1) / (s1 - s2)
                    if lo < x < hi:
                        sub.add(x)
        sub = sorted(sub)
        for slo, shi in zip(sub, sub[1:]):
            if slo == shi:
                continue
            smid = (slo + shi) / 2
            Df = min(cand_forms, key=lambda f: _lin_eval(f, smid))
            # verify the linear form against the direct definition at
            # three interior rational points
            for t in (Fr(1, 4), Fr(1, 2), Fr(3, 4)):
                x = slo + (shi - slo) * t
                assert D_of_x(x, des) == _lin_eval(Df, x), \
                    f"D form mismatch on piece ({slo},{shi}) of {des}"
                checked += 1
            # exact integral of the linear form
            total += Df[0] * (shi * shi - slo * slo) / 2 \
                + Df[1] * (shi - slo)
            pieces += 1
    return total, {"pieces": pieces, "point_checks": checked,
                   "elementary_intervals": len(cuts) - 1}


def f_low_parts(des):
    """Returns (integral_D, delta, rational_part, log2_coeff) with
    F_low = rational_part - log2_coeff * log 2."""
    n, b, q, g, h = des
    I, stats = integrate_D(des)
    delta = Fr(q + g + h, n)
    rat = -I / (n * n)
    coeff = Fr(1, 2) + delta / 2 + delta * delta / 8
    return I, delta, rat, coeff, stats


if __name__ == "__main__":
    import time
    for des, expect in [((48, 7, 4, 4, 2), Fr(8609, 2)),
                        ((96, 15, 6, 8, 5), Fr(17114)),
                        ((36, 6, 2, 3, 2), Fr(4825, 2))]:
        t0 = time.time()
        I, stats = integrate_D(des)
        print(des, "integral =", I, "expected", expect,
              "OK" if I == expect else "MISMATCH",
              stats, f"{time.time()-t0:.2f}s")
