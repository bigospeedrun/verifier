"""
assemble.py -- final assembly (link L6): from the rigorous per-kappa
enclosures to the exponent bound, in interval arithmetic throughout.

Written formulas (Carreira, Corollary xcor:massminors applied with the
design's parameters as in the claimant's Theorem 35 instantiation, and
Theorem xthm:exponent):
    rho1 = (2 - alpha - gamma_g) log 2 - Sigma_2 + 2 log 2
           -- an UPPER bound on rho1 is required; Sigma_2 is therefore
              used at its certified LOWER bound.
    second case coefficient
         = (2 - alpha - gamma_g) log 2 - Sigma_1
           - lambda^(1) (1 - 2 gamma_g) + (3/2) log 2
           -- must be <= rho1 (case 1 dominates on [0,1]); also the
              constant term uses U_1 - U_2 <= 0.
    rho2 = rho1 + (eta + gamma_q) log 2 + (1 - gamma_g) log(1 + sqrt 2)
    mu(G) <= rho2 * ((1 - gamma_g) + n0 gamma) / gamma,
    gamma = the certified (C4) margin F_low - max(U_1, U_2) > 0, used
    at its certified LOWER bound (mu decreases as gamma grows).

All inputs are the audit's own rigorous enclosures (mpf endpoints
extracted at 90 digits from 60-digit interval arithmetic); the final
combinations are done with explicit directed rounding at 90 digits so
the reported mu_hi is a rigorous upper bound for the assembled value.
"""
from fractions import Fraction as Fr

import mpmath as mpm

DES = (36, 6, 2, 3, 2)
_n0, _b0, _q0, _g0, _h0 = DES
ALPHA = Fr(_b0 + _q0, _n0)     # 2/9
GG = Fr(_g0, _n0)              # 1/12
GQ_ = Fr(_q0, _n0)             # 1/18
ETA = Fr(_h0, _n0)             # 1/18
NU = 1 - GG                    # 11/12

DPS = 90


def _q(q):
    q = Fr(q)
    return mpm.mpf(q.numerator) / q.denominator


def assemble(f_low_lo, f_low_hi, U, Sigma, lambda1):
    """U: {2: (U_lo, U_hi), 1: (U_lo, U_hi)} mpf endpoints;
    Sigma: {2: (lo, hi), 1: (lo, hi)}; lambda1 exact Fraction.
    f_low endpoints mpf.  Returns a dict of mpf values + booleans."""
    with mpm.workdps(DPS):
        log2 = mpm.log(2)
        logs = mpm.log(1 + mpm.sqrt(2))
        c_main = _q(2 - ALPHA - GG)              # 61/36 > 0
        gamma_lo = f_low_lo - max(U[2][1], U[1][1])
        gamma_hi = f_low_hi - max(U[2][0], U[1][0])
        rho1_hi = c_main * log2 - Sigma[2][0] + 2 * log2
        rho1_lo = c_main * log2 - Sigma[2][1] + 2 * log2
        lam = _q(lambda1)
        second_hi = c_main * log2 - Sigma[1][0] \
            - lam * _q(1 - 2 * GG) + mpm.mpf(3) / 2 * log2
        second_lo = c_main * log2 - Sigma[1][1] \
            - lam * _q(1 - 2 * GG) + mpm.mpf(3) / 2 * log2
        dominance_ok = bool(second_hi <= rho1_lo)
        U1_minus_U2_hi = U[1][1] - U[2][0]
        rho2_hi = rho1_hi + _q(ETA + GQ_) * log2 + _q(NU) * logs
        rho2_lo = rho1_lo + _q(ETA + GQ_) * log2 + _q(NU) * logs
        # mu decreases in gamma: use gamma_lo for the upper bound.
        mu_hi = rho2_hi * (_q(NU) / gamma_lo + _n0)
        mu_lo = rho2_lo * (_q(NU) / gamma_hi + _n0)
        return {
            "gamma_lo": gamma_lo, "gamma_hi": gamma_hi,
            "rho1_lo": rho1_lo, "rho1_hi": rho1_hi,
            "second_lo": second_lo, "second_hi": second_hi,
            "dominance_ok": dominance_ok,
            "U1_minus_U2_hi": U1_minus_U2_hi,
            "rho2_lo": rho2_lo, "rho2_hi": rho2_hi,
            "mu_lo": mu_lo, "mu_hi": mu_hi,
            "claim_2401_741": bool(mu_hi < mpm.mpf("2401.741")),
        }
