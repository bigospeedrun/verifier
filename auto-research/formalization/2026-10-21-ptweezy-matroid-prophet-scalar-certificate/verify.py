#!/usr/bin/env python3
"""Exact checks for the matroid prophet Appendix A scalar certificate.

Standard library only. Recomputes, in exact rational arithmetic and
starting only from the paper's parameter list (Appendix A of
Chen--Euler, "An Exact Rational Certificate for One-Sample Matroid
Prophet Inequalities", problems/bound-111/paper.pdf at commit
b3c7abea0d5e392777498816ca837eded8b85669):

  * the derived values p, gamma, epsilon, a0, A;
  * the conditions (4) over Q: 0 < gamma <= rho/4 and
    (1-t)(gamma*kappa + a0)/K <= 1/4;
  * s(141), C(140) (Shea's C_star), C(141) (the record C141), the exact
    gain and relative gain, and C141 > 2^-293;
  * B = (261/256)^256 > 141 as an exact fraction, s(B) > 0,
    C(B) > C(141), and the identity behind (5):
    (1-t) beta^2 t s(B) / (L (theta-1) K) == C(B);
  * the rational forms of the tilt inequalities (eq. 31):
    A^8 p^105 < (a v)^8 and (1-p)^8 p^113 < (b v)^8;
  * the paper's rational atanh check d < S4 (eq. 32, left half);
and checks that the packaged Lean file states the headline theorems,
contains no sorry/admit, and that the recorded build log shows success
and exactly the allowed axioms for the five printed theorems. The
real-number statements themselves (the tilts over R and d < -log p)
are proved in Lean (code/MatroidScalar.lean); this script does not
replace that proof.
"""
import pathlib
import sys
from fractions import Fraction as F

here = pathlib.Path(__file__).resolve().parent
failures = []


def check(name, cond):
    print(("ok   " if cond else "FAIL ") + name)
    if not cond:
        failures.append(name)


# --- the paper's parameters (Appendix A) ---
kappa = F(164)
rho = F(93, 256)
h = F(3, 4)
t = F(23, 262144)
theta = F(261, 256)
L = F(256)
mu = F(105, 8)
nu = F(113, 8)
a = F(1, 864)
b = F(1, 4000)
v = F(1, 624)
d = F(253, 250)

# --- derived quantities, exactly as defined in the paper ---
K = kappa + nu
p = rho + (1 - rho) * t
bY = ((F(2, 3)) * a * (1 / rho - 1) + b) / (1 + a) + 2 * v
gamma = rho / 4 - bY / d
eps = mu * rho / kappa + a / d
a0 = 1 / d
Rc = K * t + K * rho / kappa
A = rho * (3 + 4 * v / 3)


def loss(x):
    x = F(x)
    return eps + K * t + Rc / (x - 1)


def s(x):
    x = F(x)
    return (1 - h) * (gamma - loss(x) / h)


def C(x):
    x = F(x)
    return (1 - t) * ((x - 1) / x) ** 2 * t * s(x) / (5 * K)


C141 = F(165971304277649481670619, 324956758716416046811841770291200)
Cstar = F(4084754449786906742230661, 8009094702029267287249256448000000)

check("p == 24383141/67108864", p == F(24383141, 67108864))
check("K == 1425/8", K == F(1425, 8))
check("gamma == 69959099203/812800834560", gamma == F(69959099203, 812800834560))
check("epsilon == 69328715/2294341632", eps == F(69328715, 2294341632))
check("a0 == 250/253", a0 == F(250, 253))
check("A == 130665/119808", A == F(130665, 119808))
check("0 < gamma <= rho/4 (condition (4))", 0 < gamma <= rho / 4)
check("(1-t)(gamma*kappa + a0)/K <= 1/4 (condition (4))",
      (1 - t) * (gamma * kappa + a0) / K <= F(1, 4))
check("R = Kt + K rho/kappa > 0", Rc > 0)
check("p > (3/4)^4 (so p^(1/4) > 3/4)", p > F(3, 4) ** 4)

check("s(141) == 3932831273804099/747774506088529920",
      s(141) == F(3932831273804099, 747774506088529920))
check("s(141) > 0", s(141) > 0)
check("C(140) == Shea's C_star", C(140) == Cstar)
check("C(141) == C141 (the record)", C(141) == C141)
check("C(141) - C(140) == 116935879834753076315538659/"
      "159228811771043862937802467442688000000",
      C(141) - C(140)
      == F(116935879834753076315538659, 159228811771043862937802467442688000000))
check("C(141)/C(140) - 1 == 19396266184195562573/13470215002963864007427",
      C(141) / C(140) - 1 == F(19396266184195562573, 13470215002963864007427))
check("C141 > 2^-293", F(1, 2) ** 293 < C141)
check("5.107e-10 < C141 < 5.108e-10", F(5107, 10 ** 13) < C141 < F(5108, 10 ** 13))
check("s and C strictly increase at 141 < 200 < 1000 (spot values)",
      s(141) < s(200) < s(1000) and C(141) < C(200) < C(1000))

B = theta ** 256
beta = (B - 1) / B
check("B = (261/256)^256 > 141 (exact)", B > 141)
check("L (theta - 1) == 5", L * (theta - 1) == 5)
check("s(B) > 0 (exact)", s(B) > 0)
check("C(B) > C(141) (exact)", C(B) > C(141))
check("(5) identity: (1-t) beta^2 t s(B) / (L (theta-1) K) == C(B)",
      (1 - t) * beta ** 2 * t * s(B) / (L * (theta - 1) * K) == C(B))

check("tilt 1 rational form: A^8 p^105 < (a v)^8", A ** 8 * p ** 105 < (a * v) ** 8)
check("tilt 2 rational form: (1-p)^8 p^113 < (b v)^8",
      (1 - p) ** 8 * p ** 113 < (b * v) ** 8)

zeta = (1 - p) / (1 + p)
S4 = 2 * (zeta + zeta ** 3 / 3 + zeta ** 5 / 5 + zeta ** 7 / 7)
check("d < S4 (paper's eq. (32), rational half)", d < S4)
check("S4 < 1.0122 (sanity band)", S4 < F(10122, 10000))

lean_src = (here / "code" / "MatroidScalar.lean").read_text()
check("MatroidScalar.lean states appendixA_certificate",
      "theorem appendixA_certificate" in lean_src)
check("MatroidScalar.lean states constant_bound (eq. (5))",
      "theorem constant_bound" in lean_src)
check("MatroidScalar.lean states tilt_one and tilt_two",
      "theorem tilt_one" in lean_src and "theorem tilt_two" in lean_src)
check("MatroidScalar.lean states d_lt_neg_log_p",
      "theorem d_lt_neg_log_p" in lean_src)
check("MatroidScalar.lean has no sorry/admit",
      "sorry" not in lean_src and "admit" not in lean_src)

log = (here / "evidence" / "lean-build.log").read_text()
check("recorded lake build succeeded",
      "Build completed successfully" in log and "LAKE_EXIT:0" in log)
for thm in ["appendixA_certificate", "constant_bound", "CCurve141_value",
            "CCurve141_gt", "d_lt_S4"]:
    check(f"axioms of {thm} are exactly the allowed set",
          f"'MatroidProphet.{thm}' depends on axioms: "
          "[propext, Classical.choice, Quot.sound]" in log)

if failures:
    print(f"FAIL: {len(failures)} check(s) failed")
    sys.exit(1)
print("PASS")
