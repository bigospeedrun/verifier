#!/usr/bin/env python3
"""Exact sanity checks for the van der Waerden norm-band lemma package.

Standard library only. These checks are finite, exact (rational)
sanity checks of the arithmetic core of Lemma `lem:band` from DaysSky's
research note (`research-note.tex`, section "A sharper norm-band
multiplicity", in DaysSky/van-der-waerden-refinement at commit
54ac9715fceab938ca77d5980c36ab691765a04d):

  * the note's key step: for two parameters in one sign class
    ((-inf, 0) or [0, inf)) separated by at least 1, writing their
    absolute values as u <= v one has v^2 - u^2 = (v - u)(v + u) >= 1;
    checked as an exact identity and inequality on a grid of
    fractions, including the boundary cases (separation exactly 1,
    u = 0, both negative);
  * the band width fact: two rationals in one half-open interval
    [m, m+1) differ by less than 1;
  * the lemma itself, exhaustively, on the finite grid of parameters
    {k/2 : -6 <= k <= 6}: no three pairwise >= 1 apart grid points
    have all squares in one half-open unit band;

and package integrity checks: the packaged Lean file states the four
headline theorems, contains no sorry/admit/native_decide, and the
recorded build log shows success and exactly the allowed axioms for
each printed theorem. The proof itself is the Lean file
(code/BandLemma.lean); these finite checks do not replace it.
"""
import itertools
import pathlib
import sys
from fractions import Fraction as F

here = pathlib.Path(__file__).resolve().parent
failures = []


def check(name, cond):
    print(("ok   " if cond else "FAIL ") + name)
    if not cond:
        failures.append(name)


def same_class(u, v):
    return (0 <= u and 0 <= v) or (u < 0 and v < 0)


# --- the key step, on an exact grid including boundary cases ---
grid4 = [F(k, 4) for k in range(-16, 17)]
ident_ok = True
ineq_ok = True
for u, v in itertools.product(grid4, repeat=2):
    if same_class(u, v) and abs(u - v) >= 1:
        lo, hi = min(abs(u), abs(v)), max(abs(u), abs(v))
        if (hi - lo) * (hi + lo) != hi * hi - lo * lo:
            ident_ok = False
        if not (hi * hi - lo * lo >= 1 and abs(u * u - v * v) >= 1):
            ineq_ok = False
check("key step identity: (v-u)(v+u) == v^2-u^2 (exact, sign-class grid)",
      ident_ok)
check("key step: same class, |u-v| >= 1  =>  |u^2-v^2| >= 1 (exact)",
      ineq_ok)
check("key step boundary: u=0, v=1 gives v^2-u^2 == 1",
      F(1) ** 2 - F(0) ** 2 == 1)
check("key step boundary: u=-1, v=-2 (both negative) gives |u^2-v^2| == 3",
      abs(F(-1) ** 2 - F(-2) ** 2) == 3)

# --- the band width fact ---
width_ok = True
for m in [F(-1), F(0), F(1, 2), F(3), F(17, 3)]:
    inside = [x for x in grid4 if m <= x < m + 1]
    for p, q in itertools.product(inside, repeat=2):
        if not abs(p - q) < 1:
            width_ok = False
check("band width: p, q in [m, m+1)  =>  |p-q| < 1 (exact)", width_ok)

# --- the lemma itself, exhaustively on a finite parameter grid ---
grid2 = [F(k, 2) for k in range(-6, 7)]
bands = [F(j, 2) for j in range(-2, 19)]
counterexample = None
for triple in itertools.combinations(grid2, 3):
    if all(abs(a - b) >= 1 for a, b in itertools.combinations(triple, 2)):
        for m in bands:
            if all(m <= t * t < m + 1 for t in triple):
                counterexample = (triple, m)
check("lemma on grid {k/2}: no 3 pairwise >=1 apart points share a band",
      counterexample is None)

# --- the pair step is exactly what fails for mixed signs (sanity) ---
check("mixed signs can share a band (sign hypothesis is needed): "
      "(-1)^2 == 1^2", F(-1) ** 2 == F(1) ** 2)

lean_src = (here / "code" / "BandLemma.lean").read_text()
for thm in ["card_le_two_of_band", "band_three_points",
            "band_card_le_two", "points_band_card_le_two"]:
    check(f"BandLemma.lean states {thm}", f"theorem {thm}" in lean_src)
check("BandLemma.lean has no sorry/admit/native_decide",
      "sorry" not in lean_src and "admit" not in lean_src
      and "native_decide" not in lean_src)

log = (here / "evidence" / "lean-build.log").read_text()
check("recorded lake build succeeded",
      "Build completed successfully" in log and "LAKE_EXIT:0" in log)
for thm in ["card_le_two_of_band", "band_three_points",
            "band_card_le_two", "points_band_card_le_two"]:
    check(f"axioms of {thm} are exactly the allowed set",
          f"'VanDerWaerden.{thm}' depends on axioms: "
          "[propext, Classical.choice, Quot.sound]" in log)

if failures:
    print(f"FAIL: {len(failures)} check(s) failed")
    sys.exit(1)
print("PASS")
