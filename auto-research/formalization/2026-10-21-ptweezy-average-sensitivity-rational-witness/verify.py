#!/usr/bin/env python3
"""Exact checks for the average-sensitivity Section 7 rational witness.

Standard library only. Checks, in exact rational arithmetic:
  * the paper's arctan Taylor sum equals 1538665/489888 (times 4),
  * that value exceeds 500000/159201 by exactly 206455/1237946976,
  * 500000/159201 == 32 / (399/125)^2  (so pi > 500000/159201 suffices
    for 8/sqrt(2 pi) < 399/125, the step the Lean proof formalizes),
  * the comparison chain gaps 319/500 and 601/125,
and that the packaged Lean file states the theorems, contains no
sorry/admit, and that the recorded build log shows exactly the allowed
axioms. The real-number inequality itself is proved in Lean
(code/Cert.lean); this script does not replace that proof.
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


def taylor7(x):
    return x - x**3 / 3 + x**5 / 5 - x**7 / 7


pi_lower_paper = 4 * (taylor7(F(1, 2)) + taylor7(F(1, 3)))
check("4 * (taylor7(1/2) + taylor7(1/3)) == 1538665/489888",
      pi_lower_paper == F(1538665, 489888))

threshold = F(500000, 159201)
check("32 / (399/125)^2 == 500000/159201",
      F(32) / F(399, 125) ** 2 == threshold)
check("paper pi bound exceeds threshold by exactly 206455/1237946976",
      pi_lower_paper - threshold == F(206455, 1237946976))
check("paper pi bound > threshold (so the reduction applies)",
      pi_lower_paper > threshold)
check("Mathlib pi bound used in Lean, 3141592/1000000, also exceeds threshold",
      F(3141592, 1000000) > threshold)

check("383/100 - 399/125 == 319/500", F(383, 100) - F(399, 125) == F(319, 500))
check("8 - 399/125 == 601/125", F(8) - F(399, 125) == F(601, 125))
check("chain order: 399/125 < 383/100 < 8", F(399, 125) < F(383, 100) < F(8))

lean_src = (here / "code" / "Cert.lean").read_text()
check("Cert.lean states cert_main",
      "theorem cert_main : 8 / Real.sqrt (2 * Real.pi) < 399 / 125" in lean_src)
check("Cert.lean states cert_chain", "theorem cert_chain" in lean_src)
check("Cert.lean has no sorry/admit",
      "sorry" not in lean_src and "admit" not in lean_src)

log = (here / "evidence" / "lean-build.log").read_text()
check("recorded lake build succeeded", "Build completed successfully" in log)
check("cert_main axioms are exactly the allowed set",
      "'cert_main' depends on axioms: [propext, Classical.choice, Quot.sound]" in log)
check("cert_chain axioms are exactly the allowed set",
      "'cert_chain' depends on axioms: [propext, Classical.choice, Quot.sound]" in log)

if failures:
    print(f"FAIL: {len(failures)} check(s) failed")
    sys.exit(1)
print("PASS")
