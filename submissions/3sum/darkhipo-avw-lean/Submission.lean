import Submission.ThreeSumApsp.Statements.EndStatement

/-!
# Submission: 3SUM at exponent 2499/1250 (Theorem 22 of arXiv:2610.06783)

The proof of `Race.bound` is the Lean formalization released by Anthropic with
the paper (github.com/anthropics/formal-math, Apache 2.0) -- see LICENSE and
NOTICE alongside. Paper by Josh Alman and Virginia Vassilevska Williams.

The only line of original work is the bridge: the statement's `Theorem_22_3SUM`
uses the decimal literal `1.9992`, the exact-bound target uses the reduced
fraction `2499/1250`, and the trusted statement's own docstring records that
these are the same number (it reads `T(n)^1250 <= K n^2499`).
-/
theorem Race.bound : EndStatement.ThreeSum.SolvedInTime ((2499 : Rat) / 1250) := by
  have h : ((2499 : Rat) / 1250) = 1.9992 := by norm_num
  rw [h]
  exact ThreeSumApsp.endStatement_theorem_22_3SUM
