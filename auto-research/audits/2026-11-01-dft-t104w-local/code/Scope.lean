/-
Audit scope probe for the DFT submission 312780997/100000000000
(bigospeedrun/verifier PR #91, HalitZiyaKARTAL/bigO-dft-verifier @
524a8af8a277ca50c1237068c2b45430a03f547e).

Compiled with `lake env lean` against the staged audit build of the submission
(Lean 4.34.1, mathlib d13f23b). It checks, inside Lean's kernel:

1. `Race.bound` in `Submission.lean` discharges, verbatim and up to defeq, the
   exact target the verifier generates for this bound
   (scripts/submissions.py `challenge_source`, problem dft, bound
   312780997/100000000000).
2. The `DFTProgram` predicate inside that statement expands by `rfl` to the
   full all-lengths exact scalar/index RAM specification: a polynomial
   address/word cap, an order program supplying a valid bounded root, and a
   solve program whose work is bounded by W and whose output is the exact
   canonical DFT for every input vector, at every positive length.
3. The stated saving constant of the entry is exactly 312780997/10^11, and the
   internal rate certificate (727/232431) is strictly stronger, so the stated
   exponent is not the tightest value the machinery certified.
-/

import Submission

open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty Filter Asymptotics

namespace AuditScope

/-- 1. The verifier's generated target at this bound, restated verbatim and
discharged by the submission's own theorem. A mismatch of any named constant
(`DFTProgram`, `=O`, `atTop`, the rational literal) fails to elaborate. -/
theorem verifier_target : ∃ order solve W, DFTProgram order solve W ∧
    (fun n : ℕ => (W n : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) * (Real.log (n : ℝ)) ^ (1 - (312780997 : ℝ) / 100000000000)) :=
  Race.bound

/-- 2. The statement's program predicate expands, by `rfl`, to the full
specification with every quantifier and clause visible: work cap on W itself,
peak/value bounds on the supplied root, validity, and exact DFT output for all
inputs at all positive lengths. -/
example
    (order : RAM.Prog false RAM.Ty.w RAM.Ty.w)
    (solve : RAM.Prog false dftInKind dftOutKind) (W : ℕ → ℕ) :
    DFTProgram order solve W =
      (∃ cBound : ℕ, ∀ n : ℕ, 0 < n →
        let cap := (n + 2) ^ cBound
        let d := run order n
        W n + 10 * (n + 2) ≤ cap ∧ d.peak ≤ cap ∧ d.valid ∧
          0 < d.val ∧ d.val < 1024 * n ^ 3 ∧ d.val ≤ cap ∧
          ∀ x : Vec n,
            let result := run solve (n, root d.val, (⟨n, x⟩ : Tape ℂ))
            result.valid ∧ result.peak ≤ cap ∧ d.work + 1 + result.work ≤ W n ∧
              result.val = (⟨n, dft n x⟩ : Tape ℂ)) :=
  rfl

/-- 3. The stated saving is the literal in the theorem, and the certified rate
`727/232431` (Work/FwdOnly/P104WRate.lean) strictly exceeds it, so the stated
exponent leaves honest margin rather than rounding past the certificate. -/
example : statedSavingT104W = (312780997 : ℝ) / (100000000000 : ℝ) ∧
    (312780997 : ℝ) / (100000000000 : ℝ) < 727 / (232431 : ℝ) := by
  constructor
  · norm_num [statedSavingT104W]
  · norm_num

end AuditScope

#print axioms AuditScope.verifier_target
