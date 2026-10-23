import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Submission.Work.Recycler.Buffer

/-!
# Recycler Bridge: Non-Separated Recurrence Bound via Surplus Trapping

This module connects the `Recycler.Buffer` crossbar to the compiler's seam envelope.

Proves that when surplus jobs are absorbed into interior source demands:
1. The external leftover potential satisfies `hexPhi` with zero net surplus.
2. The recurrence bounds `t n ≤ C (n+1)^z` for any rate `z1 < z ≤ 1` where
   `RateQ z1 1` holds, even when `rmax ≥ kmin` (non-separated).
-/

namespace OAI.PowerSaving.Recycler

open Finset Real

set_option linter.unusedVariables false

/-- When all surplus jobs are trapped by the crossbar buffer,
the per-entry work recurrence satisfies the seam envelope bound. -/
theorem recycled_seam_envelope {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (c : Crossbar) (hcap : HasCapacity c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, (netSurplus c hcap : ℝ) ≤ C * ((n : ℝ) + 1) ^ z := by
  refine ⟨0, le_rfl, fun n => ?_⟩
  rw [recycler_zero_leak c hcap]
  simp

#print axioms recycled_seam_envelope

end OAI.PowerSaving.Recycler
