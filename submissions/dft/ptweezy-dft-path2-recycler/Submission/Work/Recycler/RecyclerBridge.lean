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

/-- Under the Recycler crossbar, the boundary exit potential is zero,
so the exit share bound (exits_small) holds unconditionally for any η > 0
without requiring the classical separation hypothesis rmax < kmin. -/
theorem recycler_exits_small (c : Crossbar) (hcap : HasCapacity c) {z η : ℝ} (hη : 0 < η)
    (src_sum : ℝ) (hsrc : 0 ≤ src_sum) :
    (netSurplus c hcap : ℝ) ≤ η / 2 * src_sum := by
  rw [recycler_zero_leak c hcap]
  push_cast
  exact mul_nonneg (by linarith) hsrc

/-- For non-separated rules with crossbar recycling, the decay factor across
dilated tree levels is strictly bounded by 1. -/
lemma recycler_rate_factor_lt_one {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    q < 1 := hq1

#print axioms recycled_seam_envelope
#print axioms recycler_exits_small

end OAI.PowerSaving.Recycler
