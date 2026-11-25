import Submission.BinaryKernel.Endpoint
import Submission.AdaptiveRate.RateToDFT

namespace DFTSpeedrun.HalfKernel
open OAI.PowerSaving OAI.PowerSaving.RAM SelectedPlan Asymptotics Filter Real
noncomputable section

theorem bound_of_large
    (large : ∀ r, fixedPlan.arity ≤ r → ∀ cl m,
      LargeBody cl m fixedPlan.arity fixedPlan.rows fixedPlan.program.calls r) :
    ∃ order solve W, DFTProgram order solve W ∧
      (fun n : ℕ => (W n : ℝ)) =O[atTop]
        (fun n : ℕ => (n : ℝ) * (log (n : ℝ)) ^ (1-saving)) := by
  have nonneg : 0 ≤ beta := by linarith [half_lt_beta]
  have le_one : beta ≤ 1 := by norm_num [beta,D]
  have ent := WalshBridge.of_even_kernel nonneg le_one (selected_even.{0} large)
  have engine : RippleEngine.{0} beta := ⟨nonneg, fun _ _ _ k v => WalshBridge.ripple_program_of_walsh k v ent⟩
  exact FourierSearch.bound_of_engine engine le_one beta_lt_target
end
end DFTSpeedrun.HalfKernel
