import Submission.Work.U7604.Chain.FourierTB.Main

open OAI.PowerSaving Asymptotics Filter Real

namespace FourierSearch

/-- The compiler charges an extra squared iterated logarithm. Any strictly
larger log exponent absorbs that factor in the public DFT cost model. -/
theorem bound_of_engine {z p : ℝ} (engine : RippleEngine.{0} z)
    (hz : z ≤ 1) (hp : z < p) :
    ∃ order solve W, DFTProgram order solve W ∧
      (fun n : ℕ => (W n : ℝ)) =O[atTop]
        (fun n : ℕ => (n : ℝ) * (log (n : ℝ)) ^ p) := by
  obtain ⟨order, solve, W, program, work, _⟩ := dft_program_of_engine engine hz
  refine ⟨order, solve, W, program, work.trans (isBigO_iff.mpr ⟨1, ?_⟩)⟩
  filter_upwards [targetTime_le_eventually hp (show (0 : ℝ) < 1 by norm_num)] with n hn
  rwa [Real.norm_of_nonneg (targetTime_nonneg _ n),
    Real.norm_of_nonneg (mul_nonneg (Nat.cast_nonneg n) (rpow_nonneg (log_natCast_nonneg n) p))]

end FourierSearch
