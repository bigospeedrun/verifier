-- Entry point for the Big O Speedrun verifier (exact DFT, all lengths).
-- Saving 2555269/2500000000 = 10221076/10^10, from the certificate candidate.json.gz
-- (sha256 3a705efb37f16863b005c8cb0082a4172230c0f7e1a05a6a452a0bfab7eb0ecf) and its bank plan (sha256 36e8bff0899204cffde1182fa9b75f9bf7fe24c89235f8dd51bf2f584101a608) through the entrance-gauged nine-stage layout of PR #401 (Dugongue) on the compressed nine-stage layout of PR #377 (jacklightChen), CrocSwap/integer-mult-bounds; Lean files by DFT Bridge3, DFT New Sums and DFT Lean.
-- The proof builds on Jacob Sussman's development (github.com/jacobalansussman/wht-power-saving-lean, commit
-- 9c94857, Apache-2.0). See NOTICE and CREDITS.md. Imports are prefixed with `Submission.`.
import Submission.Work.FourierC401G5.Main

open OAI.PowerSaving Filter Asymptotics

theorem Race.bound : ∃ order solve W, DFTProgram order solve W ∧
    (fun n : ℕ => (W n : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) * (Real.log (n : ℝ)) ^ (1 - (2555269 : ℝ) / 2500000000)) := by
  obtain ⟨order, solve, W, hprogram, htime⟩ := transform_mainC401G5
  refine ⟨order, solve, W, hprogram, ?_⟩
  have hexp : decimalExponentC401G5 = 1 - (2555269 : ℝ) / 2500000000 := by
    norm_num [decimalExponentC401G5]
  have htime_eq : decimalTimeC401G5 =
      (fun n : ℕ => (n : ℝ) * (Real.log (n : ℝ)) ^ (1 - (2555269 : ℝ) / 2500000000)) := by
    funext n
    simp only [decimalTimeC401G5, hexp]
  rw [← htime_eq]
  exact htime.2.1
