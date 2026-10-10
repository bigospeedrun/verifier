-- TEST ONLY. Source: chafreaky/wht-power-saving-lean @ 837dc3130adc79f7b7ab4ddd56c15576bbd766b0.
-- Proof credits and upstream notices remain in the imported source files.
-- Mechanical import-prefix adaptation for the direct PR submission layout.
import Submission.Work.Fourier233.Main

open OAI.PowerSaving Filter Asymptotics

theorem Race.bound : ∃ order solve W, DFTProgram order solve W ∧
    (fun n : ℕ => (W n : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) * (Real.log (n : ℝ)) ^ (1 - (47171 : ℝ) / 62500000)) := by
  obtain ⟨order, solve, W, hprogram, htime⟩ := transform_mainY
  refine ⟨order, solve, W, hprogram, ?_⟩
  have hexp : decimalExponentY = 1 - (47171 : ℝ) / 62500000 := by
    norm_num [decimalExponentY]
  simpa only [decimalTimeY, hexp] using htime.2.1
