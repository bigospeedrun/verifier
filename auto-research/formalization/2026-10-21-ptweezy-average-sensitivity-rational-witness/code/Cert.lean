import Mathlib

open Real

theorem cert_main : 8 / Real.sqrt (2 * Real.pi) < 399 / 125 := by
  have hpi : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hs : (1000 / 399 : ℝ) < Real.sqrt (2 * Real.pi) := by
    rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1000 / 399)]
    nlinarith [hpi]
  rw [div_lt_iff₀ hsqrt_pos]
  nlinarith [hs]

theorem cert_chain : (399 / 125 : ℝ) < 383 / 100 ∧ (383 / 100 : ℝ) < 8 := by
  constructor <;> norm_num

#print axioms cert_main
#print axioms cert_chain
