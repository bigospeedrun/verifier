/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Pruned.Costs

/-!
# The numbers for `c = 20`, `θ = 56569/500000`

* `Γ(20, θ) > 0.0660254` (the value is `0.0660254068…`), `GammaOf_B`; and `0 < Γ < 0.0661`;
* `q(θ) < 0.4339741` (the value is `0.43397406…`), `qOf_B`;
* `19 ln 3 / ln 4 < 15.05716` (the value is `15.0571437…`), `bExp_B`;
* `20 H(1/20) / ln 4 < 2.9` (the value is `2.8639696…`), `kappa_B`.

As in `ThreeSumApsp.Filter.ThinCosts`, `Γ ln 4` is written as
`(1-θ) ln(1-θ) + 19 ln((19+θ)/19) + θ ln(19+θ) - θ ln 9`, so that the two large terms are
combined.
-/

@[expose] public section

namespace ThreeSumApsp

private lemma logB_a : Real.log (443431 / 500000) ∈ Set.Icc (-0.1200658894) (-0.1200658893) :=
  ⟨le_trans (by numerics) (log_mem 0 5).1, (log_mem 0 5).2.trans (by numerics)⟩

private lemma logB_b : Real.log (9556569 / 9500000) ∈ Set.Icc 0.0059369728 0.0059369729 :=
  ⟨le_trans (by numerics) (log_mem 0 3).1, (log_mem 0 3).2.trans (by numerics)⟩

private lemma logB_c : Real.log (9556569 / 500000) ∈ Set.Icc 2.95037595 2.95037596 :=
  ⟨le_trans (by numerics) (log_mem 4 6).1, (log_mem 4 6).2.trans (by numerics)⟩

private lemma logB_9 : Real.log 9 ∈ Set.Icc 2.197224576 2.197224579 :=
  ⟨le_trans (by numerics) (log_mem 3 6).1, (log_mem 3 6).2.trans (by numerics)⟩

private lemma logB_4 : Real.log 4 ∈ Set.Icc 1.3862943606 1.3862943616 := by
  rw [Real.log_four]
  exact ⟨by linarith [Real.log_two_gt_d9], by linarith [Real.log_two_lt_d9]⟩

private lemma logB_3 : Real.log 3 ∈ Set.Icc 1.098612288 1.098612290 :=
  ⟨le_trans (by numerics) (log_mem 2 8).1, (log_mem 2 8).2.trans (by numerics)⟩

private lemma logB_19 : Real.log 19 ∈ Set.Icc 2.94443897 2.94443899 :=
  ⟨le_trans (by numerics) (log_mem 4 8).1, (log_mem 4 8).2.trans (by numerics)⟩

private lemma logB_20 : Real.log 20 ∈ Set.Icc 2.99573226 2.99573228 :=
  ⟨le_trans (by numerics) (log_mem 4 8).1, (log_mem 4 8).2.trans (by numerics)⟩

/-- `Γ ln 4` at `c = 20`, `θ = 56569/500000`, with the two large terms combined. -/
private lemma GammaOf_B_eq :
    GammaOf 20 (56569 / 500000) * Real.log 4
      = 443431 / 500000 * Real.log (443431 / 500000)
        + 19 * Real.log (9556569 / 9500000)
        + 56569 / 500000 * Real.log (9556569 / 500000)
        - 56569 / 500000 * Real.log 9 := by
  rw [GammaOf_mul_log_four (by norm_num) (by norm_num) (by norm_num)]
  have h1 : (1 : ℝ) - 56569 / 500000 = 443431 / 500000 := by norm_num
  have h2 : (20 : ℝ) - 1 + 56569 / 500000 = 9556569 / 500000 := by norm_num
  have h3 : (20 : ℝ) - 1 = 19 := by norm_num
  rw [h1, h2, h3, show (9556569 / 9500000 : ℝ) = (9556569 / 500000) / 19 by
    norm_num, Real.log_div (x := 9556569 / 500000) (y := 19) (by norm_num) (by norm_num)]
  ring

/-- `Γ(20, 56569/500000) > 0.0660254` (the value is `0.0660254068…`). -/
theorem GammaOf_B : (0.0660254 : ℝ) < GammaOf 20 (56569 / 500000) := by
  refine lt_of_mul_lt_mul_right ?_ log_four_pos.le
  rw [GammaOf_B_eq]
  have h1 := logB_a; have h2 := logB_b; have h3 := logB_c; have h4 := logB_9
  have h5 := logB_4
  simp only [Set.mem_Icc] at *
  linarith

/-- `Γ(20, 56569/500000) < 0.0661`. -/
theorem GammaOf_B_lt : GammaOf 20 (56569 / 500000) < (0.0661 : ℝ) := by
  refine lt_of_mul_lt_mul_right ?_ log_four_pos.le
  rw [GammaOf_B_eq]
  have h1 := logB_a; have h2 := logB_b; have h3 := logB_c; have h4 := logB_9
  have h5 := logB_4
  simp only [Set.mem_Icc] at *
  linarith

/-- `Γ(20, 56569/500000) > 0`. -/
theorem GammaOf_B_pos : 0 < GammaOf 20 (56569 / 500000) :=
  lt_trans (by norm_num) GammaOf_B

/-- `q(56569/500000) < 0.4339741` (the value is `0.43397406…`). -/
theorem qOf_B : qOf (56569 / 500000) < (0.4339741 : ℝ) :=
  lt_of_le_of_lt (qOf_le (-3) (r := 0.43397407)) (by norm_num)

/-- `19 ln 3 / ln 4 < 15.05716` (the value is `15.0571437…`). -/
theorem bExp_B : 19 * Real.log 3 / Real.log 4 < (15.05716 : ℝ) := by
  rw [div_lt_iff₀ log_four_pos]
  have h3 := logB_3; have h5 := logB_4
  simp only [Set.mem_Icc] at *
  linarith

/-- `20 H(1/20) / ln 4 < 2.9` (the value is `2.8639696…`). -/
theorem kappa_B : 20 * entropy (1 / 20) / Real.log 4 < (2.9 : ℝ) := by
  rw [div_lt_iff₀ log_four_pos, PrunedAux.mul_entropy_inv (by norm_num)]
  have h1 := logB_19; have h2 := logB_20; have h5 := logB_4
  simp only [Set.mem_Icc] at *
  norm_num
  linarith

end ThreeSumApsp
