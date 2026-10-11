/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Pruned.CostsAux
public import Submission.ThreeSumApsp.Sec4.Table2.LogBounds

/-!
# A sharper analysis of Corollary 31: binomial tails and pruned encodings

Two refinements of `Corollary31.costs`, for `L = ⌈cm⌉`, `t = ⌈θm⌉`, `D = 4^m`:

* The number of boxes is bounded by the binomial tail `∑_{d=t}^{m} β_d` (`tailBeta`) itself,
  instead of the geometric bound `M ρ^t/(1-ρ)`. The tail is at most `β_t/(1-ρ)`, and
  `β_t/M = 9^t binom(L, m-t)/binom(L, m) = O(D^{-Γ})` with
  `Γ(c, θ) = (c H(1/c) - c H((1-θ)/c) - θ ln 9)/ln 4` (`GammaOf`).
* The encodings are pruned: their cost is `L N ∑_{d ≤ m} β_d / √M` (`retained`), which is
  `O(L N √M)`, and `√M = O(D^{A_pruned})` with `A_pruned(c) = ((1/2) c H(1/c) + (c-1) ln 3)/ln 4`
  (`Apruned`).

The main result is `CorollaryP.costs`; the numbers for `c = 22`, `θ = 29/250` are
`GammaOf_22`, `Apruned_22`, `qOf_29_250` and `admissibleP_22`.
-/

@[expose] public section

open Finset

namespace ThreeSumApsp

open PrunedAux

/-- The exponent of the binomial tail: `Γ(c, θ) = (c H(1/c) - c H((1-θ)/c) - θ ln 9)/ln 4`. -/
noncomputable def GammaOf (c θ : ℝ) : ℝ :=
  (c * entropy (1 / c) - c * entropy ((1 - θ) / c) - θ * Real.log 9) / Real.log 4

/-- The exponent of `√M`: `A_pruned(c) = ((1/2) c H(1/c) + (c-1) ln 3)/ln 4`. -/
noncomputable def Apruned (c : ℝ) : ℝ :=
  ((1 / 2) * c * entropy (1 / c) + (c - 1) * Real.log 3) / Real.log 4

/-- The number of retained entries of the pruned encodings: `∑_{d=0}^{m} β_d`. -/
def retained (L m : ℕ) : ℕ := ∑ d ∈ Finset.range (m + 1), beta L m d

/-- The binomial tail `∑_{d=t}^{m} β_d`. -/
noncomputable def tailBeta (L m t : ℕ) : ℝ := ∑ d ∈ Finset.Icc t m, (beta L m d : ℝ)

/-- the preprocessing cost of the pruned data structure: boxes + encodings -/
noncomputable def cost8p (L m t N : ℕ) : ℝ :=
  (L : ℝ) * ((m : ℝ) + 1) * (tailBeta L m t / (M L m : ℝ)) * (N : ℝ) ^ 2
    + (L : ℝ) * (N : ℝ) * (retained L m : ℝ) / Real.sqrt (M L m : ℝ)

/-- The hypotheses of the sharper corollary on its parameters. -/
structure AdmissibleP (c θ ε : ℝ) : Prop where
  c_gt : 10 < c
  θ_pos : 0 < θ
  θ_lt : θ < 0.9
  thin : ε * (Apruned c + GammaOf c θ) < 1

/-! ### The exponents -/

/-- `Γ ln 4 = (1-θ) ln(1-θ) + (c-1+θ) ln(c-1+θ) - (c-1) ln(c-1) - θ ln 9`. -/
theorem GammaOf_mul_log_four {c θ : ℝ} (hc : 1 < c) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    GammaOf c θ * Real.log 4
      = (1 - θ) * Real.log (1 - θ) + (c - 1 + θ) * Real.log (c - 1 + θ)
        - (c - 1) * Real.log (c - 1) - θ * Real.log 9 := by
  rw [GammaOf, div_mul_cancel₀ _ log_four_pos.ne', mul_entropy_inv hc,
    mul_entropy_div (a := 1 - θ) (by linarith) (by linarith),
    show c - (1 - θ) = c - 1 + θ by ring]
  ring

/-- `A_pruned ln 4 = (1/2)(c ln c - (c-1) ln(c-1)) + (c-1) ln 3`. -/
theorem Apruned_mul_log_four {c : ℝ} (hc : 1 < c) :
    Apruned c * Real.log 4
      = (1 / 2) * (c * Real.log c - (c - 1) * Real.log (c - 1)) + (c - 1) * Real.log 3 := by
  rw [Apruned, div_mul_cancel₀ _ log_four_pos.ne', mul_assoc, mul_entropy_inv hc]

/-- `F(cx, x, θx) = -Γ x ln 4`. -/
theorem Fexp_scale_eq {c θ x : ℝ} (hc : 1 < c) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hx : 0 < x) :
    Fexp (c * x) x (θ * x) = -(GammaOf c θ * (x * Real.log 4)) := by
  rw [Fexp_scale hc hθ1 hθ0.le hx, ← mul_assoc, mul_comm (GammaOf c θ) x, mul_assoc,
    GammaOf_mul_log_four hc hθ0 hθ1]
  ring

/-- The sharper exponent is at least the exponent `γ` of Corollary 31. -/
theorem gammaOf_le_GammaOf {c θ : ℝ} (hc : 10 < c) (hθ0 : 0 < θ) (hθ1 : θ < 0.9) :
    gammaOf c θ ≤ GammaOf c θ := by
  have h := Fexp_sub_le (u := c) (m := 1) (s₁ := 0) (s₂ := θ) hθ0.le (by linarith)
    (by norm_num) (by linarith)
  rw [Fexp_zero, sub_zero, sub_zero, sub_zero, Real.log_one] at h
  simp only [add_zero] at h
  have h2 := Fexp_scale_eq (x := 1) (by linarith : (1 : ℝ) < c) hθ0 (by linarith) one_pos
  rw [mul_one, mul_one, one_mul] at h2
  rw [h2] at h
  have hγ : gammaOf c θ * Real.log 4 = θ * (Real.log (c - 1) - Real.log 9) := by
    rw [gammaOf, div_mul_cancel₀ _ log_four_pos.ne', one_div_rhoC,
      Real.log_div (by linarith) (by norm_num)]
  have : gammaOf c θ * Real.log 4 ≤ GammaOf c θ * Real.log 4 := by
    rw [hγ]
    linarith
  exact le_of_mul_le_mul_right this log_four_pos

/-- `Γ > 0` for admissible `c` and `θ`. -/
theorem GammaOf_pos {c θ : ℝ} (hc : 10 < c) (hθ0 : 0 < θ) (hθ1 : θ < 0.9) : 0 < GammaOf c θ :=
  (corollary_31_gamma_pos c θ hc hθ0).trans_le (gammaOf_le_GammaOf hc hθ0 hθ1)

/-! ### The binomial tail -/

/-- `β_d ≤ ρ^{d-t} β_t` for `t ≤ d ≤ m`. -/
theorem beta_le_rho_pow {L m t : ℕ} (hL : 10 * m ≤ L) {d : ℕ} (htd : t ≤ d) (hdm : d ≤ m) :
    (beta L m d : ℝ) ≤ rho L m ^ (d - t) * (beta L m t : ℝ) := by
  induction d, htd using Nat.le_induction with
  | base => simp
  | succ d hd ih =>
    obtain ⟨hratio, hle⟩ := eq_7_ratio L m (d + 1) hL (by omega) hdm
    have hpos : (0 : ℝ) < (beta L m d : ℝ) := by
      exact_mod_cast beta_pos (L := L) (m := m) (by omega) d
    rw [← hratio, Nat.add_sub_cancel, div_le_iff₀ hpos] at hle
    calc (beta L m (d + 1) : ℝ) ≤ rho L m * (beta L m d : ℝ) := hle
      _ ≤ rho L m * (rho L m ^ (d - t) * (beta L m t : ℝ)) :=
          mul_le_mul_of_nonneg_left (ih (by omega)) (rho_nonneg hL)
      _ = rho L m ^ (d + 1 - t) * (beta L m t : ℝ) := by
          rw [show d + 1 - t = (d - t) + 1 by omega, pow_succ]
          ring

/-- The tail is at most `β_t/(1-ρ)`. -/
theorem tailBeta_le {L m t : ℕ} (hL : 10 * m ≤ L) :
    tailBeta L m t ≤ (beta L m t : ℝ) / (1 - rho L m) := by
  have hρ0 := rho_nonneg hL
  have hρ1 := sec4_rho_lt_one L m hL
  have hβ : (0 : ℝ) ≤ beta L m t := Nat.cast_nonneg _
  calc tailBeta L m t ≤ ∑ d ∈ Icc t m, rho L m ^ (d - t) * (beta L m t : ℝ) :=
        sum_le_sum fun d hd => beta_le_rho_pow hL (mem_Icc.1 hd).1 (mem_Icc.1 hd).2
    _ = (∑ i ∈ range (m + 1 - t), rho L m ^ i) * (beta L m t : ℝ) := by
        rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, sum_mul]
        refine sum_congr rfl fun i _ => ?_
        rw [Nat.add_sub_cancel_left]
    _ ≤ (1 / (1 - rho L m)) * (beta L m t : ℝ) := by
        refine mul_le_mul_of_nonneg_right ?_ hβ
        have := geom_sum_Ico_le_of_lt_one (m := 0) (n := m + 1 - t) hρ0 hρ1
        rwa [pow_zero, ← Finset.range_eq_Ico] at this
    _ = (beta L m t : ℝ) / (1 - rho L m) := by ring

/-- The retained entries number at most `M/(1-ρ)`. -/
theorem retained_le {L m : ℕ} (hL : 10 * m ≤ L) :
    (retained L m : ℝ) ≤ (M L m : ℝ) / (1 - rho L m) := by
  have hρ0 := rho_nonneg hL
  have hρ1 := sec4_rho_lt_one L m hL
  rw [retained, Nat.cast_sum]
  calc ∑ d ∈ range (m + 1), (beta L m d : ℝ) ≤ ∑ d ∈ range (m + 1), rho L m ^ d * (M L m : ℝ) :=
        sum_le_sum fun d hd => eq_7 L m d hL (by rw [mem_range] at hd; omega)
    _ = (∑ d ∈ range (m + 1), rho L m ^ d) * (M L m : ℝ) := by rw [sum_mul]
    _ ≤ (1 / (1 - rho L m)) * (M L m : ℝ) := by
        refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
        have := geom_sum_Ico_le_of_lt_one (m := 0) (n := m + 1) hρ0 hρ1
        rwa [pow_zero, ← Finset.range_eq_Ico] at this
    _ = (M L m : ℝ) / (1 - rho L m) := by ring

/-- `β_t ≤ M · m/(m-t) · e^{F(L, m, t)}` for `t < m ≤ L`. -/
theorem beta_le_exp {L m t : ℕ} (htm : t < m) (hmL : m ≤ L) :
    (beta L m t : ℝ)
      ≤ (M L m : ℝ) * ((m : ℝ) / ((m : ℝ) - t)) * Real.exp (Fexp L m t) := by
  have hr := ratio_mono L (k₁ := m - t) (k₂ := m) (by omega) hmL
  rw [Nat.cast_sub htm.le] at hr
  have hmt : (0 : ℝ) < (m : ℝ) - t := by
    have : (t : ℝ) < m := by exact_mod_cast htm
    linarith
  have hK : (L.choose (m - t) : ℝ)
      ≤ (L.choose m : ℝ) * ((m : ℝ) / ((m : ℝ) - t))
        * Real.exp (xlogx m + xlogx ((L : ℝ) - m) - xlogx ((m : ℝ) - t)
            - xlogx ((L : ℝ) - m + t)) := by
    rw [show (L : ℝ) - ((m : ℝ) - t) = (L : ℝ) - m + t by ring] at hr
    rw [sub_sub, Real.exp_sub, mul_div_assoc', le_div_iff₀ (Real.exp_pos _),
      show (L.choose m : ℝ) * ((m : ℝ) / ((m : ℝ) - t)) * Real.exp (xlogx m + xlogx ((L : ℝ) - m))
        = (L.choose m : ℝ) * m * Real.exp (xlogx m + xlogx ((L : ℝ) - m)) / ((m : ℝ) - t) by ring,
      le_div_iff₀ hmt]
    linarith
  have hbeta : (beta L m t : ℝ) = (L.choose (m - t) : ℝ) * 9 ^ (L - m) * 9 ^ t := by
    rw [beta]
    push_cast
    ring
  have hM : (M L m : ℝ) = (L.choose m : ℝ) * 9 ^ (L - m) := by
    rw [M, K, N0]
    push_cast
    rw [← pow_mul, mul_comm (L - m) 2, pow_mul]
    norm_num
  have h9 : (9 : ℝ) ^ t = Real.exp (t * Real.log 9) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [hbeta, hM, h9, Fexp, add_sub_assoc, add_sub_assoc, add_assoc, Real.exp_add]
  have h9L : (0 : ℝ) ≤ 9 ^ (L - m) := by positivity
  calc (L.choose (m - t) : ℝ) * 9 ^ (L - m) * Real.exp (t * Real.log 9)
      ≤ (L.choose m : ℝ) * ((m : ℝ) / ((m : ℝ) - t))
          * Real.exp (xlogx m + xlogx ((L : ℝ) - m) - xlogx ((m : ℝ) - t)
            - xlogx ((L : ℝ) - m + t)) * 9 ^ (L - m) * Real.exp (t * Real.log 9) := by gcongr
    _ = _ := by
        rw [show xlogx (m : ℝ) + xlogx ((L : ℝ) - m) - xlogx ((m : ℝ) - t)
            - xlogx ((L : ℝ) - m + t) = xlogx (m : ℝ) + (xlogx ((L : ℝ) - m)
              - xlogx ((m : ℝ) - t) - xlogx ((L : ℝ) - m + t)) by ring]
        ring

/-! ### The parameters `L = ⌈cm⌉` and `t = ⌈θm⌉` -/

/-- `L = ⌈cm⌉ ≤ (c + 1) m` for `m ≥ 1`. -/
theorem levelsOf_le_mul {c : ℝ} (hc : 10 < c) {m : ℕ} (hm : 1 ≤ m) :
    (levelsOf c m : ℝ) ≤ (c + 1) * m := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hL : (levelsOf c m : ℝ) < c * m + 1 := Nat.ceil_lt_add_one (by positivity)
  linarith

/-- The rounding of `L` and `t` only helps: `F(L, m, t) ≤ F(cm, m, θm) = -Γ m ln 4`. -/
theorem Fexp_levels_le {c θ : ℝ} (hc : 10 < c) (hθ0 : 0 < θ) (hθ1 : θ < 0.9) {m : ℕ}
    (hm : 1 ≤ m) :
    Fexp (levelsOf c m) m (switchOf θ m) ≤ -(GammaOf c θ * ((m : ℝ) * Real.log 4)) := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hcL : c * m ≤ (levelsOf c m : ℝ) := Nat.le_ceil _
  have hLc : (levelsOf c m : ℝ) < c * m + 1 := Nat.ceil_lt_add_one (by positivity)
  have hθt : θ * m ≤ (switchOf θ m : ℝ) := Nat.le_ceil _
  have ht1 : (1 : ℝ) ≤ (switchOf θ m : ℝ) := by
    have : 0 < switchOf θ m := Nat.ceil_pos.2 (by positivity)
    exact_mod_cast this
  have htm : (switchOf θ m : ℝ) ≤ m := by exact_mod_cast switchOf_le (by linarith) m
  have h9 : 9 * (m : ℝ) ≤ (c - 1) * m := by nlinarith
  calc Fexp (levelsOf c m) m (switchOf θ m)
      ≤ Fexp (c * m) m (switchOf θ m) := Fexp_anti_u hcL (by linarith) (by nlinarith)
    _ ≤ Fexp (c * m) m (θ * m) :=
        Fexp_anti_s hθt htm (by nlinarith) (by nlinarith) (by nlinarith)
    _ = -(GammaOf c θ * ((m : ℝ) * Real.log 4)) :=
        Fexp_scale_eq (by linarith) hθ0 (by linarith) (by linarith)

/-- `M > 0` for `m ≤ L`. -/
theorem cast_M_pos {L m : ℕ} (hmL : m ≤ L) : (0 : ℝ) < (M L m : ℝ) := by
  rw [← beta_zero_eq_M]
  exact_mod_cast beta_pos hmL 0

/-- The step on the boxes: `tailBeta/M ≤ 1/(1-ρ_c) · 2/(1-θ) · D^{-Γ}` once `(1-θ) m ≥ 2`. -/
theorem tail_div_M_le {c θ : ℝ} (hc : 10 < c) (hθ0 : 0 < θ) (hθ1 : θ < 0.9) {m : ℕ}
    (hm : 1 ≤ m) (hm2 : 2 ≤ (1 - θ) * m) :
    tailBeta (levelsOf c m) m (switchOf θ m) / (M (levelsOf c m) m : ℝ)
      ≤ 1 / (1 - rhoC c) * (2 / (1 - θ)) * (D m : ℝ) ^ (-GammaOf c θ) := by
  set L := levelsOf c m
  set t := switchOf θ m
  have hL10 : 10 * m ≤ L := ten_mul_le_levelsOf hc m
  have hmL : m ≤ L := by omega
  have hM := cast_M_pos hmL
  have hgap : 0 < 1 - rhoC c := sub_pos.2 (rhoC_lt_one hc)
  have hgap_le : 1 - rhoC c ≤ 1 - rho L m := by linarith [Corollary31.rho_lt hc m]
  have htlt : (t : ℝ) < θ * m + 1 := Nat.ceil_lt_add_one (by positivity)
  have hmt : (1 - θ) * m / 2 ≤ (m : ℝ) - t := by linarith
  have htm : t < m := by
    have : (t : ℝ) < m := by linarith
    exact_mod_cast this
  have hmt0 : 0 < (m : ℝ) - t := by linarith
  have hratio : (m : ℝ) / ((m : ℝ) - t) ≤ 2 / (1 - θ) := by
    rw [div_le_div_iff₀ hmt0 (by linarith)]
    nlinarith
  have hexp : Real.exp (Fexp L m t) ≤ (D m : ℝ) ^ (-GammaOf c θ) := by
    rw [cast_D_rpow, neg_mul]
    exact Real.exp_le_exp.2 (Fexp_levels_le hc hθ0 hθ1 hm)
  have hβ := beta_le_exp htm hmL
  have hβ0 : (0 : ℝ) ≤ beta L m t := Nat.cast_nonneg _
  rw [div_le_iff₀ hM]
  calc tailBeta L m t ≤ (beta L m t : ℝ) / (1 - rho L m) := tailBeta_le hL10
    _ ≤ (beta L m t : ℝ) / (1 - rhoC c) := div_le_div_of_nonneg_left hβ0 hgap hgap_le
    _ ≤ (M L m : ℝ) * ((m : ℝ) / ((m : ℝ) - t)) * Real.exp (Fexp L m t) / (1 - rhoC c) :=
        div_le_div_of_nonneg_right hβ hgap.le
    _ ≤ (M L m : ℝ) * (2 / (1 - θ)) * (D m : ℝ) ^ (-GammaOf c θ) / (1 - rhoC c) := by
        gcongr
        exact mul_nonneg hM.le (div_nonneg (by norm_num) (by linarith))
    _ = 1 / (1 - rhoC c) * (2 / (1 - θ)) * (D m : ℝ) ^ (-GammaOf c θ) * (M L m : ℝ) := by
        field_simp

/-! ### The encodings: `√M = O(D^{A_pruned})` -/

/-- `K = binom(L, m) ≤ 2 e^{m (c ln c - (c-1) ln(c-1))}`. -/
theorem K_le_exp {c : ℝ} (hc : 10 < c) {m : ℕ} (hm : 1 ≤ m) :
    (K (levelsOf c m) m : ℝ)
      ≤ 2 * Real.exp (m * (c * Real.log c - (c - 1) * Real.log (c - 1))) := by
  set L := levelsOf c m
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hcL : c * m ≤ (L : ℝ) := Nat.le_ceil _
  have hLc : (L : ℝ) < c * m + 1 := Nat.ceil_lt_add_one (by positivity)
  have hmL : m ≤ L := by have := ten_mul_le_levelsOf hc m; omega
  have hcm : 0 < c * m - m := by nlinarith
  have hA := sub_le_right (a := c * m) (b := (L : ℝ)) (by positivity) (by linarith)
  have hB := le_sub_left (a := c * m - m) (b := (L : ℝ) - m) hcm (by linarith)
  have hlog0 : 0 ≤ Real.log L - Real.log (c * m - m) := by
    rw [sub_nonneg]
    exact Real.log_le_log hcm (by linarith)
  have hlog2 : Real.log L - Real.log (c * m - m) ≤ Real.log 2 := by
    rw [← Real.log_div (by linarith) hcm.ne']
    refine Real.log_le_log (div_pos (by linarith) hcm) ?_
    rw [div_le_iff₀ hcm]
    nlinarith
  have hΔ : (L : ℝ) - c * m ≤ 1 := by linarith
  have hprod : ((L : ℝ) - c * m) * (Real.log L - Real.log (c * m - m)) ≤ Real.log 2 :=
    (mul_le_of_le_one_left hlog0 hΔ).trans hlog2
  have hscale := xlogx_scale (c := c) (x := m) (by linarith) (by linarith)
  have hexp : xlogx L - xlogx m - xlogx ((L : ℝ) - m)
      ≤ Real.log 2 + m * (c * Real.log c - (c - 1) * Real.log (c - 1)) := by
    rw [show (L : ℝ) - m - (c * m - m) = L - c * m by ring] at hB
    nlinarith
  calc (K L m : ℝ) ≤ Real.exp (xlogx L - xlogx m - xlogx ((L : ℝ) - m)) := choose_le_exp L m hmL
    _ ≤ Real.exp (Real.log 2 + m * (c * Real.log c - (c - 1) * Real.log (c - 1))) :=
        Real.exp_le_exp.2 hexp
    _ = 2 * Real.exp (m * (c * Real.log c - (c - 1) * Real.log (c - 1))) := by
        rw [Real.exp_add, Real.exp_log (by norm_num)]

/-- `√M = √K N₀ ≤ 3 √2 D^{A_pruned}`, with `D^{A_pruned}` written as `e^{A_pruned m ln 4}`. -/
theorem sqrtKN0_le_exp {c : ℝ} (hc : 10 < c) {m : ℕ} (hm : 1 ≤ m) :
    sqrtKN0 (levelsOf c m) m ≤ 3 * Real.sqrt 2 * Real.exp (Apruned c * ((m : ℝ) * Real.log 4)) := by
  set L := levelsOf c m
  set E := c * Real.log c - (c - 1) * Real.log (c - 1)
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hLc : (L : ℝ) < c * m + 1 := Nat.ceil_lt_add_one (by positivity)
  have hmL : m ≤ L := by have := ten_mul_le_levelsOf hc m; omega
  have hK := K_le_exp hc hm
  have hsqrtK : Real.sqrt (K L m : ℝ) ≤ Real.sqrt 2 * Real.exp (m * E / 2) := by
    calc Real.sqrt (K L m : ℝ) ≤ Real.sqrt (2 * Real.exp (m * E)) := Real.sqrt_le_sqrt hK
      _ = Real.sqrt 2 * Real.exp (m * E / 2) := by
          rw [Real.sqrt_mul (by norm_num)]
          congr 1
          rw [show Real.exp (m * E) = Real.exp (m * E / 2) ^ 2 by
            rw [sq, ← Real.exp_add]; ring_nf, Real.sqrt_sq (Real.exp_pos _).le]
  have hN0 : (N0 L m : ℝ) ≤ 3 * Real.exp ((c - 1) * m * Real.log 3) := by
    rw [N0, Nat.cast_pow, Nat.cast_ofNat, ← Real.exp_log (by norm_num : (0 : ℝ) < 3),
      ← Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 3), Nat.cast_sub hmL]
    calc Real.exp (((L : ℝ) - m) * Real.log 3) ≤ Real.exp ((c * m + 1 - m) * Real.log 3) :=
          Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (by linarith)
            (Real.log_nonneg (by norm_num)))
      _ = 3 * Real.exp ((c - 1) * m * Real.log 3) := by
          rw [show (c * m + 1 - m) * Real.log 3 = Real.log 3 + (c - 1) * m * Real.log 3 by ring,
            Real.exp_add, Real.exp_log (by norm_num)]
  have hA : Apruned c * ((m : ℝ) * Real.log 4) = m * E / 2 + (c - 1) * m * Real.log 3 := by
    rw [← mul_assoc, mul_comm (Apruned c), mul_assoc, Apruned_mul_log_four (by linarith)]
    ring
  rw [sqrtKN0, hA, Real.exp_add]
  calc Real.sqrt (K L m : ℝ) * (N0 L m : ℝ)
      ≤ (Real.sqrt 2 * Real.exp (m * E / 2)) * (3 * Real.exp ((c - 1) * m * Real.log 3)) :=
        mul_le_mul hsqrtK hN0 (Nat.cast_nonneg _) (by positivity)
    _ = 3 * Real.sqrt 2 * (Real.exp (m * E / 2) * Real.exp ((c - 1) * m * Real.log 3)) := by ring

/-- The analogue of (10): `√M · D^Γ ≤ N` once `m` exceeds a constant depending on `c`, `θ`, `ε`. -/
theorem eq_10p {c θ ε : ℝ} (h : AdmissibleP c θ ε) (hε : 0 < ε) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ D₀ N : ℕ, 4 ^ (m - 1) < D₀ → (D₀ : ℝ) ≤ (N : ℝ) ^ ε →
      sqrtKN0 (levelsOf c m) m * (D m : ℝ) ^ GammaOf c θ ≤ N := by
  obtain ⟨hc, hθ0, hθ1, hthin⟩ := h
  set S := Apruned c + GammaOf c θ
  set g := 1 / ε - S
  have hg : 0 < g := by
    have : ε * S < ε * (1 / ε) := by rw [mul_one_div_cancel hε.ne']; exact hthin
    have := lt_of_mul_lt_mul_left this hε.le
    simp only [g]; linarith
  refine ⟨⌈(2 + 1 / ε) / g⌉₊ + 1, fun m hm D₀ N hgt hthin' => ?_⟩
  have hm1 : 1 ≤ m := by omega
  have hmg : (2 + 1 / ε) / g ≤ m := by
    have := Nat.le_ceil ((2 + 1 / ε) / g)
    have h2 : ((⌈(2 + 1 / ε) / g⌉₊ : ℕ) : ℝ) ≤ m := by exact_mod_cast (by omega : _ ≤ m)
    linarith
  rw [div_le_iff₀ hg] at hmg
  have hX := log_four_pos
  have hsq := sqrtKN0_le_exp hc hm1
  have h32 : 3 * Real.sqrt 2 ≤ Real.exp (2 * Real.log 4) := by
    rw [show 2 * Real.log 4 = Real.log 4 + Real.log 4 by ring, Real.exp_add,
      Real.exp_log (by norm_num)]
    have : Real.sqrt 2 ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    linarith
  have hN := Corollary31.hypothesis hm1 hε hgt hthin'
  rw [Real.rpow_def_of_pos (by norm_num)] at hN
  rw [cast_D_rpow]
  calc sqrtKN0 (levelsOf c m) m * Real.exp (GammaOf c θ * ((m : ℝ) * Real.log 4))
      ≤ 3 * Real.sqrt 2 * Real.exp (Apruned c * ((m : ℝ) * Real.log 4))
          * Real.exp (GammaOf c θ * ((m : ℝ) * Real.log 4)) :=
        mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le
    _ ≤ Real.exp (2 * Real.log 4) * Real.exp (Apruned c * ((m : ℝ) * Real.log 4))
          * Real.exp (GammaOf c θ * ((m : ℝ) * Real.log 4)) := by gcongr
    _ = Real.exp ((2 + S * m) * Real.log 4) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
    _ ≤ Real.exp (Real.log 4 * (((m : ℝ) - 1) / ε)) := by
        rw [Real.exp_le_exp, mul_comm (Real.log 4)]
        refine mul_le_mul_of_nonneg_right ?_ hX.le
        have : ((m : ℝ) - 1) / ε = m * (1 / ε) - 1 / ε := by ring
        rw [this]
        simp only [g] at hmg
        nlinarith
    _ ≤ (N : ℝ) := hN

/-! ### The corollary -/

/-- The first term of `cost8p`, for `D = 4^m`. -/
theorem first_term_le {c θ : ℝ} (hc : 10 < c) (hθ0 : 0 < θ) (hθ1 : θ < 0.9) {m : ℕ}
    (hm : 1 ≤ m) (hm2 : 2 ≤ (1 - θ) * m) (N : ℕ) :
    (levelsOf c m : ℝ) * ((m : ℝ) + 1)
        * (tailBeta (levelsOf c m) m (switchOf θ m) / (M (levelsOf c m) m : ℝ)) * (N : ℝ) ^ 2
      ≤ 2 * (c + 1) * (1 / (1 - rhoC c) * (2 / (1 - θ)))
          * ((D m : ℝ) ^ (-GammaOf c θ) * Real.log (D m) ^ 2) * (N : ℝ) ^ 2 := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hL := levelsOf_le_mul hc hm
  have htail := tail_div_M_le hc hθ0 hθ1 hm hm2
  have hgap : 0 < 1 - rhoC c := sub_pos.2 (rhoC_lt_one hc)
  have hk : 0 ≤ 1 / (1 - rhoC c) * (2 / (1 - θ)) :=
    mul_nonneg (by positivity) (div_nonneg (by norm_num) (by linarith))
  have hlog : (m : ℝ) ^ 2 ≤ Real.log (D m) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (cast_le_log_cast_D m) 2
  have htail0 : 0 ≤ tailBeta (levelsOf c m) m (switchOf θ m) / (M (levelsOf c m) m : ℝ) :=
    div_nonneg (sum_nonneg fun _ _ => Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hDΓ : 0 ≤ (D m : ℝ) ^ (-GammaOf c θ) := (Real.rpow_pos_of_pos (cast_D_pos m) _).le
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  calc (levelsOf c m : ℝ) * ((m : ℝ) + 1)
        * (tailBeta (levelsOf c m) m (switchOf θ m) / (M (levelsOf c m) m : ℝ))
      ≤ ((c + 1) * m) * (2 * m)
          * (1 / (1 - rhoC c) * (2 / (1 - θ)) * (D m : ℝ) ^ (-GammaOf c θ)) := by
        gcongr
        linarith
    _ = 2 * (c + 1) * (1 / (1 - rhoC c) * (2 / (1 - θ)))
          * ((D m : ℝ) ^ (-GammaOf c θ) * (m : ℝ) ^ 2) := by ring
    _ ≤ 2 * (c + 1) * (1 / (1 - rhoC c) * (2 / (1 - θ)))
          * ((D m : ℝ) ^ (-GammaOf c θ) * Real.log (D m) ^ 2) := by
        gcongr

/-- The second term of `cost8p` (the pruned encodings), for `D = 4^m`, where `√M · D^Γ ≤ N`. -/
theorem second_term_le {c : ℝ} (hc : 10 < c) {Γ : ℝ} {m N : ℕ} (hm : 1 ≤ m)
    (hkey : sqrtKN0 (levelsOf c m) m * (D m : ℝ) ^ Γ ≤ N) :
    (levelsOf c m : ℝ) * (N : ℝ) * (retained (levelsOf c m) m : ℝ)
        / Real.sqrt (M (levelsOf c m) m : ℝ)
      ≤ (c + 1) / (1 - rhoC c) * ((D m : ℝ) ^ (-Γ) * Real.log (D m) ^ 2) * (N : ℝ) ^ 2 := by
  set L := levelsOf c m
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hL10 : 10 * m ≤ L := ten_mul_le_levelsOf hc m
  have hmL : m ≤ L := by omega
  have hLm := levelsOf_le_mul hc hm
  have hgap : 0 < 1 - rhoC c := sub_pos.2 (rhoC_lt_one hc)
  have hgap_le : 1 - rhoC c ≤ 1 - rho L m := by linarith [Corollary31.rho_lt hc m]
  have hpos := sqrtKN0_pos hmL
  have hsqrtM : Real.sqrt (M L m : ℝ) = sqrtKN0 L m := by
    rw [← sqrtKN0_sq, Real.sqrt_sq hpos.le]
  have hret : (retained L m : ℝ) ≤ (M L m : ℝ) / (1 - rhoC c) :=
    (retained_le hL10).trans (div_le_div_of_nonneg_left (Nat.cast_nonneg _) hgap hgap_le)
  have hDpos : 0 < (D m : ℝ) ^ Γ := Real.rpow_pos_of_pos (cast_D_pos m) Γ
  have hs : sqrtKN0 L m ≤ (N : ℝ) * (D m : ℝ) ^ (-Γ) := by
    rw [Real.rpow_neg (cast_D_pos m).le, ← div_eq_mul_inv, le_div_iff₀ hDpos]
    exact hkey
  have hlog : (m : ℝ) ≤ Real.log (D m) ^ 2 :=
    (cast_le_log_cast_D m).trans (by nlinarith [cast_le_log_cast_D m])
  have hDΓ : 0 ≤ (D m : ℝ) ^ (-Γ) := (Real.rpow_pos_of_pos (cast_D_pos m) _).le
  rw [hsqrtM]
  calc (L : ℝ) * (N : ℝ) * (retained L m : ℝ) / sqrtKN0 L m
      ≤ (L : ℝ) * (N : ℝ) * ((M L m : ℝ) / (1 - rhoC c)) / sqrtKN0 L m := by gcongr
    _ = (L : ℝ) * (N : ℝ) * sqrtKN0 L m / (1 - rhoC c) := by
        rw [← sqrtKN0_sq]
        field_simp
    _ ≤ ((c + 1) * Real.log (D m) ^ 2) * (N : ℝ) * ((N : ℝ) * (D m : ℝ) ^ (-Γ))
          / (1 - rhoC c) := by
        gcongr
        exact hLm.trans (mul_le_mul_of_nonneg_left hlog (by linarith))
    _ = (c + 1) / (1 - rhoC c) * ((D m : ℝ) ^ (-Γ) * Real.log (D m) ^ 2) * (N : ℝ) ^ 2 := by
        field_simp

/-- `4^{m-1} < D₀ ≤ N^ε` is possible only for `ε > 0`, because `D₀ ≥ 2`. -/
theorem pos_of_le_rpow' {m D₀ N : ℕ} {ε : ℝ} (hgt : 4 ^ (m - 1) < D₀)
    (hthin : (D₀ : ℝ) ≤ (N : ℝ) ^ ε) : 0 < ε := by
  have hD : (2 : ℝ) ≤ D₀ := by
    have : 1 ≤ 4 ^ (m - 1) := Nat.one_le_pow _ _ (by norm_num)
    exact_mod_cast (by omega : 2 ≤ D₀)
  have hN : 0 < N := by
    by_contra h0
    obtain rfl : N = 0 := by omega
    rw [Nat.cast_zero] at hthin
    linarith [Real.zero_rpow_le_one ε]
  refine lt_of_not_ge fun hε => ?_
  linarith [Real.rpow_le_one_of_one_le_of_nonpos (Nat.one_le_cast.2 hN) hε]

/-- The cost of a query is `O(D^q log D)`, in the given `D` (as in Corollary 31). -/
theorem CorollaryP.dominated_costQuery {c θ : ℝ} (hc : 10 < c) (hθ0 : 0 < θ) (hθ1 : θ < 0.9) :
    Dominated Sizes.SetUp (fun p => costQuery (levelsOf c p.m) p.m (switchOf θ p.m))
      fun p => (p.D₀ : ℝ) ^ qOf θ * Real.log p.D₀ :=
  ((Corollary31.query_cost hc hθ0 hθ1).comp Sizes.m fun _ hp => hp.m_pos).trans
    (by simpa only [pow_one] using padded_le (qOf θ) 1)

/-- The sharper Corollary 31, with the binomial tail and the pruned encodings. For `c > 10`,
`0 < θ < 0.9` and `ε (A_pruned(c) + Γ(c, θ)) < 1` there are `C` and `m₀` such that for all
`2 ≤ D ≤ N^ε` with `m = ⌈log_4 D⌉ ≥ m₀`, `L = ⌈cm⌉`, `t = ⌈θm⌉`: `N ≥ √K N₀`, the pruned
preprocessing cost is at most `C N² log² D / D^Γ`, and the query cost is at most `C D^q log D`. -/
theorem CorollaryP.costs {c θ ε : ℝ} (h : AdmissibleP c θ ε) :
    ∃ (C : ℝ) (m₀ : ℕ), 0 ≤ C ∧ ∀ D₀ N m : ℕ, 2 ≤ D₀ → (D₀ : ℝ) ≤ (N : ℝ) ^ ε →
      m = ⌈Real.logb 4 (D₀ : ℝ)⌉₊ → m₀ ≤ m →
      sqrtKN0 (levelsOf c m) m ≤ N ∧
      cost8p (levelsOf c m) m (switchOf θ m) N
        ≤ C * ((N : ℝ) ^ 2 * Real.log (D₀ : ℝ) ^ 2 / (D₀ : ℝ) ^ GammaOf c θ) ∧
      costQuery (levelsOf c m) m (switchOf θ m) ≤ C * ((D₀ : ℝ) ^ qOf θ * Real.log (D₀ : ℝ)) := by
  have hc := h.c_gt
  have hθ0 := h.θ_pos
  have hθ1 := h.θ_lt
  rcases le_or_gt ε 0 with hε0 | hε0
  · refine ⟨0, 0, le_rfl, fun D₀ N m hD hDN hm _ => ?_⟩
    exact absurd (pos_of_le_rpow' (Corollary26.setting_up D₀ m hD hm).2.2 hDN) hε0.not_gt
  obtain ⟨m₁, hkey⟩ := eq_10p h hε0
  obtain ⟨Cq, hCq, hq⟩ := CorollaryP.dominated_costQuery hc hθ0 hθ1
  obtain ⟨Cp, hCp, hp⟩ := padded_le (-GammaOf c θ) 2
  have hgap : 0 < 1 - rhoC c := sub_pos.2 (rhoC_lt_one hc)
  have h1θ : 0 < 1 - θ := by linarith
  set k₁ := 2 * (c + 1) * (1 / (1 - rhoC c) * (2 / (1 - θ)))
  set k₂ := (c + 1) / (1 - rhoC c)
  have hk₁ : 0 ≤ k₁ := by positivity
  have hk₂ : 0 ≤ k₂ := div_nonneg (by linarith) hgap.le
  have hΓ := GammaOf_pos hc hθ0 hθ1
  refine ⟨max (Cp * (k₁ + k₂)) Cq, max m₁ ⌈2 / (1 - θ)⌉₊, le_max_of_le_right hCq,
    fun D₀ N m hD hDN hm hm₀ => ?_⟩
  have hsetup : Sizes.SetUp ⟨D₀, N, m⟩ := ⟨hD, hm⟩
  have hm1 : 1 ≤ m := hsetup.m_pos
  have hkeym := hkey m (le_of_max_le_left hm₀) D₀ N hsetup.gt hDN
  have hm2 : 2 ≤ (1 - θ) * m := by
    have := Nat.ceil_le.1 (le_of_max_le_right hm₀)
    rwa [div_le_iff₀ h1θ, mul_comm] at this
  have hD1 : 1 ≤ (D m : ℝ) ^ GammaOf c θ := Real.one_le_rpow (one_le_cast_D m) hΓ.le
  have hD₀ : (2 : ℝ) ≤ D₀ := by exact_mod_cast hD
  have hlogD₀ : 0 ≤ Real.log (D₀ : ℝ) := Real.log_nonneg (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · calc sqrtKN0 (levelsOf c m) m ≤ sqrtKN0 (levelsOf c m) m * (D m : ℝ) ^ GammaOf c θ :=
          le_mul_of_one_le_right (sqrtKN0_pos (by have := ten_mul_le_levelsOf hc m; omega)).le
            hD1
      _ ≤ N := hkeym
  · have hpad : (D m : ℝ) ^ (-GammaOf c θ) * Real.log (D m) ^ 2
        ≤ Cp * ((D₀ : ℝ) ^ (-GammaOf c θ) * Real.log D₀ ^ 2) := hp ⟨D₀, N, m⟩ hsetup
    have h1 := first_term_le hc hθ0 hθ1 hm1 hm2 N
    have h2 := second_term_le hc hm1 hkeym
    have hR : 0 ≤ (D₀ : ℝ) ^ (-GammaOf c θ) * Real.log D₀ ^ 2 := by positivity
    have heq : (N : ℝ) ^ 2 * Real.log (D₀ : ℝ) ^ 2 / (D₀ : ℝ) ^ GammaOf c θ
        = (D₀ : ℝ) ^ (-GammaOf c θ) * Real.log D₀ ^ 2 * (N : ℝ) ^ 2 := by
      rw [Real.rpow_neg (by linarith)]
      field_simp
    rw [heq]
    calc cost8p (levelsOf c m) m (switchOf θ m) N
        ≤ k₁ * ((D m : ℝ) ^ (-GammaOf c θ) * Real.log (D m) ^ 2) * (N : ℝ) ^ 2
          + k₂ * ((D m : ℝ) ^ (-GammaOf c θ) * Real.log (D m) ^ 2) * (N : ℝ) ^ 2 :=
          add_le_add h1 h2
      _ = (k₁ + k₂) * ((D m : ℝ) ^ (-GammaOf c θ) * Real.log (D m) ^ 2) * (N : ℝ) ^ 2 := by ring
      _ ≤ (k₁ + k₂) * (Cp * ((D₀ : ℝ) ^ (-GammaOf c θ) * Real.log D₀ ^ 2)) * (N : ℝ) ^ 2 := by
          gcongr
      _ = Cp * (k₁ + k₂) * ((D₀ : ℝ) ^ (-GammaOf c θ) * Real.log D₀ ^ 2 * (N : ℝ) ^ 2) := by
          ring
      _ ≤ max (Cp * (k₁ + k₂)) Cq
            * ((D₀ : ℝ) ^ (-GammaOf c θ) * Real.log D₀ ^ 2 * (N : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · calc costQuery (levelsOf c m) m (switchOf θ m)
        ≤ Cq * ((D₀ : ℝ) ^ qOf θ * Real.log (D₀ : ℝ)) := hq ⟨D₀, N, m⟩ hsetup
      _ ≤ max (Cp * (k₁ + k₂)) Cq * ((D₀ : ℝ) ^ qOf θ * Real.log (D₀ : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-! ### The numbers for `c = 22`, `θ = 29/250` -/

private lemma log_221_250 : Real.log (221 / 250) ∈ Set.Icc (-0.1232982164) (-0.1232982163) :=
  ⟨le_trans (by numerics) (log_mem 0 6).1, (log_mem 0 6).2.trans (by numerics)⟩

private lemma log_5279_250 : Real.log (5279 / 250) ∈ Set.Icc 3.050031045 3.050031049 :=
  ⟨le_trans (by numerics) (log_mem 4 8).1, (log_mem 4 8).2.trans (by numerics)⟩

private lemma log_21 : Real.log 21 ∈ Set.Icc 3.044522436 3.044522440 :=
  ⟨le_trans (by numerics) (log_mem 4 8).1, (log_mem 4 8).2.trans (by numerics)⟩

private lemma log_9 : Real.log 9 ∈ Set.Icc 2.197224576 2.197224579 :=
  ⟨le_trans (by numerics) (log_mem 3 6).1, (log_mem 3 6).2.trans (by numerics)⟩

private lemma log_22 : Real.log 22 ∈ Set.Icc 3.091042452 3.091042455 :=
  ⟨le_trans (by numerics) (log_mem 4 8).1, (log_mem 4 8).2.trans (by numerics)⟩

private lemma log_3 : Real.log 3 ∈ Set.Icc 1.098612288 1.098612290 :=
  ⟨le_trans (by numerics) (log_mem 2 8).1, (log_mem 2 8).2.trans (by numerics)⟩

private lemma log_4 : Real.log 4 ∈ Set.Icc 1.3862943606 1.3862943616 := by
  rw [Real.log_four]
  exact ⟨by linarith [Real.log_two_gt_d9], by linarith [Real.log_two_lt_d9]⟩

/-- `Γ ln 4` at `c = 22`, `θ = 29/250`. -/
private lemma GammaOf_22_eq :
    GammaOf 22 (29 / 250) * Real.log 4
      = 221 / 250 * Real.log (221 / 250) + 5279 / 250 * Real.log (5279 / 250)
        - 21 * Real.log 21 - 29 / 250 * Real.log 9 := by
  rw [GammaOf_mul_log_four (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- `Γ(22, 29/250) > 0.07618` (the value is `0.0761820…`). -/
theorem GammaOf_22 : 0.07618 < GammaOf 22 (29 / 250) := by
  refine lt_of_mul_lt_mul_right ?_ log_four_pos.le
  rw [GammaOf_22_eq]
  have h1 := log_221_250; have h2 := log_5279_250; have h3 := log_21; have h4 := log_9
  have h5 := log_4
  simp only [Set.mem_Icc] at *
  nlinarith

/-- `Γ(22, 29/250) < 0.0762`. -/
theorem GammaOf_22_lt : GammaOf 22 (29 / 250) < 0.0762 := by
  refine lt_of_mul_lt_mul_right ?_ log_four_pos.le
  rw [GammaOf_22_eq]
  have h1 := log_221_250; have h2 := log_5279_250; have h3 := log_21; have h4 := log_9
  have h5 := log_4
  simp only [Set.mem_Icc] at *
  nlinarith

/-- `A_pruned(22) < 18.10932` (the value is `18.1093137…`). -/
theorem Apruned_22 : Apruned 22 < 18.10932 := by
  refine lt_of_mul_lt_mul_right ?_ log_four_pos.le
  rw [Apruned_mul_log_four (by norm_num)]
  have h1 := log_22; have h2 := log_21; have h3 := log_3; have h5 := log_4
  simp only [Set.mem_Icc] at *
  norm_num
  nlinarith

/-- `q(29/250) < 0.44274` (the value is `0.4427320…`). -/
theorem qOf_29_250 : qOf (29 / 250) < 0.44274 :=
  lt_of_le_of_lt (qOf_le (-3) (r := 0.442735)) (by norm_num)

/-- The parameters `c = 22`, `θ = 29/250`, `ε = 0.05498` are admissible. -/
theorem admissibleP_22 : AdmissibleP 22 (29 / 250) 0.05498 where
  c_gt := by norm_num
  θ_pos := by norm_num
  θ_lt := by norm_num
  thin := by
    have h1 := Apruned_22
    have h2 := GammaOf_22_lt
    nlinarith

/-- The parameters `c = 22`, `θ = 29/250`, `ε = 5/91` are admissible. -/
theorem admissibleP_5_91 : AdmissibleP 22 (29 / 250) (5 / 91) where
  c_gt := by norm_num
  θ_pos := by norm_num
  θ_lt := by norm_num
  thin := by
    have h1 := Apruned_22
    have h2 := GammaOf_22_lt
    nlinarith

end ThreeSumApsp
