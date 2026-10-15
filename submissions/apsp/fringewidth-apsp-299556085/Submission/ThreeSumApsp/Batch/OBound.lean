/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Batch.OParams
public import Submission.ThreeSumApsp.Batch.Numbers
public import Submission.ThreeSumApsp.Filter2.Asymp
public import Submission.ThreeSumApsp.Pruned.Within8p

/-!
# An eventual bound on the time of the batched oracle

`oTimeF_le`: eventually, for `U ≤ c n^κ` and `p ≤ Pmax`, the batched oracle at `s = sOf n` takes at
most `n^{2.99556082}` steps.
-/

@[expose] public section

open Filter

namespace Light.Batch

open ThreeSumApsp Light.Sec4

/-! ## The parameters, in the naturals -/

section nat

variable {n s p : ℕ}

theorem one_le_oM (hs : 1 ≤ s) (hp : 1 ≤ p) : 1 ≤ oM s p :=
  Nat.clog_pos (by norm_num) (by nlinarith)

theorem four_mul_le_oD (s p : ℕ) : 4 * s * p ≤ oD s p := Nat.le_pow_clog (by norm_num) _

theorem oD_le (hs : 1 ≤ s) (hp : 1 ≤ p) : oD s p ≤ 16 * s * p := by
  have h1 := Nat.pow_pred_clog_lt_self (b := 4) (by norm_num) (x := 4 * s * p) (by nlinarith)
  have h2 := one_le_oM hs hp
  unfold oD oM
  unfold oM at h2
  obtain ⟨j, hj⟩ : ∃ j, Nat.clog 4 (4 * s * p) = j + 1 := ⟨_, (Nat.succ_pred_eq_of_pos h2).symm⟩
  rw [hj] at h1 ⊢
  simp only [Nat.pred_succ] at h1
  rw [pow_succ, show 16 * s * p = 16 * (s * p) by ring]
  rw [show 4 * s * p = 4 * (s * p) by ring] at h1
  omega

theorem oL_eq (s p : ℕ) : oL s p = levelsOf 20 (oM s p) := by
  unfold levelsOf oL
  rw [show (20 : ℝ) * (oM s p : ℝ) = ((20 * oM s p : ℕ) : ℝ) by push_cast; ring, Nat.ceil_natCast]

theorem oT_eq (s p : ℕ) : oT s p = switchOf (56569 / 500000) (oM s p) := by
  unfold switchOf oT
  set m := oM s p
  set a := (56569 * m + 500000 - 1) / 500000
  have h1 := Nat.div_add_mod (56569 * m + 500000 - 1) 500000
  have h2 := Nat.mod_lt (56569 * m + 500000 - 1) (show 0 < 500000 by norm_num)
  refine le_antisymm ?_ (Nat.ceil_le.2 ?_)
  · rcases Nat.eq_zero_or_pos a with h0 | hpos
    · rw [h0]; exact Nat.zero_le _
    · have : ((a - 1 : ℕ) : ℝ) < 56569 / 500000 * (m : ℝ) := by
        have : 500000 * (a - 1) < 56569 * m := by omega
        have : ((500000 * (a - 1) : ℕ) : ℝ) < ((56569 * m : ℕ) : ℝ) := by exact_mod_cast this
        push_cast at this
        linarith
      have := Nat.lt_ceil.2 this
      omega
  · have : 56569 * m ≤ 500000 * a := by omega
    have : ((56569 * m : ℕ) : ℝ) ≤ ((500000 * a : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this
    linarith

theorem oT_le (s p : ℕ) : oT s p ≤ oM s p := by
  rw [oT_eq]; exact switchOf_le (by norm_num) _

theorem oProd_mul_le (_hs : 1 ≤ s) : oProd n s * s ≤ n + s - 1 := Nat.div_mul_le_self _ _

theorem le_oProd_mul (hs : 1 ≤ s) : n ≤ oProd n s * s := by
  have h1 := Nat.div_add_mod (n + s - 1) s
  have h2 := Nat.mod_lt (n + s - 1) (show 0 < s by omega)
  unfold oProd
  rw [Nat.ceilDiv_eq_add_pred_div, mul_comm]
  omega

theorem oDig_sq_le (hp : 1 ≤ p) : oDig p * oDig p ≤ 3 * p := by
  unfold oDig
  have h := Nat.sqrt_le (p - 1)
  set r := Nat.sqrt (p - 1)
  have : r ≤ r * r := Nat.le_mul_self r
  have hp1 : r * r + 1 ≤ p := by omega
  nlinarith

theorem le_oDig_sq (p : ℕ) : p ≤ oDig p * oDig p := by
  unfold oDig
  have h := Nat.lt_succ_sqrt (p - 1)
  simp only [Nat.succ_eq_add_one] at h
  omega

theorem one_le_oDig (p : ℕ) : 1 ≤ oDig p := Nat.succ_pos _

theorem oNP_le (n s p : ℕ) (h0 : 1 ≤ oN0 s p) : oNP n s p ≤ n * oDig p + 2 * oN0 s p := by
  unfold oNP oNb
  rw [Nat.ceilDiv_eq_add_pred_div, add_mul, one_mul]
  have := Nat.div_mul_le_self (n * oDig p + oN0 s p - 1) (oN0 s p)
  omega

theorem one_le_oN0 (s p : ℕ) : 1 ≤ oN0 s p := Nat.one_le_pow _ _ (by norm_num)

theorem oKK_le (s p : ℕ) : oKK s p ≤ (oL s p).choose (oM s p) := Nat.sqrt_le _

theorem choose_lt (s p : ℕ) : (oL s p).choose (oM s p) < (oK0 s p + 1) * (oK0 s p + 1) :=
  Nat.lt_succ_sqrt _

theorem one_le_choose (s p : ℕ) : 1 ≤ (oL s p).choose (oM s p) :=
  Nat.choose_pos (by unfold oL; omega)

theorem one_le_oK0 (s p : ℕ) : 1 ≤ oK0 s p := by
  unfold oK0
  exact Nat.le_sqrt.2 (by simpa using one_le_choose s p)

theorem one_le_oKK (s p : ℕ) : 1 ≤ oKK s p := by
  have := one_le_oK0 s p
  unfold oKK; nlinarith

theorem oBat_mul_le (n s p : ℕ) : oBat n s p * oKK s p ≤ oProd n s + oKK s p - 1 := by
  unfold oBat
  rw [Nat.ceilDiv_eq_add_pred_div]
  exact Nat.div_mul_le_self _ _

end nat

/-! ## Exponents -/

section real

/-- `1 + ν ≤ 10^9 e^{ν/10^9}`. -/
theorem one_add_le_exp (ν : ℝ) : 1 + ν ≤ 10 ^ 9 * Real.exp (ν / 10 ^ 9) := by
  have := Real.add_one_le_exp (ν / 10 ^ 9)
  nlinarith

/-- A polylogarithmic factor and a constant are absorbed by `n^{3·10^{-8}}`. -/
theorem absorb {ν a K : ℝ} (hν : 0 ≤ ν) (hK : 0 ≤ K) (ha : a ≤ 2.9955608 * ν + 100) :
    K * (1 + ν) ^ 2 * Real.exp a ≤ K * 10 ^ 18 * Real.exp 100 * Real.exp (2.99556081 * ν) := by
  have h1 := one_add_le_exp ν
  have h2 : (1 + ν) ^ 2 ≤ (10 ^ 9 * Real.exp (ν / 10 ^ 9)) ^ 2 := by gcongr
  calc K * (1 + ν) ^ 2 * Real.exp a
      ≤ K * (10 ^ 9 * Real.exp (ν / 10 ^ 9)) ^ 2 * Real.exp a := by gcongr
    _ = K * 10 ^ 18 * Real.exp (ν / 10 ^ 9 + ν / 10 ^ 9 + a) := by
        rw [Real.exp_add, Real.exp_add]; ring
    _ ≤ K * 10 ^ 18 * Real.exp (100 + 2.99556081 * ν) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) (by positivity)
    _ = _ := by rw [Real.exp_add]; ring

theorem log_two_mem : 0.6931471803 < Real.log 2 ∧ Real.log 2 < 0.6931471808 :=
  ⟨Real.log_two_gt_d9, Real.log_two_lt_d9⟩

/-- The constraints on `ν = ln n`, `x = ln s`, `y = ln p`, `d = ln D`. -/
structure Ctx (ν x y d : ℝ) : Prop where
  ν_ge : 20000 ≤ ν
  x_nonneg : 0 ≤ x
  x_ge : 0.0336175 * ν ≤ Real.log 2 + x
  x_le : x ≤ Real.log 2 + 0.0336175 * ν
  y_nonneg : 0 ≤ y
  y_le : y ≤ x + 0.000000001 * ν
  d_ge : 2 * Real.log 2 + x + y ≤ d
  d_le : d ≤ 4 * Real.log 2 + x + y

namespace Ctx

variable {ν x y d : ℝ} (h : Ctx ν x y d)
include h

theorem ν_nonneg : 0 ≤ ν := by linarith [h.ν_ge]

theorem m_le {m : ℝ} (hm : m * (2 * Real.log 2) = d) : m ≤ 3 * (1 + ν) := by
  have := log_two_mem
  have := h.d_le; have := h.x_le; have := h.y_le; have := h.ν_ge
  nlinarith

theorem d_le' : d ≤ 3 * (1 + ν) := by
  have := log_two_mem
  have := h.d_le; have := h.x_le; have := h.y_le; have := h.ν_ge
  linarith

/-- The boxes of the preprocessing. -/
theorem boxes {BK m tl NP ct : ℝ} (_hBK0 : 0 ≤ BK) (hBK : BK ≤ 4 * Real.exp (ν - x))
    (hm0 : 0 ≤ m) (hm : m * (2 * Real.log 2) = d) (hct : 0 ≤ ct) (htl0 : 0 ≤ tl)
    (htl : tl ≤ ct * Real.exp (-0.0660254 * d)) (hNP0 : 0 ≤ NP)
    (hNP : NP ≤ 6 * Real.exp (ν + y / 2)) :
    BK * (20 * m) * (m + 1) * tl * NP ^ 2
      ≤ 34560 * ct * 10 ^ 18 * Real.exp 100 * Real.exp (2.99556081 * ν) := by
  have hm3 := h.m_le hm
  have hν := h.ν_nonneg
  calc BK * (20 * m) * (m + 1) * tl * NP ^ 2
      ≤ (4 * Real.exp (ν - x)) * (20 * (3 * (1 + ν))) * (4 * (1 + ν))
          * (ct * Real.exp (-0.0660254 * d)) * (6 * Real.exp (ν + y / 2)) ^ 2 := by
        gcongr; linarith
    _ = 34560 * ct * (1 + ν) ^ 2
          * Real.exp (ν - x + -0.0660254 * d + (ν + y / 2) + (ν + y / 2)) := by
        simp only [Real.exp_add, Real.exp_sub]; ring
    _ ≤ _ := by
        refine absorb hν (by positivity) ?_
        have := log_two_mem
        have := h.d_ge; have := h.x_ge; have := h.y_le; have := h.ν_ge; have := h.y_nonneg
        linarith

/-- The pruned encodings of the preprocessing. -/
theorem encodings {BK m NP N0 : ℝ} (hBK0 : 0 ≤ BK) (hBK : BK ≤ 4 * Real.exp (ν - x))
    (hm0 : 0 ≤ m) (hm : m * (2 * Real.log 2) = d) (hNP0 : 0 ≤ NP)
    (hNP : NP ≤ 6 * Real.exp (ν + y / 2)) (hN00 : 0 ≤ N0) (hN0 : N0 ≤ Real.exp (15.05716 * d)) :
    m * BK * NP * N0 ≤ 72 * 10 ^ 18 * Real.exp 100 * Real.exp (2.99556081 * ν) := by
  have hm3 := h.m_le hm
  have hν := h.ν_nonneg
  calc m * BK * NP * N0
      ≤ (3 * (1 + ν)) * (4 * Real.exp (ν - x)) * (6 * Real.exp (ν + y / 2))
          * Real.exp (15.05716 * d) := by
        gcongr
    _ ≤ (3 * (1 + ν) ^ 2) * (4 * Real.exp (ν - x)) * (6 * Real.exp (ν + y / 2))
          * Real.exp (15.05716 * d) := by
        gcongr; nlinarith
    _ = 72 * (1 + ν) ^ 2 * Real.exp (ν - x + (ν + y / 2) + 15.05716 * d) := by
        simp only [Real.exp_add, Real.exp_sub]; ring
    _ ≤ _ := by
        refine absorb hν (by positivity) ?_
        have := log_two_mem
        have := h.d_le; have := h.x_le; have := h.y_le; have := h.ν_ge; have := h.y_nonneg
        linarith

/-- The queries. -/
theorem queries {BK Q : ℝ} (_hBK0 : 0 ≤ BK) (hBK : BK ≤ 4 * Real.exp (ν - x)) (hQ0 : 0 ≤ Q)
    (hQ : Q ≤ Real.exp (0.4339741 * d) * d) :
    BK * Real.exp ν ^ 2 * Q ≤ 12 * 10 ^ 18 * Real.exp 100 * Real.exp (2.99556081 * ν) := by
  have hd := h.d_le'
  have hν := h.ν_nonneg
  have hd0 : 0 ≤ d := by have := log_two_mem; have := h.d_ge; have := h.y_nonneg; linarith [h.x_nonneg]
  have hQ' : Q ≤ Real.exp (0.4339741 * d) * (3 * (1 + ν)) := hQ.trans (by gcongr)
  calc BK * Real.exp ν ^ 2 * Q
      ≤ (4 * Real.exp (ν - x)) * Real.exp ν ^ 2 * (Real.exp (0.4339741 * d) * (3 * (1 + ν))) := by
        gcongr
    _ ≤ (4 * Real.exp (ν - x)) * Real.exp ν ^ 2 * (Real.exp (0.4339741 * d) * (3 * (1 + ν) ^ 2)) := by
        gcongr; nlinarith
    _ = 12 * (1 + ν) ^ 2 * Real.exp (ν - x + ν + ν + 0.4339741 * d) := by
        simp only [Real.exp_add, Real.exp_sub]; ring
    _ ≤ _ := by
        refine absorb hν (by positivity) ?_
        have := log_two_mem
        have := h.d_le; have := h.x_ge; have := h.y_le; have := h.ν_ge; have := h.y_nonneg
        linarith

/-- Everything else is below `n³/s`, up to a constant and a factor `1 + ν`. -/
theorem small {a : ℝ} (ha : a ≤ 3 * ν - x) {K : ℝ} (hK : 0 ≤ K) :
    K * (1 + ν) * Real.exp a ≤ K * 10 ^ 18 * Real.exp 100 * Real.exp (2.99556081 * ν) := by
  have hν := h.ν_nonneg
  calc K * (1 + ν) * Real.exp a ≤ K * (1 + ν) ^ 2 * Real.exp a := by
        gcongr; nlinarith
    _ ≤ _ := by
        refine absorb hν hK ?_
        have := log_two_mem
        have := h.x_ge; have := h.ν_ge
        linarith

end Ctx

end real

/-! ## The parameters, in the reals -/

section bridge

theorem cast_pow_eq_exp (b k : ℕ) (hb : 0 < b) :
    ((b ^ k : ℕ) : ℝ) = Real.exp ((k : ℝ) * Real.log b) := by
  rw [Real.exp_nat_mul, Real.exp_log (by exact_mod_cast hb)]; push_cast; rfl

/-- `N₀ = 3^{19 m} ≤ D^{15.05716}`. -/
theorem cast_N0_le (m : ℕ) :
    ((3 ^ (20 * m - m) : ℕ) : ℝ) ≤ Real.exp (15.05716 * ((m : ℝ) * Real.log 4)) := by
  rw [cast_pow_eq_exp 3 _ (by norm_num), show 20 * m - m = 19 * m by omega]
  apply Real.exp_le_exp.2
  have hb := bExp_B
  rw [div_lt_iff₀ log_four_pos] at hb
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  push_cast
  nlinarith

/-- `K = binom(20 m, m) ≤ 2 D^{2.9}`. -/
theorem cast_K_le {m : ℕ} (hm : 1 ≤ m) :
    ((levelsOf 20 m).choose m : ℝ) ≤ 2 * Real.exp (2.9 * ((m : ℝ) * Real.log 4)) := by
  have h := K_le_exp (c := 20) (by norm_num) hm
  have hk := kappa_B
  rw [div_lt_iff₀ log_four_pos, PrunedAux.mul_entropy_inv (by norm_num)] at hk
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num))
  have := mul_le_mul_of_nonneg_left hk.le hm0
  linarith

/-- The binomial tail: `tail/M ≤ ct D^{-0.0660254}`. -/
theorem tail_le {m : ℕ} (hm : 3 ≤ m) :
    tailBeta (levelsOf 20 m) m (switchOf (56569 / 500000) m) / (ThreeSumApsp.M (levelsOf 20 m) m : ℝ)
      ≤ 1 / (1 - rhoC 20) * (2 / (1 - 56569 / 500000))
        * Real.exp (-0.0660254 * ((m : ℝ) * Real.log 4)) := by
  have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have h := tail_div_M_le (c := 20) (θ := 56569 / 500000) (by norm_num) (by norm_num) (by norm_num)
    (m := m) (by omega) (by nlinarith)
  refine h.trans ?_
  rw [cast_D_rpow]
  have hg := GammaOf_B
  have hm0 : (0 : ℝ) ≤ m * Real.log 4 := mul_nonneg (by positivity) log_four_pos.le
  have hc : 0 ≤ 1 / (1 - rhoC 20) * (2 / (1 - 56569 / 500000 : ℝ)) := by
    unfold rhoC; norm_num
  gcongr

/-- The pruned encodings: `retained/√M ≤ 1.9 √K N₀`. -/
theorem retained_div_le {m : ℕ} :
    (retained (levelsOf 20 m) m : ℝ) / Real.sqrt (ThreeSumApsp.M (levelsOf 20 m) m : ℝ)
      ≤ 1.9 * sqrtKN0 (levelsOf 20 m) m := by
  set L := levelsOf 20 m
  have hL10 : 10 * m ≤ L := ten_mul_le_levelsOf (by norm_num) m
  have hρ := Corollary31.rho_lt (c := 20) (by norm_num) m
  have hρ' : rho L m < 9 / 19 := by unfold rhoC at hρ; norm_num at hρ; exact hρ
  have hpos := sqrtKN0_pos (L := L) (m := m) (by omega)
  have hret := retained_le hL10
  rw [sqrt_M_eq L m (by omega), div_le_iff₀ hpos]
  have hM := sqrtKN0_sq L m
  have hgap : (10 : ℝ) / 19 ≤ 1 - rho L m := by linarith
  have hM0 : (0 : ℝ) ≤ (ThreeSumApsp.M L m : ℝ) := Nat.cast_nonneg _
  calc (retained L m : ℝ) ≤ (ThreeSumApsp.M L m : ℝ) / (1 - rho L m) := hret
    _ ≤ (ThreeSumApsp.M L m : ℝ) / (10 / 19) := div_le_div_of_nonneg_left hM0 (by norm_num) hgap
    _ = 1.9 * sqrtKN0 L m * sqrtKN0 L m := by rw [← hM]; ring

end bridge

/-! ## The time, for one `n`, `s`, `p` -/

section assembly

/-- The bookkeeping part of the time (without the constant `A`). -/
def oBook (n U s p : ℕ) : ℕ :=
  n * n * (Nat.log 2 (U + 1) + 2) + p + oDig p * oDig p + oNP n s p + n * oDig p
    + (oL s p).choose (oM s p) + 4 ^ oL s p
    + oBat n s p * (oKK s p * oNP n s p * oD s p + oKK s p * n * oDig p * (s + 1)
        + oKK s p * n * n + 1) + 1

theorem cast_oTimeF_eq {A n U s p : ℕ} (hp : p ≠ 0) :
    (oTimeF A n U s p : ℝ) = (A : ℝ) * (oBook n U s p : ℝ)
      + (oBat n s p : ℝ) * (tPreCore cShared30 (oPar n s p) (oT s p) : ℝ)
      + ((oBat n s p * oKK s p : ℕ) : ℝ) * (n : ℝ) ^ 2
        * (tQueryAt (oL s p) (oM s p) (oT s p) : ℝ) := by
  unfold oTimeF oBook
  rw [if_neg hp]
  push_cast
  ring

/-- The constant `ct` of the binomial tail. -/
noncomputable def ctB : ℝ := 1 / (1 - rhoC 20) * (2 / (1 - 56569 / 500000))

theorem ctB_nonneg : 0 ≤ ctB := by unfold ctB rhoC; norm_num

/-- The constant of `oTimeF_le_of`. -/
noncomputable def Kt (A C1 C2 Cq a0 κ' : ℝ) : ℝ :=
  (A * (a0 + κ' + 65) + C1 * (34560 * ctB + 76 * 72) + C2 * Cq * 12) * 10 ^ 18 * Real.exp 100

set_option maxHeartbeats 400000 in
theorem oTimeF_le_of {A n U s p : ℕ} {C1 C2 Cq a0 κ' : ℝ} (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (hCq : 0 ≤ Cq) (ha0 : 0 ≤ a0) (hκ : 0 ≤ κ')
    (hpre : ∀ (P : Sec2.Par) (t : ℕ), Hyp30 P t →
      (tPreCore cShared30 P t : ℝ) ≤ C1 * cost8p P.L P.m t P.N)
    (hq : ∀ (P : Sec2.Par) (t : ℕ), Hyp30 P t →
      (tQueryAt P.L P.m t : ℝ) ≤ C2 * costQuery P.L P.m t)
    (hcq : ∀ m : ℕ, 1 ≤ m → costQuery (levelsOf 20 m) m (switchOf (56569 / 500000) m)
      ≤ Cq * ((D m : ℝ) ^ qOf (56569 / 500000) * Real.log (D m)))
    (hn : 1 ≤ n) (hs : 1 ≤ s) (hsn : s ≤ n) (hp : 1 ≤ p)
    (hν : 20000 ≤ Real.log n) (hx1 : 0.0336175 * Real.log n ≤ Real.log 2 + Real.log s)
    (hx2 : Real.log s ≤ Real.log 2 + 0.0336175 * Real.log n)
    (hy : Real.log p ≤ Real.log s + 0.000000001 * Real.log n)
    (hG : (Nat.log 2 (U + 1) : ℝ) ≤ a0 + κ' * Real.log n) :
    (oTimeF A n U s p : ℝ) ≤ Kt A C1 C2 Cq a0 κ' * Real.exp (2.99556081 * Real.log n) := by
  have hp0 : p ≠ 0 := by omega
  set m := oM s p with hm_def
  have hm1 : 1 ≤ m := one_le_oM hs hp
  set ν := Real.log (n : ℝ) with hν_def
  set x := Real.log (s : ℝ) with hx_def
  set y := Real.log (p : ℝ) with hy_def
  set d := (m : ℝ) * Real.log 4 with hd_def
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hpr0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hne : (n : ℝ) = Real.exp ν := (Real.exp_log hn0).symm
  have hse : (s : ℝ) = Real.exp x := (Real.exp_log hs0).symm
  have hpe : (p : ℝ) = Real.exp y := (Real.exp_log hpr0).symm
  have hDe : (oD s p : ℝ) = Real.exp d := by
    show ((4 ^ m : ℕ) : ℝ) = _
    rw [cast_pow_eq_exp 4 m (by norm_num)]; push_cast; rfl
  have hl4 := Real.log_four
  have hD1 : 2 * Real.log 2 + x + y ≤ d := by
    have h := four_mul_le_oD s p
    have h' : ((4 * s * p : ℕ) : ℝ) ≤ (oD s p : ℝ) := by exact_mod_cast h
    rw [hDe] at h'
    push_cast at h'
    have := Real.log_le_log (by positivity) h'
    rw [Real.log_exp, Real.log_mul (by positivity) hpr0.ne', Real.log_mul (by norm_num) hs0.ne']
      at this
    linarith
  have hD2 : d ≤ 4 * Real.log 2 + x + y := by
    have h := oD_le hs hp
    have h' : (oD s p : ℝ) ≤ ((16 * s * p : ℕ) : ℝ) := by exact_mod_cast h
    rw [hDe] at h'
    push_cast at h'
    have := Real.log_le_log (Real.exp_pos _) h'
    rw [Real.log_exp, Real.log_mul (by positivity) hpr0.ne', Real.log_mul (by norm_num) hs0.ne',
      show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow] at this
    push_cast at this
    linarith
  have ctx : Ctx ν x y d := ⟨hν, Real.log_nonneg (by exact_mod_cast hs), hx1, hx2,
    Real.log_nonneg (by exact_mod_cast hp), hy, hD1, hD2⟩
  have hmd : (m : ℝ) * (2 * Real.log 2) = d := by rw [hd_def, hl4]
  have hl2 := log_two_mem
  have hm3 : 3 ≤ m := by
    have : (3 : ℝ) ≤ m := by
      by_contra hc
      have hc' := lt_of_not_ge hc
      nlinarith only [hmd, hD1, ctx.x_ge, ctx.y_nonneg, hν, hl2.1, hl2.2, hc']
    exact_mod_cast this
  -- the products
  set T := oProd n s with hT_def
  have hT1 : (T : ℝ) ≤ 2 * Real.exp (ν - x) := by
    have h1 : T * s ≤ n + s - 1 := oProd_mul_le hs
    have h2 : ((T * s : ℕ) : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by exact_mod_cast (by omega : T * s ≤ 2 * n)
    push_cast at h2
    rw [Real.exp_sub, ← hne, ← hse, mul_div_assoc', le_div_iff₀ hs0]
    exact h2
  have hT2 : Real.exp (ν - x) ≤ T := by
    have h1 : n ≤ T * s := le_oProd_mul hs
    have h2 : (n : ℝ) ≤ ((T * s : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h2
    rw [Real.exp_sub, ← hne, ← hse, div_le_iff₀ hs0]
    exact h2
  -- the digits
  set k := oDig p with hk_def
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hey : Real.exp (y / 2) ^ 2 = p := by
    rw [← Real.exp_nat_mul, hpe]; congr 1; push_cast; ring
  have hk2 : (k : ℝ) ≤ 2 * Real.exp (y / 2) := by
    have h : ((k * k : ℕ) : ℝ) ≤ ((3 * p : ℕ) : ℝ) := by exact_mod_cast oDig_sq_le hp
    push_cast at h
    nlinarith only [h, hey, Real.exp_pos (y / 2), hk0, hpr0]
  have hk1 : Real.exp (y / 2) ≤ k := by
    have h : ((p : ℕ) : ℝ) ≤ ((k * k : ℕ) : ℝ) := by exact_mod_cast le_oDig_sq p
    push_cast at h
    nlinarith only [h, hey, Real.exp_pos (y / 2), hk0, hpr0]
  -- the binomial coefficient
  have hL : oL s p = levelsOf 20 m := oL_eq s p
  set K := (oL s p).choose m with hK_def
  have hK : (K : ℝ) ≤ 2 * Real.exp (2.9 * d) := by
    rw [hK_def, hL]; exact cast_K_le hm1
  set K0 := oK0 s p with hK0_def
  set KK := oKK s p with hKK_def
  have hKK_K : KK ≤ K := oKK_le s p
  have hKK1 : 1 ≤ KK := one_le_oKK s p
  have hK01 : 1 ≤ K0 := one_le_oK0 s p
  have hKlt : K < (K0 + 1) * (K0 + 1) := choose_lt s p
  have hKKT : KK ≤ T := by
    have : (KK : ℝ) ≤ T := by
      have h1 : (KK : ℝ) ≤ K := by exact_mod_cast hKK_K
      have h2 : 2 * Real.exp (2.9 * d) ≤ Real.exp (ν - x) := by
        rw [show (2 : ℝ) * Real.exp (2.9 * d) = Real.exp (Real.log 2 + 2.9 * d) by
          rw [Real.exp_add, Real.exp_log (by norm_num)]]
        apply Real.exp_le_exp.2
        linarith only [ctx.x_le, ctx.y_le, ctx.ν_ge, hD2, hl2.1, hl2.2]
      linarith only [h1, h2, hK, hT2]
    exact_mod_cast this
  set B := oBat n s p with hB_def
  have hBKK : B * KK ≤ 2 * T := by
    have : B * KK ≤ T + KK - 1 := oBat_mul_le n s p
    omega
  have hBK : ((B * KK : ℕ) : ℝ) ≤ 4 * Real.exp (ν - x) := by
    have : ((B * KK : ℕ) : ℝ) ≤ ((2 * T : ℕ) : ℝ) := by exact_mod_cast hBKK
    push_cast at this ⊢
    linarith only [this, hT1]
  -- the rows
  set N0 := oN0 s p with hN0_def
  have hN0 : (N0 : ℝ) ≤ Real.exp (15.05716 * d) := cast_N0_le m
  have hN0nk : N0 ≤ n * k := by
    have : (N0 : ℝ) ≤ ((n * k : ℕ) : ℝ) := by
      push_cast
      refine hN0.trans ?_
      calc Real.exp (15.05716 * d) ≤ Real.exp (ν + y / 2) := by
            apply Real.exp_le_exp.2
            linarith only [ctx.x_le, ctx.y_le, ctx.ν_ge, hD2, hl2.1, hl2.2]
        _ = Real.exp ν * Real.exp (y / 2) := Real.exp_add _ _
        _ ≤ (n : ℝ) * k := by rw [← hne]; gcongr
    exact_mod_cast this
  set NP := oNP n s p with hNP_def
  have hNPle : NP ≤ 3 * (n * k) := by
    have : NP ≤ n * k + 2 * N0 := oNP_le n s p (one_le_oN0 s p)
    omega
  have hNP : (NP : ℝ) ≤ 6 * Real.exp (ν + y / 2) := by
    have h : ((NP : ℕ) : ℝ) ≤ ((3 * (n * k) : ℕ) : ℝ) := by exact_mod_cast hNPle
    push_cast at h
    rw [Real.exp_add, ← hne]
    calc (NP : ℝ) ≤ 3 * ((n : ℝ) * k) := h
      _ ≤ 3 * ((n : ℝ) * (2 * Real.exp (y / 2))) := by gcongr
      _ = _ := by ring
  -- the parameters of Theorem 30
  have hLr : ((oL s p : ℕ) : ℝ) = 20 * (m : ℝ) := by unfold oL; push_cast; ring
  have hNPge : 2 * N0 ≤ NP := by
    have h1 : 1 ≤ (n * k + N0 - 1) / N0 := by
      rw [Nat.le_div_iff_mul_le (one_le_oN0 s p)]
      have : 1 ≤ n * k := Nat.mul_pos (by omega) (one_le_oDig p)
      omega
    show 2 * N0 ≤ ((n * k) ⌈/⌉ N0 + 1) * N0
    rw [Nat.ceilDiv_eq_add_pred_div]
    exact Nat.mul_le_mul_right _ (by omega)
  have hsqK : Real.sqrt (K : ℝ) ≤ 2 * K0 := by
    have h1 : K ≤ (2 * K0) * (2 * K0) :=
      hKlt.le.trans (Nat.mul_le_mul (by omega) (by omega))
    have h2 : (K : ℝ) ≤ ((2 * K0 : ℕ) : ℝ) ^ 2 := by
      rw [sq]; exact_mod_cast h1
    calc Real.sqrt (K : ℝ) ≤ Real.sqrt (((2 * K0 : ℕ) : ℝ) ^ 2) := Real.sqrt_le_sqrt h2
      _ = 2 * K0 := by rw [Real.sqrt_sq (Nat.cast_nonneg _)]; push_cast; ring
  have hyp : Hyp30 (oPar n s p) (oT s p) := by
    refine ⟨hm1, ?_, oT_le s p, ?_⟩
    · show 10 * oM s p ≤ oL s p
      unfold oL; omega
    · show sqrtKN0 (oL s p) (oM s p) ≤ ((K0 * NP : ℕ) : ℝ)
      unfold sqrtKN0
      have h1 : ((2 * N0 : ℕ) : ℝ) ≤ (NP : ℝ) := by exact_mod_cast hNPge
      push_cast at h1 ⊢
      change Real.sqrt (K : ℝ) * (N0 : ℝ) ≤ _
      have hN00 : (0 : ℝ) ≤ N0 := Nat.cast_nonneg _
      calc Real.sqrt (K : ℝ) * (N0 : ℝ) ≤ (2 * K0) * (N0 : ℝ) := by gcongr
        _ = K0 * (2 * N0) := by ring
        _ ≤ K0 * NP := by gcongr
  -- the preprocessing
  obtain ⟨E, hE_def⟩ : ∃ E, E = Real.exp 100 * Real.exp (2.99556081 * ν) := ⟨_, rfl⟩
  set BK : ℝ := ((B * KK : ℕ) : ℝ) with hBK_def
  have hBK0 : 0 ≤ BK := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hNP0 : (0 : ℝ) ≤ NP := Nat.cast_nonneg _
  have hN00 : (0 : ℝ) ≤ N0 := Nat.cast_nonneg _
  obtain ⟨tl, htl_def⟩ : ∃ tl, tl = tailBeta (levelsOf 20 m) m (switchOf (56569 / 500000) m)
    / (ThreeSumApsp.M (levelsOf 20 m) m : ℝ) := ⟨_, rfl⟩
  have htl0 : 0 ≤ tl := htl_def ▸
    div_nonneg (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have htl : tl ≤ ctB * Real.exp (-0.0660254 * d) := htl_def ▸ tail_le hm3
  obtain ⟨R, hR_def⟩ : ∃ R, R = (retained (levelsOf 20 m) m : ℝ)
    / Real.sqrt (ThreeSumApsp.M (levelsOf 20 m) m : ℝ) := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by rw [hR_def]; positivity
  have hR : R ≤ 1.9 * (Real.sqrt (K : ℝ) * N0) := by
    rw [hR_def]
    refine (retained_div_le (m := m)).trans (le_of_eq ?_)
    unfold sqrtKN0 ThreeSumApsp.K ThreeSumApsp.N0
    rw [← hL]
    rfl
  have hcost : cost8p (oL s p) m (oT s p) (K0 * NP)
      = (20 * m) * (m + 1) * tl * ((K0 : ℝ) * NP) ^ 2 + (20 * m) * ((K0 : ℝ) * NP) * R := by
    rw [oT_eq, ← hm_def]
    unfold cost8p
    rw [hLr, hL, ← htl_def, Nat.cast_mul, mul_div_assoc, ← hR_def]
  have hpreB : (B : ℝ) * (tPreCore cShared30 (oPar n s p) (oT s p) : ℝ)
      ≤ C1 * ((34560 * ctB + 76 * 72) * 10 ^ 18 * E) := by
    have h1 := hpre _ _ hyp
    change (tPreCore cShared30 (oPar n s p) (oT s p) : ℝ) ≤ C1 * cost8p (oL s p) m (oT s p) (K0 * NP)
      at h1
    rw [hcost] at h1
    have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg _
    have hKK : ((KK : ℕ) : ℝ) = (K0 : ℝ) * K0 := by
      have : KK = K0 * K0 := rfl
      rw [this, Nat.cast_mul]
    have hbox := ctx.boxes hBK0 hBK hm0 hmd ctB_nonneg htl0 htl hNP0 hNP
    have henc := ctx.encodings hBK0 hBK hm0 hmd hNP0 hNP hN00 hN0
    have hK0sq : (B : ℝ) * K0 * Real.sqrt (K : ℝ) ≤ 2 * BK := by
      rw [hBK_def, Nat.cast_mul, hKK]
      calc (B : ℝ) * K0 * Real.sqrt (K : ℝ) ≤ (B : ℝ) * K0 * (2 * K0) := by gcongr
        _ = _ := by ring
    have hsK0 : 0 ≤ Real.sqrt (K : ℝ) := Real.sqrt_nonneg _
    have hfirst : (B : ℝ) * ((20 * m) * (m + 1) * tl * ((K0 : ℝ) * NP) ^ 2)
        = BK * (20 * m) * (m + 1) * tl * (NP : ℝ) ^ 2 := by
      rw [hBK_def, Nat.cast_mul, hKK]; ring
    have hsecond : (B : ℝ) * ((20 * m) * ((K0 : ℝ) * NP) * R)
        ≤ 76 * ((m : ℝ) * BK * NP * N0) := by
      calc (B : ℝ) * ((20 * m) * ((K0 : ℝ) * NP) * R)
          ≤ (B : ℝ) * ((20 * m) * ((K0 : ℝ) * NP) * (1.9 * (Real.sqrt (K : ℝ) * N0))) := by
            gcongr
        _ = 38 * ((m : ℝ) * NP * N0) * ((B : ℝ) * K0 * Real.sqrt (K : ℝ)) := by ring
        _ ≤ 38 * ((m : ℝ) * NP * N0) * (2 * BK) := by gcongr
        _ = _ := by ring
    calc (B : ℝ) * (tPreCore cShared30 (oPar n s p) (oT s p) : ℝ)
        ≤ (B : ℝ) * (C1 * ((20 * m) * (m + 1) * tl * ((K0 : ℝ) * NP) ^ 2
            + (20 * m) * ((K0 : ℝ) * NP) * R)) := by gcongr
      _ = C1 * ((B : ℝ) * ((20 * m) * (m + 1) * tl * ((K0 : ℝ) * NP) ^ 2)
            + (B : ℝ) * ((20 * m) * ((K0 : ℝ) * NP) * R)) := by ring
      _ ≤ C1 * (34560 * ctB * 10 ^ 18 * Real.exp 100 * Real.exp (2.99556081 * ν)
            + 76 * (72 * 10 ^ 18 * Real.exp 100 * Real.exp (2.99556081 * ν))) := by
          rw [hfirst]
          refine mul_le_mul_of_nonneg_left (add_le_add hbox (hsecond.trans ?_)) hC1
          linarith only [henc]
      _ = _ := by rw [hE_def]; ring
  -- the queries
  have hqB : BK * (n : ℝ) ^ 2 * (tQueryAt (oL s p) m (oT s p) : ℝ)
      ≤ C2 * Cq * (12 * 10 ^ 18 * E) := by
    have h1 := hq _ _ hyp
    change (tQueryAt (oL s p) m (oT s p) : ℝ) ≤ C2 * costQuery (oL s p) m (oT s p) at h1
    have h2 := hcq m hm1
    rw [← hL, ← oT_eq] at h2
    rw [cast_D_rpow, log_cast_D, ← hd_def] at h2
    have hq0 := qOf_B
    have hd0 : 0 ≤ d := by positivity
    have h3 : Real.exp (qOf (56569 / 500000) * d) * d ≤ Real.exp (0.4339741 * d) * d := by
      gcongr
    have hQ := ctx.queries hBK0 hBK (by positivity) le_rfl
    calc BK * (n : ℝ) ^ 2 * (tQueryAt (oL s p) m (oT s p) : ℝ)
        ≤ BK * (n : ℝ) ^ 2 * (C2 * (Cq * (Real.exp (0.4339741 * d) * d))) := by
          gcongr
          exact h1.trans (by gcongr; exact h2.trans (by gcongr))
      _ = C2 * Cq * (BK * Real.exp ν ^ 2 * (Real.exp (0.4339741 * d) * d)) := by rw [hne]; ring
      _ ≤ C2 * Cq * (12 * 10 ^ 18 * Real.exp 100 * Real.exp (2.99556081 * ν)) := by gcongr
      _ = _ := by rw [hE_def]; ring
  -- the bookkeeping
  obtain ⟨W, hW_def⟩ : ∃ W, W = (1 + ν) * Real.exp (3 * ν - x) := ⟨_, rfl⟩
  have hν0 : 0 ≤ ν := ctx.ν_nonneg
  have hx0 := ctx.x_nonneg
  have hy0 := ctx.y_nonneg
  have hW : ∀ a : ℝ, a ≤ 3 * ν - x → Real.exp a ≤ W := fun a ha => by
    rw [hW_def]
    calc Real.exp a ≤ 1 * Real.exp (3 * ν - x) := by rw [one_mul]; exact Real.exp_le_exp.2 ha
      _ ≤ _ := by gcongr; linarith only [hν0]
  have hW0 : 0 ≤ W := by rw [hW_def]; positivity
  have hxν : x ≤ ν / 2 := by linarith only [ctx.x_le, hν, hl2.2]
  have hyν : y ≤ ν / 4 := by linarith only [ctx.x_le, ctx.y_le, hν, hl2.2]
  have hdν : d ≤ ν / 10 := by linarith only [ctx.x_le, ctx.y_le, hν, hl2.2, hD2]
  have hbook : (oBook n U s p : ℝ) ≤ (a0 + κ' + 65) * W := by
    -- the batched part, in the naturals
    have hbat : B * (KK * NP * oD s p + KK * n * k * (s + 1) + KK * n * n + 1)
        ≤ (B * KK) * (NP * oD s p + n * k * (s + 1) + n * n + 1) := by
      have : B ≤ B * KK := Nat.le_mul_of_pos_right _ hKK1
      calc B * (KK * NP * oD s p + KK * n * k * (s + 1) + KK * n * n + 1)
          = B * KK * (NP * oD s p + n * k * (s + 1) + n * n) + B := by ring
        _ ≤ B * KK * (NP * oD s p + n * k * (s + 1) + n * n) + B * KK := by omega
        _ = _ := by ring
    have hch : (oL s p).choose m ≤ 4 ^ oL s p :=
      (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_left (by norm_num) _)
    have h4L : ((4 ^ oL s p : ℕ) : ℝ) = Real.exp (20 * d) := by
      rw [cast_pow_eq_exp 4 _ (by norm_num), hLr, hd_def]; push_cast; congr 1; ring
    have hle : (oBook n U s p : ℝ) ≤ (n : ℝ) * n * (Nat.log 2 (U + 1) + 2) + p + k * k + NP
        + n * k + 2 * ((4 ^ oL s p : ℕ) : ℝ)
        + BK * (NP * (oD s p : ℝ) + n * k * (s + 1) + n * n + 1) + 1 := by
      have h1 : ((B * (KK * NP * oD s p + KK * n * k * (s + 1) + KK * n * n + 1) : ℕ) : ℝ)
          ≤ (((B * KK) * (NP * oD s p + n * k * (s + 1) + n * n + 1) : ℕ) : ℝ) := by
        exact_mod_cast hbat
      have h2 : (((oL s p).choose m : ℕ) : ℝ) ≤ ((4 ^ oL s p : ℕ) : ℝ) := by exact_mod_cast hch
      have e1 : (oBook n U s p : ℝ) = (n : ℝ) * n * (Nat.log 2 (U + 1) + 2) + p + k * k + NP
          + n * k + (((oL s p).choose m : ℕ) : ℝ) + ((4 ^ oL s p : ℕ) : ℝ)
          + ((B * (KK * NP * oD s p + KK * n * k * (s + 1) + KK * n * n + 1) : ℕ) : ℝ) + 1 := by
        unfold oBook; push_cast; ring
      have e2 : (((B * KK) * (NP * oD s p + n * k * (s + 1) + n * n + 1) : ℕ) : ℝ)
          = BK * (NP * (oD s p : ℝ) + n * k * (s + 1) + n * n + 1) := by
        rw [hBK_def]; push_cast; ring
      rw [e1]; rw [e2] at h1
      linarith only [h1, h2]
    have hG' : (Nat.log 2 (U + 1) : ℝ) + 2 ≤ (a0 + κ' + 2) * (1 + ν) := by
      nlinarith only [hG, ha0, hκ, hν0]
    have hp1 : (p : ℝ) ≤ W := by rw [hpe]; exact hW _ (by linarith only [hyν, hxν, hν0])
    have hkk : (k : ℝ) * k ≤ 3 * W := by
      have h : ((k * k : ℕ) : ℝ) ≤ ((3 * p : ℕ) : ℝ) := by exact_mod_cast oDig_sq_le hp
      push_cast at h
      linarith only [h, hp1]
    have hnk : (n : ℝ) * k ≤ 2 * W := by
      calc (n : ℝ) * k ≤ Real.exp ν * (2 * Real.exp (y / 2)) := by rw [hne]; gcongr
        _ = 2 * Real.exp (ν + y / 2) := by rw [Real.exp_add]; ring
        _ ≤ 2 * W := by gcongr; exact hW _ (by linarith only [hyν, hxν, hν0])
    have hNPW : (NP : ℝ) ≤ 6 * W :=
      hNP.trans (by gcongr; exact hW _ (by linarith only [hyν, hxν, hν0]))
    have h4W : ((4 ^ oL s p : ℕ) : ℝ) ≤ W := by
      rw [h4L]; exact hW _ (by linarith only [hdν, hxν, hν0])
    have hnn : (n : ℝ) * n * (Nat.log 2 (U + 1) + 2) ≤ (a0 + κ' + 2) * W := by
      have hG0 : (0 : ℝ) ≤ (Nat.log 2 (U + 1) : ℝ) + 2 := by positivity
      calc (n : ℝ) * n * (Nat.log 2 (U + 1) + 2)
          ≤ Real.exp (2 * ν) * ((a0 + κ' + 2) * (1 + ν)) := by
            rw [hne, show 2 * ν = ν + ν by ring, Real.exp_add]; gcongr
        _ = (a0 + κ' + 2) * ((1 + ν) * Real.exp (2 * ν)) := by ring
        _ ≤ (a0 + κ' + 2) * W := by
            rw [hW_def]; gcongr; linarith only [hxν, hν0]
    have hbatW : BK * (NP * (oD s p : ℝ) + n * k * (s + 1) + n * n + 1) ≤ 48 * W := by
      have hs1 : (s : ℝ) + 1 ≤ 2 * Real.exp x := by
        rw [← hse]; have : (1 : ℝ) ≤ s := by exact_mod_cast hs
        linarith
      have hin : NP * (oD s p : ℝ) + n * k * (s + 1) + n * n + 1
          ≤ 6 * Real.exp (ν + y / 2) * Real.exp d
            + Real.exp ν * (2 * Real.exp (y / 2)) * (2 * Real.exp x) + Real.exp ν * Real.exp ν
            + 1 := by
        rw [hDe, ← hne]
        have hk2' := hk2
        gcongr
      calc BK * (NP * (oD s p : ℝ) + n * k * (s + 1) + n * n + 1)
          ≤ (4 * Real.exp (ν - x)) * (6 * Real.exp (ν + y / 2) * Real.exp d
            + Real.exp ν * (2 * Real.exp (y / 2)) * (2 * Real.exp x) + Real.exp ν * Real.exp ν
            + 1) := by gcongr
        _ = 24 * Real.exp (ν - x + (ν + y / 2) + d) + 16 * Real.exp (ν - x + ν + y / 2 + x)
            + 4 * Real.exp (ν - x + ν + ν) + 4 * Real.exp (ν - x) := by
            simp only [Real.exp_add, Real.exp_sub]; field_simp; ring_nf
        _ ≤ 24 * W + 16 * W + 4 * W + 4 * W := by
            gcongr <;> refine hW _ ?_ <;> linarith only [hyν, hxν, hdν, hν0, hx0]
        _ = 48 * W := by ring
    have h1W : (1 : ℝ) ≤ W := by
      have := hW 0 (by linarith only [hxν, hν0]); rwa [Real.exp_zero] at this
    nlinarith only [hle, hnn, hp1, hkk, hNPW, hnk, h4W, hbatW, h1W]
  -- the sum
  have hA : (A : ℝ) * (oBook n U s p : ℝ) ≤ A * (a0 + κ' + 65) * 10 ^ 18 * E := by
    have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg _
    have h1 : (A : ℝ) * (oBook n U s p : ℝ) ≤ A * (a0 + κ' + 65) * W := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hbook hA0
    have h2 := ctx.small (a := 3 * ν - x) le_rfl (K := A * (a0 + κ' + 65)) (by positivity)
    rw [hW_def] at h1
    rw [hE_def]
    linarith only [h1, h2]
  have hpre' : (oBat n s p : ℝ) * (tPreCore cShared30 (oPar n s p) (oT s p) : ℝ)
      ≤ C1 * ((34560 * ctB + 76 * 72) * 10 ^ 18 * E) := hpreB
  have hq' : ((oBat n s p * oKK s p : ℕ) : ℝ) * (n : ℝ) ^ 2
      * (tQueryAt (oL s p) (oM s p) (oT s p) : ℝ) ≤ C2 * Cq * (12 * 10 ^ 18 * E) := hqB
  rw [cast_oTimeF_eq hp0]
  have hK : Kt A C1 C2 Cq a0 κ' * Real.exp (2.99556081 * ν)
      = A * (a0 + κ' + 65) * 10 ^ 18 * E + C1 * ((34560 * ctB + 76 * 72) * 10 ^ 18 * E)
        + C2 * Cq * (12 * 10 ^ 18 * E) := by
    rw [hE_def, Kt]; ring
  rw [hK]
  linarith only [hA, hpre', hq']




end assembly

/-! ## The eventual bound -/

/-- A constant times `n^e` is eventually below `n^t`, for `e < t`. -/
theorem eventually_const_mul_rpow_le (K : ℝ) {e t : ℝ} (h : e < t) :
    ∀ᶠ n : ℕ in atTop, K * (n : ℝ) ^ e ≤ (n : ℝ) ^ t := by
  have hT : Tendsto (fun n : ℕ => (n : ℝ) ^ (t - e)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hT.eventually_ge_atTop K, eventually_ge_atTop 1] with n hK hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  calc K * (n : ℝ) ^ e ≤ (n : ℝ) ^ (t - e) * (n : ℝ) ^ e :=
        mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hn0.le _)
    _ = (n : ℝ) ^ t := by rw [← Real.rpow_add hn0]; ring_nf

/-- `log₂ (U + 1) ≤ a₀ + κ' ln n` along `U ≤ c n^κ`. -/
theorem log_le_of_le {c κ : ℝ} {n U : ℕ} (hn : 1 ≤ n) (hU : (U : ℝ) ≤ c * (n : ℝ) ^ κ) :
    (Nat.log 2 (U + 1) : ℝ) ≤ Real.log (2 * max c 1) / Real.log 2
      + max κ 0 / Real.log 2 * Real.log n := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hc1 : (1 : ℝ) ≤ max c 1 := le_max_right _ _
  have hκ0 : (0 : ℝ) ≤ max κ 0 := le_max_right _ _
  have hUc : (U : ℝ) ≤ max c 1 * (n : ℝ) ^ max κ 0 := by
    calc (U : ℝ) ≤ c * (n : ℝ) ^ κ := hU
      _ ≤ max c 1 * (n : ℝ) ^ κ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hn0.le _)
      _ ≤ max c 1 * (n : ℝ) ^ max κ 0 := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hn1 (le_max_left _ _)) (by linarith)
  have h1 : 1 ≤ max c 1 * (n : ℝ) ^ max κ 0 :=
    one_le_mul_of_one_le_of_one_le hc1 (Real.one_le_rpow hn1 hκ0)
  have h2 : ((2 ^ Nat.log 2 (U + 1) : ℕ) : ℝ) ≤ ((U + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  push_cast at h2
  have hpos : 0 < (n : ℝ) ^ max κ 0 := Real.rpow_pos_of_pos hn0 _
  have h3 : (Nat.log 2 (U + 1) : ℝ) * Real.log 2
      ≤ Real.log (2 * max c 1) + max κ 0 * Real.log n := by
    calc (Nat.log 2 (U + 1) : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ Nat.log 2 (U + 1)) := by
          rw [Real.log_pow]
      _ ≤ Real.log (2 * max c 1 * (n : ℝ) ^ max κ 0) :=
          Real.log_le_log (by positivity) (by linarith)
      _ = _ := by
          rw [Real.log_mul (by positivity) hpos.ne', Real.log_rpow hn0]
  refine (show (Nat.log 2 (U + 1) : ℝ)
      ≤ (Real.log (2 * max c 1) + max κ 0 * Real.log n) / Real.log 2 from
    (le_div_iff₀ hl).2 (by linarith)).trans_eq (by ring)

/-- **The batched oracle**: eventually, for `U ≤ c n^κ` and `p ≤ Pmax`, the oracle at `s = sOf n`
takes at most `n^{2.99556082}` steps. -/
theorem oTimeF_le (A : ℕ) (c κ : ℝ) : ∀ᶠ n : ℕ in Filter.atTop, ∀ U : ℕ,
    (U : ℝ) ≤ c * (n : ℝ) ^ κ → ∀ p : ℕ, p ≤ Light.Filter2.PmaxOf n →
      (oTimeF A n U (Light.Filter2.sOf n) p : ℝ) ≤ (n : ℝ) ^ (2.99556082 : ℝ) := by
  obtain ⟨C1, hC1, hpre⟩ := exists_tPreCore_le_p cShared30
  obtain ⟨C2, hC2, hq⟩ := exists_tQueryAt_le
  obtain ⟨Cq, hCq, hcq⟩ := Corollary31.query_cost (c := 20) (θ := 56569 / 500000) (by norm_num)
    (by norm_num) (by norm_num)
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set a0 := Real.log (2 * max c 1) / Real.log 2 with ha0_def
  set κ' := max κ 0 / Real.log 2 with hκ'_def
  have ha0 : 0 ≤ a0 :=
    div_nonneg (Real.log_nonneg (by linarith [le_max_right c 1])) hl.le
  have hκ' : 0 ≤ κ' := div_nonneg (le_max_right _ _) hl.le
  filter_upwards [Light.Filter2.PmaxOf_le (η := 0.000000001) (by norm_num),
    eventually_ge_atTop ⌈Real.exp 20000⌉₊, eventually_ge_atTop 1,
    eventually_const_mul_rpow_le (Kt A C1 C2 Cq a0 κ') (e := 2.99556081) (t := 2.99556082)
      (by norm_num)] with n hPm hnE hn hev U hU p hpP
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · have h0 : oTimeF A n U (Light.Filter2.sOf n) 0 = 0 := by unfold oTimeF; rw [if_pos rfl]
    rw [h0, Nat.cast_zero]
    exact Real.rpow_nonneg hn0.le _
  set s := Light.Filter2.sOf n with hs_def
  have hs : 1 ≤ s := Light.Filter2.one_le_sOf n
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hν : 20000 ≤ Real.log n := by
    have : Real.exp 20000 ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hnE)
    calc (20000 : ℝ) = Real.log (Real.exp 20000) := (Real.log_exp _).symm
      _ ≤ Real.log n := Real.log_le_log (Real.exp_pos _) this
  have hx1 : 0.0336175 * Real.log n ≤ Real.log 2 + Real.log s := by
    have h1 := Light.Filter2.rpow_le_two_mul_sOf n
    rw [← hs_def] at h1
    calc 0.0336175 * Real.log n = Real.log ((n : ℝ) ^ (0.0336175 : ℝ)) := by
          rw [Real.log_rpow hn0]
      _ ≤ Real.log (2 * s) := Real.log_le_log (Real.rpow_pos_of_pos hn0 _) h1
      _ = _ := Real.log_mul (by norm_num) hs0.ne'
  have hx2 : Real.log s ≤ Real.log 2 + 0.0336175 * Real.log n := by
    have h1 := Light.Filter2.sOf_le_two_mul_rpow hn
    rw [← hs_def] at h1
    have hpos := Real.rpow_pos_of_pos hn0 (0.0336175 : ℝ)
    calc Real.log s ≤ Real.log (2 * (n : ℝ) ^ (0.0336175 : ℝ)) := Real.log_le_log hs0 h1
      _ = _ := by rw [Real.log_mul (by norm_num) hpos.ne', Real.log_rpow hn0]
  have hy : Real.log p ≤ Real.log s + 0.000000001 * Real.log n := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
    have h1 : (p : ℝ) ≤ s * (n : ℝ) ^ (0.000000001 : ℝ) :=
      le_trans (by exact_mod_cast hpP) hPm
    have hpos := Real.rpow_pos_of_pos hn0 (0.000000001 : ℝ)
    calc Real.log p ≤ Real.log (s * (n : ℝ) ^ (0.000000001 : ℝ)) := Real.log_le_log hp0 h1
      _ = _ := by rw [Real.log_mul hs0.ne' hpos.ne', Real.log_rpow hn0]
  have hG := log_le_of_le hn hU
  rw [← ha0_def, ← hκ'_def] at hG
  have hmain := oTimeF_le_of (A := A) hC1 hC2 hCq ha0 hκ' hpre hq
    (fun m hm => hcq m hm) hn hs (Light.Filter2.sOf_le_n hn) hp hν hx1 hx2 hy hG
  have hrp : Real.exp (2.99556081 * Real.log n) = (n : ℝ) ^ (2.99556081 : ℝ) := by
    rw [Real.rpow_def_of_pos hn0, mul_comm]
  rw [hrp] at hmain
  exact hmain.trans hev

end Light.Batch
