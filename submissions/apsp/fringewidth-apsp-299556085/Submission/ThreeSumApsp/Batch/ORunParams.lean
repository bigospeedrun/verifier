/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Batch.OSetup
public import Submission.ThreeSumApsp.Batch.OBound

/-!
# The batched counting oracle: the run of its parameters

`oParams_ends`: the first piece `oParams` of the oracle computes the parameters `m, D, L, t, N0,
K0, KK, k, nb, NP, Nv, T, B` and `binom(L, m)` into the locals `oLocP`, within the time
`tOParams`; it writes `4^m` to the cell `fr` and uses the `L + 2` cells after it for the table of
binomials.
-/

@[expose] public section

namespace Light.Batch

open ThreeSumApsp Light.Sec4 Light.Filter2

/-- The time of binom(L, m) with the constant 30. -/
def tBinom30 (L : ℕ) : ℕ := 30 * (L + 1) ^ 2

/-- The time of `oParams`. -/
def tOParams (n s p : ℕ) : ℕ :=
  tLog4 (oM s p) + tCeilMul 56569 (oM s p) + tPowNat (oL s p - oM s p)
    + tBinom30 (oL s p) + 18 * (oK0 s p + 1) + 18 * (Nat.sqrt (p - 1) + 1)
    + Sec3.tCeilDiv (n * oDig p) (oN0 s p) + Sec3.tCeilDiv n s
    + Sec3.tCeilDiv (oProd n s) (oKK s p) + 300

theorem oParams_ends (R : Program) {lim : Limits} {d : ℕ} {x : OracleInst} {μ : ℕ → ℤ} {fr : ℕ}
    (hpre : x.Pre μ fr) (hok : (oNeedAt x.n x.U x.s x.p).Ok lim fr d) :
    Ends lim (oProg ++ R) d oParams
      ⟨frame ([(x.n : ℤ), x.U, x.ab, x.bc, x.ac, x.s, x.p, x.cnt] ++ [(fr : ℤ)]), μ⟩
      (tOParams x.n x.s x.p) fun σ' =>
        σ'.loc = frame (oLocP x fr) ∧ SameOutside μ σ'.mem fr (oL x.s x.p + 3) := by
  have hWS : 100 + 4 * x.s * x.p + oD x.s x.p + 56569 * oM x.s x.p + 500000 + oN0 x.s x.p
      + oL x.s x.p + 1 + 4 * (oL x.s x.p).choose (oM x.s x.p) + 4 + 16 * x.p + 16
      + x.n * oDig x.p + oNb x.n x.s x.p + oNP x.n x.s x.p + oNv x.n x.s x.p + x.n + x.s
      + oProd x.n x.s + oKK x.s x.p + oBat x.n x.s x.p ≤ oWordSum x.n x.U x.s x.p := by
    unfold oWordSum
    generalize 10 ^ oM x.s x.p * (7 ^ oL x.s x.p * 7 ^ oL x.s x.p) = A
    generalize 7 ^ (oL x.s x.p + 1) = B
    generalize 10 ^ (oL x.s x.p + 1) = C
    generalize 2 ^ oL x.s x.p = E
    generalize 3 ^ (oL x.s x.p - oM x.s x.p) = F
    omega
  have h2W : ((2 ^ oL x.s x.p : ℕ) : ℤ) ≤ lim.word := oWordSum_fits hok (by
    unfold oWordSum
    generalize 10 ^ oM x.s x.p * (7 ^ oL x.s x.p * 7 ^ oL x.s x.p) = A
    generalize 7 ^ (oL x.s x.p + 1) = B
    generalize 10 ^ (oL x.s x.p + 1) = C
    generalize 2 ^ oL x.s x.p = E
    generalize 3 ^ (oL x.s x.p - oM x.s x.p) = F
    omega)
  have hW : ∀ z, z ≤ oWordSum x.n x.U x.s x.p → ((z : ℕ) : ℤ) ≤ lim.word :=
    fun z hz => oWordSum_fits hok hz
  have std : Std lim := ⟨hok.space, by simpa using hW 100 (by omega)⟩
  have hcells := hok.cells
  have hdepth := hok.depth
  simp only [oNeedAt, oCells] at hcells hdepth
  have hs := hpre.s_pos
  have hp := hpre.p_pos
  have hn := hpre.n_pos
  have hM1 := one_le_oM hs hp
  have hN01 := one_le_oN0 x.s x.p
  have hKK1 := one_le_oKK x.s x.p
  have hLeq : oL x.s x.p = 20 * oM x.s x.p := rfl
  -- the procedures
  have hlog : Meets lim (oProg ++ R) Proc.log4 (d + 1) [((4 * x.s * x.p : ℕ) : ℤ), (fr : ℤ)] μ
      (tLog4 (oM x.s x.p)) fun r μ' =>
        r = (oM x.s x.p : ℕ) ∧ μ' = Function.update μ fr ((oD x.s x.p : ℕ) : ℤ) :=
    log4_meets (oProg_at31 Proc.log4 (R := R)) std (4 * x.s * x.p) fr μ (by omega)
      (hW (oD x.s x.p) (by omega)) (hW (oM x.s x.p) (by omega)) (d + 1)
      (by omega)
  have hb58 : ∀ {i : ℕ} {body : Stmt}, base58[i]? = some body → i ≠ Sec2.pBandArray →
      (oProg ++ R)[i]? = some body := fun h hi => by
    rw [oProg, List.append_assoc, List.append_assoc]
    exact at_base58B h hi _
  have hsw : ∀ μ : ℕ → ℤ, Meets lim (oProg ++ R) Proc.switch31 (d + 1) [((oM x.s x.p : ℕ) : ℤ)] μ
      (tCeilMul 56569 (oM x.s x.p)) fun r μ' => r = (oT x.s x.p : ℕ) ∧ μ' = μ := fun μ =>
    ceilMul_meets (a := 56569) (b := 500000) (by norm_num) (oProg_at31 Proc.switch31 (R := R))
      (oM x.s x.p) μ (hW _ (by omega)) (d + 1) (by omega)
  have hpow : ∀ μ : ℕ → ℤ, Meets lim (oProg ++ R) pPowNat (d + 1)
      [((3 : ℕ) : ℤ), ((oL x.s x.p - oM x.s x.p : ℕ) : ℤ)] μ (tPowNat (oL x.s x.p - oM x.s x.p))
      fun r μ' => r = (oN0 x.s x.p : ℕ) ∧ μ' = μ := fun μ =>
    powNat_ok (oProg_at pPowNat (R := R)) 3 (oL x.s x.p - oM x.s x.p) μ (d + 1) (by norm_num)
      (hW (oN0 x.s x.p + (oL x.s x.p - oM x.s x.p) + 1) (by omega))
  have hbin : ∀ μ : ℕ → ℤ, Meets lim (oProg ++ R) Sec2.pBinom (d + 1)
      [((oL x.s x.p : ℕ) : ℤ), ((oM x.s x.p : ℕ) : ℤ), ((fr + 1 : ℕ) : ℤ)] μ
      (tBinom30 (oL x.s x.p)) fun r μ' =>
        r = ((oL x.s x.p).choose (oM x.s x.p) : ℕ) ∧ SameOutside μ μ' (fr + 1) (oL x.s x.p + 2) :=
    fun μ => (Sec2.binom_entry std (hb58 rfl (by decide)) le_rfl (oL x.s x.p) (oM x.s x.p) (fr + 1)
      μ (by omega) (by omega) h2W (d + 1) (by omega))
  have hsq : ∀ (K : ℕ) (μ : ℕ → ℤ), ((4 * K + 4 : ℕ) : ℤ) ≤ lim.word →
      Meets lim (oProg ++ R) Sec2.pSqrt (d + 1) [(K : ℤ)] μ (18 * (Nat.sqrt K + 1)) fun r μ' =>
        r = (Nat.sqrt K : ℕ) ∧ μ' = μ := fun K μ hK =>
    Sec2.sqrt_entry (hb58 rfl (by decide)) le_rfl K μ hK (d + 1) (by omega)
  have hcd : ∀ (a b : ℕ) (μ : ℕ → ℤ), 1 ≤ b → ((a + b + 1 : ℕ) : ℤ) ≤ lim.word →
      Meets lim (oProg ++ R) pCeilDiv (d + 1) [(a : ℤ), (b : ℤ)] μ (Sec3.tCeilDiv a b)
        fun r μ' => r = (a ⌈/⌉ b : ℕ) ∧ μ' = μ := fun a b μ hb hw =>
    Sec3.ceilDiv_meets (oProg_at pCeilDiv (R := R)) hb hw
  -- the facts for the side conditions
  have hfr : fr + oL x.s x.p + 10 ≤ lim.space := by omega
  have hdig : oDig x.p ≤ x.n * oDig x.p := Nat.le_mul_of_pos_left _ hn
  have hsdig : Nat.sqrt (x.p - 1) ≤ x.p - 1 := Nat.sqrt_le_self _
  have hs4 : 4 * x.s ≤ 4 * x.s * x.p := Nat.le_mul_of_pos_right _ hp
  have zs4 : 4 * (x.s : ℤ) ≤ lim.word := by have := hW (4 * x.s) (by omega); push_cast at this; omega
  have zsp : 4 * (x.s : ℤ) * x.p ≤ lim.word := by
    have := hW (4 * x.s * x.p) (by omega); push_cast at this; omega
  have zM : (oM x.s x.p : ℤ) ≤ lim.word := hW _ (by omega)
  have zL : (oL x.s x.p : ℤ) ≤ lim.word := hW _ (by omega)
  have zLe : (oL x.s x.p : ℤ) = 20 * oM x.s x.p := by rw [hLeq]; push_cast; ring
  have zLM : ((oL x.s x.p - oM x.s x.p : ℕ) : ℤ) = (oL x.s x.p : ℤ) - oM x.s x.p := by
    rw [Nat.cast_sub (by omega)]
  have zfr : (fr : ℤ) + 1 ≤ lim.word := by
    have := std.space_le; have : (fr : ℤ) + 1 < lim.space := by omega
    omega
  have zKK : (oKK x.s x.p : ℤ) = (oK0 x.s x.p : ℤ) * oK0 x.s x.p := by unfold oKK; push_cast; rfl
  have wKK : (oKK x.s x.p : ℤ) ≤ lim.word := hW _ (by omega)
  have zpW : (x.p : ℤ) ≤ lim.word := hW _ (by omega)
  have zp1 : ((x.p - 1 : ℕ) : ℤ) = (x.p : ℤ) - 1 := by rw [Nat.cast_sub hp]; rfl
  have zDig : (oDig x.p : ℤ) = (Nat.sqrt (x.p - 1) : ℤ) + 1 := by unfold oDig; push_cast; rfl
  have wDig : (oDig x.p : ℤ) ≤ lim.word := hW _ (by omega)
  have wnDig : (x.n : ℤ) * oDig x.p ≤ lim.word := by
    have := hW (x.n * oDig x.p) (by omega); push_cast at this; omega
  have zNb : (oNb x.n x.s x.p : ℤ) = (((x.n * oDig x.p) ⌈/⌉ oN0 x.s x.p : ℕ) : ℤ) + 1 := by
    unfold oNb; push_cast; rfl
  have wNb : (oNb x.n x.s x.p : ℤ) ≤ lim.word := hW _ (by omega)
  have zNP : (oNP x.n x.s x.p : ℤ) = (oNb x.n x.s x.p : ℤ) * oN0 x.s x.p := by
    unfold oNP; push_cast; rfl
  have wNP : (oNP x.n x.s x.p : ℤ) ≤ lim.word := hW _ (by omega)
  have zNv : (oNv x.n x.s x.p : ℤ) = (oK0 x.s x.p : ℤ) * oNP x.n x.s x.p := by
    unfold oNv; push_cast; rfl
  have wNv : (oNv x.n x.s x.p : ℤ) ≤ lim.word := hW _ (by omega)
  have n1 : 0 ≤ 4 * (x.s : ℤ) * x.p := by positivity
  have n2 : 0 ≤ (x.n : ℤ) * oDig x.p := by positivity
  have n3 : 0 ≤ (oK0 x.s x.p : ℤ) * oK0 x.s x.p := by positivity
  have n4 : 0 ≤ (oNb x.n x.s x.p : ℤ) * oN0 x.s x.p := by positivity
  have n5 : 0 ≤ (oK0 x.s x.p : ℤ) * oNP x.n x.s x.p := by positivity
  unfold oParams tOParams
  -- m := log4(4 s p, fr), which writes 4^m to fr
  light_call hlog with _ μ₁ ⟨rfl, rfl⟩
  -- D := mem[fr]
  light_set ((oD x.s x.p : ℕ) : ℤ)
  -- L := 20 m
  light_set ((oL x.s x.p : ℕ) : ℤ) using zLe
  -- t := ⌈θ m⌉
  light_call (hsw _) with _ μ₂ ⟨rfl, rfl⟩
  -- N0 := 3^(L - m)
  light_call (hpow _) using zLM with _ μ₂ ⟨rfl, rfl⟩
  -- Kb := binom(L, m) with the table at fr + 1
  light_call (hbin _) with _ μ₃ ⟨rfl, hsame⟩
  -- K0 := sqrt(Kb)
  light_call (show Meets lim (oProg ++ R) Sec2.pSqrt (d + 1)
      [(((oL x.s x.p).choose (oM x.s x.p) : ℕ) : ℤ)] _ (18 * (oK0 x.s x.p + 1))
      (fun r μ' => r = (oK0 x.s x.p : ℕ) ∧ μ' = _) from
    hsq ((oL x.s x.p).choose (oM x.s x.p)) _ (hW _ (by omega))) with _ μ₄ ⟨rfl, rfl⟩
  -- KK := K0 K0
  light_set ((oKK x.s x.p : ℕ) : ℤ) using zKK
  -- k := sqrt(p - 1) + 1
  light_call (hsq (x.p - 1) _ (hW _ (by omega))) using zp1 with _ μ₄ ⟨rfl, rfl⟩
  light_set ((oDig x.p : ℕ) : ℤ) using zDig
  -- nb := ⌈n k / N0⌉ + 1
  light_call (hcd (x.n * oDig x.p) (oN0 x.s x.p) _ hN01 (hW _ (by omega))) with _ μ₄ ⟨rfl, rfl⟩
  light_set ((oNb x.n x.s x.p : ℕ) : ℤ) using zNb
  -- NP := nb N0, Nv := K0 NP
  light_set ((oNP x.n x.s x.p : ℕ) : ℤ) using zNP
  light_set ((oNv x.n x.s x.p : ℕ) : ℤ) using zNv
  -- T := ⌈n / s⌉, B := ⌈T / KK⌉
  light_call (hcd x.n x.s _ hs (hW _ (by omega))) with _ μ₄ ⟨rfl, rfl⟩
  light_call (hcd (oProd x.n x.s) (oKK x.s x.p) _ hKK1 (hW _ (by omega))) using oProd with _ μ₄ ⟨rfl, rfl⟩
  refine ⟨rfl, fun b hb => ?_⟩
  dsimp only
  rw [hsame b (by simp only [Outside] at hb ⊢; omega), Function.update_of_ne (by omega)]

/-- The run of `oParams` from the locals of the oracle task. -/
theorem oParams_ends' (R : Program) {lim : Limits} {d : ℕ} {x : OracleInst} {μ : ℕ → ℤ} {fr : ℕ}
    (hpre : x.Pre μ fr) (hok : (oNeedAt x.n x.U x.s x.p).Ok lim fr d) :
    Ends lim (oProg ++ R) d oParams ⟨frame (Light.Filter2.oracleTask.args x ++ [(fr : ℤ)]), μ⟩
      (tOParams x.n x.s x.p) fun σ' =>
        σ'.loc = frame (oLocP x fr) ∧ SameOutside μ σ'.mem fr (oL x.s x.p + 3) :=
  oParams_ends R hpre hok

/-- The time of `oParams` is linear in `n², n k, p, 4^L`. -/
theorem tOParams_le {n s p : ℕ} (hs : 1 ≤ s) (hp : 1 ≤ p) :
    tOParams n s p ≤ 2000000 * (n * n + n * oDig p + p + 4 ^ oL s p + 1) := by
  have hL2 : oL s p + 1 ≤ 2 ^ oL s p := Nat.lt_two_pow_self
  have h24 : 2 ^ oL s p ≤ 4 ^ oL s p := Nat.pow_le_pow_left (by norm_num) _
  have hsq : (oL s p + 1) ^ 2 ≤ 4 ^ oL s p := by
    calc (oL s p + 1) ^ 2 ≤ (2 ^ oL s p) ^ 2 := Nat.pow_le_pow_left hL2 2
      _ = 4 ^ oL s p := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hK : oK0 s p ≤ 2 ^ oL s p :=
    (Nat.sqrt_le_self _).trans (Nat.choose_le_two_pow _ _)
  have hLm : oL s p = 20 * oM s p := rfl
  have hsq1 : Nat.sqrt (p - 1) ≤ p := (Nat.sqrt_le_self _).trans (Nat.sub_le _ _)
  have hc1 : (n * oDig p) ⌈/⌉ oN0 s p ≤ n * oDig p :=
    (Nat.ceilDiv_le_iff (one_le_oN0 s p)).2 (Nat.le_mul_of_pos_right _ (one_le_oN0 s p))
  have hc2 : n ⌈/⌉ s ≤ n := (Nat.ceilDiv_le_iff hs).2 (Nat.le_mul_of_pos_right _ hs)
  have hc3 : oProd n s ⌈/⌉ oKK s p ≤ oProd n s :=
    (Nat.ceilDiv_le_iff (one_le_oKK s p)).2 (Nat.le_mul_of_pos_right _ (one_le_oKK s p))
  have hnn : n ≤ n * n := Nat.le_mul_self n
  have hP : oProd n s ≤ n := hc2
  unfold tOParams tLog4 tCeilMul tPowNat tBinom30 Sec3.tCeilDiv
  generalize (oL s p + 1) ^ 2 = A at *
  generalize 4 ^ oL s p = F at *
  generalize 2 ^ oL s p = E at *
  generalize n * oDig p = B at *
  generalize n * n = G at *
  omega

end Light.Batch
