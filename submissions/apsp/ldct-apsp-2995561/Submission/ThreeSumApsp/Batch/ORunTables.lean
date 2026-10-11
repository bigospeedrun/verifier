/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Batch.OSetup
public import Submission.ThreeSumApsp.Batch.OBound

/-!
# The batched counting oracle: the run of its tables

`oTables_ends`: the third piece `oTables` of the oracle fills the tables `RAC`, `RNBC`, `RNAB`
(residues of the matrices), `NL`, `HK` (residues of the digits), `RS`, `RV` (first rows), `DK`
(quotients by `k`) and `ZH`, `ZL` (the digits of `RNAB`), within the time `tOTables`; it changes no
cell below the free pointer.  The tables, as the specifications give them, are `OTabs`.
-/

@[expose] public section

namespace Light.Batch

open ThreeSumApsp ThreeSumApsp.Batch Light.Sec4 Light.Filter2

/-- The tables that `oTables` fills, in the forms that the specifications give. -/
structure OTabs (x : OracleInst) (fr : ℕ) (μ : ℕ → ℤ) : Prop where
  rac : SegN μ fr (x.AC.map fun w => resid x.p (1 * w))
  rnbc : SegN μ (oaRNBC x.n fr) (x.BC.map fun w => resid x.p (-1 * w))
  rnab : SegN μ (oaRNAB x.n fr) (x.AB.map fun w => resid x.p (-1 * w))
  nl : SegN μ (oaNL x.n fr)
    ((List.range (oDig x.p)).map fun h : ℕ => resid x.p ((h : ℤ) * (-1) + (x.p : ℤ)))
  hk : SegN μ (oaHK x.n x.p fr)
    ((List.range (oDig x.p)).map fun h : ℕ => resid x.p ((h : ℤ) * (oDig x.p : ℤ) + 0))
  rs : SegN μ (oaRS x.n x.p fr) ((List.range (oNP x.n x.s x.p)).map fun R =>
    R / oN0 x.s x.p * (oKK x.s x.p * oN0 x.s x.p) + R % oN0 x.s x.p)
  rv : SegN μ (oaRV x.n x.s x.p fr) ((List.range (oNP x.n x.s x.p)).map fun R =>
    R / oN0 x.s x.p * (oK0 x.s x.p * oN0 x.s x.p) + R % oN0 x.s x.p)
  dk : SegN μ (oaDK x.n x.s x.p fr) ((List.range (oDig x.p * oDig x.p)).map fun z => z / oDig x.p)
  zh : SegN μ (oaZH x.n x.s x.p fr) ((x.AB.map fun w => resid x.p (-1 * w)).map (· / oDig x.p))
  zl : SegN μ (oaZL x.n x.s x.p fr) ((x.AB.map fun w => resid x.p (-1 * w)).map (· % oDig x.p))

/-- The time of `oTables`. -/
def tOTables (n U s p : ℕ) : ℕ :=
  3 * tResidTab (n * n) U p + 2 * tSmallTab (oDig p) (3 * p) p + 2 * tRowTab (oNb n s p) (oN0 s p)
    + tDivTab (oDig p) + tZTab (n * n) + 300

/-- The time of `oTables` is linear in its terms. -/
theorem tOTables_le {n U s p : ℕ} (hp : 1 ≤ p) :
    tOTables n U s p ≤
      1000 * (n * n * (Nat.log 2 (U + 1) + 2) + p + oDig p * oDig p + oNP n s p + 1) := by
  have hr : emodRounds U p ≤ Nat.log 2 (U + 1) + 1 := emodRounds_le le_rfl
  have h3 : emodRounds (3 * p) p = 2 := by
    unfold emodRounds
    rw [Nat.mul_div_cancel _ (by omega)]
    rfl
  have hk := Nat.le_mul_self (oDig p)
  have hnb : oNb n s p ≤ oNP n s p := Nat.le_mul_of_pos_right _ (one_le_oN0 s p)
  have e1 : tResidTab (n * n) U p ≤ 54 * (n * n * (Nat.log 2 (U + 1) + 2)) + 10 := by
    unfold tResidTab emodTime
    have : n * n * (43 * emodRounds U p + 34 + 30) ≤ n * n * (54 * (Nat.log 2 (U + 1) + 2)) :=
      Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_left_comm] at this
    omega
  have e2 : tSmallTab (oDig p) (3 * p) p = oDig p * 150 + 10 := by
    unfold tSmallTab emodTime
    rw [h3]
  have e3 : tRowTab (oNb n s p) (oN0 s p) = 30 * oNP n s p + 30 * oNb n s p + 10 := by
    unfold tRowTab oNP
    ring
  have e4 : tDivTab (oDig p) = 30 * (oDig p * oDig p) + 30 * oDig p + 10 := by
    unfold tDivTab
    ring
  unfold tOTables tZTab
  rw [e2, e3, e4]
  have hA : n * n ≤ n * n * (Nat.log 2 (U + 1) + 2) := Nat.le_mul_of_pos_right _ (by omega)
  generalize n * n * (Nat.log 2 (U + 1) + 2) = A at e1 hA ⊢
  generalize tResidTab (n * n) U p = B at e1 ⊢
  omega

theorem setLocal_oLocA (x : OracleInst) (fr : ℕ) (tmp bn j0 kkb r : ℤ) :
    setLocal (oLocA x fr tmp bn j0 kkb) 35 r = oLocA x fr r bn j0 kkb := by
  rfl

/-- The terms of `oWordSum` that the tables need. -/
theorem oWordSum_ge (n U s p : ℕ) :
    100 + 4 * U + 16 * p + 16 + n * n + oK0 s p * oN0 s p
      + (oNb n s p + 1) * (oKK s p * oN0 s p + oN0 s p + 1) ≤ oWordSum n U s p := by
  unfold oWordSum
  generalize 10 ^ oM s p * (7 ^ oL s p * 7 ^ oL s p) = a
  generalize 7 ^ (oL s p + 1) = b
  generalize 10 ^ (oL s p + 1) = c
  generalize 2 ^ oL s p = e
  generalize 3 ^ (oL s p - oM s p) = f
  omega

/-- The list of natural numbers as integers, written in the list monad. -/
theorem bind_pure_natCast (l : List ℕ) :
    (do let a ← l; pure (a : ℤ) : List ℤ) = l.map (fun a : ℕ => (a : ℤ)) := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.map_eq_flatMap]

/-- A segment of natural numbers whose cells are kept. -/
theorem SegN.of_sameOn' {K : ℕ → Prop} {μ μ' : ℕ → ℤ} {a : ℕ} {l : List ℕ} (h : SegN μ a l)
    (hs : SameOn K μ μ') (hK : ∀ i < l.length, K (a + i)) : SegN μ' a l :=
  Seg.of_sameOn h hs (by simpa using hK)

set_option maxHeartbeats 1600000 in
theorem oTables_ends (R : Program) {lim : Limits} {d : ℕ} {x : OracleInst} {μ : ℕ → ℤ} {fr : ℕ}
    (hpre : x.Pre μ fr) (hok : (oNeedAt x.n x.U x.s x.p).Ok lim fr d) (tmp bn j0 kkb : ℤ) :
    Ends lim (oProg ++ R) d oTables ⟨frame (oLocA x fr tmp bn j0 kkb), μ⟩ (tOTables x.n x.U x.s x.p)
      fun σ' => ∃ tmp' : ℤ, σ'.loc = frame (oLocA x fr tmp' bn j0 kkb) ∧ OTabs x fr σ'.mem ∧
        SameOn (fun b => b < fr) μ σ'.mem := by
  have hW := oWordSum_ge x.n x.U x.s x.p
  have std : Std lim := ⟨hok.space, by simpa using oWordSum_fits hok (z := 100) (by omega)⟩
  have hcells := hok.cells
  have hdepth := hok.depth
  simp only [oNeedAt, oCells] at hcells hdepth
  have hp := hpre.p_pos
  have hn := hpre.n_pos
  have lAB := hpre.lenAB
  have lBC := hpre.lenBC
  have lAC := hpre.lenAC
  have bAB := hpre.belowAB
  have bBC := hpre.belowBC
  have bAC := hpre.belowAC
  -- the layout
  have e1 : oaRNBC x.n fr = fr + x.n * x.n := rfl
  have e2 : oaRNAB x.n fr = oaRNBC x.n fr + x.n * x.n := rfl
  have e3 : oaNL x.n fr = oaRNAB x.n fr + x.n * x.n := rfl
  have e4 : oaHK x.n x.p fr = oaNL x.n fr + oDig x.p := rfl
  have e5 : oaRS x.n x.p fr = oaHK x.n x.p fr + oDig x.p := rfl
  have e6 : oaRV x.n x.s x.p fr = oaRS x.n x.p fr + oNP x.n x.s x.p := rfl
  have e7 : oaDK x.n x.s x.p fr = oaRV x.n x.s x.p fr + oNP x.n x.s x.p := rfl
  have e8 : oaZH x.n x.s x.p fr = oaDK x.n x.s x.p fr + oDig x.p * oDig x.p := rfl
  have e9 : oaZL x.n x.s x.p fr = oaZH x.n x.s x.p fr + x.n * x.n := rfl
  have e10 : oaX x.n x.s x.p fr = oaZL x.n x.s x.p fr + x.n * x.n := rfl
  have e11 : oaY x.n x.s x.p fr = oaX x.n x.s x.p fr + oSz x.n x.s x.p := rfl
  have e12 : oB0 x.n x.s x.p fr = oaY x.n x.s x.p fr + oSz x.n x.s x.p := rfl
  have eB := oB0_eq x.n x.s x.p fr
  -- the emod tables
  have hlogU : Nat.log 2 (x.U + 1) ≤ Nat.log 2 (x.U + 3 * x.p + 1) :=
    Nat.log_mono_right (by omega)
  have hlogP : Nat.log 2 (3 * x.p + 1) ≤ Nat.log 2 (x.U + 3 * x.p + 1) :=
    Nat.log_mono_right (by omega)
  have hEU : Emod.Pre lim x.p x.U (oB0 x.n x.s x.p fr) :=
    ⟨hp, hok.space, by simpa using oWordSum_fits hok (z := 4 * x.U + 4 * x.p + 16) (by omega),
      by omega⟩
  have hEP : Emod.Pre lim x.p (3 * x.p) (oB0 x.n x.s x.p fr) :=
    ⟨hp, hok.space, by simpa using oWordSum_fits hok (z := 4 * (3 * x.p) + 4 * x.p + 16) (by omega),
      by omega⟩
  have hB0 : oB0 x.n x.s x.p fr < lim.space := by omega
  -- words
  have wnn : ((x.n * x.n : ℕ) : ℤ) ≤ lim.word := oWordSum_fits hok (by omega)
  push_cast at wnn
  have hkp : oDig x.p ≤ x.p := by
    unfold oDig
    have := Nat.sqrt_le_self (x.p - 1)
    omega
  have hk1 := one_le_oDig x.p
  have hkk := oDig_sq_le hp
  have hpk := le_oDig_sq x.p
  have hN01 := one_le_oN0 x.s x.p
  have eNP : oNP x.n x.s x.p = oNb x.n x.s x.p * oN0 x.s x.p := rfl
  have wKN : ((oKK x.s x.p * oN0 x.s x.p : ℕ) : ℤ) ≤ lim.word := by
    refine oWordSum_fits hok (le_trans ?_ hW)
    have h1 : oKK x.s x.p * oN0 x.s x.p ≤ (oNb x.n x.s x.p + 1) * (oKK x.s x.p * oN0 x.s x.p) :=
      Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    have h2 : (oNb x.n x.s x.p + 1) * (oKK x.s x.p * oN0 x.s x.p)
        ≤ (oNb x.n x.s x.p + 1) * (oKK x.s x.p * oN0 x.s x.p + oN0 x.s x.p + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  have wK0N : ((oK0 x.s x.p * oN0 x.s x.p : ℕ) : ℤ) ≤ lim.word := oWordSum_fits hok (by omega)
  have hK0KK : oK0 x.s x.p * oN0 x.s x.p ≤ oKK x.s x.p * oN0 x.s x.p :=
    Nat.mul_le_mul_right _ (Nat.le_mul_self _)
  have wRS : (((oNb x.n x.s x.p + 1) * (oKK x.s x.p * oN0 x.s x.p + oN0 x.s x.p + 1) : ℕ) : ℤ)
      ≤ lim.word := oWordSum_fits hok (by omega)
  have wRV : (((oNb x.n x.s x.p + 1) * (oK0 x.s x.p * oN0 x.s x.p + oN0 x.s x.p + 1) : ℕ) : ℤ)
      ≤ lim.word := by
    refine le_trans ?_ wRS
    exact_mod_cast Nat.mul_le_mul_left _ (by omega)
  push_cast at wKN wK0N
  have hR := residTab_ok (lim := lim) (oProg_at pResidTab (h := rfl) (R := R))
    (oProg_at pEmod (h := rfl) (R := R))
  have hS := smallTab_ok (lim := lim) (oProg_at pSmallTab (h := rfl) (R := R))
    (oProg_at pEmod (h := rfl) (R := R))
  have hRow := rowTab_ok (lim := lim) (oProg_at pRowTab (h := rfl) (R := R))
  have hDiv := divTab_ok (lim := lim) (oProg_at pDivTab (h := rfl) (R := R))
  have hZ := zTab_ok (lim := lim) (oProg_at pZTab (h := rfl) (R := R))
  unfold oTables tOTables
  -- RAC
  light_call (hR fr x.ac x.AC 1 x.p x.U (oB0 x.n x.s x.p fr) μ (d + 1) (Or.inl rfl) hpre.segAC
    hpre.leAC hEU (by omega) (by omega) (by omega) (by omega))
    using lAB, lBC, lAC, oLocA with r₁ μ₁ ⟨t1, s1⟩
  rw [setLocal_oLocA]
  -- RNBC
  have gBC : Seg μ₁ x.bc x.BC := Seg.of_sameOn hpre.segBC s1
    fun i hi => ⟨by omega, Or.inl (by omega)⟩
  light_call (hR (oaRNBC x.n fr) x.bc x.BC (-1) x.p x.U (oB0 x.n x.s x.p fr) μ₁ (d + 1)
    (Or.inr rfl) gBC hpre.leBC hEU (by omega) (by omega) (by omega) (by omega))
    using lAB, lBC, lAC, oLocA with r₂ μ₂ ⟨t2, s2⟩
  rw [setLocal_oLocA]
  replace t1 := SegN.of_sameOn' t1 s2
    fun i hi => by simp at hi; simp only [Outside]; omega
  -- RNAB
  have gAB : Seg μ₂ x.ab x.AB := Seg.of_sameOn (Seg.of_sameOn hpre.segAB s1
    fun i hi => ⟨by omega, Or.inl (by omega)⟩) s2 fun i hi => ⟨by omega, Or.inl (by omega)⟩
  light_call (hR (oaRNAB x.n fr) x.ab x.AB (-1) x.p x.U (oB0 x.n x.s x.p fr) μ₂ (d + 1)
    (Or.inr rfl) gAB hpre.leAB hEU (by omega) (by omega) (by omega) (by omega))
    using lAB, lBC, lAC, oLocA with r₃ μ₃ ⟨t3, s3⟩
  rw [setLocal_oLocA]
  replace t1 := SegN.of_sameOn' t1 s3
    fun i hi => by simp at hi; simp only [Outside]; omega
  replace t2 := SegN.of_sameOn' t2 s3
    fun i hi => by simp at hi; simp only [Outside]; omega
  -- NL
  light_call (hS (oaNL x.n fr) (oDig x.p) (-1) x.p x.p (3 * x.p) (oB0 x.n x.s x.p fr) μ₃ (d + 1)
    (fun h hh => by rw [abs_le]; push_cast; constructor <;> omega)
    (by rw [abs_le]; push_cast; constructor <;> omega)
    (by rw [abs_le]; push_cast; constructor <;> omega)
    (by push_cast; omega) hEP (by omega) (by omega)) using lAB, lBC, lAC, oLocA with r₄ μ₄ ⟨t4, s4⟩
  rw [bind_pure_natCast, List.map_map] at t4
  rw [setLocal_oLocA]
  replace t1 := SegN.of_sameOn' t1 s4
    fun i hi => by simp at hi; simp only [Outside]; omega
  replace t2 := SegN.of_sameOn' t2 s4
    fun i hi => by simp at hi; simp only [Outside]; omega
  replace t3 := SegN.of_sameOn' t3 s4
    fun i hi => by simp at hi; simp only [Outside]; omega
  -- HK
  light_call (hS (oaHK x.n x.p fr) (oDig x.p) (oDig x.p) 0 x.p (3 * x.p) (oB0 x.n x.s x.p fr) μ₄
    (d + 1)
    (fun h hh => by
      have h1 : h * oDig x.p < oDig x.p * oDig x.p := Nat.mul_lt_mul_of_pos_right hh hk1
      have h2 : ((h * oDig x.p : ℕ) : ℤ) < ((oDig x.p * oDig x.p : ℕ) : ℤ) := by exact_mod_cast h1
      have h3 : ((oDig x.p * oDig x.p : ℕ) : ℤ) ≤ ((3 * x.p : ℕ) : ℤ) := by exact_mod_cast hkk
      have h4 : (0 : ℤ) ≤ ((h * oDig x.p : ℕ) : ℤ) := by positivity
      push_cast at h2 h3 h4
      rw [abs_le]; push_cast; constructor <;> omega)
    (by rw [abs_le]; push_cast; constructor <;> omega)
    (by simp)
    (by push_cast; omega) hEP (by omega) (by omega)) using lAB, lBC, lAC, oLocA with r₅ μ₅ ⟨t5, s5⟩
  rw [bind_pure_natCast, List.map_map] at t5
  rw [setLocal_oLocA]
  replace t1 := SegN.of_sameOn' t1 s5
    fun i hi => by simp at hi; simp only [Outside]; omega
  replace t2 := SegN.of_sameOn' t2 s5
    fun i hi => by simp at hi; simp only [Outside]; omega
  replace t3 := SegN.of_sameOn' t3 s5
    fun i hi => by simp at hi; simp only [Outside]; omega
  replace t4 := SegN.of_sameOn' t4 s5
    fun i hi => by simp at hi; simp only [Outside]; omega
  -- RS
  light_call (hRow (oaRS x.n x.p fr) (oNb x.n x.s x.p) (oN0 x.s x.p) (oKK x.s x.p * oN0 x.s x.p) μ₅
    (d + 1) std hN01 (by omega) wRS) using lAB, lBC, lAC, oLocA with r₆ μ₆ ⟨t6, s6⟩
  rw [setLocal_oLocA]
  replace t1 := SegN.of_sameOn' t1 s6
    fun i hi => by simp at hi; simp only [Outside]; omega
  replace t2 := SegN.of_sameOn' t2 s6
    fun i hi => by simp at hi; simp only [Outside]; omega
  replace t3 := SegN.of_sameOn' t3 s6
    fun i hi => by simp at hi; simp only [Outside]; omega
  replace t4 := SegN.of_sameOn' t4 s6
    fun i hi => by simp at hi; simp only [Outside]; omega
  replace t5 := SegN.of_sameOn' t5 s6
    fun i hi => by simp at hi; simp only [Outside]; omega
  -- RV
  light_call (hRow (oaRV x.n x.s x.p fr) (oNb x.n x.s x.p) (oN0 x.s x.p)
    (oK0 x.s x.p * oN0 x.s x.p) μ₆ (d + 1) std hN01 (by omega) wRV)
    using lAB, lBC, lAC, oLocA with r₇ μ₇ ⟨t7, s7⟩
  rw [setLocal_oLocA]
  replace t1 := SegN.of_sameOn' t1 s7
    fun i hi => by simp at hi; simp only [Outside]; omega
  replace t2 := SegN.of_sameOn' t2 s7
    fun i hi => by simp at hi; simp only [Outside]; omega
  replace t3 := SegN.of_sameOn' t3 s7
    fun i hi => by simp at hi; simp only [Outside]; omega
  replace t4 := SegN.of_sameOn' t4 s7
    fun i hi => by simp at hi; simp only [Outside]; omega
  replace t5 := SegN.of_sameOn' t5 s7
    fun i hi => by simp at hi; simp only [Outside]; omega
  replace t6 := SegN.of_sameOn' t6 s7
    fun i hi => by simp at hi; simp only [Outside]; omega
  -- DK
  light_call (hDiv (oaDK x.n x.s x.p fr) (oDig x.p) μ₇ (d + 1) std (by omega))
    using lAB, lBC, lAC, oLocA with r₈ μ₈ ⟨t8, s8⟩
  rw [setLocal_oLocA]
  replace t1 := SegN.of_sameOn' t1 s8
    fun i hi => by simp at hi; simp only [Outside]; omega
  replace t2 := SegN.of_sameOn' t2 s8
    fun i hi => by simp at hi; simp only [Outside]; omega
  replace t3 := SegN.of_sameOn' t3 s8
    fun i hi => by simp at hi; simp only [Outside]; omega
  replace t4 := SegN.of_sameOn' t4 s8
    fun i hi => by simp at hi; simp only [Outside]; omega
  replace t5 := SegN.of_sameOn' t5 s8
    fun i hi => by simp at hi; simp only [Outside]; omega
  replace t6 := SegN.of_sameOn' t6 s8
    fun i hi => by simp at hi; simp only [Outside]; omega
  replace t7 := SegN.of_sameOn' t7 s8
    fun i hi => by simp at hi; simp only [Outside]; omega
  -- ZH, ZL
  have hRN : (x.AB.map fun w => resid x.p (-1 * w)).length = x.n * x.n := by simp [lAB]
  light_call (hZ (oaZH x.n x.s x.p fr) (oaZL x.n x.s x.p fr) (oaRNAB x.n fr) (oaDK x.n x.s x.p fr)
    (oDig x.p) (x.AB.map fun w => resid x.p (-1 * w)) μ₈ (d + 1) std hk1 t3 t8
    (fun z hz => by
      obtain ⟨w, -, rfl⟩ := List.mem_map.1 hz
      exact lt_of_lt_of_le (resid_lt (by omega) _) hpk)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
    using lAB, lBC, lAC, oLocA with r₉ μ₉ ⟨t9, t10, s9⟩
  replace t1 := SegN.of_sameOn' t1 s9
    fun i hi => by simp at hi; simp only [Outside]; omega
  replace t2 := SegN.of_sameOn' t2 s9
    fun i hi => by simp at hi; simp only [Outside]; omega
  replace t3 := SegN.of_sameOn' t3 s9
    fun i hi => by simp at hi; simp only [Outside]; omega
  replace t4 := SegN.of_sameOn' t4 s9
    fun i hi => by simp at hi; simp only [Outside]; omega
  replace t5 := SegN.of_sameOn' t5 s9
    fun i hi => by simp at hi; simp only [Outside]; omega
  replace t6 := SegN.of_sameOn' t6 s9
    fun i hi => by simp at hi; simp only [Outside]; omega
  replace t7 := SegN.of_sameOn' t7 s9
    fun i hi => by simp at hi; simp only [Outside]; omega
  replace t8 := SegN.of_sameOn' t8 s9
    fun i hi => by simp at hi; simp only [Outside]; omega
  refine ⟨r₉, rfl, ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10⟩, ?_⟩
  have k1 : SameOn (· < fr) μ μ₁ := s1.mono fun b (hb : b < fr) => by simp only [Outside]; omega
  have k2 : SameOn (· < fr) μ₁ μ₂ := s2.mono fun b (hb : b < fr) => by simp only [Outside]; omega
  have k3 : SameOn (· < fr) μ₂ μ₃ := s3.mono fun b (hb : b < fr) => by simp only [Outside]; omega
  have k4 : SameOn (· < fr) μ₃ μ₄ := s4.mono fun b (hb : b < fr) => by simp only [Outside]; omega
  have k5 : SameOn (· < fr) μ₄ μ₅ := s5.mono fun b (hb : b < fr) => by simp only [Outside]; omega
  have k6 : SameOn (· < fr) μ₅ μ₆ := SameOn.mono s6
    fun b (hb : b < fr) => by simp only [Outside]; omega
  have k7 : SameOn (· < fr) μ₆ μ₇ := SameOn.mono s7
    fun b (hb : b < fr) => by simp only [Outside]; omega
  have k8 : SameOn (· < fr) μ₇ μ₈ := SameOn.mono s8
    fun b (hb : b < fr) => by simp only [Outside]; omega
  have k9 : SameOn (· < fr) μ₈ μ₉ := s9.mono fun b (hb : b < fr) => by
    simp only [Outside, List.length_map]; omega
  exact ((((((((k1.trans k2).trans k3).trans k4).trans k5).trans k6).trans k7).trans k8).trans k9)

end Light.Batch
