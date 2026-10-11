/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Batch.OSetup
public import Submission.ThreeSumApsp.Batch.OSrc
public import Submission.ThreeSumApsp.Batch.OBound

/-!
# The batched counting oracle: one batch

`oBatch` for the batch `bt`: the first product `j0 = bt KK`, the number `KKb` of products, the two
sources (writeSrc), the data structure (preCore), the queries.  Afterwards the `KKb n²` counts of
the batch stand at `cnt + j0 n²` (`oBatch_ends`).  The tables that the batch reads are `BTabs`.
-/

@[expose] public section

namespace Light.Batch

open ThreeSumApsp ThreeSumApsp.Batch Light.Sec4 Light.Filter2 OS

/-- The tables that a batch reads. -/
structure BTabs (x : OracleInst) (fr : ℕ) (μ : ℕ → ℤ) : Prop where
  rac : SegN μ fr (x.AC.map fun w => resid x.p (1 * w))
  rnbc : SegN μ (oaRNBC x.n fr) (x.BC.map fun w => resid x.p (-1 * w))
  nl : SegN μ (oaNL x.n fr) ((List.range (oDig x.p)).map fun h : ℕ => resid x.p ((x.p : ℤ) - h))
  hk : SegN μ (oaHK x.n x.p fr)
    ((List.range (oDig x.p)).map fun h : ℕ => resid x.p ((h * oDig x.p : ℕ) : ℤ))
  rs : SegN μ (oaRS x.n x.p fr) ((List.range (oNP x.n x.s x.p)).map fun R =>
    R / oN0 x.s x.p * (oKK x.s x.p * oN0 x.s x.p) + R % oN0 x.s x.p)
  rv : SegN μ (oaRV x.n x.s x.p fr) ((List.range (oNP x.n x.s x.p)).map fun R =>
    R / oN0 x.s x.p * (oK0 x.s x.p * oN0 x.s x.p) + R % oN0 x.s x.p)
  zh : SegN μ (oaZH x.n x.s x.p fr) ((x.AB.map fun w => resid x.p (-1 * w)).map (· / oDig x.p))
  zl : SegN μ (oaZL x.n x.s x.p fr) ((x.AB.map fun w => resid x.p (-1 * w)).map (· % oDig x.p))

/-- The addresses, one behind the other. -/
theorem oAddrs_eq (n s p fr : ℕ) :
    oaRNBC n fr = fr + n * n ∧ oaRNAB n fr = oaRNBC n fr + n * n ∧
      oaNL n fr = oaRNAB n fr + n * n ∧ oaHK n p fr = oaNL n fr + oDig p ∧
      oaRS n p fr = oaHK n p fr + oDig p ∧ oaRV n s p fr = oaRS n p fr + oNP n s p ∧
      oaDK n s p fr = oaRV n s p fr + oNP n s p ∧
      oaZH n s p fr = oaDK n s p fr + oDig p * oDig p ∧ oaZL n s p fr = oaZH n s p fr + n * n ∧
      oaX n s p fr = oaZL n s p fr + n * n ∧ oaY n s p fr = oaX n s p fr + oSz n s p ∧
      oB0 n s p fr = oaY n s p fr + oSz n s p :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The tables stay if no cell between fr and the sources changes. -/
theorem BTabs.congr {x : OracleInst} {fr : ℕ} {μ μ' : ℕ → ℤ} (h : BTabs x fr μ)
    (hAB : x.AB.length = x.n * x.n) (hBC : x.BC.length = x.n * x.n)
    (hAC : x.AC.length = x.n * x.n)
    (he : ∀ b, fr ≤ b → b < oaX x.n x.s x.p fr → μ' b = μ b) : BTabs x fr μ' := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, -, -⟩ := oAddrs_eq x.n x.s x.p fr
  have hk : oDig x.p ≤ oDig x.p * oDig x.p := Nat.le_mul_self _
  refine ⟨h.rac.congr fun i hi => he _ ?_ ?_, h.rnbc.congr fun i hi => he _ ?_ ?_,
    h.nl.congr fun i hi => he _ ?_ ?_, h.hk.congr fun i hi => he _ ?_ ?_,
    h.rs.congr fun i hi => he _ ?_ ?_, h.rv.congr fun i hi => he _ ?_ ?_,
    h.zh.congr fun i hi => he _ ?_ ?_, h.zl.congr fun i hi => he _ ?_ ?_⟩ <;>
    simp only [List.length_map, List.length_range, hAB, hBC, hAC] at hi <;> omega

/-- The four calls of a batch. -/
def oBatchTail : Stmt :=
  .call pWriteSrc [v aX, v aRAC, v aNL, v aRS, v Nn, v Kd, v Pr, v Dd, v N0, v J0, v KKb, v S,
    v Sz] Tmp ;;
  .call pWriteSrc [v aY, v aRNBC, v aHK, v aRS, v Nn, v Kd, v Pr, v Dd, v N0, v J0, v KKb, v S,
    v Sz] Tmp ;;
  .call Proc.preCore [v Ll, v Mm, v Tt, v Nv, v Dd, v aX, v aY, v B0] Tmp ;;
  .call pQueries [v B0, v aZL, v aZH, v aRV, v Nn, v Kd, v N0, v K0, v KKb, v Cnt, v J0] Tmp

theorem oBatch_eq : oBatch = (.set J0 (v Bn *' v KK) ;;
    .ite (v J0 +' v KK ≤' v Tp) (.set KKb (v KK)) (.set KKb (v Tp -' v J0)) ;; oBatchTail) := rfl

/-- The time of the calls of a batch. -/
def tOBTail (n s p : ℕ) : ℕ :=
  2 * tWriteSrc (oSz n s p) (oKK s p) n (oDig p) s + tPreCore cShared30 (oPar n s p) (oT s p)
    + tQueries (oKK s p) n (tQueryAt (oL s p) (oM s p) (oT s p)) + 100

theorem le_ceilDiv_mul (a b : ℕ) (hb : 1 ≤ b) : a ≤ a ⌈/⌉ b * b := by
  by_contra h
  exact lt_irrefl _ ((Nat.lt_ceilDiv_iff hb).2 (Nat.lt_of_not_le h))

/-- The parameters, as the oracle needs them. -/
theorem oParams_facts {n s p : ℕ} (hs : 1 ≤ s) (hp : 1 ≤ p) :
    1 ≤ oDig p ∧ oDig p ≤ p ∧ p ≤ oDig p * oDig p ∧ 1 ≤ oN0 s p ∧ 1 ≤ oK0 s p ∧
      1 ≤ oKK s p ∧ 1 ≤ oM s p ∧ oM s p ≤ oL s p ∧ oT s p ≤ oM s p ∧ 1 ≤ oD s p ∧
      s * p ≤ oD s p ∧ n * oDig p ≤ oNP n s p ∧ oNP n s p = oNb n s p * oN0 s p ∧
      oNv n s p = oK0 s p * oNP n s p ∧ oKK s p = oK0 s p * oK0 s p ∧
      oSz n s p = oKK s p * oNP n s p * oD s p := by
  have h1 := one_le_oM hs hp
  have h4 := four_mul_le_oD s p
  refine ⟨one_le_oDig p, ?_, le_oDig_sq p, one_le_oN0 s p, one_le_oK0 s p, one_le_oKK s p, h1,
    by unfold oL; omega, oT_le s p, Nat.one_le_pow _ _ (by norm_num), by
      have : s * p ≤ 4 * s * p := by
        rw [Nat.mul_assoc 4]; exact Nat.le_mul_of_pos_left _ (by norm_num)
      omega, ?_, rfl, rfl, rfl, rfl⟩
  · unfold oDig
    have := Nat.sqrt_le_self (p - 1)
    omega
  · unfold oNP oNb
    have := le_ceilDiv_mul (n * oDig p) (oN0 s p) (one_le_oN0 s p)
    rw [Nat.add_mul, Nat.one_mul]
    omega

theorem oSharedEnd_eq_add (p : Sec2.Par) (b0 : ℕ) : p.sharedEnd b0 = b0 + p.sharedEnd 0 := by
  simp only [Sec2.Par.sharedEnd, Sec2.Par.aZS, Sec2.Par.aARR, Sec2.Par.aENCB, Sec2.Par.aENCA,
    Sec2.Par.aDIG4, Sec2.Par.aDIG3, Sec2.Par.aBLOCK, Sec2.Par.aBAND, Sec2.Par.aMASK, Sec2.Par.aPSI,
    Sec2.Par.aPHI, Sec2.Par.aPAS, Sec2.Par.aP10, Sec2.Par.aP7, Sec2.Par.aP4, Sec2.Par.aP3]
  omega

theorem oTop_eq_add (p : Sec2.Par) (t b0 : ℕ) : top p t b0 = b0 + top p t 0 := by
  have h1 := top_sub_eq p t b0
  have h2 := top_sub_eq p t 0
  have h3 := base_le_top p t b0
  have h4 := oSharedEnd_eq_add p b0
  omega

set_option maxHeartbeats 1000000 in
theorem oBatchTail_ends (R : Program) {lim : Limits} {d : ℕ} {x : OracleInst} {μ₀ μ : ℕ → ℤ}
    {fr : ℕ} (hpre : x.Pre μ₀ fr) (hok : (oNeedAt x.n x.U x.s x.p).Ok lim fr d) {bt kb : ℕ}
    (hkb1 : 1 ≤ kb) (hkbK : kb ≤ oKK x.s x.p) (hkbT : bt * oKK x.s x.p + kb ≤ oProd x.n x.s)
    (tmp : ℤ) (hT : BTabs x fr μ) :
    Ends lim (oProg ++ R) d oBatchTail
      ⟨frame (oLocA x fr tmp bt (bt * oKK x.s x.p : ℕ) kb), μ⟩ (tOBTail x.n x.s x.p)
      fun σ' => ∃ tmp' : ℤ, σ'.loc = frame (oLocA x fr tmp' bt (bt * oKK x.s x.p : ℕ) kb) ∧
        BTabs x fr σ'.mem ∧
        (∀ e < kb * (x.n * x.n), σ'.mem (x.cnt + bt * oKK x.s x.p * (x.n * x.n) + e)
          = (cntOf x.n x.s x.p x.AB x.BC x.AC (bt * oKK x.s x.p * (x.n * x.n) + e) : ℤ)) ∧
        (∀ b < fr, (b < x.cnt + bt * oKK x.s x.p * (x.n * x.n) ∨
          x.cnt + bt * oKK x.s x.p * (x.n * x.n) + kb * (x.n * x.n) ≤ b) → σ'.mem b = μ b) := by
  have h100 : ((100 : ℕ) : ℤ) ≤ lim.word := oWordSum_fits hok
  have std : Std lim := ⟨hok.space, by exact_mod_cast h100⟩
  have hsw := hok.space
  have hcells := hok.cells
  have hdepth := hok.depth
  simp only [oNeedAt, oCells] at hcells hdepth
  obtain ⟨hk1, hkp, hpk, hN01, hK01, hKK1, hm1, hmL, htm, hD1, hspD, hnk, hNP, hNv, hKK, hSz⟩ :=
    oParams_facts (n := x.n) hpre.s_pos hpre.p_pos
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12⟩ := oAddrs_eq x.n x.s x.p fr
  have hB0 := oB0_eq x.n x.s x.p fr
  have htop := oTop_eq_add (oPar x.n x.s x.p) (oT x.s x.p) (oB0 x.n x.s x.p fr)
  have hlenAB := hpre.lenAB
  have hlenBC := hpre.lenBC
  have hlenAC := hpre.lenAC
  have hW : (oProg ++ R)[pWriteSrc]? = some writeSrcBody := oProg_at 82 (R := R)
  have hF : FillSpec lim (oProg ++ R) := fill_ok (oProg_at31 59 (R := R)) std
  have hWS := writeSrc_ok hW hF
  -- the left source
  have preX : WriteSrcPre lim μ (oaX x.n x.s x.p fr) fr (oaNL x.n fr) (oaRS x.n x.p fr) x.n
      (oDig x.p) x.p (oD x.s x.p) (oN0 x.s x.p) (bt * oKK x.s x.p) kb x.s (oKK x.s x.p)
      (oNP x.n x.s x.p) (x.AC.map fun w => resid x.p (1 * w))
      ((List.range (oDig x.p)).map fun h : ℕ => resid x.p ((x.p : ℤ) - h)) :=
    { std := std
      p_pos := hpre.p_pos
      N0_pos := hN01
      k_pos := hk1
      D_pos := hD1
      seg1 := hT.rac
      len1 := by simp [hlenAC]
      lt1 := by
        intro z hz
        obtain ⟨w, -, rfl⟩ := List.mem_map.1 hz
        exact resid_lt hpre.p_pos _
      seg2 := hT.nl
      len2 := by simp
      lt2 := by
        intro z hz
        obtain ⟨w, -, rfl⟩ := List.mem_map.1 hz
        exact resid_lt hpre.p_pos _
      segRS := hT.rs
      NP_mul := ⟨oNb x.n x.s x.p, by rw [hNP, Nat.mul_comm]⟩
      nk_le := hnk
      KKb_le := hkbK
      blocks := by
        intro u hu
        have : bt * oKK x.s x.p + u < oProd x.n x.s := by omega
        exact (Nat.lt_ceilDiv_iff hpre.s_pos).1 this
      sp_le := hspD
      space := by rw [← hSz]; omega
      apart1 := by rw [← hSz]; omega
      apart2 := by rw [← hSz]; omega
      apartRS := by rw [← hSz]; omega
      below1 := by omega
      below2 := by omega
      belowRS := by omega
      word := by
        have hle : (bt * oKK x.s x.p + kb + 1) * (x.s + 1)
            ≤ (oProd x.n x.s + oKK x.s x.p + 1) * (x.s + 1) := Nat.mul_le_mul_right _ (by omega)
        exact oWordSum_fits hok (by apply le_oWordSum_of; omega) }
  have hWX := (hWS _ _ _ _ _ _ _ _ _ bt kb _ _ _ _ _ μ (d + 1) preX (by omega)).mono_time
    (T' := tWriteSrc (oSz x.n x.s x.p) (oKK x.s x.p) x.n (oDig x.p) x.s) (by
      rw [hSz]; unfold tWriteSrc; gcongr)
  unfold oBatchTail tOBTail
  light_call hWX using oLocA, hSz with r₁ μ₁ ⟨hX, hso₁⟩
  have hT₁ : BTabs x fr μ₁ := hT.congr hlenAB hlenBC hlenAC fun b h1 h2 => hso₁ b (Or.inl h2)
  -- the right source
  have preY : WriteSrcPre lim μ₁ (oaY x.n x.s x.p fr) (oaRNBC x.n fr) (oaHK x.n x.p fr) (oaRS x.n x.p fr) x.n
      (oDig x.p) x.p (oD x.s x.p) (oN0 x.s x.p) (bt * oKK x.s x.p) kb x.s (oKK x.s x.p)
      (oNP x.n x.s x.p) (x.BC.map fun w => resid x.p (-1 * w))
      ((List.range (oDig x.p)).map fun h : ℕ => resid x.p ((h * oDig x.p : ℕ) : ℤ)) :=
    { std := std
      p_pos := hpre.p_pos
      N0_pos := hN01
      k_pos := hk1
      D_pos := hD1
      seg1 := hT₁.rnbc
      len1 := by simp [hlenBC]
      lt1 := by
        intro z hz
        obtain ⟨w, -, rfl⟩ := List.mem_map.1 hz
        exact resid_lt hpre.p_pos _
      seg2 := hT₁.hk
      len2 := by simp
      lt2 := by
        intro z hz
        obtain ⟨w, -, rfl⟩ := List.mem_map.1 hz
        exact resid_lt hpre.p_pos _
      segRS := hT₁.rs
      NP_mul := ⟨oNb x.n x.s x.p, by rw [hNP, Nat.mul_comm]⟩
      nk_le := hnk
      KKb_le := hkbK
      blocks := by
        intro u hu
        have : bt * oKK x.s x.p + u < oProd x.n x.s := by omega
        exact (Nat.lt_ceilDiv_iff hpre.s_pos).1 this
      sp_le := hspD
      space := by rw [← hSz]; omega
      apart1 := by rw [← hSz]; omega
      apart2 := by rw [← hSz]; omega
      apartRS := by rw [← hSz]; omega
      below1 := by omega
      below2 := by omega
      belowRS := by omega
      word := by
        have hle : (bt * oKK x.s x.p + kb + 1) * (x.s + 1)
            ≤ (oProd x.n x.s + oKK x.s x.p + 1) * (x.s + 1) := Nat.mul_le_mul_right _ (by omega)
        exact oWordSum_fits hok (by apply le_oWordSum_of; omega) }
  have hWY := (hWS _ _ _ _ _ _ _ _ _ bt kb _ _ _ _ _ μ₁ (d + 1) preY (by omega)).mono_time
    (T' := tWriteSrc (oSz x.n x.s x.p) (oKK x.s x.p) x.n (oDig x.p) x.s) (by
      rw [hSz]; unfold tWriteSrc; gcongr)
  light_call hWY using oLocA, hSz with r₂ μ₂ ⟨hY, hso₂⟩
  have hT₂ : BTabs x fr μ₂ := hT₁.congr hlenAB hlenBC hlenAC fun b h1 h2 => hso₂ b (Or.inl (by omega))
  -- the data structure
  set pv := oPar x.n x.s x.p with hpv
  have hmL' : pv.m ≤ pv.L := hmL
  have hpL : pv.L = oL x.s x.p := rfl
  have hDeq : ThreeSumApsp.D pv.m = oD x.s x.p := rfl
  have hrows : pv.K0 * pv.N = oKK x.s x.p * oNP x.n x.s x.p := by
    change oK0 x.s x.p * oNv x.n x.s x.p = _
    rw [hNv, hKK, Nat.mul_assoc]
  set X := srcMat (pv.K0 * pv.N) (ThreeSumApsp.D pv.m) x.n x.s x.p (oDig x.p)
    (bt * oKK x.s x.p + kb) (oKK x.s x.p) pv.N0 bt (t1X x.p x.AC) (t2X x.p) with hXdef
  set Y := (srcMat (pv.K0 * pv.N) (ThreeSumApsp.D pv.m) x.n x.s x.p (oDig x.p)
    (bt * oKK x.s x.p + kb) (oKK x.s x.p) pv.N0 bt (t1Y x.p x.BC) (t2Y x.p (oDig x.p))).transpose
    with hYdef
  have hMX : MatAt μ₂ (oaX x.n x.s x.p fr) X := by
    refine matAt_src (fun ρ hρ κ hκ => ?_) (fun u R cl h => fGen_tabX hlenAC hk1 hkp h)
    rw [hrows] at hρ
    rw [hDeq] at hκ ⊢
    rw [hso₂ _ (Or.inl (by
      have : ρ * oD x.s x.p + κ < oSz x.n x.s x.p := by
        rw [hSz]
        calc ρ * oD x.s x.p + κ < ρ * oD x.s x.p + oD x.s x.p := by omega
          _ = (ρ + 1) * oD x.s x.p := by ring
          _ ≤ oKK x.s x.p * oNP x.n x.s x.p * oD x.s x.p := Nat.mul_le_mul_right _ hρ
      omega))]
    exact hX ρ hρ κ hκ
  have hMY : MatAt μ₂ (oaY x.n x.s x.p fr) Y.transpose := by
    rw [hYdef, Matrix.transpose_transpose]
    refine matAt_src (fun ρ hρ κ hκ => ?_) (fun u R cl h => fGen_tabY hlenBC hk1 h)
    rw [hrows] at hρ
    rw [hDeq] at hκ ⊢
    exact hY ρ hρ κ hκ
  have habs : ∀ {T1 T2 : ℕ → ℕ} (i : Fin (pv.K0 * pv.N)) (j : Fin (ThreeSumApsp.D pv.m)),
      |srcMat (pv.K0 * pv.N) (ThreeSumApsp.D pv.m) x.n x.s x.p (oDig x.p)
        (bt * oKK x.s x.p + kb) (oKK x.s x.p) pv.N0 bt T1 T2 i j| ≤ 1 := by
    intro T1 T2 i j
    unfold srcMat srcVal
    split_ifs <;> simp
  have hXb : ∀ i j, |X i j| ≤ 1 := fun i j => habs i j
  have hYb : ∀ i j, |Y i j| ≤ 1 := fun i j => habs j i
  have hval : ((10 ^ oM x.s x.p * (7 ^ oL x.s x.p * 7 ^ oL x.s x.p) : ℕ) : ℤ) ≤ lim.word :=
    oWordSum_fits hok
  have henc : ((7 ^ (oL x.s x.p + 1) : ℕ) : ℤ) ≤ lim.word := oWordSum_fits hok
  have hten : ((10 ^ (oL x.s x.p + 1) : ℕ) : ℤ) ≤ lim.word := oWordSum_fits hok
  have hlim : Lim30 lim pv (oT x.s x.p) (oB0 x.n x.s x.p fr) 1 :=
    { std := std
      space := by
        change top pv (oT x.s x.p) (oB0 x.n x.s x.p fr) ≤ lim.space
        rw [htop]
        omega
      value := by simp only [mul_one]; exact_mod_cast hval
      enc := by simp only [mul_one]; exact_mod_cast henc
      pow := hten }
  have hND : pv.K0 * pv.N * pv.D = oSz x.n x.s x.p := by
    rw [hrows, hSz]; rfl
  have hpad : padN pv.L pv.m pv.N = pv.N := by
    have hbs : bandSize pv.L pv.m = oK0 x.s x.p * oN0 x.s x.p := rfl
    have hN : pv.N = oNb x.n x.s x.p * (oK0 x.s x.p * oN0 x.s x.p) := by
      change oNv x.n x.s x.p = _
      rw [hNv, hNP]; ring
    have hpos : 0 < oK0 x.s x.p * oN0 x.s x.p := Nat.mul_pos hK01 hN01
    unfold padN numBands
    rw [hbs, hN, Nat.add_sub_assoc hpos, Nat.add_comm (oNb x.n x.s x.p * _),
      Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt (by omega), Nat.zero_add]
  have hPre : PreCoreBSpec lim (oProg ++ R) cShared30 := by
    rw [show oProg ++ R = base58B ++ (procs31 G20 ++ oProcs ++ R) by simp [oProg]]
    exact preCoreB_base58B _ lim std
  have hPX := hPre pv (oT x.s x.p) hmL' (oaX x.n x.s x.p fr) (oaY x.n x.s x.p fr)
    (oB0 x.n x.s x.p fr) X Y 1 μ₂ htm hlim zero_le_one hXb hYb hMX hMY (by rw [hND]; omega)
    (by rw [hND]; omega) hpad
  have hpN : pv.N = oNv x.n x.s x.p := rfl
  have hpD : pv.D = oD x.s x.p := rfl
  have hpm : pv.m = oM x.s x.p := rfl
  have hpN0 : pv.N0 = oN0 x.s x.p := rfl
  have hpK0 : pv.K0 = oK0 x.s x.p := rfl
  light_call hPX using oLocA, hpN, hpD, hpm, hpL with r₃ μ₃ ⟨hds, hso₃⟩
  -- the queries
  have hT₃ : BTabs x fr μ₃ := hT₂.congr hlenAB hlenBC hlenAC fun b h1 h2 => hso₃ b (Or.inl (by omega))
  have hlen : x.len = oProd x.n x.s * (x.n * x.n) := rfl
  have hcntB := hpre.belowCnt
  have hjk : (bt * oKK x.s x.p + kb) * (x.n * x.n) ≤ oProd x.n x.s * (x.n * x.n) :=
    Nat.mul_le_mul_right _ hkbT
  have hjk' : (bt * oKK x.s x.p + kb) * (x.n * x.n)
      = bt * oKK x.s x.p * (x.n * x.n) + kb * (x.n * x.n) := by ring
  have hQA : QueryAtASpec lim (oProg ++ R) := by
    rw [show oProg ++ R = base58B ++ (procs31 G20 ++ oProcs ++ R) by simp [oProg]]
    exact queryAtA_base58B _ lim std
  have hnz : ∀ z ∈ x.AB.map (fun w => resid x.p (-1 * w)), z < oDig x.p * oDig x.p := by
    intro z hz
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hz
    exact lt_of_lt_of_le (resid_lt hpre.p_pos _) hpk
  have S : QSet lim (oProg ++ R) pv (oT x.s x.p) (oaX x.n x.s x.p fr) (oaY x.n x.s x.p fr)
      (oB0 x.n x.s x.p fr) (batchL pv hmL' X) (batchR pv hmL' Y) 1 μ₃ (oaZL x.n x.s x.p fr)
      (oaZH x.n x.s x.p fr) (oaRV x.n x.s x.p fr) x.n (oDig x.p) (oNP x.n x.s x.p) kb x.cnt
      (bt * oKK x.s x.p) ((x.AB.map fun w => resid x.p (-1 * w)).map (· % oDig x.p))
      ((x.AB.map fun w => resid x.p (-1 * w)).map (· / oDig x.p)) :=
    { hq := hQA
      ht := htm
      hlim := hlim
      hb := boundA_batch hmL' zero_le_one hXb hYb
      segZL := hT₃.zl
      segZH := hT₃.zh
      lenZL := by simp [hlenAB]
      lenZH := by simp [hlenAB]
      ltZL := by
        intro z hz
        obtain ⟨w, -, rfl⟩ := List.mem_map.1 hz
        exact Nat.mod_lt _ hk1
      ltZH := by
        intro z hz
        obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hz
        exact Nat.div_lt_of_lt_mul (hnz w hw)
      segRV := hT₃.rv
      hN := hNv
      n_pos := hpre.n_pos
      NP_mul := ⟨oNb x.n x.s x.p, by rw [hNP, Nat.mul_comm]; rfl⟩
      nk_le := hnk
      KKb_le := by change kb ≤ oK0 x.s x.p * oK0 x.s x.p; rw [← hKK]; exact hkbK
      belowZL := by omega
      belowZH := by omega
      belowRV := by omega
      belowCnt := by omega
      apZL := by omega
      apZH := by omega
      apRV := by omega }
  have hQP : (oProg ++ R)[pQueries]? = some queriesBody := oProg_at 83 (R := R)
  have hQ := (queries_ok (d := d + 1) hQP S hmL' (by omega) hds).mono_time
    (T' := tQueries (oKK x.s x.p) x.n (tQueryAt (oL x.s x.p) (oM x.s x.p) (oT x.s x.p)))
    (by unfold tQueries; exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hkbK) _)
  light_head
  refine Ends.callToThen hQ ?_ ?_ ?_ ?_
  rotate_left
  · light_side [oLocA, hpN, hpD, hpm, hpL, hpN0, hpK0]
  · omega
  · simp only [Cond.cost, Expr.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    generalize tQueries _ _ _ = A
    generalize tWriteSrc _ _ _ _ _ = B
    generalize tPreCore _ _ _ = C
    omega
  · intro r₄ μ₄ hQI
    light_skip
    obtain ⟨-, hans, hkeep⟩ := hQI
    refine ⟨r₄, rfl, ?_, ?_, ?_⟩
    · exact hT₃.congr hlenAB hlenBC hlenAC fun b h1 h2 => hkeep b (by omega) (Or.inr (by omega))
    · intro e he
      change μ₄ _ = _
      rw [hans e he]
      exact qAns_eq_cntOf hmL' htm hpre.p_pos hpk hkp hspD hKK hNP hNv hnk hkbK hlenAB he
    · intro b hb hor
      change μ₄ b = μ b
      rw [hkeep b (by omega) hor, hso₃ b (Or.inl (by omega)), hso₂ b (Or.inl (by omega)),
        hso₁ b (Or.inl (by omega))]

end Light.Batch
