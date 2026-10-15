/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Batch.BandArrayB
public import Submission.ThreeSumApsp.Batch.Ready
public import Submission.ThreeSumApsp.Programs.Sec2.PrunedEnc.SharedStage

/-!
# The shared stage with batched band arrays

The procedure sharedP and its callees are unchanged, but for the body of bandArray, which is
`bandArrayBBody`. Then the shared stage leaves the pruned encodings of the batched arrays
`bArrayL (stdLayout hmL) X β` and `bArrayR (stdLayout hmL) Y β` behind, where the source X is
`K₀ N × D`, row by row at aX, and the source Y is `D × K₀ N`, stored as its transpose at aY.

* `EncodeBandsPLBSpec`, `EncodeBandsPRBSpec`: encodeBandsP for the batched arrays.
* `SharedCalleesB`, `SharedPreB`, `SharedSpecB`, `sharedPB_entry`: the shared stage.
-/

@[expose] public section

namespace Light.Batch

open ThreeSumApsp Light.Sec2 Light.Sec2.Shared

variable {lim : Limits} {P : Program}

/-! ## The encodings of all bands -/

/-- encodeBandsP for the batched row bands of the source X. -/
def EncodeBandsPLBSpec (lim : Limits) (P : Program) (c : ℕ) : Prop :=
  ∀ (p : Par) (hmL : p.m ≤ p.L) (x : BandsArgs) (aX : ℕ) (μ : ℕ → ℤ)
    (X : Matrix (Fin (p.K0 * p.N)) (Fin (ThreeSumApsp.D p.m)) ℤ) (V : ℤ),
    BandsPre lim p μ x Spec.phiFlat V → MatAt μ aX X → aX + p.K0 * p.N * p.D ≤ x.enc →
    (∀ i j, |X i j| ≤ V) → padN p.L p.m p.N = p.N →
    ∀ d, d + (p.L + 2) ≤ lim.depth → Meets lim P pEncodeBandsP d (x.vals p 0 aX p.D 1) μ
      (c * (p.nB * (retW p.L p.m + bandArrayShape p) + 1)) fun _ μ' =>
        (∀ β < p.nB, RetSeg p.L p.m μ' (x.enc + β * p.T)
          (Spec.arrT (encodingL (ThreeSumApsp.Batch.bArrayL (Spec.stdLayout hmL) X β)))) ∧
          SameOutside μ μ' x.enc (x.zs + p.S7 - x.enc)

/-- encodeBandsP for the batched column bands of the source Y, stored as its transpose. -/
def EncodeBandsPRBSpec (lim : Limits) (P : Program) (c : ℕ) : Prop :=
  ∀ (p : Par) (hmL : p.m ≤ p.L) (x : BandsArgs) (aY : ℕ) (μ : ℕ → ℤ)
    (Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin (p.K0 * p.N)) ℤ) (V : ℤ),
    BandsPre lim p μ x Spec.psiFlat V → MatAt μ aY Y.transpose → aY + p.K0 * p.N * p.D ≤ x.enc →
    (∀ i j, |Y i j| ≤ V) → padN p.L p.m p.N = p.N →
    ∀ d, d + (p.L + 2) ≤ lim.depth → Meets lim P pEncodeBandsP d (x.vals p 1 aY 1 p.N) μ
      (c * (p.nB * (retW p.L p.m + bandArrayShape p) + 1)) fun _ μ' =>
        (∀ β < p.nB, RetSeg p.L p.m μ' (x.enc + β * p.T)
          (Spec.arrT (encodingR (ThreeSumApsp.Batch.bArrayR (Spec.stdLayout hmL) Y β)))) ∧
          SameOutside μ μ' x.enc (x.zs + p.S7 - x.enc)

theorem encodeBandsPLB_entry (std : Std lim) (hP : P[pEncodeBandsP]? = some encodeBandsPBody)
    {cB cE c : ℕ} (hB : BandArrayBLSpec lim P cB) (hE : EncodePLSpec lim P cE)
    (hc : cB + cE + 50 ≤ c) : EncodeBandsPLBSpec lim P c := by
  intro p hmL x aX μ X V pre hM hMle hV hpad d hd
  light_facts pre
  refine .mono_const ?_ hc
  refine encodeBandsP_proc std hP pre (by omega) (fun β => Spec.length_arrT _)
    (A := fun β => Spec.arrL (ThreeSumApsp.Batch.bArrayL (Spec.stdLayout hmL) X β))
    (fun β hβ μ' hlow => ?_) fun β hβ μ' hlow hA => ?_
  · simpa using hB p hmL β aX x.mask x.dig3 x.dig4 x.arr μ' X (by omega)
      (hM.congr_below hlow hMle) (by omega) ((pre.tables.congr_below hlow).mono (by omega)) hβ
      hpad _ (by omega)
  · exact hE p.L p.L x.arr (x.enc + β * p.T) x.zs x.tab x.p7 x.p10 p.m μ' _ V
      (pre.encodePlaces hβ hlow)
      (pre.coef.congr fun i hi => hlow _ (by
        have := Spec.length_phiFlat
        omega))
      hA (ThreeSumApsp.Batch.abs_bArrayL_le (Spec.stdLayout hmL) pre.V_nonneg hV β) pre.word _
      (by omega)

theorem encodeBandsPRB_entry (std : Std lim) (hP : P[pEncodeBandsP]? = some encodeBandsPBody)
    {cB cE c : ℕ} (hB : BandArrayBRSpec lim P cB) (hE : EncodePRSpec lim P cE)
    (hc : cB + cE + 50 ≤ c) : EncodeBandsPRBSpec lim P c := by
  intro p hmL x aY μ Y V pre hM hMle hV hpad d hd
  light_facts pre
  refine .mono_const ?_ hc
  refine encodeBandsP_proc std hP pre (by omega) (fun β => Spec.length_arrT _)
    (A := fun β => Spec.arrR (ThreeSumApsp.Batch.bArrayR (Spec.stdLayout hmL) Y β))
    (fun β hβ μ' hlow => ?_) fun β hβ μ' hlow hA => ?_
  · simpa using hB p hmL β aY x.mask x.dig3 x.dig4 x.arr μ' Y (by omega)
      (hM.congr_below hlow hMle) (by omega) ((pre.tables.congr_below hlow).mono (by omega)) hβ
      hpad _ (by omega)
  · exact hE p.L p.L x.arr (x.enc + β * p.T) x.zs x.tab x.p7 x.p10 p.m μ' _ V
      (pre.encodePlaces hβ hlow)
      (pre.coef.congr fun i hi => hlow _ (by
        have := Spec.length_psiFlat
        omega))
      hA (ThreeSumApsp.Batch.abs_bArrayR_le (Spec.stdLayout hmL) pre.V_nonneg hV β) pre.word _
      (by omega)

/-! ## The shared stage -/

/-- The entries of the routines that the shared stage calls, with the batched encodeBandsP. -/
structure SharedCalleesB (lim : Limits) (P : Program) (c : ℕ) : Prop where
  pow : PowSpec lim P c
  binom : BinomSpec lim P c
  sqrt : SqrtSpec lim P c
  coef : CoefSpec lim P c
  subsets : SubsetsSpec lim P c
  counters : CountersSpec lim P c
  digits : DigitsSpec lim P c
  bandsL : EncodeBandsPLBSpec lim P c
  bandsR : EncodeBandsPRBSpec lim P c

/-- The entry of pow, for a table of the powers b^0, …, b^L of a base b ≤ 10. -/
theorem SharedCalleesB.powTable {c : ℕ} (C : SharedCalleesB lim P c) {p : Par}
    (h10 : ((10 ^ (p.L + 1) : ℕ) : ℤ) ≤ lim.word) (b dst : ℕ) (μ : ℕ → ℤ)
    (one_le : 1 ≤ b := by omega) (le_ten : b ≤ 10 := by omega) (dst_pos : 1 ≤ dst := by omega)
    (dst_le : dst + (p.L + 1) ≤ lim.space := by omega) :
    ∀ d, d ≤ lim.depth → Meets lim P pPow d [b, p.L, dst] μ (c * (p.L + 1)) fun _ μ' =>
      Seg μ' dst (powList b (p.L + 1)) ∧ SameOutside μ μ' dst (p.L + 1) :=
  C.pow b p.L dst μ dst_pos dst_le one_le
    (le_trans (by exact_mod_cast Nat.pow_le_pow_left le_ten _) h10)

/-- **The first part of shared.** -/
theorem sharedAPB_spec (std : Std lim) {c : ℕ} (C : SharedCalleesB lim P c) {d : ℕ} {p : Par}
    (hmL : p.m ≤ p.L) {aX aY b0 : ℕ} (hd : d + (p.L + 3) ≤ lim.depth)
    (hsp : p.sharedEnd b0 ≤ lim.space) (h10 : ((10 ^ (p.L + 1) : ℕ) : ℤ) ≤ lim.word)
    (μ : ℕ → ℤ) :
    Ends lim P d sharedA ⟨frame (sharedLoc0 p aX aY b0), μ⟩ (sharedTimeA c p) fun σ' =>
      (∃ r, σ'.loc = frame (sharedLocA p aX aY b0 r)) ∧ SharedA p b0 μ σ'.mem := by
  have hw := std.space_le
  have h100 := std.const_le
  have hplaces := p.places b0
  have hsizes := p.sizes hmL
  have hTw := Par.ten_T_le h10
  unfold sharedA sharedTimeA sharedLoc0
  -- the addresses of the first eight areas
  light_set (p.aP3 b0 : ℕ)
  light_set (p.aP4 b0 : ℕ)
  light_set (p.aP7 b0 : ℕ)
  light_set (p.aP10 b0 : ℕ)
  light_set (p.aPAS b0 : ℕ)
  light_set (p.aPHI b0 : ℕ)
  light_set (p.aPSI b0 : ℕ)
  light_set (p.aMASK b0 : ℕ)
  -- the powers of 3, 4, 7 and 10
  light_call (C.powTable h10 3 (p.aP3 b0) μ) with rP3 μP3 ⟨sP3, fP3⟩
  light_call (C.powTable h10 4 (p.aP4 b0) μP3) with rP4 μP4 ⟨sP4, fP4⟩
  light_call (C.powTable h10 7 (p.aP7 b0) μP4) with rP7 μP7 ⟨sP7, fP7⟩
  light_call (C.powTable h10 10 (p.aP10 b0) μP7) with rP10 μP10 ⟨sP10, fP10⟩
  have hA := SharedA.of_calls sP3 fP3 sP4 fP4 sP7 fP7 sP10 fP10
  -- L - m, and then N₀ = 3^{L-m}, 10^L and 7^L from the tables
  have read : ∀ {b a i : ℕ}, Seg μP10 a (powList b (p.L + 1)) → i ≤ p.L →
      μP10 (a + i) = (b ^ i : ℕ) :=
    fun h hi => by rw [h.get (by rw [length_powList]; omega), getElem_powList]
  have hN0 : μP10 (p.aP3 b0 + p.Lo) = (p.N0 : ℕ) := read hA.p3 (by omega)
  have hT : μP10 (p.aP10 b0 + p.L) = (p.T : ℕ) := read hA.p10 le_rfl
  have hS7 : μP10 (p.aP7 b0 + p.L) = (p.S7 : ℕ) := read hA.p7 le_rfl
  light_set (p.Lo : ℕ)
  light_set (p.N0 : ℕ) using hN0
  light_set (p.T : ℕ) using hT
  light_set (p.S7 : ℕ) using hS7
  exact ⟨⟨rP10, rfl⟩, hA⟩


/-- **The second part of shared.** -/
theorem sharedBPB_spec (std : Std lim) {c : ℕ} (C : SharedCalleesB lim P c) {d : ℕ} {p : Par}
    (hmL : p.m ≤ p.L) {aX aY b0 : ℕ} (hd : d + (p.L + 3) ≤ lim.depth)
    (hsp : p.sharedEnd b0 ≤ lim.space) (h10 : ((10 ^ (p.L + 1) : ℕ) : ℤ) ≤ lim.word)
    (μ : ℕ → ℤ) (r0 : ℤ) :
    Ends lim P d sharedB ⟨frame (sharedLocA p aX aY b0 r0), μ⟩ (sharedTimeB c p) fun σ' =>
      (∃ r, σ'.loc = frame (sharedLocB p aX aY b0 r)) ∧ SharedB p b0 μ σ'.mem := by
  have hw := std.space_le
  have h100 := std.const_le
  have hplaces := p.places b0
  have hsizes := p.sizes hmL
  have eKK : p.KK = p.K0 * p.K0 := rfl
  have hTw := Par.ten_T_le h10
  unfold sharedB sharedTimeB sharedLocA
  -- K := binom(L, m)
  light_call (C.binom p.L p.m (p.aPAS b0) μ (by omega) hmL
    (le_trans (by exact_mod_cast p.two_pow_le_T) (by omega : (p.T : ℤ) ≤ lim.word)))
    with r μPas ⟨hr, fPas⟩
  obtain rfl : r = (p.K : ℕ) := hr
  -- K₀ := ⌊√K⌋ and K₀²
  light_call (C.sqrt p.K μPas (by push_cast; omega)) with r μPas' ⟨hr, hμ⟩
  obtain rfl : r = (p.K0 : ℕ) := hr
  obtain rfl : μPas = μPas' := hμ.symm
  light_set (p.KK : ℕ)
  -- the coefficients and the table of subsets
  light_call (C.coef (p.aPHI b0) μPas (by omega)) with rPhi μPhi ⟨sphi, spsi, fPhi⟩
  light_call (C.subsets p.L p.m p.KK (p.aMASK b0) μPhi (by omega) hmL p.KK_le_K
    (by push_cast; omega)) with rMask μMask ⟨smask, fMask⟩
  -- band and block of every row
  light_set (p.aBAND b0 : ℕ)
  light_set (p.aBLOCK b0 : ℕ)
  light_set (p.aDIG3 b0 : ℕ)
  light_call (C.counters p.N p.K0 p.N0 (p.aBAND b0) μMask (by omega) (by omega)
    (by omega) (by push_cast; omega)) with rBand μBand ⟨sband, fBand⟩
  -- the digits of every row and of every column
  light_call (C.digits p.N 3 p.Lo (p.aDIG3 b0) μBand (by omega) (by norm_num)
    (by push_cast; omega) (by omega)) with rDig3 μDig3 ⟨sdig3, fDig3⟩
  light_set (p.aDIG4 b0 : ℕ)
  light_call (C.digits p.D 4 p.m (p.aDIG4 b0) μDig3 (by omega) (by norm_num)
    (by push_cast; omega) (by omega)) with rDig4 μDig4 ⟨sdig4, fDig4⟩
  light_set (p.aENCA b0 : ℕ)
  exact ⟨⟨rDig4, rfl⟩,
    .of_calls fPas sphi spsi fPhi smask fMask sband fBand sdig3 fDig3 sdig4 fDig4⟩


/-- What the shared stage assumes of the two sources. -/
structure SharedPreB (lim : Limits) (p : Par) (aX aY b0 : ℕ)
    (X : Matrix (Fin (p.K0 * p.N)) (Fin (ThreeSumApsp.D p.m)) ℤ)
    (Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin (p.K0 * p.N)) ℤ) (V : ℤ) (μ : ℕ → ℤ) : Prop where
  space : p.sharedEnd b0 ≤ lim.space
  matX : MatAt μ aX X
  matY : MatAt μ aY Y.transpose
  belowX : aX + p.K0 * p.N * p.D ≤ b0
  belowY : aY + p.K0 * p.N * p.D ≤ b0
  absX : ∀ i j, |X i j| ≤ V
  absY : ∀ i j, |Y i j| ≤ V
  V_nonneg : 0 ≤ V
  seven : 7 ^ (p.L + 1) * V ≤ lim.word
  ten : ((10 ^ (p.L + 1) : ℕ) : ℤ) ≤ lim.word
  pad : padN p.L p.m p.N = p.N

/-- The batched input arrays of the row bands. -/
abbrev batchL (p : Par) (hmL : p.m ≤ p.L)
    (X : Matrix (Fin (p.K0 * p.N)) (Fin (ThreeSumApsp.D p.m)) ℤ) : ArrL p :=
  fun β => ThreeSumApsp.Batch.bArrayL (Spec.stdLayout hmL) X β

/-- The batched input arrays of the column bands. -/
abbrev batchR (p : Par) (hmL : p.m ≤ p.L)
    (Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin (p.K0 * p.N)) ℤ) : ArrR p :=
  fun β => ThreeSumApsp.Batch.bArrayR (Spec.stdLayout hmL) Y β

/-- sharedP(L, m, N, D, aX, aY, b0), with the batched band arrays. -/
def SharedSpecB (lim : Limits) (P : Program) (c : ℕ) : Prop :=
  ∀ (p : Par) (hmL : p.m ≤ p.L) (aX aY b0 : ℕ) (μ : ℕ → ℤ)
    (X : Matrix (Fin (p.K0 * p.N)) (Fin (ThreeSumApsp.D p.m)) ℤ)
    (Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin (p.K0 * p.N)) ℤ) (V : ℤ),
    SharedPreB lim p aX aY b0 X Y V μ →
    ∀ d, d + (p.L + 3) ≤ lim.depth →
    Meets lim P pSharedP d [p.L, p.m, p.N, p.D, aX, aY, b0] μ (c * sharedShapeP p) fun _ μ' =>
      SharedReadyA p aX aY b0 (batchL p hmL X) (batchR p hmL Y) μ' ∧
        SameOutside μ μ' b0 (p.sharedEnd b0 - b0)

theorem SharedReadyA.of_calls {p : Par} {aX aY b0 : ℕ} {AL : ArrL p} {AR : ArrR p}
    {μ μEncA μEncB μDir : ℕ → ℤ} (tb : SharedTables p b0 μ)
    (sA : ∀ β < p.nB, RetSeg p.L p.m μEncA (p.aENCA b0 + β * p.T)
      (Spec.arrT (encodingL (AL β))))
    (fEncA : SameOutside μ μEncA (p.aENCA b0) (p.sharedEnd b0 - p.aENCA b0))
    (sB : ∀ β < p.nB, RetSeg p.L p.m μEncB (p.aENCB b0 + β * p.T)
      (Spec.arrT (encodingR (AR β))))
    (fEncB : SameOutside μEncA μEncB (p.aENCB b0) (p.sharedEnd b0 - p.aENCB b0))
    (sdir : SegN μDir b0 (dirList p aX aY b0)) (fDir : SameOutside μEncB μDir b0 31) :
    SharedReadyA p aX aY b0 AL AR μDir ∧ SameOutside μ μDir b0 (p.sharedEnd b0 - b0) := by
  have hplaces := p.places b0
  have above : ∀ x, p.aP3 b0 ≤ x → μDir x = μEncB x := fun x hx => fDir x (Or.inr (by omega))
  have tbDir : SharedTables p b0 μDir := tb.congr fun x h1 h2 => by
    rw [above x h1, fEncB x (Or.inl (by omega)), fEncA x (Or.inl h2)]
  refine ⟨{ tbDir with
    dir := sdir
    encA := fun β hβ => (sA β hβ).congr fun i hi => ?_
    encB := fun β hβ => (sB β hβ).congr fun i hi => above _ (by omega) }, fun x hx => ?_⟩
  · rw [Spec.length_arrT] at hi
    have := Nat.mul_add_lt_mul hβ (show i < p.T from hi)
    rw [above _ (by omega), fEncB _ (Or.inl (by omega))]
  · show μDir x = μ x
    rw [fDir x (by omega), fEncB x (by omega), fEncA x (by omega)]

theorem sharedCPB_spec (std : Std lim) {c : ℕ} (C : SharedCalleesB lim P c) {d : ℕ} {p : Par}
    (hmL : p.m ≤ p.L) {aX aY b0 : ℕ} (hd : d + (p.L + 3) ≤ lim.depth)
    (hsp : p.sharedEnd b0 ≤ lim.space) (h10 : ((10 ^ (p.L + 1) : ℕ) : ℤ) ≤ lim.word)
    (μ : ℕ → ℤ) (r0 : ℤ) {X : Matrix (Fin (p.K0 * p.N)) (Fin (ThreeSumApsp.D p.m)) ℤ}
    {Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin (p.K0 * p.N)) ℤ} {V : ℤ} (hX : MatAt μ aX X)
    (hY : MatAt μ aY Y.transpose) (hXle : aX + p.K0 * p.N * p.D ≤ b0)
    (hYle : aY + p.K0 * p.N * p.D ≤ b0) (hV0 : 0 ≤ V)
    (hVX : ∀ i j, |X i j| ≤ V) (hVY : ∀ i j, |Y i j| ≤ V) (hVB : 7 ^ (p.L + 1) * V ≤ lim.word)
    (hpad : padN p.L p.m p.N = p.N) (tb : SharedTables p b0 μ) :
    Ends lim P d sharedCP ⟨frame (sharedLocB p aX aY b0 r0), μ⟩ (sharedTimeCP c p) fun σ' =>
      SharedReadyA p aX aY b0 (batchL p hmL X) (batchR p hmL Y) σ'.mem ∧
        SameOutside μ σ'.mem b0 (p.sharedEnd b0 - b0) := by
  have hw := std.space_le
  have h100 := std.const_le
  have hplaces := p.places b0
  have hsizes := p.sizes hmL
  have hTw := Par.ten_T_le h10
  unfold sharedCP sharedTimeCP
  refine Ends.next 13 ((sharedBands_spec std hmL hsp μ r0 tb).mono le_rfl ?_)
  rintro _ rfl
  unfold sharedLocB
  light_set (p.aENCB b0 : ℕ)
  light_set (p.aARR b0 : ℕ)
  light_set (p.aZS b0 : ℕ)
  light_set (p.sharedEnd b0 : ℕ)
  have preA : BandsPre lim p μ (p.bandsArgs b0 (p.aPHI b0) (p.aENCA b0)) Spec.phiFlat V :=
    tb.bandsPre hsp hV0 hVB tb.phi (coef_le := by omega) (le_enc := le_rfl) (enc_le := by omega)
  light_call (C.bandsL p hmL _ aX μ X V preA hX
    (hXle.trans (show b0 ≤ p.aENCA b0 by omega)) hVX hpad) with rEncA μEncA ⟨sA, fEncA⟩
  have lowEncA : ∀ x < p.aENCA b0, μEncA x = μ x := fun x hx => fEncA x (Or.inl hx)
  have tbEncA : SharedTables p b0 μEncA := tb.congr fun x _ hx => lowEncA x hx
  have hYle' : aY + p.K0 * p.N * ThreeSumApsp.D p.m ≤ p.aENCA b0 := le_trans hYle (by omega)
  have preB : BandsPre lim p μEncA (p.bandsArgs b0 (p.aPSI b0) (p.aENCB b0)) Spec.psiFlat V :=
    tbEncA.bandsPre hsp hV0 hVB tbEncA.psi (coef_le := by omega) (le_enc := by omega)
      (enc_le := by omega)
  light_call (C.bandsR p hmL _ aY μEncA Y V preB (hY.congr_below lowEncA hYle')
    (hYle.trans (show b0 ≤ p.aENCB b0 by omega)) hVY hpad) with rEncB μEncB ⟨sB, fEncB⟩
  refine (storeLocals_spec hw (base := b0) _ (by simp) _ 0 μEncB (by simp; omega)).mono
    (by simp; omega) ?_
  rintro ⟨_, μDir⟩ ⟨sdir, fDir⟩
  exact SharedReadyA.of_calls tb sA fEncA sB fEncB (by simpa [SegN, dirList] using sdir)
    (by simpa using fDir)

/-- **sharedP**, with the batched band arrays. -/
theorem sharedPB_entry (std : Std lim) (hP : P[pSharedP]? = some sharedPBody) {c : ℕ}
    (C : SharedCalleesB lim P c) {c' : ℕ} (hc : 12 * c + 600 ≤ c') : SharedSpecB lim P c' := by
  intro p hmL aX aY b0 μ X Y V pre d hd
  have hplaces := p.places b0
  refine .mono_const (.of_body hP (Ends.mono ?_ (sharedTimeP_le c p) fun _ h => h)) hc
  rw [← frame_append_zeros [(p.L : ℤ), p.m, p.N, p.D, aX, aY, b0] 26]
  unfold sharedPBody
  light_piece (sharedAPB_spec std C hmL hd pre.space pre.ten μ) with ⟨locA, μA⟩ ⟨⟨rA, hlocA⟩, hA⟩
  obtain rfl : locA = _ := hlocA
  dsimp only at hA
  light_piece (sharedBPB_spec std C hmL hd pre.space pre.ten μA rA) with ⟨locB, μB⟩
    ⟨⟨rB, hlocB⟩, hB⟩
  obtain rfl : locB = _ := hlocB
  dsimp only at hB
  have low : ∀ x < b0, μB x = μ x := fun x hx => by
    rw [hB.same x (Or.inl (by omega)), hA.same x (Or.inl (by omega))]
  refine (sharedCPB_spec std C hmL hd pre.space pre.ten μB rB (pre.matX.congr_below low pre.belowX)
    (pre.matY.congr_below low pre.belowY) pre.belowX pre.belowY
    pre.V_nonneg pre.absX pre.absY pre.seven pre.pad (.of_parts hA hB)).mono (by omega) ?_
  rintro σ' ⟨hR, hf⟩
  exact ⟨hR, fun x hx => by rw [hf x hx, hB.same x (by omega), hA.same x (by omega)]⟩

end Light.Batch
