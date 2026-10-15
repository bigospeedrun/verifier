/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Programs.Sec2.PrunedEnc.AllBands
public import Submission.ThreeSumApsp.Programs.Sec2.Theorem5.SharedStage

/-!
# The shared stage with pruned encodings

sharedP(L, m, N, D, aX, aY, b0) is shared, except that both calls of encodeBands go to encodeBandsP:
the encodings of the bands are computed only at the leaves with at most m nines.  The first two
parts (sharedA, sharedB) and the directory are those of shared; their lemmas are restated here for
the callees of sharedP (`SharedCalleesP`), and the third part (sharedCP) is proved as sharedC is.
sharedP_entry: if every callee meets its entry with the constant c, then sharedP meets `SharedSpecP`
with the constant 12 c + 600.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

variable {lim : Limits} {P : Program}

open Shared

/-- The entries of the routines that the shared stage with pruned encodings calls. -/
structure SharedCalleesP (lim : Limits) (P : Program) (c : ℕ) : Prop where
  pow : PowSpec lim P c
  binom : BinomSpec lim P c
  sqrt : SqrtSpec lim P c
  coef : CoefSpec lim P c
  subsets : SubsetsSpec lim P c
  counters : CountersSpec lim P c
  digits : DigitsSpec lim P c
  bandsL : EncodeBandsPLSpec lim P c
  bandsR : EncodeBandsPRSpec lim P c

/-- The entry of pow, for a table of the powers b^0, …, b^L of a base b ≤ 10. -/
theorem SharedCalleesP.powTable {c : ℕ} (C : SharedCalleesP lim P c) {p : Par}
    (h10 : ((10 ^ (p.L + 1) : ℕ) : ℤ) ≤ lim.word) (b dst : ℕ) (μ : ℕ → ℤ)
    (one_le : 1 ≤ b := by omega) (le_ten : b ≤ 10 := by omega) (dst_pos : 1 ≤ dst := by omega)
    (dst_le : dst + (p.L + 1) ≤ lim.space := by omega) :
    ∀ d, d ≤ lim.depth → Meets lim P pPow d [b, p.L, dst] μ (c * (p.L + 1)) fun _ μ' =>
      Seg μ' dst (powList b (p.L + 1)) ∧ SameOutside μ μ' dst (p.L + 1) :=
  C.pow b p.L dst μ dst_pos dst_le one_le
    (le_trans (by exact_mod_cast Nat.pow_le_pow_left le_ten _) h10)

/-- **The first part of shared.** -/
theorem sharedAP_spec (std : Std lim) {c : ℕ} (C : SharedCalleesP lim P c) {d : ℕ} {p : Par}
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
theorem sharedBP_spec (std : Std lim) {c : ℕ} (C : SharedCalleesP lim P c) {d : ℕ} {p : Par}
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


/-- The third part of sharedP: as sharedC, with the pruned encodings of all bands. -/
def sharedCP : Stmt :=
  sharedBands ;;
  .set AdrEncB (v AdrEncA +' v Bands *' v Leaves) ;;
  .set AdrArr (v AdrEncB +' v Bands *' v Leaves) ;;
  .set AdrZs (v AdrArr +' v Strings) ;;
  .set AdrEnd (v AdrZs +' v Strings) ;;
  .call pEncodeBandsP [v Levels, v Inner, v Rows, v Cols, v Root, v BlockRows, v Strings, v Leaves,
    v Bands, k 0, v AdrX, v Cols, k 1, v AdrMask, v AdrDig3, v AdrDig4, v AdrArr, v AdrZs, v AdrPhi,
    v AdrP7, v AdrP10, v AdrEncA] Void ;;
  .call pEncodeBandsP [v Levels, v Inner, v Rows, v Cols, v Root, v BlockRows, v Strings, v Leaves,
    v Bands, k 1, v AdrY, k 1, v Rows, v AdrMask, v AdrDig3, v AdrDig4, v AdrArr, v AdrZs, v AdrPsi,
    v AdrP7, v AdrP10, v AdrEncB] Void ;;
  storeLocals 0 [Levels, Inner, Rows, Cols, Outer, BlockRows, Subsets, Root, Table, Bands, Leaves,
    Strings, AdrX, AdrY, AdrP3, AdrP4, AdrP7, AdrP10, AdrPas, AdrPhi, AdrPsi, AdrMask, AdrBand,
    AdrBlock, AdrDig3, AdrDig4, AdrEncA, AdrEncB, AdrArr, AdrZs, AdrEnd]

/-- sharedP(L, m, N, D, aX, aY, b0). -/
def sharedPBody : Stmt := sharedA ;; sharedB ;; sharedCP

/-- The time of the third part of sharedP. -/
def sharedTimeCP (c : ℕ) (p : Par) : ℕ :=
  2 * (c * (p.nB * (retW p.L p.m + bandArrayShape p) + 1)) + 236

/-- What the two calls of encodeBandsP and the stores of the directory leave in the memory. -/
theorem SharedReadyP.of_calls {p : Par} (hmL : p.m ≤ p.L) {aX aY b0 : ℕ}
    {X : Matrix (Fin p.N) (Fin (ThreeSumApsp.D p.m)) ℤ}
    {Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin p.N) ℤ} {μ μEncA μEncB μDir : ℕ → ℤ}
    (tb : SharedTables p b0 μ)
    (sA : ∀ β < p.nB, RetSeg p.L p.m μEncA (p.aENCA b0 + β * p.T)
      (Spec.arrT (encodingL (bandArrayL (Spec.stdLayout hmL) X β))))
    (fEncA : SameOutside μ μEncA (p.aENCA b0) (p.sharedEnd b0 - p.aENCA b0))
    (sB : ∀ β < p.nB, RetSeg p.L p.m μEncB (p.aENCB b0 + β * p.T)
      (Spec.arrT (encodingR (bandArrayR (Spec.stdLayout hmL) Y β))))
    (fEncB : SameOutside μEncA μEncB (p.aENCB b0) (p.sharedEnd b0 - p.aENCB b0))
    (sdir : SegN μDir b0 (dirList p aX aY b0)) (fDir : SameOutside μEncB μDir b0 31) :
    SharedReadyP p hmL aX aY b0 X Y μDir ∧ SameOutside μ μDir b0 (p.sharedEnd b0 - b0) := by
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

/-- **The third part of sharedP.** -/
theorem sharedCP_spec (std : Std lim) {c : ℕ} (C : SharedCalleesP lim P c) {d : ℕ} {p : Par}
    (hmL : p.m ≤ p.L) {aX aY b0 : ℕ} (hd : d + (p.L + 3) ≤ lim.depth)
    (hsp : p.sharedEnd b0 ≤ lim.space) (h10 : ((10 ^ (p.L + 1) : ℕ) : ℤ) ≤ lim.word)
    (μ : ℕ → ℤ) (r0 : ℤ) {X : Matrix (Fin p.N) (Fin (ThreeSumApsp.D p.m)) ℤ}
    {Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin p.N) ℤ} {V : ℤ} (hX : MatAt μ aX X)
    (hY : MatAt μ aY Y) (hXle : aX + p.N * p.D ≤ b0) (hYle : aY + p.D * p.N ≤ b0) (hV0 : 0 ≤ V)
    (hVX : ∀ i j, |X i j| ≤ V) (hVY : ∀ i j, |Y i j| ≤ V) (hVB : 7 ^ (p.L + 1) * V ≤ lim.word)
    (tb : SharedTables p b0 μ) :
    Ends lim P d sharedCP ⟨frame (sharedLocB p aX aY b0 r0), μ⟩ (sharedTimeCP c p) fun σ' =>
      SharedReadyP p hmL aX aY b0 X Y σ'.mem ∧ SameOutside μ σ'.mem b0 (p.sharedEnd b0 - b0) := by
  have hw := std.space_le
  have h100 := std.const_le
  have hplaces := p.places b0
  have hsizes := p.sizes hmL
  have hTw := Par.ten_T_le h10
  unfold sharedCP sharedTimeCP
  -- the number of bands
  refine Ends.next 13 ((sharedBands_spec std hmL hsp μ r0 tb).mono le_rfl ?_)
  rintro _ rfl
  unfold sharedLocB
  -- the last four addresses
  light_set (p.aENCB b0 : ℕ)
  light_set (p.aARR b0 : ℕ)
  light_set (p.aZS b0 : ℕ)
  light_set (p.sharedEnd b0 : ℕ)
  -- the pruned encodings of the row bands of X
  have preA : BandsPre lim p μ (p.bandsArgs b0 (p.aPHI b0) (p.aENCA b0)) Spec.phiFlat V :=
    tb.bandsPre hsp hV0 hVB tb.phi (coef_le := by omega) (le_enc := le_rfl) (enc_le := by omega)
  light_call (C.bandsL p hmL _ aX μ X V preA hX
    (hXle.trans (show b0 ≤ p.aENCA b0 by omega)) hVX) with rEncA μEncA ⟨sA, fEncA⟩
  -- the pruned encodings of the column bands of Y
  have lowEncA : ∀ x < p.aENCA b0, μEncA x = μ x := fun x hx => fEncA x (Or.inl hx)
  have tbEncA : SharedTables p b0 μEncA := tb.congr fun x _ hx => lowEncA x hx
  have hYle' : aY + ThreeSumApsp.D p.m * p.N ≤ p.aENCA b0 := le_trans hYle (by omega)
  have preB : BandsPre lim p μEncA (p.bandsArgs b0 (p.aPSI b0) (p.aENCB b0)) Spec.psiFlat V :=
    tbEncA.bandsPre hsp hV0 hVB tbEncA.psi (coef_le := by omega) (le_enc := by omega)
      (enc_le := by omega)
  light_call (C.bandsR p hmL _ aY μEncA Y V preB (hY.congr_below lowEncA hYle')
    (hYle.trans (show b0 ≤ p.aENCB b0 by omega)) hVY) with rEncB μEncB ⟨sB, fEncB⟩
  -- the directory
  refine (storeLocals_spec hw (base := b0) _ (by simp) _ 0 μEncB (by simp; omega)).mono
    (by simp; omega) ?_
  rintro ⟨_, μDir⟩ ⟨sdir, fDir⟩
  exact SharedReadyP.of_calls hmL tb sA fEncA sB fEncB (by simpa [SegN, dirList] using sdir)
    (by simpa using fDir)

/-- The time of the shared stage with pruned encodings has the shape of its entry. -/
theorem sharedTimeP_le (c : ℕ) (p : Par) :
    sharedTimeA c p + (sharedTimeB c p + sharedTimeCP c p) ≤ (12 * c + 600) * sharedShapeP p := by
  unfold sharedTimeA sharedTimeB sharedTimeCP sharedShapeP
  have hL : p.L + 1 ≤ (p.L + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have hN : p.N + 1 ≤ (p.N + 1) * (p.Lo + 1) := Nat.le_mul_of_pos_right _ (by omega)
  generalize (p.L + 1) ^ 2 = s, Nat.sqrt p.K + 1 = q, (p.KK + 1) * (p.L + 1) = u,
    (p.N + 1) * (p.Lo + 1) = w, (p.D + 1) * (p.m + 1) = x,
    p.nB * (retW p.L p.m + bandArrayShape p) = y at hL hN ⊢
  have hcL := Nat.mul_le_mul_left c hL
  have hcN := Nat.mul_le_mul_left c hN
  have hc1 := Nat.mul_le_mul_left c (show 1 ≤ s by omega)
  have hy : c * (y + 1) = c * y + c := Nat.mul_succ c y
  have hright : (12 * c + 600) * (s + q + u + w + x + y) = 12 * (c * s) + 12 * (c * q)
      + 12 * (c * u) + 12 * (c * w) + 12 * (c * x) + 12 * (c * y)
      + 600 * (s + q + u + w + x + y) := by ring
  omega

/-- **sharedP** meets its entry: if every callee meets its entry with the constant c, then sharedP
does with the constant 12 c + 600. -/
theorem sharedP_entry (std : Std lim) (hP : P[pSharedP]? = some sharedPBody) {c : ℕ}
    (C : SharedCalleesP lim P c) {c' : ℕ} (hc : 12 * c + 600 ≤ c') : SharedSpecP lim P c' := by
  intro p hmL aX aY b0 μ X Y V pre d hd
  have hplaces := p.places b0
  refine .mono_const (.of_body hP (Ends.mono ?_ (sharedTimeP_le c p) fun _ h => h)) hc
  rw [← frame_append_zeros [(p.L : ℤ), p.m, p.N, p.D, aX, aY, b0] 26]
  unfold sharedPBody
  -- the first part
  light_piece (sharedAP_spec std C hmL hd pre.space pre.ten μ) with ⟨locA, μA⟩ ⟨⟨rA, hlocA⟩, hA⟩
  obtain rfl : locA = _ := hlocA
  dsimp only at hA
  -- the second part
  light_piece (sharedBP_spec std C hmL hd pre.space pre.ten μA rA) with ⟨locB, μB⟩
    ⟨⟨rB, hlocB⟩, hB⟩
  obtain rfl : locB = _ := hlocB
  dsimp only at hB
  -- the third part
  have low : ∀ x < b0, μB x = μ x := fun x hx => by
    rw [hB.same x (Or.inl (by omega)), hA.same x (Or.inl (by omega))]
  have hVB' : 7 ^ (p.L + 1) * max V 0 ≤ lim.word := by
    rcases le_total V 0 with h | h
    · rw [max_eq_right h, mul_zero]
      exact le_trans (by norm_num) std.const_le
    · rw [max_eq_left h]
      exact pre.seven
  refine (sharedCP_spec std C hmL hd pre.space pre.ten μB rB (pre.matX.congr_below low pre.belowX)
    (pre.matY.congr_below low pre.belowY) pre.belowX pre.belowY (le_max_right V 0)
    (fun i j => (pre.absX i j).trans (le_max_left _ _))
    (fun i j => (pre.absY i j).trans (le_max_left _ _)) hVB' (.of_parts hA hB)).mono (by omega) ?_
  rintro σ' ⟨hR, hf⟩
  exact ⟨hR, fun x hx => by rw [hf x hx, hB.same x (by omega), hA.same x (by omega)]⟩

end Light.Sec2
