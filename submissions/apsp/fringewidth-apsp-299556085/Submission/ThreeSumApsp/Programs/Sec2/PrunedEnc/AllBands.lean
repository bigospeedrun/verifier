/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Programs.Sec2.PrunedEnc.Contracts
public import Submission.ThreeSumApsp.Programs.Sec2.Theorem5.Encode.AllBands

/-!
# The pruned encodings of all bands of one matrix

encodeBandsP is encodeBands with the pruned encoder: for each band β it calls bandArray, and then
encodeP with the budget m of nines, which leaves the encoding of the band at the leaves with at most
m nines in the T = 10^L cells from enc + β T.  The arguments are those of encodeBands.

* `encodeBandsPBody`, `encodeBandsP_proc`: the loop, for callees described by what they do here.
* `EncodeBandsPLSpec`, `EncodeBandsPRSpec`: the two entries, met by `encodeBandsPL_entry` and
  `encodeBandsPR_entry`.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

variable {lim : Limits} {P : Program}

/-! ## Pruned segments -/

/-- A pruned segment only depends on its own cells. -/
theorem RetSeg.congr {L r : ℕ} {μ μ' : ℕ → ℤ} {a : ℕ} {l : List ℤ} (h : RetSeg L r μ a l)
    (he : ∀ i < l.length, μ' (a + i) = μ (a + i)) : RetSeg L r μ' a l :=
  fun i hi h9 => by rw [he i hi, h i hi h9]

/-- A pruned segment stays where it is if its cells do not change. -/
theorem RetSeg.keep {L r : ℕ} {μ μ' : ℕ → ℤ} {a : ℕ} {l : List ℤ} (h : RetSeg L r μ a l)
    (hs : SameOn (Inside a l.length) μ μ' := by light_keep) : RetSeg L r μ' a l :=
  h.congr fun i hi => hs _ ⟨by omega, by omega⟩

open Bands in
/-- encodeBandsP(L, m, N, D, K0, N0, S7, T, nB, side, aA, sI, sK, mask, dig3, dig4, arr, zs, tab,
p7, p10, enc): for each band, the input array is formed at arr and its encoding is written into the
T cells from enc + β T, at the leaves with at most m nines. -/
def encodeBandsPBody : Stmt :=
  .for BandNo (v NumBands) (
    .call pBandArray [v Levels, v Size, v Rows, v Cols, v NumBlocks, v Width, v Cells, v BandNo,
      v Side, v Source, v StepRow, v StepCol, v MaskTable, v Digits3, v Digits4, v Arr] Res ;;
    .call pEncodeP [v Levels, v Arr, v Enc +' v BandNo *' v Leaves, v Scratch, v Table, v Pow7,
      v Pow10, v Size] Res)

/-- The time of the loop is at most the constant cB + cE + 50 times the shape of the entries. -/
theorem encodeBandsP_time (p : Par) (cB cE : ℕ) :
    p.nB * (cB * bandArrayShape p + cE * retW p.L p.m + 50) + 6
      ≤ (cB + cE + 50) * (p.nB * (retW p.L p.m + bandArrayShape p) + 1) := by
  have hT : 1 ≤ retW p.L p.m :=
    le_trans (Nat.one_le_pow _ _ (by norm_num)) (nine_pow_le_retW p.L p.m)
  generalize retW p.L p.m = w at hT ⊢
  have hfifty : p.nB * 50 ≤ p.nB * (50 * w) := Nat.mul_le_mul_left _ (by omega)
  calc p.nB * (cB * bandArrayShape p + cE * w + 50) + 6
      = p.nB * (cB * bandArrayShape p) + p.nB * (cE * w) + p.nB * 50 + 6 := by ring
    _ ≤ p.nB * (cB * bandArrayShape p) + p.nB * (cE * w) + p.nB * (50 * w) + 6
        + (p.nB * (cB * w) + p.nB * ((cE + 50) * bandArrayShape p) + (cB + cE + 44)) := by omega
    _ = (cB + cE + 50) * (p.nB * (w + bandArrayShape p) + 1) := by ring

variable {p : Par} {x : BandsArgs} {coefs : List ℤ} {V : ℤ} {μ μ' : ℕ → ℤ}

/-- **encodeBandsP**, at the sizes of `p`, for callees described by what they do here: `HB` says
that `bandArray` leaves the list `A β` at `arr`, `HE` that `encodeP` turns it into the list `E β`
at `enc + β T`, at the leaves with at most m nines. -/
theorem encodeBandsP_proc (std : Std lim) (hP : P[pEncodeBandsP]? = some encodeBandsPBody)
    {d side aA sI sK cB cE : ℕ} {A E : ℕ → List ℤ} (pre : BandsPre lim p μ x coefs V)
    (hd : d < lim.depth) (hE : ∀ β, (E β).length = p.T)
    (HB : ∀ β < p.nB, ∀ μ' : ℕ → ℤ, Kept μ μ' x.enc →
      Meets lim P pBandArray (d + 1)
        [p.L, p.m, p.N, p.D, p.K0, p.N0, p.S7, β, side, aA, sI, sK, x.mask, x.dig3, x.dig4, x.arr]
        μ' (cB * bandArrayShape p) fun _ μ'' =>
          Seg μ'' x.arr (A β) ∧ SameOutside μ' μ'' x.arr p.S7)
    (HE : ∀ β < p.nB, ∀ μ' : ℕ → ℤ, Kept μ μ' x.enc → Seg μ' x.arr (A β) →
      Meets lim P pEncodeP (d + 1)
        [p.L, x.arr, (x.enc + β * p.T : ℕ), x.zs, x.tab, x.p7, x.p10, p.m] μ'
        (cE * retW p.L p.m) fun _ μ'' => RetSeg p.L p.m μ'' (x.enc + β * p.T) (E β) ∧
          SameOutside2 μ' μ'' (x.enc + β * p.T) (10 ^ p.L) x.zs (7 ^ p.L)) :
    Meets lim P pEncodeBandsP d (x.vals p side aA sI sK) μ
      ((cB + cE + 50) * (p.nB * (retW p.L p.m + bandArrayShape p) + 1)) fun _ μ' =>
        (∀ β < p.nB, RetSeg p.L p.m μ' (x.enc + β * p.T) (E β)) ∧
          SameOutside μ μ' x.enc (x.zs + p.S7 - x.enc) := by
  refine .of_body hP (Ends.mono
    (T := p.nB * (cB * bandArrayShape p + cE * retW p.L p.m + 50) + 6) ?_
    (encodeBandsP_time p cB cE) fun _ h => h)
  light_facts pre std
  have hT : p.T = 10 ^ p.L := rfl
  have hS7 : p.S7 = 7 ^ p.L := rfl
  have hnB : p.nB ≤ p.nB * p.T := Nat.le_mul_of_pos_right _ p.one_le_T
  refine Ends.forShape
    (fun β r μ' => ⟨frame [p.L, p.m, p.N, p.D, p.K0, p.N0, p.S7, p.T, p.nB, side, aA, sI, sK,
      x.mask, x.dig3, x.dig4, x.arr, x.zs, x.tab, x.p7, x.p10, x.enc, β, r], μ'⟩)
    (fun β μ' => (∀ β' < β, RetSeg p.L p.m μ' (x.enc + β' * p.T) (E β')) ∧
      SameOutside μ μ' x.enc (x.zs + p.S7 - x.enc))
    p.nB (cB * bandArrayShape p + cE * retW p.L p.m + 42) 0
    ⟨fun β' h => absurd h (by omega), .refl⟩
    ?round (fun _ _ h => h) (by rw [update_frame_setLocal, ← frame_append_zeros _ 1]; rfl)
  rintro β r μ' hβ ⟨hdone, same⟩
  have hβT : β * p.T + p.T ≤ p.nB * p.T := Nat.mul_add_le_mul hβ le_rfl
  light_call (HB β hβ μ' (by light_keep)) with r₁ μ₁ ⟨hA, same₁⟩
  light_call (HE β hβ μ₁ (by light_keep) hA) with r₂ μ₂ ⟨hEβ, same₂⟩
  refine ⟨r₂, μ₂, rfl, fun β' hβ' => ?_, by light_keep⟩
  rcases Nat.lt_or_ge β' β with h | h
  · have hβ'T : β' * p.T + p.T ≤ β * p.T := Nat.mul_add_le_mul h le_rfl
    have hlen := hE β'
    exact (hdone β' h).keep
  · obtain rfl : β' = β := by omega
    exact hEβ

/-! ## The two entries -/

/-- encodeBandsP for the row bands of X: side = 0, the coefficients φ at tab. -/
def EncodeBandsPLSpec (lim : Limits) (P : Program) (c : ℕ) : Prop :=
  ∀ (p : Par) (hmL : p.m ≤ p.L) (x : BandsArgs) (aX : ℕ) (μ : ℕ → ℤ)
    (X : Matrix (Fin p.N) (Fin (ThreeSumApsp.D p.m)) ℤ) (V : ℤ),
    BandsPre lim p μ x Spec.phiFlat V → MatAt μ aX X → aX + p.N * p.D ≤ x.enc →
    (∀ i j, |X i j| ≤ V) →
    ∀ d, d + (p.L + 2) ≤ lim.depth → Meets lim P pEncodeBandsP d (x.vals p 0 aX p.D 1) μ
      (c * (p.nB * (retW p.L p.m + bandArrayShape p) + 1)) fun _ μ' =>
        (∀ β < p.nB, RetSeg p.L p.m μ' (x.enc + β * p.T)
          (Spec.arrT (encodingL (bandArrayL (Spec.stdLayout hmL) X β)))) ∧
          SameOutside μ μ' x.enc (x.zs + p.S7 - x.enc)

/-- **encodeBandsP** meets this entry, with every constant from cB + cE + 50 on. -/
theorem encodeBandsPL_entry (std : Std lim) (hP : P[pEncodeBandsP]? = some encodeBandsPBody)
    {cB cE c : ℕ} (hB : BandArrayLSpec lim P cB) (hE : EncodePLSpec lim P cE)
    (hc : cB + cE + 50 ≤ c) : EncodeBandsPLSpec lim P c := by
  intro p hmL x aX μ X V pre hM hMle hV d hd
  light_facts pre
  refine .mono_const ?_ hc
  refine encodeBandsP_proc std hP pre (by omega) (fun β => Spec.length_arrT _)
    (A := fun β => Spec.arrL (bandArrayL (Spec.stdLayout hmL) X β))
    (fun β hβ μ' hlow => ?_) fun β hβ μ' hlow hA => ?_
  · simpa using hB p hmL β aX x.mask x.dig3 x.dig4 x.arr μ' X (by omega)
      (hM.congr_below hlow hMle) (by omega) ((pre.tables.congr_below hlow).mono (by omega)) hβ
      _ (by omega)
  · exact hE p.L p.L x.arr (x.enc + β * p.T) x.zs x.tab x.p7 x.p10 p.m μ' _ V
      (pre.encodePlaces hβ hlow)
      (pre.coef.congr fun i hi => hlow _ (by
        have := Spec.length_phiFlat
        omega))
      hA (abs_bandArrayL_le (Spec.stdLayout hmL) pre.V_nonneg hV β) pre.word _ (by omega)

/-- encodeBandsP for the column bands of Y: side = 1, the coefficients ψ at tab. -/
def EncodeBandsPRSpec (lim : Limits) (P : Program) (c : ℕ) : Prop :=
  ∀ (p : Par) (hmL : p.m ≤ p.L) (x : BandsArgs) (aY : ℕ) (μ : ℕ → ℤ)
    (Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin p.N) ℤ) (V : ℤ),
    BandsPre lim p μ x Spec.psiFlat V → MatAt μ aY Y → aY + p.D * p.N ≤ x.enc →
    (∀ i j, |Y i j| ≤ V) →
    ∀ d, d + (p.L + 2) ≤ lim.depth → Meets lim P pEncodeBandsP d (x.vals p 1 aY 1 p.N) μ
      (c * (p.nB * (retW p.L p.m + bandArrayShape p) + 1)) fun _ μ' =>
        (∀ β < p.nB, RetSeg p.L p.m μ' (x.enc + β * p.T)
          (Spec.arrT (encodingR (bandArrayR (Spec.stdLayout hmL) Y β)))) ∧
          SameOutside μ μ' x.enc (x.zs + p.S7 - x.enc)

/-- **encodeBandsP** meets this entry, with every constant from cB + cE + 50 on. -/
theorem encodeBandsPR_entry (std : Std lim) (hP : P[pEncodeBandsP]? = some encodeBandsPBody)
    {cB cE c : ℕ} (hB : BandArrayRSpec lim P cB) (hE : EncodePRSpec lim P cE)
    (hc : cB + cE + 50 ≤ c) : EncodeBandsPRSpec lim P c := by
  intro p hmL x aY μ Y V pre hM hMle hV d hd
  light_facts pre
  refine .mono_const ?_ hc
  refine encodeBandsP_proc std hP pre (by omega) (fun β => Spec.length_arrT _)
    (A := fun β => Spec.arrR (bandArrayR (Spec.stdLayout hmL) Y β))
    (fun β hβ μ' hlow => ?_) fun β hβ μ' hlow hA => ?_
  · simpa using hB p hmL β aY x.mask x.dig3 x.dig4 x.arr μ' Y (by omega)
      (hM.congr_below hlow hMle) (by omega) ((pre.tables.congr_below hlow).mono (by omega)) hβ
      _ (by omega)
  · exact hE p.L p.L x.arr (x.enc + β * p.T) x.zs x.tab x.p7 x.p10 p.m μ' _ V
      (pre.encodePlaces hβ hlow)
      (pre.coef.congr fun i hi => hlow _ (by
        have := Spec.length_psiFlat
        omega))
      hA (abs_bandArrayR_le (Spec.stdLayout hmL) pre.V_nonneg hV β) pre.word _ (by omega)

end Light.Sec2
