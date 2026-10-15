/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Batch.SharedB
public import Submission.ThreeSumApsp.Batch.PreCoreA
public import Submission.ThreeSumApsp.Batch.QueryA
public import Submission.ThreeSumApsp.Programs.Sec4.Theorem30.Program

/-!
# The batched data structure on the word RAM

`base58B` is `base58` with the body `bandArrayBBody` at the number of bandArray. Every program that
begins with it meets the specifications of the preprocessing and of a query for the batched arrays:

* `preCoreB_base58B`: preCore(L, m, t, N, D, aX, aY, b0), for the source X (`K₀ N × D`) at aX and
  the transpose of the source Y at aY, builds the data structure `DSReadyA` of the arrays
  `bArrayL (stdLayout hmL) X β`, `bArrayR (stdLayout hmL) Y β`;
* `queryAtA_base58B`: queryAt(I, J, b0) returns the value of the query of (I, J) from it.
-/

@[expose] public section

namespace Light.Batch

open ThreeSumApsp ThreeSumApsp.Spec Light.Sec4

/-- The procedures number 0 to 57, with the batched band array. -/
def base58B : Program := base58.set Sec2.pBandArray bandArrayBBody

theorem length_base58B : base58B.length = 58 := by simp [base58B, length_base58]

theorem base58B_append (R : Program) :
    base58B ++ R = (base58 ++ R).set Sec2.pBandArray bandArrayBBody := by
  rw [base58B, List.set_append_left _ _ (by rw [length_base58]; decide)]

theorem at_base58B {i : ℕ} {body : Stmt} (h : base58[i]? = some body) (hi : i ≠ Sec2.pBandArray)
    (R : Program) : (base58B ++ R)[i]? = some body := by
  rw [base58B_append, List.getElem?_set_ne (Ne.symm hi)]
  exact at_base58 h R

theorem band_base58B (R : Program) : (base58B ++ R)[Sec2.pBandArray]? = some bandArrayBBody := by
  rw [base58B_append, List.getElem?_set_self]
  simp [length_base58, Sec2.pBandArray]; omega

theorem has40_base58B (R : Program) : Has40 (base58B ++ R) := by
  intro i hi
  rw [base58B_append, List.getElem?_set_ne (by simp [Sec2.pBandArray]; omega)]
  exact has40_base58 R i hi

/-- The shared stage with the batched band arrays, in every program that begins with base58B. -/
theorem sharedB_base58B (R : Program) (lim : Limits) (std : Std lim) :
    SharedSpecB lim (base58B ++ R) cShared30 := by
  have hP : ∀ {i : ℕ} {body : Stmt}, base58[i]? = some body → i ≠ Sec2.pBandArray →
      (base58B ++ R)[i]? = some body := fun h hi => at_base58B h hi R
  have C : SharedCalleesB lim (base58B ++ R) Sec2.cShared5 :=
    { pow := Sec2.pow_entry std (hP rfl (by decide)) (by decide)
      binom := Sec2.binom_entry std (hP rfl (by decide)) (by decide)
      sqrt := Sec2.sqrt_entry (hP rfl (by decide)) (by decide)
      coef := Sec2.coef_entry std (hP rfl (by decide)) (by decide)
      subsets := Sec2.subsets_entry std (hP rfl (by decide)) (by decide)
      counters := Sec2.counters_entry std (hP rfl (by decide)) (by decide)
      digits := Sec2.digits_entry std (hP rfl (by decide)) (by decide)
      bandsL := encodeBandsPLB_entry std (hP rfl (by decide)) (bandArrayBL_entry std (band_base58B R))
        (Sec2.encodePL_entry std (hP rfl (by decide)) (hP rfl (by decide))) (by decide)
      bandsR := encodeBandsPRB_entry std (hP rfl (by decide)) (bandArrayBR_entry std (band_base58B R))
        (Sec2.encodePR_entry std (hP rfl (by decide)) (hP rfl (by decide))) (by decide) }
  exact sharedPB_entry std (hP rfl (by decide)) C le_rfl

/-! ## The preprocessing -/

/-- preCore(L, m, t, N, D, aX, aY, b0) for the two sources: X (`K₀ N × D`, row by row at aX) and Y
(`D × K₀ N`, its transpose row by row at aY). -/
def PreCoreBSpec (lim : Limits) (P : Program) (c : ℕ) : Prop :=
  ∀ (p : Sec2.Par) (t : ℕ) (hmL : p.m ≤ p.L) (aX aY b0 : ℕ)
    (X : Matrix (Fin (p.K0 * p.N)) (Fin (D p.m)) ℤ) (Y : Matrix (Fin (D p.m)) (Fin (p.K0 * p.N)) ℤ)
    (U : ℤ) (μ : ℕ → ℤ),
    t ≤ p.m → Lim30 lim p t b0 U → 0 ≤ U → (∀ i j, |X i j| ≤ U) → (∀ i j, |Y i j| ≤ U) →
    MatAt μ aX X → MatAt μ aY Y.transpose → aX + p.K0 * p.N * p.D ≤ b0 →
    aY + p.K0 * p.N * p.D ≤ b0 → padN p.L p.m p.N = p.N →
    ∀ d, d + (p.L + 6) ≤ lim.depth →
    Meets lim P Proc.preCore d [p.L, p.m, t, p.N, p.D, aX, aY, b0] μ
      (tPreCore c p t) fun _ μ' =>
      DSReadyA p t aX aY b0 (batchL p hmL X) (batchR p hmL Y) μ' ∧
        SameOutside μ μ' b0 (top p t b0 - b0)

/-- The batched arrays are bounded as their sources. -/
theorem boundA_batch {p : Sec2.Par} (hmL : p.m ≤ p.L)
    {X : Matrix (Fin (p.K0 * p.N)) (Fin (D p.m)) ℤ} {Y : Matrix (Fin (D p.m)) (Fin (p.K0 * p.N)) ℤ}
    {U : ℤ} (hU : 0 ≤ U) (hX : ∀ i j, |X i j| ≤ U) (hY : ∀ i j, |Y i j| ≤ U) :
    BoundA (batchL p hmL X) (batchR p hmL Y) U :=
  ⟨hU, fun β => ThreeSumApsp.Batch.abs_bArrayL_le (stdLayout hmL) hU hX β,
    fun β => ThreeSumApsp.Batch.abs_bArrayR_le (stdLayout hmL) hU hY β⟩

theorem preCoreB_spec {lim : Limits} {P : Program} {c : ℕ}
    (hP : P[Proc.preCore]? = some preCoreBody) (hShared : SharedSpecB lim P c)
    (hAll : AllTilesSpec lim P) : PreCoreBSpec lim P c := by
  intro p t hmL aX aY b0 X Y U μ ht hlim hU hX hY hMX hMY haX haY hpad
  refine fun d hd => ⟨preCoreBody, hP, ?_⟩
  light_facts hlim hlim.std
  have hend : p.sharedEnd b0 = aWD p b0 := rfl
  obtain ⟨⟩ := areas p t b0
  unfold tPreCore
  light_call (hShared p hmL aX aY b0 μ X Y U
    { space := by omega, matX := hMX, matY := hMY, belowX := haX, belowY := haY, absX := hX
      absY := hY, V_nonneg := hU, seven := hlim.enc, ten := hlim.pow, pad := hpad })
    with r μ₁ ⟨hSR₁, same₁⟩
  light_store (b0 + 31) t
  have hSR₂ : SharedReadyA p aX aY b0 (batchL p hmL X) (batchR p hmL Y)
      (Function.update μ₁ (b0 + 31) t) :=
    hSR₁.of_agree fun b _ hb => Function.update_of_ne hb ..
  light_piece (preCoreAddr_specA ht hlim hSR₂ r) with _ rfl
  refine (preCoreFinish_specA hAll hlim ht hmL (boundA_batch hmL hU hX hY) (by omega) r hSR₂
    (Function.update_self ..)).mono (by simp; omega) ?_
  rintro σ' ⟨hDS, same₂⟩
  refine ⟨hDS, fun b hb => ?_⟩
  rw [same₂ b (by omega), Function.update_of_ne (by omega), same₁ b (by omega)]

/-- **The batched preprocessing**, in every program that begins with base58B. -/
theorem preCoreB_base58B (R : Program) (lim : Limits) (std : Std lim) :
    PreCoreBSpec lim (base58B ++ R) cShared30 :=
  preCoreB_spec (at_base58B rfl (by decide) R) (sharedB_base58B R lim std)
    (specs40 (has40_base58B R) std).allTiles

/-- **A query of the data structure of any arrays**, in every program that begins with base58B. -/
theorem queryAtA_base58B (R : Program) (lim : Limits) (std : Std lim) :
    QueryAtASpec lim (base58B ++ R) :=
  queryAtA_spec (at_base58B rfl (by decide) R) (specs40 (has40_base58B R) std).outDigits
    (specs40 (has40_base58B R) std).queryCore

end Light.Batch
