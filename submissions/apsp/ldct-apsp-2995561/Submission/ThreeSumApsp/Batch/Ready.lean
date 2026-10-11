/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Programs.Sec4.Theorem30.Directory

/-!
# The invariants of Theorem 30 for arbitrary input arrays

`Sec2.SharedReadyP` and `Sec4.DSReady` name the input arrays of the bands by the matrices X and Y
(`bandArrayL (stdLayout hmL) X β`). Nothing in the routines of Section 4 depends on how the arrays
arise, so here the same invariants are stated for two families of arrays `AL β`, `AR β`, one for
each band, with the lemmas that the routines use. The batched data structure takes for them the
arrays `bArrayL`, `bArrayR` of `Batch.Tiling`.

* `SharedReadyA`: the shared block, with the pruned encodings of `AL β` and `AR β`.
* `DSReadyA`: the whole block of the data structure.
-/

@[expose] public section

namespace Light.Batch

open ThreeSumApsp ThreeSumApsp.Spec Light.Sec4

/-- The input arrays of the row bands. -/
abbrev ArrL (p : Sec2.Par) : Type := ℕ → LeftStr p.L → ℤ
/-- The input arrays of the column bands. -/
abbrev ArrR (p : Sec2.Par) : Type := ℕ → RightStr p.L → ℤ

/-- What the shared stage leaves behind, for the input arrays `AL β` and `AR β`. -/
structure SharedReadyA (p : Sec2.Par) (aX aY b0 : ℕ) (AL : ArrL p) (AR : ArrR p) (μ : ℕ → ℤ) :
    Prop extends Sec2.SharedTables p b0 μ where
  dir : SegN μ (p.aDIR b0) (Sec2.dirList p aX aY b0)
  encA : ∀ β < p.nB, Sec2.RetSeg p.L p.m μ (p.aENCA b0 + β * p.T) (arrT (encodingL (AL β)))
  encB : ∀ β < p.nB, Sec2.RetSeg p.L p.m μ (p.aENCB b0 + β * p.T) (arrT (encodingR (AR β)))

section

variable {p : Sec2.Par} {aX aY b0 : ℕ} {AL : ArrL p} {AR : ArrR p} {μ μ' : ℕ → ℤ}

theorem SharedReadyA.dir_read (h : SharedReadyA p aX aY b0 AL AR μ) {j : ℕ} (hj : j < 31) :
    μ ((b0 : ℤ) + j).toNat = ((Sec2.dirList p aX aY b0).getD j 0 : ℕ) := by
  rw [toNat_natCast_add_natCast]
  exact h.dir.read (by simpa [Sec2.dirList] using hj)

theorem SharedReadyA.dir_cell (h : SharedReadyA p aX aY b0 AL AR μ) {j : ℕ} (hj : j < 31) :
    μ (b0 + j) = (((Sec2.dirList p aX aY b0).getD j 0 : ℕ) : ℤ) :=
  h.dir.read (by simpa [Sec2.dirList] using hj)

theorem SharedReadyA.congr (h : SharedReadyA p aX aY b0 AL AR μ)
    (hag : ∀ a, b0 ≤ a → a < p.sharedEnd b0 → a ≠ b0 + 31 → μ' a = μ a) :
    SharedReadyA p aX aY b0 AL AR μ' := by
  have hplaces := p.places b0
  have tb : Sec2.SharedTables p b0 μ' :=
    h.toSharedTables.congr fun x hlo hx => hag x (by omega) (by omega) (by omega)
  have henc : ∀ {a β i : ℕ}, p.aENCA b0 ≤ a → a + p.nB * p.T ≤ p.sharedEnd b0 → β < p.nB →
      i < p.T → μ' (a + β * p.T + i) = μ (a + β * p.T + i) := fun ha hend hβ hi => by
    have := Nat.mul_add_lt_mul hβ hi
    exact hag _ (by omega) (by omega) (by omega)
  refine
    { tb with
      dir := h.dir.congr fun i hi => ?_
      encA := fun β hβ => (h.encA β hβ).congr fun i hi =>
        henc le_rfl (by omega) hβ (by rwa [length_arrT] at hi)
      encB := fun β hβ => (h.encB β hβ).congr fun i hi =>
        henc (by omega) (by omega) hβ (by rwa [length_arrT] at hi) }
  simp only [Sec2.dirList, List.length_map, List.length_cons, List.length_nil] at hi
  simp only [Sec2.Par.aDIR]
  exact hag _ (by omega) (by omega) (by omega)

theorem SharedReadyA.of_agree (h : SharedReadyA p aX aY b0 AL AR μ)
    (hag : ∀ a, a < p.sharedEnd b0 → a ≠ b0 + 31 → μ' a = μ a) :
    SharedReadyA p aX aY b0 AL AR μ' :=
  h.congr fun a _ => hag a

theorem SharedReadyA.dirCells (h : SharedReadyA p aX aY b0 AL AR μ) : DirCells p b0 μ where
  levels := h.dir_cell (j := Dir.levels) (by norm_num)
  inner := h.dir_cell (j := Dir.inner) (by norm_num)
  outer := h.dir_read (j := Dir.outer) (by norm_num)
  blocks := h.dir_read (j := Dir.blocks) (by norm_num)
  bands := h.dir_read (j := Dir.bands) (by norm_num)
  leaves := h.dir_read (j := Dir.leaves) (by norm_num)
  mask := h.dir_read (j := Dir.mask) (by norm_num)
  band := h.dir_read (j := Dir.band) (by norm_num)
  block := h.dir_read (j := Dir.block) (by norm_num)
  digits := h.dir_read (j := Dir.digits) (by norm_num)
  encA := h.dir_read (j := Dir.encA) (by norm_num)
  encB := h.dir_read (j := Dir.encB) (by norm_num)
  sharedEnd := h.dir_read (j := Dir.sharedEnd) (by norm_num)

end

/-! ## The data structure -/

/-- The encodings of the row bands. -/
def encRowA {p : Sec2.Par} (AL : ArrL p) (β : ℕ) : Leaf p.L → ℤ := encodingL (AL β)

/-- The encodings of the column bands. -/
def encColA {p : Sec2.Par} (AR : ArrR p) (β : ℕ) : Leaf p.L → ℤ := encodingR (AR β)

/-- The tries of all tiles, and their roots. -/
def dsTriesA (p : Sec2.Par) (t : ℕ) (AL : ArrL p) (AR : ArrR p) : TrieStore :=
  allTries p.L p.m t (tileList p.nB (encRowA AL) (encColA AR))

/-- The block from b0 on holds the data structure for the arrays `AL β`, `AR β`. -/
structure DSReadyA (p : Sec2.Par) (t aX aY b0 : ℕ) (AL : ArrL p) (AR : ArrR p) (μ : ℕ → ℤ) :
    Prop where
  shared : SharedReadyA p aX aY b0 AL AR μ
  cellT : μ (b0 + 31) = t
  roots : SegN μ (aROOTS p b0) (dsTriesA p t AL AR).roots
  trie : Seg μ (aTR p b0) (dsTriesA p t AL AR).cells

section

variable {p : Sec2.Par} {t aX aY b0 : ℕ} {AL : ArrL p} {AR : ArrR p} {μ μ' : ℕ → ℤ}

theorem memRow_eqA (h : SharedReadyA p aX aY b0 AL AR μ) {β : ℕ} (hβ : β < p.nB)
    (τ : Leaf p.L) (hτ : (digitsT τ).count 9 ≤ p.m) : memRow p b0 μ β τ = encRowA AL β τ :=
  memEnc_eq (h.encA β hβ) τ hτ

theorem memCol_eqA (h : SharedReadyA p aX aY b0 AL AR μ) {β : ℕ} (hβ : β < p.nB)
    (τ : Leaf p.L) (hτ : (digitsT τ).count 9 ≤ p.m) : memCol p b0 μ β τ = encColA AR β τ :=
  memEnc_eq (h.encB β hβ) τ hτ

theorem allTries_mem_eqA (h : SharedReadyA p aX aY b0 AL AR μ) :
    allTries p.L p.m t (tileList p.nB (memRow p b0 μ) (memCol p b0 μ)) = dsTriesA p t AL AR :=
  allTries_tileList_congr t p.nB (fun _ hβ τ hτ => memRow_eqA h hβ τ hτ)
    (fun _ hβ τ hτ => memCol_eqA h hβ τ hτ)

theorem DSReadyA.congr (h : DSReadyA p t aX aY b0 AL AR μ)
    (he : ∀ a, b0 ≤ a → Outside (aWD p b0) (3 * p.L + p.m) a → μ' a = μ a) :
    DSReadyA p t aX aY b0 AL AR μ' := by
  have hend : p.sharedEnd b0 = aWD p b0 := rfl
  obtain ⟨⟩ := areas p t b0
  exact ⟨h.shared.congr fun a ha hlt _ => he a ha (by omega),
    by rw [he _ (by omega) (by omega)]; exact h.cellT,
    h.roots.congr fun i _ => he _ (by omega) (by omega),
    h.trie.congr fun i _ => he _ (by omega) (by omega)⟩

theorem DSReadyA.of_same (h : DSReadyA p t aX aY b0 AL AR μ)
    (hs : SameOutside μ μ' (aWD p b0) (3 * p.L + p.m)) : DSReadyA p t aX aY b0 AL AR μ' :=
  h.congr fun a _ ha => hs a ha

theorem dsReadyA_congr (h : DSReadyA p t aX aY b0 AL AR μ) (he : ∀ a, b0 ≤ a → μ' a = μ a) :
    DSReadyA p t aX aY b0 AL AR μ' :=
  h.congr fun a ha _ => he a ha

end

theorem length_dsTriesA_roots (p : Sec2.Par) (t : ℕ) (AL : ArrL p) (AR : ArrR p) :
    (dsTriesA p t AL AR).roots.length = p.nB * p.nB := by
  unfold dsTriesA
  rw [length_roots_allTries, length_tileList]

theorem length_dsTriesA_le (p : Sec2.Par) (t : ℕ) (AL : ArrL p) (AR : ArrR p) :
    (dsTriesA p t AL AR).cells.length ≤ trieCap p t := by
  unfold dsTriesA trieCap
  have hle := length_allTries_le p.L p.m t (tileList p.nB (encRowA AL) (encColA AR))
  rwa [length_tileList] at hle

/-- The arrays are bounded by U. -/
structure BoundA {p : Sec2.Par} (AL : ArrL p) (AR : ArrR p) (U : ℤ) : Prop where
  nonneg : 0 ≤ U
  left : ∀ β u, |AL β u| ≤ U
  right : ∀ β v, |AR β v| ≤ U

theorem abs_encA_le {p : Sec2.Par} {AL : ArrL p} {AR : ArrR p} {U : ℤ} (hb : BoundA AL AR U)
    (β β' : ℕ) :
    (∀ τ, |encRowA AL β τ| ≤ 7 ^ p.L * U) ∧ ∀ τ, |encColA AR β' τ| ≤ 7 ^ p.L * U :=
  ⟨abs_encodingL_le (hb.left β), abs_encodingR_le (hb.right β')⟩

end Light.Batch
