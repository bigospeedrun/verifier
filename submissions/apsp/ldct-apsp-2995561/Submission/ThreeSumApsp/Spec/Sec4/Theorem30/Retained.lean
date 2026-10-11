/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Spec.Sec4.Theorem30.TileTries

/-!
# The retained leaves: what the data structure reads of the encodings

The data structure reads the two encodings of a tile only through `leafProduct`, and only at leaves
with at most m digits 9 (the retained leaves):

* the value of a box without stars (`boxValue` at e = 0) is read at a member of
  `starBoxes L m t 0`, a string with at most m - t nines (`retained_of_mem_starBoxes_zero`); the
  values of the boxes with stars are looked up in the trie;
* a query reads the products at the members of `lowList`, strings with at most m nines
  (`retained_of_mem_lowList`).

So two pairs of arrays that agree at the retained leaves (`RetAgree`) give the same tries
(`fillTrie_congr`, `fillUpTo_congr`, `tileTrie_congr`, `allTries_congr`,
`allTries_tileList_congr`) and the same queries (`queryTerms_congr`, `trieQuery_congr`).  An encoding with the other leaves set
to 0 (`clipT`) agrees with it at the retained leaves; bounds at the retained leaves are bounds of the
clipped encoding everywhere (`abs_clipT_le`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-- Two arrays on the leaves (indexed by the codes) agree at the leaves with at most r nines. -/
def RetAgree (L r : ℕ) (a a' : List ℤ) : Prop :=
  ∀ l : List ℕ, l.length = L → (∀ d ∈ l, d < 10) → l.count 9 ≤ r →
    a.getD (ofDigitList 10 l) 0 = a'.getD (ofDigitList 10 l) 0

/-- Encodings that agree at the leaves with at most r symbols P₀ have arrays that agree there. -/
theorem retAgree_arrT {L r : ℕ} {f g : Leaf L → ℤ}
    (h : ∀ τ, (digitsT τ).count 9 ≤ r → f τ = g τ) : RetAgree L r (arrT f) (arrT g) := by
  intro l hl hd hc
  obtain ⟨τ, rfl⟩ := exists_digitsT (L := L) l hl hd
  rw [ofDigitList_digitsT, getD_arrT, getD_arrT]
  exact h τ hc

/-! ## The strings that are read are retained -/

/-- A box without stars is a string of L digits with at most m - t nines. -/
theorem retained_of_mem_starBoxes_zero {L m t : ℕ} {l : List ℕ} (h : l ∈ starBoxes L m t 0) :
    l.length = L ∧ (∀ d ∈ l, d < 10) ∧ l.count 9 ≤ m := by
  obtain ⟨l', hl', rfl⟩ := List.mem_map.1 h
  obtain ⟨hlen, hdig, -, hhi⟩ := (mem_nineStrs l').1 hl'
  rw [starFirst_zero]
  exact ⟨hlen, hdig, hhi.trans (Nat.sub_le _ _)⟩

/-- A leaf of order below t contributing to η has at most m nines. -/
theorem retained_of_mem_lowList {L m t : ℕ} {η : OutStr L} (hη : (innerSetO η).card = m)
    {l : List ℕ} (h : l ∈ lowList m t (digitsO η)) :
    l.length = L ∧ (∀ d ∈ l, d < 10) ∧ l.count 9 ≤ m := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 h
  obtain ⟨hlen, hdig, -, hhi⟩ := (mem_nineStrs s).1 hs
  have hcount : (digitsO η).count 9 = m := by rw [← card_innerSetO, hη]
  refine ⟨by rw [length_scatter, length_digitsO], fun d hd => ?_, ?_⟩
  · exact (mem_of_mem_scatter hd).elim (digitsO_lt η d) (hdig d)
  · rw [count_nine_scatter _ _ (hlen.trans hcount.symm)]
    exact hhi

/-! ## Congruence -/

section

variable {L m : ℕ} {a a' b b' : List ℤ} (hA : RetAgree L m a a') (hB : RetAgree L m b b')

include hA hB

/-- The product at a retained leaf. -/
theorem leafProduct_congr {l : List ℕ} (hl : l.length = L) (hd : ∀ d ∈ l, d < 10)
    (hc : l.count 9 ≤ m) : leafProduct a b l = leafProduct a' b' l := by
  rw [leafProduct, leafProduct, hA l hl hd hc, hB l hl hd hc]

/-- The value of a box. -/
theorem boxValue_congr {t e : ℕ} (T : List ℤ) (root : ℕ) {l : List ℕ}
    (hl : l ∈ starBoxes L m t e) : boxValue a b T root e l = boxValue a' b' T root e l := by
  cases e with
  | zero =>
    obtain ⟨hlen, hd, hc⟩ := retained_of_mem_starBoxes_zero hl
    rw [boxValue_zero _ _ _ _ hd, boxValue_zero _ _ _ _ hd]
    exact leafProduct_congr hA hB hlen hd hc
  | succ e => rfl

/-- The dynamic program of Lemma 29, at a box. -/
theorem dpValueD_congr {t : ℕ} (e : ℕ) {l : List ℕ} (hl : l ∈ starBoxes L m t e) :
    dpValueD a b e l = dpValueD a' b' e l := by
  induction e generalizing l with
  | zero => exact boxValue_congr hA hB [] 0 hl
  | succ e ih =>
    obtain ⟨p, hp, hset⟩ := exists_lastStar_of_mem_starBoxes hl
    exact sumAtLastStar_congr hp fun d hd => ih (hset d hd)

/-- Inserting boxes with e stars. -/
theorem fillTrie_congr {t : ℕ} (root e : ℕ) (boxes : List (List ℕ))
    (hmem : ∀ l ∈ boxes, l ∈ starBoxes L m t e) (T : List ℤ) :
    fillTrie a b root e boxes T = fillTrie a' b' root e boxes T := by
  induction boxes generalizing T with
  | nil => rfl
  | cons l boxes ih =>
    simp only [fillTrie, List.foldl_cons]
    rw [boxValue_congr hA hB T root (hmem l (by simp))]
    exact ih (fun x hx => hmem x (by simp [hx])) _

/-- The boxes with fewer than k stars. -/
theorem fillUpTo_congr (t root k : ℕ) (T : List ℤ) :
    fillUpTo a b L m t root k T = fillUpTo a' b' L m t root k T := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [fillUpTo, fillUpTo, ih]
    exact fillTrie_congr hA hB root k _ (fun _ h => h) _

/-- The trie of a tile. -/
theorem tileTrie_congr (t : ℕ) (s : TrieStore) : tileTrie a b L m t s = tileTrie a' b' L m t s := by
  unfold tileTrie tileTrieUpTo
  rw [fillUpTo_congr hA hB]

/-- The numbers that a query adds up. -/
theorem queryTerms_congr (t : ℕ) (stored : List ℕ → ℤ) {η : OutStr L}
    (hη : (innerSetO η).card = m) :
    queryTerms m t a b stored (digitsO η) = queryTerms m t a' b' stored (digitsO η) := by
  unfold queryTerms
  congr 1
  refine List.map_congr_left fun l hl => ?_
  obtain ⟨hlen, hd, hc⟩ := retained_of_mem_lowList hη hl
  exact leafProduct_congr hA hB hlen hd hc

/-- The query on the tries. -/
theorem trieQuery_congr (t : ℕ) (T : List ℤ) (root : ℕ) {η : OutStr L}
    (hη : (innerSetO η).card = m) :
    trieQuery m t a b T root (digitsO η) = trieQuery m t a' b' T root (digitsO η) := by
  unfold trieQuery
  rw [queryTerms_congr hA hB t _ hη]

end

/-- Two tiles whose arrays agree at the retained leaves. -/
def TileEnc.Agree (L m : ℕ) (x y : TileEnc) : Prop :=
  Spec.RetAgree L m x.encA y.encA ∧ Spec.RetAgree L m x.encB y.encB

/-- The tries of all tiles. -/
theorem allTries_congr {L m : ℕ} (t : ℕ) {tiles tiles' : List TileEnc}
    (h : List.Forall₂ (TileEnc.Agree L m) tiles tiles') :
    allTries L m t tiles = allTries L m t tiles' := by
  unfold allTries
  generalize (⟨[0], []⟩ : TrieStore) = s
  induction h generalizing s with
  | nil => rfl
  | cons hxy _ ih =>
    rw [List.foldl_cons, List.foldl_cons, tileTrie_congr hxy.1 hxy.2]
    exact ih _

/-- The tries of all tiles of the product, for encodings that agree at the retained leaves. -/
theorem allTries_tileList_congr {L m : ℕ} (t nB : ℕ) {encA encA' encB encB' : ℕ → Leaf L → ℤ}
    (hA : ∀ β < nB, ∀ τ, (digitsT τ).count 9 ≤ m → encA β τ = encA' β τ)
    (hB : ∀ β < nB, ∀ τ, (digitsT τ).count 9 ≤ m → encB β τ = encB' β τ) :
    allTries L m t (tileList nB encA encB) = allTries L m t (tileList nB encA' encB') := by
  refine allTries_congr t ?_
  unfold tileList
  have hrow : ∀ (is : List ℕ), (∀ β ∈ is, β < nB) →
      List.Forall₂ (TileEnc.Agree L m)
        (is.flatMap fun β => (List.range nB).map fun β' => ⟨arrT (encA β), arrT (encB β')⟩)
        (is.flatMap fun β => (List.range nB).map fun β' => ⟨arrT (encA' β), arrT (encB' β')⟩) := by
    intro is his
    induction is with
    | nil => exact List.Forall₂.nil
    | cons β is ih =>
      rw [List.flatMap_cons, List.flatMap_cons]
      refine List.rel_append ?_ (ih fun x hx => his x (by simp [hx]))
      rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
      intro β' hβ'
      exact ⟨retAgree_arrT (hA β (his β (by simp))), retAgree_arrT (hB β' (List.mem_range.1 hβ'))⟩
  exact hrow _ fun β hβ => List.mem_range.1 hβ

/-! ## The clipped encoding -/

/-- The encoding with the leaves of more than r nines set to 0. -/
def clipT {L : ℕ} (r : ℕ) (f : Leaf L → ℤ) : Leaf L → ℤ :=
  fun τ => if (digitsT τ).count 9 ≤ r then f τ else 0

/-- The clipped encoding agrees with the encoding at the retained leaves. -/
theorem retAgree_clipT {L : ℕ} (r : ℕ) (f : Leaf L → ℤ) :
    RetAgree L r (arrT (clipT r f)) (arrT f) :=
  retAgree_arrT fun _ h => if_pos h

/-- A bound at the retained leaves bounds the clipped encoding everywhere. -/
theorem abs_clipT_le {L r : ℕ} {f : Leaf L → ℤ} {A : ℤ}
    (hA : ∀ τ, (digitsT τ).count 9 ≤ r → |f τ| ≤ A) (τ : Leaf L) : |clipT r f τ| ≤ A := by
  unfold clipT
  split_ifs with h
  · exact hA τ h
  · -- the leaf with all digits 0 is retained, so A ≥ 0
    obtain ⟨τ₀, h₀⟩ := exists_digitsT (L := L) (List.replicate L 0) (by simp) (by simp)
    rw [abs_zero]
    exact (abs_nonneg _).trans (hA τ₀ (by rw [h₀, List.count_replicate]; simp))

end ThreeSumApsp.Spec
