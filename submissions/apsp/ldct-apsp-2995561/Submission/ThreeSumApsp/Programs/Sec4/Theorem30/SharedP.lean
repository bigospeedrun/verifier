/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Programs.Sec2.PrunedEnc.Contracts
public import Submission.ThreeSumApsp.Programs.Sec2.Theorem5.CellDependencies
public import Submission.ThreeSumApsp.Spec.Sec4.Theorem30.Retained

/-!
# The shared stage with pruned encodings, as Section 4 uses it

The shared stage of Section 4 (`Sec2.SharedReadyP`) writes the encodings only at the leaves with at
most m nines, the retained leaves; the other cells of the encoding areas hold whatever was there.
The routines of Section 4 are handed what the memory holds (`memEnc`, which is a segment of the
memory by definition, `seg_memEnc`), and this agrees with the true encodings at the retained leaves
(`memEnc_eq`), which are the only ones that the data structure reads (`Spec.RetAgree`).

* The number of nines of the code of a leaf is the number of its digits 9 (`ninesIdx_ofDigitList`).
* `SharedReadyP` depends only on the cells of the shared block, without cell 31 of the directory
  (`SharedReadyP.congr`, `SharedReadyP.of_agree`), as `SharedReady` does.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## Nines of a code -/

/-- A first digit d in front of the list l. -/
theorem ofDigitList_ten_cons (d : ℕ) (l : List ℕ) :
    ofDigitList 10 (d :: l) = d * 10 ^ l.length + ofDigitList 10 l := by
  induction l using List.reverseRecOn with
  | nil => simp [ofDigitList]
  | append_singleton l x ih =>
    rw [← List.cons_append, ofDigitList_append_singleton, ofDigitList_append_singleton, ih,
      List.length_append, List.length_singleton, pow_succ]
    ring

/-- The number of nines among the L digits of the code of a list of L digits is the number of its
digits 9. -/
theorem ninesIdx_ofDigitList (l : List ℕ) (hd : ∀ d ∈ l, d < 10) :
    ninesIdx l.length (ofDigitList 10 l) = l.count 9 := by
  induction l with
  | nil => simp [ninesIdx]
  | cons d l ih =>
    have hd' := hd d (by simp)
    have hlt := ofDigitList_lt l fun x hx => hd x (by simp [hx])
    have hpos : 0 < 10 ^ l.length := Nat.pos_of_ne_zero (by positivity)
    have hdiv : (d * 10 ^ l.length + ofDigitList 10 l) / 10 ^ l.length = d := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hlt, Nat.zero_add]
    have hmod : (d * 10 ^ l.length + ofDigitList 10 l) % 10 ^ l.length = ofDigitList 10 l := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
    rw [List.length_cons, ninesIdx, ofDigitList_ten_cons, hdiv, hmod,
      ih fun x hx => hd x (by simp [hx]), List.count_cons]
    by_cases h9 : d = 9 <;> simp [h9, Nat.add_comm]

/-- The number of nines of the code of a leaf. -/
theorem ninesIdx_codeT {L : ℕ} (τ : Leaf L) : ninesIdx L (codeT τ) = (digitsT τ).count 9 := by
  have h := ninesIdx_ofDigitList (digitsT τ) (digitsT_lt τ)
  rwa [length_digitsT, ofDigitList_digitsT] at h

/-! ## Pruned segments -/

/-- A pruned segment stays where it is if its cells do not change. -/
theorem RetSeg.congr {L r : ℕ} {μ μ' : ℕ → ℤ} {a : ℕ} {l : List ℤ} (h : RetSeg L r μ a l)
    (he : ∀ i < l.length, μ' (a + i) = μ (a + i)) : RetSeg L r μ' a l :=
  fun i hi h9 => (he i hi).trans (h i hi h9)

/-- A pruned segment of an encoding holds its number at a leaf with at most r symbols P₀. -/
theorem RetSeg.read {L r : ℕ} {μ : ℕ → ℤ} {a : ℕ} {enc : Leaf L → ℤ}
    (h : RetSeg L r μ a (arrT enc)) (τ : Leaf L) (hτ : (digitsT τ).count 9 ≤ r) :
    μ (a + codeT τ) = enc τ := by
  rw [h (codeT τ) (by rw [length_arrT]; exact codeT_lt τ) (by rwa [ninesIdx_codeT]), getD_arrT]

/-! ## What the shared stage leaves behind -/

variable {p : Par} {hmL : p.m ≤ p.L} {aX aY b0 : ℕ}
  {X : Matrix (Fin p.N) (Fin (ThreeSumApsp.D p.m)) ℤ}
  {Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin p.N) ℤ} {μ μ' : ℕ → ℤ}

/-- Cell j of the directory, with the address in the form in which the evaluation of mem[b0 + j]
meets it. -/
theorem SharedReadyP.dir_read (h : SharedReadyP p hmL aX aY b0 X Y μ) {j : ℕ} (hj : j < 31) :
    μ ((b0 : ℤ) + j).toNat = ((dirList p aX aY b0).getD j 0 : ℕ) := by
  rw [toNat_natCast_add_natCast]
  exact h.dir.read (by simpa [dirList] using hj)

/-- What the shared stage leaves behind is kept by a memory that agrees on the cells of the shared
block, but for cell 31 of the directory, which the shared stage does not use. -/
theorem SharedReadyP.congr (h : SharedReadyP p hmL aX aY b0 X Y μ)
    (hag : ∀ a, b0 ≤ a → a < p.sharedEnd b0 → a ≠ b0 + 31 → μ' a = μ a) :
    SharedReadyP p hmL aX aY b0 X Y μ' := by
  have hplaces := p.places b0
  have tb : SharedTables p b0 μ' :=
    h.toSharedTables.congr fun x hlo hx => hag x (by omega) (by omega) (by omega)
  have henc : ∀ {a β i : ℕ}, p.aENCA b0 ≤ a → a + p.nB * p.T ≤ p.sharedEnd b0 → β < p.nB →
      i < p.T → μ' (a + β * p.T + i) = μ (a + β * p.T + i) := fun ha hend hβ hi => by
    have := Nat.mul_add_lt_mul hβ hi
    exact hag _ (by omega) (by omega) (by omega)
  refine
    { tb with
      dir := h.dir.congr fun i hi => ?_
      encA := fun β hβ => (h.encA β hβ).congr fun i hi =>
        henc le_rfl (by omega) hβ (by rwa [Spec.length_arrT] at hi)
      encB := fun β hβ => (h.encB β hβ).congr fun i hi =>
        henc (by omega) (by omega) hβ (by rwa [Spec.length_arrT] at hi) }
  simp only [dirList, List.length_map, List.length_cons, List.length_nil] at hi
  simp only [Par.aDIR]
  exact hag _ (by omega) (by omega) (by omega)

/-- What the shared stage leaves behind is kept by a memory that agrees on all cells below the end
of the shared block, but for cell 31 of the directory. -/
theorem SharedReadyP.of_agree (h : SharedReadyP p hmL aX aY b0 X Y μ)
    (hag : ∀ a, a < p.sharedEnd b0 → a ≠ b0 + 31 → μ' a = μ a) :
    SharedReadyP p hmL aX aY b0 X Y μ' :=
  h.congr fun a _ => hag a

end Light.Sec2

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The encodings that the routines are handed -/

/-- The cells from a, read as an array on the leaves of depth L: what the memory holds where an
encoding should be. -/
def memEnc (μ : ℕ → ℤ) (a L : ℕ) : Leaf L → ℤ := fun τ => μ (a + codeT τ)

/-- The memory holds this array. -/
theorem seg_memEnc (μ : ℕ → ℤ) (a L : ℕ) : Seg μ a (arrT (memEnc μ a L)) := by
  intro i hi
  have hi' : i < 10 ^ L := by rwa [length_arrT] at hi
  rw [← List.getD_eq_getElem _ 0 hi, arrT, getD_arrStr_of_lt termEquiv _ hi', memEnc]
  exact congrArg (fun j => μ (a + j)) (codeStr_decodeStr termEquiv hi').symm

/-- If the memory holds a pruned segment of an encoding, the array agrees with the encoding at the
leaves with at most r symbols P₀. -/
theorem memEnc_eq {L r : ℕ} {μ : ℕ → ℤ} {a : ℕ} {enc : Leaf L → ℤ}
    (h : Sec2.RetSeg L r μ a (arrT enc)) (τ : Leaf L) (hτ : (digitsT τ).count 9 ≤ r) :
    memEnc μ a L τ = enc τ :=
  h.read τ hτ

end Light.Sec4
