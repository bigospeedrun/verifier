/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Sec4.Theorem30

/-!
# Batched tiles: independent products in the slots of one run

Lemma 9 holds for every family `Q ↦ (X_Q, Y_Q)`, so the `K₀²` slots of one run of `Full` may hold
block products of `K₀²` different matrix products. Here the slot `(g, h)` of the band `β` holds the
block number `srcBlock β g h = (β K₀ + g) K₀ + h` of a stacked source matrix, on both sides. If the
source stacks the products interleaved (the row block `i` of product `u` is the block `i K₀² + u`),
then the slot `(g, h)` of the tile `(β, β')` computes the block `(β, β')` of the product
`u = g K₀ + h`.

* `bFamilyL`, `bFamilyR`, `bArrayL`, `bArrayR`: the families and the input arrays of a band.
* `Full_bArray_eq_block_mul`: one run computes the product of the two source blocks of each slot.
* `queryValue_bArray`: a query for a position `(I, J)` of the tile, as in Theorem 30, returns the
  inner product of the source row `srcRow I J` and the source column `srcCol I J`.
-/

@[expose] public section

open Finset

namespace ThreeSumApsp.Batch

/-- The source block of the slot `(g, h)` of the band `β`. -/
def srcBlock (L m β g h : ℕ) : ℕ := (β * K0 L m + g) * K0 L m + h

/-- The left family of a band: the slot `(g, h)` holds the row block `srcBlock β g h`. -/
def bFamilyL {L m R : ℕ} (lay : Layout L m) (X : Matrix (Fin R) (Fin (D m)) ℤ) (β : ℕ) :
    Finset (Fin L) → LeftMat L m :=
  fun Q => ∑ gh, if lay.table gh = Q then rowBlock lay X (srcBlock L m β gh.1 gh.2) else 0

/-- The right family of a band: the slot `(g, h)` holds the column block `srcBlock β g h`. -/
def bFamilyR {L m R : ℕ} (lay : Layout L m) (Y : Matrix (Fin (D m)) (Fin R) ℤ) (β : ℕ) :
    Finset (Fin L) → RightMat L m :=
  fun Q => ∑ gh, if lay.table gh = Q then colBlock lay Y (srcBlock L m β gh.1 gh.2) else 0

/-- The left input array of a band. -/
def bArrayL {L m R : ℕ} (lay : Layout L m) (X : Matrix (Fin R) (Fin (D m)) ℤ) (β : ℕ) :
    LeftStr L → ℤ :=
  arrayL m (bFamilyL lay X β)

/-- The right input array of a band. -/
def bArrayR {L m R : ℕ} (lay : Layout L m) (Y : Matrix (Fin (D m)) (Fin R) ℤ) (β : ℕ) :
    RightStr L → ℤ :=
  arrayR m (bFamilyR lay Y β)

private theorem sum_table_eq' {L m : ℕ} {A : Type*} [AddCommMonoid A] (lay : Layout L m)
    (F : Fin (K0 L m) × Fin (K0 L m) → A) (gh : Fin (K0 L m) × Fin (K0 L m)) :
    (∑ gh', if lay.table gh' = lay.table gh then F gh' else 0) = F gh := by
  simp [lay.table_injective.eq_iff]

@[simp]
theorem bFamilyL_table {L m R : ℕ} (lay : Layout L m) (X : Matrix (Fin R) (Fin (D m)) ℤ) (β : ℕ)
    (g h : Fin (K0 L m)) : bFamilyL lay X β (lay.table (g, h)) = rowBlock lay X (srcBlock L m β g h) :=
  sum_table_eq' lay (fun gh => rowBlock lay X (srcBlock L m β gh.1 gh.2)) (g, h)

@[simp]
theorem bFamilyR_table {L m R : ℕ} (lay : Layout L m) (Y : Matrix (Fin (D m)) (Fin R) ℤ) (β : ℕ)
    (g h : Fin (K0 L m)) : bFamilyR lay Y β (lay.table (g, h)) = colBlock lay Y (srcBlock L m β g h) :=
  sum_table_eq' lay (fun gh => colBlock lay Y (srcBlock L m β gh.1 gh.2)) (g, h)

/-- One run of `Full` on the tile `(β, β')` computes, in the slot `(g, h)`, the product of the source
blocks `srcBlock β g h` and `srcBlock β' g h`. -/
theorem Full_bArray_eq_block_mul {L m R : ℕ} (lay : Layout L m)
    (X : Matrix (Fin R) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin R) ℤ) (β β' : ℕ)
    (g h : Fin (K0 L m)) (r c : OuterStr L m) :
    Full L (bArrayL lay X β) (bArrayR lay Y β')
        (outStrOf (lay.table (g, h)) (lay.table_card (g, h)) r c)
      = (rowBlock lay X (srcBlock L m β g h) * colBlock lay Y (srcBlock L m β' g h)) r c := by
  rw [bArrayL, bArrayR, Full_arrays_eq_mul, bFamilyL_table, bFamilyR_table]

/-- The source row of the position `(I, J)` of a tile. -/
def srcRow {L m : ℕ} (lay : Layout L m) (I J : ℕ) : ℕ :=
  srcBlock L m (bandOf L m I) (blockOf lay I) (blockOf lay J) * N0 L m + I % N0 L m

/-- The source column of the position `(I, J)` of a tile. -/
def srcCol {L m : ℕ} (lay : Layout L m) (I J : ℕ) : ℕ :=
  srcBlock L m (bandOf L m J) (blockOf lay I) (blockOf lay J) * N0 L m + J % N0 L m

/-- The value of a query, as in Theorem 30, is the sum of Lemma 28 for the arrays of the tile. -/
theorem queryValue_eq_querySum {L : ℕ} (m t : ℕ) (a : LeftStr L → ℤ) (b : RightStr L → ℤ)
    (η : OutStr L) : queryValue m t (encodingL a) (encodingR b) η = querySum m t a b η := by
  unfold queryValue querySum
  congr 1
  exact sum_congr rfl fun V hV => sum_congr rfl fun π hπ =>
    dpValue_card_starLevels _ _ (Theorem30.lookup hV hπ)

/-- **A query on batched tiles.** For the position `(I, J)`, with the band of `I` and the band of
`J`, the query of Theorem 30 returns the inner product of the source row `srcRow I J` of `X` and the
source column `srcCol I J` of `Y` (zero outside the matrices). -/
theorem queryValue_bArray {L m R : ℕ} (t : ℕ) (ht : t ≤ m) (lay : Layout L m)
    (X : Matrix (Fin R) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin R) ℤ) (I J : ℕ) :
    queryValue m t (encodingL (bArrayL lay X (bandOf L m I)))
        (encodingR (bArrayR lay Y (bandOf L m J))) (outStrOfPos lay I J)
      = ∑ k : Fin (D m), padRows X (srcRow lay I J) k * padCols Y k (srcCol lay I J) := by
  rw [queryValue_eq_querySum, ← Lemma28.Mult_eq_querySum m t ht _ _ _
    (card_innerSetO_outStrOfPos lay I J), ← Lemma7.returns_Mult]
  unfold outStrOfPos
  rw [Full_bArray_eq_block_mul, Matrix.mul_apply, ← Equiv.sum_comp lay.innerIdx]
  refine sum_congr rfl fun k _ => ?_
  simp only [rowBlock, colBlock, Equiv.symm_apply_apply, srcRow, srcCol, offsetOf]

/-! ## Bounds -/

theorem abs_bArrayL_le {L m R : ℕ} (lay : Layout L m) {X : Matrix (Fin R) (Fin (D m)) ℤ} {U : ℤ}
    (hU : 0 ≤ U) (hX : ∀ i j, |X i j| ≤ U) (β : ℕ) (u : LeftStr L) : |bArrayL lay X β u| ≤ U := by
  unfold bArrayL arrayL
  split_ifs with h
  · unfold bFamilyL
    by_cases hQ : ∃ gh, lay.table gh = innerSetL u
    · obtain ⟨gh, hgh⟩ := hQ
      rw [← hgh, sum_table_eq' lay (fun gh => rowBlock lay X (srcBlock L m β gh.1 gh.2)) gh]
      unfold rowBlock padRows
      split_ifs
      · exact hX _ _
      · simpa using hU
    · rw [sum_eq_zero fun gh _ => if_neg fun h' => hQ ⟨gh, h'⟩]
      simpa using hU
  · simpa using hU

theorem abs_bArrayR_le {L m R : ℕ} (lay : Layout L m) {Y : Matrix (Fin (D m)) (Fin R) ℤ} {U : ℤ}
    (hU : 0 ≤ U) (hY : ∀ i j, |Y i j| ≤ U) (β : ℕ) (v : RightStr L) : |bArrayR lay Y β v| ≤ U := by
  unfold bArrayR arrayR
  split_ifs with h
  · unfold bFamilyR
    by_cases hQ : ∃ gh, lay.table gh = innerSetR v
    · obtain ⟨gh, hgh⟩ := hQ
      rw [← hgh, sum_table_eq' lay (fun gh => colBlock lay Y (srcBlock L m β gh.1 gh.2)) gh]
      unfold colBlock padCols
      split_ifs
      · exact hY _ _
      · simpa using hU
    · rw [sum_eq_zero fun gh _ => if_neg fun h' => hQ ⟨gh, h'⟩]
      simpa using hU
  · simpa using hU

end ThreeSumApsp.Batch
