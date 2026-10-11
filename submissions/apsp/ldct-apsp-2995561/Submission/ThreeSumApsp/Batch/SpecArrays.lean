/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Batch.Tiling
public import Submission.ThreeSumApsp.Spec.Sec2.Theorem5.Layout

/-!
# The batched input arrays at the codes of the strings

As `Spec.bandArrayL_at` and `Spec.bandArrayL_eq_zero`, for the batched arrays: at the code
`gluedCode` of the subset of the slot `(g, h)`, the row `r` of the block and the column `k`, the left
array of the band `β` holds the entry of the source in row `srcBlock β g h · N₀ + r` and column `k`;
it is 0 at every other place.  The same for the right array.
-/

@[expose] public section

namespace ThreeSumApsp.Batch

open ThreeSumApsp.Spec

section
variable {L m R : ℕ} (hmL : m ≤ L)

private theorem codeOuter_rowIdx' (k : Fin (N0 L m)) : codeOuter ((stdLayout hmL).rowIdx k) = k :=
  congrArg Fin.val ((codeEquiv 3 (L - m)).apply_symm_apply k)

private theorem codeOuter_colIdx' (k : Fin (N0 L m)) : codeOuter ((stdLayout hmL).colIdx k) = k :=
  codeOuter_rowIdx' hmL k

private theorem codeInner_innerIdx' (k : Fin (D m)) :
    codeInner ((stdLayout hmL).innerIdx k) = k :=
  congrArg Fin.val ((strEquiv pairEquiv m).apply_symm_apply k)

private theorem maskOf_table' (gh : Fin (K0 L m) × Fin (K0 L m)) :
    maskOf ((stdLayout hmL).table gh) = unrank L m (gh.1 * K0 L m + gh.2) :=
  maskOf_maskSet _ (length_unrank _ _ _)

private theorem gluedCode_table_left' (gh : Fin (K0 L m) × Fin (K0 L m)) (r : Fin (N0 L m))
    (k : Fin (D m)) :
    gluedCode L m (unrank L m (gh.1 * K0 L m + gh.2)) r k
      = codeL (leftStrOf ((stdLayout hmL).table gh) ((stdLayout hmL).table_card gh)
          ((stdLayout hmL).rowIdx r) ((stdLayout hmL).innerIdx k)) := by
  rw [codeL_leftStrOf, codeOuter_rowIdx', codeInner_innerIdx', maskOf_table']

private theorem gluedCode_table_right' (gh : Fin (K0 L m) × Fin (K0 L m)) (c : Fin (N0 L m))
    (k : Fin (D m)) :
    gluedCode L m (unrank L m (gh.1 * K0 L m + gh.2)) c k
      = codeR (rightStrOf ((stdLayout hmL).table gh) ((stdLayout hmL).table_card gh)
          ((stdLayout hmL).innerIdx k) ((stdLayout hmL).colIdx c)) := by
  rw [codeR_rightStrOf, codeOuter_colIdx', codeInner_innerIdx', maskOf_table']

/-- The batched left array, entry by entry. -/
theorem bArrayL_at (X : Matrix (Fin R) (Fin (D m)) ℤ) (β : ℕ) (g h : Fin (K0 L m))
    (r : Fin (N0 L m)) (k : Fin (D m)) :
    (arrL (bArrayL (stdLayout hmL) X β)).getD
        (gluedCode L m (unrank L m (g * K0 L m + h)) r k) 0
      = padRows X (srcBlock L m β g h * N0 L m + r) k := by
  rw [gluedCode_table_left' hmL (g, h) r k, getD_arrL, bArrayL, arrayL_leftStrOf,
    bFamilyL_table, rowBlock, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- The batched right array, entry by entry. -/
theorem bArrayR_at (Y : Matrix (Fin (D m)) (Fin R) ℤ) (β : ℕ) (g h : Fin (K0 L m))
    (c : Fin (N0 L m)) (k : Fin (D m)) :
    (arrR (bArrayR (stdLayout hmL) Y β)).getD
        (gluedCode L m (unrank L m (g * K0 L m + h)) c k) 0
      = padCols Y k (srcBlock L m β g h * N0 L m + c) := by
  rw [gluedCode_table_right' hmL (g, h) c k, getD_arrR, bArrayR, arrayR_rightStrOf,
    bFamilyR_table, colBlock, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

end

private theorem bArrayL_apply_eq_zero {L m R : ℕ} (lay : Layout L m)
    (X : Matrix (Fin R) (Fin (D m)) ℤ) (β : ℕ) (u : LeftStr L)
    (hu : ∀ gh r π, u ≠ leftStrOf (lay.table gh) (lay.table_card gh) r π) :
    bArrayL lay X β u = 0 := by
  rw [bArrayL, arrayL]
  split_ifs with hcard
  · have h0 : bFamilyL lay X β (innerSetL u) = 0 :=
      Finset.sum_eq_zero fun gh _ => if_neg fun (hgh : lay.table gh = _) =>
        hu gh _ _ (leftStr_eq_leftStrOf (lay.table_card gh) hgh.symm hcard)
    rw [h0]
    rfl
  · rfl

private theorem bArrayR_apply_eq_zero {L m R : ℕ} (lay : Layout L m)
    (Y : Matrix (Fin (D m)) (Fin R) ℤ) (β : ℕ) (v : RightStr L)
    (hv : ∀ gh π c, v ≠ rightStrOf (lay.table gh) (lay.table_card gh) π c) :
    bArrayR lay Y β v = 0 := by
  rw [bArrayR, arrayR]
  split_ifs with hcard
  · have h0 : bFamilyR lay Y β (innerSetR v) = 0 :=
      Finset.sum_eq_zero fun gh _ => if_neg fun (hgh : lay.table gh = _) =>
        hv gh _ _ (rightStr_eq_rightStrOf (lay.table_card gh) hgh.symm hcard)
    rw [h0]
    rfl
  · rfl

/-- The batched left array is 0 away from the codes of `bArrayL_at`. -/
theorem bArrayL_eq_zero {L m R : ℕ} (hmL : m ≤ L) (X : Matrix (Fin R) (Fin (D m)) ℤ)
    (β pos : ℕ) (hpos : ∀ (g h : Fin (K0 L m)) (r : Fin (N0 L m)) (k : Fin (D m)),
      pos ≠ gluedCode L m (unrank L m (g * K0 L m + h)) r k) :
    (arrL (bArrayL (stdLayout hmL) X β)).getD pos 0 = 0 := by
  refine getD_arrStr_eq_zero leftEquiv _ fun u hcode =>
    bArrayL_apply_eq_zero _ X β u fun gh r π hu =>
      hpos gh.1 gh.2 ((stdLayout hmL).rowIdx.symm r) ((stdLayout hmL).innerIdx.symm π) ?_
  rw [gluedCode_table_left' hmL gh, Equiv.apply_symm_apply, Equiv.apply_symm_apply, ← hu]
  exact hcode.symm

/-- The batched right array is 0 away from the codes of `bArrayR_at`. -/
theorem bArrayR_eq_zero {L m R : ℕ} (hmL : m ≤ L) (Y : Matrix (Fin (D m)) (Fin R) ℤ)
    (β pos : ℕ) (hpos : ∀ (g h : Fin (K0 L m)) (c : Fin (N0 L m)) (k : Fin (D m)),
      pos ≠ gluedCode L m (unrank L m (g * K0 L m + h)) c k) :
    (arrR (bArrayR (stdLayout hmL) Y β)).getD pos 0 = 0 := by
  refine getD_arrStr_eq_zero rightEquiv _ fun v hcode =>
    bArrayR_apply_eq_zero _ Y β v fun gh π c hv =>
      hpos gh.1 gh.2 ((stdLayout hmL).colIdx.symm c) ((stdLayout hmL).innerIdx.symm π) ?_
  rw [gluedCode_table_right' hmL gh, Equiv.apply_symm_apply, Equiv.apply_symm_apply, ← hv]
  exact hcode.symm

end ThreeSumApsp.Batch
