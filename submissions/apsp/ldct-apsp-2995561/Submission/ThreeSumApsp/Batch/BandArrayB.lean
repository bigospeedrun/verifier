/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Programs.Sec2.Theorem5.Encode.BandArray
public import Submission.ThreeSumApsp.Batch.SpecArrays

/-!
# The input array of a batched band

bandArrayB has the arguments of bandArray (Section 2.3.4) and fills the batched array of
`Batch/Tiling.lean`: the slot `(g, h)` of the band `β` holds the row block `srcBlock β g h =
(β K₀ + g) K₀ + h` of the source, on both sides.  The source has `K₀ N` rows of `D` entries, row by
row (for the right side it is the transpose of the `D × K₀ N` matrix); the strides among the
arguments are not read.  The number `N` of rows of a band is a multiple of the band size
(`padN = N`), so every source row exists.  The digits of the row of a block are read from the table
of digits at the row `r` itself (`r < N₀ ≤ N`).

The proof is that of bandArray, with these changes.  `blockNoB`, `rowNoB`: the number of the block
and of the row; `BandCtxB`: the surroundings; the loops over the levels and the coverage lemma
`coverLoop` are those of bandArray.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Batch

open Light.Sec2 Light.Sec2.Band

/-! ## The program -/

/-- One entry: the code of the string, and the entry copied from the source, row by row. -/
def bandCellB : Stmt :=
  .set CodeAcc (k 0) ;;
  .set Outer (v Digits3 +' v Offset *' (v Levels -' v Size)) ;;
  .set Inner (v Digits4 +' v Col *' v Size) ;;
  bandCodeLoop ;;
  .store (v Dest +' v CodeAcc) (M (v Source +' v Row *' v Cols +' v Col))

/-- The loop over the columns k. -/
def bandColLoopB : Stmt := .for Col (v Cols) bandCellB

/-- One row r of a block. -/
def bandRowB : Stmt :=
  .set Row (v BlockIdx *' v Width +' v Offset) ;;
  bandColLoopB

/-- The loop over the rows r of a block. -/
def bandRowLoopB : Stmt := .for Offset (v Width) bandRowB

/-- The address of the mask of the subset of the slot (g, h), and the rows of the block. -/
def bandRowsB : Stmt :=
  .set MaskRow (v MaskTable +' (v PosG *' v NumBlocks +' v PosH) *' v Levels) ;; bandRowLoopB

/-- One slot (g, h): the number of the source block, the same on both sides. -/
def bandBlockB : Stmt :=
  .set BlockIdx ((v BandNo *' v NumBlocks +' v PosG) *' v NumBlocks +' v PosH) ;;
  bandRowsB

/-- The loop over h. -/
def bandHLoopB : Stmt := .for PosH (v NumBlocks) bandBlockB

/-- The loop over g. -/
def bandGLoopB : Stmt := .for PosG (v NumBlocks) bandHLoopB

/-- bandArrayB(L, m, N, D, K0, N0, S7, β, side, aA, sI, sK, mask, dig3, dig4, arr). -/
def bandArrayBBody : Stmt := bandZeroLoop ;; bandGLoopB

/-! ## The numbers -/

namespace BandArgsB
variable (A : BandArgs)

/-- The number of the source block of the slot `(g, h)`. -/
def blockNo (g h : ℕ) : ℕ := (A.β * A.p.K0 + g) * A.p.K0 + h

/-- The number of the source row for the slot `(g, h)` and the row `r` of the block. -/
def rowNo (g h r : ℕ) : ℕ := blockNo A g h * A.p.N0 + r

theorem blockNo_eq (g h : ℕ) : blockNo A g h = Batch.srcBlock A.p.L A.p.m A.β g h := rfl

variable {A}

/-- The source rows are below `K₀ N` when the band size divides `N`. -/
theorem rowNo_lt (hpad : padN A.p.L A.p.m A.p.N = A.p.N) {g h r : ℕ} (hβ : A.β < A.p.nB)
    (hg : g < A.p.K0) (hh : h < A.p.K0) (hr : r < A.p.N0) :
    rowNo A g h r < A.p.K0 * A.p.N ∧ blockNo A g h ≤ rowNo A g h r := by
  have hb1 : A.β * A.p.K0 + g < A.p.nB * A.p.K0 := by
    have := Nat.mul_add_le_mul hβ (le_refl A.p.K0)
    omega
  have hb2 : blockNo A g h < A.p.nB * A.p.K0 * A.p.K0 := by
    have := Nat.mul_add_le_mul hb1 (le_refl A.p.K0)
    unfold blockNo
    omega
  have hb3 : rowNo A g h r < A.p.nB * A.p.K0 * A.p.K0 * A.p.N0 := by
    have := Nat.mul_add_le_mul hb2 (le_refl A.p.N0)
    unfold rowNo
    omega
  have hN : A.p.nB * A.p.K0 * A.p.N0 = A.p.N := by
    rw [← hpad, padN, bandSize, Nat.mul_assoc]
    rfl
  have hle : blockNo A g h ≤ rowNo A g h r := by
    unfold rowNo
    have : blockNo A g h ≤ blockNo A g h * A.p.N0 := Nat.le_mul_of_pos_right _ (N0_pos _ _)
    omega
  refine ⟨?_, hle⟩
  calc rowNo A g h r < A.p.nB * A.p.K0 * A.p.K0 * A.p.N0 := hb3
    _ = A.p.K0 * (A.p.nB * A.p.K0 * A.p.N0) := by ring
    _ = A.p.K0 * A.p.N := by rw [hN]

/-- `N₀ ≤ N`: a band exists, so `N` is at least one band. -/
theorem N0_le_N (hmL : A.p.m ≤ A.p.L) (hpad : padN A.p.L A.p.m A.p.N = A.p.N)
    (hβ : A.β < A.p.nB) : A.p.N0 ≤ A.p.N := by
  have hN : A.p.nB * A.p.K0 * A.p.N0 = A.p.N := by
    rw [← hpad, padN, bandSize, Nat.mul_assoc]
    rfl
  have hK0 : 1 ≤ A.p.K0 := ThreeSumApsp.K0_pos hmL
  calc A.p.N0 = 1 * 1 * A.p.N0 := by ring
    _ ≤ A.p.nB * A.p.K0 * A.p.N0 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul (by omega) hK0)
    _ = A.p.N := hN

end BandArgsB

/-- The local variables of the loop over `h` for the slot `(g, h)`. -/
abbrev blockTmpB (A : BandArgs) (g h : ℕ) : BlockTmp :=
  ⟨h, (BandArgsB.blockNo A g h : ℕ), (A.maskRow g h : ℕ)⟩

/-- The local variables of the loop over the rows for the row `r` of the slot `(g, h)`. -/
abbrev rowTmpB (A : BandArgs) (g h r : ℕ) : RowTmp := ⟨r, (BandArgsB.rowNo A g h r : ℕ)⟩

variable {lim : Limits} {P : Program} {d : ℕ} {A : BandArgs} {μ₀ μ : ℕ → ℤ} {T : List ℤ}

/-! ## The surroundings -/

/-- Everything that the loops assume. -/
structure BandCtxB (lim : Limits) (A : BandArgs) (μ₀ : ℕ → ℤ) (T : List ℤ) : Prop where
  std : Std lim
  hmL : A.p.m ≤ A.p.L
  space : A.arr + A.p.S7 ≤ lim.space
  aA_le : A.aA + A.p.K0 * A.p.N * A.p.D ≤ A.arr
  tabs : BandTables A.p μ₀ A.mask A.dig3 A.dig4 A.arr
  β_lt : A.β < A.p.nB
  pad : padN A.p.L A.p.m A.p.N = A.p.N
  T_len : T.length = A.p.S7
  entry : ∀ g < A.p.K0, ∀ h < A.p.K0, ∀ r < A.p.N0, ∀ k < A.p.D, T.getD (A.code g h r k) 0
    = μ₀ (A.aA + (BandArgsB.rowNo A g h r * A.p.D + k))
  zero : ∀ c : ℕ, (∀ g < A.p.K0, ∀ h < A.p.K0, ∀ r < A.p.N0, ∀ k < A.p.D,
    c ≠ A.code g h r k) → T.getD c 0 = 0

namespace BandCtxB

theorem places (C : BandCtxB lim A μ₀ T) :
    (lim.space : ℤ) ≤ lim.word ∧ 100 ≤ lim.word ∧ A.p.m ≤ A.p.L ∧ A.arr + A.p.S7 ≤ lim.space ∧
      A.aA + A.p.K0 * A.p.N * A.p.D ≤ A.arr ∧ A.mask + A.p.KK * A.p.L ≤ A.arr ∧
      A.dig3 + A.p.N * A.p.Lo ≤ A.arr ∧ A.dig4 + A.p.D * A.p.m ≤ A.arr ∧
      A.p.K0 * A.p.N ≤ A.p.K0 * A.p.N * A.p.D ∧ A.p.L.choose A.p.m ≤ A.p.S7 ∧
      A.p.K0 ≤ A.p.S7 ∧ A.p.N0 ≤ A.p.S7 ∧ A.p.L < A.p.S7 :=
  ⟨C.std.space_le, C.std.const_le, C.hmL, C.space, C.aA_le, C.tabs.mask_le, C.tabs.dig3_le,
    C.tabs.dig4_le, Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega)), A.p.sizes_le_S7⟩

/-- What the loop over the levels reads for the tuple (g, h, r, k). -/
theorem codeCtx (C : BandCtxB lim A μ₀ T) (same : SameOutside μ₀ μ A.arr A.p.S7)
    {g h r k : ℕ} (hg : g < A.p.K0) (hh : h < A.p.K0) (hr : r < A.p.N0) (hk : k < A.p.D) :
    CodeCtx lim μ A.p.L (A.maskRow g h)
      (A.dig3 + r * A.p.Lo) (A.dig4 + k * A.p.m)
      (Spec.unrank A.p.L A.p.m (g * A.p.K0 + h)) (ThreeSumApsp.digitList 3 (A.p.L - A.p.m) r)
      (ThreeSumApsp.digitList 4 A.p.m k) := by
  have hplaces := C.places
  obtain ⟨hKK, hchoose⟩ := subsetIndex_lt A.p hg hh
  have hN0 := BandArgsB.N0_le_N C.hmL C.pad C.β_lt
  have hrN : r < A.p.N := by omega
  have hmask := Nat.mul_add_le_mul hKK (le_refl A.p.L)
  have hdig3 := Nat.mul_add_le_mul hrN (le_refl A.p.Lo)
  have hdig4 := Nat.mul_add_le_mul hk (le_refl A.p.m)
  have hLo : A.p.Lo = A.p.L - A.p.m := rfl
  have hS7 : A.p.S7 = 7 ^ A.p.L := rfl
  have hmaskRow : A.maskRow g h = A.mask + (g * A.p.K0 + h) * A.p.L := rfl
  have hdigits := C.tabs.hdig3 _ hrN
  rw [Nat.mod_eq_of_lt hr] at hdigits
  exact
    { std := C.std
      length := Spec.length_unrank ..
      outer := by rw [Spec.count_false_unrank hchoose, ThreeSumApsp.length_digitList]
      inner := by rw [Spec.count_unrank hchoose, ThreeSumApsp.length_digitList]
      outer_lt := fun _ => ThreeSumApsp.lt_of_mem_digitList (by omega)
      inner_lt := fun _ => ThreeSumApsp.lt_of_mem_digitList (by omega)
      segB := (C.tabs.hmask _ hKK).keep
      segO := hdigits.keep
      segI := (C.tabs.hdig4 k hk).keep
      spaceB := by omega
      spaceO := by rw [ThreeSumApsp.length_digitList]; omega
      spaceI := by rw [ThreeSumApsp.length_digitList]; omega
      space7 := by omega }

end BandCtxB

/-! ## The loop over the columns -/

section cell
variable {g h r k : ℕ}

/-- **One entry**. -/
theorem bandCellB_spec (C : BandCtxB lim A μ₀ T) (same : SameOutside μ₀ μ A.arr A.p.S7)
    (hg : g < A.p.K0) (hh : h < A.p.K0) (hr : r < A.p.N0) (hk : k < A.p.D) (c : CellTmp) :
    Ends lim P d bandCellB
      ⟨frame (locals A g (blockTmpB A g h) (rowTmpB A g h r) { c with k := k }), μ⟩
      (tBandCell A.p)
      fun σ' => ∃ c' : CellTmp, σ' =
        ⟨frame (locals A g (blockTmpB A g h) (rowTmpB A g h r) { c' with k := k }),
          Function.update μ (A.arr + A.code g h r k) (T.getD (A.code g h r k) 0)⟩ := by
  have hplaces := C.places
  obtain ⟨hrow, -⟩ := BandArgsB.rowNo_lt C.pad C.β_lt hg hh hr
  have hN0 := BandArgsB.N0_le_N C.hmL C.pad C.β_lt
  have hrN : r < A.p.N := by omega
  have hdig3 := Nat.mul_add_le_mul hrN (le_refl A.p.Lo)
  have hdig4 := Nat.mul_add_le_mul hk (le_refl A.p.m)
  have hidx := Nat.mul_add_le_mul hrow (le_refl A.p.D)
  have hcode := A.code_lt g h r k
  have hval : μ (A.aA + (BandArgsB.rowNo A g h r * A.p.D + k))
      = T.getD (A.code g h r k) 0 := by
    rw [C.entry g hg h hh r hr k hk]
    exact same _ (Or.inl (by omega))
  have ctx := C.codeCtx same hg hh hr hk
  unfold rowTmpB
  generalize BandArgsB.rowNo A g h r = row at *
  have houter : (r : ℤ) * ((A.p.L : ℤ) - A.p.m) = ((r * A.p.Lo : ℕ) : ℤ) := by
    rw [Nat.cast_mul, show A.p.Lo = A.p.L - A.p.m from rfl, Nat.cast_sub C.hmL]
  have haddr : ((A.aA : ℤ) + row * A.p.D + k).toNat = A.aA + (row * A.p.D + k) := by
    rw [← Nat.cast_mul, ← Nat.cast_add, ← Nat.cast_add, Int.toNat_natCast, Nat.add_assoc]
  unfold bandCellB tBandCell
  -- CodeAcc := 0; Outer := dig3 + Offset (L - m); Inner := dig4 + Col m
  light_set 0
  light_set (A.dig3 + r * A.p.Lo : ℕ) using houter
  light_set (A.dig4 + k * A.p.m : ℕ)
  -- The code.
  refine Ends.next _ (bandCodeLoop_spec ctx ?_ le_rfl)
  rintro ⟨_, _, outer, inner, lev⟩ rfl rfl
  rw [show codeUpTo _ _ _ A.p.L = A.code g h r k from codeUpTo_unrank ..]
  -- mem[arr + CodeAcc] := mem[aA + Row D + Col]
  light_store (A.arr + A.code g h r k) (T.getD (A.code g h r k) 0) using haddr, hval
  exact ⟨⟨k, (A.code g h r k : ℕ), outer, inner, lev⟩, rfl⟩

/-- **The loop over the columns** fills the cells of the tuples (g, h, r, k), k < D. -/
theorem bandColLoopB_spec (C : BandCtxB lim A μ₀ T) (same : SameOutside μ₀ μ A.arr A.p.S7)
    (hg : g < A.p.K0) (hh : h < A.p.K0) (hr : r < A.p.N0) (c : CellTmp) :
    Ends lim P d bandColLoopB ⟨frame (locals A g (blockTmpB A g h) (rowTmpB A g h r) c), μ⟩
      (tBandCol A.p) fun σ' => ∃ (c' : CellTmp) (μ' : ℕ → ℤ),
        σ' = ⟨frame (locals A g (blockTmpB A g h) (rowTmpB A g h r) c'), μ'⟩ ∧
        OverwrittenWith T A.arr A.p.S7 μ μ' ∧ ∀ k < A.p.D, Covered A T μ' g h r k := by
  have hplaces := C.places
  have hD : A.p.D ≤ A.p.K0 * A.p.N * A.p.D := by
    have := (BandArgsB.rowNo_lt C.pad C.β_lt hg hh hr).1
    exact Nat.le_mul_of_pos_left _ (by omega)
  refine (coverLoop (b := tBandCell A.p) (rounds := A.p.D)
    (shape := fun z (c : CellTmp) =>
      locals A g (blockTmpB A g h) (rowTmpB A g h r) { c with k := z })
    (fact := fun k μ' => Covered A T μ' g h r k) (keep := fun _ _ _ hc => hc.keep) (round := ?_)
    c.k c (hT := by simp [tBandCol]; ring_nf; omega)).mono le_rfl
    fun σ' ⟨c', μ', hσ, hfacts⟩ => ⟨_, μ', hσ, hfacts⟩
  intro k hk c' μ' hext
  refine (bandCellB_spec C (same.trans hext.1) hg hh hr hk c').mono le_rfl ?_
  rintro _ ⟨c'', rfl⟩
  exact ⟨c'', _, rfl, .write (BandArgs.code_lt ..), Function.update_self ..⟩

end cell

/-! ## The loop over the rows of a block -/

/-- The cells of the row r of the slot (g, h) are right. -/
def CoveredRowB (A : BandArgs) (T : List ℤ) (μ : ℕ → ℤ) (g h r : ℕ) : Prop :=
  ∀ k < A.p.D, Covered A T μ g h r k

section rows
variable {g h r : ℕ}

/-- **One row of a block**. -/
theorem bandRowB_spec (C : BandCtxB lim A μ₀ T) (same : SameOutside μ₀ μ A.arr A.p.S7)
    (hg : g < A.p.K0) (hh : h < A.p.K0) (hr : r < A.p.N0) (R : RowTmp) (c : CellTmp) :
    Ends lim P d bandRowB ⟨frame (locals A g (blockTmpB A g h) { R with r := r } c), μ⟩
      (tBandRow A.p) fun σ' => ∃ (x : RowTmp × CellTmp) (μ' : ℕ → ℤ),
        σ' = ⟨frame (locals A g (blockTmpB A g h) { x.1 with r := r } x.2), μ'⟩ ∧
        OverwrittenWith T A.arr A.p.S7 μ μ' ∧ CoveredRowB A T μ' g h r := by
  have hplaces := C.places
  obtain ⟨hrow, -⟩ := BandArgsB.rowNo_lt C.pad C.β_lt hg hh hr
  have hD : A.p.K0 * A.p.N ≤ A.p.K0 * A.p.N * A.p.D := hplaces.2.2.2.2.2.2.2.2.1
  have hrowNo : BandArgsB.rowNo A g h r = BandArgsB.blockNo A g h * A.p.N0 + r := rfl
  unfold bandRowB tBandRow
  -- Row := BlockIdx N0 + Offset
  light_set (BandArgsB.rowNo A g h r : ℕ) using hrowNo
  refine (bandColLoopB_spec C same hg hh hr c).mono (by simp) ?_
  rintro _ ⟨c', μ', rfl, hext, hcov⟩
  exact ⟨(rowTmpB A g h r, c'), μ', rfl, hext, hcov⟩

/-- **The loop over the rows of a block** fills the cells of the tuples `(g, h, r, k)`. -/
theorem bandRowLoopB_spec (C : BandCtxB lim A μ₀ T) (same : SameOutside μ₀ μ A.arr A.p.S7)
    (hg : g < A.p.K0) (hh : h < A.p.K0) (R : RowTmp) (c : CellTmp) :
    Ends lim P d bandRowLoopB ⟨frame (locals A g (blockTmpB A g h) R c), μ⟩ (tBandRows A.p)
      fun σ' => ∃ (x : RowTmp × CellTmp) (μ' : ℕ → ℤ),
        σ' = ⟨frame (locals A g (blockTmpB A g h) x.1 x.2), μ'⟩ ∧
        OverwrittenWith T A.arr A.p.S7 μ μ' ∧ ∀ r < A.p.N0, CoveredRowB A T μ' g h r := by
  have hplaces := C.places
  exact (coverLoop (b := tBandRow A.p) (rounds := A.p.N0)
    (shape := fun z (x : RowTmp × CellTmp) =>
      locals A g (blockTmpB A g h) { x.1 with r := z } x.2)
    (fact := fun r μ' => CoveredRowB A T μ' g h r)
    (keep := fun _ _ _ hc hext k hk => (hc k hk).keep hext)
    (round := fun r hr x μ' hext => bandRowB_spec C (same.trans hext.1) hg hh hr x.1 x.2)
    R.r (R, c) (hT := by simp [tBandRows]; ring_nf; omega)).mono le_rfl
    fun σ' ⟨x, μ', hσ, hfacts⟩ => ⟨(_, x.2), μ', hσ, hfacts⟩

end rows

/-! ## The loops over h and g -/

section blocks
variable {g h : ℕ}

/-- **The rows of the slot (g, h)**, once the number of the block is known. -/
theorem bandRowsB_spec (C : BandCtxB lim A μ₀ T) (same : SameOutside μ₀ μ A.arr A.p.S7)
    (hg : g < A.p.K0) (hh : h < A.p.K0) (mrow : ℤ) (R : RowTmp) (c : CellTmp) {T' : ℕ}
    (hT : tBandRows A.p + 10 ≤ T') :
    Ends lim P d bandRowsB
      ⟨frame (locals A g ⟨h, (BandArgsB.blockNo A g h : ℕ), mrow⟩ R c), μ⟩ T'
      fun σ' => ∃ (x : InnerTmp) (μ' : ℕ → ℤ),
        σ' = ⟨frame (locals A g { x.block with h := h } x.row x.cell), μ'⟩ ∧
        OverwrittenWith T A.arr A.p.S7 μ μ' ∧ ∀ r < A.p.N0, CoveredRowB A T μ' g h r := by
  have hplaces := C.places
  obtain ⟨hKK, hchoose⟩ := subsetIndex_lt A.p hg hh
  have hmask := Nat.mul_add_le_mul hKK (le_refl A.p.L)
  have hprod : (((g * A.p.K0 + h) * A.p.L : ℕ) : ℤ) = ((g : ℤ) * A.p.K0 + h) * A.p.L := by
    push_cast
    rfl
  light_set (A.maskRow g h : ℕ) using BandArgs.maskRow
  refine (bandRowLoopB_spec C same hg hh R c).mono (by simp; omega) ?_
  rintro _ ⟨x, μ', rfl, hfacts⟩
  exact ⟨⟨blockTmpB A g h, x.1, x.2⟩, μ', rfl, hfacts⟩

/-- **One slot**: the number of the source block is formed, and the cells of the tuples
`(g, h, r, k)` are filled. -/
theorem bandBlockB_spec (C : BandCtxB lim A μ₀ T) (same : SameOutside μ₀ μ A.arr A.p.S7)
    (hg : g < A.p.K0) (hh : h < A.p.K0) (H : BlockTmp) (R : RowTmp) (c : CellTmp) :
    Ends lim P d bandBlockB ⟨frame (locals A g { H with h := h } R c), μ⟩ (tBandBlock A.p)
      fun σ' => ∃ (x : InnerTmp) (μ' : ℕ → ℤ),
        σ' = ⟨frame (locals A g { x.block with h := h } x.row x.cell), μ'⟩ ∧
        OverwrittenWith T A.arr A.p.S7 μ μ' ∧ ∀ r < A.p.N0, CoveredRowB A T μ' g h r := by
  have hplaces := C.places
  obtain ⟨hrow, hle⟩ := BandArgsB.rowNo_lt C.pad C.β_lt hg hh (N0_pos A.p.L A.p.m)
  have hD : A.p.K0 * A.p.N ≤ A.p.K0 * A.p.N * A.p.D := hplaces.2.2.2.2.2.2.2.2.1
  have hb1 : A.β * A.p.K0 + g ≤ BandArgsB.blockNo A g h := by
    unfold BandArgsB.blockNo
    have : A.β * A.p.K0 + g ≤ (A.β * A.p.K0 + g) * A.p.K0 :=
      Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hb0 : A.β * A.p.K0 ≤ A.β * A.p.K0 + g := Nat.le_add_right _ _
  have hprod : ((BandArgsB.blockNo A g h : ℕ) : ℤ)
      = ((A.β : ℤ) * A.p.K0 + g) * A.p.K0 + h := by
    unfold BandArgsB.blockNo
    push_cast
    rfl
  unfold bandBlockB tBandBlock
  light_set (BandArgsB.blockNo A g h : ℕ) using hprod
  exact bandRowsB_spec C same hg hh _ R c (by simp)

/-- **The loop over `h`**. -/
theorem bandHLoopB_spec (C : BandCtxB lim A μ₀ T) (same : SameOutside μ₀ μ A.arr A.p.S7)
    (hg : g < A.p.K0) (x : InnerTmp) :
    Ends lim P d bandHLoopB ⟨frame (locals A g x.block x.row x.cell), μ⟩ (tBandH A.p)
      fun σ' => ∃ (x' : InnerTmp) (μ' : ℕ → ℤ),
        σ' = ⟨frame (locals A g x'.block x'.row x'.cell), μ'⟩ ∧
        OverwrittenWith T A.arr A.p.S7 μ μ' ∧
        ∀ h < A.p.K0, ∀ r < A.p.N0, CoveredRowB A T μ' g h r := by
  have hplaces := C.places
  exact (coverLoop (b := tBandBlock A.p) (rounds := A.p.K0)
    (shape := fun z (x : InnerTmp) =>
      locals A g { x.block with h := z } x.row x.cell)
    (fact := fun h μ' => ∀ r < A.p.N0, CoveredRowB A T μ' g h r)
    (keep := fun _ _ _ hc hext r hr k hk => (hc r hr k hk).keep hext)
    (round := fun h hh x μ' hext =>
      bandBlockB_spec C (same.trans hext.1) hg hh x.block x.row x.cell)
    x.block.h x (hT := by simp [tBandH]; ring_nf; omega)).mono le_rfl
    fun σ' ⟨x', μ', hσ, hfacts⟩ => ⟨⟨_, x'.row, x'.cell⟩, μ', hσ, hfacts⟩

/-- **The loop over `g`** fills the cells of all tuples `(g, h, r, k)`. -/
theorem bandGLoopB_spec (C : BandCtxB lim A μ₀ T) (same : SameOutside μ₀ μ A.arr A.p.S7)
    (g₀ : ℤ) (x : InnerTmp) :
    Ends lim P d bandGLoopB ⟨frame (locals A g₀ x.block x.row x.cell), μ⟩ (tBandG A.p)
      fun σ' => OverwrittenWith T A.arr A.p.S7 μ σ'.mem ∧
        ∀ g < A.p.K0, ∀ h < A.p.K0, ∀ r < A.p.N0, CoveredRowB A T σ'.mem g h r := by
  have hplaces := C.places
  refine (coverLoop (b := tBandH A.p) (rounds := A.p.K0)
    (shape := fun z (x : InnerTmp) => locals A z x.block x.row x.cell)
    (fact := fun g μ' => ∀ h < A.p.K0, ∀ r < A.p.N0, CoveredRowB A T μ' g h r)
    (keep := fun _ _ _ hc hext h hh r hr k hk => (hc h hh r hr k hk).keep hext)
    (round := fun g hg x μ' hext => bandHLoopB_spec C (same.trans hext.1) hg x)
    g₀ x (hT := by simp [tBandG]; ring_nf; omega)).mono le_rfl ?_
  rintro _ ⟨x', μ', rfl, hfacts⟩
  exact hfacts

end blocks

/-! ## The whole procedure -/

private theorem bandArrayB_time (p : Par) :
    p.S7 * 13 + 6 + tBandG p ≤ cBandArray * bandArrayShape p := by
  have hD : 1 ≤ p.D := Nat.pow_pos (by omega)
  have hN0 : 1 ≤ p.N0 := N0_pos _ _
  have hK0 : p.K0 ≤ p.K0 * p.K0 := Nat.le_mul_self _
  have hKK : p.K0 * p.K0 ≤ p.K0 * p.K0 * p.N0 := Nat.le_mul_of_pos_right _ hN0
  have hrows : p.K0 * p.K0 * p.N0 ≤ p.K0 * p.K0 * p.N0 * p.D := Nat.le_mul_of_pos_right _ hD
  have htime : tBandG p = 28 * (p.K0 * p.K0 * p.N0 * p.D * p.L) + 44 * (p.K0 * p.K0 * p.N0 * p.D)
      + 24 * (p.K0 * p.K0 * p.N0) + 34 * (p.K0 * p.K0) + 14 * p.K0 + 6 := by
    unfold tBandG tBandH tBandBlock tBandRows tBandRow tBandCol tBandCell
    ring
  have hshape : cBandArray * bandArrayShape p = 120 * p.S7
      + 120 * (p.K0 * p.K0 * p.N0 * p.D * p.L) + 120 * (p.K0 * p.K0 * p.N0 * p.D) + 120 * p.L
      + 120 := by
    unfold cBandArray bandArrayShape Par.KK
    ring
  omega

/-- **bandArrayB** writes the list T to the array and changes nothing else. -/
theorem bandArrayB_spec (C : BandCtxB lim A μ₀ T) :
    Ends lim P d bandArrayBBody ⟨frame (args A), μ₀⟩ (cBandArray * bandArrayShape A.p) fun σ' =>
      Seg σ'.mem A.arr T ∧ SameOutside μ₀ σ'.mem A.arr A.p.S7 := by
  have hplaces := C.places
  have htime := bandArrayB_time A.p
  have hcleared : SameOutside μ₀ (wrote μ₀ A.arr (fun _ => 0) A.p.S7) A.arr A.p.S7 :=
    sameOutside_wrote le_rfl
  refine Ends.next _ (Ends.pass (x := Cells) (y := Dest) (dst := A.arr) (n := A.p.S7) (fun _ => 0)
    (fun j _ => by light_side) ?_ C.std.space_le C.space rfl rfl (hT := le_rfl)) (by simp; omega)
  rw [update_frame_setLocal, ← frame_append_zeros _ 10]
  refine (bandGLoopB_spec C hcleared A.p.S7 ⟨⟨0, 0, 0⟩, ⟨0, 0⟩, ⟨0, 0, 0, 0, 0⟩⟩).mono
    (by simp; omega) ?_
  rintro ⟨_, μ'⟩ ⟨hext, hcov⟩
  dsimp only at hext hcov ⊢
  refine ⟨fun c hc => ?_, hcleared.trans hext.1⟩
  have hc7 : c < A.p.S7 := C.T_len ▸ hc
  rw [← List.getD_eq_getElem T 0 hc]
  have hzero : T.getD c 0 = 0 → μ' (A.arr + c) = T.getD c 0 := fun h0 =>
    (hext.2 c hc7).elim (fun h => by rw [h, wrote_done hc7, h0]) id
  by_cases hx : ∃ g < A.p.K0, ∃ h < A.p.K0, ∃ r < A.p.N0, ∃ k < A.p.D, c = A.code g h r k
  · obtain ⟨g, hg, h, hh, r, hr, k, hk, rfl⟩ := hx
    exact hcov g hg h hh r hr k hk
  · exact hzero (C.zero c fun g hg h hh r hr k hk hce => hx ⟨g, hg, h, hh, r, hr, k, hk, hce⟩)

/-! ## What the callers assume -/

/-- bandArrayB for the left side, at the arguments with which encodeBandsP calls it: the source `X`
(`K₀ N × D`, row by row) at aX.  Writes the batched array of the band β. -/
def BandArrayBLSpec (lim : Limits) (P : Program) (c : ℕ) : Prop :=
  ∀ (p : Par) (hmL : p.m ≤ p.L) (β aX mask dig3 dig4 arr : ℕ) (μ : ℕ → ℤ)
    (X : Matrix (Fin (p.K0 * p.N)) (Fin (ThreeSumApsp.D p.m)) ℤ),
    arr + p.S7 ≤ lim.space → MatAt μ aX X → aX + p.K0 * p.N * p.D ≤ arr →
    BandTables p μ mask dig3 dig4 arr → β < p.nB → padN p.L p.m p.N = p.N →
    ∀ d, d ≤ lim.depth → Meets lim P pBandArray d
      [p.L, p.m, p.N, p.D, p.K0, p.N0, p.S7, β, 0, aX, p.D, 1, mask, dig3, dig4, arr] μ
      (c * bandArrayShape p) fun _ μ' =>
      Seg μ' arr (Spec.arrL (Batch.bArrayL (Spec.stdLayout hmL) X β)) ∧ SameOutside μ μ' arr p.S7

/-- The same for the right side: the source is the transpose of `Y` (`D × K₀ N`), that is, `Yᵀ`
row by row at aY. -/
def BandArrayBRSpec (lim : Limits) (P : Program) (c : ℕ) : Prop :=
  ∀ (p : Par) (hmL : p.m ≤ p.L) (β aY mask dig3 dig4 arr : ℕ) (μ : ℕ → ℤ)
    (Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin (p.K0 * p.N)) ℤ),
    arr + p.S7 ≤ lim.space → MatAt μ aY Y.transpose → aY + p.K0 * p.N * p.D ≤ arr →
    BandTables p μ mask dig3 dig4 arr → β < p.nB → padN p.L p.m p.N = p.N →
    ∀ d, d ≤ lim.depth → Meets lim P pBandArray d
      [p.L, p.m, p.N, p.D, p.K0, p.N0, p.S7, β, 1, aY, 1, p.N, mask, dig3, dig4, arr] μ
      (c * bandArrayShape p) fun _ μ' =>
      Seg μ' arr (Spec.arrR (Batch.bArrayR (Spec.stdLayout hmL) Y β)) ∧ SameOutside μ μ' arr p.S7

/-- **bandArrayB, left side.** -/
theorem bandArrayBL_entry (std : Std lim) (hP : P[pBandArray]? = some bandArrayBBody) :
    BandArrayBLSpec lim P cBandArray := by
  intro p hmL β aX mask dig3 dig4 arr μ X hsp hX hXle htab hβ hpad d _
  refine ⟨bandArrayBBody, hP, bandArrayB_spec (A := .ofX p β aX mask dig3 dig4 arr)
    { std := std, hmL := hmL, space := hsp, aA_le := hXle, tabs := htab, β_lt := hβ, pad := hpad
      T_len := Spec.length_arrL _
      entry := fun g hg h hh r hr k hk => ?_
      zero := fun c hc =>
        Batch.bArrayL_eq_zero hmL X β c fun g h r k => hc g g.2 h h.2 r r.2 k k.2 }⟩
  refine (Batch.bArrayL_at hmL X β ⟨g, hg⟩ ⟨h, hh⟩ ⟨r, hr⟩ ⟨k, hk⟩).trans ?_
  have hrow := (BandArgsB.rowNo_lt (A := .ofX p β aX mask dig3 dig4 arr) hpad hβ hg hh hr).1
  change padRows X (BandArgsB.rowNo (.ofX p β aX mask dig3 dig4 arr) g h r) ⟨k, hk⟩ = _
  generalize BandArgsB.rowNo (.ofX p β aX mask dig3 dig4 arr) g h r = row at hrow ⊢
  unfold padRows
  rw [dif_pos hrow, ← hX ⟨_, hrow⟩ ⟨k, hk⟩]
  show μ (aX + row * p.D + k) = μ (aX + (row * p.D + k))
  rw [Nat.add_assoc]

/-- **bandArrayB, right side.** -/
theorem bandArrayBR_entry (std : Std lim) (hP : P[pBandArray]? = some bandArrayBBody) :
    BandArrayBRSpec lim P cBandArray := by
  intro p hmL β aY mask dig3 dig4 arr μ Y hsp hY hYle htab hβ hpad d _
  refine ⟨bandArrayBBody, hP, bandArrayB_spec (A := .ofY p β aY mask dig3 dig4 arr)
    { std := std, hmL := hmL, space := hsp, aA_le := hYle, tabs := htab, β_lt := hβ, pad := hpad
      T_len := Spec.length_arrR _
      entry := fun g hg h hh r hr k hk => ?_
      zero := fun c hc =>
        Batch.bArrayR_eq_zero hmL Y β c fun g h r k => hc g g.2 h h.2 r r.2 k k.2 }⟩
  refine (Batch.bArrayR_at hmL Y β ⟨g, hg⟩ ⟨h, hh⟩ ⟨r, hr⟩ ⟨k, hk⟩).trans ?_
  have hrow := (BandArgsB.rowNo_lt (A := .ofY p β aY mask dig3 dig4 arr) hpad hβ hg hh hr).1
  change padCols Y ⟨k, hk⟩ (BandArgsB.rowNo (.ofY p β aY mask dig3 dig4 arr) g h r) = _
  generalize BandArgsB.rowNo (.ofY p β aY mask dig3 dig4 arr) g h r = row at hrow ⊢
  unfold padCols
  rw [dif_pos hrow, show Y ⟨k, hk⟩ ⟨row, hrow⟩ = Y.transpose ⟨row, hrow⟩ ⟨k, by exact hk⟩ from rfl,
    ← hY ⟨_, hrow⟩ ⟨k, by exact hk⟩]
  show μ (aY + row * p.D + k) = μ (aY + (row * p.D + k))
  rw [Nat.add_assoc]

end Light.Batch
