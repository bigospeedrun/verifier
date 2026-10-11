/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Programs.Sec2.Theorem5.Contracts

/-!
# Pruned encodings: the contracts

The data structure of Section 4 reads the encoding of a band only at the leaves whose code has at
most m digits 9 (the boxes with no star and the strings of the low lists).  The pruned encoder
computes only these leaves: below the term number 9 (the term P₀) it recurses with one 9 fewer
allowed, and with none left it skips that term.  The other cells of the output keep what was there.

* `ninesIdx L i`: the number of digits 9 among the L decimal digits of i (most significant first).
* `retW L r`: the number of leaves with at most r nines, `∑_{j ≤ r} C(L, j) 9^{L-j}`, by its
  recursion; the pruned encoder takes `O(retW L r)` steps.
* `RetSeg L r μ a l`: the cells from a hold l at the positions with at most r nines.
* `EncodePLSpec`, `EncodePRSpec`: the entries of the pruned encoder (procedure `pEncodeP`, arguments
  `[n, src, dst, scr, tab, p7, p10, r]`).
* `SharedReadyP`, `sharedShapeP`, `SharedSpecP`: the shared stage with pruned encodings (procedure
  `pSharedP`, the same arguments as `pShared`, budget `m`).
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

/-- The number of digits 9 among the `L` decimal digits of `i`, most significant first. -/
def ninesIdx : ℕ → ℕ → ℕ
  | 0, _ => 0
  | L + 1, i => (if i / 10 ^ L = 9 then 1 else 0) + ninesIdx L (i % 10 ^ L)

/-- The number of strings of `L` decimal digits with at most `r` nines. -/
def retW : ℕ → ℕ → ℕ
  | 0, _ => 1
  | L + 1, 0 => 9 * retW L 0
  | L + 1, r + 1 => 9 * retW L (r + 1) + retW L r

/-- The cells from `a` hold the list `l` at the positions whose `L` digits have at most `r`
nines. -/
def RetSeg (L r : ℕ) (μ : ℕ → ℤ) (a : ℕ) (l : List ℤ) : Prop :=
  ∀ i < l.length, ninesIdx L i ≤ r → μ (a + i) = l.getD i 0

/-! ## The numbers of the procedures (unused numbers of Section 2) -/

/-- The number of the pruned encoder. -/
def pEncodeP : ℕ := 29
/-- The number of the pruned encodeBands. -/
def pEncodeBandsP : ℕ := 30
/-- The number of the shared stage with pruned encodings. -/
def pSharedP : ℕ := 31

section Entries

variable (lim : Limits) (P : Program) (c : ℕ)

/-- encodeP(n, src, dst, scr, tab, p7, p10, r), with the coefficients φ: the encoding of the array a
at src, at the leaves with at most r nines, within c · retW n r steps. -/
def EncodePLSpec : Prop :=
  ∀ (n Lmax src dst scr tab p7 p10 r : ℕ) (μ : ℕ → ℤ) (a : LeftStr n → ℤ) (V : ℤ),
    EncodePlaces lim n Lmax src dst scr tab p7 p10 μ →
    Seg μ tab Spec.phiFlat → Seg μ src (Spec.arrL a) → (∀ u, |a u| ≤ V) →
    7 ^ (n + 1) * V ≤ lim.word →
    ∀ d, d + (n + 1) ≤ lim.depth →
    Meets lim P pEncodeP d [n, src, dst, scr, tab, p7, p10, r] μ (c * retW n r) fun _ μ' =>
      RetSeg n r μ' dst (Spec.arrT (encodingL a)) ∧ SameOutside2 μ μ' dst (10 ^ n) scr (7 ^ n)

/-- The same procedure with the coefficients ψ. -/
def EncodePRSpec : Prop :=
  ∀ (n Lmax src dst scr tab p7 p10 r : ℕ) (μ : ℕ → ℤ) (b : RightStr n → ℤ) (V : ℤ),
    EncodePlaces lim n Lmax src dst scr tab p7 p10 μ →
    Seg μ tab Spec.psiFlat → Seg μ src (Spec.arrR b) → (∀ v, |b v| ≤ V) →
    7 ^ (n + 1) * V ≤ lim.word →
    ∀ d, d + (n + 1) ≤ lim.depth →
    Meets lim P pEncodeP d [n, src, dst, scr, tab, p7, p10, r] μ (c * retW n r) fun _ μ' =>
      RetSeg n r μ' dst (Spec.arrT (encodingR b)) ∧ SameOutside2 μ μ' dst (10 ^ n) scr (7 ^ n)

end Entries

/-! ## The shared stage with pruned encodings -/

/-- What the shared stage with pruned encodings leaves behind: the tables, the directory, and the
encodings of all bands at the leaves with at most m nines. -/
structure SharedReadyP (p : Par) (hmL : p.m ≤ p.L) (aX aY b0 : ℕ)
    (X : Matrix (Fin p.N) (Fin (ThreeSumApsp.D p.m)) ℤ)
    (Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin p.N) ℤ) (μ : ℕ → ℤ) : Prop
  extends SharedTables p b0 μ where
  dir : SegN μ (p.aDIR b0) (dirList p aX aY b0)
  encA : ∀ β < p.nB, RetSeg p.L p.m μ (p.aENCA b0 + β * p.T)
    (Spec.arrT (encodingL (bandArrayL (Spec.stdLayout hmL) X β)))
  encB : ∀ β < p.nB, RetSeg p.L p.m μ (p.aENCB b0 + β * p.T)
    (Spec.arrT (encodingR (bandArrayR (Spec.stdLayout hmL) Y β)))

/-- The shape of the running time of the shared stage with pruned encodings. -/
def sharedShapeP (p : Par) : ℕ :=
  (p.L + 1) ^ 2 + (Nat.sqrt p.K + 1) + (p.KK + 1) * (p.L + 1) + (p.N + 1) * (p.Lo + 1)
    + (p.D + 1) * (p.m + 1)
    + p.nB * (retW p.L p.m + bandArrayShape p)

variable (lim : Limits) (P : Program) (c : ℕ) in
/-- sharedP(L, m, N, D, aX, aY, b0): fills the shared block, with pruned encodings. -/
def SharedSpecP : Prop :=
  ∀ (p : Par) (hmL : p.m ≤ p.L) (aX aY b0 : ℕ) (μ : ℕ → ℤ)
    (X : Matrix (Fin p.N) (Fin (ThreeSumApsp.D p.m)) ℤ)
    (Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin p.N) ℤ) (V : ℤ),
    SharedPre lim p aX aY b0 X Y V μ →
    ∀ d, d + (p.L + 3) ≤ lim.depth →
    Meets lim P pSharedP d [p.L, p.m, p.N, p.D, aX, aY, b0] μ (c * sharedShapeP p) fun _ μ' =>
      SharedReadyP p hmL aX aY b0 X Y μ' ∧ SameOutside μ μ' b0 (p.sharedEnd b0 - b0)

/-! ## Basic facts -/

/-- A full segment is a pruned one. -/
theorem Seg.retSeg {L r : ℕ} {μ : ℕ → ℤ} {a : ℕ} {l : List ℤ} (h : Seg μ a l) :
    RetSeg L r μ a l := fun _ hi _ => h.getD hi 0

/-- With a budget of at least `L` nines nothing is pruned. -/
theorem ninesIdx_le (L i : ℕ) : ninesIdx L i ≤ L := by
  induction L generalizing i with
  | zero => simp [ninesIdx]
  | succ L ih =>
    have := ih (i % 10 ^ L)
    simp only [ninesIdx]
    split_ifs <;> omega

/-- `9^L ≤ retW L r`. -/
theorem nine_pow_le_retW (L r : ℕ) : 9 ^ L ≤ retW L r := by
  induction L generalizing r with
  | zero => simp [retW]
  | succ L ih =>
    cases r with
    | zero => simp only [retW, pow_succ]; have := ih 0; omega
    | succ r => simp only [retW, pow_succ]; have := ih (r + 1); omega

/-- `retW L r ≤ 10^L`. -/
theorem retW_le (L r : ℕ) : retW L r ≤ 10 ^ L := by
  induction L generalizing r with
  | zero => simp [retW]
  | succ L ih =>
    cases r with
    | zero => simp only [retW, pow_succ]; have := ih 0; omega
    | succ r => simp only [retW, pow_succ]; have := ih (r + 1); have := ih r; omega

end Light.Sec2
