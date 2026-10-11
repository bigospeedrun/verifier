/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Programs.Sec2.PrunedEnc.Recursion
public import Submission.ThreeSumApsp.Programs.Sec2.Theorem5.Encode.Contract

/-!
# The entries of the pruned encoder

What `encodeP` computes, in the paper's terms: at the positions with at most r nines the output
holds the encoding of the array (`encodeP_str`), as for `encode` (`encode_str`).  The places that
the callers provide are a layout for it (`EncodePlaces.layout`), so the entries `EncodePLSpec` and
`EncodePRSpec` hold for every program that has encStep and encodeP at their numbers
(`encodePL_entry`, `encodePR_entry`), within `cEncodeP · retW n r` steps (`encPTime_le`).
-/

public section

open ThreeSumApsp

namespace Light.Sec2

open Finset ThreeSumApsp.Spec

/-! ## From positions to strings -/

section
variable {α : Type} [Fintype α] (e : α ≃ Fin 7) (coef : Term → α → ℤ)

/-- The recursion on positions computes the procedure of Section 2.4.1, if the array and the table
of coefficients are stored by digits (a copy of the lemma behind `encode_str`). -/
private theorem encIdx_eq_computeEncoding' {c : ℕ → ℤ}
    (hc : ∀ lam s, c (7 * (termIdx lam : ℕ) + (e s : ℕ)) = coef lam s) (L : ℕ)
    (A : (Fin L → α) → ℤ) {arr : ℕ → ℤ}
    (harr : ∀ j < 7 ^ L, arr j = A (decodeStr e L j)) {i : ℕ} (hi : i < 10 ^ L) :
    encIdx c L arr i = computeEncoding coef L A (decodeT L i) := by
  induction L generalizing arr i with
  | zero =>
    rw [encIdx, computeEncoding, harr 0 (by norm_num)]
    exact congrArg A (Subsingleton.elim _ _)
  | succ L ih =>
    -- The first digit of i is the digit of a term λ, and the rest of i is the code of a leaf below.
    have hpos : 0 < 10 ^ L := by positivity
    have hdigit : i / 10 ^ L < 10 := by rwa [Nat.div_lt_iff_lt_mul hpos, ← pow_succ']
    have hrest : i % 10 ^ L < 10 ^ L := Nat.mod_lt _ hpos
    obtain ⟨lam, hidx⟩ : ∃ lam : Term, ((termEquiv lam : Fin 10) : ℕ) = i / 10 ^ L :=
      ⟨termOfNat _, termIdx_termOfNat hdigit⟩
    have hleaf : decodeT (L + 1) i = Fin.cons lam (decodeT L (i % 10 ^ L)) := by
      have hcons := decodeStr_cons termEquiv lam hrest
      rwa [hidx, Nat.div_add_mod'] at hcons
    rw [encIdx, hleaf, computeEncoding, Fin.cons_zero, Fin.tail_cons]
    unfold encSlice
    -- Step (2) of the procedure: the sum over the digits is the sum over the variables.
    refine ih _ (fun j hj => ?_) hrest
    rw [← Fin.sum_univ_eq_sum_range (fun s => c (7 * (i / 10 ^ L) + s) * arr (s * 7 ^ L + j)) 7,
      ← e.sum_comp fun s : Fin 7 => c (7 * (i / 10 ^ L) + (s : ℕ)) * arr ((s : ℕ) * 7 ^ L + j)]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [sliceAt, ← hidx, show ((termEquiv lam : Fin 10) : ℕ) = termIdx lam from rfl, hc,
      harr _ (by rw [pow_succ']; exact Nat.mul_add_lt_mul (e s).isLt hj), decodeStr_cons e s hj]

end

/-! ## The specification of encodeP, on lists -/

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ} {src out scr tab p7 p10 L r : ℕ} {V : ℤ}

/-- The hypotheses of encode hold if the source, the table of coefficients and the two tables of
powers are in their places and the numbers obey the bounds. -/
private theorem EncodePre.of_seg' {l T : List ℤ} (lay : EncodeLayout lim src out scr tab p7 p10 L)
    (hl : l.length = 7 ^ L) (hsrc : Seg μ src l) (hV : ∀ x ∈ l, -V ≤ x ∧ x ≤ V)
    (hT : T.length = 70) (htab : Seg μ tab T) (hc : ∀ x ∈ T, -1 ≤ x ∧ x ≤ 1)
    (h7 : ∀ i < L, μ (p7 + i) = ((7 ^ i : ℕ) : ℤ)) (h10 : ∀ i < L, μ (p10 + i) = ((10 ^ i : ℕ) : ℤ))
    (hVB : ((7 ^ L : ℕ) : ℤ) * V ≤ lim.word) :
    EncodePre lim μ src out scr tab p7 p10 V L (fun j => l.getD j 0) (fun i => T.getD i 0) :=
  { lay := lay
    srcV := fun j hj => hsrc.getD (by omega) 0
    src_bound := fun j hj => by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact hV _ (List.getElem_mem _)
    tabV := fun i hi => htab.getD (by omega) 0
    coef_bound := fun i hi => by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact hc _ (List.getElem_mem _)
    p7V := h7, p10V := h10, word_bound := hVB }

/-- **The pruned encoding of an array on strings**, for both alphabets at once.  If the source holds
the array A on the strings of length L, the table holds the coefficients, the tables of powers are
in their places and the numbers obey the bounds, then encodeP ends within `cEncodeP · retW L r`
steps, the output holds what the procedure of Section 2.4.1 computes at the positions with at most
r nines, and only the output and the scratch area have changed. -/
theorem encodeP_str {α : Type} [Fintype α] (e : α ≃ Fin 7) (coef : Term → α → ℤ) {T : List ℤ}
    (hT : T.length = 70) (hc : ∀ x ∈ T, -1 ≤ x ∧ x ≤ 1)
    (hcoef : ∀ lam s, T.getD (7 * (termIdx lam : ℕ) + (e s : ℕ)) 0 = coef lam s) {pS pE : ℕ}
    (hS : P[pS]? = some encStepBody) (hE : P[pE]? = some (encodePBody pS pE))
    (lay : EncodeLayout lim src out scr tab p7 p10 L) (A : (Fin L → α) → ℤ)
    (hsrc : Seg μ src (arrStr e A)) (hV : ∀ u, |A u| ≤ V) (htab : Seg μ tab T)
    (h7 : ∀ i < L, μ (p7 + i) = ((7 ^ i : ℕ) : ℤ)) (h10 : ∀ i < L, μ (p10 + i) = ((10 ^ i : ℕ) : ℤ))
    (hVB : ((7 ^ L : ℕ) : ℤ) * V ≤ lim.word) (hd : d + L ≤ lim.depth) :
    Ends lim P d (encodePBody pS pE) ⟨frame [L, src, out, scr, tab, p7, p10, r], μ⟩
      (cEncodeP * retW L r) fun σ' => RetSeg L r σ'.mem out (arrT (computeEncoding coef L A)) ∧
        SameOutside2 μ σ'.mem out (10 ^ L) scr (scrSize L) := by
  have hbound : ∀ x ∈ arrStr e A, -V ≤ x ∧ x ≤ V := fun x hx => by
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
    exact abs_le.1 (hV _)
  have pre := EncodePre.of_seg' lay (length_arrStr e A) hsrc hbound hT htab hc h7 h10 hVB
  refine (encodeP_spec hS hE hd pre).mono (by have := encPTime_le L r; omega)
    fun σ' h => ⟨?_, h.2⟩
  intro i hi hn
  rw [length_arrT] at hi
  rw [h.1 i hi hn,
    encIdx_eq_computeEncoding' e coef hcoef L A (fun j hj => getD_arrStr_of_lt e A hj) hi,
    arrT, getD_arrStr_of_lt termEquiv _ hi]
  rfl

/-! ## The entries -/

variable {n Lmax dst : ℕ}

/-- The scratch area of encode has fewer than 7^L cells. -/
private theorem scrSize_le' (L : ℕ) : scrSize L + 1 ≤ 7 ^ L := by
  induction L with
  | zero => simp [scrSize]
  | succ L ih =>
    rw [scrSize, pow_succ]
    omega

/-- A cell of a table of powers. -/
private theorem pow_of_seg' {p b : ℕ} (h : Seg μ p (powList b (Lmax + 1))) (hn : n ≤ Lmax) :
    ∀ i < n, μ (p + i) = ((b ^ i : ℕ) : ℤ) := fun i hi => by
  rw [h.get (i := i) (by simp; omega), getElem_powList]

/-- **The specification that the callers of encodeP assume**, for any alphabet of seven
variables. -/
theorem encodeP_entry {α : Type} [Fintype α] (e : α ≃ Fin 7) (coef : Term → α → ℤ)
    {T : List ℤ} (hT : T.length = 70) (hc : ∀ x ∈ T, -1 ≤ x ∧ x ≤ 1)
    (hcoef : ∀ lam s, T.getD (7 * (termIdx lam : ℕ) + (e s : ℕ)) 0 = coef lam s) (std : Std lim)
    (hS : P[pEncStep]? = some encStepBody)
    (hE : P[pEncodeP]? = some (encodePBody pEncStep pEncodeP))
    {d : ℕ} (hd : d + (n + 1) ≤ lim.depth) (hpl : EncodePlaces lim n Lmax src dst scr tab p7 p10 μ)
    (htab : Seg μ tab T) (A : (Fin n → α) → ℤ) (hsrc : Seg μ src (arrStr e A)) {V : ℤ}
    (hV : ∀ u, |A u| ≤ V) (hVB : 7 ^ (n + 1) * V ≤ lim.word) (r : ℕ) :
    Meets lim P pEncodeP d [n, src, dst, scr, tab, p7, p10, r] μ (cEncodeP * retW n r)
      fun _ μ' => RetSeg n r μ' dst (arrT (computeEncoding coef n A)) ∧
        SameOutside2 μ μ' dst (10 ^ n) scr (7 ^ n) := by
  have hV0 : 0 ≤ V := (abs_nonneg _).trans (hV fun _ => e.symm 0)
  have hVB' : ((7 ^ n : ℕ) : ℤ) * V ≤ lim.word := by
    refine le_trans ?_ hVB
    push_cast
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (Nat.le_succ n)) hV0
  have hscr := scrSize_le' n
  refine .of_body hE ((encodeP_str e coef hT hc hcoef hS hE (hpl.layout std) A hsrc hV htab
    (pow_of_seg' hpl.hp7 hpl.n_le) (pow_of_seg' hpl.hp10 hpl.n_le) hVB' (by omega)).mono le_rfl
    fun σ' h => ⟨h.1, h.2.mono fun x hx => by omega⟩)

/-- **The pruned encoder, for the array a.** -/
theorem encodePL_entry (std : Std lim) (hS : P[pEncStep]? = some encStepBody)
    (hE : P[pEncodeP]? = some (encodePBody pEncStep pEncodeP)) : EncodePLSpec lim P cEncodeP := by
  intro n Lmax src dst scr tab p7 p10 r μ a V hpl htab hsrc hV hVB d hd
  exact computeEncoding_phi a ▸ encodeP_entry leftEquiv phi (by decide) (by decide) phiFlat_spec
    std hS hE hd hpl htab a hsrc hV hVB r

/-- **The pruned encoder, for the array b.** -/
theorem encodePR_entry (std : Std lim) (hS : P[pEncStep]? = some encStepBody)
    (hE : P[pEncodeP]? = some (encodePBody pEncStep pEncodeP)) : EncodePRSpec lim P cEncodeP := by
  intro n Lmax src dst scr tab p7 p10 r μ b V hpl htab hsrc hV hVB d hd
  exact computeEncoding_psi b ▸ encodeP_entry rightEquiv psi (by decide) (by decide) psiFlat_spec
    std hS hE hd hpl htab b hsrc hV hVB r

end Light.Sec2
