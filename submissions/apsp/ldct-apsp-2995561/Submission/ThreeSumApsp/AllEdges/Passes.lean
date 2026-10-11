/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Lang.Lib.Pass
public import Submission.ThreeSumApsp.Lang.Tactics
public import Submission.ThreeSumApsp.Lang.Frames
public import Submission.ThreeSumApsp.Util.Flag
public import Submission.ThreeSumApsp.Programs.Sec3.Theorem21b.NegativeTriangle.Passes

/-!
# Two loops over arrays for all pairs from all-edges Exact Triangle

transpose(n, src, dst) writes the transposed `n × n` matrix to dst, one row at a time
(`transpose_meets`).  or(len, dst, src) sets dst[i] to the "or" of two flags (`or_meets`).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## A row of the transposed matrix -/

/-- row(n, s, dst): for i < n, dst[i] := mem[s + i n]. -/
def rowBody : Stmt := pass 3 (v 0) (v 2) (M (v 1 +' v 3 *' v 0))

/-- The row `j` of the transposed matrix: the column `j` of `L`. -/
def colOf (n : ℕ) (L : List ℤ) (j : ℕ) : List ℤ := (List.range n).map fun i => L.getD (i * n + j) 0

/-- **row** writes the column `j` of the matrix at src to dst. -/
theorem row_meets {p : ℕ} (hp : P[p]? = some rowBody) {μ : ℕ → ℤ} {src dst n j : ℕ}
    {L : List ℤ} (hL : Seg μ src L) (hlen : L.length = n * n) (hj : j < n)
    (hw : (lim.space : ℤ) ≤ lim.word) (hsrc : src + n * n ≤ lim.space)
    (hdst : dst + n ≤ lim.space) (hsep : src + n * n ≤ dst ∨ dst + n ≤ src) :
    Meets lim P p d [(n : ℤ), ((src + j : ℕ) : ℤ), (dst : ℤ)] μ (20 * n + 6) fun _ μ' =>
      Seg μ' dst (colOf n L j) ∧ SameOutside μ μ' dst n := by
  refine .of_body hp ?_
  simp only [rowBody]
  refine Ends.pass (fun i => L.getD (i * n + j) 0) (fun i hi => ?_) ?_ hw hdst rfl rfl
    (hT := by simp [Expr.cost]; omega)
  · have hij : i * n + j < n * n := by nlinarith
    have hread : wrote μ dst (fun i => L.getD (i * n + j) 0) i (src + (i * n + j)) =
        L.getD (i * n + j) 0 := by
      rw [wrote_rest (by unfold Outside; omega), hL _ (by omega),
        List.getD_eq_getElem _ _ (by omega)]
    obtain ⟨hA, hAbs⟩ := Limits.addr_of_lt hw (x := src + (i * n + j)) (by omega)
    have hprod : (i * n : ℕ) < lim.space := by omega
    obtain ⟨-, hpfits⟩ := Limits.addr_of_lt hw hprod
    push_cast at hA hAbs hpfits
    have h1 : frame [(n : ℤ), ((src + j : ℕ) : ℤ), (dst : ℤ)] 1 = ((src + j : ℕ) : ℤ) := rfl
    have h0 : frame [(n : ℤ), ((src + j : ℕ) : ℤ), (dst : ℤ)] 0 = n := rfl
    have haddr' : ((src + j : ℕ) : ℤ) + (i : ℤ) * n = ((src + (i * n + j) : ℕ) : ℤ) := by
      push_cast; ring
    simp only [Expr.Safe, Expr.val, Op.eval, Function.update_self,
      Function.update_of_ne (show (1 : ℕ) ≠ 3 by decide),
      Function.update_of_ne (show (0 : ℕ) ≠ 3 by decide), h0, h1, haddr']
    refine ⟨⟨?_, by push_cast; exact hA⟩, ?_⟩
    · simp only [true_and]
      push_cast
      exact ⟨hpfits, hAbs⟩
    · rw [Int.toNat_natCast, hread]
  · dsimp only
    exact ⟨seg_wrote (by simp [colOf]) fun i hi => by simp [colOf], sameOutside_wrote le_rfl⟩

/-! ## The transposed matrix -/

/-- transpose(n, src, dst): for j < n, row(n, src + j, dst + j n). -/
def transBody (pRow : ℕ) : Stmt := .for 3 (v 0) (.call pRow [v 0, v 1 +' v 3, v 2 +' v 3 *' v 0] 4)

/-- The transposed matrix. -/
def transL (n : ℕ) (L : List ℤ) : List ℤ :=
  (List.range (n * n)).map fun q => L.getD (q % n * n + q / n) 0

/-- The time of transpose. -/
def tTranspose (n : ℕ) : ℕ := 20 * (n * n) + 25 * n + 6

/-- **transpose** writes the transposed matrix of the matrix at src to dst. -/
theorem transpose_meets {p pRow : ℕ} (hp : P[p]? = some (transBody pRow))
    (hrow : P[pRow]? = some rowBody) {μ : ℕ → ℤ} {src dst n : ℕ}
    {L : List ℤ} (hL : Seg μ src L) (hlen : L.length = n * n)
    (hw : (lim.space : ℤ) ≤ lim.word) (hsrc : src + n * n ≤ lim.space)
    (hdst : dst + n * n ≤ lim.space) (hsep : src + n * n ≤ dst ∨ dst + n * n ≤ src)
    (hd : d < lim.depth) :
    Meets lim P p d [(n : ℤ), (src : ℤ), (dst : ℤ)] μ (tTranspose n) fun _ μ' =>
      Seg μ' dst (transL n L) ∧ SameOutside μ μ' dst (n * n) := by
  refine .of_body hp ?_
  have hn2 : n ≤ n * n ∨ n = 0 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exact .inr h
    · exact .inl (Nat.le_mul_of_pos_left n h)
  have hnw : (n : ℤ) ≤ lim.word := by
    have : (n : ℤ) ≤ lim.space := by exact_mod_cast (show n ≤ lim.space by rcases hn2 with h | h <;> omega)
    omega
  refine Ends.forShape (fun j s μ' => ⟨frame [(n : ℤ), (src : ℤ), (dst : ℤ), (j : ℤ), s], μ'⟩)
    (fun j μ' => (∀ j' < j, Seg μ' (dst + j' * n) (colOf n L j')) ∧
      SameOutside μ μ' dst (n * n)) n (20 * n + 17) (0 : ℤ)
    ⟨fun j' hj' => absurd hj' (Nat.not_lt_zero _), SameOn.refl⟩ ?round ?done
    (first := by
      rw [update_frame_setLocal]
      exact congrArg (State.mk · μ) (frame_append_zeros _ 1).symm)
    (hT := by simp [Expr.cost, tTranspose]; ring_nf; omega)
  case round =>
    rintro j s μ' hj ⟨hrows, hout⟩
    have hjn : j * n + n ≤ n * n := by nlinarith
    have hL' : Seg μ' src L := hL.keep (SameOn.mono hout fun b hb => by
      simp only [Inside, Outside] at hb ⊢; omega)
    have hm := row_meets (d := d + 1) hrow hL' hlen hj hw hsrc (dst := dst + j * n)
      (by omega) (by omega)
    refine Ends.callTo hm (fun r μ'' ⟨hseg, hsame⟩ => ⟨r, μ'', ?_, ?_, ?_⟩)
      (ha := ?_) (hT := by simp [Expr.cost]; omega)
    · simp
    · intro j' hj'
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hlt | rfl
      · refine (hrows j' hlt).keep (SameOn.mono hsame fun b hb => ?_)
        have : j' * n + n ≤ j * n := by nlinarith
        unfold Outside at hb ⊢
        simp [colOf] at hb
        omega
      · exact hseg
    · exact hout.trans (SameOn.mono hsame fun b hb => by unfold Outside at hb ⊢; omega)
    · have hjw : ((j * n : ℕ) : ℤ) ≤ lim.space := by exact_mod_cast (show j * n ≤ lim.space by omega)
      have hsw : ((src + j : ℕ) : ℤ) ≤ lim.space := by
        exact_mod_cast (show src + j ≤ lim.space by nlinarith)
      have hdw : ((dst + j * n : ℕ) : ℤ) ≤ lim.space := by
        exact_mod_cast (show dst + j * n ≤ lim.space by omega)
      push_cast at hjw hsw hdw
      refine ⟨?_, ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        simp [Expr.Safe, Expr.val, Op.eval, abs_le]
        have h0 : (0 : ℤ) ≤ (j : ℤ) * n := by positivity
        have h1 : (0 : ℤ) ≤ lim.space := by positivity
        refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith, by linarith⟩
      · simp [Expr.val, Op.eval]
  case done =>
    rintro s μ' ⟨hrows, hout⟩
    refine ⟨fun q hq => ?_, hout⟩
    simp only [transL, List.length_map, List.length_range] at hq
    have hnpos : 0 < n := by rcases Nat.eq_zero_or_pos n with h | h <;> simp_all
    have hqn : q / n < n := Nat.div_lt_of_lt_mul hq
    have hrow := hrows (q / n) hqn (q % n) (by simp [colOf]; exact Nat.mod_lt _ hnpos)
    rw [show dst + q / n * n + q % n = dst + q by
      have := Nat.div_add_mod' q n; omega] at hrow
    simp [hrow, colOf, transL]

/-! ## Or of flags -/

/-- The flags of a predicate on the numbers below `N`. -/
noncomputable def flagsOf (N : ℕ) (A : ℕ → Prop) : List ℤ := (List.range N).map fun q => flag (A q)

@[simp] theorem length_flagsOf (N : ℕ) (A : ℕ → Prop) : (flagsOf N A).length = N := by
  simp [flagsOf]

/-- or(len, dst, src): for i < len, dst[i] := dst[i] + src[i] - dst[i] src[i]. -/
def orBody : Stmt :=
  pass 3 (v 0) (v 1) (M (v 1 +' v 3) +' M (v 2 +' v 3) -' M (v 1 +' v 3) *' M (v 2 +' v 3))

theorem flag_or_eq (A B : Prop) : flag A + flag B - flag A * flag B = flag (A ∨ B) := by
  by_cases hA : A <;> by_cases hB : B <;> simp [flag_of, flag_of_not, hA, hB]

/-- **or** sets each flag at dst to the "or" of it and the flag at src. -/
theorem or_meets {p : ℕ} (hp : P[p]? = some orBody) {μ : ℕ → ℤ} {src dst N : ℕ}
    {A B : ℕ → Prop} (hA : Seg μ dst (flagsOf N A)) (hB : Seg μ src (flagsOf N B))
    (hw : (lim.space : ℤ) ≤ lim.word) (hw2 : (2 : ℤ) ≤ lim.word)
    (hsrc : src + N ≤ lim.space) (hdst : dst + N ≤ lim.space)
    (hsep : src + N ≤ dst ∨ dst + N ≤ src) :
    Meets lim P p d [(N : ℤ), (dst : ℤ), (src : ℤ)] μ (32 * N + 6) fun _ μ' =>
      Seg μ' dst (flagsOf N fun q => A q ∨ B q) ∧ SameOutside μ μ' dst N := by
  refine .of_body hp ?_
  simp only [orBody]
  refine Ends.pass (fun i => flag (A i ∨ B i)) (fun i hi => ?_) ?_ hw hdst rfl rfl
    (hT := by simp [Expr.cost]; omega)
  · have ha : wrote μ dst (fun i => flag (A i ∨ B i)) i (dst + i) = flag (A i) := by
      rw [wrote_rest (by unfold Outside; omega), hA i (by simp [flagsOf]; omega)]
      simp [flagsOf]
    have hb : wrote μ dst (fun i => flag (A i ∨ B i)) i (src + i) = flag (B i) := by
      rw [wrote_rest (by unfold Outside; omega), hB i (by simp [flagsOf]; omega)]
      simp [flagsOf]
    obtain ⟨hAd, hBd⟩ := Limits.addr_of_lt hw (x := dst + i) (by omega)
    obtain ⟨hAs, hBs⟩ := Limits.addr_of_lt hw (x := src + i) (by omega)
    push_cast at hAd hAs hBd hBs
    have e1 : frame [(N : ℤ), (dst : ℤ), (src : ℤ)] 1 = dst := rfl
    have e2 : frame [(N : ℤ), (dst : ℤ), (src : ℤ)] 2 = src := rfl
    obtain ⟨hfa, hfa'⟩ := flag_mem (A i)
    obtain ⟨hfb, hfb'⟩ := flag_mem (B i)
    simp only [Expr.Safe, Expr.val, Op.eval, Function.update_self,
      Function.update_of_ne (show (1 : ℕ) ≠ 3 by decide),
      Function.update_of_ne (show (2 : ℕ) ≠ 3 by decide), e1, e2,
      show ((dst : ℤ) + (i : ℤ)).toNat = dst + i by omega,
      show ((src : ℤ) + (i : ℤ)).toNat = src + i by omega, ha, hb, flag_or_eq, true_and,
      and_true]
    have hab : 0 ≤ flag (A i) * flag (B i) := mul_nonneg hfa hfb
    have hab' : flag (A i) * flag (B i) ≤ 1 := by nlinarith
    obtain ⟨hfo, hfo'⟩ := flag_mem (A i ∨ B i)
    refine ⟨⟨⟨hBd, hAd⟩, ⟨hBs, hAs⟩, ?_⟩, ⟨⟨hBd, hAd⟩, ⟨hBs, hAs⟩, ?_⟩, ?_⟩ <;>
      (rw [abs_le]; constructor <;> linarith)
  · dsimp only
    refine ⟨seg_wrote (by simp [flagsOf]) fun i hi => by simp [flagsOf], sameOutside_wrote le_rfl⟩

end Light.Sec3
