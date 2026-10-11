/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Programs.Sec3.Theorem17.Witnesses.ScanPairs

/-!
# All-edges Exact Triangle: reading the answers of one instance and marking pairs

The all-edges form of the scans of Theorem 17.  The host keeps an array of `n²` marks, one for each
pair `(a, b)`; the mark of `(a, b)` is set once a zero triangle through `(a, b)` has been found.

scanPairsAE(out, qa, qb, w, fl, ab, bc, ac, n, c0, len): for every query pair number `i < w` whose
answer `out[i]` is not 0 and whose pair `(qa[i], qb[i])` is not marked yet, scan the piece
`{c0, …, c0 + len - 1}` for a zero triangle through the pair, and store the result as its mark.

A scan that succeeds sets a mark that was not set before, so over the whole run there are at most
`n²` successful scans; a scan that fails is an accepted pair whose scan fails, as in Theorem 17.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The pure side -/

/-- The marks after the first `i` query pairs, starting from the marks `g`: the place `pl j` of an
accepted query pair whose scan succeeds is marked. -/
def marksUpto (acc hit : ℕ → Bool) (pl : ℕ → ℕ) (g : ℕ → Bool) (i : ℕ) : ℕ → Bool :=
  fun q => g q || (List.range i).any fun j => acc j && hit j && decide (pl j = q)

/-- Whether the query pair number `i` is scanned: it is accepted and its place is not marked. -/
def aeExecAt (acc hit : ℕ → Bool) (pl : ℕ → ℕ) (g : ℕ → Bool) (i : ℕ) : Bool :=
  acc i && !marksUpto acc hit pl g i (pl i)

/-- The number of scans among the first `w` query pairs. -/
def aeExecsUpto (acc hit : ℕ → Bool) (pl : ℕ → ℕ) (g : ℕ → Bool) (w : ℕ) : ℕ :=
  ((List.range w).filter (aeExecAt acc hit pl g)).length

theorem marksUpto_zero (acc hit : ℕ → Bool) (pl : ℕ → ℕ) (g : ℕ → Bool) :
    marksUpto acc hit pl g 0 = g := by
  funext q
  simp [marksUpto]

theorem marksUpto_succ (acc hit : ℕ → Bool) (pl : ℕ → ℕ) (g : ℕ → Bool) (i q : ℕ) :
    marksUpto acc hit pl g (i + 1) q =
      (marksUpto acc hit pl g i q || (acc i && hit i && decide (pl i = q))) := by
  simp [marksUpto, List.range_succ, Bool.or_assoc]

theorem aeExecsUpto_succ (acc hit : ℕ → Bool) (pl : ℕ → ℕ) (g : ℕ → Bool) (w : ℕ) :
    aeExecsUpto acc hit pl g (w + 1) =
      aeExecsUpto acc hit pl g w + (if aeExecAt acc hit pl g w then 1 else 0) := by
  simp only [aeExecsUpto, List.range_succ, List.filter_append, List.length_append, List.filter_cons,
    List.filter_nil]
  split_ifs <;> rfl

/-- Marks are never removed. -/
theorem marksUpto_mono (acc hit : ℕ → Bool) (pl : ℕ → ℕ) (g : ℕ → Bool) (i q : ℕ)
    (h : g q = true) : marksUpto acc hit pl g i q = true := by
  simp [marksUpto, h]

/-- The number of marked places among the first `N`. -/
def markCount (N : ℕ) (g : ℕ → Bool) : ℕ := ((List.range N).filter g).length

theorem markCount_le (N : ℕ) (g : ℕ → Bool) : markCount N g ≤ N := by
  unfold markCount
  exact (List.length_filter_le _ _).trans (by simp)

/-- Setting a mark at a place `q < N` that was not marked adds one to the count. -/
theorem markCount_set {N q : ℕ} (hq : q < N) (g : ℕ → Bool) (hg : g q = false) :
    markCount N (fun r => g r || decide (q = r)) = markCount N g + 1 := by
  unfold markCount
  induction N with
  | zero => omega
  | succ N ih =>
    simp only [List.range_succ, List.filter_append, List.length_append, List.filter_cons,
      List.filter_nil]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hq with hlt | rfl
    · rw [ih hlt]
      have hne : ¬ q = N := by omega
      by_cases hgN : g N = true <;> simp [hgN, hne]
    · have hnot : ∀ r ∈ List.range q, (g r || decide (q = r)) = g r := by
        intro r hr
        have : ¬ q = r := by have := List.mem_range.1 hr; omega
        simp [this]
      rw [List.filter_congr hnot]
      simp [hg]

/-- **Scans are failures or new marks**: the number of scans among the first `w` query pairs, plus
the marks among the first `N` places before them, is at most the number of failed scans plus the
marks after them.  Places of the query pairs are below `N`. -/
theorem aeExecsUpto_le (acc hit : ℕ → Bool) (pl : ℕ → ℕ) (g : ℕ → Bool) (N w : ℕ)
    (hpl : ∀ i < w, pl i < N) :
    aeExecsUpto acc hit pl g w + markCount N g
      ≤ failsUpto acc hit w + markCount N (marksUpto acc hit pl g w) := by
  induction w with
  | zero => simp [aeExecsUpto, failsUpto, marksUpto_zero]
  | succ w ih =>
    have ih := ih fun i hi => hpl i (by omega)
    rw [aeExecsUpto_succ, failsUpto_succ]
    have hfun : marksUpto acc hit pl g (w + 1) =
        fun q => marksUpto acc hit pl g w q || (acc w && hit w && decide (pl w = q)) := by
      funext q
      exact marksUpto_succ acc hit pl g w q
    rw [hfun]
    unfold aeExecAt
    set G := marksUpto acc hit pl g w
    have hpw := hpl w (by omega)
    by_cases hb : (acc w && hit w) = true
    · have ha : acc w = true := by simp_all
      have hh : hit w = true := by simp_all
      by_cases hm : G (pl w) = true
      · have hsame : (fun q => G q || (acc w && hit w && decide (pl w = q))) = G := by
          funext q
          by_cases hq : pl w = q
          · subst hq; simp [hm]
          · simp [hq]
        rw [hsame]
        simp [ha, hh, hm]
        omega
      · have hm' : G (pl w) = false := by simpa using hm
        have hset := markCount_set hpw G hm'
        have hfun' : (fun q => G q || (acc w && hit w && decide (pl w = q))) =
            fun r => G r || decide (pl w = r) := by
          funext q; simp [ha, hh]
        rw [hfun', hset]
        simp [ha, hh, hm']
        omega
    · have hsame : (fun q => G q || (acc w && hit w && decide (pl w = q))) = G := by
        funext q
        simp only [Bool.not_eq_true] at hb
        simp [hb]
      rw [hsame]
      rcases ha : acc w <;> rcases hh : hit w <;> simp_all <;> split_ifs <;> omega

/-! ## The marks in the memory -/

/-- The memory `μ` with the `N` cells from `fl` holding the marks `g`. -/
def withMarks (μ : ℕ → ℤ) (fl N : ℕ) (g : ℕ → Bool) : ℕ → ℤ :=
  fun a => if fl ≤ a ∧ a < fl + N then bit (g (a - fl)) else μ a

theorem withMarks_out {μ : ℕ → ℤ} {fl N a : ℕ} (g : ℕ → Bool) (h : a < fl ∨ fl + N ≤ a) :
    withMarks μ fl N g a = μ a := by
  unfold withMarks
  rw [if_neg (by omega)]

theorem withMarks_in {μ : ℕ → ℤ} {fl N q : ℕ} (g : ℕ → Bool) (h : q < N) :
    withMarks μ fl N g (fl + q) = bit (g q) := by
  unfold withMarks
  rw [if_pos (by omega), Nat.add_sub_cancel_left]

/-- Writing the mark of a place. -/
theorem update_withMarks {μ : ℕ → ℤ} {fl N q : ℕ} (g : ℕ → Bool) (hq : q < N) (b : Bool) :
    Function.update (withMarks μ fl N g) (fl + q) (bit b) =
      withMarks μ fl N (fun r => if r = q then b else g r) := by
  funext a
  by_cases ha : a = fl + q
  · subst ha
    rw [Function.update_self, withMarks_in _ hq, if_pos rfl]
  · rw [Function.update_of_ne ha]
    unfold withMarks
    split_ifs with h
    · dsimp only; rw [if_neg (by omega)]
    · rfl

theorem bit_eq_zero_iff (b : Bool) : bit b = 0 ↔ b = false := by
  cases b <;> simp [bit]

/-! ## The routine -/

namespace ScanPairsAE

/-- The locals of `scanPairsAE`.  The arguments: the addresses of the answers and of the rows and
the columns of the query pairs, their number `w`, the address of the marks, the addresses of the
three arrays of weights, `n`, and the first vertex and the number of vertices of the piece.  Then
the counter, the place of the pair, and the result of a scan. -/
abbrev Out : ℕ := 0
@[inherit_doc Out] abbrev Rows : ℕ := 1
@[inherit_doc Out] abbrev Cols : ℕ := 2
@[inherit_doc Out] abbrev Num : ℕ := 3
@[inherit_doc Out] abbrev Fl : ℕ := 4
@[inherit_doc Out] abbrev AdrAB : ℕ := 5
@[inherit_doc Out] abbrev AdrBC : ℕ := 6
@[inherit_doc Out] abbrev AdrAC : ℕ := 7
@[inherit_doc Out] abbrev Size : ℕ := 8
@[inherit_doc Out] abbrev First : ℕ := 9
@[inherit_doc Out] abbrev Len : ℕ := 10
@[inherit_doc Out] abbrev Cnt : ℕ := 11
@[inherit_doc Out] abbrev Pl : ℕ := 12
@[inherit_doc Out] abbrev Res : ℕ := 13

end ScanPairsAE

open ScanPairsAE in
/-- One query pair: if out[i] ≠ 0 then pl := qa[i] n + qb[i]; if fl[pl] = 0 then
fl[pl] := scan(ab, bc, ac, n, qa[i], qb[i], c0, len). -/
def scanPairsAEStep (pScan : ℕ) : Stmt :=
  .ite (M (v Out +' v Cnt) =' k 0) .skip
    (.set Pl (M (v Rows +' v Cnt) *' v Size +' M (v Cols +' v Cnt)) ;;
      .ite (M (v Fl +' v Pl) =' k 0)
        (.call pScan [v AdrAB, v AdrBC, v AdrAC, v Size, M (v Rows +' v Cnt), M (v Cols +' v Cnt),
          v First, v Len] Res ;;
          .store (v Fl +' v Pl) (v Res))
        .skip)

open ScanPairsAE in
/-- scanPairsAE(out, qa, qb, w, fl, ab, bc, ac, n, c0, len); the parameter is the procedure number
of `scan`. -/
def scanPairsAEBody (pScan : ℕ) : Stmt :=
  .set Cnt (k 0) ;;
  .while (v Cnt <' v Num) (scanPairsAEStep pScan ;; .set Cnt (v Cnt +' k 1)) ;;
  .set 0 (k 0)

/-- The time of one round, given whether a scan is made. -/
def tAERound (len : ℕ) (exec : Bool) : ℕ := 60 + if exec then tScanCall len + 20 else 0

/-- The time for reading w answers and marks. -/
def tAEAnswers (w : ℕ) : ℕ := 70 * w + 8

/-- The time of scanPairsAE, given the number of scans. -/
def tScanPairsAE (w len execs : ℕ) : ℕ := tAEAnswers w + (tScanCall len + 20) * execs

section

variable {pScan : ℕ} {μ : ℕ → ℤ} {out qa qb w fl ab bc ac n c0 len U : ℕ} {OUT AB BC AC : List ℤ}
  {QA QB : List ℕ} {g : ℕ → Bool}

/-- The place of the query pair number `i`. -/
abbrev plOf (n : ℕ) (QA QB : List ℕ) (i : ℕ) : ℕ := QA.getD i 0 * n + QB.getD i 0

/-- What `scanPairsAE` assumes about where the arrays lie: everything it reads lies outside the
marks, and the marks lie in the memory. -/
structure MarksApart (lim : Limits) (fl out qa qb w ab bc ac n : ℕ) : Prop where
  out : Apart out w fl (n * n)
  qa : Apart qa w fl (n * n)
  qb : Apart qb w fl (n * n)
  ab : Apart ab (n * n) fl (n * n)
  bc : Apart bc (n * n) fl (n * n)
  ac : Apart ac (n * n) fl (n * n)
  space : fl + n * n ≤ lim.space

/-- The state of `scanPairsAE` when `i` query pairs have been treated and the counter is `j`. -/
def scanPairsAEState (μ : ℕ → ℤ) (out qa qb w fl ab bc ac n c0 len : ℕ) (OUT AB BC AC : List ℤ)
    (QA QB : List ℕ) (g : ℕ → Bool) (i j : ℕ) (pl r : ℤ) : State :=
  ⟨frame [out, qa, qb, w, fl, ab, bc, ac, n, c0, len, j, pl, r],
    withMarks μ fl (n * n)
      (marksUpto (accOf OUT) (hitOf n AB BC AC QA QB c0 len) (plOf n QA QB) g i)⟩

/-- The weights stand in the memory with marks. -/
theorem Weights.marked (C : Weights lim μ ab bc ac n U AB BC AC)
    (H : MarksApart lim fl out qa qb w ab bc ac n) (h : ℕ → Bool) :
    Weights lim (withMarks μ fl (n * n) h) ab bc ac n U AB BC AC := by
  light_facts C C.arrAB C.arrBC C.arrAC H
  have sAB : Seg (withMarks μ fl (n * n) h) ab AB := fun i hi => by
    rw [withMarks_out _ (by omega)]; exact C.arrAB.seg i hi
  have sBC : Seg (withMarks μ fl (n * n) h) bc BC := fun i hi => by
    rw [withMarks_out _ (by omega)]; exact C.arrBC.seg i hi
  have sAC : Seg (withMarks μ fl (n * n) h) ac AC := fun i hi => by
    rw [withMarks_out _ (by omega)]; exact C.arrAC.seg i hi
  exact ⟨C.hw, C.hU, { C.arrAB with seg := sAB }, { C.arrBC with seg := sBC },
    { C.arrAC with seg := sAC }⟩

/-- One query pair: a scan is made if the pair is accepted and not marked; its result becomes the
mark. -/
theorem scanPairsAEStep_spec (hp : P[pScan]? = some scanBody)
    (C : Weights lim μ ab bc ac n U AB BC AC) (A : Answers lim μ out qa qb w n OUT QA QB)
    (H : MarksApart lim fl out qa qb w ab bc ac n) (hd : d < lim.depth) (hc : c0 + len ≤ n)
    {i : ℕ} (hi : i < w) (pl r : ℤ) :
    Ends lim P d (scanPairsAEStep pScan)
      (scanPairsAEState μ out qa qb w fl ab bc ac n c0 len OUT AB BC AC QA QB g i i pl r)
      (tAERound len (aeExecAt (accOf OUT) (hitOf n AB BC AC QA QB c0 len) (plOf n QA QB) g i))
      (fun σ => ∃ pl' r' : ℤ,
        σ = scanPairsAEState μ out qa qb w fl ab bc ac n c0 len OUT AB BC AC QA QB g (i + 1) i
          pl' r') := by
  light_facts C C.arrAB C.arrBC C.arrAC
  light_facts A A.arrOUT A.arrQA A.arrQB
  light_facts H
  have hreadOUT := A.arrOUT.read hi
  have hreadQA := A.arrQA.read hi
  have hreadQB := A.arrQB.read hi
  have ha := A.arrQA.getD_lt hi
  have hb := A.arrQB.getD_lt hi
  have hlenOUT := A.arrOUT.len
  have hlenQA := A.arrQA.len
  have hlenQB := A.arrQB.len
  set G := marksUpto (accOf OUT) (hitOf n AB BC AC QA QB c0 len) (plOf n QA QB) g i with hG
  have hsucc : ∀ q, marksUpto (accOf OUT) (hitOf n AB BC AC QA QB c0 len) (plOf n QA QB) g (i + 1) q
      = (G q || (accOf OUT i && hitOf n AB BC AC QA QB c0 len i && decide (plOf n QA QB i = q))) :=
    marksUpto_succ _ _ _ _ i
  -- the memory with marks reads the same outside the marks
  have rOUT : withMarks μ fl (n * n) G (out + i) = OUT.getD i 0 := by
    rw [withMarks_out _ (by omega)]; exact hreadOUT
  have rQA : withMarks μ fl (n * n) G (qa + i) = (QA.getD i 0 : ℤ) := by
    rw [withMarks_out _ (by omega)]; exact hreadQA
  have rQB : withMarks μ fl (n * n) G (qb + i) = (QB.getD i 0 : ℤ) := by
    rw [withMarks_out _ (by omega)]; exact hreadQB
  have hpl : plOf n QA QB i < n * n := Nat.mul_add_lt_mul ha hb
  have rFL : withMarks μ fl (n * n) G (fl + plOf n QA QB i) = bit (G (plOf n QA QB i)) :=
    withMarks_in _ hpl
  unfold scanPairsAEStep scanPairsAEState tAERound aeExecAt
  rw [← hG]
  generalize hacc : accOf OUT i = acc at hsucc
  have haccv : acc = decide (OUT.getD i 0 ≠ 0) := hacc.symm
  generalize hans : OUT.getD i 0 = answer at rOUT haccv
  have hqv : ((QA.getD i 0 : ℕ) : ℤ) * (n : ℤ) + ((QB.getD i 0 : ℕ) : ℤ) = ((plOf n QA QB i : ℕ) : ℤ) := by
    push_cast; ring
  have hplspace : fl + plOf n QA QB i < lim.space := by omega
  generalize hpq : plOf n QA QB i = q at rFL hpl hsucc hqv hplspace ⊢
  -- if out[i] = 0
  by_cases hz : answer = 0
  · subst haccv
    have hsame : marksUpto (accOf OUT) (hitOf n AB BC AC QA QB c0 len) (plOf n QA QB) g (i + 1)
        = G := by funext q'; rw [hsucc]; simp [hz]
    refine Ends.iteLast (fun _ => Ends.skip ⟨pl, r, ?_⟩) (fun h => absurd ?_ h) (by light_side [rOUT])
    · rw [hsame]
    · simp [rOUT, hz]
  refine Ends.iteLast (fun h => absurd h (by simp [rOUT, hz])) (fun _ => ?_) (by light_side [rOUT])
  have hacc1 : acc = true := by simp [haccv, hz]
  rw [hacc1]
  -- pl := qa[i] n + qb[i]
  have hqv2 : ((QA[i]?.getD 0 : ℕ) : ℤ) * (n : ℤ) + ((QB[i]?.getD 0 : ℕ) : ℤ) = q := by
    simpa [List.getD_eq_getElem?_getD] using hqv
  have hqn : (0 : ℤ) ≤ ((QA[i]?.getD 0 : ℕ) : ℤ) * (n : ℤ) := by positivity
  have hqn2 : ((QA[i]?.getD 0 : ℕ) : ℤ) * (n : ℤ) ≤ q := by omega
  refine Ends.setToThen (q : ℤ) ?_ (by light_side [rQA, rQB, hqv, hqv2, hqn, hqn2])
  -- if fl[pl] = 0
  by_cases hm : G q = true
  · have hsame : marksUpto (accOf OUT) (hitOf n AB BC AC QA QB c0 len) (plOf n QA QB) g (i + 1)
        = G := by
      funext q'
      rw [hsucc]
      by_cases hq : q = q'
      · subst hq; simp [hm]
      · simp [hq]
    refine Ends.iteLast (fun h => absurd h ?_) (fun _ => Ends.skip ⟨q, r, ?_⟩) (by light_side)
    · simp [rFL, hm, bit]
    · simp [hsame, setLocal]
  · have hm' : G q = false := by simpa using hm
    refine Ends.iteLast (fun _ => ?_) (fun h => absurd (by simp [rFL, hm', bit]) h)
      (by light_side [rFL])
    -- res := scan(ab, bc, ac, n, qa[i], qb[i], c0, len)
    refine Ends.callToThen (scan_meets hp (C.marked H G) ha hb hc) ?_
      (by light_side [rQA, rQB]) (by omega)
      (by simp [hm', tScanCall]; omega)
    rintro _ _ ⟨rfl, rfl⟩
    -- fl[pl] := res
    refine Ends.storeTo (fl + q) (flag (scanHit n AB BC AC (QA.getD i 0) (QB.getD i 0) c0 len = true))
      ⟨q, flag (scanHit n AB BC AC (QA.getD i 0) (QB.getD i 0) c0 len = true), ?_⟩
      (by light_side) (by simp [hm', tScanCall]; omega)
    rw [flag_eq_bit, update_withMarks _ hpl]
    congr 2
    funext q'
    rw [hsucc]
    by_cases hq : q' = q
    · subst hq; simp [hm', hitOf, hacc1]
    · simp [hq, Ne.symm hq]


/-- The time of the rounds, added up. -/
theorem sum_scanPairsAE_rounds (acc hit : ℕ → Bool) (pl : ℕ → ℕ) (g : ℕ → Bool) (c a X w : ℕ) :
    ∑ i ∈ Finset.range w, (c + (a + if aeExecAt acc hit pl g i then X else 0))
      = (c + a) * w + X * aeExecsUpto acc hit pl g w := by
  induction w with
  | zero => simp [aeExecsUpto]
  | succ w ih =>
    rw [Finset.sum_range_succ, ih, aeExecsUpto_succ]
    split_ifs <;> ring

/-- **scanPairsAE** sets the marks of the accepted query pairs whose scans succeed; no other cell
changes; the time depends on the number of scans that are made. -/
theorem scanPairsAE_spec (hp : P[pScan]? = some scanBody) (C : Weights lim μ ab bc ac n U AB BC AC)
    (A : Answers lim μ out qa qb w n OUT QA QB) (H : MarksApart lim fl out qa qb w ab bc ac n)
    (hd : d < lim.depth) (hc : c0 + len ≤ n) :
    Ends lim P d (scanPairsAEBody pScan)
      ⟨frame [out, qa, qb, w, fl, ab, bc, ac, n, c0, len], withMarks μ fl (n * n) g⟩
      (tScanPairsAE w len (aeExecsUpto (accOf OUT) (hitOf n AB BC AC QA QB c0 len) (plOf n QA QB) g w))
      fun σ' => σ'.mem = withMarks μ fl (n * n)
        (marksUpto (accOf OUT) (hitOf n AB BC AC QA QB c0 len) (plOf n QA QB) g w) := by
  light_facts C C.arrAB C.arrBC C.arrAC
  light_facts A A.arrOUT A.arrQA A.arrQB
  unfold tScanPairsAE tAEAnswers
  -- i := 0
  light_set (0 : ℕ)
  have hsum := sum_scanPairsAE_rounds (accOf OUT) (hitOf n AB BC AC QA QB c0 len) (plOf n QA QB) g
    4 64 (tScanCall len + 20) w
  -- while i < w
  refine Ends.next _ (Ends.while
    (fun i σ => ∃ pl r : ℤ,
      σ = scanPairsAEState μ out qa qb w fl ab bc ac n c0 len OUT AB BC AC QA QB g i i pl r) w
    (fun i => 64 + if aeExecAt (accOf OUT) (hitOf n AB BC AC QA QB c0 len) (plOf n QA QB) g i
      then tScanCall len + 20 else 0) ?start ?round ?done)
    (by simp only [Cond.cost, Expr.cost, Nat.reduceAdd]; omega)
  case start =>
    refine ⟨0, 0, ?_⟩
    simp only [scanPairsAEState, marksUpto_zero]
    congr 1
    rw [← frame_append_zeros _ 2]
    simp [setLocal]
  case round =>
    rintro i _ hi ⟨pl, r, rfl⟩
    refine ⟨by simp, by simp [scanPairsAEState]; omega, ?_⟩
    -- the query pair number i; then i := i + 1
    refine Ends.next _ ((scanPairsAEStep_spec hp C A H hd hc hi pl r).mono le_rfl ?_)
      (by simp only [tAERound]; split_ifs <;> omega)
    rintro _ ⟨pl', r', rfl⟩
    light_set (i + 1 : ℕ) using tAERound
    exact ⟨pl', r', by simp [scanPairsAEState]⟩
  case done =>
    rintro _ ⟨pl, r, rfl⟩
    exact ⟨by simp, by simp [scanPairsAEState],
      Ends.setTo (0 : ℤ) rfl (by simp; omega) (by simp only [Cond.cost, Expr.cost, Nat.reduceAdd]; omega)⟩

end

end Light.Sec3
