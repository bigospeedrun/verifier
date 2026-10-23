import Submission.Work.KLowW.ScalSound

/-!
# (key: p-warpchk) THE WARP CERTIFICATE THEOREM of a checked segment

`warp_groute`: the label replay (`segW`, with the frame table `tabK` and the warp table `wtK`) and the free-warp-algebra
replay (`scalW`) of the same events, from identity rows (`idK`) to warp-free rows (`freeK`), give for EVERY stage-B
frame map `X` with a warp meaning `W : WarpSem` an ordinary exact route of the generalised engine

    GRoute (Lf S) (Lf S') (actPoint (rowsMat q un emb R')) (rcost rs)

in either orientation (`o = false` forward with the forward family `W`, `o = true` the dual stream with the backward
family).  All four hypotheses are kernel checks (`decide +kernel` on data).  Without warps, `RunW.ofRun` and
`esMap_gates` give back the old statement (`Run.route`).

No `sorry`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace KLW
open SSC GXD GLab OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.GF OAI.PowerSaving.RAM
  OAI.PowerSaving.CB Finset Matrix

/-- every key of the row is below `N` (no warp word) -/
noncomputable def allLt (N : Nat) : Row → Bool :=
  List.rec (motive := fun _ => Bool) true (fun e _ ih => guard (Nat.blt e.1 N) ih)

/-- the rows of the registers `< n` are the identity rows `[(r, D)]` -/
noncomputable def idKn (q : SPw) (R : RT) (n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun r ih => guard (R.getK r (fun row => rowEq row [(r, (q.D : Int))])) ih) n

/-- the rows of the registers `< nr` are the identity rows -/
noncomputable def idK (q : SPw) (R : RT) : Bool := idKn q R q.nr

/-- the rows of the registers `< n` are warp-free -/
noncomputable def freeKn (q : SPw) (R : RT) (n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun r ih => guard (R.getK r (fun row => allLt q.N row)) ih) n

/-- the rows of the registers `< nr` are warp-free -/
noncomputable def freeK (q : SPw) (R : RT) : Bool := freeKn q R q.nr

theorem allLt_sound (N : Nat) : ∀ (row : Row), allLt N row = true → ∀ e ∈ row, e.1 < N := by
  intro row
  induction row with
  | nil => intro _ e he; exact absurd he List.not_mem_nil
  | cons x xs ih =>
    intro H e he
    have H' : SSC.guard (Nat.blt x.1 N) (allLt N xs) = true := H
    obtain ⟨g1, g2⟩ := SSC.guard_true H'
    rcases List.mem_cons.mp he with h | h
    · rw [h]; have := g1; rw [Nat.blt_eq] at this; exact this
    · exact ih g2 e h

theorem idK_sound (q : SPw) (R : RT) (hR : R.wf q.d) (H : idK q R = true) :
    ∀ r, r < q.nr → R.get r = [(r, (q.D : Int))] := by
  have key : ∀ n, idKn q R n = true → ∀ r, r < n → R.get r = [(r, (q.D : Int))] := by
    intro n
    induction n with
    | zero => intro _ r hr; exact absurd hr (Nat.not_lt_zero r)
    | succ n ih =>
      intro H r hr
      have H' : SSC.guard (R.getK n (fun row => rowEq row [(n, (q.D : Int))])) (idKn q R n) = true := H
      obtain ⟨g1, g2⟩ := SSC.guard_true H'
      rcases Nat.lt_succ_iff_lt_or_eq.mp hr with h | h
      · exact ih g2 r h
      · subst h
        exact rowEq_sound _ _ (RT.getK_true hR g1).2
  exact key q.nr H

theorem freeK_sound (q : SPw) (R : RT) (hR : R.wf q.d) (H : freeK q R = true) :
    ∀ r, r < q.nr → ∀ e ∈ R.get r, e.1 < q.N := by
  have key : ∀ n, freeKn q R n = true → ∀ r, r < n → ∀ e ∈ R.get r, e.1 < q.N := by
    intro n
    induction n with
    | zero => intro _ r hr; exact absurd hr (Nat.not_lt_zero r)
    | succ n ih =>
      intro H r hr
      have H' : SSC.guard (R.getK n (fun row => allLt q.N row)) (freeKn q R n) = true := H
      obtain ⟨g1, g2⟩ := SSC.guard_true H'
      rcases Nat.lt_succ_iff_lt_or_eq.mp hr with h | h
      · exact ih g2 r h
      · subst h
        exact allLt_sound _ _ (RT.getK_true hR g1).2
  exact key q.nr H

/-- the parameters of the row replay are sane (checked once, e.g. read off any passing `scalW`) -/
def ParOK (q : SPw) : Prop := 1 ≤ q.N ∧ q.nr ≤ q.N ∧ q.nr ≤ 2 ^ q.d ∧ 2 ≤ q.B ∧ 1 ≤ q.D

/-- **what a passing free-algebra replay of a segment proves**, composable across segments (`ScalOK.append`) -/
def ScalOK (q : SPw) (o : Bool) (evs : List WEv) (R R' : RT) : Prop :=
  R.wf q.d ∧ ∀ {α ρ : Type} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
    (K : Int → CMat α) (emb : ρ → Nat) (un : Nat → ρ), SCtx q emb un → (∀ a, K a * K (-a) = 1) →
    ∀ {f : ℕ} (x : Data α ρ f), esMap o K un evs f (vecR q K un emb R x) = vecR q K un emb R' x

theorem ParOK.of_scalW {q : SPw} {o : Bool} {evs : List WEv} {R R' : RT} (H : scalW q o evs R R' = true) :
    ParOK q := by
  unfold scalW at H
  obtain ⟨g0, H⟩ := guard_true H
  obtain ⟨g1, H⟩ := guard_true H
  obtain ⟨g2, H⟩ := guard_true H
  obtain ⟨g3, H⟩ := guard_true H
  obtain ⟨g4, H⟩ := guard_true H
  obtain ⟨g5, H⟩ := guard_true H
  exact ⟨ble_true g1, ble_true g2, by have := ble_true g3; simpa using this, ble_true g4, ble_true g5⟩

/-- one kernel replay of a segment is a `ScalOK` -/
theorem ScalOK.of_check {q : SPw} {o : Bool} {evs : List WEv} {R R' : RT} (H : scalW q o evs R R' = true) :
    ScalOK q o evs R R' := by
  refine ⟨?_, by intro α ρ _ _ _ _ K emb un hq hK f x; exact (scalW_sound (K := K) hq hK H).2.2.2 x⟩
  unfold scalW at H
  exact RT.wfK_sound R q.d (guard_true H).1

/-- **composition of checked segments** -/
theorem ScalOK.append {q : SPw} {o : Bool} {e1 e2 : List WEv} {R R1 R2 : RT} (a : ScalOK q o e1 R R1)
    (b : ScalOK q o e2 R1 R2) : ScalOK q o (e1 ++ e2) R R2 :=
  ⟨a.1, by intro α ρ _ _ _ _ K emb un hq hK f x; rw [esMap_append, a.2 K emb un hq hK x, b.2 K emb un hq hK x]⟩

section
variable {α ρ : Type} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
variable {p : GLab.Par} {emb : ρ → Nat} {un : Nat → ρ}

/-- the row trie after a passing replay is well formed -/
theorem RT.wf_of_scalW {q : SPw} {o : Bool} {evs : List WEv} {R R' : RT} (H : scalW q o evs R R' = true) :
    R.wf q.d := by
  unfold scalW at H
  exact RT.wfK_sound R q.d (guard_true H).1

/-- **THE WARP CERTIFICATE THEOREM** of one checked segment (see the file header) -/
theorem warp_groute (C : Ctx p emb un) (X : BXMap (Fin p.h) α) (hα : p.h < Fintype.card α) {wt : List WOp}
    (W : WarpSem p.h wt X) (o : Bool) {S S' : Trie} {evs : List WEv} {rs : List Nat}
    (hWK : wtK p.h wt = true) (hL : segW p wt evs S S' rs = true) (hS : S.wf p.d)
    (q : SPw) (hq : SCtx q emb un) {R0 R' : RT} (hR' : R'.wf q.d) (h0 : idK q R0 = true)
    (hfree : freeK q R' = true) (hSc : scalW q o evs R0 R' = true) :
    GRoute (Lf p emb X S) (Lf p emb X S') (actPoint (rowsMat q un emb R')) (fun φ => rcost φ rs) := by
  have R := RunW.of_seg C.hT hWK hL
  have rt := (RunW.route C X hα W o R hS).1
  obtain ⟨hR0, hN, hD, hv⟩ := scalW_sound (K := W.K) hq W.hinv hSc
  have hN1 : 1 ≤ q.N := by
    unfold scalW at hSc
    exact ble_true (guard_true (guard_true hSc).2).1
  have hid := idK_sound q R0 hR0 h0
  have hfr := freeK_sound q R' hR' hfree
  refine GRouteF.toG (rt.congrF (fun f x => ?_))
  have e1 : esMap o W.K un evs f x = vecR q W.K un emb R' x := by
    have := hv x
    rwa [vecR_id (K := W.K) hq hN hD hid x] at this
  rw [e1, vecR_free hN1 (fun j e he => hfr (emb j) (hq.hlt j) e he)]

/-- **THE WARP CERTIFICATE THEOREM**, segment form: the label replay as `RunW` and the row replay as `ScalOK`
(each composed from per-segment kernel checks by `RunW.append` / `ScalOK.append`) -/
theorem warp_grouteS (C : Ctx p emb un) (X : BXMap (Fin p.h) α) (hα : p.h < Fintype.card α) {wt : List WOp}
    (W : WarpSem p.h wt X) (o : Bool) {S S' : Trie} {evs : List WEv} {rs : List Nat}
    (R : RunW p wt S evs S' rs) (hS : S.wf p.d)
    (q : SPw) (hpar : ParOK q) (hq : SCtx q emb un) {R0 R' : RT} (hR' : R'.wf q.d) (h0 : idK q R0 = true)
    (hfree : freeK q R' = true) (hSc : ScalOK q o evs R0 R') :
    GRoute (Lf p emb X S) (Lf p emb X S') (actPoint (rowsMat q un emb R')) (fun φ => rcost φ rs) := by
  have rt := (RunW.route C X hα W o R hS).1
  have hid := idK_sound q R0 hSc.1 h0
  have hfr := freeK_sound q R' hR' hfree
  refine GRouteF.toG (rt.congrF (fun f x => ?_))
  have e1 : esMap o W.K un evs f x = vecR q W.K un emb R' x := by
    have := hSc.2 W.K emb un hq W.hinv x
    rwa [vecR_id (K := W.K) hq hpar.2.1 hpar.2.2.2.2 hid x] at this
  rw [e1, vecR_free hpar.1 (fun j e he => hfr (emb j) (hq.hlt j) e he)]

end
end KLW

#print axioms KLW.warp_groute
#print axioms KLW.warp_grouteS
#print axioms KLW.ScalOK.append
