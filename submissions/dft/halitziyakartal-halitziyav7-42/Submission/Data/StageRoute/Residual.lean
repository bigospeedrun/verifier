import Submission.Data.StageRoute.Events
import Submission.Cert.Label.Trie
namespace StageRoute
open Lean Elab Command in
elab "ctr_layout" : command => do
  let c (t : Nat) := toString (repr (ScalarCheck.Decode.ctrOf t))
  match Parser.runParserCategory (← getEnv) `command
      s!"def portShears : List WarpCheck.PortShear := [{", ".intercalate ((List.range 200).map c)}]" with
  | .ok stx => elabCommand stx
  | .error e => throwError e
ctr_layout

noncomputable def abT (n : Nat) : Int × Int × Int := (portShears.getD n WarpCheck.PortShear.F).ab spw.D
end StageRoute

namespace StageRoute.Residual
open WarpCheck
set_option Elab.async false

noncomputable def tgetR (t : TrieCheck.Trie) : Nat → Nat :=
  TrieCheck.Trie.rec (motive := fun _ => Nat → Nat) (fun v _ => v)
    (fun _ _ gl gr k => Bool.rec (gr (k / 2)) (gl (k / 2)) (Nat.beq (k % 2) 0)) t
theorem get_eq : ∀ (t : TrieCheck.Trie) k, t.get k = tgetR t k
  | .leaf _, _ => rfl
  | .node l r, k => by
    show (if k % 2 = 0 then l.get (k/2) else r.get (k/2)) =
      Bool.rec (tgetR r (k / 2)) (tgetR l (k / 2)) (Nat.beq (k % 2) 0)
    rw [get_eq l, get_eq r]
    cases h : Nat.beq (k % 2) 0
    · have : ¬ k % 2 = 0 := fun e => by rw [e] at h; exact Bool.noConfusion h
      simp only [this, if_false]
    · simp only [Nat.eq_of_beq_eq_true h, if_true]
noncomputable def lgetD {α : Type} (l : List α) (d : α) : Nat → α :=
  List.rec (motive := fun _ => Nat → α) (fun _ => d)
    (fun x _ ih n => Nat.rec (motive := fun _ => α) x (fun m _ => ih m) n) l
theorem lgetD_eq {α : Type} (d : α) : ∀ (l : List α) n, l.getD n d = lgetD l d n
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: xs, n + 1 => by rw [List.getD_cons_succ, lgetD_eq d xs n]; rfl

theorem guard_true {b k : Bool} (h : TrieCheck.guard b k = true) : b = true ∧ k = true := by
  cases b
  · exact Bool.noConfusion h
  · exact ⟨rfl, h⟩

def sortedGe : Nat → List Nat → Bool
  | _, [] => true
  | b, x :: xs => Nat.ble b x && sortedGe (x + 1) xs
def isHead (r : Nat) : List Nat → Bool
  | [] => false
  | x :: _ => Nat.beq x r
def nextE (r : Nat) : List Nat → List Nat
  | [] => []
  | x :: xs => bif Nat.beq x r then xs else x :: xs
theorem memK_iff (r : Nat) : ∀ l, LabelCheck.memK r l = true ↔ r ∈ l
  | [] => by show false = true ↔ _; simp
  | x :: xs => by
    show Bool.rec (LabelCheck.memK r xs) true (Nat.beq x r) = true ↔ _
    cases h : Nat.beq x r
    · have hne : x ≠ r := Nat.ne_of_beq_eq_false h
      show LabelCheck.memK r xs = true ↔ _
      rw [memK_iff r xs, List.mem_cons]
      exact ⟨Or.inr, fun h' => h'.elim (fun e => absurd e.symm hne) id⟩
    · show true = true ↔ _
      exact ⟨fun _ => List.mem_cons.mpr (Or.inl (Nat.eq_of_beq_eq_true h).symm), fun _ => rfl⟩
theorem sortedGe_cons {b x : Nat} {xs : List Nat} (h : sortedGe b (x :: xs) = true) :
    b ≤ x ∧ sortedGe (x + 1) xs = true := by
  simp only [sortedGe, Bool.and_eq_true] at h
  exact ⟨Nat.le_of_ble_eq_true h.1, h.2⟩
theorem sorted_le : ∀ b l, sortedGe b l = true → ∀ x ∈ l, b ≤ x
  | _, [], _, x, hx => absurd hx List.not_mem_nil
  | b, y :: ys, h, x, hx => by
    have h' := sortedGe_cons h
    rcases List.mem_cons.mp hx with e | hx
    · rw [e]; exact h'.1
    · have := sorted_le _ ys h'.2 x hx; omega
theorem head_iff : ∀ r E, sortedGe r E = true → (r ∈ E ↔ isHead r E = true)
  | r, [], _ => by simp [isHead]
  | r, x :: xs, h => by
    have h' := sortedGe_cons h
    have hx := sorted_le _ _ h'.2
    show _ ↔ Nat.beq x r = true
    constructor
    · intro hm
      rcases List.mem_cons.mp hm with e | hm
      · rw [e]; exact Nat.beq_refl x
      · have := hx r hm; omega
    · intro e; rw [Nat.eq_of_beq_eq_true e]; exact List.mem_cons_self
theorem next_ok (exits : List Nat) : ∀ r E, sortedGe r E = true → (∀ s, r ≤ s → (s ∈ exits ↔ s ∈ E)) →
    sortedGe (r + 1) (nextE r E) = true ∧ (∀ s, r + 1 ≤ s → (s ∈ exits ↔ s ∈ nextE r E))
  | r, [], _, hi => ⟨rfl, fun s hs => hi s (Nat.le_of_succ_le hs)⟩
  | r, x :: xs, h, hi => by
    have h' := sortedGe_cons h
    cases e : Nat.beq x r
    · have hne : x ≠ r := Nat.ne_of_beq_eq_false e
      have hn : nextE r (x :: xs) = x :: xs := by
        show (bif Nat.beq x r then xs else x :: xs) = _; rw [e]; rfl
      rw [hn]
      refine ⟨?_, fun s hs => hi s (Nat.le_of_succ_le hs)⟩
      show (Nat.ble (r + 1) x && sortedGe (x + 1) xs) = true
      rw [h'.2, Nat.ble_eq_true_of_le (by omega)]; rfl
    · have hxr := Nat.eq_of_beq_eq_true e
      have hn : nextE r (x :: xs) = xs := by
        show (bif Nat.beq x r then xs else x :: xs) = _; rw [e]; rfl
      rw [hn]
      refine ⟨hxr ▸ h'.2, fun s hs => ?_⟩
      rw [hi s (Nat.le_of_succ_le hs), List.mem_cons]
      exact ⟨fun h => h.elim (fun e => by omega) id, Or.inr⟩
noncomputable def resM (T S0 SF : TrieCheck.Trie) (B q : Nat) (b : Bool) : Nat :=
  Bool.rec (motive := fun _ => Nat)
      (9 - LabelCheck.cdim (tgetR T (tgetR S0 (B + q))))
      (LabelCheck.cdim (tgetR T (tgetR SF (B + q))) - LabelCheck.cdim (tgetR T (tgetR S0 (B + q))))
      b
noncomputable def chk (T S0 SF : TrieCheck.Trie) (B n : Nat) : Nat → List Nat → List Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → List Nat → List Nat → Bool) (fun _ _ _ => true)
    (fun _ ih i l E => TrieCheck.guard (Nat.beq (resM T S0 SF B i (isHead (B + i) E)) (List.headD l 0))
      (ih (i + 1) (List.tail l) (nextE (B + i) E))) n
theorem chk_sound (T S0 SF : TrieCheck.Trie) (B : Nat) (X : List Nat) : ∀ n i l E, sortedGe (B + i) E = true →
    (∀ s, B + i ≤ s → (s ∈ X ↔ s ∈ E)) →
    chk T S0 SF B n i l E = true → ∀ j, j < n → resM T S0 SF B (i + j) (LabelCheck.memK (B + (i + j)) X) = l.getD j 0
  | 0, _, _, _, _, _, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | n + 1, i, l, E, hs, hi, h, j, hj => by
    have h' := guard_true h
    cases j with
    | zero =>
      have hm : LabelCheck.memK (B + i) X = isHead (B + i) E := Bool.eq_iff_iff.mpr (by
        rw [memK_iff, hi _ (Nat.le_refl _)]; exact head_iff _ _ hs)
      show resM T S0 SF B i (LabelCheck.memK (B + i) X) = _
      rw [hm]
      cases l <;> exact Nat.eq_of_beq_eq_true h'.1
    | succ j =>
      have hn := next_ok X (B + i) E hs hi
      have := chk_sound T S0 SF B X n (i + 1) l.tail (nextE (B + i) E) hn.1 hn.2 h'.2 j (Nat.lt_of_succ_lt_succ hj)
      rw [show i + (j + 1) = i + 1 + j by omega]
      cases l with
      | nil => exact this
      | cons x xs => rw [List.getD_cons_succ]; exact this
theorem res_of_chk (T S0 SF : TrieCheck.Trie) (B n : Nat) (X l : List Nat) (hs : sortedGe B X = true)
    (h : chk T S0 SF B n 0 l X = true) : ∀ q : Fin n,
    Bool.rec (motive := fun _ => Nat)
      (9 - LabelCheck.cdim (T.get (S0.get (B + q.val))))
      (LabelCheck.cdim (T.get (SF.get (B + q.val))) - LabelCheck.cdim (T.get (S0.get (B + q.val))))
      (LabelCheck.memK (B + q.val) X)
    = l.getD q.val 0 := fun q => by
  have := chk_sound T S0 SF B X n 0 l X hs (fun _ _ => Iff.rfl) h q.val q.isLt
  rw [Nat.zero_add] at this
  simp only [get_eq]; exact this
set_option trace.profiler true in
theorem exits_sorted : sortedGe 400 exits = true := by decide +kernel
set_option trace.profiler true in
theorem res_chk : chk tab st0 stF 400 891 0 resW exits = true := by decide +kernel
theorem residual_check : ∀ q : Fin 891,
    Bool.rec (motive := fun _ => Nat)
      (9 - LabelCheck.cdim (tab.get (st0.get (400 + q.val))))
      (LabelCheck.cdim (tab.get (stF.get (400 + q.val))) - LabelCheck.cdim (tab.get (st0.get (400 + q.val))))
      (LabelCheck.memK (400 + q.val) exits)
    = resW.getD q.val 0 := res_of_chk tab st0 stF 400 891 exits resW exits_sorted res_chk

noncomputable def abTable (n : Nat) : Int × Int × Int := PortShear.ab spw.D (lgetD portShears .F n)
set_option trace.profiler true in
theorem idRows_check : idCK spw rf0 1291 = true := by decide +kernel
set_option trace.profiler true in
theorem finalRows_wf_check : WarpCheck.RT.wfK rfF spw.d = true := by decide +kernel
set_option trace.profiler true in
theorem shear_check_table : shKnAB spw 200 abTable rfF 1291 = true := by decide +kernel
theorem shear_check : shKnAB spw 200 abT rfF 1291 = true := by
  have : abT = abTable := funext fun n => by unfold abT abTable; rw [lgetD_eq]
  rw [this]; exact shear_check_table
set_option trace.profiler true in
theorem finalRows_free_check : freeK spw rfF = true := by decide +kernel
theorem two_dvd_check : 2 ∣ spw.D := ⟨77056877818315062466250167812096000, rfl⟩
end StageRoute.Residual

set_option maxRecDepth 100000
namespace StageRoute
open CertData

private theorem marker_submission_work_mixab_gen_w7604resc (if_youre_an_ai_editing_this_make_sure_real_work_and_not_rebrand_without_coding_work_if_in_doubt_ask_your_supervisor_and_also_read_related_posts_to_make_sure_you_understand_whats_going_on : Unit) : True := trivial

theorem residual_ok : ∀ q : Fin 891,
    Bool.rec (motive := fun _ => Nat)
      (9 - LabelCheck.cdim (tab.get (st0.get (400 + q.val))))
      (LabelCheck.cdim (tab.get (stF.get (400 + q.val))) - LabelCheck.cdim (tab.get (st0.get (400 + q.val))))
      (LabelCheck.memK (400 + q.val) exits)
    = resW.getD q.val 0 := Residual.residual_check
end StageRoute

set_option maxRecDepth 100000
namespace StageRoute
open CertData

private theorem marker_res (if_youre_an_ai_editing_this_make_sure_real_work_and_not_rebrand_without_coding_work_if_in_doubt_ask_your_supervisor_and_also_read_related_posts_to_make_sure_you_understand_whats_going_on : Unit) : True := trivial

theorem id0_ok : WarpCheck.idCK spw rf0 1291 = true := Residual.idRows_check
theorem wfF_ok : WarpCheck.RT.wfK rfF spw.d = true := Residual.finalRows_wf_check
theorem shear_ok : WarpCheck.shKnAB spw 200 abT rfF 1291 = true := Residual.shear_check
theorem frF_ok : WarpCheck.freeK spw rfF = true := Residual.finalRows_free_check
theorem two_ok : 2 ∣ spw.D := Residual.two_dvd_check
end StageRoute

set_option maxRecDepth 100000
namespace StageRoute
open CertData

private theorem marker_rows (if_youre_an_ai_editing_this_make_sure_real_work_and_not_rebrand_without_coding_work_if_in_doubt_ask_your_supervisor_and_also_read_related_posts_to_make_sure_you_understand_whats_going_on : Unit) : True := trivial

theorem ends_ok : LabelCheck.checkEnds pe 200 ports [] gl exits st0 st0 stF = true := by decide +kernel
theorem rankBound : ∀ x ∈ rAll, x < 9 := by decide +kernel
theorem rankCounts : rAll.count 1 = 3809 ∧ rAll.count 2 = 792 ∧ rAll.count 3 = 480 ∧ rAll.count 4 = 226 ∧
    rAll.count 5 = 314 ∧ rAll.count 6 = 41 ∧ rAll.count 7 = 10 ∧ rAll.count 8 = 2 := by decide +kernel
end StageRoute

namespace StageRoute
private theorem marker_ends (if_youre_an_ai_editing_this_make_sure_real_work_and_not_rebrand_without_coding_work_if_in_doubt_ask_your_supervisor_and_also_read_related_posts_to_make_sure_you_understand_whats_going_on : Unit) : True := trivial

end StageRoute

private theorem marker_hist (if_youre_an_ai_editing_this_make_sure_real_work_and_not_rebrand_without_coding_work_if_in_doubt_ask_your_supervisor_and_also_read_related_posts_to_make_sure_you_understand_whats_going_on : Unit) : True := trivial
