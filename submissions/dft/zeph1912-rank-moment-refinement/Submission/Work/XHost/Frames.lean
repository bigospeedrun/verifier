import Submission.Work.Bank401.Frames
import Submission.Work.GFrame.Clifford.Old

/-!
# XHost.Frames: hosting = a bank whose start and end are the host's idle-climb frames

Idle-axis hosting (DaysSky, CrocSwap/integer-mult-bounds PR #442) puts the residual of a helper slot of an invocation
on the pending coordinates of an idle data role.  In our engine this needs NO new conjugation lemma:

* the residual of a gauged slot is already `Wn = C * pk R * C'` with `C`, `C'` free and `|R| = 9 - e_q`
  (`entW_form`, Work/Bridge401/Sched.lean; `gauged_Wn`, Work/Bank401/Adapt.lean: Nil Mamano / Ryan Shea, on
  Dugongue's #401 banks);
* an idle climb inside ONE orthonormal base, `frame A s → frame A t`, is `X1 = Q * pk D * Q' * X0` with `Q`, `Q'`
  free and `|D| = |t \ s|` (`hostForm_frame`, from Jacob Sussman's `frame_core_free` and `core_nested`);
* the bank adapter (`bank_adapt`, K6 of Work/Bank401/Adapt.lean) moves `R` by a free coordinate permutation onto
  ANY unused coordinates; `host_adapt` is the same with the new coordinates chosen inside the pending set `D`;
* the bank pad (`bank_pad`, K7) becomes `host_pad`: the remainder of the climb is ONE block of rank `|D| - load`.

`slot_frames` is `bank_frames` (Work/Bank401/Frames.lean) for a family of slot roles `J` (banks AND hosts) with
start frames `X0`, end frames `X1` in host form, and a partial schedule `use k q : Option J`.  A bank is the case
`X0 = 1`, `X1 = kernel α`, `D = univ`.

Fresh namespace `OAI.PowerSaving.XHost`.  Written for the wht43 h-L3-design study (13 Oct 2026), adapted from
Work/Bank401 (Shea's complex588 tree at 0e61af6), prepared with assistance from Claude.  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace XHost
open Binary Matrix Finset GF CB B401
noncomputable section

section Form
variable {α : Type} [Fintype α] [DecidableEq α]

/-- **Host form** of an idle climb: `X1 = Q * pk D * Q' * X0`, `Q`, `Q'` free, `|D| = r`. -/
def HostForm (X0 X1 : CMat α) (r : ℕ) : Prop :=
  ∃ (Q Q' : CMat α) (D : Finset α), Free Q ∧ Free Q' ∧ D.card = r ∧ X1 = Q * pk D * Q' * X0

/-- **Every nested climb inside one orthonormal base has host form** (`frame_core_free`, `core_nested`). -/
theorem hostForm_frame (A : OBase α) {s t : Finset α} (h : s ⊆ t) :
    HostForm (frame A s) (frame A t) (t \ s).card := by
  obtain ⟨N0, hN0, e0⟩ := frame_core_free A s
  obtain ⟨N1, hN1, e1⟩ := frame_core_free A t
  obtain ⟨N0i, hN0i, h0i, -⟩ := free_inv hN0
  refine ⟨N1 * kg (coordPerm A), kg (apInv (coordPerm A)) * N0i, t \ s,
    Free.mul hN1 (free_kg _), Free.mul (free_kg _) hN0i, rfl, ?_⟩
  have e2 : N0i * (N0 * core (coordPerm A) s) = core (coordPerm A) s := by
    rw [← Matrix.mul_assoc, h0i, Matrix.one_mul]
  rw [e1, e0, core_nested _ h, ← pk_eq_blockMat]
  simp only [Matrix.mul_assoc]
  rw [e2]

/-- the bank case: from `1` to `kernel α` is host form with `D = univ`. -/
theorem hostForm_bank : HostForm (1 : CMat α) (kernel α) (Fintype.card α) :=
  ⟨1, 1, univ, Free.one, Free.one, Finset.card_univ, by rw [pk_univ]; simp⟩

end Form

section Adapt
variable {α : Type} [Fintype α] [DecidableEq α]

/-- **The host adapter** (`bank_adapt` with the new coordinates inside the pending set `D`). -/
theorem host_adapt {A B C C' : CMat α} (hA : Free A) (hC : Free C) (hC' : Free C')
    (D U R : Finset α) (hUD : U ⊆ D) (hc : U.card + R.card ≤ D.card) :
    ∃ P, Free P ∧ ∃ (A2 : CMat α) (U2 : Finset α), Free A2 ∧ U2 ⊆ D ∧ U2.card = U.card + R.card ∧
      C * pk R * C' * (P * (A * pk U * B)) = A2 * pk U2 * B := by
  obtain ⟨Ai, hAi, hAiA, -⟩ := free_inv hA
  obtain ⟨Ci, hCi, -, hC'Ci⟩ := free_inv hC'
  have hUc : R.card ≤ (D \ U).card := by
    rw [Finset.card_sdiff_of_subset hUD]
    omega
  obtain ⟨T, hTU, hTc⟩ := Finset.exists_subset_card_eq hUc
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq T R (hTc.trans rfl)
  have hPi : pk R * permMat (cperm σ) = permMat (cperm σ) * pk T := by
    rw [pk_cperm, hσ]
  have hdisj : Disjoint T U := by
    rw [Finset.disjoint_left]
    intro a ha hu
    exact (Finset.mem_sdiff.mp (hTU ha)).2 hu
  refine ⟨Ci * permMat (cperm σ) * Ai, Free.mul (Free.mul hCi (free_cperm σ)) hAi,
    C * permMat (cperm σ), T ∪ U, Free.mul hC (free_cperm σ), ?_, ?_, ?_⟩
  · intro a ha
    rcases Finset.mem_union.mp ha with ht | hu
    · exact (Finset.mem_sdiff.mp (hTU ht)).1
    · exact hUD hu
  · rw [Finset.card_union_of_disjoint hdisj, hTc, Nat.add_comm]
  · have e : C * pk R * C' * (Ci * permMat (cperm σ) * Ai * (A * pk U * B))
        = C * (pk R * permMat (cperm σ)) * (Ai * A) * pk U * B := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc C' Ci, hC'Ci, Matrix.one_mul]
    rw [e, hAiA, Matrix.mul_one, hPi, pk_union T U hdisj]
    simp only [Matrix.mul_assoc]

/-- **The remaining climb of a host** (`bank_pad` with target `Q * pk D * B`): ONE block of rank `|D| - |U|`
(free when the host is full). -/
theorem host_pad {A Q : CMat α} (hA : Free A) (hQ : Free Q) (B : CMat α) (D U : Finset α) (hUD : U ⊆ D)
    (hD : D.card - U.card < Fintype.card α) :
    GReach (A * pk U * B) (Q * pk D * B) (fun φ => bcost φ (D.card - U.card)) := by
  intro ρ _ _ l
  obtain ⟨Ai, hAi, hAiA, -⟩ := free_inv hA
  obtain ⟨Qi, hQi, hQiQ, -⟩ := free_inv hQ
  have h1 := gstep_free (Free.mul hQ hAi) l (A * pk U * B)
  have e1 : Q * Ai * (A * pk U * B) = Q * pk U * B := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Ai A, hAiA, Matrix.one_mul]
  rw [e1] at h1
  have hk : (D \ U).card = D.card - U.card := Finset.card_sdiff_of_subset hUD
  by_cases h0 : D.card - U.card = 0
  · have hUeq : U = D := Finset.eq_of_subset_of_card_le hUD (by omega)
    subst hUeq
    refine h1.cast (fun φ => ?_)
    simp [bcost]
  · have h2 := gstep_of_factor l (Q * pk U * B) ((OBase.canonical α).fam (D \ U))
      ((OBase.canonical α).fam_indep _) hQ hQi (by omega) (by omega)
    have e2 : Q * blockMat ((OBase.canonical α).fam (D \ U)) * Qi * (Q * pk U * B) = Q * pk D * B := by
      rw [← pk_eq_blockMat, pk_sdiff hUD]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Qi Q, hQiQ, Matrix.one_mul]
    rw [e2, hk] at h2
    refine (h1.trans h2).cast (fun φ => ?_)
    rw [bcost_pos φ h0]
    ring

end Adapt

section Sched
variable {α Γ Sl J : Type} [Fintype α] [DecidableEq α] [Fintype Sl] [DecidableEq Sl] [DecidableEq J]
variable (use : ℕ → Sl → Option J) (r : Sl → ℕ)

/-- the residual the slot role `j` takes in sub-stage `k`. -/
def rrH (k : ℕ) (j : J) : ℕ := ∑ q ∈ univ.filter (fun q => use k q = some j), r q

/-- the load of the slot role `j` after `k` sub-stages. -/
def LH (k : ℕ) (j : J) : ℕ := ∑ i ∈ range k, rrH use r i j

lemma LH_zero (j : J) : LH use r 0 j = 0 := by simp [LH]

lemma LH_succ (k : ℕ) (j : J) : LH use r (k + 1) j = LH use r k j + rrH use r k j := by
  simp [LH, Finset.sum_range_succ]

lemma LH_mono {k k' : ℕ} (h : k ≤ k') (j : J) : LH use r k j ≤ LH use r k' j :=
  Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr h)

/-- at most ONE slot of an invocation on a slot role per sub-stage. -/
def OneUse (k : ℕ) : Prop := ∀ q q' j, use k q = some j → use k q' = some j → q = q'

lemma rrH_of_use {k : ℕ} (hinj : OneUse use k) {q : Sl} {j : J} (hq : use k q = some j) :
    rrH use r k j = r q := by
  unfold rrH
  rw [Finset.sum_eq_single q]
  · intro q' hq' hne
    exact absurd (hinj q' q j (Finset.mem_filter.mp hq').2 hq) hne
  · intro h
    exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ q, hq⟩) h

lemma rrH_of_not {k : ℕ} {j : J} (h : ∀ q, use k q ≠ some j) : rrH use r k j = 0 := by
  unfold rrH
  exact Finset.sum_eq_zero (fun q hq => absurd (Finset.mem_filter.mp hq).2 (h q))

variable (Wn : ℕ → Γ → Sl → CMat α) (B : Γ → J → CMat α) (D : Γ → J → Finset α)

/-- one step of one slot role (`t = (P, A2, U2)`), frames `A * pk U * B d j`. -/
def StepOkH (k : ℕ) (d : Γ) (j : J) (A : CMat α) (U : Finset α) (t : CMat α × CMat α × Finset α) : Prop :=
  Free t.1 ∧ Free t.2.1 ∧ t.2.2 ⊆ D d j ∧ t.2.2.card = LH use r (k + 1) j ∧
    (∀ q, use k q = some j → Wn k d q * (t.1 * (A * pk U * B d j)) = t.2.1 * pk t.2.2 * B d j) ∧
    ((∀ q, use k q ≠ some j) → t.1 = 1 ∧ t.2.1 * pk t.2.2 = A * pk U)

lemma stepH_ex {k : ℕ} (d : Γ) (j : J) {A : CMat α} {U : Finset α} (hA : Free A) (hUD : U ⊆ D d j)
    (hU : U.card = LH use r k j) (hb : LH use r (k + 1) j ≤ (D d j).card) (hinj : OneUse use k)
    (hWn : ∀ q, ∃ (C C' : CMat α) (R : Finset α), Free C ∧ Free C' ∧ R.card = r q ∧ Wn k d q = C * pk R * C') :
    ∃ t, StepOkH use r Wn B D k d j A U t := by
  by_cases h : ∃ q, use k q = some j
  · obtain ⟨q0, hq0⟩ := h
    obtain ⟨C, C', R, hC, hC', hR, hW⟩ := hWn q0
    have hL : LH use r (k + 1) j = U.card + R.card := by
      rw [LH_succ, rrH_of_use use r hinj hq0, hU, hR]
    obtain ⟨P, hP, A2, U2, hA2, hU2D, hc, he⟩ :=
      host_adapt (B := B d j) hA hC hC' (D d j) U R hUD (by rw [← hL]; exact hb)
    refine ⟨(P, A2, U2), hP, hA2, hU2D, by rw [hL]; exact hc, fun q hq => ?_, fun hn => absurd hq0 (hn q0)⟩
    have e : q = q0 := hinj q q0 j hq hq0
    subst e
    show Wn k d q * (P * (A * pk U * B d j)) = A2 * pk U2 * B d j
    rw [hW]
    exact he
  · push_neg at h
    refine ⟨(1, A, U), Free.one, hA, hUD, ?_, fun q hq => absurd hq (h q), fun _ => ⟨rfl, rfl⟩⟩
    show U.card = LH use r (k + 1) j
    rw [LH_succ, rrH_of_not use r h, hU, Nat.add_zero]

variable (K : ℕ)

/-- the state invariant of a slot role after `k` sub-stages. -/
def InvH (d : Γ) (j : J) (k : ℕ) (p : CMat α × Finset α) : Prop :=
  Free p.1 ∧ p.2 ⊆ D d j ∧ (k ≤ K → LH use r k j ≤ (D d j).card → p.2.card = LH use r k j)

lemma stepH_ex' (hinj : ∀ k < K, OneUse use k)
    (hWn : ∀ k < K, ∀ d q, ∃ (C C' : CMat α) (R : Finset α), Free C ∧ Free C' ∧ R.card = r q ∧
      Wn k d q = C * pk R * C')
    (k : ℕ) (d : Γ) (j : J) (s : {p : CMat α × Finset α // InvH use r D K d j k p}) :
    ∃ t : CMat α × CMat α × Finset α, Free t.2.1 ∧ t.2.2 ⊆ D d j ∧
      (k + 1 ≤ K → LH use r (k + 1) j ≤ (D d j).card → t.2.2.card = LH use r (k + 1) j) ∧
      (k < K → LH use r (k + 1) j ≤ (D d j).card → StepOkH use r Wn B D k d j s.1.1 s.1.2 t) := by
  by_cases hk : k < K
  · by_cases hb : LH use r (k + 1) j ≤ (D d j).card
    · have hU := s.2.2.2 hk.le (le_trans (LH_mono use r (Nat.le_succ k) j) hb)
      obtain ⟨t, ht⟩ := stepH_ex use r Wn B D d j s.2.1 s.2.2.1 hU hb (hinj k hk) (hWn k hk d)
      exact ⟨t, ht.2.1, ht.2.2.1, fun _ _ => ht.2.2.2.1, fun _ _ => ht⟩
    · exact ⟨(1, s.1.1, s.1.2), s.2.1, s.2.2.1, fun _ h => absurd h hb, fun _ h => absurd h hb⟩
  · exact ⟨(1, s.1.1, s.1.2), s.2.1, s.2.2.1, fun h => absurd (Nat.lt_of_succ_le h) hk,
      fun h => absurd h hk⟩

/-- the state `(A, U)` of every slot role after `k` sub-stages (start `A0 d j`, `U = ∅`). -/
def stSH (hinj : ∀ k < K, OneUse use k)
    (hWn : ∀ k < K, ∀ d q, ∃ (C C' : CMat α) (R : Finset α), Free C ∧ Free C' ∧ R.card = r q ∧
      Wn k d q = C * pk R * C')
    (A0 : Γ → J → CMat α) (hA0 : ∀ d j, Free (A0 d j)) (d : Γ) (j : J) :
    (k : ℕ) → {p : CMat α × Finset α // InvH use r D K d j k p}
  | 0 => ⟨(A0 d j, ∅), hA0 d j, Finset.empty_subset _, fun _ _ => by rw [LH_zero]; rfl⟩
  | k + 1 =>
    let t := Classical.choose (stepH_ex' use r Wn B D K hinj hWn k d j (stSH hinj hWn A0 hA0 d j k))
    have ht := Classical.choose_spec (stepH_ex' use r Wn B D K hinj hWn k d j (stSH hinj hWn A0 hA0 d j k))
    ⟨(t.2.1, t.2.2), ht.1, ht.2.1, ht.2.2.1⟩

/-- the step of sub-stage `k`. -/
def stTH (hinj : ∀ k < K, OneUse use k)
    (hWn : ∀ k < K, ∀ d q, ∃ (C C' : CMat α) (R : Finset α), Free C ∧ Free C' ∧ R.card = r q ∧
      Wn k d q = C * pk R * C')
    (A0 : Γ → J → CMat α) (hA0 : ∀ d j, Free (A0 d j)) (d : Γ) (j : J) (k : ℕ) : CMat α × CMat α × Finset α :=
  Classical.choose (stepH_ex' use r Wn B D K hinj hWn k d j (stSH use r Wn B D K hinj hWn A0 hA0 d j k))

lemma stTH_spec (hinj : ∀ k < K, OneUse use k)
    (hWn : ∀ k < K, ∀ d q, ∃ (C C' : CMat α) (R : Finset α), Free C ∧ Free C' ∧ R.card = r q ∧
      Wn k d q = C * pk R * C')
    (A0 : Γ → J → CMat α) (hA0 : ∀ d j, Free (A0 d j)) (d : Γ) (j : J) (k : ℕ) (hk : k < K)
    (hb : LH use r (k + 1) j ≤ (D d j).card) :
    StepOkH use r Wn B D k d j (stSH use r Wn B D K hinj hWn A0 hA0 d j k).1.1
      (stSH use r Wn B D K hinj hWn A0 hA0 d j k).1.2 (stTH use r Wn B D K hinj hWn A0 hA0 d j k) :=
  (Classical.choose_spec (stepH_ex' use r Wn B D K hinj hWn k d j
    (stSH use r Wn B D K hinj hWn A0 hA0 d j k))).2.2.2 hk hb

lemma stSH_succ (hinj : ∀ k < K, OneUse use k)
    (hWn : ∀ k < K, ∀ d q, ∃ (C C' : CMat α) (R : Finset α), Free C ∧ Free C' ∧ R.card = r q ∧
      Wn k d q = C * pk R * C')
    (A0 : Γ → J → CMat α) (hA0 : ∀ d j, Free (A0 d j)) (d : Γ) (j : J) (k : ℕ) :
    (stSH use r Wn B D K hinj hWn A0 hA0 d j (k + 1)).1 =
      ((stTH use r Wn B D K hinj hWn A0 hA0 d j k).2.1, (stTH use r Wn B D K hinj hWn A0 hA0 d j k).2.2) := rfl

/-- **The frames of a family of slot roles (banks and hosts) over a partial schedule.**  Slot role `j` of class
`d` starts at `X0 d j = A0 d j * B d j` (`A0` free) and ends at `X1 d j = Q d j * pk (D d j) * B d j`; every use
adds the residual of the slot inside `D d j`; the end is ONE block of rank `|D d j| - load`. -/
theorem slot_frames (hinj : ∀ k < K, OneUse use k)
    (hWn : ∀ k < K, ∀ d q, ∃ (C C' : CMat α) (R : Finset α), Free C ∧ Free C' ∧ R.card = r q ∧
      Wn k d q = C * pk R * C')
    (A0 Q : Γ → J → CMat α) (hA0 : ∀ d j, Free (A0 d j)) (hQ : ∀ d j, Free (Q d j))
    (hload : ∀ d j, LH use r K j ≤ (D d j).card)
    (hrk : ∀ d j, (D d j).card - LH use r K j < Fintype.card α) :
    ∃ (Zb Zp : ℕ → Γ → J → CMat α),
      (∀ d j, Zb 0 d j = A0 d j * B d j) ∧
      (∀ k < K, ∀ d j, GReach (Zb k d j) (Zp k d j) (fun _ => 0)) ∧
      (∀ k < K, ∀ d q j, use k q = some j → Wn k d q * Zp k d j = Zb (k + 1) d j) ∧
      (∀ k < K, ∀ d j, (∀ q, use k q ≠ some j) → Zb (k + 1) d j = Zp k d j) ∧
      (∀ d j, GReach (Zb K d j) (Q d j * pk (D d j) * B d j)
        (fun φ => bcost φ ((D d j).card - LH use r K j))) := by
  let S := stSH use r Wn B D K hinj hWn A0 hA0
  let T := stTH use r Wn B D K hinj hWn A0 hA0
  have hb' : ∀ k < K, ∀ d j, LH use r (k + 1) j ≤ (D d j).card := fun k hk d j =>
    le_trans (LH_mono use r (Nat.succ_le_of_lt hk) j) (hload d j)
  refine ⟨fun k d j => (S d j k).1.1 * pk (S d j k).1.2 * B d j,
    fun k d j => (T d j k).1 * ((S d j k).1.1 * pk (S d j k).1.2 * B d j), ?_, ?_, ?_, ?_, ?_⟩
  · intro d j
    show A0 d j * pk ∅ * B d j = A0 d j * B d j
    rw [pk_empty, Matrix.mul_one]
  · intro k hk d j
    have h := (stTH_spec use r Wn B D K hinj hWn A0 hA0 d j k hk (hb' k hk d j)).1
    exact fun ρ _ _ l => gstep_free h l _
  · intro k hk d q j hq
    have h := (stTH_spec use r Wn B D K hinj hWn A0 hA0 d j k hk (hb' k hk d j)).2.2.2.2.1 q hq
    show Wn k d q * ((T d j k).1 * ((S d j k).1.1 * pk (S d j k).1.2 * B d j))
      = (S d j (k + 1)).1.1 * pk (S d j (k + 1)).1.2 * B d j
    rw [h, stSH_succ]
  · intro k hk d j hn
    have h := (stTH_spec use r Wn B D K hinj hWn A0 hA0 d j k hk (hb' k hk d j)).2.2.2.2.2 hn
    show (S d j (k + 1)).1.1 * pk (S d j (k + 1)).1.2 * B d j
      = (T d j k).1 * ((S d j k).1.1 * pk (S d j k).1.2 * B d j)
    rw [stSH_succ, h.1, Matrix.one_mul, ← h.2]
  · intro d j
    have hA := (S d j K).2.1
    have hUD := (S d j K).2.2.1
    have hU : (S d j K).1.2.card = LH use r K j := (S d j K).2.2.2 le_rfl (hload d j)
    have h := host_pad hA (hQ d j) (B d j) (D d j) (S d j K).1.2 hUD (by rw [hU]; exact hrk d j)
    rw [hU] at h
    exact h

end Sched

section Host
variable {α Γ Sl J : Type} [Fintype α] [DecidableEq α] [Fintype Sl] [DecidableEq Sl] [DecidableEq J]

/-- **Hosting, end to end.**  If every slot role's idle climb has host form `X1 = Q * pk D * Q' * X0` (rank
`rk j`) and its load fits, the slot roles have frames from `X0` to `X1`: free adapters, the hosted residuals, and ONE
remaining block of rank `rk j - load` each. -/
theorem host_frames (use : ℕ → Sl → Option J) (r : Sl → ℕ) (Wn : ℕ → Γ → Sl → CMat α) (K : ℕ)
    (hinj : ∀ k < K, OneUse use k)
    (hWn : ∀ k < K, ∀ d q, ∃ (C C' : CMat α) (R : Finset α), Free C ∧ Free C' ∧ R.card = r q ∧
      Wn k d q = C * pk R * C')
    (X0 X1 : Γ → J → CMat α) (rk : J → ℕ) (hform : ∀ d j, HostForm (X0 d j) (X1 d j) (rk j))
    (hload : ∀ j, LH use r K j ≤ rk j) (hrk : ∀ j, rk j - LH use r K j < Fintype.card α) :
    ∃ (Zb Zp : ℕ → Γ → J → CMat α),
      (∀ d j, Zb 0 d j = X0 d j) ∧
      (∀ k < K, ∀ d j, GReach (Zb k d j) (Zp k d j) (fun _ => 0)) ∧
      (∀ k < K, ∀ d q j, use k q = some j → Wn k d q * Zp k d j = Zb (k + 1) d j) ∧
      (∀ k < K, ∀ d j, (∀ q, use k q ≠ some j) → Zb (k + 1) d j = Zp k d j) ∧
      (∀ d j, GReach (Zb K d j) (X1 d j) (fun φ => bcost φ (rk j - LH use r K j))) := by
  simp only [HostForm] at hform
  choose Q Q' D hQ hQ' hD hX using hform
  have hQ'i : ∀ d j, ∃ Ai : CMat α, Free Ai ∧ Ai * Q' d j = 1 := fun d j => by
    obtain ⟨Ai, hAi, h1, -⟩ := free_inv (hQ' d j)
    exact ⟨Ai, hAi, h1⟩
  choose A0 hA0 hA0Q using hQ'i
  obtain ⟨Zb, Zp, h0, hP, hU, hN, hE⟩ := slot_frames use r Wn (fun d j => Q' d j * X0 d j) D K hinj hWn A0 Q hA0 hQ
    (fun d j => by rw [hD]; exact hload j) (fun d j => by rw [hD]; exact hrk j)
  refine ⟨Zb, Zp, fun d j => ?_, hP, hU, hN, fun d j => ?_⟩
  · rw [h0, ← Matrix.mul_assoc, hA0Q, Matrix.one_mul]
  · have h := hE d j
    have e : Q d j * pk (D d j) * (Q' d j * X0 d j) = X1 d j := by
      rw [hX]; simp only [Matrix.mul_assoc]
    rw [e, hD] at h
    exact h

end Host
end
end XHost
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.XHost.hostForm_frame
#print axioms OAI.PowerSaving.XHost.host_adapt
#print axioms OAI.PowerSaving.XHost.host_pad
#print axioms OAI.PowerSaving.XHost.slot_frames
#print axioms OAI.PowerSaving.XHost.host_frames
