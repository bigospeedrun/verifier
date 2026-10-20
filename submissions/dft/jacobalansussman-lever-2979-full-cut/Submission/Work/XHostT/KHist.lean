import Submission.Work.XHostT.KWhole
import Submission.Work.XHostT.KHistC

/-!
# (key: bridge-host-cross) Global facts of a kernel host table: the remainder histogram and the residual sums

Small "global parts" next to the per-kind parts of the host check (Work/XHostT/KGlue.lean, KWhole.lean).  The
computable counters are in Work/XHostT/KHistC.lean (core Lean, decided by the kernel in a table's chunk modules); here
is what they mean:

* `cntR_card`: `cntR rt v 0 n` is the number of host indices `i < 224 n` whose remainder `remAt rt i` (p-a3's TSchedK)
  is `v`; `inR_sound`: `inR rt V 0 n = true` means every such remainder lies in `V`;
* `cntR_list`, `inR_list`: chunks of `G` kinds each assemble to the whole range;
* `rem_sum`: with every remainder in `V` (no repeats), the sum of ANY function of the remainders over all host
  indices is `∑ v ∈ V, cntR rt v 0 n • f v` (the form a price lemma needs, e.g. `f = bcost φ`);
* `resS_eq`: `resS resT p m` is the sum of the residuals `resAt resT p q`, `q < m`.
Written by p-hostck (wht45/lever, 19 Oct 2026); prepared with assistance from Claude.  No `sorry`.
-/

namespace OAI.PowerSaving.XHostT.K
open Finset

lemma remAt_kind (rt : CT) (n b : ℕ) (hb : b < 224) : remAt rt (224 * n + b) = fld6 (rt.get n).1 b := by
  have e1 : (224 * n + b) / 224 = n := by omega
  have e2 : (224 * n + b) % 224 = b := by omega
  simp only [remAt, fld6, e1, e2]

lemma bif_beq (a v : ℕ) : (bif Nat.beq a v then 1 else 0) = (if a = v then 1 else 0) := by
  simp only [cond_eq_if, Nat.beq_eq]

lemma cntB_sum (x v : ℕ) : ∀ m, cntB x v m = ∑ b ∈ range m, (if fld6 x b = v then 1 else 0)
  | 0 => by simp [cntB]
  | m + 1 => by rw [cntB, cntB_sum x v m, sum_range_succ, bif_beq]

lemma cntR_sum (rt : CT) (v a : ℕ) : ∀ n,
    cntR rt v a n = ∑ i ∈ range (224 * n), (if remAt rt (224 * a + i) = v then 1 else 0)
  | 0 => by simp [cntR]
  | n + 1 => by
    rw [cntR, cntR_sum rt v a n, show 224 * (n + 1) = 224 * n + 224 by ring, sum_range_add, cntB_sum,
      add_right_inj]
    refine sum_congr rfl (fun b hb => ?_)
    rw [show 224 * a + (224 * n + b) = 224 * (a + n) + b by ring, remAt_kind rt (a + n) b (mem_range.mp hb)]

/-- **what `cntR` counts**. -/
theorem cntR_card (rt : CT) (v n : ℕ) : cntR rt v 0 n = #{i ∈ range (224 * n) | remAt rt i = v} := by
  rw [cntR_sum, card_filter]
  simp only [Nat.mul_zero, Nat.zero_add]

lemma cntR_add (rt : CT) (v a n : ℕ) : ∀ m, cntR rt v a (n + m) = cntR rt v a n + cntR rt v (a + n) m
  | 0 => by simp [cntR]
  | m + 1 => by
    rw [← Nat.add_assoc, cntR, cntR_add rt v a n m, cntR, Nat.add_assoc a n m, Nat.add_assoc]

lemma cntR_list' (rt : CT) (v G : ℕ) : ∀ (cs : List ℕ) (a : ℕ),
    (∀ j < cs.length, cntR rt v (a + G * j) G = cs.getD j 0) → cntR rt v a (G * cs.length) = cs.sum
  | [], a, _ => by simp [cntR]
  | c :: cs, a, h => by
    rw [List.length_cons, Nat.mul_succ, Nat.add_comm (G * cs.length) G, cntR_add, List.sum_cons]
    have h0 := h 0 (by simp)
    simp only [Nat.mul_zero, Nat.add_zero, List.getD_cons_zero] at h0
    rw [h0, cntR_list' rt v G cs (a + G) (fun j hj => ?_)]
    have := h (j + 1) (by simp only [List.length_cons]; omega)
    rw [show a + G * (j + 1) = a + G + G * j by ring, List.getD_cons_succ] at this
    exact this

/-- chunks of `G` kinds with counts `cs` (`k` chunks) give the count of the whole range. -/
theorem cntR_list (rt : CT) (v G : ℕ) (cs : List ℕ) (a k : ℕ) (hk : cs.length = k)
    (h : ∀ j < k, cntR rt v (a + G * j) G = cs.getD j 0) : cntR rt v a (G * k) = cs.sum := by
  subst hk
  exact cntR_list' rt v G cs a h

lemma inB_sound (x : ℕ) (V : List ℕ) : ∀ m, inB x V m = true → ∀ b < m, fld6 x b ∈ V
  | 0, _, b, hb => absurd hb (Nat.not_lt_zero b)
  | m + 1, h, b, hb => by
    simp only [inB, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hb with hb | rfl
    · exact inB_sound x V m h.1 b hb
    · exact List.contains_iff_mem.mp h.2

/-- **what `inR` checks**. -/
theorem inR_sound (rt : CT) (V : List ℕ) (a : ℕ) : ∀ n, inR rt V a n = true → ∀ i < 224 * n, remAt rt (224 * a + i) ∈ V
  | 0, _, i, hi => absurd hi (by omega)
  | n + 1, h, i, hi => by
    simp only [inR, Bool.and_eq_true] at h
    by_cases hlt : i < 224 * n
    · exact inR_sound rt V a n h.1 i hlt
    · obtain ⟨b, rfl, hb⟩ : ∃ b, i = 224 * n + b ∧ b < 224 := ⟨i - 224 * n, by omega, by omega⟩
      rw [show 224 * a + (224 * n + b) = 224 * (a + n) + b by ring, remAt_kind rt (a + n) b hb]
      exact inB_sound _ V 224 h.2 b hb

lemma inR_add (rt : CT) (V : List ℕ) (a n : ℕ) : ∀ m, inR rt V a (n + m) = (inR rt V a n && inR rt V (a + n) m)
  | 0 => by simp [inR]
  | m + 1 => by
    rw [← Nat.add_assoc, inR, inR_add rt V a n m, inR, Nat.add_assoc a n m, Bool.and_assoc]

/-- chunks of `G` kinds, each checked, give the whole range. -/
theorem inR_list (rt : CT) (V : List ℕ) (G : ℕ) : ∀ (k a : ℕ),
    (∀ j < k, inR rt V (a + G * j) G = true) → inR rt V a (G * k) = true
  | 0, a, _ => by simp [inR]
  | k + 1, a, h => by
    rw [Nat.mul_succ, Nat.add_comm (G * k) G, inR_add, Bool.and_eq_true]
    refine ⟨by simpa using h 0 (by omega), inR_list rt V G k (a + G) (fun j hj => ?_)⟩
    have := h (j + 1) (by omega)
    rwa [show a + G * (j + 1) = a + G + G * j by ring] at this

/-- **the remainder histogram**: any function of the remainders, summed over all host indices. -/
theorem rem_sum {M : Type*} [AddCommMonoid M] (rt : CT) (n : ℕ) (V : List ℕ) (hV : V.Nodup)
    (hin : inR rt V 0 n = true) (f : ℕ → M) :
    ∑ i ∈ range (224 * n), f (remAt rt i) = (V.map (fun v => cntR rt v 0 n • f v)).sum := by
  have hmap : ∀ i ∈ range (224 * n), remAt rt i ∈ V.toFinset := by
    intro i hi
    rw [List.mem_toFinset]
    have := inR_sound rt V 0 n hin i (mem_range.mp hi)
    simpa using this
  rw [← sum_fiberwise_of_maps_to' hmap f, ← List.sum_toFinset _ hV]
  refine sum_congr rfl (fun v _ => ?_)
  rw [sum_const, cntR_card]

/-- **the residual sums**. -/
theorem resS_eq (resT p : ℕ) : ∀ m, resS resT p m = ∑ q ∈ range m, resAt resT p q
  | 0 => by simp [resS]
  | m + 1 => by rw [resS, resS_eq resT p m, sum_range_succ]

end OAI.PowerSaving.XHostT.K

#print axioms OAI.PowerSaving.XHostT.K.rem_sum
#print axioms OAI.PowerSaving.XHostT.K.cntR_list
#print axioms OAI.PowerSaving.XHostT.K.inR_list
#print axioms OAI.PowerSaving.XHostT.K.resS_eq
