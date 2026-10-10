import Submission.Work.GFrame.Engine.Free

/-!
# GFrame engine, part 12: free matrices of a fibre; the twisted block (agent key: eng-ram)

A free matrix on the block coordinates of a splitting, lifted to the label space, is free:

* `Split.liftPerm`, `Split.lift_permMat_split`   lifted address permutation;
* `Split.lift_phaseMat`                    lifted diagonal phase (`functional_dot`: every
                                           additive functional is `dot z'`);
* `Free.lift`          `Free A → Free (S.lift A)`;
* `Split.dirs`, `Split.dirs_indep`   the block directions of a splitting are independent;
* `gstep_of_lift`      `A * S.lift (kernel (Fin rk)) * B` with `A`, `B` free = ONE block;
* `gstep_twisted`      **twisted block**: `S.lift (L * kernel (Fin rk) * R)` with `L`, `R` free
                       matrices OF THE FIBRE is ONE block of rank `rk` (stage A's letter).
-/

set_option linter.unusedSectionVars false

namespace OAI
namespace PowerSaving.GF
open Binary Matrix Finset RAM
noncomputable section
section
variable {α β γ ρ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ] [Fintype ρ] [DecidableEq ρ]

/-- Every additive functional on the label space is `dot z'`. -/
lemma functional_dot (g : Space α → F) (hg : ∀ x y, g (x+y) = g x + g y) (x : Space α) :
    dot (fun a => g (eu a)) x = g x := by
  rw [additive_functional g hg x, Finset.sum_filter]
  unfold dot
  apply Finset.sum_congr rfl
  intro a _
  rcases bit_cases (g (eu a)) with h|h <;> simp [h]

/-- An additive bijection of the block coordinates, acting on the label space. -/
def _root_.OAI.PowerSaving.Binary.Split.liftPerm (S : Split α β γ) (G : APerm γ) : APerm α where
  π :=
    { toFun := fun x => S.e.symm ((S.e x).1, G.π (S.e x).2)
      invFun := fun x => S.e.symm ((S.e x).1, G.π.symm (S.e x).2)
      left_inv := fun x => by simp
      right_inv := fun x => by simp }
  add := by
    intro x y
    change S.e.symm ((S.e (x+y)).1, G.π (S.e (x+y)).2)
      = S.e.symm ((S.e x).1, G.π (S.e x).2) + S.e.symm ((S.e y).1, G.π (S.e y).2)
    rw [← S.symm_add, S.add]
    congr 1
    exact Prod.ext rfl (G.add _ _)

lemma lift_permMat_split (S : Split α β γ) (G : APerm γ) :
    S.lift (permMat G) = permMat (S.liftPerm G) := by
  ext x y
  change (if (S.e x).1 = (S.e y).1 then (if G.π (S.e x).2 = (S.e y).2 then (1:ℂ) else 0) else 0)
     = if S.e.symm ((S.e x).1, G.π (S.e x).2) = y then 1 else 0
  have key : S.e.symm ((S.e x).1, G.π (S.e x).2) = y ↔
      (S.e x).1 = (S.e y).1 ∧ G.π (S.e x).2 = (S.e y).2 := by
    rw [Equiv.symm_apply_eq]
    constructor
    · intro h; rw [← h]; exact ⟨rfl, rfl⟩
    · intro h; exact Prod.ext h.1 h.2
  by_cases h1 : (S.e x).1 = (S.e y).1
  · by_cases h2 : G.π (S.e x).2 = (S.e y).2
    · rw [if_pos h1, if_pos h2, if_pos (key.2 ⟨h1,h2⟩)]
    · rw [if_pos h1, if_neg h2, if_neg (fun h => h2 (key.1 h).2)]
  · rw [if_neg h1, if_neg (fun h => h1 (key.1 h).1)]

lemma lift_phaseMat (S : Split α β γ) (z : Space γ) (c : F) :
    S.lift (phaseMat z c) = phaseMat (fun a => dot z (S.e (eu a)).2) c := by
  ext x y
  have hd : dot (fun a => dot z (S.e (eu a)).2) x = dot z (S.e x).2 :=
    functional_dot (fun x => dot z (S.e x).2)
      (fun p q => by rw [S.add]; exact dot_add_right z _ _) x
  simp only [Split.lift, phaseMat, Matrix.diagonal_apply]
  rw [hd]
  by_cases hxy : x = y
  · subst hxy; simp
  · by_cases h1 : (S.e x).1 = (S.e y).1
    · have h2 : (S.e x).2 ≠ (S.e y).2 := fun h2 => hxy (S.e.injective (Prod.ext h1 h2))
      simp [h1, h2, hxy]
    · simp [h1, hxy]

/-- **A free matrix of the fibre is free on the label space.** -/
theorem Free.lift (S : Split α β γ) {A : CMat γ} (h : Free A) : Free (S.lift A) := by
  induction h with
  | one => rw [S.lift_one]; exact Free.one
  | perm G => rw [lift_permMat_split]; exact Free.perm _
  | phase z c => rw [lift_phaseMat]; exact Free.phase _ _
  | shift z => rw [S.lift_shift]; exact Free.shift _
  | mul _ _ ihA ihB => rw [S.lift_mul]; exact Free.mul ihA ihB

variable {rk : ℕ}

/-- The block directions of a splitting. -/
def _root_.OAI.PowerSaving.Binary.Split.dirs (S : Split α β (Fin rk)) (i : Fin rk) : Space α :=
  S.e.symm (0, eu i)

lemma dirs_indep (S : Split α β (Fin rk)) : LinearIndependent F S.dirs := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h1 : ∀ j, g j • S.dirs j = S.e.symm ((0:Space β), g j • (eu j : Space (Fin rk))) := by
    intro j
    rcases bit_cases (g j) with h|h
    · rw [h, zero_smul, zero_smul]
      exact (show S.e.symm ((0:Space β), (0:Space (Fin rk))) = 0 from S.symm_zero).symm
    · rw [h, one_smul, one_smul]; rfl
  have h2 : ∑ j, S.e.symm ((0:Space β), g j • (eu j : Space (Fin rk)))
      = S.e.symm (∑ j, ((0:Space β), g j • (eu j : Space (Fin rk)))) :=
    (map_sum (AddMonoidHom.mk' S.e.symm S.symm_add) _ _).symm
  have h3 : ∑ j, ((0:Space β), g j • (eu j : Space (Fin rk))) = (0, g) := by
    apply Prod.ext
    · rw [Prod.fst_sum]; simp
    · rw [Prod.snd_sum]; funext i; simp [Finset.sum_apply, eu]
  have key : ∑ j, g j • S.dirs j = S.e.symm (0, g) := by
    rw [Finset.sum_congr rfl (fun j _ => h1 j), h2, h3]
  rw [key] at hg
  have h0 : ((0 : Space β), g) = 0 := by
    apply S.e.symm.injective
    rw [hg]; exact S.symm_zero.symm
  exact congrFun (congrArg Prod.snd h0) i

/-- `free * (kernel on the block coordinates of ANY splitting) * free` is ONE block. -/
theorem gstep_of_lift (l : ρ) (M : CMat α) (S : Split α β (Fin rk)) {A B : CMat α}
    (hA : Free A) (hB : Free B) (h1 : 1 ≤ rk) (h2 : rk < Fintype.card α) :
    GStep l M (A * S.lift (kernel (Fin rk)) * B * M) (fun φ => φ rk) :=
  gstep_of_split l M S S.dirs (fun _ => rfl) (dirs_indep S) hA hB h1 h2

/-- **Twisted block.**  The kernel on the block coordinates between two free matrices of the
fibre (coordinate permutation, diagonal fourth roots of unity) is ONE block of rank `rk`. -/
theorem gstep_twisted (l : ρ) (M : CMat α) (S : Split α β (Fin rk)) {L R : CMat (Fin rk)}
    (hL : Free L) (hR : Free R) (h1 : 1 ≤ rk) (h2 : rk < Fintype.card α) :
    GStep l M (S.lift (L * kernel (Fin rk) * R) * M) (fun φ => φ rk) := by
  rw [S.lift_mul, S.lift_mul]
  exact gstep_of_lift l M S (hL.lift S) (hR.lift S) h1 h2

end
end
end PowerSaving.GF
end OAI

#print axioms OAI.PowerSaving.GF.Free.lift
#print axioms OAI.PowerSaving.GF.dirs_indep
#print axioms OAI.PowerSaving.GF.gstep_of_lift
#print axioms OAI.PowerSaving.GF.gstep_twisted
