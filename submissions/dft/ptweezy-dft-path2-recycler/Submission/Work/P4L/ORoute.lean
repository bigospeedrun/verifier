import Submission.Work.GFrame.Top.Api
import Submission.Work.P4L.OpSem
-- changed for the tensor-power extension (30103/10000000); see Submission.lean

/-!
# P4-L, part 3: operator routes

`ORoute Op c`: a proper generalised word of exact price `c` whose semantics IS the explicit operator `Op` (on every
data, at every column count).  Unlike a frame route (`GRoute`) it has no frames, so routes compose whatever the
frames of the roles are (`ORoute.trans`); this is what the boundary adapters of the p4 keep303 controller need.

* `ORoute.refl`, `ORoute.trans`, `ORoute.cast`;
* `ORoute.of_groute`   a frame route with invertible start matrices is an operator route
                       (`T ∘ g ∘ S⁻¹`, `GRoute.op`);
* `ORoute.localM`      a gate letter (one rational matrix on all roles, free);
* `ORoute.of_gstep`    a generalised step on one role (`roleAct l U`);
* `ORoute.reach`       every role moves by its own `GReach` (`GRoute.reach_all`, then `of_groute`): the operator
                       on role `r` is `T r * S' r`.
No `sorry`.
-/

set_option linter.unusedSectionVars false

namespace OAI
namespace PowerSaving
namespace P4L
open Binary Matrix Finset GF

noncomputable section

section
variable {α ρ : Type} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

/-- **An operator route**: a proper word of exact price `c` acting as `Op`. -/
def ORoute (Op : ∀ f : ℕ, Data α ρ f → Data α ρ f) (c : (ℕ → ℝ) → ℝ) : Prop :=
  ∃ w : GWord α ρ, w.Proper (Fintype.card α) ∧ (∀ φ, w.costR φ = c φ) ∧
    ∀ (f : ℕ) (y : Data α ρ f), gwalk f w y = Op f y

namespace ORoute

theorem refl : ORoute (α := α) (ρ := ρ) (fun _ y => y) (fun _ => 0) :=
  ⟨[], GWord.proper_nil _, fun _ => rfl, fun _ _ => rfl⟩

theorem trans {Op Op' : ∀ f : ℕ, Data α ρ f → Data α ρ f} {c c' : (ℕ → ℝ) → ℝ}
    (a : ORoute Op c) (b : ORoute Op' c') :
    ORoute (fun f y => Op' f (Op f y)) (fun φ => c φ + c' φ) := by
  obtain ⟨p, hp, cp, ap⟩ := a
  obtain ⟨q, hq, cq, aq⟩ := b
  refine ⟨p ++ q, hp.append hq, fun φ => by rw [GWord.costR_append, cp, cq], ?_⟩
  intro f y
  rw [gwalk_append, ap, aq]

theorem cast {Op Op' : ∀ f : ℕ, Data α ρ f → Data α ρ f} {c c' : (ℕ → ℝ) → ℝ}
    (a : ORoute Op c) (hOp : ∀ f y, Op f y = Op' f y) (hc : ∀ φ, c φ = c' φ) : ORoute Op' c' := by
  obtain ⟨w, hw, hcw, aw⟩ := a
  exact ⟨w, hw, fun φ => (hcw φ).trans (hc φ), fun f y => (aw f y).trans (hOp f y)⟩

/-- a frame route with invertible start matrices is an operator route. -/
theorem of_groute {S S' T : ρ → CMat α} {g : (ρ → ℂ) → (ρ → ℂ)} {c : (ℕ → ℝ) → ℝ}
    (h : GRoute S T g c) (hS : ∀ r, S r * S' r = 1) :
    ORoute (fun f y => multiAct f T (point f g (multiAct f S' y))) c := by
  obtain ⟨w, hw, hc, hwalk⟩ := h
  exact ⟨w, hw, hc, fun f y => op_of_walk hwalk hS f y⟩

/-- a gate letter: one rational matrix on all roles, free. -/
theorem localM (G : Matrix ρ ρ ℚ) : ORoute (α := α) (fun f => point f (actPoint G)) (fun _ => 0) :=
  ⟨[GMove.old (BMove.localM G)], fun mv hmv => by
      rw [List.mem_singleton] at hmv; subst hmv; trivial,
    fun φ => by simp [GWord.costR, GMove.costR, GMove.shadow, BMove.costR, BMove.rk?], fun f y => rfl⟩

/-- a generalised step on one role. -/
theorem of_gstep {l : ρ} {M N : CMat α} {c : (ℕ → ℝ) → ℝ} (h : GStep l M N c) :
    ∃ U : CMat α, U * M = N ∧ ORoute (fun f => roleAct f l U) c := by
  obtain ⟨w, U, hw, hc, hU, hwalk⟩ := h
  exact ⟨U, hU, w, hw, hc, hwalk⟩

/-- **every role moves by its own `GReach`**: the operator on role `r` is `T r * S' r`. -/
theorem reach (S S' T : ρ → CMat α) (hS : ∀ r, S r * S' r = 1) (c : ρ → (ℕ → ℝ) → ℝ)
    (h : ∀ r, GReach (S r) (T r) (c r)) :
    ORoute (fun f y r => matAct f (T r * S' r) (y r)) (fun φ => ∑ r, c r φ) := by
  have R := GRoute.reach_all S T c h
  refine (of_groute R hS).cast (fun f y => ?_) (fun _ => rfl)
  show multiAct f T (point f id (multiAct f S' y)) = fun r => matAct f (T r * S' r) (y r)
  have e : point f id (multiAct f S' y) = multiAct f S' y := rfl
  rw [e]
  funext r
  simp only [multiAct, matAct_mul]

/-- **every role of `s` moves by its own generalised step** (the other roles stay): the operator on `r ∈ s` is a
matrix `U r` with `U r * A r = B r`. -/
theorem steps (s : Finset ρ) (A B : ρ → CMat α) (c : ρ → (ℕ → ℝ) → ℝ)
    (h : ∀ r ∈ s, GStep r (A r) (B r) (c r)) :
    ∃ U : ρ → CMat α, (∀ r ∈ s, U r * A r = B r) ∧
      ORoute (fun f y r => if r ∈ s then matAct f (U r) (y r) else y r) (fun φ => ∑ r ∈ s, c r φ) := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨fun _ => 1, fun r hr => absurd hr (Finset.notMem_empty r), ?_⟩
    exact refl.cast (fun f y => by funext r; simp) (fun φ => by simp)
  | insert a s ha ih =>
    obtain ⟨U, hU, R⟩ := ih (fun r hr => h r (Finset.mem_insert_of_mem hr))
    obtain ⟨Ua, hUa, Ra⟩ := of_gstep (h a (Finset.mem_insert_self a s))
    refine ⟨Function.update U a Ua, fun r hr => ?_, ?_⟩
    · rcases Finset.mem_insert.mp hr with e | hr
      · subst e; rw [Function.update_self]; exact hUa
      · have hra : r ≠ a := fun e => ha (e ▸ hr)
        rw [Function.update_of_ne hra]; exact hU r hr
    · refine (R.trans Ra).cast (fun f y => ?_) (fun φ => by rw [Finset.sum_insert ha, add_comm])
      funext r
      simp only [roleAct]
      by_cases hra : r = a
      · subst hra
        simp [ha, Function.update_self]
      · have e1 : (r ∈ insert a s) = (r ∈ s) := by
          simp [Finset.mem_insert, hra]
        simp only [hra, if_false, e1, Function.update_of_ne hra]

/-- `steps` with invertible start matrices: the operator is explicit, `B r * A' r` on `r ∈ s`. -/
theorem steps_inv (s : Finset ρ) (A A' B : ρ → CMat α) (hA : ∀ r ∈ s, A r * A' r = 1) (c : ρ → (ℕ → ℝ) → ℝ)
    (h : ∀ r ∈ s, GStep r (A r) (B r) (c r)) :
    ORoute (fun f y r => if r ∈ s then matAct f (B r * A' r) (y r) else y r) (fun φ => ∑ r ∈ s, c r φ) := by
  obtain ⟨U, hU, R⟩ := steps s A B c h
  refine R.cast (fun f y => ?_) (fun _ => rfl)
  funext r
  by_cases hr : r ∈ s
  · have e : U r = B r * A' r := by
      rw [← hU r hr, Matrix.mul_assoc, hA r hr, Matrix.mul_one]
    simp only [hr, if_true, e]
  · simp only [hr, if_false]

end ORoute
end
end
end P4L
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.P4L.ORoute.trans
#print axioms OAI.PowerSaving.P4L.ORoute.reach
