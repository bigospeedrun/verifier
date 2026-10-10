import Submission.Work.GFrame.Top.Stages

/-!
# GFrame, top (key: eng-integrate): the first certificate through an ARBITRARY subspace

End-to-end test of the chain at certificate level, on one role: the kernel of the whole
address space, reached through ANY intermediate subspace `U` (degenerate and isotropic ones
included; no orthonormal basis, no unit direction), is a generalised certificate paying
exactly two blocks, of ranks `dim U` and `m - dim U`:

    0  --one block of rank dim U-->  U  --one block of rank m - dim U-->  everything.

* `flagSched`, `flagSched_ok`   the two-move schedule and its label-level legality;
* `gcert_through`               the certificate, from `gcert_of_bsched`;
* `gcert_through_submodule`     the same for an arbitrary `Submodule F (Space α)`
                                (`exists_rep`: every subspace has a representative).

The old calculus cannot reach a degenerate `U`: `SS.Climb` moves only between the projectors
`A.mat s` of ONE orthonormal basis.  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.GF
open Binary Matrix Finset RAM CB
noncomputable section
section
variable {α : Type} [Fintype α] [DecidableEq α]

/-- the zero subspace and the full space, in the standard base. -/
def botL (α : Type) [Fintype α] [DecidableEq α] : SLbl α := ⟨apId α, ∅⟩
def topL (α : Type) [Fintype α] [DecidableEq α] : SLbl α := ⟨apId α, univ⟩

lemma botL_dim : (botL α).dim = 0 := by simp [botL, SLbl.dim]
lemma topL_dim : (topL α).dim = Fintype.card α := by simp [topL, SLbl.dim]

lemma botL_sub (U : SLbl α) : ∀ x, (botL α).Mem x → U.Mem x := by
  intro x hx k _
  have h0 : x = 0 := by
    funext j
    exact hx j (Finset.notMem_empty j)
  rw [h0, U.G.map_zero']
  rfl

lemma sub_topL (U : SLbl α) : ∀ x, U.Mem x → (topL α).Mem x :=
  fun x _ k hk => absurd (Finset.mem_univ k) hk

/-- the schedule `0 → U → everything` on one role. -/
def flagSched (U : SLbl α) : List (GSt (SLbl α) Unit) :=
  [.move () U [U.dim], .move () (topL α) [Fintype.card α - U.dim]]

theorem flagSched_ok (U : SLbl α) (h1 : 1 ≤ U.dim) (h2 : U.dim < Fintype.card α) :
    BSchedOk (fun _ : Unit => botL α) (flagSched U) := by
  have a : SMv (Fintype.card α) (botL α) U [U.dim] := by
    have g := SMv.of_sub (m := Fintype.card α) (botL α) U (botL_sub U)
      (by rw [botL_dim]; omega) (by rw [botL_dim]; omega)
    rw [botL_dim] at g
    exact g
  have b : SMv (Fintype.card α) U (topL α) [Fintype.card α - U.dim] := by
    have g := SMv.of_sub (m := Fintype.card α) U (topL α) (sub_topL U)
      (by rw [topL_dim]; omega) (by rw [topL_dim]; omega)
    rw [topL_dim] at g
    exact g
  refine ⟨a, ?_, trivial⟩
  show SMv (Fintype.card α) (Function.update (fun _ : Unit => botL α) () U ()) (topL α) _
  rw [Function.update_self]
  exact b

/-- **The kernel through an arbitrary subspace is a certificate of two blocks.** -/
theorem gcert_through (U : SLbl α) (h1 : 1 ≤ U.dim) (h2 : U.dim < Fintype.card α) :
    GCert α (fun _ : Unit => ()) (fun φ => φ U.dim + φ (Fintype.card α - U.dim)) := by
  have c := gcert_of_bsched (fun _ : Unit => botL α) (flagSched U) (flagSched_ok U h1 h2)
    (fun _ : Unit => ()) (fun _ => rfl) (fun x _ t => rfl)
    (fun t => by
      show SLbl.rep (Function.update (Function.update (fun _ : Unit => botL α) () U) ()
        (topL α) ()) = kernel α
      rw [Function.update_self]
      exact SLbl.rep_full)
  refine c.cast (fun φ => ?_)
  show rcost φ [U.dim, Fintype.card α - U.dim] = _
  rw [rcost_cons, rcost_single, bcost_pos φ (by omega), bcost_pos φ (by omega)]

/-- the same for an arbitrary submodule: some representative `V` of it carries the
certificate (its `dim` is the dimension of the submodule). -/
theorem gcert_through_submodule (U : Submodule F (Space α)) :
    ∃ V : SLbl α, (∀ x, V.Mem x ↔ x ∈ U) ∧
      (1 ≤ V.dim → V.dim < Fintype.card α →
        GCert α (fun _ : Unit => ()) (fun φ => φ V.dim + φ (Fintype.card α - V.dim))) := by
  obtain ⟨G, s, h⟩ := exists_rep U
  exact ⟨⟨G, s⟩, h, fun h1 h2 => gcert_through ⟨G, s⟩ h1 h2⟩

end
end
end PowerSaving.GF
end OAI

#print axioms OAI.PowerSaving.GF.flagSched_ok
#print axioms OAI.PowerSaving.GF.gcert_through
#print axioms OAI.PowerSaving.GF.gcert_through_submodule
