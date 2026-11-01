import Submission.Work.Block.Frames
import Submission.Work.P4L.OpSem
-- changed for the tensor-power extension (30103/10000000); see Submission.lean

/-!
# P4-L, part 4: frames of ONE orthonormal basis as functions

In the leader's geometry every frame a port `(g, t)` meets is a coordinate frame `frame A s` of ONE orthonormal basis
`A = BC.BBC (base t) l g` (Work/BridgeC/Stage: `classT_X0`, `bank_inX`, `classT_X`, ...).  Here the frames of one
basis are handled as their Walsh functions `fr A s = fun x => lum (A.proj s x)` (`frame A s = wrap (fr A s)`):

* `fr_union`        `fr A (c ∪ d) = fr A c * fr A d` for disjoint `c d` (from `OBase.frame_union`);
* `fr_ne_zero`, `frame_mul_unframe`, `unframe_eq`  inverses;
* `walsh_frame`     in Walsh coordinates `frame A s` is the pointwise product with `prodF f (fr A s)`;
* `frame_eq_shift_blockMat`   `frame A s = shift (A.corr s) * blockMat (A.fam s)` (`OBase.deltas_eq`): a frame is a
                    free shift times ONE block of its own lines (this is how a role is normalised to its target);
* `fr_single_inv`   `(fr A {i} x)⁻¹ = fr A {i} x * sign (dot (A.v i) x)`: the inverse of a one-line frame is the
                    frame times a free shift (the `q⁻¹` of the controller).
No `sorry`.
-/

set_option linter.unusedSectionVars false

namespace OAI
namespace PowerSaving
namespace P4L
open Binary Matrix Finset

noncomputable section

section
variable {α : Type} [Fintype α] [DecidableEq α]

/-- the Walsh function of the frame of the lines `s` of `A`. -/
def fr (A : OBase α) (s : Finset α) : Space α → ℂ := fun x => lum (A.proj s x)

lemma frame_eq_wrap (A : OBase α) (s : Finset α) : frame A s = wrap (fr A s) := rfl

lemma unframe_eq_wrap (A : OBase α) (s : Finset α) :
    unframe A s = wrap (fun x => (fr A s x)⁻¹) := rfl

lemma fr_ne_zero (A : OBase α) (s : Finset α) (x : Space α) : fr A s x ≠ 0 := lum_nonzero _

lemma wrap_injective : Function.Injective (wrap (α := α)) := by
  intro f g h
  have hd : ∀ u : Space α → ℂ, diagonal u = walI α * wrap u * wal α := by
    intro u
    unfold wrap
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, wal_left α, Matrix.one_mul, Matrix.mul_assoc, wal_left α,
      Matrix.mul_one]
  have h2 : diagonal f = diagonal g := by rw [hd f, hd g, h]
  funext x
  have := congrFun (congrFun h2 x) x
  simpa using this

lemma frame_eq_deltas (A : OBase α) (d : Finset α) : frame A d = A.deltas d := by
  have h := OBase.frame_union A ∅ d (Finset.disjoint_empty_left d)
  rw [Finset.empty_union, frame_zero, Matrix.mul_one] at h
  exact h

/-- **frames of disjoint sets of lines multiply.** -/
theorem fr_union (A : OBase α) (c d : Finset α) (h : Disjoint c d) :
    fr A (c ∪ d) = fr A c * fr A d := by
  apply wrap_injective
  have e := OBase.frame_union A c d h
  rw [← frame_eq_deltas, frame_eq_wrap, frame_eq_wrap, frame_eq_wrap, wrap_mul] at e
  rw [e]
  congr 1
  funext x
  exact mul_comm _ _

lemma frame_mul_unframe (A : OBase α) (s : Finset α) : frame A s * unframe A s = 1 := unframe_right A s

/-- in Walsh coordinates a frame of `A` is the pointwise product with `prodF f (fr A s)`. -/
lemma walsh_frame (f : ℕ) (A : OBase α) (s : Finset α) (y : Sky α f → ℂ) :
    walsh f (matAct f (frame A s) y) = prodF f (fr A s) * walsh f y :=
  walsh_matAct_wrap f _ y

lemma walsh_unframe (f : ℕ) (A : OBase α) (s : Finset α) (y : Sky α f → ℂ) :
    walsh f (matAct f (unframe A s) y) = prodF f (fun x => (fr A s x)⁻¹) * walsh f y :=
  walsh_matAct_wrap f _ y

lemma prodF_inv_mul (f : ℕ) (A : OBase α) (s : Finset α) :
    prodF f (fun x => (fr A s x)⁻¹) * prodF f (fr A s) = 1 := by
  rw [← prodF_mul]
  have e : (fun x => (fr A s x)⁻¹ * fr A s x) = fun _ => (1 : ℂ) := by
    funext x; exact inv_mul_cancel₀ (fr_ne_zero A s x)
  rw [e, prodF_one]

/-- **a frame is a free shift times ONE block of its own lines.** -/
theorem frame_eq_shift_blockMat (A : OBase α) (s : Finset α) :
    frame A s = shift (A.corr s) * blockMat (A.fam s) := by
  rw [frame_eq_deltas, OBase.deltas_eq]

/-- the inverse of a one-line frame is the frame times a free shift. -/
lemma fr_single_inv (A : OBase α) (i : α) (x : Space α) :
    (fr A {i} x)⁻¹ = fr A {i} x * sign (dot (A.v i) x) := by
  have hp : A.proj {i} x = dot (A.v i) x • A.v i := by
    unfold OBase.proj
    rw [Finset.sum_singleton]
  unfold fr
  rw [hp]
  rcases bit_cases (dot (A.v i) x) with hb | hb
  · rw [hb, zero_smul, lum_zero, inv_one, one_mul]
    simp [sign]
  · have hl := lum_sq (A.v i)
    rw [A.self i] at hl
    have hs : sign (1 : F) = -1 := by simp [sign]
    rw [hs] at hl
    rw [hb, one_smul, hs]
    apply inv_eq_of_mul_eq_one_right
    have e : lum (A.v i) * (lum (A.v i) * -1) = -(lum (A.v i) * lum (A.v i)) := by ring
    rw [e, hl]
    norm_num

end
end
end P4L
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.P4L.fr_union
#print axioms OAI.PowerSaving.P4L.frame_eq_shift_blockMat
#print axioms OAI.PowerSaving.P4L.fr_single_inv
