import Submission.Work.GFrame.Engine.Over
-- changed for the tensor-power extension (30103/10000000); see Submission.lean

/-!
# P4-L, part 1: the operator semantics of generalised words

The p4 keep303 controller (boundary adapters, terminal windows of pairs 0 and 1 omitted) is exact only as an
OPERATOR identity: its final bridges mix roles whose frames differ, so the frame-route calculus (`GRoute`, gates
between equal frames) cannot certify it directly.  This file gives the three generic tools of the operator form:

* `gwalk_add`, `gwalk_zero`: the semantics of a word is additive (every letter acts linearly);
* `GRoute.op`: a route whose start matrices are invertible acts on EVERY data as `T ∘ g ∘ S⁻¹`
  (so the provider's stage routes, the host chains and the gates all have an operator form);
* `walsh`, `walsh_matAct_wrap`: in Walsh coordinates (`walI` on every digit) a Walsh-diagonal matrix `wrap φ` acts as
  the POINTWISE product with `prodF φ = fun y => ∏ i, φ (y i)`.  Frames (`frameM`), blocks (`blockMat`), the kernel
  and the free shifts are all Walsh-diagonal, so on the main data the whole controller becomes an identity in the
  commutative ring `Sky α f → ℂ` (`P4Ctrl.ctrl_diag`).

No `sorry`.
-/

set_option linter.unusedSectionVars false

namespace OAI
namespace PowerSaving
namespace P4L
open Binary Matrix Finset GF

noncomputable section

section Lin
variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

lemma matAct_add (f : ℕ) (M : CMat α) (x y : Sky α f → ℂ) :
    matAct f M (x + y) = matAct f M x + matAct f M y := by
  unfold matAct; exact Matrix.mulVec_add _ _ _

lemma matAct_zero (f : ℕ) (M : CMat α) : matAct f M (0 : Sky α f → ℂ) = 0 := by
  unfold matAct; exact Matrix.mulVec_zero _

lemma roleAct_add (f : ℕ) (r : ρ) (M : CMat α) (x y : Data α ρ f) :
    roleAct f r M (x + y) = roleAct f r M x + roleAct f r M y := by
  funext j
  simp only [roleAct, Pi.add_apply]
  split_ifs <;> first | exact matAct_add f M _ _ | rfl

lemma roleAct_zero (f : ℕ) (r : ρ) (M : CMat α) : roleAct f r M (0 : Data α ρ f) = 0 := by
  funext j
  simp only [roleAct, Pi.zero_apply]
  split_ifs <;> first | exact matAct_zero f M | rfl

lemma point_actPoint_add (f : ℕ) (g : Matrix ρ ρ ℚ) (x y : Data α ρ f) :
    point f (actPoint g) (x + y) = point f (actPoint g) x + point f (actPoint g) y := by
  funext r i
  simp only [point, actPoint, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma point_actPoint_zero (f : ℕ) (g : Matrix ρ ρ ℚ) :
    point f (actPoint g) (0 : Data α ρ f) = 0 := by
  funext r i
  simp only [point, actPoint, Pi.zero_apply, mul_zero, Finset.sum_const_zero]

lemma BMove.act_add (f : ℕ) (mv : BMove α ρ) (x y : Data α ρ f) :
    mv.act f (x + y) = mv.act f x + mv.act f y := by
  cases mv with
  | localM g => exact point_actPoint_add f g x y
  | shift l z => exact roleAct_add f l _ x y
  | block l rk z ind => exact roleAct_add f l _ x y

lemma BMove.act_zero (f : ℕ) (mv : BMove α ρ) : mv.act f (0 : Data α ρ f) = 0 := by
  cases mv with
  | localM g => exact point_actPoint_zero f g
  | shift l z => exact roleAct_zero f l _
  | block l rk z ind => exact roleAct_zero f l _

lemma GMove.act_add (f : ℕ) (mv : GMove α ρ) (x y : Data α ρ f) :
    mv.act f (x + y) = mv.act f x + mv.act f y := by
  cases mv with
  | old mv => exact BMove.act_add f mv x y
  | perm l G => exact roleAct_add f l _ x y
  | phase l z c => exact roleAct_add f l _ x y

lemma GMove.act_zero (f : ℕ) (mv : GMove α ρ) : mv.act f (0 : Data α ρ f) = 0 := by
  cases mv with
  | old mv => exact BMove.act_zero f mv
  | perm l G => exact roleAct_zero f l _
  | phase l z c => exact roleAct_zero f l _

/-- **The semantics of a word is additive.** -/
theorem gwalk_add (f : ℕ) (w : GWord α ρ) (x y : Data α ρ f) :
    gwalk f w (x + y) = gwalk f w x + gwalk f w y := by
  induction w generalizing x y with
  | nil => rfl
  | cons mv w ih =>
    rw [gwalk_cons, gwalk_cons, gwalk_cons, GMove.act_add, ih]

theorem gwalk_zero (f : ℕ) (w : GWord α ρ) : gwalk f w (0 : Data α ρ f) = 0 := by
  induction w with
  | nil => rfl
  | cons mv w ih => rw [gwalk_cons, GMove.act_zero, ih]

end Lin

section Op
variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

/-- **A route is an operator identity.**  If the start matrices are invertible (`S r * S' r = 1`), the word of the
route acts on EVERY data (not only on data in the start frames) as `T ∘ g ∘ S⁻¹`. -/
theorem _root_.OAI.PowerSaving.GF.GRoute.op {S S' T : ρ → CMat α} {g : (ρ → ℂ) → (ρ → ℂ)}
    {c : (ℕ → ℝ) → ℝ} (h : GRoute S T g c) (hS : ∀ r, S r * S' r = 1) :
    ∃ w : GWord α ρ, w.Proper (Fintype.card α) ∧ (∀ φ, w.costR φ = c φ) ∧
      ∀ (f : ℕ) (y : Data α ρ f), gwalk f w y = multiAct f T (point f g (multiAct f S' y)) := by
  obtain ⟨w, hw, hc, hwalk⟩ := h
  refine ⟨w, hw, hc, fun f y => ?_⟩
  have hy : multiAct f S (multiAct f S' y) = y := by
    funext r
    simp only [multiAct, matAct_mul, hS, matAct_one]
  conv_lhs => rw [← hy]
  exact hwalk f (multiAct f S' y)

/-- the operator form of a route on ONE word (the word of the route is fixed by `hwalk`). -/
theorem op_of_walk {S S' T : ρ → CMat α} {g : (ρ → ℂ) → (ρ → ℂ)} {w : GWord α ρ}
    (hwalk : ∀ (f : ℕ) (x : Data α ρ f), gwalk f w (multiAct f S x) = multiAct f T (point f g x))
    (hS : ∀ r, S r * S' r = 1) (f : ℕ) (y : Data α ρ f) :
    gwalk f w y = multiAct f T (point f g (multiAct f S' y)) := by
  have hy : multiAct f S (multiAct f S' y) = y := by
    funext r
    simp only [multiAct, matAct_mul, hS, matAct_one]
  conv_lhs => rw [← hy]
  exact hwalk f (multiAct f S' y)

end Op

section Walsh
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Walsh coordinates of the data of one role: `walI` on every digit. -/
def walsh (f : ℕ) (x : Sky α f → ℂ) : Sky α f → ℂ :=
  digitProd (fun _ : Fin f => walI α) *ᵥ x

/-- back from Walsh coordinates. -/
def unwalsh (f : ℕ) (x : Sky α f → ℂ) : Sky α f → ℂ :=
  digitProd (fun _ : Fin f => wal α) *ᵥ x

/-- the digit-wise product of a function on the label space. -/
def prodF (f : ℕ) (φ : Space α → ℂ) : Sky α f → ℂ := fun y => ∏ i, φ (y i)

lemma unwalsh_walsh (f : ℕ) (x : Sky α f → ℂ) : unwalsh f (walsh f x) = x := by
  unfold unwalsh walsh
  rw [Matrix.mulVec_mulVec, digitProd_mul]
  simp_rw [wal_right α]
  rw [digitProd_one, Matrix.one_mulVec]

lemma walsh_unwalsh (f : ℕ) (x : Sky α f → ℂ) : walsh f (unwalsh f x) = x := by
  unfold unwalsh walsh
  rw [Matrix.mulVec_mulVec, digitProd_mul]
  simp_rw [wal_left α]
  rw [digitProd_one, Matrix.one_mulVec]

lemma walsh_injective (f : ℕ) : Function.Injective (walsh (α := α) f) := by
  intro x y h
  rw [← unwalsh_walsh f x, h, unwalsh_walsh]

lemma walsh_add (f : ℕ) (x y : Sky α f → ℂ) : walsh f (x + y) = walsh f x + walsh f y := by
  unfold walsh; exact Matrix.mulVec_add _ _ _

lemma walsh_smul (f : ℕ) (c : ℂ) (x : Sky α f → ℂ) : walsh f (c • x) = c • walsh f x := by
  unfold walsh; exact Matrix.mulVec_smul _ _ _

lemma walsh_sub (f : ℕ) (x y : Sky α f → ℂ) : walsh f (x - y) = walsh f x - walsh f y := by
  unfold walsh; exact Matrix.mulVec_sub _ _ _

lemma walsh_neg (f : ℕ) (x : Sky α f → ℂ) : walsh f (-x) = -walsh f x := by
  unfold walsh; exact Matrix.mulVec_neg _ _

lemma walsh_zero (f : ℕ) : walsh f (0 : Sky α f → ℂ) = 0 := by
  unfold walsh; exact Matrix.mulVec_zero _

/-- **A Walsh-diagonal matrix acts in Walsh coordinates as a pointwise product.** -/
theorem walsh_matAct_wrap (f : ℕ) (φ : Space α → ℂ) (x : Sky α f → ℂ) :
    walsh f (matAct f (wrap φ) x) = prodF f φ * walsh f x := by
  unfold walsh matAct
  rw [Matrix.mulVec_mulVec, digitProd_mul]
  have e : walI α * wrap φ = diagonal φ * walI α := by
    unfold wrap
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, wal_left α, Matrix.one_mul]
  simp_rw [e]
  rw [← digitProd_mul, ← Matrix.mulVec_mulVec, digitProd_diagonal]
  funext y
  simp only [Matrix.mulVec_diagonal, Pi.mul_apply, prodF]

lemma prodF_mul (f : ℕ) (φ ψ : Space α → ℂ) : prodF f (fun x => φ x * ψ x) = prodF f φ * prodF f ψ := by
  funext y
  simp only [prodF, Pi.mul_apply, Finset.prod_mul_distrib]

lemma prodF_one (f : ℕ) : prodF f (fun _ : Space α => (1 : ℂ)) = 1 := by
  funext y
  simp only [prodF, Finset.prod_const_one, Pi.one_apply]

end Walsh

end
end P4L
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.P4L.gwalk_add
#print axioms OAI.PowerSaving.GF.GRoute.op
#print axioms OAI.PowerSaving.P4L.walsh_matAct_wrap
