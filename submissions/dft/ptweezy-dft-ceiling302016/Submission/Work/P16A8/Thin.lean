import Submission.Work.P16A8.View
-- changed for the tensor-power extension (30103/10000000); see Submission.lean

/-!
# P16A8 (p16a8), the THIN query (the one genuinely new segment)

A thin query `Y += Q⁻¹ X` (no stage transform) on every port: the scratch role `(g, j, t)` gets a COPY of `X` (a
free gate, `copyM`), then ONE generalised step `unframe A {p} = shift (A.corr {p}) * blockMat (A.fam {p}) *
shift (A.v p)` (a rank-1 block between two free shifts: `GF.gstep_of_factor`), then `Y += Z` (a free gate, `addM`).
The copy OVERWRITES the scratch, so the operator (`thinOp`) holds on every input; the scratch output is free
(scratch roles are not live).  `thin_route`: price `∑ (g, t) bcost 1`; `view_thin`: the view moves by `shear`;
`thin_fresh`: the helpers are untouched.
No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace OAI
namespace PowerSaving
namespace P16A8
open Binary Matrix Finset RAM SS CB RF BR GF GX XHostTW

noncomputable section

section Thin
variable {α Γ T Sl C : Type} [Fintype α] [DecidableEq α] [Fintype Γ] [DecidableEq Γ] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]

/-- the scratch roles of thin query `j`: one per gauge and port. -/
def zSet (j : Fin 15) : Finset (PRole Γ T Sl C) :=
  (Finset.univ : Finset (Γ × T)).image fun p => zR p.1 j p.2

lemma mem_zSet (j : Fin 15) (r : PRole Γ T Sl C) :
    r ∈ zSet (Γ := Γ) (T := T) (Sl := Sl) (C := C) j ↔ ∃ g t, r = zR g j t := by
  unfold zSet
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨g, t⟩, -, rfl⟩; exact ⟨g, t, rfl⟩
  · rintro ⟨g, t, rfl⟩; exact ⟨(g, t), Finset.mem_univ _, rfl⟩

lemma card_zSet (j : Fin 15) :
    (zSet (Γ := Γ) (T := T) (Sl := Sl) (C := C) j).card = Fintype.card Γ * Fintype.card T := by
  unfold zSet
  rw [Finset.card_image_of_injective _ (fun a b h => by
    simp only [zR, Sum.inr.injEq, Prod.mk.injEq] at h
    exact Prod.ext h.1 h.2.2), Finset.card_univ, Fintype.card_prod]

/-- the copy gate of thin query `j`: every scratch role `(g, j, t)` := `x` of port `(g, t)`; identity elsewhere. -/
def copyM (x : R32) (j : Fin 15) : Matrix (PRole Γ T Sl C) (PRole Γ T Sl C) ℚ := fun r r' =>
  match r with
  | .inr (.inr (g, (j', t))) => if j' = j then (if r' = mainR g x t then 1 else 0) else (if r' = r then 1 else 0)
  | _ => if r' = r then 1 else 0

/-- the add gate of thin query `j`: `y` of port `(g, t)` += the scratch role `(g, j, t)`; identity elsewhere. -/
def addM (y : R32) (j : Fin 15) : Matrix (PRole Γ T Sl C) (PRole Γ T Sl C) ℚ := fun r r' =>
  match r with
  | .inl (.inl (g, (i, t))) =>
      if i = y then (if r' = r then 1 else 0) + (if r' = zR g j t then 1 else 0) else (if r' = r then 1 else 0)
  | _ => if r' = r then 1 else 0

/-- the matrix of the scratch step: `U g t` on the scratch roles (indexwise), `1` elsewhere. -/
def zMat (U : Γ → T → CMat α) : PRole Γ T Sl C → CMat α
  | .inr (.inr (g, (_, t))) => U g t
  | _ => 1

lemma zMat_z (U : Γ → T → CMat α) (g : Γ) (j : Fin 15) (t : T) :
    zMat (Sl := Sl) (C := C) U (zR g j t) = U g t := rfl

/-- **the thin-query operator**: copy gate, the scratch steps of query `j`, add gate. -/
def thinOp (x y : R32) (j : Fin 15) (U : Γ → T → CMat α) (f : ℕ) (v : Data α (PRole Γ T Sl C) f) :
    Data α (PRole Γ T Sl C) f :=
  point f (actPoint (addM y j)) (fun r => if r ∈ zSet (Γ := Γ) (T := T) (Sl := Sl) (C := C) j
    then matAct f (zMat U r * 1) (point f (actPoint (copyM x j)) v r) else point f (actPoint (copyM x j)) v r)

lemma ratCast_ite01 (P : Prop) [Decidable P] : (((if P then 1 else 0 : ℚ)) : ℂ) = if P then 1 else 0 := by
  split_ifs <;> simp

lemma copyM_z (x : R32) (j : Fin 15) (f : ℕ) (v : Data α (PRole Γ T Sl C) f) (g : Γ) (t : T) :
    point f (actPoint (copyM x j)) v (zR g j t) = v (mainR g x t) := by
  funext pt
  simp [point, actPoint, copyM, zR, ratCast_ite01, Finset.sum_ite_eq']

lemma copyM_main (x : R32) (j : Fin 15) (f : ℕ) (v : Data α (PRole Γ T Sl C) f) (g : Γ) (i : R32) (t : T) :
    point f (actPoint (copyM x j)) v (mainR g i t) = v (mainR g i t) := by
  funext pt
  simp [point, actPoint, copyM, mainR, ratCast_ite01, Finset.sum_ite_eq']

lemma copyM_fresh (x : R32) (j : Fin 15) (f : ℕ) (v : Data α (PRole Γ T Sl C) f) (g : Γ) (k : Fin 18) (q : Sl) :
    point f (actPoint (copyM x j)) v (freshR g k q) = v (freshR g k q) := by
  funext pt
  simp [point, actPoint, copyM, freshR, ratCast_ite01, Finset.sum_ite_eq']

lemma addM_y (y : R32) (j : Fin 15) (f : ℕ) (v : Data α (PRole Γ T Sl C) f) (g : Γ) (t : T) :
    point f (actPoint (addM y j)) v (mainR g y t) = v (mainR g y t) + v (zR g j t) := by
  funext pt
  simp [point, actPoint, addM, mainR, zR, ratCast_ite01, add_mul, Finset.sum_add_distrib, Finset.sum_ite_eq']

lemma addM_main (y : R32) (j : Fin 15) (f : ℕ) (v : Data α (PRole Γ T Sl C) f) (g : Γ) (i : R32) (t : T)
    (hi : i ≠ y) : point f (actPoint (addM y j)) v (mainR g i t) = v (mainR g i t) := by
  funext pt
  simp [point, actPoint, addM, mainR, hi, ratCast_ite01, Finset.sum_ite_eq']

lemma addM_fresh (y : R32) (j : Fin 15) (f : ℕ) (v : Data α (PRole Γ T Sl C) f) (g : Γ) (k : Fin 18) (q : Sl) :
    point f (actPoint (addM y j)) v (freshR g k q) = v (freshR g k q) := by
  funext pt
  simp [point, actPoint, addM, freshR, ratCast_ite01, Finset.sum_ite_eq']

lemma main_not_zSet (j : Fin 15) (g : Γ) (i : R32) (t : T) :
    mainR (Sl := Sl) (C := C) g i t ∉ zSet (Γ := Γ) (T := T) (Sl := Sl) (C := C) j := by
  rw [mem_zSet]; rintro ⟨g', t', h⟩; cases h

lemma fresh_not_zSet (j : Fin 15) (g : Γ) (k : Fin 18) (q : Sl) :
    freshR (T := T) (C := C) g k q ∉ zSet (Γ := Γ) (T := T) (Sl := Sl) (C := C) j := by
  rw [mem_zSet]; rintro ⟨g', t', h⟩; cases h

/-- **the thin query as an operator route**: two free gates and ONE step `1 → U g t` per scratch role. -/
theorem thin_route (x y : R32) (hxy : x ≠ y) (j : Fin 15) (U : Γ → T → CMat α) (c : (ℕ → ℝ) → ℝ)
    (hU : ∀ g t, GReach 1 (U g t) c) :
    P4L.ORoute (thinOp (Sl := Sl) (C := C) x y j U)
      (fun φ => ∑ r ∈ zSet (Γ := Γ) (T := T) (Sl := Sl) (C := C) j, c φ) := by
  have R1 := P4L.ORoute.localM (α := α) (copyM (Γ := Γ) (T := T) (Sl := Sl) (C := C) x j)
  have R2 := P4L.ORoute.steps_inv (α := α) (zSet (Γ := Γ) (T := T) (Sl := Sl) (C := C) j) (fun _ => 1) (fun _ => 1)
    (zMat U) (fun r _ => Matrix.mul_one 1) (fun _ => c) (fun r hr => by
      obtain ⟨g, t, rfl⟩ := (mem_zSet j r).mp hr
      exact hU g t _ _)
  have R3 := P4L.ORoute.localM (α := α) (addM (Γ := Γ) (T := T) (Sl := Sl) (C := C) y j)
  exact ((R1.trans R2).trans R3).cast (fun f v => rfl) (fun φ => by simp)

/-- the thin query on a fresh helper: nothing. -/
lemma thin_fresh (x y : R32) (j : Fin 15) (U : Γ → T → CMat α) (f : ℕ) (v : Data α (PRole Γ T Sl C) f)
    (g : Γ) (k : Fin 18) (q : Sl) : thinOp x y j U f v (freshR g k q) = v (freshR g k q) := by
  unfold thinOp
  rw [addM_fresh]
  simp only [if_neg (fresh_not_zSet (Γ := Γ) (T := T) (Sl := Sl) (C := C) j g k q), copyM_fresh]

/-- **the thin query moves the view of every port by `shear`** (`U g t` a Walsh product `m`). -/
theorem view_thin (x y : R32) (hxy : x ≠ y) (j : Fin 15) (U : Γ → T → CMat α) (f : ℕ)
    (v : Data α (PRole Γ T Sl C) f) (g : Γ) (t : T) (m : Sky α f → ℂ)
    (hU : ∀ w, P4L.walsh f (matAct f (U g t) w) = m * P4L.walsh f w) :
    view f g t (thinOp x y j U f v) = shear x y m (view f g t v) := by
  have hz : zR (Sl := Sl) (C := C) g j t ∈ zSet (Γ := Γ) (T := T) (Sl := Sl) (C := C) j :=
    (mem_zSet j _).mpr ⟨g, t, rfl⟩
  apply S32.ext_get
  intro i
  rw [view_get]
  by_cases hi : i = y
  · rw [hi, shear_get_y, view_get, view_get]
    unfold thinOp
    rw [addM_y]
    simp only [if_neg (main_not_zSet (Sl := Sl) (C := C) j g y t), if_pos hz, copyM_main, copyM_z, zMat_z,
      Matrix.mul_one]
    rw [P4L.walsh_add, hU]
  · rw [shear_get_o _ _ _ _ i hi, view_get]
    unfold thinOp
    rw [addM_main _ _ _ _ _ _ _ hi]
    simp only [if_neg (main_not_zSet (Sl := Sl) (C := C) j g i t), copyM_main]

end Thin

section ThinStep
variable {α : Type} [Fintype α] [DecidableEq α]

/-- the inverse port translation as a matrix: `unframe A {p} = shift (A.corr {p}) * blockMat (A.fam {p}) * shift (A.v p)`. -/
lemma unframe_single (A : OBase α) (p : α) :
    unframe A {p} = Binary.shift (A.corr {p}) * blockMat (A.fam {p}) * Binary.shift (A.v p) := by
  rw [← P4L.frame_eq_shift_blockMat, P4L.unframe_eq_wrap, P4L.frame_eq_wrap, shift_phase, wrap_mul]
  congr 1
  funext x
  exact P4L.fr_single_inv A p x

/-- **ONE rank-1 block between two free shifts** takes a scratch role from `1` to `unframe A {p}`. -/
lemma greach_unframe_single (A : OBase α) (p : α) (h2 : 1 < Fintype.card α) :
    GReach 1 (unframe A {p}) (fun φ => bcost φ 1) := by
  intro ρ _ _ r
  have h := gstep_of_factor r (1 : CMat α) (A.fam {p}) (OBase.fam_indep A {p})
    (Free.shift (A.corr {p})) (Free.shift (A.v p)) (by rw [Finset.card_singleton]) (by rw [Finset.card_singleton]; exact h2)
  rw [Matrix.mul_one, ← unframe_single] at h
  refine h.cast (fun φ => ?_)
  rw [Finset.card_singleton]
  simp [bcost]

end ThinStep

end
end P16A8
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.P16A8.thin_route
#print axioms OAI.PowerSaving.P16A8.view_thin
#print axioms OAI.PowerSaving.P16A8.greach_unframe_single
