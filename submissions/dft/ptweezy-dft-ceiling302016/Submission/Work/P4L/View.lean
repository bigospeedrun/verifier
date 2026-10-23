import Submission.Work.P4L.Stage
import Submission.Work.P4L.S8
-- changed for the tensor-power extension (30103/10000000); see Submission.lean

/-!
# P4-L, part 9: the view of one port, and how each kind of segment moves it

`view f g t y : S8 (Sky α f → ℂ)` = the eight main roles of port `(g, t)` in Walsh coordinates.  Every segment of the
P4-L word moves the view of every port by one controller event (Work/P4L/S8):

* `view_call_fwd`, `view_call_bwd`  a native call (`call_fwd`, `call_bwd`) is `callF` / `callB` with
  `d = prodF f (fr A Δ)` and `qi = prodF f (fr A {p})⁻¹`, `q = prodF f (fr A {p})` (frames in one basis per port:
  `sX' = sX ∪ Δ`, `sY' = sY ∪ Δ`, `sX = sY ∪ {p}`);
* `view_steps`      single-role steps on roles outside the port's main roles leave the view unchanged; on an owner
  pair with `U * frame A s = frame A s'` (`s' = s ∪ Δ`) they are the window `win x y (prodF f (fr A Δ))`;
* `view_linMat`     a gate letter `linMat M` (the 8×8 rational matrix `M` on the main roles of every port) is the linear
  map `lin8 M` of the view.
No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace OAI
namespace PowerSaving
namespace P4L
open Binary Matrix Finset RAM SS CB RF BR GF GX XHostTW P4Ctrl

noncomputable section

section View
variable {α Γ T Sl C : Type} [Fintype α] [DecidableEq α] [Fintype Γ] [DecidableEq Γ] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]

/-- the eight main roles of port `(g, t)` in Walsh coordinates. -/
def view (f : ℕ) (g : Γ) (t : T) (y : Data α (PRole Γ T Sl C) f) : S8 (Sky α f → ℂ) :=
  ⟨walsh f (y (mainR g .x0 t)), walsh f (y (mainR g .y0 t)), walsh f (y (mainR g .x1 t)),
   walsh f (y (mainR g .y1 t)), walsh f (y (mainR g .x2 t)), walsh f (y (mainR g .y2 t)),
   walsh f (y (mainR g .x3 t)), walsh f (y (mainR g .y3 t))⟩

lemma view_get (f : ℕ) (g : Γ) (t : T) (y : Data α (PRole Γ T Sl C) f) (i : R8) :
    (view f g t y).get i = walsh f (y (mainR g i t)) := by
  cases i <;> rfl

/-- two data with the same main roles at the port have the same view. -/
lemma view_congr (f : ℕ) (g : Γ) (t : T) (y y' : Data α (PRole Γ T Sl C) f)
    (h : ∀ i, y (mainR g i t) = y' (mainR g i t)) : view f g t y = view f g t y' := by
  simp only [view, h]

/-- an S8 is determined by its eight roles. -/
lemma S8.ext_get {R : Type*} [CommRing R] (u v : S8 R) (h : ∀ i, u.get i = v.get i) : u = v := by
  have h0 := h .x0; have h1 := h .y0; have h2 := h .x1; have h3 := h .y1
  have h4 := h .x2; have h5 := h .y2; have h6 := h .x3; have h7 := h .y3
  cases u; cases v
  simp only [S8.get] at h0 h1 h2 h3 h4 h5 h6 h7
  subst h0 h1 h2 h3 h4 h5 h6 h7
  rfl

lemma S8.get_set_same {R : Type*} [CommRing R] (u : S8 R) (i : R8) (v : R) : (u.set i v).get i = v := by
  cases i <;> rfl

lemma S8.get_set_ne {R : Type*} [CommRing R] (u : S8 R) (i j : R8) (v : R) (h : j ≠ i) :
    (u.set i v).get j = u.get j := by
  cases i <;> cases j <;> first | rfl | exact absurd rfl h

end View

section CallView
variable {H T Sl C α Γ : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C] [Fintype α] [DecidableEq α]
  [Fintype Γ] [DecidableEq Γ]

/-- in Walsh coordinates, `frame A (s ∪ Δ) * unframe A s` is the product with `prodF (fr A Δ)`. -/
lemma walsh_ratio (f : ℕ) (A : OBase α) (s Δ : Finset α) (h : Disjoint s Δ) (y : Sky α f → ℂ) :
    walsh f (matAct f (frame A (s ∪ Δ)) (matAct f (unframe A s) y)) = prodF f (fr A Δ) * walsh f y := by
  rw [walsh_frame, walsh_unframe, fr_union A s Δ h]
  have e : prodF f (fr A s * fr A Δ) = prodF f (fr A s) * prodF f (fr A Δ) := prodF_mul f (fr A s) (fr A Δ)
  rw [e]
  have hinv := prodF_inv_mul f A s
  calc prodF f (fr A s) * prodF f (fr A Δ) * (prodF f (fun x => (fr A s x)⁻¹) * walsh f y)
      = prodF f (fr A Δ) * ((prodF f (fun x => (fr A s x)⁻¹) * prodF f (fr A s)) * walsh f y) := by ring
    _ = prodF f (fr A Δ) * walsh f y := by rw [hinv, one_mul]

/-- the cross term of a call: `frame A (sY ∪ Δ) * unframe A (sY ∪ {p})` is `prodF (fr A Δ) * prodF (fr A {p})⁻¹`. -/
lemma walsh_cross (f : ℕ) (A : OBase α) (sY Δ : Finset α) (p : α) (hΔ : Disjoint sY Δ)
    (hp : Disjoint sY {p}) (y : Sky α f → ℂ) :
    walsh f (matAct f (frame A (sY ∪ Δ)) (matAct f (unframe A (sY ∪ {p})) y))
      = prodF f (fr A Δ) * (prodF f (fun x => (fr A {p} x)⁻¹) * walsh f y) := by
  rw [walsh_frame, walsh_unframe, fr_union A sY Δ hΔ]
  have e1 : (fun x => (fr A (sY ∪ {p}) x)⁻¹) = fun x => (fr A sY x)⁻¹ * (fr A {p} x)⁻¹ := by
    funext x
    rw [fr_union A sY {p} hp, Pi.mul_apply, mul_inv]
  rw [e1]
  have e2 : prodF f (fun x => (fr A sY x)⁻¹ * (fr A {p} x)⁻¹)
      = prodF f (fun x => (fr A sY x)⁻¹) * prodF f (fun x => (fr A {p} x)⁻¹) := prodF_mul f _ _
  have e3 : prodF f (fr A sY * fr A Δ) = prodF f (fr A sY) * prodF f (fr A Δ) := prodF_mul f (fr A sY) (fr A Δ)
  rw [e2, e3]
  have hinv := prodF_inv_mul f A sY
  calc prodF f (fr A sY) * prodF f (fr A Δ) * (prodF f (fun x => (fr A sY x)⁻¹) * prodF f (fun x => (fr A {p} x)⁻¹)
          * walsh f y)
      = prodF f (fr A Δ) * ((prodF f (fun x => (fr A sY x)⁻¹) * prodF f (fr A sY))
          * (prodF f (fun x => (fr A {p} x)⁻¹) * walsh f y)) := by ring
    _ = prodF f (fr A Δ) * (prodF f (fun x => (fr A {p} x)⁻¹) * walsh f y) := by rw [hinv, one_mul]

/-- the back cross term: `frame A (sY ∪ {p} ∪ Δ) * unframe A sY` is `prodF (fr A Δ) * prodF (fr A {p})`. -/
lemma walsh_cross_b (f : ℕ) (A : OBase α) (sY Δ : Finset α) (p : α) (hΔ : Disjoint (sY ∪ {p}) Δ)
    (hp : Disjoint sY {p}) (y : Sky α f → ℂ) :
    walsh f (matAct f (frame A (sY ∪ {p} ∪ Δ)) (matAct f (unframe A sY) y))
      = prodF f (fr A Δ) * (prodF f (fr A {p}) * walsh f y) := by
  rw [walsh_frame, walsh_unframe, fr_union A (sY ∪ {p}) Δ hΔ, fr_union A sY {p} hp]
  have e3 : prodF f (fr A sY * fr A {p} * fr A Δ) = prodF f (fr A sY) * prodF f (fr A {p}) * prodF f (fr A Δ) := by
    have a1 : prodF f (fr A sY * fr A {p} * fr A Δ) = prodF f (fr A sY * fr A {p}) * prodF f (fr A Δ) :=
      prodF_mul f (fr A sY * fr A {p}) (fr A Δ)
    have a2 : prodF f (fr A sY * fr A {p}) = prodF f (fr A sY) * prodF f (fr A {p}) :=
      prodF_mul f (fr A sY) (fr A {p})
    rw [a1, a2]
  rw [e3]
  have hinv := prodF_inv_mul f A sY
  calc prodF f (fr A sY) * prodF f (fr A {p}) * prodF f (fr A Δ) * (prodF f (fun x => (fr A sY x)⁻¹) * walsh f y)
      = prodF f (fr A Δ) * ((prodF f (fun x => (fr A sY x)⁻¹) * prodF f (fr A sY)) * (prodF f (fr A {p}) * walsh f y)) := by
        ring
    _ = prodF f (fr A Δ) * (prodF f (fr A {p}) * walsh f y) := by rw [hinv, one_mul]

end CallView


section CallGet
variable {R : Type*} [CommRing R]

lemma callF_get_x (x y : R8) (hxy : x ≠ y) (d qi : R) (u : S8 R) : (callF x y d qi u).get x = d * u.get x := by
  unfold callF
  rw [S8.get_set_ne _ _ _ _ hxy, S8.get_set_same]

lemma callF_get_y (x y : R8) (d qi : R) (u : S8 R) :
    (callF x y d qi u).get y = d * (u.get y + qi * u.get x) := by
  unfold callF
  rw [S8.get_set_same]

lemma callF_get_o (x y : R8) (d qi : R) (u : S8 R) (i : R8) (hx : i ≠ x) (hy : i ≠ y) :
    (callF x y d qi u).get i = u.get i := by
  unfold callF
  rw [S8.get_set_ne _ _ _ _ hy, S8.get_set_ne _ _ _ _ hx]

lemma callB_get_x (x y : R8) (hxy : x ≠ y) (d q : R) (u : S8 R) :
    (callB x y d q u).get x = d * (u.get x - q * u.get y) := by
  unfold callB
  rw [S8.get_set_ne _ _ _ _ hxy, S8.get_set_same]

lemma callB_get_y (x y : R8) (d q : R) (u : S8 R) : (callB x y d q u).get y = d * u.get y := by
  unfold callB
  rw [S8.get_set_same]

lemma callB_get_o (x y : R8) (d q : R) (u : S8 R) (i : R8) (hx : i ≠ x) (hy : i ≠ y) :
    (callB x y d q u).get i = u.get i := by
  unfold callB
  rw [S8.get_set_ne _ _ _ _ hy, S8.get_set_ne _ _ _ _ hx]

end CallGet

section CallView2
variable {H T Sl C α Γ : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C] [Fintype α] [DecidableEq α]
  [Fintype Γ] [DecidableEq Γ]

lemma matAct_sub' (f : ℕ) (M : CMat α) (x y : Sky α f → ℂ) :
    matAct f M (x - y) = matAct f M x - matAct f M y := by
  unfold matAct; exact Matrix.mulVec_sub _ _ _

lemma point_gFk (k : Fin 9) (f : ℕ) (z : Data α (PRole Γ T Sl C) f) (g : Γ) (i : R8) (t : T) :
    point f (gFk k) z (mainR g i t)
      = if i = yOf k then z (mainR g (yOf k) t) + z (mainR g (xOf k) t) else z (mainR g i t) := by
  funext pt
  by_cases hy : i = yOf k
  · subst hy
    simp [point, gFk, mainR]
  · simp [point, gFk, mainR, hy]

lemma point_gBk (k : Fin 9) (f : ℕ) (z : Data α (PRole Γ T Sl C) f) (g : Γ) (i : R8) (t : T) :
    point f (gBk k) z (mainR g i t)
      = if i = xOf k then z (mainR g (xOf k) t) - z (mainR g (yOf k) t) else z (mainR g i t) := by
  funext pt
  by_cases hx : i = xOf k
  · subst hx
    simp [point, gBk, mainR]
  · simp [point, gBk, mainR, hx]

lemma stT_main (k : Fin 9) (A : Γ → T → OBase α) (sX' sY' : Finset α) (Wn : Γ → Sl → CMat α)
    (g : Γ) (i : R8) (t : T) :
    stT (Sl := Sl) (C := C) k A sX' sY' Wn (mainR g i t)
      = if i = xOf k then frame (A g t) sX' else if i = yOf k then frame (A g t) sY' else 1 := rfl

lemma stS'_main (k : Fin 9) (A : Γ → T → OBase α) (sX sY : Finset α) (g : Γ) (i : R8) (t : T) :
    stS' (Sl := Sl) (C := C) k A sX sY (mainR g i t)
      = if i = xOf k then unframe (A g t) sX else if i = yOf k then unframe (A g t) sY else 1 := rfl

/-- the value of a call operator at a main role (forward). -/
lemma callF_at (k : Fin 9) (A : Γ → T → OBase α) (sX sX' sY sY' : Finset α) (Wn : Γ → Sl → CMat α)
    (f : ℕ) (y : Data α (PRole Γ T Sl C) f) (g : Γ) (i : R8) (t : T) :
    multiAct f (stT k A sX' sY' Wn) (point f (gFk k) (multiAct f (stS' k A sX sY) y)) (mainR g i t)
      = if i = xOf k then matAct f (frame (A g t) sX') (matAct f (unframe (A g t) sX) (y (mainR g i t)))
        else if i = yOf k then matAct f (frame (A g t) sY')
          (matAct f (unframe (A g t) sY) (y (mainR g (yOf k) t))
            + matAct f (unframe (A g t) sX) (y (mainR g (xOf k) t)))
        else y (mainR g i t) := by
  have hxy := xOf_ne_yOf k
  by_cases hx : i = xOf k
  · subst hx
    simp [multiAct, point_gFk, stT_main, stS'_main, hxy, Ne.symm hxy]
  · by_cases hy : i = yOf k
    · subst hy
      simp [multiAct, point_gFk, stT_main, stS'_main, hxy, Ne.symm hxy]
    · simp [multiAct, point_gFk, stT_main, stS'_main, hx, hy, Ne.symm hx, Ne.symm hy]

/-- the value of a call operator at a main role (backward). -/
lemma callB_at (k : Fin 9) (A : Γ → T → OBase α) (sX sX' sY sY' : Finset α) (Wn : Γ → Sl → CMat α)
    (f : ℕ) (y : Data α (PRole Γ T Sl C) f) (g : Γ) (i : R8) (t : T) :
    multiAct f (stT k A sX' sY' Wn) (point f (gBk k) (multiAct f (stS' k A sX sY) y)) (mainR g i t)
      = if i = xOf k then matAct f (frame (A g t) sX')
          (matAct f (unframe (A g t) sX) (y (mainR g (xOf k) t))
            - matAct f (unframe (A g t) sY) (y (mainR g (yOf k) t)))
        else if i = yOf k then matAct f (frame (A g t) sY') (matAct f (unframe (A g t) sY) (y (mainR g i t)))
        else y (mainR g i t) := by
  have hxy := xOf_ne_yOf k
  by_cases hx : i = xOf k
  · subst hx
    simp [multiAct, point_gBk, stT_main, stS'_main, hxy, Ne.symm hxy]
  · by_cases hy : i = yOf k
    · subst hy
      simp [multiAct, point_gBk, stT_main, stS'_main, hxy, Ne.symm hxy]
    · simp [multiAct, point_gBk, stT_main, stS'_main, hx, hy, Ne.symm hx, Ne.symm hy]

/-- **a forward call moves the view of every port by `callF`.** -/
theorem view_call_fwd (k : Fin 9) (A : Γ → T → OBase α) (sY Δ : Finset α) (p : α)
    (hΔ : Disjoint (sY ∪ {p}) Δ) (hΔY : Disjoint sY Δ) (hp : Disjoint sY {p}) (Wn : Γ → Sl → CMat α)
    (f : ℕ) (y : Data α (PRole Γ T Sl C) f) (g : Γ) (t : T) :
    view f g t (multiAct f (stT k A (sY ∪ {p} ∪ Δ) (sY ∪ Δ) Wn)
        (point f (gFk k) (multiAct f (stS' k A (sY ∪ {p}) sY) y)))
      = callF (xOf k) (yOf k) (prodF f (fr (A g t) Δ)) (prodF f (fun x => (fr (A g t) {p} x)⁻¹))
          (view f g t y) := by
  have hxy := xOf_ne_yOf k
  apply S8.ext_get
  intro i
  rw [view_get, callF_at]
  by_cases hx : i = xOf k
  · subst hx
    rw [if_pos rfl, callF_get_x _ _ hxy, view_get]
    exact walsh_ratio f (A g t) (sY ∪ {p}) Δ hΔ _
  · by_cases hy : i = yOf k
    · subst hy
      rw [if_neg hx, if_pos rfl, callF_get_y, view_get, view_get, matAct_add, walsh_add,
        walsh_ratio f (A g t) sY Δ hΔY, walsh_cross f (A g t) sY Δ p hΔY hp]
      ring
    · rw [if_neg hx, if_neg hy, callF_get_o _ _ _ _ _ i hx hy, view_get]

/-- **a backward call moves the view of every port by `callB`.** -/
theorem view_call_bwd (k : Fin 9) (A : Γ → T → OBase α) (sY Δ : Finset α) (p : α)
    (hΔ : Disjoint (sY ∪ {p}) Δ) (hΔY : Disjoint sY Δ) (hp : Disjoint sY {p}) (Wn : Γ → Sl → CMat α)
    (f : ℕ) (y : Data α (PRole Γ T Sl C) f) (g : Γ) (t : T) :
    view f g t (multiAct f (stT k A (sY ∪ {p} ∪ Δ) (sY ∪ Δ) Wn)
        (point f (gBk k) (multiAct f (stS' k A (sY ∪ {p}) sY) y)))
      = callB (xOf k) (yOf k) (prodF f (fr (A g t) Δ)) (prodF f (fr (A g t) {p})) (view f g t y) := by
  have hxy := xOf_ne_yOf k
  apply S8.ext_get
  intro i
  rw [view_get, callB_at]
  by_cases hx : i = xOf k
  · subst hx
    rw [if_pos rfl, callB_get_x _ _ hxy, view_get, view_get, matAct_sub', walsh_sub,
      walsh_ratio f (A g t) (sY ∪ {p}) Δ hΔ, walsh_cross_b f (A g t) sY Δ p hΔ hp]
    ring
  · by_cases hy : i = yOf k
    · subst hy
      rw [if_neg hx, if_pos rfl, callB_get_y, view_get]
      exact walsh_ratio f (A g t) sY Δ hΔY _
    · rw [if_neg hx, if_neg hy, callB_get_o _ _ _ _ _ i hx hy, view_get]

end CallView2


section StepsView
variable {α Γ T Sl C : Type} [Fintype α] [DecidableEq α] [Fintype Γ] [DecidableEq Γ] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]

lemma win_get_x {R : Type*} [CommRing R] (x y : R8) (hxy : x ≠ y) (m : R) (u : S8 R) :
    (win x y m u).get x = m * u.get x := by
  unfold win; rw [S8.get_set_ne _ _ _ _ hxy, S8.get_set_same]

lemma win_get_y {R : Type*} [CommRing R] (x y : R8) (m : R) (u : S8 R) : (win x y m u).get y = m * u.get y := by
  unfold win; rw [S8.get_set_same]

lemma win_get_o {R : Type*} [CommRing R] (x y : R8) (m : R) (u : S8 R) (i : R8) (hx : i ≠ x) (hy : i ≠ y) :
    (win x y m u).get i = u.get i := by
  unfold win; rw [S8.get_set_ne _ _ _ _ hy, S8.get_set_ne _ _ _ _ hx]

/-- single-role steps that touch no main role of the port leave its view unchanged. -/
theorem view_steps_none (s : Finset (PRole Γ T Sl C)) (U : PRole Γ T Sl C → CMat α) (f : ℕ)
    (y : Data α (PRole Γ T Sl C) f) (g : Γ) (t : T) (hs : ∀ i, mainR g i t ∉ s) :
    view f g t (fun r => if r ∈ s then matAct f (U r) (y r) else y r) = view f g t y := by
  apply view_congr
  intro i
  simp only [hs i, if_false]

/-- single-role steps on the two roles of a pair, each a Walsh product `m`: the window `win x y m`. -/
theorem view_steps_win (s : Finset (PRole Γ T Sl C)) (U : PRole Γ T Sl C → CMat α) (f : ℕ)
    (y : Data α (PRole Γ T Sl C) f) (g : Γ) (t : T) (x yR : R8) (hxy : x ≠ yR) (m : Sky α f → ℂ)
    (hs : ∀ i, mainR g i t ∈ s ↔ (i = x ∨ i = yR))
    (hU : ∀ i, (i = x ∨ i = yR) → ∀ v, walsh f (matAct f (U (mainR g i t)) v) = m * walsh f v) :
    view f g t (fun r => if r ∈ s then matAct f (U r) (y r) else y r) = win x yR m (view f g t y) := by
  apply S8.ext_get
  intro i
  rw [view_get]
  by_cases hx : i = x
  · subst hx
    rw [if_pos ((hs i).mpr (Or.inl rfl)), hU i (Or.inl rfl), win_get_x _ _ hxy, view_get]
  · by_cases hy : i = yR
    · subst hy
      rw [if_pos ((hs i).mpr (Or.inr rfl)), hU i (Or.inr rfl), win_get_y, view_get]
    · have hn : mainR g i t ∉ s := fun h => by
        rcases (hs i).mp h with h | h
        · exact hx h
        · exact hy h
      rw [if_neg hn, win_get_o _ _ _ _ i hx hy, view_get]

/-- a step `U * frame A s = frame A (s ∪ Δ)` is, in Walsh coordinates, the product with `prodF (fr A Δ)`. -/
lemma walsh_step (f : ℕ) (A : OBase α) (s Δ : Finset α) (h : Disjoint s Δ) (U : CMat α)
    (hU : U * frame A s = frame A (s ∪ Δ)) (v : Sky α f → ℂ) :
    walsh f (matAct f U v) = prodF f (fr A Δ) * walsh f v := by
  have e : U = frame A (s ∪ Δ) * unframe A s := by
    rw [← hU, Matrix.mul_assoc, unframe_right, Matrix.mul_one]
  rw [e, ← matAct_mul]
  exact walsh_ratio f A s Δ h v

end StepsView

section LinView
variable {α Γ T Sl C : Type} [Fintype α] [DecidableEq α] [Fintype Γ] [DecidableEq Γ] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]

lemma walsh_sum {ι : Type*} (f : ℕ) (s : Finset ι) (x : ι → Sky α f → ℂ) :
    walsh f (∑ i ∈ s, x i) = ∑ i ∈ s, walsh f (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact walsh_zero f
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, walsh_add, ih]

/-- a gate layer on every port: the rational matrix `M` on the eight main roles of each port, identity elsewhere. -/
def linMat (M : Matrix R8 R8 ℚ) : Matrix (PRole Γ T Sl C) (PRole Γ T Sl C) ℚ := fun r r' =>
  match r, r' with
  | .inl (.inl (g, (i, t))), .inl (.inl (g', (i', t'))) => if g = g' ∧ t = t' then M i i' else 0
  | .inl (.inl _), _ => 0
  | _, .inl (.inl _) => 0
  | r, r' => if r = r' then 1 else 0

lemma R8_univ : (Finset.univ : Finset R8) = {.x0, .y0, .x1, .y1, .x2, .y2, .x3, .y3} := rfl

lemma R8_sum {M : Type*} [AddCommMonoid M] (φ : R8 → M) :
    ∑ i, φ i = φ .x0 + (φ .y0 + (φ .x1 + (φ .y1 + (φ .x2 + (φ .y2 + (φ .x3 + φ .y3)))))) := by
  rw [R8_univ]
  simp [Finset.sum_insert]

/-- the S8 of eight values. -/
def S8.ofFun {R : Type*} (v : R8 → R) : S8 R :=
  ⟨v .x0, v .y0, v .x1, v .y1, v .x2, v .y2, v .x3, v .y3⟩

lemma S8.ofFun_get {R : Type*} [CommRing R] (v : R8 → R) (i : R8) : (S8.ofFun v).get i = v i := by
  cases i <;> rfl

/-- the gate layer on one port's view (the view's roles are functions to `ℂ`; `ℂ` acts by scalars). -/
def lin8 {β : Type*} (M : Matrix R8 R8 ℚ) (u : S8 (β → ℂ)) : S8 (β → ℂ) :=
  S8.ofFun fun i => ∑ i', ((M i i' : ℚ) : ℂ) • u.get i'

/-- the value of a gate layer at a main role. -/
lemma linMat_at (M : Matrix R8 R8 ℚ) (f : ℕ) (y : Data α (PRole Γ T Sl C) f) (g : Γ) (i : R8) (t : T) :
    point f (actPoint (linMat M)) y (mainR g i t) = ∑ i', ((M i i' : ℚ) : ℂ) • y (mainR g i' t) := by
  funext pt
  simp only [point, actPoint, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have h2 : ∑ x : Γ × (Fin 9 × Sl), ((linMat (Γ := Γ) (T := T) (Sl := Sl) (C := C) M (mainR g i t)
      (Sum.inl (Sum.inr x)) : ℚ) : ℂ) * y (Sum.inl (Sum.inr x)) pt = 0 := by
    apply Finset.sum_eq_zero; intro x _; simp [linMat, mainR]
  have h3 : ∑ x : Γ × C, ((linMat (Γ := Γ) (T := T) (Sl := Sl) (C := C) M (mainR g i t)
      (Sum.inr x) : ℚ) : ℂ) * y (Sum.inr x) pt = 0 := by
    apply Finset.sum_eq_zero; intro x _; simp [linMat, mainR]
  rw [h2, h3, add_zero, add_zero]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single g]
  · rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i' _
    rw [Finset.sum_eq_single t]
    · simp [linMat, mainR]
    · intro t' _ ht'; simp [linMat, mainR, Ne.symm ht']
    · intro h; exact absurd (Finset.mem_univ t) h
  · intro g' _ hg'
    apply Finset.sum_eq_zero
    intro x _
    simp [linMat, mainR, Ne.symm hg']
  · intro h; exact absurd (Finset.mem_univ g) h

/-- **a gate layer moves the view of every port by `lin8`.** -/
theorem view_linMat (M : Matrix R8 R8 ℚ) (f : ℕ) (y : Data α (PRole Γ T Sl C) f) (g : Γ) (t : T) :
    view f g t (point f (actPoint (linMat M)) y) = lin8 M (view f g t y) := by
  apply S8.ext_get
  intro i
  rw [view_get, linMat_at, lin8, S8.ofFun_get, walsh_sum]
  apply Finset.sum_congr rfl
  intro i' _
  rw [walsh_smul, view_get]

/-- a gate layer leaves the other roles unchanged. -/
lemma linMat_other (M : Matrix R8 R8 ℚ) (f : ℕ) (y : Data α (PRole Γ T Sl C) f) (r : PRole Γ T Sl C)
    (hr : ∀ g i t, r ≠ mainR g i t) : point f (actPoint (linMat M)) y r = y r := by
  funext pt
  simp only [point, actPoint]
  rw [Finset.sum_eq_single r]
  · rcases r with ((⟨g, i, t⟩ | h) | c)
    · exact absurd rfl (hr g i t)
    · simp [linMat]
    · simp [linMat]
  · intro r' _ hr'
    rcases r with ((⟨g, i, t⟩ | h) | c)
    · exact absurd rfl (hr g i t)
    · rcases r' with ((⟨g', i', t'⟩ | h') | c') <;> simp [linMat, Ne.symm hr']
    · rcases r' with ((⟨g', i', t'⟩ | h') | c') <;> simp [linMat, Ne.symm hr']
  · intro h; exact absurd (Finset.mem_univ r) h

end LinView

end
end P4L
end PowerSaving
end OAI
