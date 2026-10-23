import Submission.Work.P16A8.Stage
import Submission.Work.P4L.View
-- changed for the tensor-power extension (30103/10000000); see Submission.lean

/-!
# P16A8 (p16a8), the view of one port, and how each kind of segment moves it

`view f g t y : S32 (Sky α f → ℂ)` = the 32 main roles of port `(g, t)` in Walsh coordinates.  A full call moves
it by `callF`/`callB` (`view_call_fwd/bwd`), single-role steps on an owner pair by `win` (`view_steps_win`), a gate
layer `linMat M` by `lin32 M` (`view_linMat`).  The generic Walsh identities are P4L's.
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

section View
variable {α Γ T Sl C : Type} [Fintype α] [DecidableEq α] [Fintype Γ] [DecidableEq Γ] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]

/-- the 32 main roles of port `(g, t)` in Walsh coordinates. -/
def view (f : ℕ) (g : Γ) (t : T) (y : Data α (PRole Γ T Sl C) f) : S32 (Sky α f → ℂ) :=
  ⟨P4L.walsh f (y (mainR g .x0 t)), P4L.walsh f (y (mainR g .y0 t)), P4L.walsh f (y (mainR g .x1 t)), P4L.walsh f (y (mainR g .y1 t)), P4L.walsh f (y (mainR g .x2 t)), P4L.walsh f (y (mainR g .y2 t)), P4L.walsh f (y (mainR g .x3 t)), P4L.walsh f (y (mainR g .y3 t)), P4L.walsh f (y (mainR g .x4 t)), P4L.walsh f (y (mainR g .y4 t)), P4L.walsh f (y (mainR g .x5 t)), P4L.walsh f (y (mainR g .y5 t)), P4L.walsh f (y (mainR g .x6 t)), P4L.walsh f (y (mainR g .y6 t)), P4L.walsh f (y (mainR g .x7 t)), P4L.walsh f (y (mainR g .y7 t)), P4L.walsh f (y (mainR g .x8 t)), P4L.walsh f (y (mainR g .y8 t)), P4L.walsh f (y (mainR g .x9 t)), P4L.walsh f (y (mainR g .y9 t)), P4L.walsh f (y (mainR g .x10 t)), P4L.walsh f (y (mainR g .y10 t)), P4L.walsh f (y (mainR g .x11 t)), P4L.walsh f (y (mainR g .y11 t)), P4L.walsh f (y (mainR g .x12 t)), P4L.walsh f (y (mainR g .y12 t)), P4L.walsh f (y (mainR g .x13 t)), P4L.walsh f (y (mainR g .y13 t)), P4L.walsh f (y (mainR g .x14 t)), P4L.walsh f (y (mainR g .y14 t)), P4L.walsh f (y (mainR g .x15 t)), P4L.walsh f (y (mainR g .y15 t))⟩

lemma view_get (f : ℕ) (g : Γ) (t : T) (y : Data α (PRole Γ T Sl C) f) (i : R32) :
    (view f g t y).get i = P4L.walsh f (y (mainR g i t)) := by
  cases i <;> rfl

lemma view_congr (f : ℕ) (g : Γ) (t : T) (y y' : Data α (PRole Γ T Sl C) f)
    (h : ∀ i, y (mainR g i t) = y' (mainR g i t)) : view f g t y = view f g t y' := by
  simp only [view, h]

lemma S32.ext_get {R : Type*} (u v : S32 R) (h : ∀ i, u.get i = v.get i) : u = v := by
  have h0 := h .x0
  have h1 := h .y0
  have h2 := h .x1
  have h3 := h .y1
  have h4 := h .x2
  have h5 := h .y2
  have h6 := h .x3
  have h7 := h .y3
  have h8 := h .x4
  have h9 := h .y4
  have h10 := h .x5
  have h11 := h .y5
  have h12 := h .x6
  have h13 := h .y6
  have h14 := h .x7
  have h15 := h .y7
  have h16 := h .x8
  have h17 := h .y8
  have h18 := h .x9
  have h19 := h .y9
  have h20 := h .x10
  have h21 := h .y10
  have h22 := h .x11
  have h23 := h .y11
  have h24 := h .x12
  have h25 := h .y12
  have h26 := h .x13
  have h27 := h .y13
  have h28 := h .x14
  have h29 := h .y14
  have h30 := h .x15
  have h31 := h .y15
  cases u; cases v
  simp only [S32.get] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31
  subst h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31
  rfl

lemma S32.get_set_same {R : Type*} (u : S32 R) (i : R32) (v : R) : (u.set i v).get i = v := by
  cases i <;> rfl

lemma S32.get_set_ne {R : Type*} (u : S32 R) (i j : R32) (v : R) (h : j ≠ i) :
    (u.set i v).get j = u.get j := by
  cases i <;> cases j <;> first | rfl | exact absurd rfl h

end View

section CallGet
variable {R : Type*} [CommRing R]

lemma callF_get_x (x y : R32) (hxy : x ≠ y) (d qi : R) (u : S32 R) : (callF x y d qi u).get x = d * u.get x := by
  unfold callF
  rw [S32.get_set_ne _ _ _ _ hxy, S32.get_set_same]

lemma callF_get_y (x y : R32) (d qi : R) (u : S32 R) :
    (callF x y d qi u).get y = d * (u.get y + qi * u.get x) := by
  unfold callF
  rw [S32.get_set_same]

lemma callF_get_o (x y : R32) (d qi : R) (u : S32 R) (i : R32) (hx : i ≠ x) (hy : i ≠ y) :
    (callF x y d qi u).get i = u.get i := by
  unfold callF
  rw [S32.get_set_ne _ _ _ _ hy, S32.get_set_ne _ _ _ _ hx]

lemma callB_get_x (x y : R32) (hxy : x ≠ y) (d q : R) (u : S32 R) :
    (callB x y d q u).get x = d * (u.get x - q * u.get y) := by
  unfold callB
  rw [S32.get_set_ne _ _ _ _ hxy, S32.get_set_same]

lemma callB_get_y (x y : R32) (d q : R) (u : S32 R) : (callB x y d q u).get y = d * u.get y := by
  unfold callB
  rw [S32.get_set_same]

lemma callB_get_o (x y : R32) (d q : R) (u : S32 R) (i : R32) (hx : i ≠ x) (hy : i ≠ y) :
    (callB x y d q u).get i = u.get i := by
  unfold callB
  rw [S32.get_set_ne _ _ _ _ hy, S32.get_set_ne _ _ _ _ hx]

lemma shear_get_y (x y : R32) (qi : R) (u : S32 R) : (shear x y qi u).get y = u.get y + qi * u.get x := by
  unfold shear
  rw [S32.get_set_same]

lemma shear_get_o (x y : R32) (qi : R) (u : S32 R) (i : R32) (hy : i ≠ y) :
    (shear x y qi u).get i = u.get i := by
  unfold shear
  rw [S32.get_set_ne _ _ _ _ hy]

lemma win_get_x (x y : R32) (hxy : x ≠ y) (m : R) (u : S32 R) :
    (win x y m u).get x = m * u.get x := by
  unfold win; rw [S32.get_set_ne _ _ _ _ hxy, S32.get_set_same]

lemma win_get_y (x y : R32) (m : R) (u : S32 R) : (win x y m u).get y = m * u.get y := by
  unfold win; rw [S32.get_set_same]

lemma win_get_o (x y : R32) (m : R) (u : S32 R) (i : R32) (hx : i ≠ x) (hy : i ≠ y) :
    (win x y m u).get i = u.get i := by
  unfold win; rw [S32.get_set_ne _ _ _ _ hy, S32.get_set_ne _ _ _ _ hx]

end CallGet

section CallView2
variable {H T Sl C α Γ : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C] [Fintype α] [DecidableEq α]
  [Fintype Γ] [DecidableEq Γ]

lemma point_gFk (k : Fin 18) (f : ℕ) (z : Data α (PRole Γ T Sl C) f) (g : Γ) (i : R32) (t : T) :
    point f (gFk k) z (mainR g i t)
      = if i = yOf k then z (mainR g (yOf k) t) + z (mainR g (xOf k) t) else z (mainR g i t) := by
  funext pt
  by_cases hy : i = yOf k
  · subst hy
    simp [point, gFk, mainR]
  · simp [point, gFk, mainR, hy]

lemma point_gBk (k : Fin 18) (f : ℕ) (z : Data α (PRole Γ T Sl C) f) (g : Γ) (i : R32) (t : T) :
    point f (gBk k) z (mainR g i t)
      = if i = xOf k then z (mainR g (xOf k) t) - z (mainR g (yOf k) t) else z (mainR g i t) := by
  funext pt
  by_cases hx : i = xOf k
  · subst hx
    simp [point, gBk, mainR]
  · simp [point, gBk, mainR, hx]

lemma stT_main (k : Fin 18) (A : Γ → T → OBase α) (sX' sY' : Finset α) (Wn : Γ → Sl → CMat α)
    (g : Γ) (i : R32) (t : T) :
    stT (Sl := Sl) (C := C) k A sX' sY' Wn (mainR g i t)
      = if i = xOf k then frame (A g t) sX' else if i = yOf k then frame (A g t) sY' else 1 := rfl

lemma stS'_main (k : Fin 18) (A : Γ → T → OBase α) (sX sY : Finset α) (g : Γ) (i : R32) (t : T) :
    stS' (Sl := Sl) (C := C) k A sX sY (mainR g i t)
      = if i = xOf k then unframe (A g t) sX else if i = yOf k then unframe (A g t) sY else 1 := rfl

lemma callF_at (k : Fin 18) (A : Γ → T → OBase α) (sX sX' sY sY' : Finset α) (Wn : Γ → Sl → CMat α)
    (f : ℕ) (y : Data α (PRole Γ T Sl C) f) (g : Γ) (i : R32) (t : T) :
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

lemma callB_at (k : Fin 18) (A : Γ → T → OBase α) (sX sX' sY sY' : Finset α) (Wn : Γ → Sl → CMat α)
    (f : ℕ) (y : Data α (PRole Γ T Sl C) f) (g : Γ) (i : R32) (t : T) :
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

/-- **a forward full call moves the view of every port by `callF`.** -/
theorem view_call_fwd (k : Fin 18) (A : Γ → T → OBase α) (sY Δ : Finset α) (p : α)
    (hΔ : Disjoint (sY ∪ {p}) Δ) (hΔY : Disjoint sY Δ) (hp : Disjoint sY {p}) (Wn : Γ → Sl → CMat α)
    (f : ℕ) (y : Data α (PRole Γ T Sl C) f) (g : Γ) (t : T) :
    view f g t (multiAct f (stT k A (sY ∪ {p} ∪ Δ) (sY ∪ Δ) Wn)
        (point f (gFk k) (multiAct f (stS' k A (sY ∪ {p}) sY) y)))
      = callF (xOf k) (yOf k) (P4L.prodF f (P4L.fr (A g t) Δ)) (P4L.prodF f (fun x => (P4L.fr (A g t) {p} x)⁻¹))
          (view f g t y) := by
  have hxy := xOf_ne_yOf k
  apply S32.ext_get
  intro i
  rw [view_get, callF_at]
  by_cases hx : i = xOf k
  · subst hx
    rw [if_pos rfl, callF_get_x _ _ hxy, view_get]
    exact P4L.walsh_ratio f (A g t) (sY ∪ {p}) Δ hΔ _
  · by_cases hy : i = yOf k
    · subst hy
      rw [if_neg hx, if_pos rfl, callF_get_y, view_get, view_get, P4L.matAct_add, P4L.walsh_add,
        P4L.walsh_ratio f (A g t) sY Δ hΔY, P4L.walsh_cross f (A g t) sY Δ p hΔY hp]
      ring
    · rw [if_neg hx, if_neg hy, callF_get_o _ _ _ _ _ i hx hy, view_get]

/-- **a backward full call moves the view of every port by `callB`.** -/
theorem view_call_bwd (k : Fin 18) (A : Γ → T → OBase α) (sY Δ : Finset α) (p : α)
    (hΔ : Disjoint (sY ∪ {p}) Δ) (hΔY : Disjoint sY Δ) (hp : Disjoint sY {p}) (Wn : Γ → Sl → CMat α)
    (f : ℕ) (y : Data α (PRole Γ T Sl C) f) (g : Γ) (t : T) :
    view f g t (multiAct f (stT k A (sY ∪ {p} ∪ Δ) (sY ∪ Δ) Wn)
        (point f (gBk k) (multiAct f (stS' k A (sY ∪ {p}) sY) y)))
      = callB (xOf k) (yOf k) (P4L.prodF f (P4L.fr (A g t) Δ)) (P4L.prodF f (P4L.fr (A g t) {p})) (view f g t y) := by
  have hxy := xOf_ne_yOf k
  apply S32.ext_get
  intro i
  rw [view_get, callB_at]
  by_cases hx : i = xOf k
  · subst hx
    rw [if_pos rfl, callB_get_x _ _ hxy, view_get, view_get, P4L.matAct_sub', P4L.walsh_sub,
      P4L.walsh_ratio f (A g t) (sY ∪ {p}) Δ hΔ, P4L.walsh_cross_b f (A g t) sY Δ p hΔ hp]
    ring
  · by_cases hy : i = yOf k
    · subst hy
      rw [if_neg hx, if_pos rfl, callB_get_y, view_get]
      exact P4L.walsh_ratio f (A g t) sY Δ hΔY _
    · rw [if_neg hx, if_neg hy, callB_get_o _ _ _ _ _ i hx hy, view_get]

end CallView2

section StepsView
variable {α Γ T Sl C : Type} [Fintype α] [DecidableEq α] [Fintype Γ] [DecidableEq Γ] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]

/-- single-role steps on the two roles of a pair, each a Walsh product `m`: the window `win x y m`. -/
theorem view_steps_win (s : Finset (PRole Γ T Sl C)) (U : PRole Γ T Sl C → CMat α) (f : ℕ)
    (y : Data α (PRole Γ T Sl C) f) (g : Γ) (t : T) (x yR : R32) (hxy : x ≠ yR) (m : Sky α f → ℂ)
    (hs : ∀ i, mainR g i t ∈ s ↔ (i = x ∨ i = yR))
    (hU : ∀ i, (i = x ∨ i = yR) → ∀ v, P4L.walsh f (matAct f (U (mainR g i t)) v) = m * P4L.walsh f v) :
    view f g t (fun r => if r ∈ s then matAct f (U r) (y r) else y r) = win x yR m (view f g t y) := by
  apply S32.ext_get
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

end StepsView

section LinView
variable {α Γ T Sl C : Type} [Fintype α] [DecidableEq α] [Fintype Γ] [DecidableEq Γ] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]

/-- a gate layer on every port: the rational matrix `M` on the 32 main roles of each port, identity elsewhere. -/
def linMat (M : Matrix R32 R32 ℚ) : Matrix (PRole Γ T Sl C) (PRole Γ T Sl C) ℚ := fun r r' =>
  match r, r' with
  | .inl (.inl (g, (i, t))), .inl (.inl (g', (i', t'))) => if g = g' ∧ t = t' then M i i' else 0
  | .inl (.inl _), _ => 0
  | _, .inl (.inl _) => 0
  | r, r' => if r = r' then 1 else 0

lemma R32_univ : (Finset.univ : Finset R32) = {.x0, .y0, .x1, .y1, .x2, .y2, .x3, .y3, .x4, .y4, .x5, .y5, .x6, .y6, .x7, .y7, .x8, .y8, .x9, .y9, .x10, .y10, .x11, .y11, .x12, .y12, .x13, .y13, .x14, .y14, .x15, .y15} := rfl

lemma R32_sum {M : Type*} [AddCommMonoid M] (φ : R32 → M) :
    ∑ i, φ i = φ .x0 + (φ .y0 + (φ .x1 + (φ .y1 + (φ .x2 + (φ .y2 + (φ .x3 + (φ .y3 + (φ .x4 + (φ .y4 + (φ .x5 + (φ .y5 + (φ .x6 + (φ .y6 + (φ .x7 + (φ .y7 + (φ .x8 + (φ .y8 + (φ .x9 + (φ .y9 + (φ .x10 + (φ .y10 + (φ .x11 + (φ .y11 + (φ .x12 + (φ .y12 + (φ .x13 + (φ .y13 + (φ .x14 + (φ .y14 + (φ .x15 + (φ .y15))))))))))))))))))))))))))))))) := by
  rw [R32_univ]
  simp [Finset.sum_insert]

def S32.ofFun {R : Type*} (v : R32 → R) : S32 R :=
  ⟨v .x0, v .y0, v .x1, v .y1, v .x2, v .y2, v .x3, v .y3, v .x4, v .y4, v .x5, v .y5, v .x6, v .y6, v .x7, v .y7, v .x8, v .y8, v .x9, v .y9, v .x10, v .y10, v .x11, v .y11, v .x12, v .y12, v .x13, v .y13, v .x14, v .y14, v .x15, v .y15⟩

lemma S32.ofFun_get {R : Type*} (v : R32 → R) (i : R32) : (S32.ofFun v).get i = v i := by
  cases i <;> rfl

/-- the gate layer on one port's view. -/
def lin32 {β : Type*} (M : Matrix R32 R32 ℚ) (u : S32 (β → ℂ)) : S32 (β → ℂ) :=
  S32.ofFun fun i => ∑ i', ((M i i' : ℚ) : ℂ) • u.get i'

lemma linMat_at (M : Matrix R32 R32 ℚ) (f : ℕ) (y : Data α (PRole Γ T Sl C) f) (g : Γ) (i : R32) (t : T) :
    point f (actPoint (linMat M)) y (mainR g i t) = ∑ i', ((M i i' : ℚ) : ℂ) • y (mainR g i' t) := by
  funext pt
  simp only [point, actPoint, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  have h2 : ∑ x : Γ × (Fin 18 × Sl), ((linMat (Γ := Γ) (T := T) (Sl := Sl) (C := C) M (mainR g i t)
      (Sum.inl (Sum.inr x)) : ℚ) : ℂ) * y (Sum.inl (Sum.inr x)) pt = 0 := by
    apply Finset.sum_eq_zero; intro x _; simp [linMat, mainR]
  have h3 : ∑ x : Γ × C, ((linMat (Γ := Γ) (T := T) (Sl := Sl) (C := C) M (mainR g i t)
      (Sum.inr (Sum.inl x)) : ℚ) : ℂ) * y (Sum.inr (Sum.inl x)) pt = 0 := by
    apply Finset.sum_eq_zero; intro x _; simp [linMat, mainR]
  have h4 : ∑ x : Γ × (Fin 15 × T), ((linMat (Γ := Γ) (T := T) (Sl := Sl) (C := C) M (mainR g i t)
      (Sum.inr (Sum.inr x)) : ℚ) : ℂ) * y (Sum.inr (Sum.inr x)) pt = 0 := by
    apply Finset.sum_eq_zero; intro x _; simp [linMat, mainR]
  rw [h2, h3, h4]
  simp only [add_zero]
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

/-- **a gate layer moves the view of every port by `lin32`.** -/
theorem view_linMat (M : Matrix R32 R32 ℚ) (f : ℕ) (y : Data α (PRole Γ T Sl C) f) (g : Γ) (t : T) :
    view f g t (point f (actPoint (linMat M)) y) = lin32 M (view f g t y) := by
  apply S32.ext_get
  intro i
  rw [view_get, linMat_at, lin32, S32.ofFun_get, P4L.walsh_sum]
  apply Finset.sum_congr rfl
  intro i' _
  rw [P4L.walsh_smul, view_get]

/-- a gate layer leaves the other roles unchanged. -/
lemma linMat_other (M : Matrix R32 R32 ℚ) (f : ℕ) (y : Data α (PRole Γ T Sl C) f) (r : PRole Γ T Sl C)
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
end P16A8
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.P16A8.view_call_fwd
#print axioms OAI.PowerSaving.P16A8.view_linMat
