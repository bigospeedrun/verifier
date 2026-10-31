import Submission.Work.P16A8.Stages
import Submission.Work.P16A8.Windows
import Submission.Work.P16A8.Thin
import Submission.Work.P4L.Seg
-- changed for the tensor-power extension (30103/10000000); see Submission.lean

/-!
# P16A8 (p16a8), the gate layers and the fresh roles of the word

The fresh helpers are untouched by everything but their own call; the role sets of the word; the 32 x 32 rational
matrices of the bridges, the signed exchanges and the boundary adapters, and their action on the view.
No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace OAI
namespace PowerSaving
namespace P16A8
open Binary Matrix Finset RAM SS CB RF BC GX GF XHostTW

noncomputable section

section FreshAt
variable {α Γ T Sl C : Type} [Fintype α] [DecidableEq α] [Fintype Γ] [DecidableEq Γ] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]

lemma freshR_ne_mainR (g g' : Γ) (k : Fin 18) (q : Sl) (i : R32) (t : T) :
    freshR (T := T) (C := C) g k q ≠ mainR (Sl := Sl) g' i t := by
  intro h
  simp [freshR, mainR] at h

lemma callOpF_fresh (k : Fin 18) (A : Γ → T → OBase α) (sX sX' sY sY' : Finset α) (Wn : Γ → Sl → CMat α)
    (f : ℕ) (y : Data α (PRole Γ T Sl C) f) (g : Γ) (k' : Fin 18) (q : Sl) :
    multiAct f (stT k A sX' sY' Wn) (point f (gFk k) (multiAct f (stS' k A sX sY) y)) (freshR g k' q)
      = matAct f (if k' = k then Wn g q else 1) (y (freshR g k' q)) := by
  have e1 : stT (Sl := Sl) (C := C) k A sX' sY' Wn (freshR g k' q) = if k' = k then Wn g q else 1 := by
    simp only [stT, freshR, Matrix.mul_one]
  have e2 : point f (gFk k) (multiAct f (stS' k A sX sY) y) (freshR g k' q) = y (freshR g k' q) := by
    funext pt
    simp only [point, gFk, freshR, multiAct, stS', matAct_one]
  show matAct f (stT k A sX' sY' Wn (freshR g k' q))
      (point f (gFk k) (multiAct f (stS' k A sX sY) y) (freshR g k' q)) = _
  rw [e1, e2]

lemma callOpB_fresh (k : Fin 18) (A : Γ → T → OBase α) (sX sX' sY sY' : Finset α) (Wn : Γ → Sl → CMat α)
    (f : ℕ) (y : Data α (PRole Γ T Sl C) f) (g : Γ) (k' : Fin 18) (q : Sl) :
    multiAct f (stT k A sX' sY' Wn) (point f (gBk k) (multiAct f (stS' k A sX sY) y)) (freshR g k' q)
      = matAct f (if k' = k then Wn g q else 1) (y (freshR g k' q)) := by
  have e1 : stT (Sl := Sl) (C := C) k A sX' sY' Wn (freshR g k' q) = if k' = k then Wn g q else 1 := by
    simp only [stT, freshR, Matrix.mul_one]
  have e2 : point f (gBk k) (multiAct f (stS' k A sX sY) y) (freshR g k' q) = y (freshR g k' q) := by
    funext pt
    simp only [point, gBk, freshR, multiAct, stS', matAct_one]
  show matAct f (stT k A sX' sY' Wn (freshR g k' q))
      (point f (gBk k) (multiAct f (stS' k A sX sY) y) (freshR g k' q)) = _
  rw [e1, e2]

lemma linMat_fresh (M : Matrix R32 R32 ℚ) (f : ℕ) (y : Data α (PRole Γ T Sl C) f) (g : Γ) (k : Fin 18) (q : Sl) :
    point f (actPoint (linMat M)) y (freshR g k q) = y (freshR g k q) :=
  linMat_other M f y (freshR g k q) (fun g' i t => freshR_ne_mainR g g' k q i t)

end FreshAt

section OwnerFresh
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T] [Fintype Sl] [DecidableEq Sl]
  [Fintype C] [DecidableEq C] (l : H)

lemma fresh_not_ownerSet (x y : R32) (g : Orth (LC (Fin 17) H l)) (k : Fin 18) (q : Sl) :
    freshR (T := T) (C := C) g k q ∉ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l x y := by
  intro h
  obtain ⟨g', i, t, e⟩ := ownerSet_main l x y _ h
  exact freshR_ne_mainR g g' k q i t e

lemma card_ownerSet (x y : R32) (hxy : x ≠ y) :
    (ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l x y).card
      = 2 * (Fintype.card (Orth (LC (Fin 17) H l)) * Fintype.card T) := by
  have inj : ∀ i : R32, Function.Injective
      (fun p : Orth (LC (Fin 17) H l) × T => (mainR (Sl := Sl) (C := C) p.1 i p.2)) := by
    intro i a b h
    simp only [mainR, Sum.inl.injEq, Prod.mk.injEq] at h
    exact Prod.ext h.1 h.2.2
  have hd : Disjoint
      ((Finset.univ : Finset (Orth (LC (Fin 17) H l) × T)).image (fun p => mainR (Sl := Sl) (C := C) p.1 x p.2))
      ((Finset.univ : Finset (Orth (LC (Fin 17) H l) × T)).image (fun p => mainR (Sl := Sl) (C := C) p.1 y p.2)) := by
    rw [Finset.disjoint_left]
    intro r h1 h2
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp h1
    obtain ⟨b, -, hb⟩ := Finset.mem_image.mp h2
    simp only [mainR, Sum.inl.injEq, Prod.mk.injEq] at hb
    exact hxy hb.2.1.symm
  unfold ownerSet
  rw [Finset.card_union_of_disjoint hd, Finset.card_image_of_injective _ (inj x),
    Finset.card_image_of_injective _ (inj y), Finset.card_univ, Fintype.card_prod]
  ring

end OwnerFresh

section RoleSets
variable {α Γ T Sl C : Type} [Fintype α] [DecidableEq α] [Fintype Γ] [DecidableEq Γ] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]

def freshAll : Finset (PRole Γ T Sl C) :=
  (Finset.univ : Finset (Γ × Fin 18 × Sl)).image fun p => freshR p.1 p.2.1 p.2.2

def mainAll : Finset (PRole Γ T Sl C) :=
  (Finset.univ : Finset (Γ × R32 × T)).image fun p => mainR p.1 p.2.1 p.2.2

lemma fresh_mem_freshAll (g : Γ) (k : Fin 18) (q : Sl) :
    freshR (T := T) (C := C) g k q ∈ freshAll (Γ := Γ) (T := T) (Sl := Sl) (C := C) :=
  Finset.mem_image.mpr ⟨(g, k, q), Finset.mem_univ _, rfl⟩

lemma main_mem_mainAll (g : Γ) (i : R32) (t : T) :
    mainR (Sl := Sl) (C := C) g i t ∈ mainAll (Γ := Γ) (T := T) (Sl := Sl) (C := C) :=
  Finset.mem_image.mpr ⟨(g, i, t), Finset.mem_univ _, rfl⟩

lemma main_not_freshAll (g : Γ) (i : R32) (t : T) :
    mainR (Sl := Sl) (C := C) g i t ∉ freshAll (Γ := Γ) (T := T) (Sl := Sl) (C := C) := by
  intro h
  obtain ⟨⟨g', k, q⟩, -, e⟩ := Finset.mem_image.mp h
  exact freshR_ne_mainR g' g k q i t e

lemma fresh_not_mainAll (g : Γ) (k : Fin 18) (q : Sl) :
    freshR (T := T) (C := C) g k q ∉ mainAll (Γ := Γ) (T := T) (Sl := Sl) (C := C) := by
  intro h
  obtain ⟨⟨g', i, t⟩, -, e⟩ := Finset.mem_image.mp h
  exact freshR_ne_mainR g g' k q i t e.symm

lemma of_mem_freshAll {r : PRole Γ T Sl C} (h : r ∈ freshAll (Γ := Γ) (T := T) (Sl := Sl) (C := C)) :
    ∃ g k q, r = freshR g k q := by
  obtain ⟨⟨g, k, q⟩, -, e⟩ := Finset.mem_image.mp h
  exact ⟨g, k, q, e.symm⟩

def freshMat (Z : Fin 18 → Γ → Sl → CMat α) : PRole Γ T Sl C → CMat α
  | .inl (.inr (g, (k, q))) => Z k g q
  | _ => 1

def freshTgt (D : Sl → Finset α) : PRole Γ T Sl C → CMat α
  | .inl (.inr (_, (_, q))) => pk (D q)
  | _ => 1

def freshCost (c : Sl → (ℕ → ℝ) → ℝ) : PRole Γ T Sl C → (ℕ → ℝ) → ℝ
  | .inl (.inr (_, (_, q))) => c q
  | _ => fun _ => 0

lemma sum_freshAll (c : Sl → (ℕ → ℝ) → ℝ) (φ : ℕ → ℝ) :
    ∑ r ∈ freshAll (Γ := Γ) (T := T) (Sl := Sl) (C := C), freshCost c r φ
      = (Fintype.card Γ : ℝ) * 18 * ∑ q, c q φ := by
  unfold freshAll
  rw [Finset.sum_image (fun a _ b _ h => by
    simp only [freshR, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq] at h
    exact Prod.ext h.1 (Prod.ext h.2.1 h.2.2))]
  have e : ∀ p : Γ × Fin 18 × Sl, freshCost (T := T) (C := C) c (freshR p.1 p.2.1 p.2.2) φ = c p.2.2 φ :=
    fun p => rfl
  simp only [e, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

end RoleSets

section Gates

def gateM (dst src : R32) (c : ℚ) : Matrix R32 R32 ℚ := fun i j =>
  if i = dst then (if j = dst then 1 else if j = src then c else 0) else (if j = i then 1 else 0)

def swapM (x y : R32) : Matrix R32 R32 ℚ := fun i j =>
  if i = y then (if j = x then -1 else 0) else if i = x then (if j = y then 1 else 0) else (if j = i then 1 else 0)

lemma lin32_gateM {β : Type*} (dst src : R32) (hds : dst ≠ src) (c : ℚ) (u : S32 (β → ℂ)) :
    lin32 (gateM dst src c) u = gate dst src (fun _ => (c : ℂ)) u := by
  apply S32.ext_get
  intro i
  rw [lin32, S32.ofFun_get]
  unfold gate
  by_cases hi : i = dst
  · rw [hi, S32.get_set_same, Fintype.sum_eq_add dst src hds]
    · have h1 : gateM dst src c dst dst = 1 := by simp [gateM]
      have h2 : gateM dst src c dst src = c := by simp [gateM, Ne.symm hds]
      rw [h1, h2, Rat.cast_one, one_smul]
      funext x
      simp [Pi.mul_apply, Pi.smul_apply, Pi.add_apply]
    · intro j hj
      have h3 : gateM dst src c dst j = 0 := by simp [gateM, hj.1, hj.2]
      rw [h3, Rat.cast_zero, zero_smul]
  · rw [S32.get_set_ne _ _ _ _ hi, Fintype.sum_eq_single i]
    · have h1 : gateM dst src c i i = 1 := by simp [gateM, hi]
      rw [h1, Rat.cast_one, one_smul]
    · intro j hj
      have h3 : gateM dst src c i j = 0 := by simp [gateM, hi, hj]
      rw [h3, Rat.cast_zero, zero_smul]

lemma lin32_gate_one {β : Type*} (dst src : R32) (hds : dst ≠ src) (u : S32 (β → ℂ)) :
    lin32 (gateM dst src 1) u = gate dst src 1 u := by
  rw [lin32_gateM dst src hds]
  have e : (fun _ : β => ((1 : ℚ) : ℂ)) = 1 := by funext x; simp
  rw [e]

lemma lin32_gate_neg {β : Type*} (dst src : R32) (hds : dst ≠ src) (u : S32 (β → ℂ)) :
    lin32 (gateM dst src (-1)) u = gate dst src (-1) u := by
  rw [lin32_gateM dst src hds]
  have e : (fun _ : β => ((-1 : ℚ) : ℂ)) = -1 := by funext x; simp
  rw [e]

lemma lin32_swapM {β : Type*} (x y : R32) (hxy : x ≠ y) (u : S32 (β → ℂ)) : lin32 (swapM x y) u = swap x y u := by
  apply S32.ext_get
  intro i
  rw [lin32, S32.ofFun_get]
  unfold swap
  by_cases hy : i = y
  · rw [hy, S32.get_set_same, Fintype.sum_eq_single x]
    · have h1 : swapM x y y x = -1 := by simp [swapM]
      rw [h1, Rat.cast_neg, Rat.cast_one, neg_one_smul]
    · intro j hj
      have h3 : swapM x y y j = 0 := by simp [swapM, hj]
      rw [h3, Rat.cast_zero, zero_smul]
  · rw [S32.get_set_ne _ _ _ _ hy]
    by_cases hx : i = x
    · rw [hx, S32.get_set_same, Fintype.sum_eq_single y]
      · have h1 : swapM x y x y = 1 := by simp [swapM, hxy]
        rw [h1, Rat.cast_one, one_smul]
      · intro j hj
        have h3 : swapM x y x j = 0 := by simp [swapM, hxy, hj]
        rw [h3, Rat.cast_zero, zero_smul]
    · rw [S32.get_set_ne _ _ _ _ hx, Fintype.sum_eq_single i]
      · have h1 : swapM x y i i = 1 := by simp [swapM, hy, hx]
        rw [h1, Rat.cast_one, one_smul]
      · intro j hj
        have h3 : swapM x y i j = 0 := by simp [swapM, hy, hx, hj]
        rw [h3, Rat.cast_zero, zero_smul]

/-- a row of an 32 x 32 matrix. -/
def row32 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 : ℚ) : R32 → ℚ
  | .x0 => a0
  | .y0 => a1
  | .x1 => a2
  | .y1 => a3
  | .x2 => a4
  | .y2 => a5
  | .x3 => a6
  | .y3 => a7
  | .x4 => a8
  | .y4 => a9
  | .x5 => a10
  | .y5 => a11
  | .x6 => a12
  | .y6 => a13
  | .x7 => a14
  | .y7 => a15
  | .x8 => a16
  | .y8 => a17
  | .x9 => a18
  | .y9 => a19
  | .x10 => a20
  | .y10 => a21
  | .x11 => a22
  | .y11 => a23
  | .x12 => a24
  | .y12 => a25
  | .x13 => a26
  | .y13 => a27
  | .x14 => a28
  | .y14 => a29
  | .x15 => a30
  | .y15 => a31

/-- the input adapter `A` (`adaptIn`): physical role `i` := `∑ j, A i j * (adapted role j)`. -/
def AinM : Matrix R32 R32 ℚ := fun i =>
  match i with
  | .x0 => row32 0 0 0 0 0 0 0 1 (-1) 1 (-1) 1 (-1) 1 (-1) 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
  | .y0 => row32 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0
  | .x1 => row32 0 0 0 0 0 0 0 0 1 (-1) 1 (-1) 1 (-1) 1 (-1) 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
  | .y1 => row32 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 (-1) 0 0 0 0 0 0 0
  | .x2 => row32 0 0 0 0 0 0 0 0 0 1 (-1) 1 (-1) 1 (-1) 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
  | .y2 => row32 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 (-1) 1 0 0 0 0 0 0
  | .x3 => row32 0 0 0 0 0 0 0 0 0 0 1 (-1) 1 (-1) 1 (-1) 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
  | .y3 => row32 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 (-1) 0 0 0 0 0
  | .x4 => row32 0 0 0 0 0 0 0 0 0 0 0 1 (-1) 1 (-1) 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
  | .y4 => row32 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 (-1) 1 0 0 0 0
  | .x5 => row32 0 0 0 0 0 0 0 0 0 0 0 0 1 (-1) 1 (-1) 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
  | .y5 => row32 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 (-1) 0 0 0
  | .x6 => row32 0 0 0 0 0 0 0 0 0 0 0 0 0 1 (-1) 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
  | .y6 => row32 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 (-1) 1 0 0
  | .x7 => row32 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 (-1) 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
  | .y7 => row32 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 (-1) 0
  | .x8 => row32 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
  | .y8 => row32 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 (-1) 1
  | .x9 => row32 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
  | .y9 => row32 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0
  | .x10 => row32 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
  | .y10 => row32 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0
  | .x11 => row32 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
  | .y11 => row32 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0
  | .x12 => row32 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
  | .y12 => row32 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0
  | .x13 => row32 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
  | .y13 => row32 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0
  | .x14 => row32 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
  | .y14 => row32 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0
  | .x15 => row32 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
  | .y15 => row32 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0

/-- the output adapter `B` (`adaptOut`): adapted role `i` := `∑ r, B i r * (physical role r)`. -/
def AoutM : Matrix R32 R32 ℚ := fun i =>
  match i with
  | .x0 => row32 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0
  | .y0 => row32 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0
  | .x1 => row32 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0
  | .y1 => row32 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0
  | .x2 => row32 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0
  | .y2 => row32 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0
  | .x3 => row32 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0
  | .y3 => row32 1 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
  | .x4 => row32 0 0 1 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
  | .y4 => row32 0 0 0 0 1 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
  | .x5 => row32 0 0 0 0 0 0 1 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
  | .y5 => row32 0 0 0 0 0 0 0 0 1 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
  | .x6 => row32 0 0 0 0 0 0 0 0 0 0 1 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
  | .y6 => row32 0 0 0 0 0 0 0 0 0 0 0 0 1 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
  | .x7 => row32 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
  | .y7 => row32 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
  | .x8 => row32 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1
  | .y8 => row32 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0
  | .x9 => row32 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0
  | .y9 => row32 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0
  | .x10 => row32 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0
  | .y10 => row32 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0
  | .x11 => row32 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0
  | .y11 => row32 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
  | .x12 => row32 0 1 0 (-1) 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
  | .y12 => row32 0 1 0 (-1) 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
  | .x13 => row32 0 1 0 (-1) 0 1 0 (-1) 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
  | .y13 => row32 0 1 0 (-1) 0 1 0 (-1) 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
  | .x14 => row32 0 1 0 (-1) 0 1 0 (-1) 0 1 0 (-1) 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
  | .y14 => row32 0 1 0 (-1) 0 1 0 (-1) 0 1 0 (-1) 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
  | .x15 => row32 0 1 0 (-1) 0 1 0 (-1) 0 1 0 (-1) 0 1 0 (-1) 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
  | .y15 => row32 0 1 0 (-1) 0 1 0 (-1) 0 1 0 (-1) 0 1 0 (-1) 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0

lemma lin32_AinM {β : Type*} (u : S32 (β → ℂ)) : lin32 AinM u = adaptIn u := by
  apply S32.ext_get
  intro i
  rw [lin32, S32.ofFun_get, R32_sum]
  cases i <;> simp [AinM, row32, adaptIn, S32.get] <;> ring

lemma lin32_AoutM {β : Type*} (u : S32 (β → ℂ)) : lin32 AoutM u = adaptOut u := by
  apply S32.ext_get
  intro i
  rw [lin32, S32.ofFun_get, R32_sum]
  cases i <;> simp [AoutM, row32, adaptOut, S32.get] <;> ring

end Gates

end
end P16A8
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.P16A8.lin32_AinM
#print axioms OAI.PowerSaving.P16A8.lin32_AoutM
