import Submission.Work.P4L.Stages
import Submission.Work.P4L.Windows
import Submission.Work.P4L.Fresh
-- changed for the tensor-power extension (30103/10000000); see Submission.lean

/-!
# P4-L, part 13: the gate layers, the free shifts and the fresh roles of the P4-L word

The generic pieces the word (Work/P4L/Word, generated) is assembled from:

* `gstep_shift`                 one free shift letter is a generalised step `1 → shift z` of price `0`;
* `freshR_ne_mainR`, `fresh_not_ownerSet`, `callOpF_fresh`, `callOpB_fresh`   a native call acts on the fresh helper
                                `(g, k', q)` by its residual if `k' = k`, by nothing otherwise; windows and gate layers
                                do not touch the helpers;
* `gateM`, `swapM`, `AinM`, `AoutM`, and `lin8_gate_one`, `lin8_gate_neg`, `lin8_swapM`, `lin8_AinM`, `lin8_AoutM`
                                the 8 x 8 rational matrices of the bridges, the signed exchanges and the boundary adapters,
                                and their action on the view (the controller events of Work/P4L/S8 and `P4Ctrl.adaptIn`,
                                `P4Ctrl.adaptOut`);
* `prodF_union`, `prodF_incr`, `incr_sub_setX`, `pivot_sub_setX`, `disj_incr`   products of stage
                                transforms are the Walsh functions of unions of increments;
* `normal_q`, `normal_qi`       the endpoint normaliser: a role whose Walsh coordinates are multiplied by
                                `prodF (fr A S)` (resp. `prodF (sign (A.v p ·)) * prodF (fr A S)`) ends, after ONE free shift,
                                at `blockMat (A.fam S)` of its own input.
No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace OAI
namespace PowerSaving
namespace P4L
open Binary Matrix Finset RAM SS CB RF BC GX GF XHostTW P4Ctrl

noncomputable section

/-! ### one free shift -/

section Shift
variable {α ρ : Type} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

/-- one free shift on role `r` is a generalised step from `1` to `shift z`, price `0`. -/
lemma gstep_shift (r : ρ) (z : Space α) : GStep r (1 : CMat α) (Binary.shift z) (fun _ => 0) :=
  ⟨[GMove.old (BMove.shift r z)], Binary.shift z,
    fun mv hmv => by rw [List.mem_singleton] at hmv; subst hmv; trivial,
    fun φ => by simp [GWord.costR, GMove.costR, GMove.shadow, BMove.costR, BMove.rk?],
    Matrix.mul_one _, fun f x => rfl⟩

end Shift

/-! ### the fresh helpers are untouched by everything but their own call -/

section FreshAt
variable {α Γ T Sl C : Type} [Fintype α] [DecidableEq α] [Fintype Γ] [DecidableEq Γ] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]

lemma freshR_ne_mainR (g g' : Γ) (k : Fin 9) (q : Sl) (i : R8) (t : T) :
    freshR (T := T) (C := C) g k q ≠ mainR (Sl := Sl) g' i t := by
  intro h
  simp [freshR, mainR] at h

/-- a forward call at a fresh helper: its residual if the helper belongs to the call. -/
lemma callOpF_fresh (k : Fin 9) (A : Γ → T → OBase α) (sX sX' sY sY' : Finset α) (Wn : Γ → Sl → CMat α)
    (f : ℕ) (y : Data α (PRole Γ T Sl C) f) (g : Γ) (k' : Fin 9) (q : Sl) :
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

/-- a backward call at a fresh helper. -/
lemma callOpB_fresh (k : Fin 9) (A : Γ → T → OBase α) (sX sX' sY sY' : Finset α) (Wn : Γ → Sl → CMat α)
    (f : ℕ) (y : Data α (PRole Γ T Sl C) f) (g : Γ) (k' : Fin 9) (q : Sl) :
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

/-- a gate layer does not touch a fresh helper. -/
lemma linMat_fresh (M : Matrix R8 R8 ℚ) (f : ℕ) (y : Data α (PRole Γ T Sl C) f) (g : Γ) (k : Fin 9) (q : Sl) :
    point f (actPoint (linMat M)) y (freshR g k q) = y (freshR g k q) :=
  linMat_other M f y (freshR g k q) (fun g' i t => freshR_ne_mainR g g' k q i t)

/-- single-role steps on a set without the helper do not touch it. -/
lemma steps_out (s : Finset (PRole Γ T Sl C)) (U : PRole Γ T Sl C → CMat α) (f : ℕ)
    (y : Data α (PRole Γ T Sl C) f) (r : PRole Γ T Sl C) (hr : r ∉ s) :
    (fun r => if r ∈ s then matAct f (U r) (y r) else y r) r = y r := by
  simp only [hr, if_false]

end FreshAt

section OwnerFresh
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T] [Fintype Sl] [DecidableEq Sl]
  [Fintype C] [DecidableEq C] (l : H)

lemma fresh_not_ownerSet (x y : R8) (g : Orth (LC (Fin 8) H l)) (k : Fin 9) (q : Sl) :
    freshR (T := T) (C := C) g k q ∉ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l x y := by
  intro h
  obtain ⟨g', i, t, e⟩ := ownerSet_main l x y _ h
  exact freshR_ne_mainR g g' k q i t e

end OwnerFresh

/-! ### the role sets of the word -/

section RoleSets
variable {α Γ T Sl C : Type} [Fintype α] [DecidableEq α] [Fintype Γ] [DecidableEq Γ] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]

/-- all fresh helpers (all gauges, stages and slots). -/
def freshAll : Finset (PRole Γ T Sl C) :=
  (Finset.univ : Finset (Γ × Fin 9 × Sl)).image fun p => freshR p.1 p.2.1 p.2.2

/-- all main roles (all gauges, kinds and ports). -/
def mainAll : Finset (PRole Γ T Sl C) :=
  (Finset.univ : Finset (Γ × R8 × T)).image fun p => mainR p.1 p.2.1 p.2.2

lemma fresh_mem_freshAll (g : Γ) (k : Fin 9) (q : Sl) :
    freshR (T := T) (C := C) g k q ∈ freshAll (Γ := Γ) (T := T) (Sl := Sl) (C := C) :=
  Finset.mem_image.mpr ⟨(g, k, q), Finset.mem_univ _, rfl⟩

lemma main_mem_mainAll (g : Γ) (i : R8) (t : T) :
    mainR (Sl := Sl) (C := C) g i t ∈ mainAll (Γ := Γ) (T := T) (Sl := Sl) (C := C) :=
  Finset.mem_image.mpr ⟨(g, i, t), Finset.mem_univ _, rfl⟩

lemma main_not_freshAll (g : Γ) (i : R8) (t : T) :
    mainR (Sl := Sl) (C := C) g i t ∉ freshAll (Γ := Γ) (T := T) (Sl := Sl) (C := C) := by
  intro h
  obtain ⟨⟨g', k, q⟩, -, e⟩ := Finset.mem_image.mp h
  exact freshR_ne_mainR g' g k q i t e

lemma fresh_not_mainAll (g : Γ) (k : Fin 9) (q : Sl) :
    freshR (T := T) (C := C) g k q ∉ mainAll (Γ := Γ) (T := T) (Sl := Sl) (C := C) := by
  intro h
  obtain ⟨⟨g', i, t⟩, -, e⟩ := Finset.mem_image.mp h
  exact freshR_ne_mainR g g' k q i t e.symm

lemma of_mem_freshAll {r : PRole Γ T Sl C} (h : r ∈ freshAll (Γ := Γ) (T := T) (Sl := Sl) (C := C)) :
    ∃ g k q, r = freshR g k q := by
  obtain ⟨⟨g, k, q⟩, -, e⟩ := Finset.mem_image.mp h
  exact ⟨g, k, q, e.symm⟩

lemma of_mem_mainAll {r : PRole Γ T Sl C} (h : r ∈ mainAll (Γ := Γ) (T := T) (Sl := Sl) (C := C)) :
    ∃ g i t, r = mainR g i t := by
  obtain ⟨⟨g, i, t⟩, -, e⟩ := Finset.mem_image.mp h
  exact ⟨g, i, t, e.symm⟩

/-- a matrix per fresh helper, `1` elsewhere. -/
def freshMat (Z : Fin 9 → Γ → Sl → CMat α) : PRole Γ T Sl C → CMat α
  | .inl (.inr (g, (k, q))) => Z k g q
  | _ => 1

/-- the target of every fresh helper: `pk (D q)`, `1` elsewhere. -/
def freshTgt (D : Sl → Finset α) : PRole Γ T Sl C → CMat α
  | .inl (.inr (_, (_, q))) => pk (D q)
  | _ => 1

/-- a price per slot on every fresh helper, `0` elsewhere. -/
def freshCost (c : Sl → (ℕ → ℝ) → ℝ) : PRole Γ T Sl C → (ℕ → ℝ) → ℝ
  | .inl (.inr (_, (_, q))) => c q
  | _ => fun _ => 0

/-- the helpers' prices add up to `|Γ| * 9` copies of the slot prices. -/
lemma sum_freshAll (c : Sl → (ℕ → ℝ) → ℝ) (φ : ℕ → ℝ) :
    ∑ r ∈ freshAll (Γ := Γ) (T := T) (Sl := Sl) (C := C), freshCost c r φ
      = (Fintype.card Γ : ℝ) * 9 * ∑ q, c q φ := by
  unfold freshAll
  rw [Finset.sum_image (fun a _ b _ h => by
    simp only [freshR, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq] at h
    exact Prod.ext h.1 (Prod.ext h.2.1 h.2.2))]
  have e : ∀ p : Γ × Fin 9 × Sl, freshCost (T := T) (C := C) c (freshR p.1 p.2.1 p.2.2) φ = c p.2.2 φ :=
    fun p => rfl
  simp only [e, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

end RoleSets

section OwnerCard
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T] [Fintype Sl] [DecidableEq Sl]
  [Fintype C] [DecidableEq C] (l : H)

/-- the owner set of a pair has two roles per gauge and port. -/
lemma card_ownerSet (x y : R8) (hxy : x ≠ y) :
    (ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l x y).card
      = 2 * (Fintype.card (Orth (LC (Fin 8) H l)) * Fintype.card T) := by
  have inj : ∀ i : R8, Function.Injective
      (fun p : Orth (LC (Fin 8) H l) × T => (mainR (Sl := Sl) (C := C) p.1 i p.2)) := by
    intro i a b h
    simp only [mainR, Sum.inl.injEq, Prod.mk.injEq] at h
    exact Prod.ext h.1 h.2.2
  have hd : Disjoint
      ((Finset.univ : Finset (Orth (LC (Fin 8) H l) × T)).image (fun p => mainR (Sl := Sl) (C := C) p.1 x p.2))
      ((Finset.univ : Finset (Orth (LC (Fin 8) H l) × T)).image (fun p => mainR (Sl := Sl) (C := C) p.1 y p.2)) := by
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

end OwnerCard

/-! ### the gate matrices and their action on the view -/

section Gates

/-- the elementary bridge `dst += c src` on the main roles of every port. -/
def gateM (dst src : R8) (c : ℚ) : Matrix R8 R8 ℚ := fun i j =>
  if i = dst then (if j = dst then 1 else if j = src then c else 0) else (if j = i then 1 else 0)

/-- the signed exchange `(x, y) ↦ (y, -x)` on the main roles of every port. -/
def swapM (x y : R8) : Matrix R8 R8 ℚ := fun i j =>
  if i = y then (if j = x then -1 else 0) else if i = x then (if j = y then 1 else 0) else (if j = i then 1 else 0)

lemma lin8_gateM {β : Type*} (dst src : R8) (hds : dst ≠ src) (c : ℚ) (u : S8 (β → ℂ)) :
    lin8 (gateM dst src c) u = gate dst src (fun _ => (c : ℂ)) u := by
  apply S8.ext_get
  intro i
  rw [lin8, S8.ofFun_get]
  unfold gate
  by_cases hi : i = dst
  · rw [hi, S8.get_set_same, Fintype.sum_eq_add dst src hds]
    · have h1 : gateM dst src c dst dst = 1 := by simp [gateM]
      have h2 : gateM dst src c dst src = c := by simp [gateM, Ne.symm hds]
      rw [h1, h2, Rat.cast_one, one_smul]
      funext x
      simp [Pi.mul_apply, Pi.smul_apply, Pi.add_apply]
    · intro j hj
      have h3 : gateM dst src c dst j = 0 := by simp [gateM, hj.1, hj.2]
      rw [h3, Rat.cast_zero, zero_smul]
  · rw [S8.get_set_ne _ _ _ _ hi, Fintype.sum_eq_single i]
    · have h1 : gateM dst src c i i = 1 := by simp [gateM, hi]
      rw [h1, Rat.cast_one, one_smul]
    · intro j hj
      have h3 : gateM dst src c i j = 0 := by simp [gateM, hi, hj]
      rw [h3, Rat.cast_zero, zero_smul]

lemma lin8_gate_one {β : Type*} (dst src : R8) (hds : dst ≠ src) (u : S8 (β → ℂ)) :
    lin8 (gateM dst src 1) u = gate dst src 1 u := by
  rw [lin8_gateM dst src hds]
  have e : (fun _ : β => ((1 : ℚ) : ℂ)) = 1 := by funext x; simp
  rw [e]

lemma lin8_gate_neg {β : Type*} (dst src : R8) (hds : dst ≠ src) (u : S8 (β → ℂ)) :
    lin8 (gateM dst src (-1)) u = gate dst src (-1) u := by
  rw [lin8_gateM dst src hds]
  have e : (fun _ : β => ((-1 : ℚ) : ℂ)) = -1 := by funext x; simp
  rw [e]

lemma lin8_swapM {β : Type*} (x y : R8) (hxy : x ≠ y) (u : S8 (β → ℂ)) : lin8 (swapM x y) u = swap x y u := by
  apply S8.ext_get
  intro i
  rw [lin8, S8.ofFun_get]
  unfold swap
  by_cases hy : i = y
  · rw [hy, S8.get_set_same, Fintype.sum_eq_single x]
    · have h1 : swapM x y y x = -1 := by simp [swapM]
      rw [h1, Rat.cast_neg, Rat.cast_one, neg_one_smul]
    · intro j hj
      have h3 : swapM x y y j = 0 := by simp [swapM, hj]
      rw [h3, Rat.cast_zero, zero_smul]
  · rw [S8.get_set_ne _ _ _ _ hy]
    by_cases hx : i = x
    · rw [hx, S8.get_set_same, Fintype.sum_eq_single y]
      · have h1 : swapM x y x y = 1 := by simp [swapM, hxy]
        rw [h1, Rat.cast_one, one_smul]
      · intro j hj
        have h3 : swapM x y x j = 0 := by simp [swapM, hxy, hj]
        rw [h3, Rat.cast_zero, zero_smul]
    · rw [S8.get_set_ne _ _ _ _ hx, Fintype.sum_eq_single i]
      · have h1 : swapM x y i i = 1 := by simp [swapM, hy, hx]
        rw [h1, Rat.cast_one, one_smul]
      · intro j hj
        have h3 : swapM x y i j = 0 := by simp [swapM, hy, hx, hj]
        rw [h3, Rat.cast_zero, zero_smul]

/-- a row of an 8 x 8 matrix. -/
def row8 (a0 a1 a2 a3 a4 a5 a6 a7 : ℚ) : R8 → ℚ
  | .x0 => a0 | .y0 => a1 | .x1 => a2 | .y1 => a3 | .x2 => a4 | .y2 => a5 | .x3 => a6 | .y3 => a7

/-- the input adapter `A` (`P4Ctrl.adaptIn`): physical role `i` := `∑ j, A i j * (adapted role j)`. -/
def AinM : Matrix R8 R8 ℚ := fun i =>
  match i with
  | .x0 => row8 0 1 (-1) 1 0 0 0 0
  | .y0 => row8 0 0 0 0 0 1 0 0
  | .x1 => row8 0 0 1 (-1) 0 0 0 0
  | .y1 => row8 0 0 0 0 0 1 (-1) 0
  | .x2 => row8 0 0 0 1 0 0 0 0
  | .y2 => row8 0 0 0 0 0 0 (-1) 1
  | .x3 => row8 1 0 0 0 0 0 0 0
  | .y3 => row8 0 0 0 0 1 0 0 0

/-- the output adapter `B` (`P4Ctrl.adaptOut`): adapted role `i` := `∑ r, B i r * (physical role r)`. -/
def AoutM : Matrix R8 R8 ℚ := fun i =>
  match i with
  | .x0 => row8 0 0 0 0 0 0 1 0
  | .y0 => row8 1 0 1 0 0 0 0 0
  | .x1 => row8 0 0 1 0 1 0 0 0
  | .y1 => row8 0 0 0 0 1 0 0 0
  | .x2 => row8 0 0 0 0 0 0 0 1
  | .y2 => row8 0 1 0 0 0 0 0 0
  | .x3 => row8 0 1 0 (-1) 0 0 0 0
  | .y3 => row8 0 1 0 (-1) 0 1 0 0

lemma lin8_AinM {β : Type*} (u : S8 (β → ℂ)) : lin8 AinM u = adaptIn u := by
  apply S8.ext_get
  intro i
  rw [lin8, S8.ofFun_get, R8_sum]
  cases i <;> simp [AinM, row8, adaptIn, S8.get] <;> ring

lemma lin8_AoutM {β : Type*} (u : S8 (β → ℂ)) : lin8 AoutM u = adaptOut u := by
  apply S8.ext_get
  intro i
  rw [lin8, S8.ofFun_get, R8_sum]
  cases i <;> simp [AoutM, row8, adaptOut, S8.get] <;> ring

end Gates

/-! ### products of stage transforms -/

section Incr
variable {H : Type} [Fintype H] [DecidableEq H] (l : H)

lemma prodF_union {α : Type} [Fintype α] [DecidableEq α] (f : ℕ) (A : OBase α) (s t : Finset α)
    (h : Disjoint s t) : prodF f (fr A (s ∪ t)) = prodF f (fr A s) * prodF f (fr A t) := by
  rw [fr_union A s t h]
  exact prodF_mul f (fr A s) (fr A t)

lemma incr_sub_setX (j k : ℕ) (hjk : j < k) (hk : k ≤ 9) : incr l j ⊆ setX l k := by
  have h1 : incr l j ⊆ setX l (j + 1) := by
    rw [(setX_succ l j (by omega)).1]
    exact Finset.subset_union_right
  exact h1.trans (setX_mono l (j + 1) k (by omega) hk)

lemma pivot_sub_setX (k : ℕ) (hk : k ≤ 9) : ({Sum.inl l} : Finset (LC (Fin 8) H l)) ⊆ setX l k := by
  rw [(setX_pivot l k hk).1]
  exact Finset.subset_union_right

/-- a set inside the X set of stage `k` is disjoint from the increment of stage `k`. -/
lemma disj_incr (U : Finset (LC (Fin 8) H l)) (k : ℕ) (hk : k < 9) (hU : U ⊆ setX l k) :
    Disjoint U (incr l k) :=
  Finset.disjoint_of_subset_left hU (setX_succ l k hk).2

/-- the product of the stage transforms of a window is the Walsh function of its increments. -/
lemma prodF_incr (f : ℕ) (A : OBase (LC (Fin 8) H l)) (a : ℕ) : ∀ n, a + n < 9 →
    prodF f (fr A ((Finset.range (n + 1)).biUnion fun j => incr l (a + j)))
      = ∏ j ∈ Finset.range (n + 1), prodF f (fr A (incr l (a + j)))
  | 0, _ => by
    rw [Finset.range_one, Finset.singleton_biUnion, Finset.prod_singleton]
  | n + 1, h => by
    have ih := prodF_incr f A a n (by omega)
    obtain ⟨e, -⟩ := setX_add l a n (by omega)
    have d2 := (setX_succ l (a + n + 1) (by omega)).2
    have hd : Disjoint ((Finset.range (n + 1)).biUnion fun j => incr l (a + j)) (incr l (a + (n + 1))) := by
      have hs : ((Finset.range (n + 1)).biUnion fun j => incr l (a + j)) ⊆ setX l (a + n + 1) := by
        rw [e]; exact Finset.subset_union_right
      rw [show a + (n + 1) = a + n + 1 by omega]
      exact Finset.disjoint_of_subset_left hs d2
    rw [Finset.range_add_one, Finset.biUnion_insert, Finset.prod_insert Finset.notMem_range_self,
      Finset.union_comm, prodF_union f A _ _ hd, ih, mul_comm]

end Incr

/-! ### the endpoint normaliser -/

section Normal
variable {α : Type} [Fintype α] [DecidableEq α]

/-- a role multiplied by `prodF (fr A S)` in Walsh coordinates ends, after the free shift `shift (A.corr S)`, at the
block of the lines `S` of its own input. -/
lemma normal_q (f : ℕ) (A : OBase α) (S : Finset α) (v w : Sky α f → ℂ)
    (h : walsh f w = prodF f (fr A S) * walsh f v) :
    matAct f (Binary.shift (A.corr S)) w = matAct f (blockMat (A.fam S)) v := by
  have e : w = matAct f (frame A S) v := by
    apply walsh_injective f
    rw [walsh_frame, h]
  rw [e, matAct_mul, frame_eq_shift_blockMat, MX.shift_mul_shift_self]

/-- the same with the inverse translation: the free shift is `shift (A.v p + A.corr S)`. -/
lemma normal_qi (f : ℕ) (A : OBase α) (S : Finset α) (p : α) (v w : Sky α f → ℂ)
    (h : walsh f w = prodF f (fun x => sign (dot (A.v p) x)) * prodF f (fr A S) * walsh f v) :
    matAct f (Binary.shift (A.v p + A.corr S)) w = matAct f (blockMat (A.fam S)) v := by
  have e : w = matAct f (Binary.shift (A.v p) * frame A S) v := by
    apply walsh_injective f
    rw [← matAct_mul, shift_phase, walsh_matAct_wrap, walsh_frame, h, mul_assoc]
  rw [e, matAct_mul, frame_eq_shift_blockMat, ← Matrix.mul_assoc (Binary.shift (A.v p)),
    MX.shift_mul_shift (A.v p) (A.corr S), MX.shift_mul_shift_self (A.v p + A.corr S) (blockMat (A.fam S))]

/-- the inverse translation of a port is the translation times a free phase. -/
lemma qi_split (f : ℕ) (A : OBase α) (p : α) :
    prodF f (fun x => (fr A {p} x)⁻¹) = prodF f (fr A {p}) * prodF f (fun x => sign (dot (A.v p) x)) := by
  have e : (fun x => (fr A {p} x)⁻¹) = fun x => fr A {p} x * sign (dot (A.v p) x) := by
    funext x
    exact fr_single_inv A p x
  rw [e]
  exact prodF_mul f _ _

lemma q_mul_qi (f : ℕ) (A : OBase α) (p : α) :
    prodF f (fr A {p}) * prodF f (fun x => (fr A {p} x)⁻¹) = 1 := by
  rw [mul_comm]
  exact prodF_inv_mul f A {p}

end Normal

end
end P4L
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.P4L.lin8_gateM
#print axioms OAI.PowerSaving.P4L.lin8_swapM
#print axioms OAI.PowerSaving.P4L.lin8_AinM
#print axioms OAI.PowerSaving.P4L.lin8_AoutM
#print axioms OAI.PowerSaving.P4L.prodF_incr
#print axioms OAI.PowerSaving.P4L.normal_qi
