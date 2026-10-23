import Submission.Work.P4L.Windows
import Submission.Work.G18.Lemmas
import Submission.Work.P16A8.View
-- changed for the tensor-power extension (30103/10000000); see Submission.lean

/-!
# P16A8 (p16a8), the retained idle windows (raw: ONE block of rank 8 m per owner)

Windows (pair, stages a..b of the full calls): [(1, 0, 1), (2, 0, 2), (3, 0, 3), (4, 0, 4), (5, 0, 5), (6, 0, 6), (7, 0, 7), (8, 0, 8), (8, 10, 17), (9, 11, 17), (10, 12, 17), (11, 13, 17), (12, 14, 17), (13, 15, 17), (14, 16, 17)].  Every owner climbs the whole window with ONE block of
rank `8 m` inside `BBC (base t) l g` (`BC.reach_of_pos`, `BC.reach_of_lt`); the window is one operator route
(`ORoute.steps_inv`) and moves the view of every port by `win x y m`, `m` the product of its stage transforms.
No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace OAI
namespace PowerSaving
namespace P16A8
open Binary Matrix Finset RAM SS CB RF BC GX GF

noncomputable section

section Win
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T] [Fintype Sl] [DecidableEq Sl]
  [Fintype C] [DecidableEq C] (base : T → OBase H) (l : H) (hH : Fintype.card H = 9)

/-- the two owner roles of a pair at every port. -/
def ownerSet (x y : R32) : Finset (PRole (Orth (LC (Fin 17) H l)) T Sl C) :=
  (Finset.univ : Finset (Orth (LC (Fin 17) H l) × T)).image (fun p => mainR p.1 x p.2) ∪
    (Finset.univ : Finset (Orth (LC (Fin 17) H l) × T)).image (fun p => mainR p.1 y p.2)

lemma mem_ownerSet (x y : R32) (g : Orth (LC (Fin 17) H l)) (i : R32) (t : T) :
    mainR (Sl := Sl) (C := C) g i t ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l x y ↔ (i = x ∨ i = y) := by
  unfold ownerSet
  rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
  constructor
  · rintro (⟨⟨g', t'⟩, -, h⟩ | ⟨⟨g', t'⟩, -, h⟩)
    · simp only [mainR, Sum.inl.injEq, Prod.mk.injEq] at h; exact Or.inl h.2.1.symm
    · simp only [mainR, Sum.inl.injEq, Prod.mk.injEq] at h; exact Or.inr h.2.1.symm
  · rintro (rfl | rfl)
    · exact Or.inl ⟨(g, t), Finset.mem_univ _, rfl⟩
    · exact Or.inr ⟨(g, t), Finset.mem_univ _, rfl⟩

lemma ownerSet_main (x y : R32) (r : PRole (Orth (LC (Fin 17) H l)) T Sl C)
    (hr : r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l x y) : ∃ g i t, r = mainR g i t := by
  unfold ownerSet at hr
  rw [Finset.mem_union, Finset.mem_image, Finset.mem_image] at hr
  rcases hr with (⟨⟨g, t⟩, -, rfl⟩ | ⟨⟨g, t⟩, -, rfl⟩)
  · exact ⟨g, x, t, rfl⟩
  · exact ⟨g, y, t, rfl⟩

/-- start / end frames of a window's owners. -/
def winF (x : R32) (a : ℕ) : PRole (Orth (LC (Fin 17) H l)) T Sl C → CMat (LC (Fin 17) H l)
  | .inl (.inl (g, (i, t))) =>
      if i = x then frame (BBC (base t) l g) (G18.setX l a) else frame (BBC (base t) l g) (G18.setY l a)
  | _ => 1

def winF' (x : R32) (a : ℕ) : PRole (Orth (LC (Fin 17) H l)) T Sl C → CMat (LC (Fin 17) H l)
  | .inl (.inl (g, (i, t))) =>
      if i = x then unframe (BBC (base t) l g) (G18.setX l a) else unframe (BBC (base t) l g) (G18.setY l a)
  | _ => 1

lemma winF_inv (x : R32) (a : ℕ) (r : PRole (Orth (LC (Fin 17) H l)) T Sl C) :
    winF (Sl := Sl) (C := C) base l x a r * winF' (Sl := Sl) (C := C) base l x a r = 1 := by
  rcases r with ((⟨g, i, t⟩ | h) | c)
  · simp only [winF, winF']; split_ifs <;> exact unframe_right _ _
  · simp [winF, winF']
  · simp [winF, winF']

include hH in
lemma win0X (t : T) (g : Orth (LC (Fin 17) H l)) :
    GReach (frame (BBC (base t) l g) (G18.setX l 0)) (frame (BBC (base t) l g) (G18.setX l 2))
      (fun φ => bcost φ 16) := by
  have h1 := G18.card_setX l hH 0 (by norm_num)
  have h2 := G18.card_setX l hH 2 (by norm_num)
  have h3 := G18.card_LC145 l hH
  exact GReach.ofX (reach_of_pos (by omega) (BBC (base t) l g) (G18.setX_mono l 0 2 (by norm_num) (by norm_num))
    16 (by omega) (by omega))

include hH in
lemma win0Y (t : T) (g : Orth (LC (Fin 17) H l)) :
    GReach (frame (BBC (base t) l g) (G18.setY l 0)) (frame (BBC (base t) l g) (G18.setY l 2))
      (fun φ => bcost φ 16) := by
  have h1 := G18.card_setY l hH 0 (by norm_num)
  have h2 := G18.card_setY l hH 2 (by norm_num)
  have h3 := G18.card_LC145 l hH
  exact GReach.ofX (reach_of_lt (by omega) (BBC (base t) l g) (G18.setY_mono l 0 2 (by norm_num) (by norm_num))
    16 (by omega) (by omega))

include hH in
/-- **window 0** (pair 1, stages 0..1) as an operator route (all gauges and ports). -/
theorem winSeg0 : P4L.ORoute (fun f y r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x1 .y1
      then matAct f (winF (Sl := Sl) (C := C) base l .x1 2 r * winF' (Sl := Sl) (C := C) base l .x1 0 r) (y r)
      else y r)
      (fun φ => ∑ r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x1 .y1, bcost φ 16) := by
  refine P4L.ORoute.steps_inv _ (winF base l .x1 0) (winF' base l .x1 0) (winF base l .x1 2)
    (fun r _ => winF_inv base l .x1 0 r) (fun _ φ => bcost φ 16) (fun r hr => ?_)
  obtain ⟨g, i, t, rfl⟩ := ownerSet_main l .x1 .y1 r hr
  rw [mem_ownerSet] at hr
  rcases hr with rfl | rfl
  · exact win0X base l hH t g _ (mainR g .x1 t)
  · exact win0Y base l hH t g _ (mainR g .y1 t)

/-- window 0 moves the view of every port by `win` with the product of its stage transforms. -/
theorem view_winSeg0 (f : ℕ) (y : Data (LC (Fin 17) H l) (PRole (Orth (LC (Fin 17) H l)) T Sl C) f)
    (g : Orth (LC (Fin 17) H l)) (t : T) :
    view f g t (fun r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x1 .y1
      then matAct f (winF (Sl := Sl) (C := C) base l .x1 2 r * winF' (Sl := Sl) (C := C) base l .x1 0 r) (y r)
      else y r)
      = win .x1 .y1 (P4L.prodF f (P4L.fr (BBC (base t) l g) ((Finset.range 2).biUnion fun j => G18.incr l (0 + j)))) (view f g t y) := by
  obtain ⟨eX, dX⟩ := G18.setX_add l 0 1 (by norm_num)
  obtain ⟨eY, dY⟩ := G18.setY_add l 0 1 (by norm_num)
  apply view_steps_win _ _ f y g t .x1 .y1 (by decide) _ (fun i => mem_ownerSet l .x1 .y1 g i t)
  rintro i (rfl | rfl) v
  · simp only [winF, winF', mainR, if_pos rfl]
    rw [← matAct_mul]
    have e : G18.setX l 2 = G18.setX l 0 ∪ ((Finset.range 2).biUnion fun j => G18.incr l (0 + j)) := eX
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dX v
  · simp only [winF, winF', mainR, if_neg (by decide : R32.y1 ≠ R32.x1)]
    rw [← matAct_mul]
    have e : G18.setY l 2 = G18.setY l 0 ∪ ((Finset.range 2).biUnion fun j => G18.incr l (0 + j)) := eY
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dY v

include hH in
lemma win1X (t : T) (g : Orth (LC (Fin 17) H l)) :
    GReach (frame (BBC (base t) l g) (G18.setX l 0)) (frame (BBC (base t) l g) (G18.setX l 3))
      (fun φ => bcost φ 24) := by
  have h1 := G18.card_setX l hH 0 (by norm_num)
  have h2 := G18.card_setX l hH 3 (by norm_num)
  have h3 := G18.card_LC145 l hH
  exact GReach.ofX (reach_of_pos (by omega) (BBC (base t) l g) (G18.setX_mono l 0 3 (by norm_num) (by norm_num))
    24 (by omega) (by omega))

include hH in
lemma win1Y (t : T) (g : Orth (LC (Fin 17) H l)) :
    GReach (frame (BBC (base t) l g) (G18.setY l 0)) (frame (BBC (base t) l g) (G18.setY l 3))
      (fun φ => bcost φ 24) := by
  have h1 := G18.card_setY l hH 0 (by norm_num)
  have h2 := G18.card_setY l hH 3 (by norm_num)
  have h3 := G18.card_LC145 l hH
  exact GReach.ofX (reach_of_lt (by omega) (BBC (base t) l g) (G18.setY_mono l 0 3 (by norm_num) (by norm_num))
    24 (by omega) (by omega))

include hH in
/-- **window 1** (pair 2, stages 0..2) as an operator route (all gauges and ports). -/
theorem winSeg1 : P4L.ORoute (fun f y r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x2 .y2
      then matAct f (winF (Sl := Sl) (C := C) base l .x2 3 r * winF' (Sl := Sl) (C := C) base l .x2 0 r) (y r)
      else y r)
      (fun φ => ∑ r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x2 .y2, bcost φ 24) := by
  refine P4L.ORoute.steps_inv _ (winF base l .x2 0) (winF' base l .x2 0) (winF base l .x2 3)
    (fun r _ => winF_inv base l .x2 0 r) (fun _ φ => bcost φ 24) (fun r hr => ?_)
  obtain ⟨g, i, t, rfl⟩ := ownerSet_main l .x2 .y2 r hr
  rw [mem_ownerSet] at hr
  rcases hr with rfl | rfl
  · exact win1X base l hH t g _ (mainR g .x2 t)
  · exact win1Y base l hH t g _ (mainR g .y2 t)

/-- window 1 moves the view of every port by `win` with the product of its stage transforms. -/
theorem view_winSeg1 (f : ℕ) (y : Data (LC (Fin 17) H l) (PRole (Orth (LC (Fin 17) H l)) T Sl C) f)
    (g : Orth (LC (Fin 17) H l)) (t : T) :
    view f g t (fun r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x2 .y2
      then matAct f (winF (Sl := Sl) (C := C) base l .x2 3 r * winF' (Sl := Sl) (C := C) base l .x2 0 r) (y r)
      else y r)
      = win .x2 .y2 (P4L.prodF f (P4L.fr (BBC (base t) l g) ((Finset.range 3).biUnion fun j => G18.incr l (0 + j)))) (view f g t y) := by
  obtain ⟨eX, dX⟩ := G18.setX_add l 0 2 (by norm_num)
  obtain ⟨eY, dY⟩ := G18.setY_add l 0 2 (by norm_num)
  apply view_steps_win _ _ f y g t .x2 .y2 (by decide) _ (fun i => mem_ownerSet l .x2 .y2 g i t)
  rintro i (rfl | rfl) v
  · simp only [winF, winF', mainR, if_pos rfl]
    rw [← matAct_mul]
    have e : G18.setX l 3 = G18.setX l 0 ∪ ((Finset.range 3).biUnion fun j => G18.incr l (0 + j)) := eX
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dX v
  · simp only [winF, winF', mainR, if_neg (by decide : R32.y2 ≠ R32.x2)]
    rw [← matAct_mul]
    have e : G18.setY l 3 = G18.setY l 0 ∪ ((Finset.range 3).biUnion fun j => G18.incr l (0 + j)) := eY
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dY v

include hH in
lemma win2X (t : T) (g : Orth (LC (Fin 17) H l)) :
    GReach (frame (BBC (base t) l g) (G18.setX l 0)) (frame (BBC (base t) l g) (G18.setX l 4))
      (fun φ => bcost φ 32) := by
  have h1 := G18.card_setX l hH 0 (by norm_num)
  have h2 := G18.card_setX l hH 4 (by norm_num)
  have h3 := G18.card_LC145 l hH
  exact GReach.ofX (reach_of_pos (by omega) (BBC (base t) l g) (G18.setX_mono l 0 4 (by norm_num) (by norm_num))
    32 (by omega) (by omega))

include hH in
lemma win2Y (t : T) (g : Orth (LC (Fin 17) H l)) :
    GReach (frame (BBC (base t) l g) (G18.setY l 0)) (frame (BBC (base t) l g) (G18.setY l 4))
      (fun φ => bcost φ 32) := by
  have h1 := G18.card_setY l hH 0 (by norm_num)
  have h2 := G18.card_setY l hH 4 (by norm_num)
  have h3 := G18.card_LC145 l hH
  exact GReach.ofX (reach_of_lt (by omega) (BBC (base t) l g) (G18.setY_mono l 0 4 (by norm_num) (by norm_num))
    32 (by omega) (by omega))

include hH in
/-- **window 2** (pair 3, stages 0..3) as an operator route (all gauges and ports). -/
theorem winSeg2 : P4L.ORoute (fun f y r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x3 .y3
      then matAct f (winF (Sl := Sl) (C := C) base l .x3 4 r * winF' (Sl := Sl) (C := C) base l .x3 0 r) (y r)
      else y r)
      (fun φ => ∑ r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x3 .y3, bcost φ 32) := by
  refine P4L.ORoute.steps_inv _ (winF base l .x3 0) (winF' base l .x3 0) (winF base l .x3 4)
    (fun r _ => winF_inv base l .x3 0 r) (fun _ φ => bcost φ 32) (fun r hr => ?_)
  obtain ⟨g, i, t, rfl⟩ := ownerSet_main l .x3 .y3 r hr
  rw [mem_ownerSet] at hr
  rcases hr with rfl | rfl
  · exact win2X base l hH t g _ (mainR g .x3 t)
  · exact win2Y base l hH t g _ (mainR g .y3 t)

/-- window 2 moves the view of every port by `win` with the product of its stage transforms. -/
theorem view_winSeg2 (f : ℕ) (y : Data (LC (Fin 17) H l) (PRole (Orth (LC (Fin 17) H l)) T Sl C) f)
    (g : Orth (LC (Fin 17) H l)) (t : T) :
    view f g t (fun r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x3 .y3
      then matAct f (winF (Sl := Sl) (C := C) base l .x3 4 r * winF' (Sl := Sl) (C := C) base l .x3 0 r) (y r)
      else y r)
      = win .x3 .y3 (P4L.prodF f (P4L.fr (BBC (base t) l g) ((Finset.range 4).biUnion fun j => G18.incr l (0 + j)))) (view f g t y) := by
  obtain ⟨eX, dX⟩ := G18.setX_add l 0 3 (by norm_num)
  obtain ⟨eY, dY⟩ := G18.setY_add l 0 3 (by norm_num)
  apply view_steps_win _ _ f y g t .x3 .y3 (by decide) _ (fun i => mem_ownerSet l .x3 .y3 g i t)
  rintro i (rfl | rfl) v
  · simp only [winF, winF', mainR, if_pos rfl]
    rw [← matAct_mul]
    have e : G18.setX l 4 = G18.setX l 0 ∪ ((Finset.range 4).biUnion fun j => G18.incr l (0 + j)) := eX
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dX v
  · simp only [winF, winF', mainR, if_neg (by decide : R32.y3 ≠ R32.x3)]
    rw [← matAct_mul]
    have e : G18.setY l 4 = G18.setY l 0 ∪ ((Finset.range 4).biUnion fun j => G18.incr l (0 + j)) := eY
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dY v

include hH in
lemma win3X (t : T) (g : Orth (LC (Fin 17) H l)) :
    GReach (frame (BBC (base t) l g) (G18.setX l 0)) (frame (BBC (base t) l g) (G18.setX l 5))
      (fun φ => bcost φ 40) := by
  have h1 := G18.card_setX l hH 0 (by norm_num)
  have h2 := G18.card_setX l hH 5 (by norm_num)
  have h3 := G18.card_LC145 l hH
  exact GReach.ofX (reach_of_pos (by omega) (BBC (base t) l g) (G18.setX_mono l 0 5 (by norm_num) (by norm_num))
    40 (by omega) (by omega))

include hH in
lemma win3Y (t : T) (g : Orth (LC (Fin 17) H l)) :
    GReach (frame (BBC (base t) l g) (G18.setY l 0)) (frame (BBC (base t) l g) (G18.setY l 5))
      (fun φ => bcost φ 40) := by
  have h1 := G18.card_setY l hH 0 (by norm_num)
  have h2 := G18.card_setY l hH 5 (by norm_num)
  have h3 := G18.card_LC145 l hH
  exact GReach.ofX (reach_of_lt (by omega) (BBC (base t) l g) (G18.setY_mono l 0 5 (by norm_num) (by norm_num))
    40 (by omega) (by omega))

include hH in
/-- **window 3** (pair 4, stages 0..4) as an operator route (all gauges and ports). -/
theorem winSeg3 : P4L.ORoute (fun f y r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x4 .y4
      then matAct f (winF (Sl := Sl) (C := C) base l .x4 5 r * winF' (Sl := Sl) (C := C) base l .x4 0 r) (y r)
      else y r)
      (fun φ => ∑ r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x4 .y4, bcost φ 40) := by
  refine P4L.ORoute.steps_inv _ (winF base l .x4 0) (winF' base l .x4 0) (winF base l .x4 5)
    (fun r _ => winF_inv base l .x4 0 r) (fun _ φ => bcost φ 40) (fun r hr => ?_)
  obtain ⟨g, i, t, rfl⟩ := ownerSet_main l .x4 .y4 r hr
  rw [mem_ownerSet] at hr
  rcases hr with rfl | rfl
  · exact win3X base l hH t g _ (mainR g .x4 t)
  · exact win3Y base l hH t g _ (mainR g .y4 t)

/-- window 3 moves the view of every port by `win` with the product of its stage transforms. -/
theorem view_winSeg3 (f : ℕ) (y : Data (LC (Fin 17) H l) (PRole (Orth (LC (Fin 17) H l)) T Sl C) f)
    (g : Orth (LC (Fin 17) H l)) (t : T) :
    view f g t (fun r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x4 .y4
      then matAct f (winF (Sl := Sl) (C := C) base l .x4 5 r * winF' (Sl := Sl) (C := C) base l .x4 0 r) (y r)
      else y r)
      = win .x4 .y4 (P4L.prodF f (P4L.fr (BBC (base t) l g) ((Finset.range 5).biUnion fun j => G18.incr l (0 + j)))) (view f g t y) := by
  obtain ⟨eX, dX⟩ := G18.setX_add l 0 4 (by norm_num)
  obtain ⟨eY, dY⟩ := G18.setY_add l 0 4 (by norm_num)
  apply view_steps_win _ _ f y g t .x4 .y4 (by decide) _ (fun i => mem_ownerSet l .x4 .y4 g i t)
  rintro i (rfl | rfl) v
  · simp only [winF, winF', mainR, if_pos rfl]
    rw [← matAct_mul]
    have e : G18.setX l 5 = G18.setX l 0 ∪ ((Finset.range 5).biUnion fun j => G18.incr l (0 + j)) := eX
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dX v
  · simp only [winF, winF', mainR, if_neg (by decide : R32.y4 ≠ R32.x4)]
    rw [← matAct_mul]
    have e : G18.setY l 5 = G18.setY l 0 ∪ ((Finset.range 5).biUnion fun j => G18.incr l (0 + j)) := eY
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dY v

include hH in
lemma win4X (t : T) (g : Orth (LC (Fin 17) H l)) :
    GReach (frame (BBC (base t) l g) (G18.setX l 0)) (frame (BBC (base t) l g) (G18.setX l 6))
      (fun φ => bcost φ 48) := by
  have h1 := G18.card_setX l hH 0 (by norm_num)
  have h2 := G18.card_setX l hH 6 (by norm_num)
  have h3 := G18.card_LC145 l hH
  exact GReach.ofX (reach_of_pos (by omega) (BBC (base t) l g) (G18.setX_mono l 0 6 (by norm_num) (by norm_num))
    48 (by omega) (by omega))

include hH in
lemma win4Y (t : T) (g : Orth (LC (Fin 17) H l)) :
    GReach (frame (BBC (base t) l g) (G18.setY l 0)) (frame (BBC (base t) l g) (G18.setY l 6))
      (fun φ => bcost φ 48) := by
  have h1 := G18.card_setY l hH 0 (by norm_num)
  have h2 := G18.card_setY l hH 6 (by norm_num)
  have h3 := G18.card_LC145 l hH
  exact GReach.ofX (reach_of_lt (by omega) (BBC (base t) l g) (G18.setY_mono l 0 6 (by norm_num) (by norm_num))
    48 (by omega) (by omega))

include hH in
/-- **window 4** (pair 5, stages 0..5) as an operator route (all gauges and ports). -/
theorem winSeg4 : P4L.ORoute (fun f y r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x5 .y5
      then matAct f (winF (Sl := Sl) (C := C) base l .x5 6 r * winF' (Sl := Sl) (C := C) base l .x5 0 r) (y r)
      else y r)
      (fun φ => ∑ r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x5 .y5, bcost φ 48) := by
  refine P4L.ORoute.steps_inv _ (winF base l .x5 0) (winF' base l .x5 0) (winF base l .x5 6)
    (fun r _ => winF_inv base l .x5 0 r) (fun _ φ => bcost φ 48) (fun r hr => ?_)
  obtain ⟨g, i, t, rfl⟩ := ownerSet_main l .x5 .y5 r hr
  rw [mem_ownerSet] at hr
  rcases hr with rfl | rfl
  · exact win4X base l hH t g _ (mainR g .x5 t)
  · exact win4Y base l hH t g _ (mainR g .y5 t)

/-- window 4 moves the view of every port by `win` with the product of its stage transforms. -/
theorem view_winSeg4 (f : ℕ) (y : Data (LC (Fin 17) H l) (PRole (Orth (LC (Fin 17) H l)) T Sl C) f)
    (g : Orth (LC (Fin 17) H l)) (t : T) :
    view f g t (fun r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x5 .y5
      then matAct f (winF (Sl := Sl) (C := C) base l .x5 6 r * winF' (Sl := Sl) (C := C) base l .x5 0 r) (y r)
      else y r)
      = win .x5 .y5 (P4L.prodF f (P4L.fr (BBC (base t) l g) ((Finset.range 6).biUnion fun j => G18.incr l (0 + j)))) (view f g t y) := by
  obtain ⟨eX, dX⟩ := G18.setX_add l 0 5 (by norm_num)
  obtain ⟨eY, dY⟩ := G18.setY_add l 0 5 (by norm_num)
  apply view_steps_win _ _ f y g t .x5 .y5 (by decide) _ (fun i => mem_ownerSet l .x5 .y5 g i t)
  rintro i (rfl | rfl) v
  · simp only [winF, winF', mainR, if_pos rfl]
    rw [← matAct_mul]
    have e : G18.setX l 6 = G18.setX l 0 ∪ ((Finset.range 6).biUnion fun j => G18.incr l (0 + j)) := eX
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dX v
  · simp only [winF, winF', mainR, if_neg (by decide : R32.y5 ≠ R32.x5)]
    rw [← matAct_mul]
    have e : G18.setY l 6 = G18.setY l 0 ∪ ((Finset.range 6).biUnion fun j => G18.incr l (0 + j)) := eY
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dY v

include hH in
lemma win5X (t : T) (g : Orth (LC (Fin 17) H l)) :
    GReach (frame (BBC (base t) l g) (G18.setX l 0)) (frame (BBC (base t) l g) (G18.setX l 7))
      (fun φ => bcost φ 56) := by
  have h1 := G18.card_setX l hH 0 (by norm_num)
  have h2 := G18.card_setX l hH 7 (by norm_num)
  have h3 := G18.card_LC145 l hH
  exact GReach.ofX (reach_of_pos (by omega) (BBC (base t) l g) (G18.setX_mono l 0 7 (by norm_num) (by norm_num))
    56 (by omega) (by omega))

include hH in
lemma win5Y (t : T) (g : Orth (LC (Fin 17) H l)) :
    GReach (frame (BBC (base t) l g) (G18.setY l 0)) (frame (BBC (base t) l g) (G18.setY l 7))
      (fun φ => bcost φ 56) := by
  have h1 := G18.card_setY l hH 0 (by norm_num)
  have h2 := G18.card_setY l hH 7 (by norm_num)
  have h3 := G18.card_LC145 l hH
  exact GReach.ofX (reach_of_lt (by omega) (BBC (base t) l g) (G18.setY_mono l 0 7 (by norm_num) (by norm_num))
    56 (by omega) (by omega))

include hH in
/-- **window 5** (pair 6, stages 0..6) as an operator route (all gauges and ports). -/
theorem winSeg5 : P4L.ORoute (fun f y r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x6 .y6
      then matAct f (winF (Sl := Sl) (C := C) base l .x6 7 r * winF' (Sl := Sl) (C := C) base l .x6 0 r) (y r)
      else y r)
      (fun φ => ∑ r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x6 .y6, bcost φ 56) := by
  refine P4L.ORoute.steps_inv _ (winF base l .x6 0) (winF' base l .x6 0) (winF base l .x6 7)
    (fun r _ => winF_inv base l .x6 0 r) (fun _ φ => bcost φ 56) (fun r hr => ?_)
  obtain ⟨g, i, t, rfl⟩ := ownerSet_main l .x6 .y6 r hr
  rw [mem_ownerSet] at hr
  rcases hr with rfl | rfl
  · exact win5X base l hH t g _ (mainR g .x6 t)
  · exact win5Y base l hH t g _ (mainR g .y6 t)

/-- window 5 moves the view of every port by `win` with the product of its stage transforms. -/
theorem view_winSeg5 (f : ℕ) (y : Data (LC (Fin 17) H l) (PRole (Orth (LC (Fin 17) H l)) T Sl C) f)
    (g : Orth (LC (Fin 17) H l)) (t : T) :
    view f g t (fun r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x6 .y6
      then matAct f (winF (Sl := Sl) (C := C) base l .x6 7 r * winF' (Sl := Sl) (C := C) base l .x6 0 r) (y r)
      else y r)
      = win .x6 .y6 (P4L.prodF f (P4L.fr (BBC (base t) l g) ((Finset.range 7).biUnion fun j => G18.incr l (0 + j)))) (view f g t y) := by
  obtain ⟨eX, dX⟩ := G18.setX_add l 0 6 (by norm_num)
  obtain ⟨eY, dY⟩ := G18.setY_add l 0 6 (by norm_num)
  apply view_steps_win _ _ f y g t .x6 .y6 (by decide) _ (fun i => mem_ownerSet l .x6 .y6 g i t)
  rintro i (rfl | rfl) v
  · simp only [winF, winF', mainR, if_pos rfl]
    rw [← matAct_mul]
    have e : G18.setX l 7 = G18.setX l 0 ∪ ((Finset.range 7).biUnion fun j => G18.incr l (0 + j)) := eX
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dX v
  · simp only [winF, winF', mainR, if_neg (by decide : R32.y6 ≠ R32.x6)]
    rw [← matAct_mul]
    have e : G18.setY l 7 = G18.setY l 0 ∪ ((Finset.range 7).biUnion fun j => G18.incr l (0 + j)) := eY
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dY v

include hH in
lemma win6X (t : T) (g : Orth (LC (Fin 17) H l)) :
    GReach (frame (BBC (base t) l g) (G18.setX l 0)) (frame (BBC (base t) l g) (G18.setX l 8))
      (fun φ => bcost φ 64) := by
  have h1 := G18.card_setX l hH 0 (by norm_num)
  have h2 := G18.card_setX l hH 8 (by norm_num)
  have h3 := G18.card_LC145 l hH
  exact GReach.ofX (reach_of_pos (by omega) (BBC (base t) l g) (G18.setX_mono l 0 8 (by norm_num) (by norm_num))
    64 (by omega) (by omega))

include hH in
lemma win6Y (t : T) (g : Orth (LC (Fin 17) H l)) :
    GReach (frame (BBC (base t) l g) (G18.setY l 0)) (frame (BBC (base t) l g) (G18.setY l 8))
      (fun φ => bcost φ 64) := by
  have h1 := G18.card_setY l hH 0 (by norm_num)
  have h2 := G18.card_setY l hH 8 (by norm_num)
  have h3 := G18.card_LC145 l hH
  exact GReach.ofX (reach_of_lt (by omega) (BBC (base t) l g) (G18.setY_mono l 0 8 (by norm_num) (by norm_num))
    64 (by omega) (by omega))

include hH in
/-- **window 6** (pair 7, stages 0..7) as an operator route (all gauges and ports). -/
theorem winSeg6 : P4L.ORoute (fun f y r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x7 .y7
      then matAct f (winF (Sl := Sl) (C := C) base l .x7 8 r * winF' (Sl := Sl) (C := C) base l .x7 0 r) (y r)
      else y r)
      (fun φ => ∑ r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x7 .y7, bcost φ 64) := by
  refine P4L.ORoute.steps_inv _ (winF base l .x7 0) (winF' base l .x7 0) (winF base l .x7 8)
    (fun r _ => winF_inv base l .x7 0 r) (fun _ φ => bcost φ 64) (fun r hr => ?_)
  obtain ⟨g, i, t, rfl⟩ := ownerSet_main l .x7 .y7 r hr
  rw [mem_ownerSet] at hr
  rcases hr with rfl | rfl
  · exact win6X base l hH t g _ (mainR g .x7 t)
  · exact win6Y base l hH t g _ (mainR g .y7 t)

/-- window 6 moves the view of every port by `win` with the product of its stage transforms. -/
theorem view_winSeg6 (f : ℕ) (y : Data (LC (Fin 17) H l) (PRole (Orth (LC (Fin 17) H l)) T Sl C) f)
    (g : Orth (LC (Fin 17) H l)) (t : T) :
    view f g t (fun r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x7 .y7
      then matAct f (winF (Sl := Sl) (C := C) base l .x7 8 r * winF' (Sl := Sl) (C := C) base l .x7 0 r) (y r)
      else y r)
      = win .x7 .y7 (P4L.prodF f (P4L.fr (BBC (base t) l g) ((Finset.range 8).biUnion fun j => G18.incr l (0 + j)))) (view f g t y) := by
  obtain ⟨eX, dX⟩ := G18.setX_add l 0 7 (by norm_num)
  obtain ⟨eY, dY⟩ := G18.setY_add l 0 7 (by norm_num)
  apply view_steps_win _ _ f y g t .x7 .y7 (by decide) _ (fun i => mem_ownerSet l .x7 .y7 g i t)
  rintro i (rfl | rfl) v
  · simp only [winF, winF', mainR, if_pos rfl]
    rw [← matAct_mul]
    have e : G18.setX l 8 = G18.setX l 0 ∪ ((Finset.range 8).biUnion fun j => G18.incr l (0 + j)) := eX
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dX v
  · simp only [winF, winF', mainR, if_neg (by decide : R32.y7 ≠ R32.x7)]
    rw [← matAct_mul]
    have e : G18.setY l 8 = G18.setY l 0 ∪ ((Finset.range 8).biUnion fun j => G18.incr l (0 + j)) := eY
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dY v

include hH in
lemma win7X (t : T) (g : Orth (LC (Fin 17) H l)) :
    GReach (frame (BBC (base t) l g) (G18.setX l 0)) (frame (BBC (base t) l g) (G18.setX l 9))
      (fun φ => bcost φ 72) := by
  have h1 := G18.card_setX l hH 0 (by norm_num)
  have h2 := G18.card_setX l hH 9 (by norm_num)
  have h3 := G18.card_LC145 l hH
  exact GReach.ofX (reach_of_pos (by omega) (BBC (base t) l g) (G18.setX_mono l 0 9 (by norm_num) (by norm_num))
    72 (by omega) (by omega))

include hH in
lemma win7Y (t : T) (g : Orth (LC (Fin 17) H l)) :
    GReach (frame (BBC (base t) l g) (G18.setY l 0)) (frame (BBC (base t) l g) (G18.setY l 9))
      (fun φ => bcost φ 72) := by
  have h1 := G18.card_setY l hH 0 (by norm_num)
  have h2 := G18.card_setY l hH 9 (by norm_num)
  have h3 := G18.card_LC145 l hH
  exact GReach.ofX (reach_of_lt (by omega) (BBC (base t) l g) (G18.setY_mono l 0 9 (by norm_num) (by norm_num))
    72 (by omega) (by omega))

include hH in
/-- **window 7** (pair 8, stages 0..8) as an operator route (all gauges and ports). -/
theorem winSeg7 : P4L.ORoute (fun f y r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x8 .y8
      then matAct f (winF (Sl := Sl) (C := C) base l .x8 9 r * winF' (Sl := Sl) (C := C) base l .x8 0 r) (y r)
      else y r)
      (fun φ => ∑ r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x8 .y8, bcost φ 72) := by
  refine P4L.ORoute.steps_inv _ (winF base l .x8 0) (winF' base l .x8 0) (winF base l .x8 9)
    (fun r _ => winF_inv base l .x8 0 r) (fun _ φ => bcost φ 72) (fun r hr => ?_)
  obtain ⟨g, i, t, rfl⟩ := ownerSet_main l .x8 .y8 r hr
  rw [mem_ownerSet] at hr
  rcases hr with rfl | rfl
  · exact win7X base l hH t g _ (mainR g .x8 t)
  · exact win7Y base l hH t g _ (mainR g .y8 t)

/-- window 7 moves the view of every port by `win` with the product of its stage transforms. -/
theorem view_winSeg7 (f : ℕ) (y : Data (LC (Fin 17) H l) (PRole (Orth (LC (Fin 17) H l)) T Sl C) f)
    (g : Orth (LC (Fin 17) H l)) (t : T) :
    view f g t (fun r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x8 .y8
      then matAct f (winF (Sl := Sl) (C := C) base l .x8 9 r * winF' (Sl := Sl) (C := C) base l .x8 0 r) (y r)
      else y r)
      = win .x8 .y8 (P4L.prodF f (P4L.fr (BBC (base t) l g) ((Finset.range 9).biUnion fun j => G18.incr l (0 + j)))) (view f g t y) := by
  obtain ⟨eX, dX⟩ := G18.setX_add l 0 8 (by norm_num)
  obtain ⟨eY, dY⟩ := G18.setY_add l 0 8 (by norm_num)
  apply view_steps_win _ _ f y g t .x8 .y8 (by decide) _ (fun i => mem_ownerSet l .x8 .y8 g i t)
  rintro i (rfl | rfl) v
  · simp only [winF, winF', mainR, if_pos rfl]
    rw [← matAct_mul]
    have e : G18.setX l 9 = G18.setX l 0 ∪ ((Finset.range 9).biUnion fun j => G18.incr l (0 + j)) := eX
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dX v
  · simp only [winF, winF', mainR, if_neg (by decide : R32.y8 ≠ R32.x8)]
    rw [← matAct_mul]
    have e : G18.setY l 9 = G18.setY l 0 ∪ ((Finset.range 9).biUnion fun j => G18.incr l (0 + j)) := eY
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dY v

include hH in
lemma win8X (t : T) (g : Orth (LC (Fin 17) H l)) :
    GReach (frame (BBC (base t) l g) (G18.setX l 10)) (frame (BBC (base t) l g) (G18.setX l 18))
      (fun φ => bcost φ 64) := by
  have h1 := G18.card_setX l hH 10 (by norm_num)
  have h2 := G18.card_setX l hH 18 (by norm_num)
  have h3 := G18.card_LC145 l hH
  exact GReach.ofX (reach_of_pos (by omega) (BBC (base t) l g) (G18.setX_mono l 10 18 (by norm_num) (by norm_num))
    64 (by omega) (by omega))

include hH in
lemma win8Y (t : T) (g : Orth (LC (Fin 17) H l)) :
    GReach (frame (BBC (base t) l g) (G18.setY l 10)) (frame (BBC (base t) l g) (G18.setY l 18))
      (fun φ => bcost φ 64) := by
  have h1 := G18.card_setY l hH 10 (by norm_num)
  have h2 := G18.card_setY l hH 18 (by norm_num)
  have h3 := G18.card_LC145 l hH
  exact GReach.ofX (reach_of_lt (by omega) (BBC (base t) l g) (G18.setY_mono l 10 18 (by norm_num) (by norm_num))
    64 (by omega) (by omega))

include hH in
/-- **window 8** (pair 8, stages 10..17) as an operator route (all gauges and ports). -/
theorem winSeg8 : P4L.ORoute (fun f y r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x8 .y8
      then matAct f (winF (Sl := Sl) (C := C) base l .x8 18 r * winF' (Sl := Sl) (C := C) base l .x8 10 r) (y r)
      else y r)
      (fun φ => ∑ r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x8 .y8, bcost φ 64) := by
  refine P4L.ORoute.steps_inv _ (winF base l .x8 10) (winF' base l .x8 10) (winF base l .x8 18)
    (fun r _ => winF_inv base l .x8 10 r) (fun _ φ => bcost φ 64) (fun r hr => ?_)
  obtain ⟨g, i, t, rfl⟩ := ownerSet_main l .x8 .y8 r hr
  rw [mem_ownerSet] at hr
  rcases hr with rfl | rfl
  · exact win8X base l hH t g _ (mainR g .x8 t)
  · exact win8Y base l hH t g _ (mainR g .y8 t)

/-- window 8 moves the view of every port by `win` with the product of its stage transforms. -/
theorem view_winSeg8 (f : ℕ) (y : Data (LC (Fin 17) H l) (PRole (Orth (LC (Fin 17) H l)) T Sl C) f)
    (g : Orth (LC (Fin 17) H l)) (t : T) :
    view f g t (fun r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x8 .y8
      then matAct f (winF (Sl := Sl) (C := C) base l .x8 18 r * winF' (Sl := Sl) (C := C) base l .x8 10 r) (y r)
      else y r)
      = win .x8 .y8 (P4L.prodF f (P4L.fr (BBC (base t) l g) ((Finset.range 8).biUnion fun j => G18.incr l (10 + j)))) (view f g t y) := by
  obtain ⟨eX, dX⟩ := G18.setX_add l 10 7 (by norm_num)
  obtain ⟨eY, dY⟩ := G18.setY_add l 10 7 (by norm_num)
  apply view_steps_win _ _ f y g t .x8 .y8 (by decide) _ (fun i => mem_ownerSet l .x8 .y8 g i t)
  rintro i (rfl | rfl) v
  · simp only [winF, winF', mainR, if_pos rfl]
    rw [← matAct_mul]
    have e : G18.setX l 18 = G18.setX l 10 ∪ ((Finset.range 8).biUnion fun j => G18.incr l (10 + j)) := eX
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dX v
  · simp only [winF, winF', mainR, if_neg (by decide : R32.y8 ≠ R32.x8)]
    rw [← matAct_mul]
    have e : G18.setY l 18 = G18.setY l 10 ∪ ((Finset.range 8).biUnion fun j => G18.incr l (10 + j)) := eY
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dY v

include hH in
lemma win9X (t : T) (g : Orth (LC (Fin 17) H l)) :
    GReach (frame (BBC (base t) l g) (G18.setX l 11)) (frame (BBC (base t) l g) (G18.setX l 18))
      (fun φ => bcost φ 56) := by
  have h1 := G18.card_setX l hH 11 (by norm_num)
  have h2 := G18.card_setX l hH 18 (by norm_num)
  have h3 := G18.card_LC145 l hH
  exact GReach.ofX (reach_of_pos (by omega) (BBC (base t) l g) (G18.setX_mono l 11 18 (by norm_num) (by norm_num))
    56 (by omega) (by omega))

include hH in
lemma win9Y (t : T) (g : Orth (LC (Fin 17) H l)) :
    GReach (frame (BBC (base t) l g) (G18.setY l 11)) (frame (BBC (base t) l g) (G18.setY l 18))
      (fun φ => bcost φ 56) := by
  have h1 := G18.card_setY l hH 11 (by norm_num)
  have h2 := G18.card_setY l hH 18 (by norm_num)
  have h3 := G18.card_LC145 l hH
  exact GReach.ofX (reach_of_lt (by omega) (BBC (base t) l g) (G18.setY_mono l 11 18 (by norm_num) (by norm_num))
    56 (by omega) (by omega))

include hH in
/-- **window 9** (pair 9, stages 11..17) as an operator route (all gauges and ports). -/
theorem winSeg9 : P4L.ORoute (fun f y r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x9 .y9
      then matAct f (winF (Sl := Sl) (C := C) base l .x9 18 r * winF' (Sl := Sl) (C := C) base l .x9 11 r) (y r)
      else y r)
      (fun φ => ∑ r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x9 .y9, bcost φ 56) := by
  refine P4L.ORoute.steps_inv _ (winF base l .x9 11) (winF' base l .x9 11) (winF base l .x9 18)
    (fun r _ => winF_inv base l .x9 11 r) (fun _ φ => bcost φ 56) (fun r hr => ?_)
  obtain ⟨g, i, t, rfl⟩ := ownerSet_main l .x9 .y9 r hr
  rw [mem_ownerSet] at hr
  rcases hr with rfl | rfl
  · exact win9X base l hH t g _ (mainR g .x9 t)
  · exact win9Y base l hH t g _ (mainR g .y9 t)

/-- window 9 moves the view of every port by `win` with the product of its stage transforms. -/
theorem view_winSeg9 (f : ℕ) (y : Data (LC (Fin 17) H l) (PRole (Orth (LC (Fin 17) H l)) T Sl C) f)
    (g : Orth (LC (Fin 17) H l)) (t : T) :
    view f g t (fun r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x9 .y9
      then matAct f (winF (Sl := Sl) (C := C) base l .x9 18 r * winF' (Sl := Sl) (C := C) base l .x9 11 r) (y r)
      else y r)
      = win .x9 .y9 (P4L.prodF f (P4L.fr (BBC (base t) l g) ((Finset.range 7).biUnion fun j => G18.incr l (11 + j)))) (view f g t y) := by
  obtain ⟨eX, dX⟩ := G18.setX_add l 11 6 (by norm_num)
  obtain ⟨eY, dY⟩ := G18.setY_add l 11 6 (by norm_num)
  apply view_steps_win _ _ f y g t .x9 .y9 (by decide) _ (fun i => mem_ownerSet l .x9 .y9 g i t)
  rintro i (rfl | rfl) v
  · simp only [winF, winF', mainR, if_pos rfl]
    rw [← matAct_mul]
    have e : G18.setX l 18 = G18.setX l 11 ∪ ((Finset.range 7).biUnion fun j => G18.incr l (11 + j)) := eX
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dX v
  · simp only [winF, winF', mainR, if_neg (by decide : R32.y9 ≠ R32.x9)]
    rw [← matAct_mul]
    have e : G18.setY l 18 = G18.setY l 11 ∪ ((Finset.range 7).biUnion fun j => G18.incr l (11 + j)) := eY
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dY v

include hH in
lemma win10X (t : T) (g : Orth (LC (Fin 17) H l)) :
    GReach (frame (BBC (base t) l g) (G18.setX l 12)) (frame (BBC (base t) l g) (G18.setX l 18))
      (fun φ => bcost φ 48) := by
  have h1 := G18.card_setX l hH 12 (by norm_num)
  have h2 := G18.card_setX l hH 18 (by norm_num)
  have h3 := G18.card_LC145 l hH
  exact GReach.ofX (reach_of_pos (by omega) (BBC (base t) l g) (G18.setX_mono l 12 18 (by norm_num) (by norm_num))
    48 (by omega) (by omega))

include hH in
lemma win10Y (t : T) (g : Orth (LC (Fin 17) H l)) :
    GReach (frame (BBC (base t) l g) (G18.setY l 12)) (frame (BBC (base t) l g) (G18.setY l 18))
      (fun φ => bcost φ 48) := by
  have h1 := G18.card_setY l hH 12 (by norm_num)
  have h2 := G18.card_setY l hH 18 (by norm_num)
  have h3 := G18.card_LC145 l hH
  exact GReach.ofX (reach_of_lt (by omega) (BBC (base t) l g) (G18.setY_mono l 12 18 (by norm_num) (by norm_num))
    48 (by omega) (by omega))

include hH in
/-- **window 10** (pair 10, stages 12..17) as an operator route (all gauges and ports). -/
theorem winSeg10 : P4L.ORoute (fun f y r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x10 .y10
      then matAct f (winF (Sl := Sl) (C := C) base l .x10 18 r * winF' (Sl := Sl) (C := C) base l .x10 12 r) (y r)
      else y r)
      (fun φ => ∑ r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x10 .y10, bcost φ 48) := by
  refine P4L.ORoute.steps_inv _ (winF base l .x10 12) (winF' base l .x10 12) (winF base l .x10 18)
    (fun r _ => winF_inv base l .x10 12 r) (fun _ φ => bcost φ 48) (fun r hr => ?_)
  obtain ⟨g, i, t, rfl⟩ := ownerSet_main l .x10 .y10 r hr
  rw [mem_ownerSet] at hr
  rcases hr with rfl | rfl
  · exact win10X base l hH t g _ (mainR g .x10 t)
  · exact win10Y base l hH t g _ (mainR g .y10 t)

/-- window 10 moves the view of every port by `win` with the product of its stage transforms. -/
theorem view_winSeg10 (f : ℕ) (y : Data (LC (Fin 17) H l) (PRole (Orth (LC (Fin 17) H l)) T Sl C) f)
    (g : Orth (LC (Fin 17) H l)) (t : T) :
    view f g t (fun r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x10 .y10
      then matAct f (winF (Sl := Sl) (C := C) base l .x10 18 r * winF' (Sl := Sl) (C := C) base l .x10 12 r) (y r)
      else y r)
      = win .x10 .y10 (P4L.prodF f (P4L.fr (BBC (base t) l g) ((Finset.range 6).biUnion fun j => G18.incr l (12 + j)))) (view f g t y) := by
  obtain ⟨eX, dX⟩ := G18.setX_add l 12 5 (by norm_num)
  obtain ⟨eY, dY⟩ := G18.setY_add l 12 5 (by norm_num)
  apply view_steps_win _ _ f y g t .x10 .y10 (by decide) _ (fun i => mem_ownerSet l .x10 .y10 g i t)
  rintro i (rfl | rfl) v
  · simp only [winF, winF', mainR, if_pos rfl]
    rw [← matAct_mul]
    have e : G18.setX l 18 = G18.setX l 12 ∪ ((Finset.range 6).biUnion fun j => G18.incr l (12 + j)) := eX
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dX v
  · simp only [winF, winF', mainR, if_neg (by decide : R32.y10 ≠ R32.x10)]
    rw [← matAct_mul]
    have e : G18.setY l 18 = G18.setY l 12 ∪ ((Finset.range 6).biUnion fun j => G18.incr l (12 + j)) := eY
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dY v

include hH in
lemma win11X (t : T) (g : Orth (LC (Fin 17) H l)) :
    GReach (frame (BBC (base t) l g) (G18.setX l 13)) (frame (BBC (base t) l g) (G18.setX l 18))
      (fun φ => bcost φ 40) := by
  have h1 := G18.card_setX l hH 13 (by norm_num)
  have h2 := G18.card_setX l hH 18 (by norm_num)
  have h3 := G18.card_LC145 l hH
  exact GReach.ofX (reach_of_pos (by omega) (BBC (base t) l g) (G18.setX_mono l 13 18 (by norm_num) (by norm_num))
    40 (by omega) (by omega))

include hH in
lemma win11Y (t : T) (g : Orth (LC (Fin 17) H l)) :
    GReach (frame (BBC (base t) l g) (G18.setY l 13)) (frame (BBC (base t) l g) (G18.setY l 18))
      (fun φ => bcost φ 40) := by
  have h1 := G18.card_setY l hH 13 (by norm_num)
  have h2 := G18.card_setY l hH 18 (by norm_num)
  have h3 := G18.card_LC145 l hH
  exact GReach.ofX (reach_of_lt (by omega) (BBC (base t) l g) (G18.setY_mono l 13 18 (by norm_num) (by norm_num))
    40 (by omega) (by omega))

include hH in
/-- **window 11** (pair 11, stages 13..17) as an operator route (all gauges and ports). -/
theorem winSeg11 : P4L.ORoute (fun f y r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x11 .y11
      then matAct f (winF (Sl := Sl) (C := C) base l .x11 18 r * winF' (Sl := Sl) (C := C) base l .x11 13 r) (y r)
      else y r)
      (fun φ => ∑ r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x11 .y11, bcost φ 40) := by
  refine P4L.ORoute.steps_inv _ (winF base l .x11 13) (winF' base l .x11 13) (winF base l .x11 18)
    (fun r _ => winF_inv base l .x11 13 r) (fun _ φ => bcost φ 40) (fun r hr => ?_)
  obtain ⟨g, i, t, rfl⟩ := ownerSet_main l .x11 .y11 r hr
  rw [mem_ownerSet] at hr
  rcases hr with rfl | rfl
  · exact win11X base l hH t g _ (mainR g .x11 t)
  · exact win11Y base l hH t g _ (mainR g .y11 t)

/-- window 11 moves the view of every port by `win` with the product of its stage transforms. -/
theorem view_winSeg11 (f : ℕ) (y : Data (LC (Fin 17) H l) (PRole (Orth (LC (Fin 17) H l)) T Sl C) f)
    (g : Orth (LC (Fin 17) H l)) (t : T) :
    view f g t (fun r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x11 .y11
      then matAct f (winF (Sl := Sl) (C := C) base l .x11 18 r * winF' (Sl := Sl) (C := C) base l .x11 13 r) (y r)
      else y r)
      = win .x11 .y11 (P4L.prodF f (P4L.fr (BBC (base t) l g) ((Finset.range 5).biUnion fun j => G18.incr l (13 + j)))) (view f g t y) := by
  obtain ⟨eX, dX⟩ := G18.setX_add l 13 4 (by norm_num)
  obtain ⟨eY, dY⟩ := G18.setY_add l 13 4 (by norm_num)
  apply view_steps_win _ _ f y g t .x11 .y11 (by decide) _ (fun i => mem_ownerSet l .x11 .y11 g i t)
  rintro i (rfl | rfl) v
  · simp only [winF, winF', mainR, if_pos rfl]
    rw [← matAct_mul]
    have e : G18.setX l 18 = G18.setX l 13 ∪ ((Finset.range 5).biUnion fun j => G18.incr l (13 + j)) := eX
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dX v
  · simp only [winF, winF', mainR, if_neg (by decide : R32.y11 ≠ R32.x11)]
    rw [← matAct_mul]
    have e : G18.setY l 18 = G18.setY l 13 ∪ ((Finset.range 5).biUnion fun j => G18.incr l (13 + j)) := eY
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dY v

include hH in
lemma win12X (t : T) (g : Orth (LC (Fin 17) H l)) :
    GReach (frame (BBC (base t) l g) (G18.setX l 14)) (frame (BBC (base t) l g) (G18.setX l 18))
      (fun φ => bcost φ 32) := by
  have h1 := G18.card_setX l hH 14 (by norm_num)
  have h2 := G18.card_setX l hH 18 (by norm_num)
  have h3 := G18.card_LC145 l hH
  exact GReach.ofX (reach_of_pos (by omega) (BBC (base t) l g) (G18.setX_mono l 14 18 (by norm_num) (by norm_num))
    32 (by omega) (by omega))

include hH in
lemma win12Y (t : T) (g : Orth (LC (Fin 17) H l)) :
    GReach (frame (BBC (base t) l g) (G18.setY l 14)) (frame (BBC (base t) l g) (G18.setY l 18))
      (fun φ => bcost φ 32) := by
  have h1 := G18.card_setY l hH 14 (by norm_num)
  have h2 := G18.card_setY l hH 18 (by norm_num)
  have h3 := G18.card_LC145 l hH
  exact GReach.ofX (reach_of_lt (by omega) (BBC (base t) l g) (G18.setY_mono l 14 18 (by norm_num) (by norm_num))
    32 (by omega) (by omega))

include hH in
/-- **window 12** (pair 12, stages 14..17) as an operator route (all gauges and ports). -/
theorem winSeg12 : P4L.ORoute (fun f y r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x12 .y12
      then matAct f (winF (Sl := Sl) (C := C) base l .x12 18 r * winF' (Sl := Sl) (C := C) base l .x12 14 r) (y r)
      else y r)
      (fun φ => ∑ r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x12 .y12, bcost φ 32) := by
  refine P4L.ORoute.steps_inv _ (winF base l .x12 14) (winF' base l .x12 14) (winF base l .x12 18)
    (fun r _ => winF_inv base l .x12 14 r) (fun _ φ => bcost φ 32) (fun r hr => ?_)
  obtain ⟨g, i, t, rfl⟩ := ownerSet_main l .x12 .y12 r hr
  rw [mem_ownerSet] at hr
  rcases hr with rfl | rfl
  · exact win12X base l hH t g _ (mainR g .x12 t)
  · exact win12Y base l hH t g _ (mainR g .y12 t)

/-- window 12 moves the view of every port by `win` with the product of its stage transforms. -/
theorem view_winSeg12 (f : ℕ) (y : Data (LC (Fin 17) H l) (PRole (Orth (LC (Fin 17) H l)) T Sl C) f)
    (g : Orth (LC (Fin 17) H l)) (t : T) :
    view f g t (fun r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x12 .y12
      then matAct f (winF (Sl := Sl) (C := C) base l .x12 18 r * winF' (Sl := Sl) (C := C) base l .x12 14 r) (y r)
      else y r)
      = win .x12 .y12 (P4L.prodF f (P4L.fr (BBC (base t) l g) ((Finset.range 4).biUnion fun j => G18.incr l (14 + j)))) (view f g t y) := by
  obtain ⟨eX, dX⟩ := G18.setX_add l 14 3 (by norm_num)
  obtain ⟨eY, dY⟩ := G18.setY_add l 14 3 (by norm_num)
  apply view_steps_win _ _ f y g t .x12 .y12 (by decide) _ (fun i => mem_ownerSet l .x12 .y12 g i t)
  rintro i (rfl | rfl) v
  · simp only [winF, winF', mainR, if_pos rfl]
    rw [← matAct_mul]
    have e : G18.setX l 18 = G18.setX l 14 ∪ ((Finset.range 4).biUnion fun j => G18.incr l (14 + j)) := eX
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dX v
  · simp only [winF, winF', mainR, if_neg (by decide : R32.y12 ≠ R32.x12)]
    rw [← matAct_mul]
    have e : G18.setY l 18 = G18.setY l 14 ∪ ((Finset.range 4).biUnion fun j => G18.incr l (14 + j)) := eY
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dY v

include hH in
lemma win13X (t : T) (g : Orth (LC (Fin 17) H l)) :
    GReach (frame (BBC (base t) l g) (G18.setX l 15)) (frame (BBC (base t) l g) (G18.setX l 18))
      (fun φ => bcost φ 24) := by
  have h1 := G18.card_setX l hH 15 (by norm_num)
  have h2 := G18.card_setX l hH 18 (by norm_num)
  have h3 := G18.card_LC145 l hH
  exact GReach.ofX (reach_of_pos (by omega) (BBC (base t) l g) (G18.setX_mono l 15 18 (by norm_num) (by norm_num))
    24 (by omega) (by omega))

include hH in
lemma win13Y (t : T) (g : Orth (LC (Fin 17) H l)) :
    GReach (frame (BBC (base t) l g) (G18.setY l 15)) (frame (BBC (base t) l g) (G18.setY l 18))
      (fun φ => bcost φ 24) := by
  have h1 := G18.card_setY l hH 15 (by norm_num)
  have h2 := G18.card_setY l hH 18 (by norm_num)
  have h3 := G18.card_LC145 l hH
  exact GReach.ofX (reach_of_lt (by omega) (BBC (base t) l g) (G18.setY_mono l 15 18 (by norm_num) (by norm_num))
    24 (by omega) (by omega))

include hH in
/-- **window 13** (pair 13, stages 15..17) as an operator route (all gauges and ports). -/
theorem winSeg13 : P4L.ORoute (fun f y r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x13 .y13
      then matAct f (winF (Sl := Sl) (C := C) base l .x13 18 r * winF' (Sl := Sl) (C := C) base l .x13 15 r) (y r)
      else y r)
      (fun φ => ∑ r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x13 .y13, bcost φ 24) := by
  refine P4L.ORoute.steps_inv _ (winF base l .x13 15) (winF' base l .x13 15) (winF base l .x13 18)
    (fun r _ => winF_inv base l .x13 15 r) (fun _ φ => bcost φ 24) (fun r hr => ?_)
  obtain ⟨g, i, t, rfl⟩ := ownerSet_main l .x13 .y13 r hr
  rw [mem_ownerSet] at hr
  rcases hr with rfl | rfl
  · exact win13X base l hH t g _ (mainR g .x13 t)
  · exact win13Y base l hH t g _ (mainR g .y13 t)

/-- window 13 moves the view of every port by `win` with the product of its stage transforms. -/
theorem view_winSeg13 (f : ℕ) (y : Data (LC (Fin 17) H l) (PRole (Orth (LC (Fin 17) H l)) T Sl C) f)
    (g : Orth (LC (Fin 17) H l)) (t : T) :
    view f g t (fun r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x13 .y13
      then matAct f (winF (Sl := Sl) (C := C) base l .x13 18 r * winF' (Sl := Sl) (C := C) base l .x13 15 r) (y r)
      else y r)
      = win .x13 .y13 (P4L.prodF f (P4L.fr (BBC (base t) l g) ((Finset.range 3).biUnion fun j => G18.incr l (15 + j)))) (view f g t y) := by
  obtain ⟨eX, dX⟩ := G18.setX_add l 15 2 (by norm_num)
  obtain ⟨eY, dY⟩ := G18.setY_add l 15 2 (by norm_num)
  apply view_steps_win _ _ f y g t .x13 .y13 (by decide) _ (fun i => mem_ownerSet l .x13 .y13 g i t)
  rintro i (rfl | rfl) v
  · simp only [winF, winF', mainR, if_pos rfl]
    rw [← matAct_mul]
    have e : G18.setX l 18 = G18.setX l 15 ∪ ((Finset.range 3).biUnion fun j => G18.incr l (15 + j)) := eX
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dX v
  · simp only [winF, winF', mainR, if_neg (by decide : R32.y13 ≠ R32.x13)]
    rw [← matAct_mul]
    have e : G18.setY l 18 = G18.setY l 15 ∪ ((Finset.range 3).biUnion fun j => G18.incr l (15 + j)) := eY
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dY v

include hH in
lemma win14X (t : T) (g : Orth (LC (Fin 17) H l)) :
    GReach (frame (BBC (base t) l g) (G18.setX l 16)) (frame (BBC (base t) l g) (G18.setX l 18))
      (fun φ => bcost φ 16) := by
  have h1 := G18.card_setX l hH 16 (by norm_num)
  have h2 := G18.card_setX l hH 18 (by norm_num)
  have h3 := G18.card_LC145 l hH
  exact GReach.ofX (reach_of_pos (by omega) (BBC (base t) l g) (G18.setX_mono l 16 18 (by norm_num) (by norm_num))
    16 (by omega) (by omega))

include hH in
lemma win14Y (t : T) (g : Orth (LC (Fin 17) H l)) :
    GReach (frame (BBC (base t) l g) (G18.setY l 16)) (frame (BBC (base t) l g) (G18.setY l 18))
      (fun φ => bcost φ 16) := by
  have h1 := G18.card_setY l hH 16 (by norm_num)
  have h2 := G18.card_setY l hH 18 (by norm_num)
  have h3 := G18.card_LC145 l hH
  exact GReach.ofX (reach_of_lt (by omega) (BBC (base t) l g) (G18.setY_mono l 16 18 (by norm_num) (by norm_num))
    16 (by omega) (by omega))

include hH in
/-- **window 14** (pair 14, stages 16..17) as an operator route (all gauges and ports). -/
theorem winSeg14 : P4L.ORoute (fun f y r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x14 .y14
      then matAct f (winF (Sl := Sl) (C := C) base l .x14 18 r * winF' (Sl := Sl) (C := C) base l .x14 16 r) (y r)
      else y r)
      (fun φ => ∑ r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x14 .y14, bcost φ 16) := by
  refine P4L.ORoute.steps_inv _ (winF base l .x14 16) (winF' base l .x14 16) (winF base l .x14 18)
    (fun r _ => winF_inv base l .x14 16 r) (fun _ φ => bcost φ 16) (fun r hr => ?_)
  obtain ⟨g, i, t, rfl⟩ := ownerSet_main l .x14 .y14 r hr
  rw [mem_ownerSet] at hr
  rcases hr with rfl | rfl
  · exact win14X base l hH t g _ (mainR g .x14 t)
  · exact win14Y base l hH t g _ (mainR g .y14 t)

/-- window 14 moves the view of every port by `win` with the product of its stage transforms. -/
theorem view_winSeg14 (f : ℕ) (y : Data (LC (Fin 17) H l) (PRole (Orth (LC (Fin 17) H l)) T Sl C) f)
    (g : Orth (LC (Fin 17) H l)) (t : T) :
    view f g t (fun r => if r ∈ ownerSet (H := H) (T := T) (Sl := Sl) (C := C) l .x14 .y14
      then matAct f (winF (Sl := Sl) (C := C) base l .x14 18 r * winF' (Sl := Sl) (C := C) base l .x14 16 r) (y r)
      else y r)
      = win .x14 .y14 (P4L.prodF f (P4L.fr (BBC (base t) l g) ((Finset.range 2).biUnion fun j => G18.incr l (16 + j)))) (view f g t y) := by
  obtain ⟨eX, dX⟩ := G18.setX_add l 16 1 (by norm_num)
  obtain ⟨eY, dY⟩ := G18.setY_add l 16 1 (by norm_num)
  apply view_steps_win _ _ f y g t .x14 .y14 (by decide) _ (fun i => mem_ownerSet l .x14 .y14 g i t)
  rintro i (rfl | rfl) v
  · simp only [winF, winF', mainR, if_pos rfl]
    rw [← matAct_mul]
    have e : G18.setX l 18 = G18.setX l 16 ∪ ((Finset.range 2).biUnion fun j => G18.incr l (16 + j)) := eX
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dX v
  · simp only [winF, winF', mainR, if_neg (by decide : R32.y14 ≠ R32.x14)]
    rw [← matAct_mul]
    have e : G18.setY l 18 = G18.setY l 16 ∪ ((Finset.range 2).biUnion fun j => G18.incr l (16 + j)) := eY
    rw [e]
    exact P4L.walsh_ratio f _ _ _ dY v

end Win

end
end P16A8
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.P16A8.winSeg0
#print axioms OAI.PowerSaving.P16A8.winSeg1
#print axioms OAI.PowerSaving.P16A8.winSeg2
#print axioms OAI.PowerSaving.P16A8.winSeg3
#print axioms OAI.PowerSaving.P16A8.winSeg4
#print axioms OAI.PowerSaving.P16A8.winSeg5
#print axioms OAI.PowerSaving.P16A8.winSeg6
#print axioms OAI.PowerSaving.P16A8.winSeg7
#print axioms OAI.PowerSaving.P16A8.winSeg8
#print axioms OAI.PowerSaving.P16A8.winSeg9
#print axioms OAI.PowerSaving.P16A8.winSeg10
#print axioms OAI.PowerSaving.P16A8.winSeg11
#print axioms OAI.PowerSaving.P16A8.winSeg12
#print axioms OAI.PowerSaving.P16A8.winSeg13
#print axioms OAI.PowerSaving.P16A8.winSeg14
