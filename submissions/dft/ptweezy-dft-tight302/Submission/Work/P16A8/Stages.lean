import Submission.Work.P4L.Stages
import Submission.Work.G18.Lemmas
import Submission.Work.P16A8.View
-- changed for the tensor-power extension (30103/10000000); see Submission.lean

/-!
# P16A8 (p16a8), the full native calls of a unit

Full call `k` (pairs [0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 15], backward [False, True, True, True, True, True, True, True, True, True, True, True, True, True, True, True, True, False]) runs the provider `I` at the
windows `G18.winN l hH k d` with the gauges `G18.gaugeE base l k`; its frames are coordinate frames of
`BBC (base t) l g` (G18's `stage*_Xin` .. `stage*_Yout`), so `call_fwd` / `call_bwd` apply and the call moves the view of
every port by `callF` / `callB` with `d = prodF (fr A (incr k))` and `q = prodF (fr A {pivot})`.
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

section Stages
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T] [Fintype Sl] [DecidableEq Sl]
  [Fintype C] [DecidableEq C] {Ok : ∀ {β : Type} [Fintype β] [DecidableEq β], GWin H β → Prop}
  (I : GInvW H T Sl C Ok) (base : T → OBase H) (l : H) (hbase : ∀ t, I.tv t = (base t).v l)
  (hH : Fintype.card H = 9) (hOk : ∀ (n : ℕ) (d : Orth (LC (Fin 17) H l)), Ok (G18.winN l hH n d))

include hbase hOk in
/-- **full call 0** (forward, pair 0) as an operator route on the network. -/
theorem callSeg0 : P4L.ORoute (fun f y => multiAct f (stT (Sl := Sl) (C := C) (0 : Fin 18) (G18.basisA base l)
      (G18.setY l 0 ∪ {Sum.inl l} ∪ G18.incr l 0) (G18.setY l 0 ∪ G18.incr l 0) (G18.wnK I l hH 0))
      (point f (gFk (0 : Fin 18)) (multiAct f (stS' (0 : Fin 18) (G18.basisA base l) (G18.setY l 0 ∪ {Sum.inl l})
        (G18.setY l 0)) y)))
      (fun φ => (Fintype.card (Orth (LC (Fin 17) H l)) : ℝ) * I.cost φ) := by
  have eX1 := (G18.setX_succ l 0 (by norm_num)).1
  have eY1 := (G18.setY_succ l 0 (by norm_num)).1
  have eP := G18.setX_eq l 0 (by norm_num)
  refine call_fwd I (0 : Fin 18) (G18.gaugeE base l 0) (fun d => G18.winN l hH 0 d) (hOk 0) (G18.basisA base l)
    (G18.setY l 0 ∪ {Sum.inl l}) (G18.setY l 0 ∪ {Sum.inl l} ∪ G18.incr l 0) (G18.setY l 0) (G18.setY l 0 ∪ G18.incr l 0)
    (fun g t => ?_) (fun g t => ?_) (fun g t => ?_) (fun g t => ?_)
  · rw [hbase t, ← eP]; exact G18.stage0_Xin base l t g
  · rw [← eP, ← eX1]; exact G18.stage0_Xout base l t g
  · exact G18.stage0_Yin base l t g
  · rw [hbase t, ← eY1]; exact G18.stage0_Yout base l t g

/-- full call 0 moves the view of every port by `callF`. -/
theorem view_callSeg0 (f : ℕ) (y : Data (LC (Fin 17) H l) (PRole (Orth (LC (Fin 17) H l)) T Sl C) f)
    (g : Orth (LC (Fin 17) H l)) (t : T) :
    view f g t (multiAct f (stT (Sl := Sl) (C := C) (0 : Fin 18) (G18.basisA base l)
      (G18.setY l 0 ∪ {Sum.inl l} ∪ G18.incr l 0) (G18.setY l 0 ∪ G18.incr l 0) (G18.wnK I l hH 0))
      (point f (gFk (0 : Fin 18)) (multiAct f (stS' (0 : Fin 18) (G18.basisA base l) (G18.setY l 0 ∪ {Sum.inl l})
        (G18.setY l 0)) y)))
      = callF (xOf 0) (yOf 0) (P4L.prodF f (P4L.fr (G18.basisA base l g t) (G18.incr l 0))) (P4L.prodF f (fun x => (P4L.fr (G18.basisA base l g t) {Sum.inl l} x)⁻¹)) (view f g t y) := by
  have dX := (G18.setX_succ l 0 (by norm_num)).2
  have dY := (G18.setY_succ l 0 (by norm_num)).2
  have dP := (G18.setX_pivot l 0 (by norm_num)).2
  have eP := G18.setX_eq l 0 (by norm_num)
  rw [eP] at dX
  exact view_call_fwd (0 : Fin 18) (G18.basisA base l) (G18.setY l 0) (G18.incr l 0) (Sum.inl l) dX dY dP (G18.wnK I l hH 0) f y g t

include hbase hOk in
/-- **full call 1** (backward, pair 0) as an operator route on the network. -/
theorem callSeg1 : P4L.ORoute (fun f y => multiAct f (stT (Sl := Sl) (C := C) (1 : Fin 18) (G18.basisA base l)
      (G18.setY l 1 ∪ {Sum.inl l} ∪ G18.incr l 1) (G18.setY l 1 ∪ G18.incr l 1) (G18.wnK I l hH 1))
      (point f (gBk (1 : Fin 18)) (multiAct f (stS' (1 : Fin 18) (G18.basisA base l) (G18.setY l 1 ∪ {Sum.inl l})
        (G18.setY l 1)) y)))
      (fun φ => (Fintype.card (Orth (LC (Fin 17) H l)) : ℝ) * I.cost φ) := by
  have eX1 := (G18.setX_succ l 1 (by norm_num)).1
  have eY1 := (G18.setY_succ l 1 (by norm_num)).1
  have eP := G18.setX_eq l 1 (by norm_num)
  refine call_bwd I (1 : Fin 18) (G18.gaugeE base l 1) (fun d => G18.winN l hH 1 d) (hOk 1) (G18.basisA base l)
    (G18.setY l 1 ∪ {Sum.inl l}) (G18.setY l 1 ∪ {Sum.inl l} ∪ G18.incr l 1) (G18.setY l 1) (G18.setY l 1 ∪ G18.incr l 1)
    (fun g t => ?_) (fun g t => ?_) (fun g t => ?_) (fun g t => ?_)
  · rw [hbase t, ← eP]; exact G18.stage1_Xin base l t g
  · rw [← eP, ← eX1]; exact G18.stage1_Xout base l t g
  · exact G18.stage1_Yin base l t g
  · rw [hbase t, ← eY1]; exact G18.stage1_Yout base l t g

/-- full call 1 moves the view of every port by `callB`. -/
theorem view_callSeg1 (f : ℕ) (y : Data (LC (Fin 17) H l) (PRole (Orth (LC (Fin 17) H l)) T Sl C) f)
    (g : Orth (LC (Fin 17) H l)) (t : T) :
    view f g t (multiAct f (stT (Sl := Sl) (C := C) (1 : Fin 18) (G18.basisA base l)
      (G18.setY l 1 ∪ {Sum.inl l} ∪ G18.incr l 1) (G18.setY l 1 ∪ G18.incr l 1) (G18.wnK I l hH 1))
      (point f (gBk (1 : Fin 18)) (multiAct f (stS' (1 : Fin 18) (G18.basisA base l) (G18.setY l 1 ∪ {Sum.inl l})
        (G18.setY l 1)) y)))
      = callB (xOf 1) (yOf 1) (P4L.prodF f (P4L.fr (G18.basisA base l g t) (G18.incr l 1))) (P4L.prodF f (P4L.fr (G18.basisA base l g t) {Sum.inl l})) (view f g t y) := by
  have dX := (G18.setX_succ l 1 (by norm_num)).2
  have dY := (G18.setY_succ l 1 (by norm_num)).2
  have dP := (G18.setX_pivot l 1 (by norm_num)).2
  have eP := G18.setX_eq l 1 (by norm_num)
  rw [eP] at dX
  exact view_call_bwd (1 : Fin 18) (G18.basisA base l) (G18.setY l 1) (G18.incr l 1) (Sum.inl l) dX dY dP (G18.wnK I l hH 1) f y g t

include hbase hOk in
/-- **full call 2** (backward, pair 1) as an operator route on the network. -/
theorem callSeg2 : P4L.ORoute (fun f y => multiAct f (stT (Sl := Sl) (C := C) (2 : Fin 18) (G18.basisA base l)
      (G18.setY l 2 ∪ {Sum.inl l} ∪ G18.incr l 2) (G18.setY l 2 ∪ G18.incr l 2) (G18.wnK I l hH 2))
      (point f (gBk (2 : Fin 18)) (multiAct f (stS' (2 : Fin 18) (G18.basisA base l) (G18.setY l 2 ∪ {Sum.inl l})
        (G18.setY l 2)) y)))
      (fun φ => (Fintype.card (Orth (LC (Fin 17) H l)) : ℝ) * I.cost φ) := by
  have eX1 := (G18.setX_succ l 2 (by norm_num)).1
  have eY1 := (G18.setY_succ l 2 (by norm_num)).1
  have eP := G18.setX_eq l 2 (by norm_num)
  refine call_bwd I (2 : Fin 18) (G18.gaugeE base l 2) (fun d => G18.winN l hH 2 d) (hOk 2) (G18.basisA base l)
    (G18.setY l 2 ∪ {Sum.inl l}) (G18.setY l 2 ∪ {Sum.inl l} ∪ G18.incr l 2) (G18.setY l 2) (G18.setY l 2 ∪ G18.incr l 2)
    (fun g t => ?_) (fun g t => ?_) (fun g t => ?_) (fun g t => ?_)
  · rw [hbase t, ← eP]; exact G18.stage2_Xin base l t g
  · rw [← eP, ← eX1]; exact G18.stage2_Xout base l t g
  · exact G18.stage2_Yin base l t g
  · rw [hbase t, ← eY1]; exact G18.stage2_Yout base l t g

/-- full call 2 moves the view of every port by `callB`. -/
theorem view_callSeg2 (f : ℕ) (y : Data (LC (Fin 17) H l) (PRole (Orth (LC (Fin 17) H l)) T Sl C) f)
    (g : Orth (LC (Fin 17) H l)) (t : T) :
    view f g t (multiAct f (stT (Sl := Sl) (C := C) (2 : Fin 18) (G18.basisA base l)
      (G18.setY l 2 ∪ {Sum.inl l} ∪ G18.incr l 2) (G18.setY l 2 ∪ G18.incr l 2) (G18.wnK I l hH 2))
      (point f (gBk (2 : Fin 18)) (multiAct f (stS' (2 : Fin 18) (G18.basisA base l) (G18.setY l 2 ∪ {Sum.inl l})
        (G18.setY l 2)) y)))
      = callB (xOf 2) (yOf 2) (P4L.prodF f (P4L.fr (G18.basisA base l g t) (G18.incr l 2))) (P4L.prodF f (P4L.fr (G18.basisA base l g t) {Sum.inl l})) (view f g t y) := by
  have dX := (G18.setX_succ l 2 (by norm_num)).2
  have dY := (G18.setY_succ l 2 (by norm_num)).2
  have dP := (G18.setX_pivot l 2 (by norm_num)).2
  have eP := G18.setX_eq l 2 (by norm_num)
  rw [eP] at dX
  exact view_call_bwd (2 : Fin 18) (G18.basisA base l) (G18.setY l 2) (G18.incr l 2) (Sum.inl l) dX dY dP (G18.wnK I l hH 2) f y g t

include hbase hOk in
/-- **full call 3** (backward, pair 2) as an operator route on the network. -/
theorem callSeg3 : P4L.ORoute (fun f y => multiAct f (stT (Sl := Sl) (C := C) (3 : Fin 18) (G18.basisA base l)
      (G18.setY l 3 ∪ {Sum.inl l} ∪ G18.incr l 3) (G18.setY l 3 ∪ G18.incr l 3) (G18.wnK I l hH 3))
      (point f (gBk (3 : Fin 18)) (multiAct f (stS' (3 : Fin 18) (G18.basisA base l) (G18.setY l 3 ∪ {Sum.inl l})
        (G18.setY l 3)) y)))
      (fun φ => (Fintype.card (Orth (LC (Fin 17) H l)) : ℝ) * I.cost φ) := by
  have eX1 := (G18.setX_succ l 3 (by norm_num)).1
  have eY1 := (G18.setY_succ l 3 (by norm_num)).1
  have eP := G18.setX_eq l 3 (by norm_num)
  refine call_bwd I (3 : Fin 18) (G18.gaugeE base l 3) (fun d => G18.winN l hH 3 d) (hOk 3) (G18.basisA base l)
    (G18.setY l 3 ∪ {Sum.inl l}) (G18.setY l 3 ∪ {Sum.inl l} ∪ G18.incr l 3) (G18.setY l 3) (G18.setY l 3 ∪ G18.incr l 3)
    (fun g t => ?_) (fun g t => ?_) (fun g t => ?_) (fun g t => ?_)
  · rw [hbase t, ← eP]; exact G18.stage3_Xin base l t g
  · rw [← eP, ← eX1]; exact G18.stage3_Xout base l t g
  · exact G18.stage3_Yin base l t g
  · rw [hbase t, ← eY1]; exact G18.stage3_Yout base l t g

/-- full call 3 moves the view of every port by `callB`. -/
theorem view_callSeg3 (f : ℕ) (y : Data (LC (Fin 17) H l) (PRole (Orth (LC (Fin 17) H l)) T Sl C) f)
    (g : Orth (LC (Fin 17) H l)) (t : T) :
    view f g t (multiAct f (stT (Sl := Sl) (C := C) (3 : Fin 18) (G18.basisA base l)
      (G18.setY l 3 ∪ {Sum.inl l} ∪ G18.incr l 3) (G18.setY l 3 ∪ G18.incr l 3) (G18.wnK I l hH 3))
      (point f (gBk (3 : Fin 18)) (multiAct f (stS' (3 : Fin 18) (G18.basisA base l) (G18.setY l 3 ∪ {Sum.inl l})
        (G18.setY l 3)) y)))
      = callB (xOf 3) (yOf 3) (P4L.prodF f (P4L.fr (G18.basisA base l g t) (G18.incr l 3))) (P4L.prodF f (P4L.fr (G18.basisA base l g t) {Sum.inl l})) (view f g t y) := by
  have dX := (G18.setX_succ l 3 (by norm_num)).2
  have dY := (G18.setY_succ l 3 (by norm_num)).2
  have dP := (G18.setX_pivot l 3 (by norm_num)).2
  have eP := G18.setX_eq l 3 (by norm_num)
  rw [eP] at dX
  exact view_call_bwd (3 : Fin 18) (G18.basisA base l) (G18.setY l 3) (G18.incr l 3) (Sum.inl l) dX dY dP (G18.wnK I l hH 3) f y g t

include hbase hOk in
/-- **full call 4** (backward, pair 3) as an operator route on the network. -/
theorem callSeg4 : P4L.ORoute (fun f y => multiAct f (stT (Sl := Sl) (C := C) (4 : Fin 18) (G18.basisA base l)
      (G18.setY l 4 ∪ {Sum.inl l} ∪ G18.incr l 4) (G18.setY l 4 ∪ G18.incr l 4) (G18.wnK I l hH 4))
      (point f (gBk (4 : Fin 18)) (multiAct f (stS' (4 : Fin 18) (G18.basisA base l) (G18.setY l 4 ∪ {Sum.inl l})
        (G18.setY l 4)) y)))
      (fun φ => (Fintype.card (Orth (LC (Fin 17) H l)) : ℝ) * I.cost φ) := by
  have eX1 := (G18.setX_succ l 4 (by norm_num)).1
  have eY1 := (G18.setY_succ l 4 (by norm_num)).1
  have eP := G18.setX_eq l 4 (by norm_num)
  refine call_bwd I (4 : Fin 18) (G18.gaugeE base l 4) (fun d => G18.winN l hH 4 d) (hOk 4) (G18.basisA base l)
    (G18.setY l 4 ∪ {Sum.inl l}) (G18.setY l 4 ∪ {Sum.inl l} ∪ G18.incr l 4) (G18.setY l 4) (G18.setY l 4 ∪ G18.incr l 4)
    (fun g t => ?_) (fun g t => ?_) (fun g t => ?_) (fun g t => ?_)
  · rw [hbase t, ← eP]; exact G18.stage4_Xin base l t g
  · rw [← eP, ← eX1]; exact G18.stage4_Xout base l t g
  · exact G18.stage4_Yin base l t g
  · rw [hbase t, ← eY1]; exact G18.stage4_Yout base l t g

/-- full call 4 moves the view of every port by `callB`. -/
theorem view_callSeg4 (f : ℕ) (y : Data (LC (Fin 17) H l) (PRole (Orth (LC (Fin 17) H l)) T Sl C) f)
    (g : Orth (LC (Fin 17) H l)) (t : T) :
    view f g t (multiAct f (stT (Sl := Sl) (C := C) (4 : Fin 18) (G18.basisA base l)
      (G18.setY l 4 ∪ {Sum.inl l} ∪ G18.incr l 4) (G18.setY l 4 ∪ G18.incr l 4) (G18.wnK I l hH 4))
      (point f (gBk (4 : Fin 18)) (multiAct f (stS' (4 : Fin 18) (G18.basisA base l) (G18.setY l 4 ∪ {Sum.inl l})
        (G18.setY l 4)) y)))
      = callB (xOf 4) (yOf 4) (P4L.prodF f (P4L.fr (G18.basisA base l g t) (G18.incr l 4))) (P4L.prodF f (P4L.fr (G18.basisA base l g t) {Sum.inl l})) (view f g t y) := by
  have dX := (G18.setX_succ l 4 (by norm_num)).2
  have dY := (G18.setY_succ l 4 (by norm_num)).2
  have dP := (G18.setX_pivot l 4 (by norm_num)).2
  have eP := G18.setX_eq l 4 (by norm_num)
  rw [eP] at dX
  exact view_call_bwd (4 : Fin 18) (G18.basisA base l) (G18.setY l 4) (G18.incr l 4) (Sum.inl l) dX dY dP (G18.wnK I l hH 4) f y g t

include hbase hOk in
/-- **full call 5** (backward, pair 4) as an operator route on the network. -/
theorem callSeg5 : P4L.ORoute (fun f y => multiAct f (stT (Sl := Sl) (C := C) (5 : Fin 18) (G18.basisA base l)
      (G18.setY l 5 ∪ {Sum.inl l} ∪ G18.incr l 5) (G18.setY l 5 ∪ G18.incr l 5) (G18.wnK I l hH 5))
      (point f (gBk (5 : Fin 18)) (multiAct f (stS' (5 : Fin 18) (G18.basisA base l) (G18.setY l 5 ∪ {Sum.inl l})
        (G18.setY l 5)) y)))
      (fun φ => (Fintype.card (Orth (LC (Fin 17) H l)) : ℝ) * I.cost φ) := by
  have eX1 := (G18.setX_succ l 5 (by norm_num)).1
  have eY1 := (G18.setY_succ l 5 (by norm_num)).1
  have eP := G18.setX_eq l 5 (by norm_num)
  refine call_bwd I (5 : Fin 18) (G18.gaugeE base l 5) (fun d => G18.winN l hH 5 d) (hOk 5) (G18.basisA base l)
    (G18.setY l 5 ∪ {Sum.inl l}) (G18.setY l 5 ∪ {Sum.inl l} ∪ G18.incr l 5) (G18.setY l 5) (G18.setY l 5 ∪ G18.incr l 5)
    (fun g t => ?_) (fun g t => ?_) (fun g t => ?_) (fun g t => ?_)
  · rw [hbase t, ← eP]; exact G18.stage5_Xin base l t g
  · rw [← eP, ← eX1]; exact G18.stage5_Xout base l t g
  · exact G18.stage5_Yin base l t g
  · rw [hbase t, ← eY1]; exact G18.stage5_Yout base l t g

/-- full call 5 moves the view of every port by `callB`. -/
theorem view_callSeg5 (f : ℕ) (y : Data (LC (Fin 17) H l) (PRole (Orth (LC (Fin 17) H l)) T Sl C) f)
    (g : Orth (LC (Fin 17) H l)) (t : T) :
    view f g t (multiAct f (stT (Sl := Sl) (C := C) (5 : Fin 18) (G18.basisA base l)
      (G18.setY l 5 ∪ {Sum.inl l} ∪ G18.incr l 5) (G18.setY l 5 ∪ G18.incr l 5) (G18.wnK I l hH 5))
      (point f (gBk (5 : Fin 18)) (multiAct f (stS' (5 : Fin 18) (G18.basisA base l) (G18.setY l 5 ∪ {Sum.inl l})
        (G18.setY l 5)) y)))
      = callB (xOf 5) (yOf 5) (P4L.prodF f (P4L.fr (G18.basisA base l g t) (G18.incr l 5))) (P4L.prodF f (P4L.fr (G18.basisA base l g t) {Sum.inl l})) (view f g t y) := by
  have dX := (G18.setX_succ l 5 (by norm_num)).2
  have dY := (G18.setY_succ l 5 (by norm_num)).2
  have dP := (G18.setX_pivot l 5 (by norm_num)).2
  have eP := G18.setX_eq l 5 (by norm_num)
  rw [eP] at dX
  exact view_call_bwd (5 : Fin 18) (G18.basisA base l) (G18.setY l 5) (G18.incr l 5) (Sum.inl l) dX dY dP (G18.wnK I l hH 5) f y g t

include hbase hOk in
/-- **full call 6** (backward, pair 5) as an operator route on the network. -/
theorem callSeg6 : P4L.ORoute (fun f y => multiAct f (stT (Sl := Sl) (C := C) (6 : Fin 18) (G18.basisA base l)
      (G18.setY l 6 ∪ {Sum.inl l} ∪ G18.incr l 6) (G18.setY l 6 ∪ G18.incr l 6) (G18.wnK I l hH 6))
      (point f (gBk (6 : Fin 18)) (multiAct f (stS' (6 : Fin 18) (G18.basisA base l) (G18.setY l 6 ∪ {Sum.inl l})
        (G18.setY l 6)) y)))
      (fun φ => (Fintype.card (Orth (LC (Fin 17) H l)) : ℝ) * I.cost φ) := by
  have eX1 := (G18.setX_succ l 6 (by norm_num)).1
  have eY1 := (G18.setY_succ l 6 (by norm_num)).1
  have eP := G18.setX_eq l 6 (by norm_num)
  refine call_bwd I (6 : Fin 18) (G18.gaugeE base l 6) (fun d => G18.winN l hH 6 d) (hOk 6) (G18.basisA base l)
    (G18.setY l 6 ∪ {Sum.inl l}) (G18.setY l 6 ∪ {Sum.inl l} ∪ G18.incr l 6) (G18.setY l 6) (G18.setY l 6 ∪ G18.incr l 6)
    (fun g t => ?_) (fun g t => ?_) (fun g t => ?_) (fun g t => ?_)
  · rw [hbase t, ← eP]; exact G18.stage6_Xin base l t g
  · rw [← eP, ← eX1]; exact G18.stage6_Xout base l t g
  · exact G18.stage6_Yin base l t g
  · rw [hbase t, ← eY1]; exact G18.stage6_Yout base l t g

/-- full call 6 moves the view of every port by `callB`. -/
theorem view_callSeg6 (f : ℕ) (y : Data (LC (Fin 17) H l) (PRole (Orth (LC (Fin 17) H l)) T Sl C) f)
    (g : Orth (LC (Fin 17) H l)) (t : T) :
    view f g t (multiAct f (stT (Sl := Sl) (C := C) (6 : Fin 18) (G18.basisA base l)
      (G18.setY l 6 ∪ {Sum.inl l} ∪ G18.incr l 6) (G18.setY l 6 ∪ G18.incr l 6) (G18.wnK I l hH 6))
      (point f (gBk (6 : Fin 18)) (multiAct f (stS' (6 : Fin 18) (G18.basisA base l) (G18.setY l 6 ∪ {Sum.inl l})
        (G18.setY l 6)) y)))
      = callB (xOf 6) (yOf 6) (P4L.prodF f (P4L.fr (G18.basisA base l g t) (G18.incr l 6))) (P4L.prodF f (P4L.fr (G18.basisA base l g t) {Sum.inl l})) (view f g t y) := by
  have dX := (G18.setX_succ l 6 (by norm_num)).2
  have dY := (G18.setY_succ l 6 (by norm_num)).2
  have dP := (G18.setX_pivot l 6 (by norm_num)).2
  have eP := G18.setX_eq l 6 (by norm_num)
  rw [eP] at dX
  exact view_call_bwd (6 : Fin 18) (G18.basisA base l) (G18.setY l 6) (G18.incr l 6) (Sum.inl l) dX dY dP (G18.wnK I l hH 6) f y g t

include hbase hOk in
/-- **full call 7** (backward, pair 6) as an operator route on the network. -/
theorem callSeg7 : P4L.ORoute (fun f y => multiAct f (stT (Sl := Sl) (C := C) (7 : Fin 18) (G18.basisA base l)
      (G18.setY l 7 ∪ {Sum.inl l} ∪ G18.incr l 7) (G18.setY l 7 ∪ G18.incr l 7) (G18.wnK I l hH 7))
      (point f (gBk (7 : Fin 18)) (multiAct f (stS' (7 : Fin 18) (G18.basisA base l) (G18.setY l 7 ∪ {Sum.inl l})
        (G18.setY l 7)) y)))
      (fun φ => (Fintype.card (Orth (LC (Fin 17) H l)) : ℝ) * I.cost φ) := by
  have eX1 := (G18.setX_succ l 7 (by norm_num)).1
  have eY1 := (G18.setY_succ l 7 (by norm_num)).1
  have eP := G18.setX_eq l 7 (by norm_num)
  refine call_bwd I (7 : Fin 18) (G18.gaugeE base l 7) (fun d => G18.winN l hH 7 d) (hOk 7) (G18.basisA base l)
    (G18.setY l 7 ∪ {Sum.inl l}) (G18.setY l 7 ∪ {Sum.inl l} ∪ G18.incr l 7) (G18.setY l 7) (G18.setY l 7 ∪ G18.incr l 7)
    (fun g t => ?_) (fun g t => ?_) (fun g t => ?_) (fun g t => ?_)
  · rw [hbase t, ← eP]; exact G18.stage7_Xin base l t g
  · rw [← eP, ← eX1]; exact G18.stage7_Xout base l t g
  · exact G18.stage7_Yin base l t g
  · rw [hbase t, ← eY1]; exact G18.stage7_Yout base l t g

/-- full call 7 moves the view of every port by `callB`. -/
theorem view_callSeg7 (f : ℕ) (y : Data (LC (Fin 17) H l) (PRole (Orth (LC (Fin 17) H l)) T Sl C) f)
    (g : Orth (LC (Fin 17) H l)) (t : T) :
    view f g t (multiAct f (stT (Sl := Sl) (C := C) (7 : Fin 18) (G18.basisA base l)
      (G18.setY l 7 ∪ {Sum.inl l} ∪ G18.incr l 7) (G18.setY l 7 ∪ G18.incr l 7) (G18.wnK I l hH 7))
      (point f (gBk (7 : Fin 18)) (multiAct f (stS' (7 : Fin 18) (G18.basisA base l) (G18.setY l 7 ∪ {Sum.inl l})
        (G18.setY l 7)) y)))
      = callB (xOf 7) (yOf 7) (P4L.prodF f (P4L.fr (G18.basisA base l g t) (G18.incr l 7))) (P4L.prodF f (P4L.fr (G18.basisA base l g t) {Sum.inl l})) (view f g t y) := by
  have dX := (G18.setX_succ l 7 (by norm_num)).2
  have dY := (G18.setY_succ l 7 (by norm_num)).2
  have dP := (G18.setX_pivot l 7 (by norm_num)).2
  have eP := G18.setX_eq l 7 (by norm_num)
  rw [eP] at dX
  exact view_call_bwd (7 : Fin 18) (G18.basisA base l) (G18.setY l 7) (G18.incr l 7) (Sum.inl l) dX dY dP (G18.wnK I l hH 7) f y g t

include hbase hOk in
/-- **full call 8** (backward, pair 7) as an operator route on the network. -/
theorem callSeg8 : P4L.ORoute (fun f y => multiAct f (stT (Sl := Sl) (C := C) (8 : Fin 18) (G18.basisA base l)
      (G18.setY l 8 ∪ {Sum.inl l} ∪ G18.incr l 8) (G18.setY l 8 ∪ G18.incr l 8) (G18.wnK I l hH 8))
      (point f (gBk (8 : Fin 18)) (multiAct f (stS' (8 : Fin 18) (G18.basisA base l) (G18.setY l 8 ∪ {Sum.inl l})
        (G18.setY l 8)) y)))
      (fun φ => (Fintype.card (Orth (LC (Fin 17) H l)) : ℝ) * I.cost φ) := by
  have eX1 := (G18.setX_succ l 8 (by norm_num)).1
  have eY1 := (G18.setY_succ l 8 (by norm_num)).1
  have eP := G18.setX_eq l 8 (by norm_num)
  refine call_bwd I (8 : Fin 18) (G18.gaugeE base l 8) (fun d => G18.winN l hH 8 d) (hOk 8) (G18.basisA base l)
    (G18.setY l 8 ∪ {Sum.inl l}) (G18.setY l 8 ∪ {Sum.inl l} ∪ G18.incr l 8) (G18.setY l 8) (G18.setY l 8 ∪ G18.incr l 8)
    (fun g t => ?_) (fun g t => ?_) (fun g t => ?_) (fun g t => ?_)
  · rw [hbase t, ← eP]; exact G18.stage8_Xin base l t g
  · rw [← eP, ← eX1]; exact G18.stage8_Xout base l t g
  · exact G18.stage8_Yin base l t g
  · rw [hbase t, ← eY1]; exact G18.stage8_Yout base l t g

/-- full call 8 moves the view of every port by `callB`. -/
theorem view_callSeg8 (f : ℕ) (y : Data (LC (Fin 17) H l) (PRole (Orth (LC (Fin 17) H l)) T Sl C) f)
    (g : Orth (LC (Fin 17) H l)) (t : T) :
    view f g t (multiAct f (stT (Sl := Sl) (C := C) (8 : Fin 18) (G18.basisA base l)
      (G18.setY l 8 ∪ {Sum.inl l} ∪ G18.incr l 8) (G18.setY l 8 ∪ G18.incr l 8) (G18.wnK I l hH 8))
      (point f (gBk (8 : Fin 18)) (multiAct f (stS' (8 : Fin 18) (G18.basisA base l) (G18.setY l 8 ∪ {Sum.inl l})
        (G18.setY l 8)) y)))
      = callB (xOf 8) (yOf 8) (P4L.prodF f (P4L.fr (G18.basisA base l g t) (G18.incr l 8))) (P4L.prodF f (P4L.fr (G18.basisA base l g t) {Sum.inl l})) (view f g t y) := by
  have dX := (G18.setX_succ l 8 (by norm_num)).2
  have dY := (G18.setY_succ l 8 (by norm_num)).2
  have dP := (G18.setX_pivot l 8 (by norm_num)).2
  have eP := G18.setX_eq l 8 (by norm_num)
  rw [eP] at dX
  exact view_call_bwd (8 : Fin 18) (G18.basisA base l) (G18.setY l 8) (G18.incr l 8) (Sum.inl l) dX dY dP (G18.wnK I l hH 8) f y g t

include hbase hOk in
/-- **full call 9** (backward, pair 8) as an operator route on the network. -/
theorem callSeg9 : P4L.ORoute (fun f y => multiAct f (stT (Sl := Sl) (C := C) (9 : Fin 18) (G18.basisA base l)
      (G18.setY l 9 ∪ {Sum.inl l} ∪ G18.incr l 9) (G18.setY l 9 ∪ G18.incr l 9) (G18.wnK I l hH 9))
      (point f (gBk (9 : Fin 18)) (multiAct f (stS' (9 : Fin 18) (G18.basisA base l) (G18.setY l 9 ∪ {Sum.inl l})
        (G18.setY l 9)) y)))
      (fun φ => (Fintype.card (Orth (LC (Fin 17) H l)) : ℝ) * I.cost φ) := by
  have eX1 := (G18.setX_succ l 9 (by norm_num)).1
  have eY1 := (G18.setY_succ l 9 (by norm_num)).1
  have eP := G18.setX_eq l 9 (by norm_num)
  refine call_bwd I (9 : Fin 18) (G18.gaugeE base l 9) (fun d => G18.winN l hH 9 d) (hOk 9) (G18.basisA base l)
    (G18.setY l 9 ∪ {Sum.inl l}) (G18.setY l 9 ∪ {Sum.inl l} ∪ G18.incr l 9) (G18.setY l 9) (G18.setY l 9 ∪ G18.incr l 9)
    (fun g t => ?_) (fun g t => ?_) (fun g t => ?_) (fun g t => ?_)
  · rw [hbase t, ← eP]; exact G18.stage9_Xin base l t g
  · rw [← eP, ← eX1]; exact G18.stage9_Xout base l t g
  · exact G18.stage9_Yin base l t g
  · rw [hbase t, ← eY1]; exact G18.stage9_Yout base l t g

/-- full call 9 moves the view of every port by `callB`. -/
theorem view_callSeg9 (f : ℕ) (y : Data (LC (Fin 17) H l) (PRole (Orth (LC (Fin 17) H l)) T Sl C) f)
    (g : Orth (LC (Fin 17) H l)) (t : T) :
    view f g t (multiAct f (stT (Sl := Sl) (C := C) (9 : Fin 18) (G18.basisA base l)
      (G18.setY l 9 ∪ {Sum.inl l} ∪ G18.incr l 9) (G18.setY l 9 ∪ G18.incr l 9) (G18.wnK I l hH 9))
      (point f (gBk (9 : Fin 18)) (multiAct f (stS' (9 : Fin 18) (G18.basisA base l) (G18.setY l 9 ∪ {Sum.inl l})
        (G18.setY l 9)) y)))
      = callB (xOf 9) (yOf 9) (P4L.prodF f (P4L.fr (G18.basisA base l g t) (G18.incr l 9))) (P4L.prodF f (P4L.fr (G18.basisA base l g t) {Sum.inl l})) (view f g t y) := by
  have dX := (G18.setX_succ l 9 (by norm_num)).2
  have dY := (G18.setY_succ l 9 (by norm_num)).2
  have dP := (G18.setX_pivot l 9 (by norm_num)).2
  have eP := G18.setX_eq l 9 (by norm_num)
  rw [eP] at dX
  exact view_call_bwd (9 : Fin 18) (G18.basisA base l) (G18.setY l 9) (G18.incr l 9) (Sum.inl l) dX dY dP (G18.wnK I l hH 9) f y g t

include hbase hOk in
/-- **full call 10** (backward, pair 9) as an operator route on the network. -/
theorem callSeg10 : P4L.ORoute (fun f y => multiAct f (stT (Sl := Sl) (C := C) (10 : Fin 18) (G18.basisA base l)
      (G18.setY l 10 ∪ {Sum.inl l} ∪ G18.incr l 10) (G18.setY l 10 ∪ G18.incr l 10) (G18.wnK I l hH 10))
      (point f (gBk (10 : Fin 18)) (multiAct f (stS' (10 : Fin 18) (G18.basisA base l) (G18.setY l 10 ∪ {Sum.inl l})
        (G18.setY l 10)) y)))
      (fun φ => (Fintype.card (Orth (LC (Fin 17) H l)) : ℝ) * I.cost φ) := by
  have eX1 := (G18.setX_succ l 10 (by norm_num)).1
  have eY1 := (G18.setY_succ l 10 (by norm_num)).1
  have eP := G18.setX_eq l 10 (by norm_num)
  refine call_bwd I (10 : Fin 18) (G18.gaugeE base l 10) (fun d => G18.winN l hH 10 d) (hOk 10) (G18.basisA base l)
    (G18.setY l 10 ∪ {Sum.inl l}) (G18.setY l 10 ∪ {Sum.inl l} ∪ G18.incr l 10) (G18.setY l 10) (G18.setY l 10 ∪ G18.incr l 10)
    (fun g t => ?_) (fun g t => ?_) (fun g t => ?_) (fun g t => ?_)
  · rw [hbase t, ← eP]; exact G18.stage10_Xin base l t g
  · rw [← eP, ← eX1]; exact G18.stage10_Xout base l t g
  · exact G18.stage10_Yin base l t g
  · rw [hbase t, ← eY1]; exact G18.stage10_Yout base l t g

/-- full call 10 moves the view of every port by `callB`. -/
theorem view_callSeg10 (f : ℕ) (y : Data (LC (Fin 17) H l) (PRole (Orth (LC (Fin 17) H l)) T Sl C) f)
    (g : Orth (LC (Fin 17) H l)) (t : T) :
    view f g t (multiAct f (stT (Sl := Sl) (C := C) (10 : Fin 18) (G18.basisA base l)
      (G18.setY l 10 ∪ {Sum.inl l} ∪ G18.incr l 10) (G18.setY l 10 ∪ G18.incr l 10) (G18.wnK I l hH 10))
      (point f (gBk (10 : Fin 18)) (multiAct f (stS' (10 : Fin 18) (G18.basisA base l) (G18.setY l 10 ∪ {Sum.inl l})
        (G18.setY l 10)) y)))
      = callB (xOf 10) (yOf 10) (P4L.prodF f (P4L.fr (G18.basisA base l g t) (G18.incr l 10))) (P4L.prodF f (P4L.fr (G18.basisA base l g t) {Sum.inl l})) (view f g t y) := by
  have dX := (G18.setX_succ l 10 (by norm_num)).2
  have dY := (G18.setY_succ l 10 (by norm_num)).2
  have dP := (G18.setX_pivot l 10 (by norm_num)).2
  have eP := G18.setX_eq l 10 (by norm_num)
  rw [eP] at dX
  exact view_call_bwd (10 : Fin 18) (G18.basisA base l) (G18.setY l 10) (G18.incr l 10) (Sum.inl l) dX dY dP (G18.wnK I l hH 10) f y g t

include hbase hOk in
/-- **full call 11** (backward, pair 10) as an operator route on the network. -/
theorem callSeg11 : P4L.ORoute (fun f y => multiAct f (stT (Sl := Sl) (C := C) (11 : Fin 18) (G18.basisA base l)
      (G18.setY l 11 ∪ {Sum.inl l} ∪ G18.incr l 11) (G18.setY l 11 ∪ G18.incr l 11) (G18.wnK I l hH 11))
      (point f (gBk (11 : Fin 18)) (multiAct f (stS' (11 : Fin 18) (G18.basisA base l) (G18.setY l 11 ∪ {Sum.inl l})
        (G18.setY l 11)) y)))
      (fun φ => (Fintype.card (Orth (LC (Fin 17) H l)) : ℝ) * I.cost φ) := by
  have eX1 := (G18.setX_succ l 11 (by norm_num)).1
  have eY1 := (G18.setY_succ l 11 (by norm_num)).1
  have eP := G18.setX_eq l 11 (by norm_num)
  refine call_bwd I (11 : Fin 18) (G18.gaugeE base l 11) (fun d => G18.winN l hH 11 d) (hOk 11) (G18.basisA base l)
    (G18.setY l 11 ∪ {Sum.inl l}) (G18.setY l 11 ∪ {Sum.inl l} ∪ G18.incr l 11) (G18.setY l 11) (G18.setY l 11 ∪ G18.incr l 11)
    (fun g t => ?_) (fun g t => ?_) (fun g t => ?_) (fun g t => ?_)
  · rw [hbase t, ← eP]; exact G18.stage11_Xin base l t g
  · rw [← eP, ← eX1]; exact G18.stage11_Xout base l t g
  · exact G18.stage11_Yin base l t g
  · rw [hbase t, ← eY1]; exact G18.stage11_Yout base l t g

/-- full call 11 moves the view of every port by `callB`. -/
theorem view_callSeg11 (f : ℕ) (y : Data (LC (Fin 17) H l) (PRole (Orth (LC (Fin 17) H l)) T Sl C) f)
    (g : Orth (LC (Fin 17) H l)) (t : T) :
    view f g t (multiAct f (stT (Sl := Sl) (C := C) (11 : Fin 18) (G18.basisA base l)
      (G18.setY l 11 ∪ {Sum.inl l} ∪ G18.incr l 11) (G18.setY l 11 ∪ G18.incr l 11) (G18.wnK I l hH 11))
      (point f (gBk (11 : Fin 18)) (multiAct f (stS' (11 : Fin 18) (G18.basisA base l) (G18.setY l 11 ∪ {Sum.inl l})
        (G18.setY l 11)) y)))
      = callB (xOf 11) (yOf 11) (P4L.prodF f (P4L.fr (G18.basisA base l g t) (G18.incr l 11))) (P4L.prodF f (P4L.fr (G18.basisA base l g t) {Sum.inl l})) (view f g t y) := by
  have dX := (G18.setX_succ l 11 (by norm_num)).2
  have dY := (G18.setY_succ l 11 (by norm_num)).2
  have dP := (G18.setX_pivot l 11 (by norm_num)).2
  have eP := G18.setX_eq l 11 (by norm_num)
  rw [eP] at dX
  exact view_call_bwd (11 : Fin 18) (G18.basisA base l) (G18.setY l 11) (G18.incr l 11) (Sum.inl l) dX dY dP (G18.wnK I l hH 11) f y g t

include hbase hOk in
/-- **full call 12** (backward, pair 11) as an operator route on the network. -/
theorem callSeg12 : P4L.ORoute (fun f y => multiAct f (stT (Sl := Sl) (C := C) (12 : Fin 18) (G18.basisA base l)
      (G18.setY l 12 ∪ {Sum.inl l} ∪ G18.incr l 12) (G18.setY l 12 ∪ G18.incr l 12) (G18.wnK I l hH 12))
      (point f (gBk (12 : Fin 18)) (multiAct f (stS' (12 : Fin 18) (G18.basisA base l) (G18.setY l 12 ∪ {Sum.inl l})
        (G18.setY l 12)) y)))
      (fun φ => (Fintype.card (Orth (LC (Fin 17) H l)) : ℝ) * I.cost φ) := by
  have eX1 := (G18.setX_succ l 12 (by norm_num)).1
  have eY1 := (G18.setY_succ l 12 (by norm_num)).1
  have eP := G18.setX_eq l 12 (by norm_num)
  refine call_bwd I (12 : Fin 18) (G18.gaugeE base l 12) (fun d => G18.winN l hH 12 d) (hOk 12) (G18.basisA base l)
    (G18.setY l 12 ∪ {Sum.inl l}) (G18.setY l 12 ∪ {Sum.inl l} ∪ G18.incr l 12) (G18.setY l 12) (G18.setY l 12 ∪ G18.incr l 12)
    (fun g t => ?_) (fun g t => ?_) (fun g t => ?_) (fun g t => ?_)
  · rw [hbase t, ← eP]; exact G18.stage12_Xin base l t g
  · rw [← eP, ← eX1]; exact G18.stage12_Xout base l t g
  · exact G18.stage12_Yin base l t g
  · rw [hbase t, ← eY1]; exact G18.stage12_Yout base l t g

/-- full call 12 moves the view of every port by `callB`. -/
theorem view_callSeg12 (f : ℕ) (y : Data (LC (Fin 17) H l) (PRole (Orth (LC (Fin 17) H l)) T Sl C) f)
    (g : Orth (LC (Fin 17) H l)) (t : T) :
    view f g t (multiAct f (stT (Sl := Sl) (C := C) (12 : Fin 18) (G18.basisA base l)
      (G18.setY l 12 ∪ {Sum.inl l} ∪ G18.incr l 12) (G18.setY l 12 ∪ G18.incr l 12) (G18.wnK I l hH 12))
      (point f (gBk (12 : Fin 18)) (multiAct f (stS' (12 : Fin 18) (G18.basisA base l) (G18.setY l 12 ∪ {Sum.inl l})
        (G18.setY l 12)) y)))
      = callB (xOf 12) (yOf 12) (P4L.prodF f (P4L.fr (G18.basisA base l g t) (G18.incr l 12))) (P4L.prodF f (P4L.fr (G18.basisA base l g t) {Sum.inl l})) (view f g t y) := by
  have dX := (G18.setX_succ l 12 (by norm_num)).2
  have dY := (G18.setY_succ l 12 (by norm_num)).2
  have dP := (G18.setX_pivot l 12 (by norm_num)).2
  have eP := G18.setX_eq l 12 (by norm_num)
  rw [eP] at dX
  exact view_call_bwd (12 : Fin 18) (G18.basisA base l) (G18.setY l 12) (G18.incr l 12) (Sum.inl l) dX dY dP (G18.wnK I l hH 12) f y g t

include hbase hOk in
/-- **full call 13** (backward, pair 12) as an operator route on the network. -/
theorem callSeg13 : P4L.ORoute (fun f y => multiAct f (stT (Sl := Sl) (C := C) (13 : Fin 18) (G18.basisA base l)
      (G18.setY l 13 ∪ {Sum.inl l} ∪ G18.incr l 13) (G18.setY l 13 ∪ G18.incr l 13) (G18.wnK I l hH 13))
      (point f (gBk (13 : Fin 18)) (multiAct f (stS' (13 : Fin 18) (G18.basisA base l) (G18.setY l 13 ∪ {Sum.inl l})
        (G18.setY l 13)) y)))
      (fun φ => (Fintype.card (Orth (LC (Fin 17) H l)) : ℝ) * I.cost φ) := by
  have eX1 := (G18.setX_succ l 13 (by norm_num)).1
  have eY1 := (G18.setY_succ l 13 (by norm_num)).1
  have eP := G18.setX_eq l 13 (by norm_num)
  refine call_bwd I (13 : Fin 18) (G18.gaugeE base l 13) (fun d => G18.winN l hH 13 d) (hOk 13) (G18.basisA base l)
    (G18.setY l 13 ∪ {Sum.inl l}) (G18.setY l 13 ∪ {Sum.inl l} ∪ G18.incr l 13) (G18.setY l 13) (G18.setY l 13 ∪ G18.incr l 13)
    (fun g t => ?_) (fun g t => ?_) (fun g t => ?_) (fun g t => ?_)
  · rw [hbase t, ← eP]; exact G18.stage13_Xin base l t g
  · rw [← eP, ← eX1]; exact G18.stage13_Xout base l t g
  · exact G18.stage13_Yin base l t g
  · rw [hbase t, ← eY1]; exact G18.stage13_Yout base l t g

/-- full call 13 moves the view of every port by `callB`. -/
theorem view_callSeg13 (f : ℕ) (y : Data (LC (Fin 17) H l) (PRole (Orth (LC (Fin 17) H l)) T Sl C) f)
    (g : Orth (LC (Fin 17) H l)) (t : T) :
    view f g t (multiAct f (stT (Sl := Sl) (C := C) (13 : Fin 18) (G18.basisA base l)
      (G18.setY l 13 ∪ {Sum.inl l} ∪ G18.incr l 13) (G18.setY l 13 ∪ G18.incr l 13) (G18.wnK I l hH 13))
      (point f (gBk (13 : Fin 18)) (multiAct f (stS' (13 : Fin 18) (G18.basisA base l) (G18.setY l 13 ∪ {Sum.inl l})
        (G18.setY l 13)) y)))
      = callB (xOf 13) (yOf 13) (P4L.prodF f (P4L.fr (G18.basisA base l g t) (G18.incr l 13))) (P4L.prodF f (P4L.fr (G18.basisA base l g t) {Sum.inl l})) (view f g t y) := by
  have dX := (G18.setX_succ l 13 (by norm_num)).2
  have dY := (G18.setY_succ l 13 (by norm_num)).2
  have dP := (G18.setX_pivot l 13 (by norm_num)).2
  have eP := G18.setX_eq l 13 (by norm_num)
  rw [eP] at dX
  exact view_call_bwd (13 : Fin 18) (G18.basisA base l) (G18.setY l 13) (G18.incr l 13) (Sum.inl l) dX dY dP (G18.wnK I l hH 13) f y g t

include hbase hOk in
/-- **full call 14** (backward, pair 13) as an operator route on the network. -/
theorem callSeg14 : P4L.ORoute (fun f y => multiAct f (stT (Sl := Sl) (C := C) (14 : Fin 18) (G18.basisA base l)
      (G18.setY l 14 ∪ {Sum.inl l} ∪ G18.incr l 14) (G18.setY l 14 ∪ G18.incr l 14) (G18.wnK I l hH 14))
      (point f (gBk (14 : Fin 18)) (multiAct f (stS' (14 : Fin 18) (G18.basisA base l) (G18.setY l 14 ∪ {Sum.inl l})
        (G18.setY l 14)) y)))
      (fun φ => (Fintype.card (Orth (LC (Fin 17) H l)) : ℝ) * I.cost φ) := by
  have eX1 := (G18.setX_succ l 14 (by norm_num)).1
  have eY1 := (G18.setY_succ l 14 (by norm_num)).1
  have eP := G18.setX_eq l 14 (by norm_num)
  refine call_bwd I (14 : Fin 18) (G18.gaugeE base l 14) (fun d => G18.winN l hH 14 d) (hOk 14) (G18.basisA base l)
    (G18.setY l 14 ∪ {Sum.inl l}) (G18.setY l 14 ∪ {Sum.inl l} ∪ G18.incr l 14) (G18.setY l 14) (G18.setY l 14 ∪ G18.incr l 14)
    (fun g t => ?_) (fun g t => ?_) (fun g t => ?_) (fun g t => ?_)
  · rw [hbase t, ← eP]; exact G18.stage14_Xin base l t g
  · rw [← eP, ← eX1]; exact G18.stage14_Xout base l t g
  · exact G18.stage14_Yin base l t g
  · rw [hbase t, ← eY1]; exact G18.stage14_Yout base l t g

/-- full call 14 moves the view of every port by `callB`. -/
theorem view_callSeg14 (f : ℕ) (y : Data (LC (Fin 17) H l) (PRole (Orth (LC (Fin 17) H l)) T Sl C) f)
    (g : Orth (LC (Fin 17) H l)) (t : T) :
    view f g t (multiAct f (stT (Sl := Sl) (C := C) (14 : Fin 18) (G18.basisA base l)
      (G18.setY l 14 ∪ {Sum.inl l} ∪ G18.incr l 14) (G18.setY l 14 ∪ G18.incr l 14) (G18.wnK I l hH 14))
      (point f (gBk (14 : Fin 18)) (multiAct f (stS' (14 : Fin 18) (G18.basisA base l) (G18.setY l 14 ∪ {Sum.inl l})
        (G18.setY l 14)) y)))
      = callB (xOf 14) (yOf 14) (P4L.prodF f (P4L.fr (G18.basisA base l g t) (G18.incr l 14))) (P4L.prodF f (P4L.fr (G18.basisA base l g t) {Sum.inl l})) (view f g t y) := by
  have dX := (G18.setX_succ l 14 (by norm_num)).2
  have dY := (G18.setY_succ l 14 (by norm_num)).2
  have dP := (G18.setX_pivot l 14 (by norm_num)).2
  have eP := G18.setX_eq l 14 (by norm_num)
  rw [eP] at dX
  exact view_call_bwd (14 : Fin 18) (G18.basisA base l) (G18.setY l 14) (G18.incr l 14) (Sum.inl l) dX dY dP (G18.wnK I l hH 14) f y g t

include hbase hOk in
/-- **full call 15** (backward, pair 14) as an operator route on the network. -/
theorem callSeg15 : P4L.ORoute (fun f y => multiAct f (stT (Sl := Sl) (C := C) (15 : Fin 18) (G18.basisA base l)
      (G18.setY l 15 ∪ {Sum.inl l} ∪ G18.incr l 15) (G18.setY l 15 ∪ G18.incr l 15) (G18.wnK I l hH 15))
      (point f (gBk (15 : Fin 18)) (multiAct f (stS' (15 : Fin 18) (G18.basisA base l) (G18.setY l 15 ∪ {Sum.inl l})
        (G18.setY l 15)) y)))
      (fun φ => (Fintype.card (Orth (LC (Fin 17) H l)) : ℝ) * I.cost φ) := by
  have eX1 := (G18.setX_succ l 15 (by norm_num)).1
  have eY1 := (G18.setY_succ l 15 (by norm_num)).1
  have eP := G18.setX_eq l 15 (by norm_num)
  refine call_bwd I (15 : Fin 18) (G18.gaugeE base l 15) (fun d => G18.winN l hH 15 d) (hOk 15) (G18.basisA base l)
    (G18.setY l 15 ∪ {Sum.inl l}) (G18.setY l 15 ∪ {Sum.inl l} ∪ G18.incr l 15) (G18.setY l 15) (G18.setY l 15 ∪ G18.incr l 15)
    (fun g t => ?_) (fun g t => ?_) (fun g t => ?_) (fun g t => ?_)
  · rw [hbase t, ← eP]; exact G18.stage15_Xin base l t g
  · rw [← eP, ← eX1]; exact G18.stage15_Xout base l t g
  · exact G18.stage15_Yin base l t g
  · rw [hbase t, ← eY1]; exact G18.stage15_Yout base l t g

/-- full call 15 moves the view of every port by `callB`. -/
theorem view_callSeg15 (f : ℕ) (y : Data (LC (Fin 17) H l) (PRole (Orth (LC (Fin 17) H l)) T Sl C) f)
    (g : Orth (LC (Fin 17) H l)) (t : T) :
    view f g t (multiAct f (stT (Sl := Sl) (C := C) (15 : Fin 18) (G18.basisA base l)
      (G18.setY l 15 ∪ {Sum.inl l} ∪ G18.incr l 15) (G18.setY l 15 ∪ G18.incr l 15) (G18.wnK I l hH 15))
      (point f (gBk (15 : Fin 18)) (multiAct f (stS' (15 : Fin 18) (G18.basisA base l) (G18.setY l 15 ∪ {Sum.inl l})
        (G18.setY l 15)) y)))
      = callB (xOf 15) (yOf 15) (P4L.prodF f (P4L.fr (G18.basisA base l g t) (G18.incr l 15))) (P4L.prodF f (P4L.fr (G18.basisA base l g t) {Sum.inl l})) (view f g t y) := by
  have dX := (G18.setX_succ l 15 (by norm_num)).2
  have dY := (G18.setY_succ l 15 (by norm_num)).2
  have dP := (G18.setX_pivot l 15 (by norm_num)).2
  have eP := G18.setX_eq l 15 (by norm_num)
  rw [eP] at dX
  exact view_call_bwd (15 : Fin 18) (G18.basisA base l) (G18.setY l 15) (G18.incr l 15) (Sum.inl l) dX dY dP (G18.wnK I l hH 15) f y g t

include hbase hOk in
/-- **full call 16** (backward, pair 15) as an operator route on the network. -/
theorem callSeg16 : P4L.ORoute (fun f y => multiAct f (stT (Sl := Sl) (C := C) (16 : Fin 18) (G18.basisA base l)
      (G18.setY l 16 ∪ {Sum.inl l} ∪ G18.incr l 16) (G18.setY l 16 ∪ G18.incr l 16) (G18.wnK I l hH 16))
      (point f (gBk (16 : Fin 18)) (multiAct f (stS' (16 : Fin 18) (G18.basisA base l) (G18.setY l 16 ∪ {Sum.inl l})
        (G18.setY l 16)) y)))
      (fun φ => (Fintype.card (Orth (LC (Fin 17) H l)) : ℝ) * I.cost φ) := by
  have eX1 := (G18.setX_succ l 16 (by norm_num)).1
  have eY1 := (G18.setY_succ l 16 (by norm_num)).1
  have eP := G18.setX_eq l 16 (by norm_num)
  refine call_bwd I (16 : Fin 18) (G18.gaugeE base l 16) (fun d => G18.winN l hH 16 d) (hOk 16) (G18.basisA base l)
    (G18.setY l 16 ∪ {Sum.inl l}) (G18.setY l 16 ∪ {Sum.inl l} ∪ G18.incr l 16) (G18.setY l 16) (G18.setY l 16 ∪ G18.incr l 16)
    (fun g t => ?_) (fun g t => ?_) (fun g t => ?_) (fun g t => ?_)
  · rw [hbase t, ← eP]; exact G18.stage16_Xin base l t g
  · rw [← eP, ← eX1]; exact G18.stage16_Xout base l t g
  · exact G18.stage16_Yin base l t g
  · rw [hbase t, ← eY1]; exact G18.stage16_Yout base l t g

/-- full call 16 moves the view of every port by `callB`. -/
theorem view_callSeg16 (f : ℕ) (y : Data (LC (Fin 17) H l) (PRole (Orth (LC (Fin 17) H l)) T Sl C) f)
    (g : Orth (LC (Fin 17) H l)) (t : T) :
    view f g t (multiAct f (stT (Sl := Sl) (C := C) (16 : Fin 18) (G18.basisA base l)
      (G18.setY l 16 ∪ {Sum.inl l} ∪ G18.incr l 16) (G18.setY l 16 ∪ G18.incr l 16) (G18.wnK I l hH 16))
      (point f (gBk (16 : Fin 18)) (multiAct f (stS' (16 : Fin 18) (G18.basisA base l) (G18.setY l 16 ∪ {Sum.inl l})
        (G18.setY l 16)) y)))
      = callB (xOf 16) (yOf 16) (P4L.prodF f (P4L.fr (G18.basisA base l g t) (G18.incr l 16))) (P4L.prodF f (P4L.fr (G18.basisA base l g t) {Sum.inl l})) (view f g t y) := by
  have dX := (G18.setX_succ l 16 (by norm_num)).2
  have dY := (G18.setY_succ l 16 (by norm_num)).2
  have dP := (G18.setX_pivot l 16 (by norm_num)).2
  have eP := G18.setX_eq l 16 (by norm_num)
  rw [eP] at dX
  exact view_call_bwd (16 : Fin 18) (G18.basisA base l) (G18.setY l 16) (G18.incr l 16) (Sum.inl l) dX dY dP (G18.wnK I l hH 16) f y g t

include hbase hOk in
/-- **full call 17** (forward, pair 15) as an operator route on the network. -/
theorem callSeg17 : P4L.ORoute (fun f y => multiAct f (stT (Sl := Sl) (C := C) (17 : Fin 18) (G18.basisA base l)
      (G18.setY l 17 ∪ {Sum.inl l} ∪ G18.incr l 17) (G18.setY l 17 ∪ G18.incr l 17) (G18.wnK I l hH 17))
      (point f (gFk (17 : Fin 18)) (multiAct f (stS' (17 : Fin 18) (G18.basisA base l) (G18.setY l 17 ∪ {Sum.inl l})
        (G18.setY l 17)) y)))
      (fun φ => (Fintype.card (Orth (LC (Fin 17) H l)) : ℝ) * I.cost φ) := by
  have eX1 := (G18.setX_succ l 17 (by norm_num)).1
  have eY1 := (G18.setY_succ l 17 (by norm_num)).1
  have eP := G18.setX_eq l 17 (by norm_num)
  refine call_fwd I (17 : Fin 18) (G18.gaugeE base l 17) (fun d => G18.winN l hH 17 d) (hOk 17) (G18.basisA base l)
    (G18.setY l 17 ∪ {Sum.inl l}) (G18.setY l 17 ∪ {Sum.inl l} ∪ G18.incr l 17) (G18.setY l 17) (G18.setY l 17 ∪ G18.incr l 17)
    (fun g t => ?_) (fun g t => ?_) (fun g t => ?_) (fun g t => ?_)
  · rw [hbase t, ← eP]; exact G18.stage17_Xin base l t g
  · rw [← eP, ← eX1]; exact G18.stage17_Xout base l t g
  · exact G18.stage17_Yin base l t g
  · rw [hbase t, ← eY1]; exact G18.stage17_Yout base l t g

/-- full call 17 moves the view of every port by `callF`. -/
theorem view_callSeg17 (f : ℕ) (y : Data (LC (Fin 17) H l) (PRole (Orth (LC (Fin 17) H l)) T Sl C) f)
    (g : Orth (LC (Fin 17) H l)) (t : T) :
    view f g t (multiAct f (stT (Sl := Sl) (C := C) (17 : Fin 18) (G18.basisA base l)
      (G18.setY l 17 ∪ {Sum.inl l} ∪ G18.incr l 17) (G18.setY l 17 ∪ G18.incr l 17) (G18.wnK I l hH 17))
      (point f (gFk (17 : Fin 18)) (multiAct f (stS' (17 : Fin 18) (G18.basisA base l) (G18.setY l 17 ∪ {Sum.inl l})
        (G18.setY l 17)) y)))
      = callF (xOf 17) (yOf 17) (P4L.prodF f (P4L.fr (G18.basisA base l g t) (G18.incr l 17))) (P4L.prodF f (fun x => (P4L.fr (G18.basisA base l g t) {Sum.inl l} x)⁻¹)) (view f g t y) := by
  have dX := (G18.setX_succ l 17 (by norm_num)).2
  have dY := (G18.setY_succ l 17 (by norm_num)).2
  have dP := (G18.setX_pivot l 17 (by norm_num)).2
  have eP := G18.setX_eq l 17 (by norm_num)
  rw [eP] at dX
  exact view_call_fwd (17 : Fin 18) (G18.basisA base l) (G18.setY l 17) (G18.incr l 17) (Sum.inl l) dX dY dP (G18.wnK I l hH 17) f y g t

end Stages

end
end P16A8
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.P16A8.callSeg0
#print axioms OAI.PowerSaving.P16A8.callSeg1
#print axioms OAI.PowerSaving.P16A8.callSeg2
#print axioms OAI.PowerSaving.P16A8.callSeg3
#print axioms OAI.PowerSaving.P16A8.callSeg4
#print axioms OAI.PowerSaving.P16A8.callSeg5
#print axioms OAI.PowerSaving.P16A8.callSeg6
#print axioms OAI.PowerSaving.P16A8.callSeg7
#print axioms OAI.PowerSaving.P16A8.callSeg8
#print axioms OAI.PowerSaving.P16A8.callSeg9
#print axioms OAI.PowerSaving.P16A8.callSeg10
#print axioms OAI.PowerSaving.P16A8.callSeg11
#print axioms OAI.PowerSaving.P16A8.callSeg12
#print axioms OAI.PowerSaving.P16A8.callSeg13
#print axioms OAI.PowerSaving.P16A8.callSeg14
#print axioms OAI.PowerSaving.P16A8.callSeg15
#print axioms OAI.PowerSaving.P16A8.callSeg16
#print axioms OAI.PowerSaving.P16A8.callSeg17
