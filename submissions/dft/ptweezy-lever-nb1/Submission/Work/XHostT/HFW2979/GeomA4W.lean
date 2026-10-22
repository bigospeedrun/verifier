import Submission.Work.XHostT.TProvW
import Submission.Work.XHostT.HF.GeomA4

/-!
# (key: heads-first, warp) The A4 head geometry for the tv-parameterised frames of the warp network

p-hfirst's Work/XHostT/HF/GeomA4.lean with lg-a2a4's frames `x0_A4 I` / `x1_A4 I` replaced by p-a3's
tv-parameterised `x0t_A4 tv` / `x1t_A4 tv` (Work/XHostT/TProvW.lean, the frames of `xnetGeomW`): the A4 climb of
class `t`, side `s`, gauge `g` is ONE block of the 48 lines `a4Lines l s` of the frame `a4Base base l g t`, then a
free shift.  The lines, frames and directions (`a4Lines`, `a4Base`, `a4Dir`, `a4Dir_indep`, `blockMat_a4Dir`) are
p-hfirst's (imported).
Written by x-inst (wht45/lever2979, 19 Oct 2026) on p-hfirst's file; prepared with assistance from Claude.  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
namespace OAI
namespace PowerSaving
namespace XHostTW
open Binary Matrix Finset RAM SS CB RF BR GF GX BC B401 XHost XHostR XHostD XHostT
noncomputable section

section GeomA4W
variable {H T : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]

variable (tv : T → Space H) (base : T → OBase H) (l : H)
variable (hbase : ∀ t, tv t = (base t).v l) (hH : Fintype.card H = 9)
include hbase

/-- the A4 start / end frames are the frames of `a4S0` / `a4S1` in `a4Base`. -/
lemma x0t_A4_frame (g : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    x0t_A4 tv base l g j = frame (a4Base base l g j.2) (a4S0 l j.1) := by
  obtain ⟨s, t⟩ := j
  cases s
  · show PhiC g ∅ (tt (tv t)) = frame (BBC (base t) l g) (JC {l} ∅)
    rw [hbase t]; exact classT_X0 (base t) l g
  · exact classT_Y0 (base t) l g

lemma x1t_A4_frame (g : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    x1t_A4 tv base l g j = frame (a4Base base l g j.2) (a4S1 l j.1) := by
  obtain ⟨s, t⟩ := j
  cases s
  · exact classT_X (base t) l bs401_5 (4 : Fin 8) (Finset.mem_insert_self _ _) g
  · show PhiC (RrC (base t) l (4 : Fin 8) g) (qC bs401_5) (1 + tt (tv t))
      = frame (BBC (base t) l g) (JC (univ \ {l}) (qC bs401_5))
    rw [hbase t]; exact classT_Y (base t) l bs401_5 (4 : Fin 8) (Finset.mem_insert_self _ _) g

/-- **the A4 climb is the head block and a free shift** (tv frames). -/
theorem a4t_climb_eq (g : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    x1t_A4 tv base l g j = Binary.shift ((a4Base base l g j.2).corr (a4Lines l j.1))
      * (blockMat (a4Dir base l hH g j) * x0t_A4 tv base l g j) := by
  rw [x0t_A4_frame tv base l hbase, x1t_A4_frame tv base l hbase, blockMat_a4Dir, ← Matrix.mul_assoc,
    ← OBase.deltas_eq, a4Lines, ← OBase.frame_union _ _ _ Finset.disjoint_sdiff,
    Finset.union_sdiff_of_subset (a4S0_sub l j.1)]

/-- **the head geometry** (tv frames): after the head block the A4 end frame is reached for free. -/
theorem a4t_head_geom (g : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    GReach (blockMat (a4Dir base l hH g j) * x0t_A4 tv base l g j) (x1t_A4 tv base l g j) (fun _ => 0) := by
  rw [a4t_climb_eq tv base l hbase hH g j]
  exact fun ρ _ _ r => gstep_free (Free.shift _) r _

end GeomA4W
end
end XHostTW
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.XHostTW.a4t_climb_eq
#print axioms OAI.PowerSaving.XHostTW.a4t_head_geom
