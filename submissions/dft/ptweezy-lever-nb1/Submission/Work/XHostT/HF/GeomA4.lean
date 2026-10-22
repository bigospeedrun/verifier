import Submission.Work.XHostD.HGeom
import Submission.Work.Mixed.HeadM1

/-!
# (key: heads-first) The head geometry: each A4 climb is ONE block of 48 lines of one frame, plus a free shift

On Shea's label space `LC (Fin 8) H l` (lg-a2a4's / p-a3's geometry `XHostD.x0_A4`, `x1_A4`, `hf_A4`), the idle climb
A4 of class `t`, side `s`, gauge `g` runs inside ONE orthonormal base, `A = BBC (base t) l g`, from the frame of the
lines `a4S0 l s` to the frame of the lines `a4S1 l s` (`a4S0 ⊆ a4S1`).  So (`OBase.frame_union`, `OBase.deltas_eq`)
`x1 = shift (A.corr d) * blockMat (A.fam d) * x0` with `d = a4Lines l s = a4S1 \ a4S0`, `|d| = 48`:
* `a4Dir`: the 48 head directions, the lines `d` of `A` in `A.fam` order (cast to `Fin 48`);
* `a4_head_geom`: `GReach (blockMat (a4Dir ..) * x0_A4 ..) (x1_A4 ..) 0` — what remains after the head block is a free
  shift (the `hz` hypothesis of `XNet.heads_first`).
For e-r45m1's `cut_heads_half`: the frame of head role `(ρ, s, t, g)` is `A = BBC (base t) l g`, its line set
`a4Lines l s`; `MX.bph_partA_fam A (a4Lines l s) (h : card = 24 + 24)` gives the 24 cut lines.
Written by p-hfirst (wht45/lever, 19 Oct 2026); the frames are Shea's (BridgeC/Stage.lean: classT_X0, classT_Y0,
classT_X, classT_Y) and Sussman's (Work/Block/Frames.lean); prepared with assistance from Claude.  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
namespace OAI
namespace PowerSaving
namespace XHostT
open Binary Matrix Finset RAM SS CB RF BR GF GX BC B401 XHost XHostR XHostD
noncomputable section

section GeomA4
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]

/-- the lines of the A4 start frame (side `s`). -/
def a4S0 (l : H) : Bool → Finset (BC.LC (Fin 8) H l)
  | false => JC {l} ∅
  | true => JC ∅ ∅

/-- the lines of the A4 end frame (side `s`). -/
def a4S1 (l : H) : Bool → Finset (BC.LC (Fin 8) H l)
  | false => JC univ (qC bs401_5)
  | true => JC (univ \ {l}) (qC bs401_5)

/-- **the 48 lines of a head** (side `s`): the lines the A4 climb adds. -/
def a4Lines (l : H) (s : Bool) : Finset (BC.LC (Fin 8) H l) := a4S1 l s \ a4S0 l s

lemma a4S0_sub (l : H) (s : Bool) : a4S0 l s ⊆ a4S1 l s := by
  cases s
  · exact Finset.disjSum_mono (Finset.subset_univ _) (Finset.empty_subset _)
  · exact Finset.disjSum_mono (Finset.empty_subset _) (Finset.empty_subset _)

lemma a4Lines_card (hH : Fintype.card H = 9) (l : H) (s : Bool) : (a4Lines l s).card = 48 := by
  have e1 := Finset.card_sdiff_add_card_eq_card (a4S0_sub l s)
  have e2 : 48 + (a4S0 l s).card = (a4S1 l s).card := by
    cases s
    · show 48 + (JC {l} ∅ : Finset (BC.LC (Fin 8) H l)).card = (JC univ (qC bs401_5)).card
      rw [card_JCX, card_JC, Finset.card_singleton, Finset.card_empty, card_bs401_5, hH]
    · show 48 + (JC ∅ ∅ : Finset (BC.LC (Fin 8) H l)).card = (JC (univ \ {l}) (qC bs401_5)).card
      rw [card_JCY, card_JC, Finset.card_empty, Finset.card_empty, card_bs401_5, hH]
  unfold a4Lines
  omega

/-- the frame of the head of class `t`, gauge `g`: Shea's base `BBC (base t) l g`. -/
def a4Base (base : T → OBase H) (l : H) (g : Orth (BC.LC (Fin 8) H l)) (t : T) : OBase (BC.LC (Fin 8) H l) :=
  BBC (base t) l g

/-- **the 48 head directions** of bin side `j.1`, class `j.2`, gauge `g`: the lines `a4Lines` of `a4Base`. -/
def a4Dir (base : T → OBase H) (l : H) (hH : Fintype.card H = 9) (g : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    Fin 48 → Space (BC.LC (Fin 8) H l) :=
  fun i => (a4Base base l g j.2).fam (a4Lines l j.1) (Fin.cast (a4Lines_card hH l j.1).symm i)

lemma a4Dir_indep (base : T → OBase H) (l : H) (hH : Fintype.card H = 9) (g : Orth (BC.LC (Fin 8) H l))
    (j : Bool × T) : LinearIndependent F (a4Dir base l hH g j) :=
  ((a4Base base l g j.2).fam_indep _).comp _ (Fin.cast_injective _)

lemma blockMat_a4Dir (base : T → OBase H) (l : H) (hH : Fintype.card H = 9) (g : Orth (BC.LC (Fin 8) H l))
    (j : Bool × T) : blockMat (a4Dir base l hH g j) = blockMat ((a4Base base l g j.2).fam (a4Lines l j.1)) :=
  MX.blockMat_congr _ _ (fun x => MX.bph_cast (a4Lines_card hH l j.1).symm ((a4Base base l g j.2).fam (a4Lines l j.1)) x)

variable (I : GInvE H T Sl C) (base : T → OBase H) (l : H)
variable (hbase : ∀ t, I.tv t = (base t).v l) (hH : Fintype.card H = 9)
include hbase

/-- the A4 start / end frames are the frames of `a4S0` / `a4S1` in `a4Base`. -/
lemma x0_A4_frame (g : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    x0_A4 I base l g j = frame (a4Base base l g j.2) (a4S0 l j.1) := by
  obtain ⟨s, t⟩ := j
  cases s
  · show PhiC g ∅ (tt (I.tv t)) = frame (BBC (base t) l g) (JC {l} ∅)
    rw [hbase t]; exact classT_X0 (base t) l g
  · exact classT_Y0 (base t) l g

lemma x1_A4_frame (g : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    x1_A4 I base l g j = frame (a4Base base l g j.2) (a4S1 l j.1) := by
  obtain ⟨s, t⟩ := j
  cases s
  · exact classT_X (base t) l bs401_5 (4 : Fin 8) (Finset.mem_insert_self _ _) g
  · show PhiC (RrC (base t) l (4 : Fin 8) g) (qC bs401_5) (1 + tt (I.tv t))
      = frame (BBC (base t) l g) (JC (univ \ {l}) (qC bs401_5))
    rw [hbase t]; exact classT_Y (base t) l bs401_5 (4 : Fin 8) (Finset.mem_insert_self _ _) g

/-- **the A4 climb is the head block and a free shift**: `x1 = shift c * blockMat (a4Dir ..) * x0`. -/
theorem a4_climb_eq (g : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    x1_A4 I base l g j = Binary.shift ((a4Base base l g j.2).corr (a4Lines l j.1))
      * (blockMat (a4Dir base l hH g j) * x0_A4 I base l g j) := by
  rw [x0_A4_frame I base l hbase, x1_A4_frame I base l hbase, blockMat_a4Dir, ← Matrix.mul_assoc,
    ← OBase.deltas_eq, a4Lines, ← OBase.frame_union _ _ _ Finset.disjoint_sdiff,
    Finset.union_sdiff_of_subset (a4S0_sub l j.1)]

/-- **the head geometry** (the `hz` hypothesis of `XNet.heads_first`): after the head block, the A4 end frame is
reached for free. -/
theorem a4_head_geom (g : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    GReach (blockMat (a4Dir base l hH g j) * x0_A4 I base l g j) (x1_A4 I base l g j) (fun _ => 0) := by
  rw [a4_climb_eq I base l hbase hH g j]
  exact fun ρ _ _ r => gstep_free (Free.shift _) r _

end GeomA4
end
end XHostT
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.XHostT.a4Lines_card
#print axioms OAI.PowerSaving.XHostT.a4Dir_indep
#print axioms OAI.PowerSaving.XHostT.a4_climb_eq
#print axioms OAI.PowerSaving.XHostT.a4_head_geom
