import Submission.Work.XHostD.Merged1
import Submission.Work.XHostR.HSchedR
import Submission.Work.XHostD.HSchedD
import Submission.Work.Bridge401.End

/-!
# (key: bridge-host) The HOSTED nine-stage word on the label space `LC (Fin 8) H l` (geometry of Shea's GGeom)

Copy of the instance part of Work/Bridge401/GGeom.lean (Ryan Shea's complex588 tree; written by Nil Mamano's gen401.py
on jacklightChen's #377 geometry, Dugongue's #401 banks, Jacob Sussman's engine and stage geometry) for `GHost401`:

* `HostSchedR`: a host table `hostAt ρ` PER RUN (fsp-perrun; h-L3-build had the same table in every run; DaysSky's idle-axis hosting, PR #442), a bank map `bk` for
  the slots that are not hosted, the pads of the banks and the remainders `hrem` of the hosts; `HostSched.fits`: every
  bank's load plus pad is 73 (pad < 73), every host's load plus remainder is the rank of its idle climb.
* the bank frames and the host chains are ONE theorem, `XHost.host_frames` (h-L3-design's Frames.lean, after Shea's
  `bank_frames`): a bank is a host whose climb is `1 → kernel` (`hostForm_bank`), an idle climb inside one orthonormal
  basis has host form (`hostForm_frame`, from Sussman's `frame_core_free` / `core_nested`), and every gauged residual is
  `C * pk R * C'` (`entW_form`, Mamano / Shea).
* `ghostGeom`: the hosted network as a term of `GHost401`; `bridgeHost_gcert`: its `GCert`.
Written by h-L3-build/gen/gen_hgeom.py (wht43, 13 Oct 2026), prepared with assistance from Claude.  PER-RUN version (one host table per run) written by fsp-perrun/tools/mk_perrun.py (wht43, 14 Oct 2026) from h-L3-build's file by checked text substitution; prepared with assistance from Claude.  TWO-PROVIDER version (a per-call invocation `Ic ρ l` with the target vectors of `I`, per-call entrance labels and residuals) written by lg-a2a4/tools/mk_disp.py (wht43, 14 Oct 2026) from fsp-perrun's file by checked text substitution; prepared with assistance from Claude.  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
namespace OAI
namespace PowerSaving
namespace XHostD
open Binary Matrix Finset RAM SS CB RF BR GF GX BC B401 XHost XHostR
noncomputable section

/-- **The residual conditions** of a host schedule for the entrance labels `ent`. -/
def HostSchedR.fits {Sl T H : Type} [Fintype Sl] [DecidableEq Sl] [DecidableEq T] [Fintype H] (S : HostSchedR Sl T)
    (ent : Sl → SLbl H) : Prop :=
  S.fitsR (fun q => Fintype.card H - (ent q).dim)

/-- HostForm of a nested pair of index sets of one orthonormal basis, with the rank of the difference. -/
lemma hform_of {α : Type} [Fintype α] [DecidableEq α] (A : OBase α) {s t : Finset α} (h : s ⊆ t) (k : ℕ)
    (hk : k + s.card = t.card) : HostForm (frame A s) (frame A t) k := by
  have e : (t \ s).card = k := by
    have := Finset.card_sdiff_add_card_eq_card h
    omega
  rw [← e]
  exact hostForm_frame A h

/-! ## The idle climbs of the geometry have host form -/

section Geom
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]

/-- start and end frames of the idle climb A2. -/
def x0_A2 (I : GInvE H T Sl C) (base : T → OBase H) (l : H) (g : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    CMat (BC.LC (Fin 8) H l) :=
  match j with
  | (false, t) => PhiC g ∅ (tt (I.tv t))
  | (true, t) => PhiC g ∅ 0
def x1_A2 (I : GInvE H T Sl C) (base : T → OBase H) (l : H) (g : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    CMat (BC.LC (Fin 8) H l) :=
  match j with
  | (false, t) => PhiC (RrC (base t) l (0 : Fin 8) g) (qC bs401_1) 1
  | (true, t) => PhiC (RrC (base t) l (0 : Fin 8) g) (qC bs401_1) (1 + tt (I.tv t))

/-- start and end frames of the idle climb B2. -/
def x0_B2 (I : GInvE H T Sl C) (base : T → OBase H) (l : H) (g : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    CMat (BC.LC (Fin 8) H l) :=
  match j with
  | (false, t) => PhiC (RrC (base t) l (1 : Fin 8) g) (qC bs401_2) (tt (I.tv t))
  | (true, t) => PhiC (RrC (base t) l (1 : Fin 8) g) (qC bs401_2) 0
def x1_B2 (I : GInvE H T Sl C) (base : T → OBase H) (l : H) (g : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    CMat (BC.LC (Fin 8) H l) :=
  match j with
  | (false, t) => PhiC (RrC (base t) l (1 : Fin 8) g) (qC bs401_2) 1
  | (true, t) => PhiC (RrC (base t) l (1 : Fin 8) g) (qC bs401_2) (1 + tt (I.tv t))

/-- start and end frames of the idle climb A3. -/
def x0_A3 (I : GInvE H T Sl C) (base : T → OBase H) (l : H) (g : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    CMat (BC.LC (Fin 8) H l) :=
  match j with
  | (false, t) => PhiC g ∅ (tt (I.tv t))
  | (true, t) => PhiC g ∅ 0
def x1_A3 (I : GInvE H T Sl C) (base : T → OBase H) (l : H) (g : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    CMat (BC.LC (Fin 8) H l) :=
  match j with
  | (false, t) => PhiC (RrC (base t) l (2 : Fin 8) g) (qC bs401_3) 1
  | (true, t) => PhiC (RrC (base t) l (2 : Fin 8) g) (qC bs401_3) (1 + tt (I.tv t))

/-- start and end frames of the idle climb B3. -/
def x0_B3 (I : GInvE H T Sl C) (base : T → OBase H) (l : H) (g : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    CMat (BC.LC (Fin 8) H l) :=
  match j with
  | (false, t) => PhiC (RrC (base t) l (3 : Fin 8) g) (qC bs401_4) (tt (I.tv t))
  | (true, t) => PhiC (RrC (base t) l (3 : Fin 8) g) (qC bs401_4) 0
def x1_B3 (I : GInvE H T Sl C) (base : T → OBase H) (l : H) (g : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    CMat (BC.LC (Fin 8) H l) :=
  match j with
  | (false, t) => PhiC (RrC (base t) l (3 : Fin 8) g) (qC bs401_4) 1
  | (true, t) => PhiC (RrC (base t) l (3 : Fin 8) g) (qC bs401_4) (1 + tt (I.tv t))

/-- start and end frames of the idle climb A4. -/
def x0_A4 (I : GInvE H T Sl C) (base : T → OBase H) (l : H) (g : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    CMat (BC.LC (Fin 8) H l) :=
  match j with
  | (false, t) => PhiC g ∅ (tt (I.tv t))
  | (true, t) => PhiC g ∅ 0
def x1_A4 (I : GInvE H T Sl C) (base : T → OBase H) (l : H) (g : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    CMat (BC.LC (Fin 8) H l) :=
  match j with
  | (false, t) => PhiC (RrC (base t) l (4 : Fin 8) g) (qC bs401_5) 1
  | (true, t) => PhiC (RrC (base t) l (4 : Fin 8) g) (qC bs401_5) (1 + tt (I.tv t))

/-- start and end frames of the idle climb B4. -/
def x0_B4 (I : GInvE H T Sl C) (base : T → OBase H) (l : H) (g : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    CMat (BC.LC (Fin 8) H l) :=
  match j with
  | (false, t) => PhiC (RrC (base t) l (5 : Fin 8) g) (qC bs401_6) (tt (I.tv t))
  | (true, t) => PhiC (RrC (base t) l (5 : Fin 8) g) (qC bs401_6) 0
def x1_B4 (I : GInvE H T Sl C) (base : T → OBase H) (l : H) (g : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    CMat (BC.LC (Fin 8) H l) :=
  match j with
  | (false, t) => PhiC (RrC (base t) l (5 : Fin 8) g) (qC bs401_6) 1
  | (true, t) => PhiC (RrC (base t) l (5 : Fin 8) g) (qC bs401_6) (1 + tt (I.tv t))

/-- start and end frames of the idle climb F1. -/
def x0_F1 (I : GInvE H T Sl C) (base : T → OBase H) (l : H) (g : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    CMat (BC.LC (Fin 8) H l) :=
  match j with
  | (false, t) => PhiC (RrC (base t) l (1 : Fin 8) g) (qC bs401_2) 1
  | (true, t) => PhiC (RrC (base t) l (1 : Fin 8) g) (qC bs401_2) (1 + tt (I.tv t))
def x1_F1 (I : GInvE H T Sl C) (base : T → OBase H) (l : H) (g : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    CMat (BC.LC (Fin 8) H l) :=
  match j with
  | (false, t) => kernel (BC.LC (Fin 8) H l)
  | (true, t) => frame (BBC (base t) l g) (univ \ {Sum.inl l})

/-- start and end frames of the idle climb F2. -/
def x0_F2 (I : GInvE H T Sl C) (base : T → OBase H) (l : H) (g : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    CMat (BC.LC (Fin 8) H l) :=
  match j with
  | (false, t) => PhiC (RrC (base t) l (3 : Fin 8) g) (qC bs401_4) 1
  | (true, t) => PhiC (RrC (base t) l (3 : Fin 8) g) (qC bs401_4) (1 + tt (I.tv t))
def x1_F2 (I : GInvE H T Sl C) (base : T → OBase H) (l : H) (g : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    CMat (BC.LC (Fin 8) H l) :=
  match j with
  | (false, t) => kernel (BC.LC (Fin 8) H l)
  | (true, t) => frame (BBC (base t) l g) (univ \ {Sum.inl l})

/-- start and end frames of the idle climb F3. -/
def x0_F3 (I : GInvE H T Sl C) (base : T → OBase H) (l : H) (g : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    CMat (BC.LC (Fin 8) H l) :=
  match j with
  | (false, t) => PhiC (RrC (base t) l (5 : Fin 8) g) (qC bs401_6) 1
  | (true, t) => PhiC (RrC (base t) l (5 : Fin 8) g) (qC bs401_6) (1 + tt (I.tv t))
def x1_F3 (I : GInvE H T Sl C) (base : T → OBase H) (l : H) (g : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    CMat (BC.LC (Fin 8) H l) :=
  match j with
  | (false, t) => kernel (BC.LC (Fin 8) H l)
  | (true, t) => frame (BBC (base t) l g) (univ \ {Sum.inl l})

variable (I : GInvE H T Sl C) (base : T → OBase H) (l : H)
variable (hbase : ∀ t, I.tv t = (base t).v l) (hH : Fintype.card H = 9)
include hbase hH

/-- host form of the idle climb A2 (rank 16), both sides. -/
lemma hf_A2 (g : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    HostForm (x0_A2 I base l g j) (x1_A2 I base l g j) 16 := by
  obtain ⟨s, t⟩ := j
  cases s
  · show HostForm (PhiC g ∅ (tt (I.tv t))) (PhiC (RrC (base t) l (0 : Fin 8) g) (qC bs401_1) 1) 16
    have e0 : PhiC g ∅ (tt (I.tv t)) = frame (BBC (base t) l g) (JC {l} ∅) := by
      rw [hbase t]; exact classT_X0 (base t) l g
    have e1 : PhiC (RrC (base t) l (0 : Fin 8) g) (qC bs401_1) 1 = frame (BBC (base t) l g) (JC univ (qC bs401_1)) :=
      classT_X (base t) l bs401_1 (0 : Fin 8) (Finset.mem_singleton_self _) g
    rw [e0, e1]
    refine hform_of _ (Finset.disjSum_mono (Finset.subset_univ _) (Finset.empty_subset _)) 16 ?_
    rw [card_JCX, card_JC, Finset.card_singleton, Finset.card_empty, card_bs401_1, hH]
  · show HostForm (PhiC g ∅ 0) (PhiC (RrC (base t) l (0 : Fin 8) g) (qC bs401_1) (1 + tt (I.tv t))) 16
    have e0 : PhiC g ∅ 0 = frame (BBC (base t) l g) (JC ∅ ∅) := classT_Y0 (base t) l g
    have e1 : PhiC (RrC (base t) l (0 : Fin 8) g) (qC bs401_1) (1 + tt (I.tv t)) = frame (BBC (base t) l g) (JC (univ \ {l}) (qC bs401_1)) := by
      rw [hbase t]; exact classT_Y (base t) l bs401_1 (0 : Fin 8) (Finset.mem_singleton_self _) g
    rw [e0, e1]
    refine hform_of _ (Finset.disjSum_mono (Finset.empty_subset _) (Finset.empty_subset _)) 16 ?_
    rw [card_JCY, card_JC, Finset.card_empty, Finset.card_empty, card_bs401_1, hH]

/-- host form of the idle climb B2 (rank 8), both sides. -/
lemma hf_B2 (g : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    HostForm (x0_B2 I base l g j) (x1_B2 I base l g j) 8 := by
  obtain ⟨s, t⟩ := j
  cases s
  · show HostForm (PhiC (RrC (base t) l (1 : Fin 8) g) (qC bs401_2) (tt (I.tv t))) (PhiC (RrC (base t) l (1 : Fin 8) g) (qC bs401_2) 1) 8
    have e0 : PhiC (RrC (base t) l (1 : Fin 8) g) (qC bs401_2) (tt (I.tv t)) = frame (BBC (base t) l g) (JC univ (qC bs401_1)) :=
      (g401geom_xx I base l hbase bs401_1 (0 : Fin 8) (1 : Fin 8) (Finset.mem_singleton_self _) mem401_1 g t).symm.trans
        (classT_X (base t) l bs401_1 (0 : Fin 8) (Finset.mem_singleton_self _) g)
    have e1 : PhiC (RrC (base t) l (1 : Fin 8) g) (qC bs401_2) 1 = frame (BBC (base t) l g) (JC univ (qC bs401_2)) :=
      classT_X (base t) l bs401_2 (1 : Fin 8) (Finset.mem_insert_self _ _) g
    rw [e0, e1]
    refine hform_of _ (Finset.disjSum_mono (Finset.Subset.refl _) (qC_mono (Finset.subset_insert _ _))) 8 ?_
    rw [card_JCX, card_JCX, card_bs401_1, card_bs401_2, hH]
  · show HostForm (PhiC (RrC (base t) l (1 : Fin 8) g) (qC bs401_2) 0) (PhiC (RrC (base t) l (1 : Fin 8) g) (qC bs401_2) (1 + tt (I.tv t))) 8
    have e0 : PhiC (RrC (base t) l (1 : Fin 8) g) (qC bs401_2) 0 = frame (BBC (base t) l g) (JC (univ \ {l}) (qC bs401_1)) :=
      (g401geom_yy I base l hbase bs401_1 (0 : Fin 8) (1 : Fin 8) (Finset.mem_singleton_self _) mem401_1 g t).symm.trans
        (by rw [hbase t]; exact classT_Y (base t) l bs401_1 (0 : Fin 8) (Finset.mem_singleton_self _) g)
    have e1 : PhiC (RrC (base t) l (1 : Fin 8) g) (qC bs401_2) (1 + tt (I.tv t)) = frame (BBC (base t) l g) (JC (univ \ {l}) (qC bs401_2)) := by
      rw [hbase t]; exact classT_Y (base t) l bs401_2 (1 : Fin 8) (Finset.mem_insert_self _ _) g
    rw [e0, e1]
    refine hform_of _ (Finset.disjSum_mono (Finset.Subset.refl _) (qC_mono (Finset.subset_insert _ _))) 8 ?_
    rw [card_JCY, card_JCY, card_bs401_1, card_bs401_2, hH]

/-- host form of the idle climb A3 (rank 32), both sides. -/
lemma hf_A3 (g : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    HostForm (x0_A3 I base l g j) (x1_A3 I base l g j) 32 := by
  obtain ⟨s, t⟩ := j
  cases s
  · show HostForm (PhiC g ∅ (tt (I.tv t))) (PhiC (RrC (base t) l (2 : Fin 8) g) (qC bs401_3) 1) 32
    have e0 : PhiC g ∅ (tt (I.tv t)) = frame (BBC (base t) l g) (JC {l} ∅) := by
      rw [hbase t]; exact classT_X0 (base t) l g
    have e1 : PhiC (RrC (base t) l (2 : Fin 8) g) (qC bs401_3) 1 = frame (BBC (base t) l g) (JC univ (qC bs401_3)) :=
      classT_X (base t) l bs401_3 (2 : Fin 8) (Finset.mem_insert_self _ _) g
    rw [e0, e1]
    refine hform_of _ (Finset.disjSum_mono (Finset.subset_univ _) (Finset.empty_subset _)) 32 ?_
    rw [card_JCX, card_JC, Finset.card_singleton, Finset.card_empty, card_bs401_3, hH]
  · show HostForm (PhiC g ∅ 0) (PhiC (RrC (base t) l (2 : Fin 8) g) (qC bs401_3) (1 + tt (I.tv t))) 32
    have e0 : PhiC g ∅ 0 = frame (BBC (base t) l g) (JC ∅ ∅) := classT_Y0 (base t) l g
    have e1 : PhiC (RrC (base t) l (2 : Fin 8) g) (qC bs401_3) (1 + tt (I.tv t)) = frame (BBC (base t) l g) (JC (univ \ {l}) (qC bs401_3)) := by
      rw [hbase t]; exact classT_Y (base t) l bs401_3 (2 : Fin 8) (Finset.mem_insert_self _ _) g
    rw [e0, e1]
    refine hform_of _ (Finset.disjSum_mono (Finset.empty_subset _) (Finset.empty_subset _)) 32 ?_
    rw [card_JCY, card_JC, Finset.card_empty, Finset.card_empty, card_bs401_3, hH]

/-- host form of the idle climb B3 (rank 8), both sides. -/
lemma hf_B3 (g : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    HostForm (x0_B3 I base l g j) (x1_B3 I base l g j) 8 := by
  obtain ⟨s, t⟩ := j
  cases s
  · show HostForm (PhiC (RrC (base t) l (3 : Fin 8) g) (qC bs401_4) (tt (I.tv t))) (PhiC (RrC (base t) l (3 : Fin 8) g) (qC bs401_4) 1) 8
    have e0 : PhiC (RrC (base t) l (3 : Fin 8) g) (qC bs401_4) (tt (I.tv t)) = frame (BBC (base t) l g) (JC univ (qC bs401_3)) :=
      (g401geom_xx I base l hbase bs401_3 (2 : Fin 8) (3 : Fin 8) (Finset.mem_insert_self _ _) mem401_3 g t).symm.trans
        (classT_X (base t) l bs401_3 (2 : Fin 8) (Finset.mem_insert_self _ _) g)
    have e1 : PhiC (RrC (base t) l (3 : Fin 8) g) (qC bs401_4) 1 = frame (BBC (base t) l g) (JC univ (qC bs401_4)) :=
      classT_X (base t) l bs401_4 (3 : Fin 8) (Finset.mem_insert_self _ _) g
    rw [e0, e1]
    refine hform_of _ (Finset.disjSum_mono (Finset.Subset.refl _) (qC_mono (Finset.subset_insert _ _))) 8 ?_
    rw [card_JCX, card_JCX, card_bs401_3, card_bs401_4, hH]
  · show HostForm (PhiC (RrC (base t) l (3 : Fin 8) g) (qC bs401_4) 0) (PhiC (RrC (base t) l (3 : Fin 8) g) (qC bs401_4) (1 + tt (I.tv t))) 8
    have e0 : PhiC (RrC (base t) l (3 : Fin 8) g) (qC bs401_4) 0 = frame (BBC (base t) l g) (JC (univ \ {l}) (qC bs401_3)) :=
      (g401geom_yy I base l hbase bs401_3 (2 : Fin 8) (3 : Fin 8) (Finset.mem_insert_self _ _) mem401_3 g t).symm.trans
        (by rw [hbase t]; exact classT_Y (base t) l bs401_3 (2 : Fin 8) (Finset.mem_insert_self _ _) g)
    have e1 : PhiC (RrC (base t) l (3 : Fin 8) g) (qC bs401_4) (1 + tt (I.tv t)) = frame (BBC (base t) l g) (JC (univ \ {l}) (qC bs401_4)) := by
      rw [hbase t]; exact classT_Y (base t) l bs401_4 (3 : Fin 8) (Finset.mem_insert_self _ _) g
    rw [e0, e1]
    refine hform_of _ (Finset.disjSum_mono (Finset.Subset.refl _) (qC_mono (Finset.subset_insert _ _))) 8 ?_
    rw [card_JCY, card_JCY, card_bs401_3, card_bs401_4, hH]

/-- host form of the idle climb A4 (rank 48), both sides. -/
lemma hf_A4 (g : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    HostForm (x0_A4 I base l g j) (x1_A4 I base l g j) 48 := by
  obtain ⟨s, t⟩ := j
  cases s
  · show HostForm (PhiC g ∅ (tt (I.tv t))) (PhiC (RrC (base t) l (4 : Fin 8) g) (qC bs401_5) 1) 48
    have e0 : PhiC g ∅ (tt (I.tv t)) = frame (BBC (base t) l g) (JC {l} ∅) := by
      rw [hbase t]; exact classT_X0 (base t) l g
    have e1 : PhiC (RrC (base t) l (4 : Fin 8) g) (qC bs401_5) 1 = frame (BBC (base t) l g) (JC univ (qC bs401_5)) :=
      classT_X (base t) l bs401_5 (4 : Fin 8) (Finset.mem_insert_self _ _) g
    rw [e0, e1]
    refine hform_of _ (Finset.disjSum_mono (Finset.subset_univ _) (Finset.empty_subset _)) 48 ?_
    rw [card_JCX, card_JC, Finset.card_singleton, Finset.card_empty, card_bs401_5, hH]
  · show HostForm (PhiC g ∅ 0) (PhiC (RrC (base t) l (4 : Fin 8) g) (qC bs401_5) (1 + tt (I.tv t))) 48
    have e0 : PhiC g ∅ 0 = frame (BBC (base t) l g) (JC ∅ ∅) := classT_Y0 (base t) l g
    have e1 : PhiC (RrC (base t) l (4 : Fin 8) g) (qC bs401_5) (1 + tt (I.tv t)) = frame (BBC (base t) l g) (JC (univ \ {l}) (qC bs401_5)) := by
      rw [hbase t]; exact classT_Y (base t) l bs401_5 (4 : Fin 8) (Finset.mem_insert_self _ _) g
    rw [e0, e1]
    refine hform_of _ (Finset.disjSum_mono (Finset.empty_subset _) (Finset.empty_subset _)) 48 ?_
    rw [card_JCY, card_JC, Finset.card_empty, Finset.card_empty, card_bs401_5, hH]

/-- host form of the idle climb B4 (rank 8), both sides. -/
lemma hf_B4 (g : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    HostForm (x0_B4 I base l g j) (x1_B4 I base l g j) 8 := by
  obtain ⟨s, t⟩ := j
  cases s
  · show HostForm (PhiC (RrC (base t) l (5 : Fin 8) g) (qC bs401_6) (tt (I.tv t))) (PhiC (RrC (base t) l (5 : Fin 8) g) (qC bs401_6) 1) 8
    have e0 : PhiC (RrC (base t) l (5 : Fin 8) g) (qC bs401_6) (tt (I.tv t)) = frame (BBC (base t) l g) (JC univ (qC bs401_5)) :=
      (g401geom_xx I base l hbase bs401_5 (4 : Fin 8) (5 : Fin 8) (Finset.mem_insert_self _ _) mem401_5 g t).symm.trans
        (classT_X (base t) l bs401_5 (4 : Fin 8) (Finset.mem_insert_self _ _) g)
    have e1 : PhiC (RrC (base t) l (5 : Fin 8) g) (qC bs401_6) 1 = frame (BBC (base t) l g) (JC univ (qC bs401_6)) :=
      classT_X (base t) l bs401_6 (5 : Fin 8) (Finset.mem_insert_self _ _) g
    rw [e0, e1]
    refine hform_of _ (Finset.disjSum_mono (Finset.Subset.refl _) (qC_mono (Finset.subset_insert _ _))) 8 ?_
    rw [card_JCX, card_JCX, card_bs401_5, card_bs401_6, hH]
  · show HostForm (PhiC (RrC (base t) l (5 : Fin 8) g) (qC bs401_6) 0) (PhiC (RrC (base t) l (5 : Fin 8) g) (qC bs401_6) (1 + tt (I.tv t))) 8
    have e0 : PhiC (RrC (base t) l (5 : Fin 8) g) (qC bs401_6) 0 = frame (BBC (base t) l g) (JC (univ \ {l}) (qC bs401_5)) :=
      (g401geom_yy I base l hbase bs401_5 (4 : Fin 8) (5 : Fin 8) (Finset.mem_insert_self _ _) mem401_5 g t).symm.trans
        (by rw [hbase t]; exact classT_Y (base t) l bs401_5 (4 : Fin 8) (Finset.mem_insert_self _ _) g)
    have e1 : PhiC (RrC (base t) l (5 : Fin 8) g) (qC bs401_6) (1 + tt (I.tv t)) = frame (BBC (base t) l g) (JC (univ \ {l}) (qC bs401_6)) := by
      rw [hbase t]; exact classT_Y (base t) l bs401_6 (5 : Fin 8) (Finset.mem_insert_self _ _) g
    rw [e0, e1]
    refine hform_of _ (Finset.disjSum_mono (Finset.Subset.refl _) (qC_mono (Finset.subset_insert _ _))) 8 ?_
    rw [card_JCY, card_JCY, card_bs401_5, card_bs401_6, hH]

/-- host form of the idle climb F1 (rank 48), both sides. -/
lemma hf_F1 (g : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    HostForm (x0_F1 I base l g j) (x1_F1 I base l g j) 48 := by
  obtain ⟨s, t⟩ := j
  cases s
  · show HostForm (PhiC (RrC (base t) l (1 : Fin 8) g) (qC bs401_2) 1) (kernel (BC.LC (Fin 8) H l)) 48
    have e0 : PhiC (RrC (base t) l (1 : Fin 8) g) (qC bs401_2) 1 = frame (BBC (base t) l g) (JC univ (qC bs401_2)) :=
      classT_X (base t) l bs401_2 (1 : Fin 8) (Finset.mem_insert_self _ _) g
    rw [e0, ← frame_univ (BBC (base t) l g)]
    refine hform_of _ (Finset.subset_univ _) 48 ?_
    rw [card_JCX, card_univ_LC, card_bs401_2, hH, Fintype.card_fin]
  · show HostForm (PhiC (RrC (base t) l (1 : Fin 8) g) (qC bs401_2) (1 + tt (I.tv t))) (frame (BBC (base t) l g) (univ \ {Sum.inl l})) 48
    have e0 : PhiC (RrC (base t) l (1 : Fin 8) g) (qC bs401_2) (1 + tt (I.tv t)) = frame (BBC (base t) l g) (JC (univ \ {l}) (qC bs401_2)) := by
      rw [hbase t]; exact classT_Y (base t) l bs401_2 (1 : Fin 8) (Finset.mem_insert_self _ _) g
    rw [e0]
    refine hform_of _ (JCY_sub l _) 48 ?_
    rw [card_JCY, Finset.card_sdiff_of_subset (Finset.subset_univ _), card_univ_LC, Finset.card_singleton,
      card_bs401_2, hH, Fintype.card_fin]

/-- host form of the idle climb F2 (rank 32), both sides. -/
lemma hf_F2 (g : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    HostForm (x0_F2 I base l g j) (x1_F2 I base l g j) 32 := by
  obtain ⟨s, t⟩ := j
  cases s
  · show HostForm (PhiC (RrC (base t) l (3 : Fin 8) g) (qC bs401_4) 1) (kernel (BC.LC (Fin 8) H l)) 32
    have e0 : PhiC (RrC (base t) l (3 : Fin 8) g) (qC bs401_4) 1 = frame (BBC (base t) l g) (JC univ (qC bs401_4)) :=
      classT_X (base t) l bs401_4 (3 : Fin 8) (Finset.mem_insert_self _ _) g
    rw [e0, ← frame_univ (BBC (base t) l g)]
    refine hform_of _ (Finset.subset_univ _) 32 ?_
    rw [card_JCX, card_univ_LC, card_bs401_4, hH, Fintype.card_fin]
  · show HostForm (PhiC (RrC (base t) l (3 : Fin 8) g) (qC bs401_4) (1 + tt (I.tv t))) (frame (BBC (base t) l g) (univ \ {Sum.inl l})) 32
    have e0 : PhiC (RrC (base t) l (3 : Fin 8) g) (qC bs401_4) (1 + tt (I.tv t)) = frame (BBC (base t) l g) (JC (univ \ {l}) (qC bs401_4)) := by
      rw [hbase t]; exact classT_Y (base t) l bs401_4 (3 : Fin 8) (Finset.mem_insert_self _ _) g
    rw [e0]
    refine hform_of _ (JCY_sub l _) 32 ?_
    rw [card_JCY, Finset.card_sdiff_of_subset (Finset.subset_univ _), card_univ_LC, Finset.card_singleton,
      card_bs401_4, hH, Fintype.card_fin]

/-- host form of the idle climb F3 (rank 16), both sides. -/
lemma hf_F3 (g : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    HostForm (x0_F3 I base l g j) (x1_F3 I base l g j) 16 := by
  obtain ⟨s, t⟩ := j
  cases s
  · show HostForm (PhiC (RrC (base t) l (5 : Fin 8) g) (qC bs401_6) 1) (kernel (BC.LC (Fin 8) H l)) 16
    have e0 : PhiC (RrC (base t) l (5 : Fin 8) g) (qC bs401_6) 1 = frame (BBC (base t) l g) (JC univ (qC bs401_6)) :=
      classT_X (base t) l bs401_6 (5 : Fin 8) (Finset.mem_insert_self _ _) g
    rw [e0, ← frame_univ (BBC (base t) l g)]
    refine hform_of _ (Finset.subset_univ _) 16 ?_
    rw [card_JCX, card_univ_LC, card_bs401_6, hH, Fintype.card_fin]
  · show HostForm (PhiC (RrC (base t) l (5 : Fin 8) g) (qC bs401_6) (1 + tt (I.tv t))) (frame (BBC (base t) l g) (univ \ {Sum.inl l})) 16
    have e0 : PhiC (RrC (base t) l (5 : Fin 8) g) (qC bs401_6) (1 + tt (I.tv t)) = frame (BBC (base t) l g) (JC (univ \ {l}) (qC bs401_6)) := by
      rw [hbase t]; exact classT_Y (base t) l bs401_6 (5 : Fin 8) (Finset.mem_insert_self _ _) g
    rw [e0]
    refine hform_of _ (JCY_sub l _) 16 ?_
    rw [card_JCY, Finset.card_sdiff_of_subset (Finset.subset_univ _), card_univ_LC, Finset.card_singleton,
      card_bs401_6, hH, Fintype.card_fin]

end Geom

/-! ## Per-call entrance labels (two-provider dispatch) -/

section Ent
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]

/-- the entrance label of slot `q` in sub-stage `k = 9 ρ + l`: that of the call's own invocation. -/
def entK (Ic : Fin 8 → Fin 9 → GInvE H T Sl C) (k : ℕ) (q : Sl) : SLbl H :=
  (Ic ⟨k / 9 % 8, Nat.mod_lt _ (by norm_num)⟩ ⟨k % 9, Nat.mod_lt _ (by norm_num)⟩).ent q

/-- the residual of slot `q` in sub-stage `k`. -/
def rK (Ic : Fin 8 → Fin 9 → GInvE H T Sl C) (k : ℕ) (q : Sl) : ℕ := Fintype.card H - (entK Ic k q).dim

lemma entK_eq (Ic : Fin 8 → Fin 9 → GInvE H T Sl C) (ρ : Fin 8) (l : ℕ) (hl : l < 9) (q : Sl) :
    entK Ic (9 * ρ.val + l) q = (Ic ρ ⟨l, hl⟩).ent q := by
  unfold entK
  have h1 : (⟨(9 * ρ.val + l) / 9 % 8, Nat.mod_lt _ (by norm_num)⟩ : Fin 8) = ρ := by
    apply Fin.ext
    show (9 * ρ.val + l) / 9 % 8 = ρ.val
    have := ρ.isLt
    omega
  have h2 : (⟨(9 * ρ.val + l) % 9, Nat.mod_lt _ (by norm_num)⟩ : Fin 9) = ⟨l, hl⟩ := by
    apply Fin.ext
    show (9 * ρ.val + l) % 9 = l
    omega
  rw [h1, h2]

/-- with one invocation in every call, `rK` is the old residual. -/
lemma rK_const (I : GInvE H T Sl C) : rK (fun _ _ => I) = fun _ q => Fintype.card H - (I.ent q).dim := rfl

end Ent

/-! ## The hosted network on `LC (Fin 8) H l` -/

section Net
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]
variable (I : GInvE H T Sl C) (Ic : Fin 8 → Fin 9 → GInvE H T Sl C) (hIc : ∀ ρ l, (Ic ρ l).tv = I.tv)
  (base : T → OBase H) (l : H)
  (hbase : ∀ t, I.tv t = (base t).v l) (hH : Fintype.card H = 9) (S : HostSchedR Sl T) (hfit : fitsRK S (rK Ic))

lemma hWnK (ρ : Fin 8) (k0 : ℕ) : ∀ k : ℕ, ∀ d q, ∃ (C C' : CMat (BC.LC (Fin 8) H l)) (R : Finset (BC.LC (Fin 8) H l)),
    Free C ∧ Free C' ∧ R.card = rK Ic (9 * ρ.val + (k0 + k)) q ∧
      entW (win401N l hH (k0 + k) d).X (entK Ic (9 * ρ.val + (k0 + k)) q) = C * pk R * C' :=
  fun k d q => entW_form _ _

lemma hWnB : ∀ k : ℕ, ∀ d q, ∃ (C C' : CMat (BC.LC (Fin 8) H l)) (R : Finset (BC.LC (Fin 8) H l)),
    Free C ∧ Free C' ∧ R.card = rK Ic k q ∧ entW (win401N l hH (k % 9) d).X (entK Ic k q) = C * pk R * C' :=
  fun k d q => entW_form _ _

include hbase hfit in
/-- the bank frames (`host_frames` with the banks as hosts of the climb `1 → kernel`). -/
lemma bank_ex : ∃ (Zb Zp : ℕ → Orth (BC.LC (Fin 8) H l) → Fin S.nb → CMat (BC.LC (Fin 8) H l)),
      (∀ d j, Zb 0 d j = 1) ∧
      (∀ k < 72, ∀ d j, GReach (Zb k d j) (Zp k d j) (fun _ => 0)) ∧
      (∀ k < 72, ∀ d q j, bUseR S.hostAt S.bk k q = some j →
        entW (win401N l hH (k % 9) d).X (entK Ic k q) * Zp k d j = Zb (k + 1) d j) ∧
      (∀ k < 72, ∀ d j, (∀ q, bUseR S.hostAt S.bk k q ≠ some j) → Zb (k + 1) d j = Zp k d j) ∧
      (∀ d j, GReach (Zb 72 d j) (kernel (BC.LC (Fin 8) H l)) (fun φ => bcost φ (S.pad j))) := by
  have hc : Fintype.card (BC.LC (Fin 8) H l) = 73 := card_LC401 l hH
  obtain ⟨Zb, Zp, h0, hP, hU, hN, hE⟩ := host_framesK (bUseR S.hostAt S.bk) (rK Ic)
    (fun k d q => entW (win401N l hH (k % 9) d).X (entK Ic k q)) 72
    (fun k hk => bUseR_one S.hostAt S.bk S.hinj k hk) (fun k _ => hWnB Ic l hH k)
    (fun _ _ => (1 : CMat (BC.LC (Fin 8) H l))) (fun _ _ => kernel (BC.LC (Fin 8) H l)) (fun _ => 73)
    (fun _ _ => by rw [← hc]; exact hostForm_bank)
    (fun j => by show LHK _ _ 72 j ≤ 73; have := hfit.1 j; omega)
    (fun j => by show 73 - LHK _ _ 72 j < _; rw [hc]; have := hfit.1 j; have := hfit.2.1 j; omega)
  refine ⟨Zb, Zp, h0, hP, hU, hN, fun d j => ?_⟩
  have e : 73 - LHK (bUseR S.hostAt S.bk) (rK Ic) 72 j = S.pad j := by have := hfit.1 j; omega
  have h : GReach (Zb 72 d j) (kernel (BC.LC (Fin 8) H l))
      (fun φ => bcost φ (73 - LHK (bUseR S.hostAt S.bk) (rK Ic) 72 j)) := hE d j
  rw [e] at h
  exact h

def zbH := Classical.choose (bank_ex I Ic base l hbase hH S hfit)
def zpH := Classical.choose (Classical.choose_spec (bank_ex I Ic base l hbase hH S hfit))
def zH_spec := Classical.choose_spec (Classical.choose_spec (bank_ex I Ic base l hbase hH S hfit))

include hbase hfit in
/-- the host chains of the idle climb A2 (window: stages 0..1, rank 16). -/
lemma chain_ex_A2 (ρ : Fin 8) : ∃ (Zb Zp : ℕ → Orth (BC.LC (Fin 8) H l) → Bool × T → CMat (BC.LC (Fin 8) H l)),
      (∀ d j, Zb 0 d j = x0_A2 I base l d j) ∧
      (∀ k < 2, ∀ d j, GReach (Zb k d j) (Zp k d j) (fun _ => 0)) ∧
      (∀ k < 2, ∀ d q j, hUse (S.hostAt ρ) 0 0 k q = some j →
        entW (win401N l hH (0 + k) d).X (entK Ic (9 * ρ.val + (0 + k)) q) * Zp k d j = Zb (k + 1) d j) ∧
      (∀ k < 2, ∀ d j, (∀ q, hUse (S.hostAt ρ) 0 0 k q ≠ some j) → Zb (k + 1) d j = Zp k d j) ∧
      (∀ d j, GReach (Zb 2 d j) (x1_A2 I base l d j) (fun φ => bcost φ (S.hrem ρ 0 j))) := by
  have hc : Fintype.card (BC.LC (Fin 8) H l) = 73 := card_LC401 l hH
  have hf : ∀ j, LHK (hUse (S.hostAt ρ) 0 0) (fun k q => rK Ic (9 * ρ.val + (0 + k)) q) 2 j + S.hrem ρ 0 j = 16 := fun j => hfit.2.2 ρ 0 j
  obtain ⟨Zb, Zp, h0, hP, hU, hN, hE⟩ := host_framesK (hUse (S.hostAt ρ) 0 0) (fun k q => rK Ic (9 * ρ.val + (0 + k)) q)
    (fun k d q => entW (win401N l hH (0 + k) d).X (entK Ic (9 * ρ.val + (0 + k)) q)) 2
    (fun k _ => hUse_one (S.hostAt ρ) (S.hostInj ρ) 0 0 k) (fun k _ => hWnK Ic l hH ρ 0 k)
    (x0_A2 I base l) (x1_A2 I base l) (fun _ => 16) (fun d j => hf_A2 I base l hbase hH d j)
    (fun j => by show LHK _ _ 2 j ≤ 16; have := hf j; omega)
    (fun j => by show 16 - LHK _ _ 2 j < _; rw [hc]; have := hf j; omega)
  refine ⟨Zb, Zp, h0, hP, hU, hN, fun d j => ?_⟩
  have e : 16 - LHK (hUse (S.hostAt ρ) 0 0) (fun k q => rK Ic (9 * ρ.val + (0 + k)) q) 2 j = S.hrem ρ 0 j := by have := hf j; omega
  have h : GReach (Zb 2 d j) (x1_A2 I base l d j)
      (fun φ => bcost φ (16 - LHK (hUse (S.hostAt ρ) 0 0) (fun k q => rK Ic (9 * ρ.val + (0 + k)) q) 2 j)) := hE d j
  rw [e] at h
  exact h

def zb_A2 (ρ : Fin 8) := Classical.choose (chain_ex_A2 I Ic base l hbase hH S hfit ρ)
def zp_A2 (ρ : Fin 8) := Classical.choose (Classical.choose_spec (chain_ex_A2 I Ic base l hbase hH S hfit ρ))
def z_A2_spec (ρ : Fin 8) := Classical.choose_spec (Classical.choose_spec (chain_ex_A2 I Ic base l hbase hH S hfit ρ))

include hbase hfit in
/-- the host chains of the idle climb B2 (window: stages 2..2, rank 8). -/
lemma chain_ex_B2 (ρ : Fin 8) : ∃ (Zb Zp : ℕ → Orth (BC.LC (Fin 8) H l) → Bool × T → CMat (BC.LC (Fin 8) H l)),
      (∀ d j, Zb 0 d j = x0_B2 I base l d j) ∧
      (∀ k < 1, ∀ d j, GReach (Zb k d j) (Zp k d j) (fun _ => 0)) ∧
      (∀ k < 1, ∀ d q j, hUse (S.hostAt ρ) 1 2 k q = some j →
        entW (win401N l hH (2 + k) d).X (entK Ic (9 * ρ.val + (2 + k)) q) * Zp k d j = Zb (k + 1) d j) ∧
      (∀ k < 1, ∀ d j, (∀ q, hUse (S.hostAt ρ) 1 2 k q ≠ some j) → Zb (k + 1) d j = Zp k d j) ∧
      (∀ d j, GReach (Zb 1 d j) (x1_B2 I base l d j) (fun φ => bcost φ (S.hrem ρ 1 j))) := by
  have hc : Fintype.card (BC.LC (Fin 8) H l) = 73 := card_LC401 l hH
  have hf : ∀ j, LHK (hUse (S.hostAt ρ) 1 2) (fun k q => rK Ic (9 * ρ.val + (2 + k)) q) 1 j + S.hrem ρ 1 j = 8 := fun j => hfit.2.2 ρ 1 j
  obtain ⟨Zb, Zp, h0, hP, hU, hN, hE⟩ := host_framesK (hUse (S.hostAt ρ) 1 2) (fun k q => rK Ic (9 * ρ.val + (2 + k)) q)
    (fun k d q => entW (win401N l hH (2 + k) d).X (entK Ic (9 * ρ.val + (2 + k)) q)) 1
    (fun k _ => hUse_one (S.hostAt ρ) (S.hostInj ρ) 1 2 k) (fun k _ => hWnK Ic l hH ρ 2 k)
    (x0_B2 I base l) (x1_B2 I base l) (fun _ => 8) (fun d j => hf_B2 I base l hbase hH d j)
    (fun j => by show LHK _ _ 1 j ≤ 8; have := hf j; omega)
    (fun j => by show 8 - LHK _ _ 1 j < _; rw [hc]; have := hf j; omega)
  refine ⟨Zb, Zp, h0, hP, hU, hN, fun d j => ?_⟩
  have e : 8 - LHK (hUse (S.hostAt ρ) 1 2) (fun k q => rK Ic (9 * ρ.val + (2 + k)) q) 1 j = S.hrem ρ 1 j := by have := hf j; omega
  have h : GReach (Zb 1 d j) (x1_B2 I base l d j)
      (fun φ => bcost φ (8 - LHK (hUse (S.hostAt ρ) 1 2) (fun k q => rK Ic (9 * ρ.val + (2 + k)) q) 1 j)) := hE d j
  rw [e] at h
  exact h

def zb_B2 (ρ : Fin 8) := Classical.choose (chain_ex_B2 I Ic base l hbase hH S hfit ρ)
def zp_B2 (ρ : Fin 8) := Classical.choose (Classical.choose_spec (chain_ex_B2 I Ic base l hbase hH S hfit ρ))
def z_B2_spec (ρ : Fin 8) := Classical.choose_spec (Classical.choose_spec (chain_ex_B2 I Ic base l hbase hH S hfit ρ))

include hbase hfit in
/-- the host chains of the idle climb A3 (window: stages 0..3, rank 32). -/
lemma chain_ex_A3 (ρ : Fin 8) : ∃ (Zb Zp : ℕ → Orth (BC.LC (Fin 8) H l) → Bool × T → CMat (BC.LC (Fin 8) H l)),
      (∀ d j, Zb 0 d j = x0_A3 I base l d j) ∧
      (∀ k < 4, ∀ d j, GReach (Zb k d j) (Zp k d j) (fun _ => 0)) ∧
      (∀ k < 4, ∀ d q j, hUse (S.hostAt ρ) 2 0 k q = some j →
        entW (win401N l hH (0 + k) d).X (entK Ic (9 * ρ.val + (0 + k)) q) * Zp k d j = Zb (k + 1) d j) ∧
      (∀ k < 4, ∀ d j, (∀ q, hUse (S.hostAt ρ) 2 0 k q ≠ some j) → Zb (k + 1) d j = Zp k d j) ∧
      (∀ d j, GReach (Zb 4 d j) (x1_A3 I base l d j) (fun φ => bcost φ (S.hrem ρ 2 j))) := by
  have hc : Fintype.card (BC.LC (Fin 8) H l) = 73 := card_LC401 l hH
  have hf : ∀ j, LHK (hUse (S.hostAt ρ) 2 0) (fun k q => rK Ic (9 * ρ.val + (0 + k)) q) 4 j + S.hrem ρ 2 j = 32 := fun j => hfit.2.2 ρ 2 j
  obtain ⟨Zb, Zp, h0, hP, hU, hN, hE⟩ := host_framesK (hUse (S.hostAt ρ) 2 0) (fun k q => rK Ic (9 * ρ.val + (0 + k)) q)
    (fun k d q => entW (win401N l hH (0 + k) d).X (entK Ic (9 * ρ.val + (0 + k)) q)) 4
    (fun k _ => hUse_one (S.hostAt ρ) (S.hostInj ρ) 2 0 k) (fun k _ => hWnK Ic l hH ρ 0 k)
    (x0_A3 I base l) (x1_A3 I base l) (fun _ => 32) (fun d j => hf_A3 I base l hbase hH d j)
    (fun j => by show LHK _ _ 4 j ≤ 32; have := hf j; omega)
    (fun j => by show 32 - LHK _ _ 4 j < _; rw [hc]; have := hf j; omega)
  refine ⟨Zb, Zp, h0, hP, hU, hN, fun d j => ?_⟩
  have e : 32 - LHK (hUse (S.hostAt ρ) 2 0) (fun k q => rK Ic (9 * ρ.val + (0 + k)) q) 4 j = S.hrem ρ 2 j := by have := hf j; omega
  have h : GReach (Zb 4 d j) (x1_A3 I base l d j)
      (fun φ => bcost φ (32 - LHK (hUse (S.hostAt ρ) 2 0) (fun k q => rK Ic (9 * ρ.val + (0 + k)) q) 4 j)) := hE d j
  rw [e] at h
  exact h

def zb_A3 (ρ : Fin 8) := Classical.choose (chain_ex_A3 I Ic base l hbase hH S hfit ρ)
def zp_A3 (ρ : Fin 8) := Classical.choose (Classical.choose_spec (chain_ex_A3 I Ic base l hbase hH S hfit ρ))
def z_A3_spec (ρ : Fin 8) := Classical.choose_spec (Classical.choose_spec (chain_ex_A3 I Ic base l hbase hH S hfit ρ))

include hbase hfit in
/-- the host chains of the idle climb B3 (window: stages 4..4, rank 8). -/
lemma chain_ex_B3 (ρ : Fin 8) : ∃ (Zb Zp : ℕ → Orth (BC.LC (Fin 8) H l) → Bool × T → CMat (BC.LC (Fin 8) H l)),
      (∀ d j, Zb 0 d j = x0_B3 I base l d j) ∧
      (∀ k < 1, ∀ d j, GReach (Zb k d j) (Zp k d j) (fun _ => 0)) ∧
      (∀ k < 1, ∀ d q j, hUse (S.hostAt ρ) 3 4 k q = some j →
        entW (win401N l hH (4 + k) d).X (entK Ic (9 * ρ.val + (4 + k)) q) * Zp k d j = Zb (k + 1) d j) ∧
      (∀ k < 1, ∀ d j, (∀ q, hUse (S.hostAt ρ) 3 4 k q ≠ some j) → Zb (k + 1) d j = Zp k d j) ∧
      (∀ d j, GReach (Zb 1 d j) (x1_B3 I base l d j) (fun φ => bcost φ (S.hrem ρ 3 j))) := by
  have hc : Fintype.card (BC.LC (Fin 8) H l) = 73 := card_LC401 l hH
  have hf : ∀ j, LHK (hUse (S.hostAt ρ) 3 4) (fun k q => rK Ic (9 * ρ.val + (4 + k)) q) 1 j + S.hrem ρ 3 j = 8 := fun j => hfit.2.2 ρ 3 j
  obtain ⟨Zb, Zp, h0, hP, hU, hN, hE⟩ := host_framesK (hUse (S.hostAt ρ) 3 4) (fun k q => rK Ic (9 * ρ.val + (4 + k)) q)
    (fun k d q => entW (win401N l hH (4 + k) d).X (entK Ic (9 * ρ.val + (4 + k)) q)) 1
    (fun k _ => hUse_one (S.hostAt ρ) (S.hostInj ρ) 3 4 k) (fun k _ => hWnK Ic l hH ρ 4 k)
    (x0_B3 I base l) (x1_B3 I base l) (fun _ => 8) (fun d j => hf_B3 I base l hbase hH d j)
    (fun j => by show LHK _ _ 1 j ≤ 8; have := hf j; omega)
    (fun j => by show 8 - LHK _ _ 1 j < _; rw [hc]; have := hf j; omega)
  refine ⟨Zb, Zp, h0, hP, hU, hN, fun d j => ?_⟩
  have e : 8 - LHK (hUse (S.hostAt ρ) 3 4) (fun k q => rK Ic (9 * ρ.val + (4 + k)) q) 1 j = S.hrem ρ 3 j := by have := hf j; omega
  have h : GReach (Zb 1 d j) (x1_B3 I base l d j)
      (fun φ => bcost φ (8 - LHK (hUse (S.hostAt ρ) 3 4) (fun k q => rK Ic (9 * ρ.val + (4 + k)) q) 1 j)) := hE d j
  rw [e] at h
  exact h

def zb_B3 (ρ : Fin 8) := Classical.choose (chain_ex_B3 I Ic base l hbase hH S hfit ρ)
def zp_B3 (ρ : Fin 8) := Classical.choose (Classical.choose_spec (chain_ex_B3 I Ic base l hbase hH S hfit ρ))
def z_B3_spec (ρ : Fin 8) := Classical.choose_spec (Classical.choose_spec (chain_ex_B3 I Ic base l hbase hH S hfit ρ))

include hbase hfit in
/-- the host chains of the idle climb A4 (window: stages 0..5, rank 48). -/
lemma chain_ex_A4 (ρ : Fin 8) : ∃ (Zb Zp : ℕ → Orth (BC.LC (Fin 8) H l) → Bool × T → CMat (BC.LC (Fin 8) H l)),
      (∀ d j, Zb 0 d j = x0_A4 I base l d j) ∧
      (∀ k < 6, ∀ d j, GReach (Zb k d j) (Zp k d j) (fun _ => 0)) ∧
      (∀ k < 6, ∀ d q j, hUse (S.hostAt ρ) 4 0 k q = some j →
        entW (win401N l hH (0 + k) d).X (entK Ic (9 * ρ.val + (0 + k)) q) * Zp k d j = Zb (k + 1) d j) ∧
      (∀ k < 6, ∀ d j, (∀ q, hUse (S.hostAt ρ) 4 0 k q ≠ some j) → Zb (k + 1) d j = Zp k d j) ∧
      (∀ d j, GReach (Zb 6 d j) (x1_A4 I base l d j) (fun φ => bcost φ (S.hrem ρ 4 j))) := by
  have hc : Fintype.card (BC.LC (Fin 8) H l) = 73 := card_LC401 l hH
  have hf : ∀ j, LHK (hUse (S.hostAt ρ) 4 0) (fun k q => rK Ic (9 * ρ.val + (0 + k)) q) 6 j + S.hrem ρ 4 j = 48 := fun j => hfit.2.2 ρ 4 j
  obtain ⟨Zb, Zp, h0, hP, hU, hN, hE⟩ := host_framesK (hUse (S.hostAt ρ) 4 0) (fun k q => rK Ic (9 * ρ.val + (0 + k)) q)
    (fun k d q => entW (win401N l hH (0 + k) d).X (entK Ic (9 * ρ.val + (0 + k)) q)) 6
    (fun k _ => hUse_one (S.hostAt ρ) (S.hostInj ρ) 4 0 k) (fun k _ => hWnK Ic l hH ρ 0 k)
    (x0_A4 I base l) (x1_A4 I base l) (fun _ => 48) (fun d j => hf_A4 I base l hbase hH d j)
    (fun j => by show LHK _ _ 6 j ≤ 48; have := hf j; omega)
    (fun j => by show 48 - LHK _ _ 6 j < _; rw [hc]; have := hf j; omega)
  refine ⟨Zb, Zp, h0, hP, hU, hN, fun d j => ?_⟩
  have e : 48 - LHK (hUse (S.hostAt ρ) 4 0) (fun k q => rK Ic (9 * ρ.val + (0 + k)) q) 6 j = S.hrem ρ 4 j := by have := hf j; omega
  have h : GReach (Zb 6 d j) (x1_A4 I base l d j)
      (fun φ => bcost φ (48 - LHK (hUse (S.hostAt ρ) 4 0) (fun k q => rK Ic (9 * ρ.val + (0 + k)) q) 6 j)) := hE d j
  rw [e] at h
  exact h

def zb_A4 (ρ : Fin 8) := Classical.choose (chain_ex_A4 I Ic base l hbase hH S hfit ρ)
def zp_A4 (ρ : Fin 8) := Classical.choose (Classical.choose_spec (chain_ex_A4 I Ic base l hbase hH S hfit ρ))
def z_A4_spec (ρ : Fin 8) := Classical.choose_spec (Classical.choose_spec (chain_ex_A4 I Ic base l hbase hH S hfit ρ))

include hbase hfit in
/-- the host chains of the idle climb B4 (window: stages 6..6, rank 8). -/
lemma chain_ex_B4 (ρ : Fin 8) : ∃ (Zb Zp : ℕ → Orth (BC.LC (Fin 8) H l) → Bool × T → CMat (BC.LC (Fin 8) H l)),
      (∀ d j, Zb 0 d j = x0_B4 I base l d j) ∧
      (∀ k < 1, ∀ d j, GReach (Zb k d j) (Zp k d j) (fun _ => 0)) ∧
      (∀ k < 1, ∀ d q j, hUse (S.hostAt ρ) 5 6 k q = some j →
        entW (win401N l hH (6 + k) d).X (entK Ic (9 * ρ.val + (6 + k)) q) * Zp k d j = Zb (k + 1) d j) ∧
      (∀ k < 1, ∀ d j, (∀ q, hUse (S.hostAt ρ) 5 6 k q ≠ some j) → Zb (k + 1) d j = Zp k d j) ∧
      (∀ d j, GReach (Zb 1 d j) (x1_B4 I base l d j) (fun φ => bcost φ (S.hrem ρ 5 j))) := by
  have hc : Fintype.card (BC.LC (Fin 8) H l) = 73 := card_LC401 l hH
  have hf : ∀ j, LHK (hUse (S.hostAt ρ) 5 6) (fun k q => rK Ic (9 * ρ.val + (6 + k)) q) 1 j + S.hrem ρ 5 j = 8 := fun j => hfit.2.2 ρ 5 j
  obtain ⟨Zb, Zp, h0, hP, hU, hN, hE⟩ := host_framesK (hUse (S.hostAt ρ) 5 6) (fun k q => rK Ic (9 * ρ.val + (6 + k)) q)
    (fun k d q => entW (win401N l hH (6 + k) d).X (entK Ic (9 * ρ.val + (6 + k)) q)) 1
    (fun k _ => hUse_one (S.hostAt ρ) (S.hostInj ρ) 5 6 k) (fun k _ => hWnK Ic l hH ρ 6 k)
    (x0_B4 I base l) (x1_B4 I base l) (fun _ => 8) (fun d j => hf_B4 I base l hbase hH d j)
    (fun j => by show LHK _ _ 1 j ≤ 8; have := hf j; omega)
    (fun j => by show 8 - LHK _ _ 1 j < _; rw [hc]; have := hf j; omega)
  refine ⟨Zb, Zp, h0, hP, hU, hN, fun d j => ?_⟩
  have e : 8 - LHK (hUse (S.hostAt ρ) 5 6) (fun k q => rK Ic (9 * ρ.val + (6 + k)) q) 1 j = S.hrem ρ 5 j := by have := hf j; omega
  have h : GReach (Zb 1 d j) (x1_B4 I base l d j)
      (fun φ => bcost φ (8 - LHK (hUse (S.hostAt ρ) 5 6) (fun k q => rK Ic (9 * ρ.val + (6 + k)) q) 1 j)) := hE d j
  rw [e] at h
  exact h

def zb_B4 (ρ : Fin 8) := Classical.choose (chain_ex_B4 I Ic base l hbase hH S hfit ρ)
def zp_B4 (ρ : Fin 8) := Classical.choose (Classical.choose_spec (chain_ex_B4 I Ic base l hbase hH S hfit ρ))
def z_B4_spec (ρ : Fin 8) := Classical.choose_spec (Classical.choose_spec (chain_ex_B4 I Ic base l hbase hH S hfit ρ))

include hbase hfit in
/-- the host chains of the idle climb F1 (window: stages 3..8, rank 48). -/
lemma chain_ex_F1 (ρ : Fin 8) : ∃ (Zb Zp : ℕ → Orth (BC.LC (Fin 8) H l) → Bool × T → CMat (BC.LC (Fin 8) H l)),
      (∀ d j, Zb 0 d j = x0_F1 I base l d j) ∧
      (∀ k < 6, ∀ d j, GReach (Zb k d j) (Zp k d j) (fun _ => 0)) ∧
      (∀ k < 6, ∀ d q j, hUse (S.hostAt ρ) 6 3 k q = some j →
        entW (win401N l hH (3 + k) d).X (entK Ic (9 * ρ.val + (3 + k)) q) * Zp k d j = Zb (k + 1) d j) ∧
      (∀ k < 6, ∀ d j, (∀ q, hUse (S.hostAt ρ) 6 3 k q ≠ some j) → Zb (k + 1) d j = Zp k d j) ∧
      (∀ d j, GReach (Zb 6 d j) (x1_F1 I base l d j) (fun φ => bcost φ (S.hrem ρ 6 j))) := by
  have hc : Fintype.card (BC.LC (Fin 8) H l) = 73 := card_LC401 l hH
  have hf : ∀ j, LHK (hUse (S.hostAt ρ) 6 3) (fun k q => rK Ic (9 * ρ.val + (3 + k)) q) 6 j + S.hrem ρ 6 j = 48 := fun j => hfit.2.2 ρ 6 j
  obtain ⟨Zb, Zp, h0, hP, hU, hN, hE⟩ := host_framesK (hUse (S.hostAt ρ) 6 3) (fun k q => rK Ic (9 * ρ.val + (3 + k)) q)
    (fun k d q => entW (win401N l hH (3 + k) d).X (entK Ic (9 * ρ.val + (3 + k)) q)) 6
    (fun k _ => hUse_one (S.hostAt ρ) (S.hostInj ρ) 6 3 k) (fun k _ => hWnK Ic l hH ρ 3 k)
    (x0_F1 I base l) (x1_F1 I base l) (fun _ => 48) (fun d j => hf_F1 I base l hbase hH d j)
    (fun j => by show LHK _ _ 6 j ≤ 48; have := hf j; omega)
    (fun j => by show 48 - LHK _ _ 6 j < _; rw [hc]; have := hf j; omega)
  refine ⟨Zb, Zp, h0, hP, hU, hN, fun d j => ?_⟩
  have e : 48 - LHK (hUse (S.hostAt ρ) 6 3) (fun k q => rK Ic (9 * ρ.val + (3 + k)) q) 6 j = S.hrem ρ 6 j := by have := hf j; omega
  have h : GReach (Zb 6 d j) (x1_F1 I base l d j)
      (fun φ => bcost φ (48 - LHK (hUse (S.hostAt ρ) 6 3) (fun k q => rK Ic (9 * ρ.val + (3 + k)) q) 6 j)) := hE d j
  rw [e] at h
  exact h

def zb_F1 (ρ : Fin 8) := Classical.choose (chain_ex_F1 I Ic base l hbase hH S hfit ρ)
def zp_F1 (ρ : Fin 8) := Classical.choose (Classical.choose_spec (chain_ex_F1 I Ic base l hbase hH S hfit ρ))
def z_F1_spec (ρ : Fin 8) := Classical.choose_spec (Classical.choose_spec (chain_ex_F1 I Ic base l hbase hH S hfit ρ))

include hbase hfit in
/-- the host chains of the idle climb F2 (window: stages 5..8, rank 32). -/
lemma chain_ex_F2 (ρ : Fin 8) : ∃ (Zb Zp : ℕ → Orth (BC.LC (Fin 8) H l) → Bool × T → CMat (BC.LC (Fin 8) H l)),
      (∀ d j, Zb 0 d j = x0_F2 I base l d j) ∧
      (∀ k < 4, ∀ d j, GReach (Zb k d j) (Zp k d j) (fun _ => 0)) ∧
      (∀ k < 4, ∀ d q j, hUse (S.hostAt ρ) 7 5 k q = some j →
        entW (win401N l hH (5 + k) d).X (entK Ic (9 * ρ.val + (5 + k)) q) * Zp k d j = Zb (k + 1) d j) ∧
      (∀ k < 4, ∀ d j, (∀ q, hUse (S.hostAt ρ) 7 5 k q ≠ some j) → Zb (k + 1) d j = Zp k d j) ∧
      (∀ d j, GReach (Zb 4 d j) (x1_F2 I base l d j) (fun φ => bcost φ (S.hrem ρ 7 j))) := by
  have hc : Fintype.card (BC.LC (Fin 8) H l) = 73 := card_LC401 l hH
  have hf : ∀ j, LHK (hUse (S.hostAt ρ) 7 5) (fun k q => rK Ic (9 * ρ.val + (5 + k)) q) 4 j + S.hrem ρ 7 j = 32 := fun j => hfit.2.2 ρ 7 j
  obtain ⟨Zb, Zp, h0, hP, hU, hN, hE⟩ := host_framesK (hUse (S.hostAt ρ) 7 5) (fun k q => rK Ic (9 * ρ.val + (5 + k)) q)
    (fun k d q => entW (win401N l hH (5 + k) d).X (entK Ic (9 * ρ.val + (5 + k)) q)) 4
    (fun k _ => hUse_one (S.hostAt ρ) (S.hostInj ρ) 7 5 k) (fun k _ => hWnK Ic l hH ρ 5 k)
    (x0_F2 I base l) (x1_F2 I base l) (fun _ => 32) (fun d j => hf_F2 I base l hbase hH d j)
    (fun j => by show LHK _ _ 4 j ≤ 32; have := hf j; omega)
    (fun j => by show 32 - LHK _ _ 4 j < _; rw [hc]; have := hf j; omega)
  refine ⟨Zb, Zp, h0, hP, hU, hN, fun d j => ?_⟩
  have e : 32 - LHK (hUse (S.hostAt ρ) 7 5) (fun k q => rK Ic (9 * ρ.val + (5 + k)) q) 4 j = S.hrem ρ 7 j := by have := hf j; omega
  have h : GReach (Zb 4 d j) (x1_F2 I base l d j)
      (fun φ => bcost φ (32 - LHK (hUse (S.hostAt ρ) 7 5) (fun k q => rK Ic (9 * ρ.val + (5 + k)) q) 4 j)) := hE d j
  rw [e] at h
  exact h

def zb_F2 (ρ : Fin 8) := Classical.choose (chain_ex_F2 I Ic base l hbase hH S hfit ρ)
def zp_F2 (ρ : Fin 8) := Classical.choose (Classical.choose_spec (chain_ex_F2 I Ic base l hbase hH S hfit ρ))
def z_F2_spec (ρ : Fin 8) := Classical.choose_spec (Classical.choose_spec (chain_ex_F2 I Ic base l hbase hH S hfit ρ))

include hbase hfit in
/-- the host chains of the idle climb F3 (window: stages 7..8, rank 16). -/
lemma chain_ex_F3 (ρ : Fin 8) : ∃ (Zb Zp : ℕ → Orth (BC.LC (Fin 8) H l) → Bool × T → CMat (BC.LC (Fin 8) H l)),
      (∀ d j, Zb 0 d j = x0_F3 I base l d j) ∧
      (∀ k < 2, ∀ d j, GReach (Zb k d j) (Zp k d j) (fun _ => 0)) ∧
      (∀ k < 2, ∀ d q j, hUse (S.hostAt ρ) 8 7 k q = some j →
        entW (win401N l hH (7 + k) d).X (entK Ic (9 * ρ.val + (7 + k)) q) * Zp k d j = Zb (k + 1) d j) ∧
      (∀ k < 2, ∀ d j, (∀ q, hUse (S.hostAt ρ) 8 7 k q ≠ some j) → Zb (k + 1) d j = Zp k d j) ∧
      (∀ d j, GReach (Zb 2 d j) (x1_F3 I base l d j) (fun φ => bcost φ (S.hrem ρ 8 j))) := by
  have hc : Fintype.card (BC.LC (Fin 8) H l) = 73 := card_LC401 l hH
  have hf : ∀ j, LHK (hUse (S.hostAt ρ) 8 7) (fun k q => rK Ic (9 * ρ.val + (7 + k)) q) 2 j + S.hrem ρ 8 j = 16 := fun j => hfit.2.2 ρ 8 j
  obtain ⟨Zb, Zp, h0, hP, hU, hN, hE⟩ := host_framesK (hUse (S.hostAt ρ) 8 7) (fun k q => rK Ic (9 * ρ.val + (7 + k)) q)
    (fun k d q => entW (win401N l hH (7 + k) d).X (entK Ic (9 * ρ.val + (7 + k)) q)) 2
    (fun k _ => hUse_one (S.hostAt ρ) (S.hostInj ρ) 8 7 k) (fun k _ => hWnK Ic l hH ρ 7 k)
    (x0_F3 I base l) (x1_F3 I base l) (fun _ => 16) (fun d j => hf_F3 I base l hbase hH d j)
    (fun j => by show LHK _ _ 2 j ≤ 16; have := hf j; omega)
    (fun j => by show 16 - LHK _ _ 2 j < _; rw [hc]; have := hf j; omega)
  refine ⟨Zb, Zp, h0, hP, hU, hN, fun d j => ?_⟩
  have e : 16 - LHK (hUse (S.hostAt ρ) 8 7) (fun k q => rK Ic (9 * ρ.val + (7 + k)) q) 2 j = S.hrem ρ 8 j := by have := hf j; omega
  have h : GReach (Zb 2 d j) (x1_F3 I base l d j)
      (fun φ => bcost φ (16 - LHK (hUse (S.hostAt ρ) 8 7) (fun k q => rK Ic (9 * ρ.val + (7 + k)) q) 2 j)) := hE d j
  rw [e] at h
  exact h

def zb_F3 (ρ : Fin 8) := Classical.choose (chain_ex_F3 I Ic base l hbase hH S hfit ρ)
def zp_F3 (ρ : Fin 8) := Classical.choose (Classical.choose_spec (chain_ex_F3 I Ic base l hbase hH S hfit ρ))
def z_F3_spec (ρ : Fin 8) := Classical.choose_spec (Classical.choose_spec (chain_ex_F3 I Ic base l hbase hH S hfit ρ))

/-- the host chains of all kinds, indexed by stage (`k - kz c` steps into the window). -/
def hbH (ρ : Fin 8) (c : Fin 9) (k : ℕ) : Orth (BC.LC (Fin 8) H l) → Bool × T → CMat (BC.LC (Fin 8) H l) :=
  match c.val with
  | 0 => zb_A2 I Ic base l hbase hH S hfit ρ (k - 0)
  | 1 => zb_B2 I Ic base l hbase hH S hfit ρ (k - 2)
  | 2 => zb_A3 I Ic base l hbase hH S hfit ρ (k - 0)
  | 3 => zb_B3 I Ic base l hbase hH S hfit ρ (k - 4)
  | 4 => zb_A4 I Ic base l hbase hH S hfit ρ (k - 0)
  | 5 => zb_B4 I Ic base l hbase hH S hfit ρ (k - 6)
  | 6 => zb_F1 I Ic base l hbase hH S hfit ρ (k - 3)
  | 7 => zb_F2 I Ic base l hbase hH S hfit ρ (k - 5)
  | _ => zb_F3 I Ic base l hbase hH S hfit ρ (k - 7)

def hpH (ρ : Fin 8) (c : Fin 9) (k : ℕ) : Orth (BC.LC (Fin 8) H l) → Bool × T → CMat (BC.LC (Fin 8) H l) :=
  match c.val with
  | 0 => zp_A2 I Ic base l hbase hH S hfit ρ (k - 0)
  | 1 => zp_B2 I Ic base l hbase hH S hfit ρ (k - 2)
  | 2 => zp_A3 I Ic base l hbase hH S hfit ρ (k - 0)
  | 3 => zp_B3 I Ic base l hbase hH S hfit ρ (k - 4)
  | 4 => zp_A4 I Ic base l hbase hH S hfit ρ (k - 0)
  | 5 => zp_B4 I Ic base l hbase hH S hfit ρ (k - 6)
  | 6 => zp_F1 I Ic base l hbase hH S hfit ρ (k - 3)
  | 7 => zp_F2 I Ic base l hbase hH S hfit ρ (k - 5)
  | _ => zp_F3 I Ic base l hbase hH S hfit ρ (k - 7)

/-- **The hosted nine-stage word as a term of `GHost401`** on the label space `LC (Fin 8) H l`. -/
def ghostGeom : GHost401 H T Sl C (BC.LC (Fin 8) H l) (Orth (BC.LC (Fin 8) H l)) S.nb where
  I := I
  Ic := Ic
  hIc := hIc
  G0 := fun d => gwinC hB401 (by omega) d ∅
  G1 := fun d => gwinC hB401 (by omega) d (qC bs401_1)
  G2 := fun d => gwinC hB401 (by omega) d (qC bs401_2)
  G3 := fun d => gwinC hB401 (by omega) d (qC bs401_3)
  G4 := fun d => gwinC hB401 (by omega) d (qC bs401_4)
  G5 := fun d => gwinC hB401 (by omega) d (qC bs401_5)
  G6 := fun d => gwinC hB401 (by omega) d (qC bs401_6)
  G7 := fun d => gwinC hB401 (by omega) d (qC bs401_7)
  G8 := fun d => gwinC hB401 (by omega) d (qC bs401_8)
  r1 := fun t => RrC (base t) l (0 : Fin 8)
  r2 := fun t => RrC (base t) l (1 : Fin 8)
  r3 := fun t => RrC (base t) l (2 : Fin 8)
  r4 := fun t => RrC (base t) l (3 : Fin 8)
  r5 := fun t => RrC (base t) l (4 : Fin 8)
  r6 := fun t => RrC (base t) l (5 : Fin 8)
  r7 := fun t => RrC (base t) l (6 : Fin 8)
  r8 := fun t => RrC (base t) l (7 : Fin 8)
  N0 := fun ρ d q => entN (gwinC hB401 (by omega) d ∅).X ((Ic ρ 0).ent q)
  Wn0 := fun ρ d q => entW (gwinC hB401 (by omega) d ∅).X ((Ic ρ 0).ent q)
  N1 := fun ρ d q => entN (gwinC hB401 (by omega) d (qC bs401_1)).X ((Ic ρ 1).ent q)
  Wn1 := fun ρ d q => entW (gwinC hB401 (by omega) d (qC bs401_1)).X ((Ic ρ 1).ent q)
  N2 := fun ρ d q => entN (gwinC hB401 (by omega) d (qC bs401_2)).X ((Ic ρ 2).ent q)
  Wn2 := fun ρ d q => entW (gwinC hB401 (by omega) d (qC bs401_2)).X ((Ic ρ 2).ent q)
  N3 := fun ρ d q => entN (gwinC hB401 (by omega) d (qC bs401_3)).X ((Ic ρ 3).ent q)
  Wn3 := fun ρ d q => entW (gwinC hB401 (by omega) d (qC bs401_3)).X ((Ic ρ 3).ent q)
  N4 := fun ρ d q => entN (gwinC hB401 (by omega) d (qC bs401_4)).X ((Ic ρ 4).ent q)
  Wn4 := fun ρ d q => entW (gwinC hB401 (by omega) d (qC bs401_4)).X ((Ic ρ 4).ent q)
  N5 := fun ρ d q => entN (gwinC hB401 (by omega) d (qC bs401_5)).X ((Ic ρ 5).ent q)
  Wn5 := fun ρ d q => entW (gwinC hB401 (by omega) d (qC bs401_5)).X ((Ic ρ 5).ent q)
  N6 := fun ρ d q => entN (gwinC hB401 (by omega) d (qC bs401_6)).X ((Ic ρ 6).ent q)
  Wn6 := fun ρ d q => entW (gwinC hB401 (by omega) d (qC bs401_6)).X ((Ic ρ 6).ent q)
  N7 := fun ρ d q => entN (gwinC hB401 (by omega) d (qC bs401_7)).X ((Ic ρ 7).ent q)
  Wn7 := fun ρ d q => entW (gwinC hB401 (by omega) d (qC bs401_7)).X ((Ic ρ 7).ent q)
  N8 := fun ρ d q => entN (gwinC hB401 (by omega) d (qC bs401_8)).X ((Ic ρ 8).ent q)
  Wn8 := fun ρ d q => entW (gwinC hB401 (by omega) d (qC bs401_8)).X ((Ic ρ 8).ent q)
  hostAt := S.hostAt
  hostInj := S.hostInj
  hostWin := S.hostWin
  bk := S.bk
  hinj := S.hinj
  Zb := zbH I Ic base l hbase hH S hfit
  Zp := zpH I Ic base l hbase hH S hfit
  pad := S.pad
  Hb := hbH I Ic base l hbase hH S hfit
  Hp := hpH I Ic base l hbase hH S hfit
  hrem := S.hrem
  u := fun g t => (BBC (base t) l g).v (Sum.inl l)
  YF := fun g t => frame (BBC (base t) l g) (univ \ {Sum.inl l})
  hm := two_le_card_LC hB401 (by omega)
  cX4 := fun φ => bcost φ 0
  cY4 := fun φ => bcost φ 0
  inv0 := fun g t => ⟨unframeM (g.1 * Matrix.fromBlocks (tt (I.tv t)) 0 0 (diagI ∅) * g.1ᵀ),
    frameM_unframeM _⟩
  z0 := fun g => PhiC_zero_empty g
  hN0 := fun ρ d q => entN_spec _ _
  hW0 := fun ρ d q => entW_spec _ _
  hN1 := fun ρ d q => entN_spec _ _
  hW1 := fun ρ d q => entW_spec _ _
  hN2 := fun ρ d q => entN_spec _ _
  hW2 := fun ρ d q => entW_spec _ _
  hN3 := fun ρ d q => entN_spec _ _
  hW3 := fun ρ d q => entW_spec _ _
  hN4 := fun ρ d q => entN_spec _ _
  hW4 := fun ρ d q => entW_spec _ _
  hN5 := fun ρ d q => entN_spec _ _
  hW5 := fun ρ d q => entW_spec _ _
  hN6 := fun ρ d q => entN_spec _ _
  hW6 := fun ρ d q => entW_spec _ _
  hN7 := fun ρ d q => entN_spec _ _
  hW7 := fun ρ d q => entW_spec _ _
  hN8 := fun ρ d q => entN_spec _ _
  hW8 := fun ρ d q => entW_spec _ _
  x01 := fun g t => g401geom_x01 I base l hbase g t
  y01 := fun g t => g401geom_y01 I base l hbase g t
  x12 := fun g t => g401geom_xx I base l hbase bs401_1 0 1 (Finset.mem_singleton_self _) mem401_1 g t
  y12 := fun g t => g401geom_yy I base l hbase bs401_1 0 1 (Finset.mem_singleton_self _) mem401_1 g t
  x23 := fun g t => g401geom_xx I base l hbase bs401_2 1 2 (Finset.mem_insert_self _ _) mem401_2 g t
  y23 := fun g t => g401geom_yy I base l hbase bs401_2 1 2 (Finset.mem_insert_self _ _) mem401_2 g t
  x34 := fun g t => g401geom_xx I base l hbase bs401_3 2 3 (Finset.mem_insert_self _ _) mem401_3 g t
  y34 := fun g t => g401geom_yy I base l hbase bs401_3 2 3 (Finset.mem_insert_self _ _) mem401_3 g t
  x45 := fun g t => g401geom_xx I base l hbase bs401_4 3 4 (Finset.mem_insert_self _ _) mem401_4 g t
  y45 := fun g t => g401geom_yy I base l hbase bs401_4 3 4 (Finset.mem_insert_self _ _) mem401_4 g t
  x56 := fun g t => g401geom_xx I base l hbase bs401_5 4 5 (Finset.mem_insert_self _ _) mem401_5 g t
  y56 := fun g t => g401geom_yy I base l hbase bs401_5 4 5 (Finset.mem_insert_self _ _) mem401_5 g t
  x67 := fun g t => g401geom_xx I base l hbase bs401_6 5 6 (Finset.mem_insert_self _ _) mem401_6 g t
  y67 := fun g t => g401geom_yy I base l hbase bs401_6 5 6 (Finset.mem_insert_self _ _) mem401_6 g t
  x78 := fun g t => g401geom_xx I base l hbase bs401_7 6 7 (Finset.mem_insert_self _ _) mem401_7 g t
  y78 := fun g t => g401geom_yy I base l hbase bs401_7 6 7 (Finset.mem_insert_self _ _) mem401_7 g t
  z0b := (zH_spec I Ic base l hbase hH S hfit).1
  hP0 := fun ρ g b => (zH_spec I Ic base l hbase hH S hfit).2.1 (9 * ρ.val + 0) (by have := ρ.isLt; omega) g b
  hZ0 := fun ρ g q hq => by
    have h := (zH_spec I Ic base l hbase hH S hfit).2.2.1 (9 * ρ.val + 0) (by have := ρ.isLt; omega) g q (S.bk ρ 0 q)
      (bUseR_bank ρ 0 q hq)
    rw [show (9 * ρ.val + 0) % 9 = 0 by omega] at h
    rw [entK_eq Ic ρ 0 (by decide)] at h
    exact h
  hZn0 := fun ρ g b hb => (zH_spec I Ic base l hbase hH S hfit).2.2.2.1 (9 * ρ.val + 0) (by have := ρ.isLt; omega) g b
    (fun q hq => by obtain ⟨h1, h2⟩ := bUseR_to ρ 0 q b hq; exact hb q h1 h2)
  hP1 := fun ρ g b => (zH_spec I Ic base l hbase hH S hfit).2.1 (9 * ρ.val + 1) (by have := ρ.isLt; omega) g b
  hZ1 := fun ρ g q hq => by
    have h := (zH_spec I Ic base l hbase hH S hfit).2.2.1 (9 * ρ.val + 1) (by have := ρ.isLt; omega) g q (S.bk ρ 1 q)
      (bUseR_bank ρ 1 q hq)
    rw [show (9 * ρ.val + 1) % 9 = 1 by omega] at h
    rw [entK_eq Ic ρ 1 (by decide)] at h
    exact h
  hZn1 := fun ρ g b hb => (zH_spec I Ic base l hbase hH S hfit).2.2.2.1 (9 * ρ.val + 1) (by have := ρ.isLt; omega) g b
    (fun q hq => by obtain ⟨h1, h2⟩ := bUseR_to ρ 1 q b hq; exact hb q h1 h2)
  hP2 := fun ρ g b => (zH_spec I Ic base l hbase hH S hfit).2.1 (9 * ρ.val + 2) (by have := ρ.isLt; omega) g b
  hZ2 := fun ρ g q hq => by
    have h := (zH_spec I Ic base l hbase hH S hfit).2.2.1 (9 * ρ.val + 2) (by have := ρ.isLt; omega) g q (S.bk ρ 2 q)
      (bUseR_bank ρ 2 q hq)
    rw [show (9 * ρ.val + 2) % 9 = 2 by omega] at h
    rw [entK_eq Ic ρ 2 (by decide)] at h
    exact h
  hZn2 := fun ρ g b hb => (zH_spec I Ic base l hbase hH S hfit).2.2.2.1 (9 * ρ.val + 2) (by have := ρ.isLt; omega) g b
    (fun q hq => by obtain ⟨h1, h2⟩ := bUseR_to ρ 2 q b hq; exact hb q h1 h2)
  hP3 := fun ρ g b => (zH_spec I Ic base l hbase hH S hfit).2.1 (9 * ρ.val + 3) (by have := ρ.isLt; omega) g b
  hZ3 := fun ρ g q hq => by
    have h := (zH_spec I Ic base l hbase hH S hfit).2.2.1 (9 * ρ.val + 3) (by have := ρ.isLt; omega) g q (S.bk ρ 3 q)
      (bUseR_bank ρ 3 q hq)
    rw [show (9 * ρ.val + 3) % 9 = 3 by omega] at h
    rw [entK_eq Ic ρ 3 (by decide)] at h
    exact h
  hZn3 := fun ρ g b hb => (zH_spec I Ic base l hbase hH S hfit).2.2.2.1 (9 * ρ.val + 3) (by have := ρ.isLt; omega) g b
    (fun q hq => by obtain ⟨h1, h2⟩ := bUseR_to ρ 3 q b hq; exact hb q h1 h2)
  hP4 := fun ρ g b => (zH_spec I Ic base l hbase hH S hfit).2.1 (9 * ρ.val + 4) (by have := ρ.isLt; omega) g b
  hZ4 := fun ρ g q hq => by
    have h := (zH_spec I Ic base l hbase hH S hfit).2.2.1 (9 * ρ.val + 4) (by have := ρ.isLt; omega) g q (S.bk ρ 4 q)
      (bUseR_bank ρ 4 q hq)
    rw [show (9 * ρ.val + 4) % 9 = 4 by omega] at h
    rw [entK_eq Ic ρ 4 (by decide)] at h
    exact h
  hZn4 := fun ρ g b hb => (zH_spec I Ic base l hbase hH S hfit).2.2.2.1 (9 * ρ.val + 4) (by have := ρ.isLt; omega) g b
    (fun q hq => by obtain ⟨h1, h2⟩ := bUseR_to ρ 4 q b hq; exact hb q h1 h2)
  hP5 := fun ρ g b => (zH_spec I Ic base l hbase hH S hfit).2.1 (9 * ρ.val + 5) (by have := ρ.isLt; omega) g b
  hZ5 := fun ρ g q hq => by
    have h := (zH_spec I Ic base l hbase hH S hfit).2.2.1 (9 * ρ.val + 5) (by have := ρ.isLt; omega) g q (S.bk ρ 5 q)
      (bUseR_bank ρ 5 q hq)
    rw [show (9 * ρ.val + 5) % 9 = 5 by omega] at h
    rw [entK_eq Ic ρ 5 (by decide)] at h
    exact h
  hZn5 := fun ρ g b hb => (zH_spec I Ic base l hbase hH S hfit).2.2.2.1 (9 * ρ.val + 5) (by have := ρ.isLt; omega) g b
    (fun q hq => by obtain ⟨h1, h2⟩ := bUseR_to ρ 5 q b hq; exact hb q h1 h2)
  hP6 := fun ρ g b => (zH_spec I Ic base l hbase hH S hfit).2.1 (9 * ρ.val + 6) (by have := ρ.isLt; omega) g b
  hZ6 := fun ρ g q hq => by
    have h := (zH_spec I Ic base l hbase hH S hfit).2.2.1 (9 * ρ.val + 6) (by have := ρ.isLt; omega) g q (S.bk ρ 6 q)
      (bUseR_bank ρ 6 q hq)
    rw [show (9 * ρ.val + 6) % 9 = 6 by omega] at h
    rw [entK_eq Ic ρ 6 (by decide)] at h
    exact h
  hZn6 := fun ρ g b hb => (zH_spec I Ic base l hbase hH S hfit).2.2.2.1 (9 * ρ.val + 6) (by have := ρ.isLt; omega) g b
    (fun q hq => by obtain ⟨h1, h2⟩ := bUseR_to ρ 6 q b hq; exact hb q h1 h2)
  hP7 := fun ρ g b => (zH_spec I Ic base l hbase hH S hfit).2.1 (9 * ρ.val + 7) (by have := ρ.isLt; omega) g b
  hZ7 := fun ρ g q hq => by
    have h := (zH_spec I Ic base l hbase hH S hfit).2.2.1 (9 * ρ.val + 7) (by have := ρ.isLt; omega) g q (S.bk ρ 7 q)
      (bUseR_bank ρ 7 q hq)
    rw [show (9 * ρ.val + 7) % 9 = 7 by omega] at h
    rw [entK_eq Ic ρ 7 (by decide)] at h
    exact h
  hZn7 := fun ρ g b hb => (zH_spec I Ic base l hbase hH S hfit).2.2.2.1 (9 * ρ.val + 7) (by have := ρ.isLt; omega) g b
    (fun q hq => by obtain ⟨h1, h2⟩ := bUseR_to ρ 7 q b hq; exact hb q h1 h2)
  hP8 := fun ρ g b => (zH_spec I Ic base l hbase hH S hfit).2.1 (9 * ρ.val + 8) (by have := ρ.isLt; omega) g b
  hZ8 := fun ρ g q hq => by
    have h := (zH_spec I Ic base l hbase hH S hfit).2.2.1 (9 * ρ.val + 8) (by have := ρ.isLt; omega) g q (S.bk ρ 8 q)
      (bUseR_bank ρ 8 q hq)
    rw [show (9 * ρ.val + 8) % 9 = 8 by omega] at h
    rw [entK_eq Ic ρ 8 (by decide)] at h
    exact h
  hZn8 := fun ρ g b hb => (zH_spec I Ic base l hbase hH S hfit).2.2.2.1 (9 * ρ.val + 8) (by have := ρ.isLt; omega) g b
    (fun q hq => by obtain ⟨h1, h2⟩ := bUseR_to ρ 8 q b hq; exact hb q h1 h2)
  bpad := (zH_spec I Ic base l hbase hH S hfit).2.2.2.2
  hH0_A2 := fun ρ g t => ⟨(z_A2_spec I Ic base l hbase hH S hfit ρ).1 g (false, t), (z_A2_spec I Ic base l hbase hH S hfit ρ).1 g (true, t)⟩
  hHP_A2_0 := fun ρ g j => (z_A2_spec I Ic base l hbase hH S hfit ρ).2.1 0 (by decide) g j
  hHZ_A2_0 := fun ρ g q j h => by
    have hh := (z_A2_spec I Ic base l hbase hH S hfit ρ).2.2.1 0 (by decide) g q j (hUse_of (c := 0) (k0 := 0) (k := 0) (by decide) h)
    rw [entK_eq Ic ρ (0 + 0) (by decide)] at hh
    exact hh
  hHZn_A2_0 := fun ρ g j h => (z_A2_spec I Ic base l hbase hH S hfit ρ).2.2.2.1 0 (by decide) g j
    (fun q hq => by obtain ⟨hk, e⟩ := hUse_to hq; exact h q e)
  hHP_A2_1 := fun ρ g j => (z_A2_spec I Ic base l hbase hH S hfit ρ).2.1 1 (by decide) g j
  hHZ_A2_1 := fun ρ g q j h => by
    have hh := (z_A2_spec I Ic base l hbase hH S hfit ρ).2.2.1 1 (by decide) g q j (hUse_of (c := 0) (k0 := 0) (k := 1) (by decide) h)
    rw [entK_eq Ic ρ (0 + 1) (by decide)] at hh
    exact hh
  hHZn_A2_1 := fun ρ g j h => (z_A2_spec I Ic base l hbase hH S hfit ρ).2.2.2.1 1 (by decide) g j
    (fun q hq => by obtain ⟨hk, e⟩ := hUse_to hq; exact h q e)
  hHE_A2 := fun ρ g t => ⟨(z_A2_spec I Ic base l hbase hH S hfit ρ).2.2.2.2 g (false, t), (z_A2_spec I Ic base l hbase hH S hfit ρ).2.2.2.2 g (true, t)⟩
  hH0_B2 := fun ρ g t => ⟨(z_B2_spec I Ic base l hbase hH S hfit ρ).1 g (false, t), (z_B2_spec I Ic base l hbase hH S hfit ρ).1 g (true, t)⟩
  hHP_B2_2 := fun ρ g j => (z_B2_spec I Ic base l hbase hH S hfit ρ).2.1 0 (by decide) g j
  hHZ_B2_2 := fun ρ g q j h => by
    have hh := (z_B2_spec I Ic base l hbase hH S hfit ρ).2.2.1 0 (by decide) g q j (hUse_of (c := 1) (k0 := 2) (k := 0) (by decide) h)
    rw [entK_eq Ic ρ (2 + 0) (by decide)] at hh
    exact hh
  hHZn_B2_2 := fun ρ g j h => (z_B2_spec I Ic base l hbase hH S hfit ρ).2.2.2.1 0 (by decide) g j
    (fun q hq => by obtain ⟨hk, e⟩ := hUse_to hq; exact h q e)
  hHE_B2 := fun ρ g t => ⟨(z_B2_spec I Ic base l hbase hH S hfit ρ).2.2.2.2 g (false, t), (z_B2_spec I Ic base l hbase hH S hfit ρ).2.2.2.2 g (true, t)⟩
  hH0_A3 := fun ρ g t => ⟨(z_A3_spec I Ic base l hbase hH S hfit ρ).1 g (false, t), (z_A3_spec I Ic base l hbase hH S hfit ρ).1 g (true, t)⟩
  hHP_A3_0 := fun ρ g j => (z_A3_spec I Ic base l hbase hH S hfit ρ).2.1 0 (by decide) g j
  hHZ_A3_0 := fun ρ g q j h => by
    have hh := (z_A3_spec I Ic base l hbase hH S hfit ρ).2.2.1 0 (by decide) g q j (hUse_of (c := 2) (k0 := 0) (k := 0) (by decide) h)
    rw [entK_eq Ic ρ (0 + 0) (by decide)] at hh
    exact hh
  hHZn_A3_0 := fun ρ g j h => (z_A3_spec I Ic base l hbase hH S hfit ρ).2.2.2.1 0 (by decide) g j
    (fun q hq => by obtain ⟨hk, e⟩ := hUse_to hq; exact h q e)
  hHP_A3_1 := fun ρ g j => (z_A3_spec I Ic base l hbase hH S hfit ρ).2.1 1 (by decide) g j
  hHZ_A3_1 := fun ρ g q j h => by
    have hh := (z_A3_spec I Ic base l hbase hH S hfit ρ).2.2.1 1 (by decide) g q j (hUse_of (c := 2) (k0 := 0) (k := 1) (by decide) h)
    rw [entK_eq Ic ρ (0 + 1) (by decide)] at hh
    exact hh
  hHZn_A3_1 := fun ρ g j h => (z_A3_spec I Ic base l hbase hH S hfit ρ).2.2.2.1 1 (by decide) g j
    (fun q hq => by obtain ⟨hk, e⟩ := hUse_to hq; exact h q e)
  hHP_A3_2 := fun ρ g j => (z_A3_spec I Ic base l hbase hH S hfit ρ).2.1 2 (by decide) g j
  hHZ_A3_2 := fun ρ g q j h => by
    have hh := (z_A3_spec I Ic base l hbase hH S hfit ρ).2.2.1 2 (by decide) g q j (hUse_of (c := 2) (k0 := 0) (k := 2) (by decide) h)
    rw [entK_eq Ic ρ (0 + 2) (by decide)] at hh
    exact hh
  hHZn_A3_2 := fun ρ g j h => (z_A3_spec I Ic base l hbase hH S hfit ρ).2.2.2.1 2 (by decide) g j
    (fun q hq => by obtain ⟨hk, e⟩ := hUse_to hq; exact h q e)
  hHP_A3_3 := fun ρ g j => (z_A3_spec I Ic base l hbase hH S hfit ρ).2.1 3 (by decide) g j
  hHZ_A3_3 := fun ρ g q j h => by
    have hh := (z_A3_spec I Ic base l hbase hH S hfit ρ).2.2.1 3 (by decide) g q j (hUse_of (c := 2) (k0 := 0) (k := 3) (by decide) h)
    rw [entK_eq Ic ρ (0 + 3) (by decide)] at hh
    exact hh
  hHZn_A3_3 := fun ρ g j h => (z_A3_spec I Ic base l hbase hH S hfit ρ).2.2.2.1 3 (by decide) g j
    (fun q hq => by obtain ⟨hk, e⟩ := hUse_to hq; exact h q e)
  hHE_A3 := fun ρ g t => ⟨(z_A3_spec I Ic base l hbase hH S hfit ρ).2.2.2.2 g (false, t), (z_A3_spec I Ic base l hbase hH S hfit ρ).2.2.2.2 g (true, t)⟩
  hH0_B3 := fun ρ g t => ⟨(z_B3_spec I Ic base l hbase hH S hfit ρ).1 g (false, t), (z_B3_spec I Ic base l hbase hH S hfit ρ).1 g (true, t)⟩
  hHP_B3_4 := fun ρ g j => (z_B3_spec I Ic base l hbase hH S hfit ρ).2.1 0 (by decide) g j
  hHZ_B3_4 := fun ρ g q j h => by
    have hh := (z_B3_spec I Ic base l hbase hH S hfit ρ).2.2.1 0 (by decide) g q j (hUse_of (c := 3) (k0 := 4) (k := 0) (by decide) h)
    rw [entK_eq Ic ρ (4 + 0) (by decide)] at hh
    exact hh
  hHZn_B3_4 := fun ρ g j h => (z_B3_spec I Ic base l hbase hH S hfit ρ).2.2.2.1 0 (by decide) g j
    (fun q hq => by obtain ⟨hk, e⟩ := hUse_to hq; exact h q e)
  hHE_B3 := fun ρ g t => ⟨(z_B3_spec I Ic base l hbase hH S hfit ρ).2.2.2.2 g (false, t), (z_B3_spec I Ic base l hbase hH S hfit ρ).2.2.2.2 g (true, t)⟩
  hH0_A4 := fun ρ g t => ⟨(z_A4_spec I Ic base l hbase hH S hfit ρ).1 g (false, t), (z_A4_spec I Ic base l hbase hH S hfit ρ).1 g (true, t)⟩
  hHP_A4_0 := fun ρ g j => (z_A4_spec I Ic base l hbase hH S hfit ρ).2.1 0 (by decide) g j
  hHZ_A4_0 := fun ρ g q j h => by
    have hh := (z_A4_spec I Ic base l hbase hH S hfit ρ).2.2.1 0 (by decide) g q j (hUse_of (c := 4) (k0 := 0) (k := 0) (by decide) h)
    rw [entK_eq Ic ρ (0 + 0) (by decide)] at hh
    exact hh
  hHZn_A4_0 := fun ρ g j h => (z_A4_spec I Ic base l hbase hH S hfit ρ).2.2.2.1 0 (by decide) g j
    (fun q hq => by obtain ⟨hk, e⟩ := hUse_to hq; exact h q e)
  hHP_A4_1 := fun ρ g j => (z_A4_spec I Ic base l hbase hH S hfit ρ).2.1 1 (by decide) g j
  hHZ_A4_1 := fun ρ g q j h => by
    have hh := (z_A4_spec I Ic base l hbase hH S hfit ρ).2.2.1 1 (by decide) g q j (hUse_of (c := 4) (k0 := 0) (k := 1) (by decide) h)
    rw [entK_eq Ic ρ (0 + 1) (by decide)] at hh
    exact hh
  hHZn_A4_1 := fun ρ g j h => (z_A4_spec I Ic base l hbase hH S hfit ρ).2.2.2.1 1 (by decide) g j
    (fun q hq => by obtain ⟨hk, e⟩ := hUse_to hq; exact h q e)
  hHP_A4_2 := fun ρ g j => (z_A4_spec I Ic base l hbase hH S hfit ρ).2.1 2 (by decide) g j
  hHZ_A4_2 := fun ρ g q j h => by
    have hh := (z_A4_spec I Ic base l hbase hH S hfit ρ).2.2.1 2 (by decide) g q j (hUse_of (c := 4) (k0 := 0) (k := 2) (by decide) h)
    rw [entK_eq Ic ρ (0 + 2) (by decide)] at hh
    exact hh
  hHZn_A4_2 := fun ρ g j h => (z_A4_spec I Ic base l hbase hH S hfit ρ).2.2.2.1 2 (by decide) g j
    (fun q hq => by obtain ⟨hk, e⟩ := hUse_to hq; exact h q e)
  hHP_A4_3 := fun ρ g j => (z_A4_spec I Ic base l hbase hH S hfit ρ).2.1 3 (by decide) g j
  hHZ_A4_3 := fun ρ g q j h => by
    have hh := (z_A4_spec I Ic base l hbase hH S hfit ρ).2.2.1 3 (by decide) g q j (hUse_of (c := 4) (k0 := 0) (k := 3) (by decide) h)
    rw [entK_eq Ic ρ (0 + 3) (by decide)] at hh
    exact hh
  hHZn_A4_3 := fun ρ g j h => (z_A4_spec I Ic base l hbase hH S hfit ρ).2.2.2.1 3 (by decide) g j
    (fun q hq => by obtain ⟨hk, e⟩ := hUse_to hq; exact h q e)
  hHP_A4_4 := fun ρ g j => (z_A4_spec I Ic base l hbase hH S hfit ρ).2.1 4 (by decide) g j
  hHZ_A4_4 := fun ρ g q j h => by
    have hh := (z_A4_spec I Ic base l hbase hH S hfit ρ).2.2.1 4 (by decide) g q j (hUse_of (c := 4) (k0 := 0) (k := 4) (by decide) h)
    rw [entK_eq Ic ρ (0 + 4) (by decide)] at hh
    exact hh
  hHZn_A4_4 := fun ρ g j h => (z_A4_spec I Ic base l hbase hH S hfit ρ).2.2.2.1 4 (by decide) g j
    (fun q hq => by obtain ⟨hk, e⟩ := hUse_to hq; exact h q e)
  hHP_A4_5 := fun ρ g j => (z_A4_spec I Ic base l hbase hH S hfit ρ).2.1 5 (by decide) g j
  hHZ_A4_5 := fun ρ g q j h => by
    have hh := (z_A4_spec I Ic base l hbase hH S hfit ρ).2.2.1 5 (by decide) g q j (hUse_of (c := 4) (k0 := 0) (k := 5) (by decide) h)
    rw [entK_eq Ic ρ (0 + 5) (by decide)] at hh
    exact hh
  hHZn_A4_5 := fun ρ g j h => (z_A4_spec I Ic base l hbase hH S hfit ρ).2.2.2.1 5 (by decide) g j
    (fun q hq => by obtain ⟨hk, e⟩ := hUse_to hq; exact h q e)
  hHE_A4 := fun ρ g t => ⟨(z_A4_spec I Ic base l hbase hH S hfit ρ).2.2.2.2 g (false, t), (z_A4_spec I Ic base l hbase hH S hfit ρ).2.2.2.2 g (true, t)⟩
  hH0_B4 := fun ρ g t => ⟨(z_B4_spec I Ic base l hbase hH S hfit ρ).1 g (false, t), (z_B4_spec I Ic base l hbase hH S hfit ρ).1 g (true, t)⟩
  hHP_B4_6 := fun ρ g j => (z_B4_spec I Ic base l hbase hH S hfit ρ).2.1 0 (by decide) g j
  hHZ_B4_6 := fun ρ g q j h => by
    have hh := (z_B4_spec I Ic base l hbase hH S hfit ρ).2.2.1 0 (by decide) g q j (hUse_of (c := 5) (k0 := 6) (k := 0) (by decide) h)
    rw [entK_eq Ic ρ (6 + 0) (by decide)] at hh
    exact hh
  hHZn_B4_6 := fun ρ g j h => (z_B4_spec I Ic base l hbase hH S hfit ρ).2.2.2.1 0 (by decide) g j
    (fun q hq => by obtain ⟨hk, e⟩ := hUse_to hq; exact h q e)
  hHE_B4 := fun ρ g t => ⟨(z_B4_spec I Ic base l hbase hH S hfit ρ).2.2.2.2 g (false, t), (z_B4_spec I Ic base l hbase hH S hfit ρ).2.2.2.2 g (true, t)⟩
  hH0_F1 := fun ρ g t => ⟨(z_F1_spec I Ic base l hbase hH S hfit ρ).1 g (false, t), (z_F1_spec I Ic base l hbase hH S hfit ρ).1 g (true, t)⟩
  hHP_F1_3 := fun ρ g j => (z_F1_spec I Ic base l hbase hH S hfit ρ).2.1 0 (by decide) g j
  hHZ_F1_3 := fun ρ g q j h => by
    have hh := (z_F1_spec I Ic base l hbase hH S hfit ρ).2.2.1 0 (by decide) g q j (hUse_of (c := 6) (k0 := 3) (k := 0) (by decide) h)
    rw [entK_eq Ic ρ (3 + 0) (by decide)] at hh
    exact hh
  hHZn_F1_3 := fun ρ g j h => (z_F1_spec I Ic base l hbase hH S hfit ρ).2.2.2.1 0 (by decide) g j
    (fun q hq => by obtain ⟨hk, e⟩ := hUse_to hq; exact h q e)
  hHP_F1_4 := fun ρ g j => (z_F1_spec I Ic base l hbase hH S hfit ρ).2.1 1 (by decide) g j
  hHZ_F1_4 := fun ρ g q j h => by
    have hh := (z_F1_spec I Ic base l hbase hH S hfit ρ).2.2.1 1 (by decide) g q j (hUse_of (c := 6) (k0 := 3) (k := 1) (by decide) h)
    rw [entK_eq Ic ρ (3 + 1) (by decide)] at hh
    exact hh
  hHZn_F1_4 := fun ρ g j h => (z_F1_spec I Ic base l hbase hH S hfit ρ).2.2.2.1 1 (by decide) g j
    (fun q hq => by obtain ⟨hk, e⟩ := hUse_to hq; exact h q e)
  hHP_F1_5 := fun ρ g j => (z_F1_spec I Ic base l hbase hH S hfit ρ).2.1 2 (by decide) g j
  hHZ_F1_5 := fun ρ g q j h => by
    have hh := (z_F1_spec I Ic base l hbase hH S hfit ρ).2.2.1 2 (by decide) g q j (hUse_of (c := 6) (k0 := 3) (k := 2) (by decide) h)
    rw [entK_eq Ic ρ (3 + 2) (by decide)] at hh
    exact hh
  hHZn_F1_5 := fun ρ g j h => (z_F1_spec I Ic base l hbase hH S hfit ρ).2.2.2.1 2 (by decide) g j
    (fun q hq => by obtain ⟨hk, e⟩ := hUse_to hq; exact h q e)
  hHP_F1_6 := fun ρ g j => (z_F1_spec I Ic base l hbase hH S hfit ρ).2.1 3 (by decide) g j
  hHZ_F1_6 := fun ρ g q j h => by
    have hh := (z_F1_spec I Ic base l hbase hH S hfit ρ).2.2.1 3 (by decide) g q j (hUse_of (c := 6) (k0 := 3) (k := 3) (by decide) h)
    rw [entK_eq Ic ρ (3 + 3) (by decide)] at hh
    exact hh
  hHZn_F1_6 := fun ρ g j h => (z_F1_spec I Ic base l hbase hH S hfit ρ).2.2.2.1 3 (by decide) g j
    (fun q hq => by obtain ⟨hk, e⟩ := hUse_to hq; exact h q e)
  hHP_F1_7 := fun ρ g j => (z_F1_spec I Ic base l hbase hH S hfit ρ).2.1 4 (by decide) g j
  hHZ_F1_7 := fun ρ g q j h => by
    have hh := (z_F1_spec I Ic base l hbase hH S hfit ρ).2.2.1 4 (by decide) g q j (hUse_of (c := 6) (k0 := 3) (k := 4) (by decide) h)
    rw [entK_eq Ic ρ (3 + 4) (by decide)] at hh
    exact hh
  hHZn_F1_7 := fun ρ g j h => (z_F1_spec I Ic base l hbase hH S hfit ρ).2.2.2.1 4 (by decide) g j
    (fun q hq => by obtain ⟨hk, e⟩ := hUse_to hq; exact h q e)
  hHP_F1_8 := fun ρ g j => (z_F1_spec I Ic base l hbase hH S hfit ρ).2.1 5 (by decide) g j
  hHZ_F1_8 := fun ρ g q j h => by
    have hh := (z_F1_spec I Ic base l hbase hH S hfit ρ).2.2.1 5 (by decide) g q j (hUse_of (c := 6) (k0 := 3) (k := 5) (by decide) h)
    rw [entK_eq Ic ρ (3 + 5) (by decide)] at hh
    exact hh
  hHZn_F1_8 := fun ρ g j h => (z_F1_spec I Ic base l hbase hH S hfit ρ).2.2.2.1 5 (by decide) g j
    (fun q hq => by obtain ⟨hk, e⟩ := hUse_to hq; exact h q e)
  hHE_F1 := fun ρ g t => ⟨(z_F1_spec I Ic base l hbase hH S hfit ρ).2.2.2.2 g (false, t), (z_F1_spec I Ic base l hbase hH S hfit ρ).2.2.2.2 g (true, t)⟩
  hH0_F2 := fun ρ g t => ⟨(z_F2_spec I Ic base l hbase hH S hfit ρ).1 g (false, t), (z_F2_spec I Ic base l hbase hH S hfit ρ).1 g (true, t)⟩
  hHP_F2_5 := fun ρ g j => (z_F2_spec I Ic base l hbase hH S hfit ρ).2.1 0 (by decide) g j
  hHZ_F2_5 := fun ρ g q j h => by
    have hh := (z_F2_spec I Ic base l hbase hH S hfit ρ).2.2.1 0 (by decide) g q j (hUse_of (c := 7) (k0 := 5) (k := 0) (by decide) h)
    rw [entK_eq Ic ρ (5 + 0) (by decide)] at hh
    exact hh
  hHZn_F2_5 := fun ρ g j h => (z_F2_spec I Ic base l hbase hH S hfit ρ).2.2.2.1 0 (by decide) g j
    (fun q hq => by obtain ⟨hk, e⟩ := hUse_to hq; exact h q e)
  hHP_F2_6 := fun ρ g j => (z_F2_spec I Ic base l hbase hH S hfit ρ).2.1 1 (by decide) g j
  hHZ_F2_6 := fun ρ g q j h => by
    have hh := (z_F2_spec I Ic base l hbase hH S hfit ρ).2.2.1 1 (by decide) g q j (hUse_of (c := 7) (k0 := 5) (k := 1) (by decide) h)
    rw [entK_eq Ic ρ (5 + 1) (by decide)] at hh
    exact hh
  hHZn_F2_6 := fun ρ g j h => (z_F2_spec I Ic base l hbase hH S hfit ρ).2.2.2.1 1 (by decide) g j
    (fun q hq => by obtain ⟨hk, e⟩ := hUse_to hq; exact h q e)
  hHP_F2_7 := fun ρ g j => (z_F2_spec I Ic base l hbase hH S hfit ρ).2.1 2 (by decide) g j
  hHZ_F2_7 := fun ρ g q j h => by
    have hh := (z_F2_spec I Ic base l hbase hH S hfit ρ).2.2.1 2 (by decide) g q j (hUse_of (c := 7) (k0 := 5) (k := 2) (by decide) h)
    rw [entK_eq Ic ρ (5 + 2) (by decide)] at hh
    exact hh
  hHZn_F2_7 := fun ρ g j h => (z_F2_spec I Ic base l hbase hH S hfit ρ).2.2.2.1 2 (by decide) g j
    (fun q hq => by obtain ⟨hk, e⟩ := hUse_to hq; exact h q e)
  hHP_F2_8 := fun ρ g j => (z_F2_spec I Ic base l hbase hH S hfit ρ).2.1 3 (by decide) g j
  hHZ_F2_8 := fun ρ g q j h => by
    have hh := (z_F2_spec I Ic base l hbase hH S hfit ρ).2.2.1 3 (by decide) g q j (hUse_of (c := 7) (k0 := 5) (k := 3) (by decide) h)
    rw [entK_eq Ic ρ (5 + 3) (by decide)] at hh
    exact hh
  hHZn_F2_8 := fun ρ g j h => (z_F2_spec I Ic base l hbase hH S hfit ρ).2.2.2.1 3 (by decide) g j
    (fun q hq => by obtain ⟨hk, e⟩ := hUse_to hq; exact h q e)
  hHE_F2 := fun ρ g t => ⟨(z_F2_spec I Ic base l hbase hH S hfit ρ).2.2.2.2 g (false, t), (z_F2_spec I Ic base l hbase hH S hfit ρ).2.2.2.2 g (true, t)⟩
  hH0_F3 := fun ρ g t => ⟨(z_F3_spec I Ic base l hbase hH S hfit ρ).1 g (false, t), (z_F3_spec I Ic base l hbase hH S hfit ρ).1 g (true, t)⟩
  hHP_F3_7 := fun ρ g j => (z_F3_spec I Ic base l hbase hH S hfit ρ).2.1 0 (by decide) g j
  hHZ_F3_7 := fun ρ g q j h => by
    have hh := (z_F3_spec I Ic base l hbase hH S hfit ρ).2.2.1 0 (by decide) g q j (hUse_of (c := 8) (k0 := 7) (k := 0) (by decide) h)
    rw [entK_eq Ic ρ (7 + 0) (by decide)] at hh
    exact hh
  hHZn_F3_7 := fun ρ g j h => (z_F3_spec I Ic base l hbase hH S hfit ρ).2.2.2.1 0 (by decide) g j
    (fun q hq => by obtain ⟨hk, e⟩ := hUse_to hq; exact h q e)
  hHP_F3_8 := fun ρ g j => (z_F3_spec I Ic base l hbase hH S hfit ρ).2.1 1 (by decide) g j
  hHZ_F3_8 := fun ρ g q j h => by
    have hh := (z_F3_spec I Ic base l hbase hH S hfit ρ).2.2.1 1 (by decide) g q j (hUse_of (c := 8) (k0 := 7) (k := 1) (by decide) h)
    rw [entK_eq Ic ρ (7 + 1) (by decide)] at hh
    exact hh
  hHZn_F3_8 := fun ρ g j h => (z_F3_spec I Ic base l hbase hH S hfit ρ).2.2.2.1 1 (by decide) g j
    (fun q hq => by obtain ⟨hk, e⟩ := hUse_to hq; exact h q e)
  hHE_F3 := fun ρ g t => ⟨(z_F3_spec I Ic base l hbase hH S hfit ρ).2.2.2.2 g (false, t), (z_F3_spec I Ic base l hbase hH S hfit ρ).2.2.2.2 g (true, t)⟩
  fX4 := fun g t => g401geom_fX4 I base l hbase hH g t
  fY4 := fun g t => g401geom_fY4 I base l hbase hH g t
  term := fun g t => g401geom_term I base l hbase g t

end Net

section End
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]

/-- the price of the remaining climbs of kind `c` (both sides, all classes). -/
def hcostS {Sl T : Type} [Fintype Sl] [Fintype T] (S : HostSchedR Sl T) (ρ : Fin 8) (c : Fin 9) (φ : ℕ → ℝ) : ℝ :=
  ∑ t : T, (bcost φ (S.hrem ρ c (false, t)) + bcost φ (S.hrem ρ c (true, t)))

/-- **the unit price of the hosted word**: its 72 calls (each its own provider's price), the remaining climbs of each of the 8 runs, one pad per bank. -/
def unitPriceHost (Ic : Fin 8 → Fin 9 → GInvE H T Sl C) (S : HostSchedR Sl T) (φ : ℕ → ℝ) : ℝ :=
  (∑ ρ : Fin 8, ((Ic ρ 0).cost φ + (Ic ρ 1).cost φ + (Ic ρ 2).cost φ + (Ic ρ 3).cost φ + (Ic ρ 4).cost φ + (Ic ρ 5).cost φ + (Ic ρ 6).cost φ + (Ic ρ 7).cost φ + (Ic ρ 8).cost φ)) + (∑ ρ : Fin 8, (hcostS S ρ 0 φ + hcostS S ρ 1 φ + hcostS S ρ 2 φ + hcostS S ρ 3 φ + hcostS S ρ 4 φ
    + hcostS S ρ 5 φ + hcostS S ρ 6 φ + hcostS S ρ 7 φ + hcostS S ρ 8 φ)) + ∑ b, bcost φ (S.pad b)

/-- **Generalised certificate of the HOSTED nine-stage word** for a gauged invocation package and a host schedule. -/
theorem bridgeHost_gcert (I : GInvE H T Sl C) (Ic : Fin 8 → Fin 9 → GInvE H T Sl C)
    (hIc : ∀ ρ l, (Ic ρ l).tv = I.tv) (hH : Fintype.card H = 9) (l : H) (S : HostSchedR Sl T)
    (hfit : fitsRK S (rK Ic)) :
    GCert (BC.LC (Fin 8) H l)
      (Sum.inl : BLive401 (Orth (BC.LC (Fin 8) H l)) T S.nb → BRole401 (Orth (BC.LC (Fin 8) H l)) T S.nb C)
      (fun φ => (Fintype.card (Orth (BC.LC (Fin 8) H l)) : ℝ) * unitPriceHost Ic S φ) := by
  have hb : ∀ t, ∃ A : OBase H, I.tv t = A.v l :=
    fun t => base_ex (I.tv t) (I.hunit t) (I.hgap t) l
  choose base hbase using hb
  have hc := ghost_certificate (ghostGeom I Ic hIc base l hbase hH S hfit)
  have e : (fun φ => (Fintype.card (Orth (BC.LC (Fin 8) H l)) : ℝ)
        * (ghostGeom I Ic hIc base l hbase hH S hfit).unit φ)
      = (fun φ => (Fintype.card (Orth (BC.LC (Fin 8) H l)) : ℝ) * unitPriceHost Ic S φ) := by
    funext φ
    simp only [GHost401.unit, GHost401.runUnit, GHost401.hcost, ghostGeom, unitPriceHost, hcostS, bcost_zero,
      add_zero, mul_zero, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_ofNat]
    try ring
  rw [e] at hc
  exact hc

end End
end
end XHostD
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.XHostD.ghostGeom
#print axioms OAI.PowerSaving.XHostD.bridgeHost_gcert

