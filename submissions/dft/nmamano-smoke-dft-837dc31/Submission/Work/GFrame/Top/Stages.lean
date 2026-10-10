import Submission.Work.GFrame.Top.Menu

/-!
# GFrame, top (key: eng-integrate): every label calculus feeds the assembled theorem

The assembled theorem (`RAM.engine_program_gsched`, `Top/Assemble.lean`) asks for
`GSchedOkR (gcalc α) Φ lab l`.  Each label calculus of LABELS reduces to it:

* `oldSchedOkR`   the OLD calculus (`CR.SchedOk`, `SS.Lbl`, `Climb`, `Mv`): existing
                  certificates keep working, same ranks, same scalar map;
* `aschedOkR`     stage A (`ASchedOk`: orthonormal-type and alternating nested steps, frames
                  Walsh-diagonal, any `GXMap`);
* `bschedOkR`     stage B (`BSchedOk`: arbitrary subspaces with exact representatives on the
                  address space);
* `hschedOkR`     stage B through a frame map `BXMap H α` (label space ≠ address space).

Headline for stage B on the address space (`engine_program_bsched`, `wht_main_of_bsched`):
every role starts on the zero subspace (frame `1`), every live role ends on a label whose
representative is the kernel; gates only between identical representatives.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving

namespace GF
open Binary Matrix Finset RAM CB SS
noncomputable section
section
variable {H α ρ σ : Type} [Fintype H] [DecidableEq H] [Fintype α] [DecidableEq α]
  [Fintype ρ] [DecidableEq ρ]

/-- the OLD label calculus embeds: an old legal schedule is a legal generalised schedule. -/
theorem oldSchedOkR (X : GXMap H α) (lab : ρ → Lbl H) (l : List (CR.Step H ρ))
    (h : CR.SchedOk lab l) :
    GSchedOkR (gcalc α) (fun U : Lbl H => X.Φ U.P) lab (emb lab l) :=
  GSchedOk.toR (K := gcalc α) (Φ := fun U : Lbl H => X.Φ U.P) (emb lab l) lab
    (emb_ok X (gcalc α) lab l h)

/-- stage A: nested steps with orthonormal-type or alternating residual. -/
theorem aschedOkR (X : GXMap H α) (lab : ρ → Lbl H) (l : List (GSt (Lbl H) ρ))
    (h : ASchedOk (fun p => [2 * p]) lab l) :
    GSchedOkR (gcalc α) (fun U : Lbl H => X.Φ U.P) lab l :=
  GSchedOk.toR (K := gcalc α) (Φ := fun U : Lbl H => X.Φ U.P) l lab
    (asched_ok X (K := gcalc α) (ar := fun p => [2 * p]) altAt_gcalc lab l h)

/-- stage B: arbitrary subspaces of the address space with exact representatives. -/
theorem bschedOkR (lab : ρ → SLbl α) (l : List (GSt (SLbl α) ρ)) (h : BSchedOk lab l) :
    GSchedOkR (gcalc α) (SLbl.rep (α := α)) lab l :=
  GSchedOk.toR (K := gcalc α) (Φ := SLbl.rep (α := α)) l lab (bsched_ok (repChange α) lab l h)

/-- stage B through a frame map. -/
theorem hschedOkR (X : BXMap H α) (lab : ρ → SLbl H) (l : List (GSt (SLbl H) ρ))
    (h : HSchedOk X lab l) : GSchedOkR (gcalc α) X.Φ lab l :=
  GSchedOk.toR (K := gcalc α) (Φ := X.Φ) l lab (hsched_ok X lab l h)

/-- **Stage B kernel schedule**: every role starts on the zero subspace and every live role
ends on a label whose representative is the kernel (for instance `⟨apId α, univ⟩`, or any
representative of the full space after a free `rebase`). -/
theorem kernelSched_B (lab : ρ → SLbl α) (l : List (GSt (SLbl α) ρ)) (e : σ → ρ)
    (h0 : ∀ r, (lab r).s = ∅)
    (hfix : ∀ x : ρ → ℂ, (∀ s, (∀ t, e t ≠ s) → x s = 0) →
      ∀ t, gschedAct l x (e t) = x (e t))
    (hend : ∀ t, (gschedOut lab l (e t)).rep = kernel α) :
    KernelSched (SLbl.rep (α := α)) lab l e := by
  have h1 : ∀ r, (lab r).rep = 1 := fun r => by
    unfold SLbl.rep
    rw [h0 r]
    exact core_empty _
  exact ⟨fun r => ⟨1, by rw [h1 r, Matrix.mul_one]⟩, hfix,
    fun t => by rw [hend t, h1, Matrix.mul_one]⟩

/-- stage B certificate. -/
theorem gcert_of_bsched (lab : ρ → SLbl α) (l : List (GSt (SLbl α) ρ)) (h : BSchedOk lab l)
    (e : σ → ρ) (h0 : ∀ r, (lab r).s = ∅)
    (hfix : ∀ x : ρ → ℂ, (∀ s, (∀ t, e t ≠ s) → x s = 0) →
      ∀ t, gschedAct l x (e t) = x (e t))
    (hend : ∀ t, (gschedOut lab l (e t)).rep = kernel α) :
    GCert α e (fun φ => rcost φ (gschedRanks l)) :=
  gcert_of_sched (SLbl.rep (α := α)) l lab (bschedOkR lab l h) e
    (kernelSched_B lab l e h0 hfix hend)

end
end
end GF

namespace RAM
open Binary Matrix Ty Finset FoldRate GF CB
universe V

/-- **Stage B, engine.**  A schedule on ARBITRARY subspace labels (degenerate and isotropic
ones included), legal at label level, from the zero subspace to the kernel on `G * W` live
roles, gives the program of the block engine under the unchanged numeric hypothesis. -/
theorem engine_program_bsched {α ρ σ : Type} [Fintype α] [DecidableEq α] [Fintype ρ]
    [DecidableEq ρ] [Fintype σ] [DecidableEq σ]
    (u : ℕ) (hα : Fintype.card α = u) (hu : 3 ≤ u)
    (lab : ρ → SLbl α) (l : List (GSt (SLbl α) ρ)) (h : BSchedOk lab l)
    (e : σ → ρ) (he : Function.Injective e) (h0 : ∀ r, (lab r).s = ∅)
    (hfix : ∀ x : ρ → ℂ, (∀ s, (∀ t, e t ≠ s) → x s = 0) →
      ∀ t, gschedAct l x (e t) = x (e t))
    (hend : ∀ t, (gschedOut lab l (e t)).rep = kernel α)
    (G W : ℕ) (hG : 1 ≤ G) (hW : 1 ≤ W) (hσ : Fintype.card σ = G * W)
    (U : List (ℕ × ℕ)) (hc : ∀ φ, rcost φ (gschedRanks l) = (G:ℝ) * listCost φ U)
    (s : ℕ) (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hnum : ((2:ℝ)^s - 1) * BlockAccounting.moment u z U
        + (W:ℝ) * (BlockAccounting.T u z (u - 1) 1 + BlockAccounting.T u z 1 1)
        < (2:ℝ)^s * (W:ℝ))
    (cl : Paint) (m : Bool) {ι : Type V} (k : ι→ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*envelope z (k i)) :=
  engine_program_gsched u hα hu (SLbl.rep (α := α)) l lab (bschedOkR lab l h) e he
    (kernelSched_B lab l e h0 hfix hend) G W hG hW hσ U hc s z hz hz1 hnum cl m k v

end RAM

namespace BlockWHT
open RAM Binary FoldRate GF CB

/-- **Stage B, Walsh-Hadamard transform.** -/
theorem wht_main_of_bsched {α ρ σ : Type} [Fintype α] [DecidableEq α] [Fintype ρ]
    [DecidableEq ρ] [Fintype σ] [DecidableEq σ]
    (u : ℕ) (hα : Fintype.card α = u) (hu : 3 ≤ u)
    (lab : ρ → SLbl α) (l : List (GSt (SLbl α) ρ)) (h : BSchedOk lab l)
    (e : σ → ρ) (he : Function.Injective e) (h0 : ∀ r, (lab r).s = ∅)
    (hfix : ∀ x : ρ → ℂ, (∀ s, (∀ t, e t ≠ s) → x s = 0) →
      ∀ t, gschedAct l x (e t) = x (e t))
    (hend : ∀ t, (gschedOut lab l (e t)).rep = kernel α)
    (G W : ℕ) (hG : 1 ≤ G) (hW : 1 ≤ W) (hσ : Fintype.card σ = G * W)
    (U : List (ℕ × ℕ)) (hc : ∀ φ, rcost φ (gschedRanks l) = (G:ℝ) * listCost φ U)
    (s : ℕ) (z : ℝ) (hz : 0 ≤ z) (hz1 : z < 1)
    (hnum : ((2:ℝ)^s - 1) * BlockAccounting.moment u z U
        + (W:ℝ) * (BlockAccounting.T u z (u - 1) 1 + BlockAccounting.T u z 1 1)
        < (2:ℝ)^s * (W:ℝ)) :
    ∃ solve W', WHT.WHTProgram solve W' ∧ WHTTimeBoundsAt z W' :=
  wht_main_of_gsched u hα hu (SLbl.rep (α := α)) l lab (bschedOkR lab l h) e he
    (kernelSched_B lab l e h0 hfix hend) G W hG hW hσ U hc s z hz hz1 hnum

end BlockWHT
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.GF.oldSchedOkR
#print axioms OAI.PowerSaving.GF.aschedOkR
#print axioms OAI.PowerSaving.GF.bschedOkR
#print axioms OAI.PowerSaving.GF.hschedOkR
#print axioms OAI.PowerSaving.GF.gcert_of_bsched
#print axioms OAI.PowerSaving.RAM.engine_program_bsched
#print axioms OAI.PowerSaving.BlockWHT.wht_main_of_bsched
