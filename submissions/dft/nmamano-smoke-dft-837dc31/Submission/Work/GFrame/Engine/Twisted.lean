import Submission.Work.GFrame.Engine.FreeLift
import Submission.Work.GFrame.Engine.Sweep

/-!
# GFrame engine, part 13: a twisted block in the RAM (agent key: eng-ram)

The RAM statement that the sketch `Rig.open_tblockB_sketch`
(`Work/FrameLemma/fl_engine/EngineSketch.lean`) asked for, now proved:

* `GRig.open_gstep`   any generalised word that acts on one role by the matrix `U` runs at the
                      price of its blocks (free adapters: linear work only);
* `GRig.open_tblock`  **one twisted block** `S.lift (L * kernel (Fin rk) * R')`, `L`, `R'` free
                      matrices of the fibre: ONE family of recursive calls of order `rk * f`,
                      `n rk` batches at `τ rk` each (the cost of `Rig.open_blockB`), plus
                      linear work;
* `GRig.open_factor`  the same for `A * blockMat z * B` with `A`, `B` free on the label space
                      (the form of the frame lemma for degenerate subspaces).
-/

set_option linter.unusedSectionVars false

namespace OAI
namespace PowerSaving.GF
open Binary Matrix Finset RAM
section
variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

/-- A word whose price is `φ rk` for every real price list costs `g rk` for every natural one. -/
lemma GWord.cost_of_costR (w : GWord α ρ) (rk : ℕ) (h : ∀ φ : ℕ → ℝ, w.costR φ = φ rk)
    (g : ℕ → ℕ) : w.cost g = g rk := by
  have h1 : ((w.cost g : ℕ) : ℝ) = w.costR (fun r => (g r : ℝ)) := by
    rw [GWord.costR_shadow]
    exact BWord.cost_cast g w.shadow
  rw [h] at h1
  exact_mod_cast h1

end
end PowerSaving.GF

namespace PowerSaving.RAM
open Binary Matrix Ty Finset GF
noncomputable section
universe U
variable {α β ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype ρ] [DecidableEq ρ]
variable {ι : Type U}
variable {m : Bool} {f : ι → ℕ} {s : Ty} {x : ι → T s}
    {cl : Paint} {X : Layout α} {R : Layout ρ} {r : ℕ} {v : ∀ i, Grain α ρ r (f i)}
    {b : Bank (hatch cl) ι}

namespace GRig
variable (h : GRig m b.B f s x cl X R r v)
include h

omit [Fintype β] [DecidableEq β] in
/-- A generalised word acting on role `l` by the matrix `U`, run in the RAM. -/
lemma open_gstep (n τ : ℕ → ι → ℕ) (Q : Layout σ) (hQ : 0<Q.n)
    (hk : ∀ rk, 1 ≤ rk → rk < X.n → Contract cl b (fun i => rk * f i) (τ rk) Q)
    (hg : ∀ rk, 1 ≤ rk → rk < X.n → ∀ i,
      n rk i*(sim Q (rk * f i)).n=(book X r (f i)).n)
    (l : ρ) (U : CMat α) (w : GWord α ρ) (hw : w.Proper X.n)
    (hwalk : ∀ (f : ℕ) (y : Data α ρ f), gwalk f w y = roleAct f l U y) :
    Able m b s (bundle cl) x
      (fun i => (fleet X R r (f i)).tape (ferryM r (f i) l U (v i)))
      (fun i => (fleet X R r (f i)).n)
      (fun i => w.cost (fun rk => n rk i * τ rk i)) := by
  refine (h.gsweep n τ Q hQ hk hg w hw).cong (fun _ => rfl) (fun i => ?_)
  congr 1
  funext y
  unfold gcoast ferryM
  rw [hwalk]

/-- **One twisted block in the RAM**: one family of recursive calls of order `rk * f`
(`n rk` batches, `τ rk` each), exactly the cost of `Rig.open_blockB`, plus linear work for
the two adapters of the fibre. -/
theorem open_tblock (n τ : ℕ → ι → ℕ) (Q : Layout σ) (hQ : 0<Q.n)
    (hk : ∀ rk, 1 ≤ rk → rk < X.n → Contract cl b (fun i => rk * f i) (τ rk) Q)
    (hg : ∀ rk, 1 ≤ rk → rk < X.n → ∀ i,
      n rk i*(sim Q (rk * f i)).n=(book X r (f i)).n)
    (l : ρ) {rk : ℕ} (S : Split α β (Fin rk)) {L R' : CMat (Fin rk)}
    (hL : Free L) (hR : Free R') (h1 : 1 ≤ rk) (h2 : rk < X.n) :
    Able m b s (bundle cl) x
      (fun i => (fleet X R r (f i)).tape
        (ferryM r (f i) l (S.lift (L * kernel (Fin rk) * R')) (v i)))
      (fun i => (fleet X R r (f i)).n) (fun i => n rk i * τ rk i) := by
  have hc : Fintype.card α = X.n := Layout.card X
  obtain ⟨w, U, hw, hcost, hU, hwalk⟩ :=
    gstep_twisted (ρ:=ρ) l (1 : CMat α) S hL hR h1 (hc ▸ h2)
  rw [mul_one, mul_one] at hU
  subst hU
  have H := h.open_gstep n τ Q hQ hk hg l _ w (hc ▸ hw) hwalk
  refine H.mono (fun _ => le_rfl) (fun i => le_of_eq ?_)
  exact GWord.cost_of_costR w rk hcost _

omit [Fintype β] [DecidableEq β] in
/-- **The frame-lemma step in the RAM**: `A * blockMat z * B` with `A`, `B` free on the label
space is one family of recursive calls of order `rk * f` plus linear work. -/
theorem open_factor (n τ : ℕ → ι → ℕ) (Q : Layout σ) (hQ : 0<Q.n)
    (hk : ∀ rk, 1 ≤ rk → rk < X.n → Contract cl b (fun i => rk * f i) (τ rk) Q)
    (hg : ∀ rk, 1 ≤ rk → rk < X.n → ∀ i,
      n rk i*(sim Q (rk * f i)).n=(book X r (f i)).n)
    (l : ρ) {rk : ℕ} (z : Fin rk → Space α) (ind : LinearIndependent F z) {A B : CMat α}
    (hA : Free A) (hB : Free B) (h1 : 1 ≤ rk) (h2 : rk < X.n) :
    Able m b s (bundle cl) x
      (fun i => (fleet X R r (f i)).tape (ferryM r (f i) l (A * blockMat z * B) (v i)))
      (fun i => (fleet X R r (f i)).n) (fun i => n rk i * τ rk i) := by
  have hc : Fintype.card α = X.n := Layout.card X
  obtain ⟨w, U, hw, hcost, hU, hwalk⟩ :=
    gstep_of_factor (ρ:=ρ) l (1 : CMat α) z ind hA hB h1 (hc ▸ h2)
  rw [mul_one, mul_one] at hU
  subst hU
  have H := h.open_gstep n τ Q hQ hk hg l _ w (hc ▸ hw) hwalk
  refine H.mono (fun _ => le_rfl) (fun i => le_of_eq ?_)
  exact GWord.cost_of_costR w rk hcost _

end GRig
end
end PowerSaving.RAM
end OAI

#print axioms OAI.PowerSaving.RAM.GRig.open_gstep
#print axioms OAI.PowerSaving.RAM.GRig.open_tblock
#print axioms OAI.PowerSaving.RAM.GRig.open_factor
