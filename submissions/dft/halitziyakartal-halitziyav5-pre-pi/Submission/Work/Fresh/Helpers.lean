import Submission.Work.XHostD.FramesK
import Submission.Work.Mixed.HeadM1
-- changed for the tensor-power extension (30103/10000000); see Submission.lean

/-!
# Fresh productive helpers: frames and the live certificate (obligation O1)

A FRESH helper is a live role of its own.  It serves as the slot of native calls (normally ONE call: one sub-stage),
takes the residual `Wn` of that slot, and is then finished by ONE remnant block, so that it ends at the partial
transform `pk D = blockMat (lines of D)` of its OWN input, `|D|` its target rank (for the p3/p4 units: `max 6 width`).
This is the productive-helper contract of CrocSwap/integer-mult-bounds #4359 in the leader's frame language; the only
difference with a bank (Work/Bank401) is that the end frame is `pk D` instead of `kernel α = pk univ`, and with a host
(Work/XHost) that the start frame is `1`.

* `hostForm_fresh`        `HostForm 1 (pk D) |D|`;
* `fresh_frames`          `XHostD.host_framesK` for a family `J` of fresh helpers, with the use `use k q` of slot `q` in
                          sub-stage `k`, residuals `r k q`, gauged residual matrices `Wn` (`C * pk R * C'`, `C`, `C'`
                          free, `|R| = r k q`) and targets `D j`: frames `Zb`/`Zp` from `1`: free adapters, the hosted
                          residuals, and ONE remnant block of rank `|D j| - load` ending at `pk (D j)`;
* `fresh_frames_card`     the same with `|D j| = max L (load j)` (the targets of the p3/p4 units, `L = 6`);
* `GRoute.liveKernelM`    a route whose live roles end at `Targ l * (start frame)` gives the MIXED certificate
                          `GLiveKernelM e Targ w` (the leader's `GRoute.liveKernel` is the case `Targ = kernel α`);
* `targ`, `targ_indep`, `pk_eq_targ`, `targ_card`   the target of a fresh helper as a legal block (`|D|` lines).

Everything is parametric in the helper table (`use`, `r`, `Wn`, `D`); nothing depends on a particular unit.
No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace FH
open Binary Matrix Finset GF CB B401 XHost XHostD

noncomputable section

section Target
variable {α : Type} [Fintype α] [DecidableEq α]

/-- the target lines of a fresh helper with target set `D` (the canonical lines of `D`). -/
def targ (D : Finset α) : Fin D.card → Space α := (OBase.canonical α).fam D

lemma targ_indep (D : Finset α) : LinearIndependent F (targ D) := OBase.fam_indep _ D

lemma pk_eq_targ (D : Finset α) : pk D = blockMat (targ D) := pk_eq_blockMat D

/-- **a fresh helper is a host whose idle climb is `1 → pk D`.** -/
theorem hostForm_fresh (D : Finset α) : HostForm (1 : CMat α) (pk D) D.card :=
  ⟨1, 1, D, Free.one, Free.one, rfl, by simp⟩

end Target

section Frames
variable {α Γ Sl J : Type} [Fintype α] [DecidableEq α] [Fintype Sl] [DecidableEq Sl] [DecidableEq J]

/-- **The frames of a family of fresh helpers.**  Helper `j` starts at `1`; every use adds the (gauged) residual of
the slot; the end is ONE block of rank `|D j| - load j`, at `pk (D j)`. -/
theorem fresh_frames (use : ℕ → Sl → Option J) (r : ℕ → Sl → ℕ) (Wn : ℕ → Γ → Sl → CMat α) (K : ℕ)
    (hinj : ∀ k < K, OneUseK use k)
    (hWn : ∀ k < K, ∀ d q, ∃ (C C' : CMat α) (R : Finset α), Free C ∧ Free C' ∧ R.card = r k q ∧
      Wn k d q = C * pk R * C')
    (D : J → Finset α) (hload : ∀ j, LHK use r K j ≤ (D j).card)
    (hrk : ∀ j, (D j).card - LHK use r K j < Fintype.card α) :
    ∃ (Zb Zp : ℕ → Γ → J → CMat α),
      (∀ d j, Zb 0 d j = 1) ∧
      (∀ k < K, ∀ d j, GReach (Zb k d j) (Zp k d j) (fun _ => 0)) ∧
      (∀ k < K, ∀ d q j, use k q = some j → Wn k d q * Zp k d j = Zb (k + 1) d j) ∧
      (∀ k < K, ∀ d j, (∀ q, use k q ≠ some j) → Zb (k + 1) d j = Zp k d j) ∧
      (∀ d j, GReach (Zb K d j) (pk (D j)) (fun φ => bcost φ ((D j).card - LHK use r K j))) :=
  host_framesK use r Wn K hinj hWn (fun _ _ => 1) (fun _ j => pk (D j)) (fun j => (D j).card)
    (fun _ j => hostForm_fresh (D j)) hload hrk

/-- the same with the targets of the p3/p4 units: `|D j| = max L (load j)`, so the remnant (the top-up) is
`max L load - load`. -/
theorem fresh_frames_card (use : ℕ → Sl → Option J) (r : ℕ → Sl → ℕ) (Wn : ℕ → Γ → Sl → CMat α) (K : ℕ)
    (hinj : ∀ k < K, OneUseK use k)
    (hWn : ∀ k < K, ∀ d q, ∃ (C C' : CMat α) (R : Finset α), Free C ∧ Free C' ∧ R.card = r k q ∧
      Wn k d q = C * pk R * C')
    (L : ℕ) (D : J → Finset α) (hD : ∀ j, (D j).card = max L (LHK use r K j))
    (hα : ∀ j, max L (LHK use r K j) - LHK use r K j < Fintype.card α) :
    ∃ (Zb Zp : ℕ → Γ → J → CMat α),
      (∀ d j, Zb 0 d j = 1) ∧
      (∀ k < K, ∀ d j, GReach (Zb k d j) (Zp k d j) (fun _ => 0)) ∧
      (∀ k < K, ∀ d q j, use k q = some j → Wn k d q * Zp k d j = Zb (k + 1) d j) ∧
      (∀ k < K, ∀ d j, (∀ q, use k q ≠ some j) → Zb (k + 1) d j = Zp k d j) ∧
      (∀ d j, GReach (Zb K d j) (pk (D j)) (fun φ => bcost φ (max L (LHK use r K j) - LHK use r K j))) := by
  obtain ⟨Zb, Zp, h0, hP, hU, hN, hE⟩ := fresh_frames use r Wn K hinj hWn D
    (fun j => by rw [hD]; exact le_max_right _ _) (fun j => by rw [hD]; exact hα j)
  exact ⟨Zb, Zp, h0, hP, hU, hN, fun d j => by have h := hE d j; rw [hD] at h; exact h⟩

end Frames

section Live
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

/-- **The mixed certificate from a route.**  If the start matrices are invertible, the scalar map fixes every live
role when the scratch is zero, and every live role ends at `Targ l` times its start matrix, the word of the route is a
mixed certificate with targets `Targ`, at the exact price of the route.  (`GRoute.liveKernel` with `kernel α`
replaced by any `Targ l`: fresh helpers end at `pk D`, cut heads at their partial blocks.) -/
theorem _root_.OAI.PowerSaving.GF.GRoute.liveKernelM (e : σ → ρ) (S S' T : ρ → CMat α)
    (hS : ∀ r, S r * S' r = 1) (g : (ρ → ℂ) → (ρ → ℂ)) (c : (ℕ → ℝ) → ℝ) (h : GRoute S T g c)
    (hg : ∀ x : ρ → ℂ, (∀ s, (∀ l, e l ≠ s) → x s = 0) → ∀ l, g x (e l) = x (e l))
    (Targ : σ → CMat α) (hT : ∀ l, T (e l) = Targ l * S (e l)) :
    ∃ w : GWord α ρ, w.Proper (Fintype.card α) ∧ (∀ φ, w.costR φ = c φ) ∧ MX.GLiveKernelM e Targ w := by
  obtain ⟨w, hp, hc, hw⟩ := h
  refine ⟨w, hp, hc, ?_⟩
  intro f v hv l
  let y : Data α ρ f := multiAct f S' v
  have hy : multiAct f S y = v := by
    funext r; simp [y, multiAct, hS]
  have hy0 (s : ρ) (hs : ∀ l, e l ≠ s) : y s = 0 := by
    change matAct f (S' s) (v s) = 0
    rw [hv s hs]; unfold matAct; exact Matrix.mulVec_zero _
  have hpt : point f g y (e l) = y (e l) := by
    funext i
    exact hg (fun r => y r i) (fun s hs => by rw [hy0 s hs]; rfl) l
  have h1 := congrFun (hw f y) (e l)
  rw [hy] at h1
  rw [h1]
  change matAct f (T (e l)) (point f g y (e l)) = _
  rw [hpt, hT, ← matAct_mul]
  exact congrArg _ (congrFun hy (e l))

end Live

end
end FH
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.FH.fresh_frames
#print axioms OAI.PowerSaving.FH.fresh_frames_card
#print axioms OAI.PowerSaving.GF.GRoute.liveKernelM
