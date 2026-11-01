import Submission.Work.KLowW.InvMain

/-!
# (key: p-warpchk) Packages for the windows with a warp meaning: `GInvEW`, and the reduction `GInvXW.toEW'`

p-warpsem: the meaning of a warp exists for every frame map with a `WLift` (the windows `gwinB` of the bridged
geometry, `BXMap.refl`, `BXMap.ofConj`), not for every `BXMap`.  So a warp word gives an exit-frame package only for
the windows satisfying a condition `Ok` (`GInvXW`, `Work/KLowW/InvMain.lean`).  This file is XExit/Pack's reduction
`GInvX.toE'` (Shea's gauged package `GInvE`, the input of the networks) with the window condition threaded through:

* `GInvEW H T Sl C Ok`        `GInvE` whose routes are asked only at windows with `Ok`;
* `GInvEW.toE`                every window fine: a `GInvE`;
* `GInvXW.toEW'`              **the reduction** (same lines, same price, stand-in entrance labels `entS`);
* `fitsXW`, `fits_toEW'`      the residual condition `dim ex - dim ent` is `BankSched.fits` for `entS`.

A network that consumes `GInvEW Ok` asks `Ok` of its windows (`XNet.G0 .. G8`, the `gistageE_fwd/bwd` calls).
No `sorry`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace KLW
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.GF OAI.PowerSaving.RAM OAI.PowerSaving.SS
  OAI.PowerSaving.CB OAI.PowerSaving.BR OAI.PowerSaving.GX OAI.PowerSaving.XEX OAI.PowerSaving.B401 Finset Matrix

section
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]

/-- **the gauged package for the windows with `Ok`** (Shea's `GInvE` with a window condition) -/
structure GInvEW (H T Sl C : Type) [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
    [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]
    (Ok : ∀ {α : Type} [Fintype α] [DecidableEq α], GWin H α → Prop) where
  tv : T → Space H
  hunit : ∀ t, dot (tv t) (tv t) = 1
  hgap : ∀ t, ∃ p, tv t p = 0
  cost : (ℕ → ℝ) → ℝ
  ent : Sl → SLbl H
  fwd : ∀ {α : Type} [Fintype α] [DecidableEq α] (W : GWin H α), Ok W → ∀ (N Wn : Sl → CMat α),
    (∀ q, W.X.Φ (ent q) * N q = 1) → (∀ q, W.X.Φ (ent q).top = Wn q * W.X.Φ (ent q)) →
    ∀ (Z : Sl → CMat α) (c0 c1 : C → CMat α),
    GRoute (iin W.Xm tv Z c0) (iout W.Xm tv (fun q => Wn q * Z q) c1) shearF cost
  bwd : ∀ {α : Type} [Fintype α] [DecidableEq α] (W : GWin H α), Ok W → ∀ (N Wn : Sl → CMat α),
    (∀ q, W.X.Φ (ent q) * N q = 1) → (∀ q, W.X.Φ (ent q).top = Wn q * W.X.Φ (ent q)) →
    ∀ (Z : Sl → CMat α) (c0 c1 : C → CMat α),
    GRoute (iin W.Xm tv Z c0) (iout W.Xm tv (fun q => Wn q * Z q) c1) shearB cost

variable {Ok : ∀ {α : Type} [Fintype α] [DecidableEq α], GWin H α → Prop}

/-- every window fine: Shea's `GInvE` -/
def GInvEW.toE (I : GInvEW H T Sl C Ok) (hOk : ∀ {α : Type} [Fintype α] [DecidableEq α] (W : GWin H α), Ok W) :
    GInvE H T Sl C where
  tv := I.tv
  hunit := I.hunit
  hgap := I.hgap
  cost := I.cost
  ent := I.ent
  fwd := fun W => I.fwd W (hOk W)
  bwd := fun W => I.bwd W (hOk W)

/-- every gauged package is one for any window condition (a warp-free provider in a network with `Ok`) -/
def _root_.OAI.PowerSaving.GX.GInvE.toW (I : GInvE H T Sl C) (Ok : ∀ {α : Type} [Fintype α] [DecidableEq α], GWin H α → Prop) :
    GInvEW H T Sl C Ok where
  tv := I.tv
  hunit := I.hunit
  hgap := I.hgap
  cost := I.cost
  ent := I.ent
  fwd := fun W _ => I.fwd W
  bwd := fun W _ => I.bwd W

@[simp] lemma _root_.OAI.PowerSaving.GX.GInvE.toW_cost (I : GInvE H T Sl C) (Ok : ∀ {α : Type} [Fintype α] [DecidableEq α], GWin H α → Prop)
    (φ : ℕ → ℝ) : (I.toW Ok).cost φ = I.cost φ := rfl

/-- the free adapters between the stand-in entrance step and the exit step (`GInvX.adapters`) -/
theorem GInvXW.adapters (I : GInvXW H T Sl C Ok) (ent' : Sl → SLbl H)
    (hd : ∀ q, Fintype.card H - (ent' q).dim = (I.ex q).dim - (I.ent q).dim) {α : Type} [Fintype α] [DecidableEq α]
    (X : BXMap H α) (q : Sl) :
    ∃ F1 F2 : CMat α, Free F1 ∧ Free F2 ∧ entW X (ent' q) = F1 * exW X (I.ent q) (I.ex q) * F2 := by
  obtain ⟨C, C', R, hC, hC', hR, hA⟩ := exW_form X (I.ent q) (I.ex q) (I.hexs q)
  obtain ⟨D, D', R', hD, hD', hR', hB⟩ := entW_form X (ent' q)
  exact conj_of_forms hC hC' hD hD' hA hB (by rw [hR, hR', hd q])

/-- the route of the reduction at one window with `Ok` (`GInvX.routeE`) -/
theorem GInvXW.routeE (I : GInvXW H T Sl C Ok) (ent' : Sl → SLbl H)
    (hd : ∀ q, Fintype.card H - (ent' q).dim = (I.ex q).dim - (I.ent q).dim)
    {g : (Box T Sl C → ℂ) → (Box T Sl C → ℂ)} {α : Type} [Fintype α] [DecidableEq α] (W : GWin H α)
    (hI : ∀ (N Wn : Sl → CMat α),
      (∀ q, W.X.Φ (I.ent q) * N q = 1) → (∀ q, W.X.Φ (I.ex q) = Wn q * W.X.Φ (I.ent q)) →
      ∀ (Z : Sl → CMat α) (c0 c1 : C → CMat α),
      GRoute (iin W.Xm I.tv Z c0) (iout W.Xm I.tv (fun q => Wn q * Z q) c1) g I.cost)
    (N Wn : Sl → CMat α) (hN : ∀ q, W.X.Φ (ent' q) * N q = 1)
    (hW : ∀ q, W.X.Φ (ent' q).top = Wn q * W.X.Φ (ent' q))
    (Z : Sl → CMat α) (c0 c1 : C → CMat α) :
    GRoute (iin W.Xm I.tv Z c0) (iout W.Xm I.tv (fun q => Wn q * Z q) c1) g I.cost := by
  choose F1 F2 hF1 hF2 hF using fun q => I.adapters ent' hd W.X q
  exact route_swap W.Xm I.tv (fun q => exW W.X (I.ent q) (I.ex q)) Wn F1 F2 hF1 hF2
    (fun q => (Wn_eq_entW W.X (ent' q) (hN q) (hW q)).trans (hF q)) Z c0 c1
    (hI (fun q => entN W.X (I.ent q)) (fun q => exW W.X (I.ent q) (I.ex q)) (fun q => entN_spec _ _)
      (fun q => exW_spec _ _ _ (I.hexG q) (I.hexs q)) _ c0 c1)

/-- **THE REDUCTION** with windows: same lines, same price, entrance labels `ent'` -/
def GInvXW.toEW (I : GInvXW H T Sl C Ok) (ent' : Sl → SLbl H)
    (hd : ∀ q, Fintype.card H - (ent' q).dim = (I.ex q).dim - (I.ent q).dim) : GInvEW H T Sl C Ok where
  tv := I.tv
  hunit := I.hunit
  hgap := I.hgap
  cost := I.cost
  ent := ent'
  fwd := fun W hOk N Wn hN hW Z c0 c1 =>
    I.routeE ent' hd W (fun N Wn hN hW Z c0 c1 => I.fwd W hOk N Wn hN hW Z c0 c1) N Wn hN hW Z c0 c1
  bwd := fun W hOk N Wn hN hW Z c0 c1 =>
    I.routeE ent' hd W (fun N Wn hN hW Z c0 c1 => I.bwd W hOk N Wn hN hW Z c0 c1) N Wn hN hW Z c0 c1

lemma GInvXW.res_le (I : GInvXW H T Sl C Ok) (q : Sl) : (I.ex q).dim - (I.ent q).dim ≤ Fintype.card H :=
  le_trans (Nat.sub_le _ _) (Finset.card_le_univ _)

/-- the stand-in entrance labels -/
noncomputable def GInvXW.entS (I : GInvXW H T Sl C Ok) (q : Sl) : SLbl H :=
  Classical.choose (exists_label (I.ent q).G (Fintype.card H - ((I.ex q).dim - (I.ent q).dim)) (Nat.sub_le _ _))

lemma GInvXW.entS_hd (I : GInvXW H T Sl C Ok) (q : Sl) :
    Fintype.card H - (I.entS q).dim = (I.ex q).dim - (I.ent q).dim := by
  have h : (I.entS q).dim = Fintype.card H - ((I.ex q).dim - (I.ent q).dim) :=
    (Classical.choose_spec (exists_label (I.ent q).G
      (Fintype.card H - ((I.ex q).dim - (I.ent q).dim)) (Nat.sub_le _ _))).2
  have h2 := I.res_le q
  rw [h]
  omega

/-- the reduction with the stand-in labels -/
noncomputable def GInvXW.toEW' (I : GInvXW H T Sl C Ok) : GInvEW H T Sl C Ok := I.toEW I.entS I.entS_hd

@[simp] lemma GInvXW.toEW'_cost (I : GInvXW H T Sl C Ok) (φ : ℕ → ℝ) : I.toEW'.cost φ = I.cost φ := rfl
@[simp] lemma GInvXW.toEW'_tv (I : GInvXW H T Sl C Ok) : I.toEW'.tv = I.tv := rfl
@[simp] lemma GInvXW.toEW'_ent (I : GInvXW H T Sl C Ok) : I.toEW'.ent = I.entS := rfl

/-- the residual condition of an exit-frame package with windows -/
def fitsXW (S : BankSched Sl) (I : GInvXW H T Sl C Ok) : Prop :=
  (∀ b, S.load (fun q => (I.ex q).dim - (I.ent q).dim) b + S.pad b = 73) ∧ ∀ b, S.pad b < 73

theorem fits_toEW' (S : BankSched Sl) (I : GInvXW H T Sl C Ok) (h : fitsXW S I) : S.fits I.toEW'.ent := by
  refine ⟨fun b => ?_, h.2⟩
  show S.load (fun q => Fintype.card H - (I.entS q).dim) b + S.pad b = 73
  rw [show (fun q => Fintype.card H - (I.entS q).dim) = fun q => (I.ex q).dim - (I.ent q).dim from
    funext I.entS_hd]
  exact h.1 b

/-- with every window fine, the windowed reduction is XExit's (`GInvXW.toX` then `toE'`): same price -/
theorem GInvXW.toEW'_toE_cost (I : GInvXW H T Sl C Ok)
    (hOk : ∀ {α : Type} [Fintype α] [DecidableEq α] (W : GWin H α), Ok W) (φ : ℕ → ℝ) :
    (I.toEW'.toE hOk).cost φ = (I.toX hOk).toE'.cost φ := rfl

end
end KLW

#print axioms KLW.GInvXW.toEW'
#print axioms KLW.fits_toEW'
#print axioms KLW.GInvEW.toE
#print axioms OAI.PowerSaving.GX.GInvE.toW
