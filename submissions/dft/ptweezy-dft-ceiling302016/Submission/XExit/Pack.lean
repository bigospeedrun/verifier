import Submission.Work.Bridge401.Sched

/-!
# (key: x-exit) Exit-frame helpers: the package `GInvX` (slot `q` from `ent q` to an EXIT label `ex q`) and its
# reduction to the gauged package `GInvE`

`GInvE` (Gauge/Defs, DFT Bridge3 on Dugongue's #401) lets slot `q` start at the frame of its entrance label `ent q`
and end at the frame of the FULL label of the same base, `(ent q).top`; the bank of the slot absorbs the residual
step `entW = C * pk R * C'`, `|R| = 9 - dim ent q`.  The hub's #799/#869/#890 lineage has helpers that end at a lower
EXIT frame in the same base (hyperplane exits, dim 8; cold exits, dim 4): `X.Φ (ex q) = Wn q * X.Φ (ent q)` with
`Wn q` ONE kernel block of rank `dim ex q - dim ent q` between free adapters (`exW_form`).

* `exW`, `exW_spec`, `exW_form` the exit step `X.Φ V = exW X U V * X.Φ U` (same base, `U.s ⊆ V.s`), one kernel block
                                 of rank `dim V - dim U` between free adapters;
* `pk_conj`, `conj_of_forms`     two kernel blocks of the same rank are conjugate by FREE matrices;
* `GInvX`                        the exit-frame package (`GInvE` with `ex q` in place of `(ent q).top`);
* `GInvX.ofE`                    every `GInvE` is a `GInvX` (`ex = top`);
* `route_swap`                   free slot adapters before and after an invocation route cost nothing;
* `GInvX.toE`                    **THE REDUCTION**: a `GInvX` is a `GInvE` with the SAME price whose entrance labels
                                 `ent' q` have dimension `card H - (dim ex q - dim ent q)`;
* `fitsX`, `fits_toE`            the residual condition with residual `dim ex - dim ent` is Shea's `BankSched.fits`
                                 for `ent'`.
So `GX.engine_of_ginv_401` / `GX.wht_of_ginv_401` (Shea's tree, lean/complex588) apply to exit-frame packages with
bank loads `dim ex - dim ent` (see XExit/End.lean).

Credits: the engine (`pk`, `kg`, `core`, `Free`, `GRoute`, `gstep_free`, the invocation package) is Jacob Sussman's
(wht-power-saving-lean, Apache-2.0); `GInvE`, `entW`, `entN`, `BankSched` are DFT Bridge3's / Nil Mamano's as used in
Ryan Shea's shea256/fourier-transform-below-nlogn lean/complex588, on Dugongue's entrance gauges (#401); `pk_cperm`,
`cperm` are from Work/Bank401/Adapt (same authors); the exit frames are the hub's (#593/#599 hyperplane ends, cold
ends; #799 Kothe lineage).  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace XEX
open Binary Matrix Finset RAM SS CB BR CR GF RF GX B401
noncomputable section

section Kernel
variable {α : Type} [Fintype α] [DecidableEq α]

/-- **Two kernel blocks of the same rank are conjugate by free matrices.** -/
theorem pk_conj (R R' : Finset α) (h : R.card = R'.card) :
    ∃ P Pi : CMat α, Free P ∧ Free Pi ∧ pk R' = P * pk R * Pi := by
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq R R' h
  obtain ⟨Pi, hPi, -, hPPi⟩ := free_inv (free_cperm σ)
  refine ⟨permMat (cperm σ), Pi, free_cperm σ, hPi, ?_⟩
  rw [pk_cperm, hσ, Matrix.mul_assoc, hPPi, Matrix.mul_one]

/-- **Same rank between free adapters: free conjugates.** -/
theorem conj_of_forms {A B C C' D D' : CMat α} {R R' : Finset α}
    (hC : Free C) (hC' : Free C') (hD : Free D) (hD' : Free D')
    (hA : A = C * pk R * C') (hB : B = D * pk R' * D') (hc : R.card = R'.card) :
    ∃ F1 F2 : CMat α, Free F1 ∧ Free F2 ∧ B = F1 * A * F2 := by
  obtain ⟨P, Pi, hP, hPi, hpk⟩ := pk_conj R R' hc
  obtain ⟨Ci, hCi, hCiC, -⟩ := free_inv hC
  obtain ⟨C'i, hC'i, -, hC'C'i⟩ := free_inv hC'
  refine ⟨D * P * Ci, C'i * Pi * D', Free.mul (Free.mul hD hP) hCi, Free.mul (Free.mul hC'i hPi) hD', ?_⟩
  have e : D * P * Ci * (C * pk R * C') * (C'i * Pi * D')
      = D * P * (Ci * C) * pk R * (C' * C'i) * Pi * D' := by
    simp only [Matrix.mul_assoc]
  rw [hB, hA, hpk, e, hCiC, hC'C'i]
  simp only [Matrix.mul_one, Matrix.mul_assoc]

end Kernel

section Exit
variable {H α : Type} [Fintype H] [DecidableEq H] [Fintype α] [DecidableEq α]

/-- the exit step from the label `U` to the label `V` (same base, `U.s ⊆ V.s`) in the window map `X`. -/
def exW (X : BXMap H α) (U V : SLbl H) : CMat α :=
  kg (X.liftG U.G) * pk (X.liftS V.s \ X.liftS U.s) * kg (apInv (X.liftG U.G))

/-- **The exit step**: `X.Φ V = exW X U V * X.Φ U`. -/
lemma exW_spec (X : BXMap H α) (U V : SLbl H) (hG : V.G = U.G) (hs : U.s ⊆ V.s) :
    X.Φ V = exW X U V * X.Φ U := by
  have hs' : X.liftS U.s ⊆ X.liftS V.s := X.mono hs
  show core (X.liftG V.G) (X.liftS V.s) = exW X U V * core (X.liftG U.G) (X.liftS U.s)
  rw [hG, core_nested _ hs', exW, pk_eq_blockMat]

/-- the exit step is ONE kernel block of rank `dim V - dim U` between free adapters. -/
lemma exW_form (X : BXMap H α) (U V : SLbl H) (hs : U.s ⊆ V.s) :
    ∃ (C C' : CMat α) (R : Finset α), Free C ∧ Free C' ∧ R.card = V.dim - U.dim ∧
      exW X U V = C * pk R * C' := by
  refine ⟨_, _, X.liftS V.s \ X.liftS U.s, free_kg _, free_kg _, ?_, rfl⟩
  rw [X.card hs, Finset.card_sdiff_of_subset hs]
  rfl

/-- `exW` to the full label is Shea's `entW`. -/
lemma exW_top (X : BXMap H α) (U : SLbl H) : exW X U U.top = entW X U := rfl

/-- any `Wn` with `X.Φ U * N = 1` and `X.Φ U.top = Wn * X.Φ U` is `entW X U`. -/
lemma Wn_eq_entW (X : BXMap H α) (U : SLbl H) {N Wn : CMat α} (hN : X.Φ U * N = 1)
    (hW : X.Φ U.top = Wn * X.Φ U) : Wn = entW X U := by
  calc Wn = Wn * (X.Φ U * N) := by rw [hN, Matrix.mul_one]
    _ = X.Φ U.top * N := by rw [hW, Matrix.mul_assoc]
    _ = entW X U * (X.Φ U * N) := by rw [entW_spec, Matrix.mul_assoc]
    _ = entW X U := by rw [hN, Matrix.mul_one]

/-- a label of every dimension `k ≤ card H` in every base. -/
lemma exists_label (G : APerm H) (k : ℕ) (hk : k ≤ Fintype.card H) :
    ∃ U : SLbl H, U.G = G ∧ U.dim = k := by
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (univ : Finset H)) (n := k)
    (by rw [Finset.card_univ]; exact hk)
  exact ⟨⟨G, s⟩, rfl, hs⟩

end Exit

section Pkg
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]

/-- **An exit-frame invocation package** (`GInvE` with an exit label `ex q` per slot in place of `(ent q).top`):
slot `q` goes from `X.Φ (ent q) * N q * Z q = Z q` to `X.Φ (ex q) * N q * Z q = Wn q * Z q`. -/
structure GInvX (H T Sl C : Type) [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
    [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C] where
  tv : T → Space H
  hunit : ∀ t, dot (tv t) (tv t) = 1
  hgap : ∀ t, ∃ p, tv t p = 0
  cost : (ℕ → ℝ) → ℝ
  ent : Sl → SLbl H
  ex : Sl → SLbl H
  hexG : ∀ q, (ex q).G = (ent q).G
  hexs : ∀ q, (ent q).s ⊆ (ex q).s
  fwd : ∀ {α : Type} [Fintype α] [DecidableEq α] (W : GWin H α) (N Wn : Sl → CMat α),
    (∀ q, W.X.Φ (ent q) * N q = 1) → (∀ q, W.X.Φ (ex q) = Wn q * W.X.Φ (ent q)) →
    ∀ (Z : Sl → CMat α) (c0 c1 : C → CMat α),
    GRoute (iin W.Xm tv Z c0) (iout W.Xm tv (fun q => Wn q * Z q) c1) shearF cost
  bwd : ∀ {α : Type} [Fintype α] [DecidableEq α] (W : GWin H α) (N Wn : Sl → CMat α),
    (∀ q, W.X.Φ (ent q) * N q = 1) → (∀ q, W.X.Φ (ex q) = Wn q * W.X.Φ (ent q)) →
    ∀ (Z : Sl → CMat α) (c0 c1 : C → CMat α),
    GRoute (iin W.Xm tv Z c0) (iout W.Xm tv (fun q => Wn q * Z q) c1) shearB cost

/-- every gauged package is an exit-frame package with `ex = top`. -/
def GInvX.ofE (I : GInvE H T Sl C) : GInvX H T Sl C where
  tv := I.tv
  hunit := I.hunit
  hgap := I.hgap
  cost := I.cost
  ent := I.ent
  ex := fun q => (I.ent q).top
  hexG := fun q => rfl
  hexs := fun q => Finset.subset_univ _
  fwd := fun W N Wn hN hW Z c0 c1 => I.fwd W N Wn hN hW Z c0 c1
  bwd := fun W N Wn hN hW Z c0 c1 => I.bwd W N Wn hN hW Z c0 c1

variable {α : Type} [Fintype α] [DecidableEq α]

/-- **Free slot adapters around a route.**  If `Wn q = F1 q * Wx q * F2 q` with `F1 q`, `F2 q` free, a route that
ends the slots at `Wx q * Z' q` from `Z' q = F2 q * Z q` gives one that ends them at `Wn q * Z q`, same map, same
price. -/
theorem route_swap {g : (Box T Sl C → ℂ) → (Box T Sl C → ℂ)} {cost : (ℕ → ℝ) → ℝ}
    (Xm : XMap H α) (tv : T → Space H) (Wx Wn F1 F2 : Sl → CMat α)
    (hF1 : ∀ q, Free (F1 q)) (hF2 : ∀ q, Free (F2 q)) (he : ∀ q, Wn q = F1 q * Wx q * F2 q)
    (Z : Sl → CMat α) (c0 c1 : C → CMat α)
    (h : GRoute (iin Xm tv (fun q => F2 q * Z q) c0) (iout Xm tv (fun q => Wx q * (F2 q * Z q)) c1) g cost) :
    GRoute (iin Xm tv Z c0) (iout Xm tv (fun q => Wn q * Z q) c1) g cost := by
  have r1 : GRoute (iin Xm tv Z c0) (iin Xm tv (fun q => F2 q * Z q) c0) id (fun _ => 0) := by
    refine (GRoute.reach_all _ _ (fun _ _ => 0) ?_).cast (fun φ => by simp)
    rintro ((t|t)|(q|k))
    · exact GReach.refl _
    · exact GReach.refl _
    · show GReach (Z q) (F2 q * Z q) _
      exact fun ρ _ _ l => gstep_free (hF2 q) l _
    · exact GReach.refl _
  have r3 : GRoute (iout Xm tv (fun q => Wx q * (F2 q * Z q)) c1) (iout Xm tv (fun q => Wn q * Z q) c1) id
      (fun _ => 0) := by
    refine (GRoute.reach_all _ _ (fun _ _ => 0) ?_).cast (fun φ => by simp)
    rintro ((t|t)|(q|k))
    · exact GReach.refl _
    · exact GReach.refl _
    · show GReach (Wx q * (F2 q * Z q)) (Wn q * Z q) _
      have e : Wn q * Z q = F1 q * (Wx q * (F2 q * Z q)) := by
        rw [he q]; simp only [Matrix.mul_assoc]
      rw [e]
      exact fun ρ _ _ l => gstep_free (hF1 q) l _
    · exact GReach.refl _
  exact (((r1.trans h).trans r3).castg rfl).cast (fun φ => by simp)

/-- the free adapters between the stand-in entrance step and the exit step. -/
theorem GInvX.adapters (I : GInvX H T Sl C) (ent' : Sl → SLbl H)
    (hd : ∀ q, Fintype.card H - (ent' q).dim = (I.ex q).dim - (I.ent q).dim) (X : BXMap H α) (q : Sl) :
    ∃ F1 F2 : CMat α, Free F1 ∧ Free F2 ∧ entW X (ent' q) = F1 * exW X (I.ent q) (I.ex q) * F2 := by
  obtain ⟨C, C', R, hC, hC', hR, hA⟩ := exW_form X (I.ent q) (I.ex q) (I.hexs q)
  obtain ⟨D, D', R', hD, hD', hR', hB⟩ := entW_form X (ent' q)
  exact conj_of_forms hC hC' hD hD' hA hB (by rw [hR, hR', hd q])

/-- **The route of the reduction** (for `shearF` and `shearB` alike). -/
theorem GInvX.routeE (I : GInvX H T Sl C) (ent' : Sl → SLbl H)
    (hd : ∀ q, Fintype.card H - (ent' q).dim = (I.ex q).dim - (I.ent q).dim)
    {g : (Box T Sl C → ℂ) → (Box T Sl C → ℂ)}
    (hI : ∀ (W : GWin H α) (N Wn : Sl → CMat α),
      (∀ q, W.X.Φ (I.ent q) * N q = 1) → (∀ q, W.X.Φ (I.ex q) = Wn q * W.X.Φ (I.ent q)) →
      ∀ (Z : Sl → CMat α) (c0 c1 : C → CMat α),
      GRoute (iin W.Xm I.tv Z c0) (iout W.Xm I.tv (fun q => Wn q * Z q) c1) g I.cost)
    (W : GWin H α) (N Wn : Sl → CMat α) (hN : ∀ q, W.X.Φ (ent' q) * N q = 1)
    (hW : ∀ q, W.X.Φ (ent' q).top = Wn q * W.X.Φ (ent' q))
    (Z : Sl → CMat α) (c0 c1 : C → CMat α) :
    GRoute (iin W.Xm I.tv Z c0) (iout W.Xm I.tv (fun q => Wn q * Z q) c1) g I.cost := by
  choose F1 F2 hF1 hF2 hF using fun q => I.adapters ent' hd W.X q
  exact route_swap W.Xm I.tv (fun q => exW W.X (I.ent q) (I.ex q)) Wn F1 F2 hF1 hF2
    (fun q => (Wn_eq_entW W.X (ent' q) (hN q) (hW q)).trans (hF q)) Z c0 c1
    (hI W (fun q => entN W.X (I.ent q)) (fun q => exW W.X (I.ent q) (I.ex q)) (fun q => entN_spec _ _)
      (fun q => exW_spec _ _ _ (I.hexG q) (I.hexs q)) _ c0 c1)

/-- **THE REDUCTION.**  An exit-frame package is a gauged package (`GInvE`) with the same lines and the SAME price,
whose entrance labels `ent' q` have dimension `card H - (dim ex q - dim ent q)`. -/
def GInvX.toE (I : GInvX H T Sl C) (ent' : Sl → SLbl H)
    (hd : ∀ q, Fintype.card H - (ent' q).dim = (I.ex q).dim - (I.ent q).dim) : GInvE H T Sl C where
  tv := I.tv
  hunit := I.hunit
  hgap := I.hgap
  cost := I.cost
  ent := ent'
  fwd := fun W N Wn hN hW Z c0 c1 =>
    I.routeE ent' hd (fun W N Wn hN hW Z c0 c1 => I.fwd W N Wn hN hW Z c0 c1) W N Wn hN hW Z c0 c1
  bwd := fun W N Wn hN hW Z c0 c1 =>
    I.routeE ent' hd (fun W N Wn hN hW Z c0 c1 => I.bwd W N Wn hN hW Z c0 c1) W N Wn hN hW Z c0 c1

@[simp] lemma GInvX.toE_cost (I : GInvX H T Sl C) (ent' : Sl → SLbl H)
    (hd : ∀ q, Fintype.card H - (ent' q).dim = (I.ex q).dim - (I.ent q).dim) (φ : ℕ → ℝ) :
    (I.toE ent' hd).cost φ = I.cost φ := rfl

@[simp] lemma GInvX.toE_ent (I : GInvX H T Sl C) (ent' : Sl → SLbl H)
    (hd : ∀ q, Fintype.card H - (ent' q).dim = (I.ex q).dim - (I.ent q).dim) :
    (I.toE ent' hd).ent = ent' := rfl

/-- the residual of slot `q`: `dim ex q - dim ent q ≤ card H`. -/
lemma GInvX.res_le (I : GInvX H T Sl C) (q : Sl) : (I.ex q).dim - (I.ent q).dim ≤ Fintype.card H :=
  le_trans (Nat.sub_le _ _) (Finset.card_le_univ _)

/-- the stand-in entrance labels (base of `ent q`, dimension `card H - (dim ex q - dim ent q)`). -/
def GInvX.entS (I : GInvX H T Sl C) (q : Sl) : SLbl H :=
  Classical.choose (exists_label (I.ent q).G (Fintype.card H - ((I.ex q).dim - (I.ent q).dim)) (Nat.sub_le _ _))

lemma GInvX.entS_hd (I : GInvX H T Sl C) (q : Sl) :
    Fintype.card H - (I.entS q).dim = (I.ex q).dim - (I.ent q).dim := by
  have h : (I.entS q).dim = Fintype.card H - ((I.ex q).dim - (I.ent q).dim) :=
    (Classical.choose_spec (exists_label (I.ent q).G
      (Fintype.card H - ((I.ex q).dim - (I.ent q).dim)) (Nat.sub_le _ _))).2
  have h2 := I.res_le q
  rw [h]
  omega

/-- the reduction with the stand-in labels. -/
def GInvX.toE' (I : GInvX H T Sl C) : GInvE H T Sl C := I.toE I.entS I.entS_hd

/-- **The residual condition of an exit-frame package**: bank loads `dim ex - dim ent`, pads, `73` roles per bank. -/
def fitsX (S : BankSched Sl) (I : GInvX H T Sl C) : Prop :=
  (∀ b, S.load (fun q => (I.ex q).dim - (I.ent q).dim) b + S.pad b = 73) ∧ ∀ b, S.pad b < 73

/-- `fitsX` is Shea's `BankSched.fits` for the stand-in labels. -/
theorem fits_toE (S : BankSched Sl) (I : GInvX H T Sl C) (ent' : Sl → SLbl H)
    (hd : ∀ q, Fintype.card H - (ent' q).dim = (I.ex q).dim - (I.ent q).dim) (h : fitsX S I) :
    S.fits (I.toE ent' hd).ent := by
  refine ⟨fun b => ?_, h.2⟩
  show S.load (fun q => Fintype.card H - (ent' q).dim) b + S.pad b = 73
  rw [show (fun q => Fintype.card H - (ent' q).dim) = fun q => (I.ex q).dim - (I.ent q).dim from funext hd]
  exact h.1 b

theorem fits_toE' (S : BankSched Sl) (I : GInvX H T Sl C) (h : fitsX S I) : S.fits I.toE'.ent :=
  fits_toE S I I.entS I.entS_hd h

/-- for a gauged package seen as an exit-frame package, `fitsX` is `fits` (residual `card H - dim ent`). -/
theorem fitsX_ofE (S : BankSched Sl) (I : GInvE H T Sl C) : fitsX S (GInvX.ofE I) ↔ S.fits I.ent := Iff.rfl

end Pkg
end
end XEX
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.XEX.pk_conj
#print axioms OAI.PowerSaving.XEX.conj_of_forms
#print axioms OAI.PowerSaving.XEX.exW_spec
#print axioms OAI.PowerSaving.XEX.exW_form
#print axioms OAI.PowerSaving.XEX.route_swap
#print axioms OAI.PowerSaving.XEX.GInvX.routeE
#print axioms OAI.PowerSaving.XEX.GInvX.toE
#print axioms OAI.PowerSaving.XEX.GInvX.toE'
#print axioms OAI.PowerSaving.XEX.fits_toE'
