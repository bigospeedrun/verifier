import Submission.Work.KLowW.Inv

/-!
# (key: p-warpchk) THE WARP INVOCATION THEOREM: `WValid.inv : GInvX`

See `Work/KLowW/Inv.lean` for the plan.  `WValid.clean`: the clean route (slots from their entrance labels to their
exit labels) in either orientation; `WValid.inv`: the exit-frame package of x-exit-lean, with `gdirtyE` as
`GLabX.inv`.  The warp meanings `WSf` (forward) and `WSb` (backward) are hypotheses for EVERY stage-B frame map (the
statement p-warpsem proves; `GInvX` quantifies over all windows).

No `sorry`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace KLW
open SSC GXD GLab OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.GF OAI.PowerSaving.RAM
  OAI.PowerSaving.SS OAI.PowerSaving.CB OAI.PowerSaving.BR OAI.PowerSaving.GX OAI.PowerSaving.XEX Finset Matrix

section
variable {c : WCert} {emb : Box (Fin c.v) (Fin c.R) (Fin c.nc) → Nat} {un : Nat → Box (Fin c.v) (Fin c.R) (Fin c.nc)}

/-- the port vector of `t` -/
noncomputable def WCert.tv (c : WCert) (t : Fin c.v) : Space (Fin c.p.h) := tvec c.p.h (c.ports.getD t.val 0)

theorem WValidS.E (V : WValidS c) : EndsX c.pe c.v c.ports [] c.gl c.el c.S0 c.S0 c.SF := endKX_sound V.tab V.ends

theorem WValidS.good (V : WValidS c) (k : Nat) : Good c.p.h (c.p.tab.get k) := tabK_good _ _ V.tab k

theorem WValidS.dim (V : WValidS c) (k : Nat) : (GLab.lab c.p.h (c.p.tab.get k)).dim = cdim (c.p.tab.get k) :=
  lab_dim (V.good k)

theorem WValidS.qlt (V : WValidS c) (q : Fin c.R) : q.val < c.pe.n - 2 * c.v := by
  show q.val < 2 * c.v + c.R - 2 * c.v
  omega

/-- an exit slot's end frame contains its start frame -/
theorem WValidS.hsub (V : WValidS c) (Ro : WRoles c emb un) (q : Fin c.R) (hq : q ∈ c.exits) :
    ∀ x, (c.L emb c.S0 (CR.lS q)).Mem x → (c.L emb c.SF (CR.lS q)).Mem x := by
  have hm : memK (2 * c.v + q.val) c.el = true := (Finset.mem_filter.mp hq).2
  intro x hx
  show (GLab.lab c.p.h (c.p.tab.get (c.SF.get (emb (bS q))))).Mem x
  rw [Ro.num.hs q]
  have hx' : (GLab.lab c.p.h (c.p.tab.get (c.S0.get (emb (bS q))))).Mem x := hx
  rw [Ro.num.hs q] at hx'
  exact (V.E.slot q.val (V.qlt q)).2.2 hm x hx'

theorem WValidS.hexG (V : WValidS c) (Ro : WRoles c emb un) (q : Fin c.R) :
    (c.exq emb q).G = (c.ent emb q).G := by
  unfold WCert.exq WCert.ent
  by_cases h : q ∈ c.exits
  · rw [if_pos h, XEX.lab0X_E _ _ _ h]; rfl
  · rw [if_neg h]; rfl

theorem WValidS.hexs (V : WValidS c) (Ro : WRoles c emb un) (q : Fin c.R) :
    (c.ent emb q).s ⊆ (c.exq emb q).s := by
  unfold WCert.exq
  by_cases h : q ∈ c.exits
  · rw [if_pos h]
    unfold WCert.ent
    rw [XEX.lab0X_E _ _ _ h]
    exact (XEX.adPair_spec _ _ (V.hsub Ro q h)).1
  · rw [if_neg h]; exact Finset.subset_univ _

variable {α : Type} [Fintype α] [DecidableEq α]

/-- (free) the start adapters: old frames of x and y, adapted entrance labels, to the frames of `S0` -/
theorem WValidS.a0 (V : WValidS c) (Ro : WRoles c emb un) (W : GWin (Fin c.p.h) α) :
    GRoute (stamp (fun t => W.Xm.Φ (tt (c.tv t))) (fun _ => W.Xm.Φ 0) (fun q => W.X.Φ (c.ent emb q))
        (fun k => Lf c.p emb W.X c.S0 (bC k)))
      (Lf c.p emb W.X c.S0) id (fun _ => 0) := by
  refine (GRoute.reach_all _ _ (fun _ _ => 0) ?_).cast (fun φ => by simp)
  rintro ((t|t)|(q|k))
  · have P := V.E.port t.val t.isLt
    obtain ⟨p0, hp⟩ := P.gap
    obtain ⟨A, k, hA⟩ := exists_base_one (c.tv t) P.unit p0 hp
    show GReach (W.Xm.Φ (tt (c.tv t))) (W.X.Φ (GLab.lab c.p.h (c.p.tab.get (c.S0.get (emb (bX t)))))) _
    rw [Ro.num.hx t]
    have h := W.line A k (GLab.lab c.p.h (c.p.tab.get (c.S0.get t.val))) (by rw [V.dim]; exact P.x0d)
      (by rw [hA]; exact P.x0m)
    rw [hA] at h
    exact h
  · have P := V.E.port t.val t.isLt
    show GReach (W.Xm.Φ 0) (W.X.Φ (GLab.lab c.p.h (c.p.tab.get (c.S0.get (emb (bY t)))))) _
    rw [Ro.num.hy t]
    exact W.zero _ (by rw [V.dim, P.y0]; exact V.E.z0)
  · show GReach (W.X.Φ (c.ent emb q)) (W.X.Φ (GLab.lab c.p.h (c.p.tab.get (c.S0.get (emb (bS q)))))) _
    by_cases hq : q ∈ c.exits
    · unfold WCert.ent
      rw [XEX.lab0X_E _ _ _ hq]
      exact XEX.rebaseR W.X _ _ (XEX.entA_mem _ _ (V.hsub Ro q hq))
    · unfold WCert.ent
      rw [XEX.lab0X_nE _ _ _ hq]
      exact GReach.refl _
  · exact GReach.refl _

/-- (free) the end adapters: the frames of `SF` to the old frames of x and y and the exit labels -/
theorem WValidS.aF (V : WValidS c) (Ro : WRoles c emb un) (W : GWin (Fin c.p.h) α) :
    GRoute (Lf c.p emb W.X c.SF)
      (stamp (fun _ => W.Xm.Φ 1) (fun t => W.Xm.Φ (1 + tt (c.tv t))) (fun q => W.X.Φ (c.exq emb q))
        (fun k => Lf c.p emb W.X c.SF (bC k))) id (fun _ => 0) := by
  refine (GRoute.reach_all _ _ (fun _ _ => 0) ?_).cast (fun φ => by simp)
  rintro ((t|t)|(q|k))
  · have P := V.E.port t.val t.isLt
    show GReach (W.X.Φ (GLab.lab c.p.h (c.p.tab.get (c.SF.get (emb (bX t)))))) (W.Xm.Φ 1) _
    rw [Ro.num.hx t]
    exact W.full _ (by rw [V.dim, Fintype.card_fin]; exact P.xF)
  · have P := V.E.port t.val t.isLt
    obtain ⟨p0, hp⟩ := P.gap
    obtain ⟨A, k, hA⟩ := exists_base_one (c.tv t) P.unit p0 hp
    show GReach (W.X.Φ (GLab.lab c.p.h (c.p.tab.get (c.SF.get (emb (bY t)))))) (W.Xm.Φ (1 + tt (c.tv t))) _
    rw [Ro.num.hy t]
    have h := W.perp A k (GLab.lab c.p.h (c.p.tab.get (c.SF.get (c.v + t.val))))
      (by rw [V.dim, Fintype.card_fin]; exact P.yFd) (by rw [hA]; exact P.yFm)
    rw [hA] at h
    exact h
  · show GReach (W.X.Φ (GLab.lab c.p.h (c.p.tab.get (c.SF.get (emb (bS q)))))) (W.X.Φ (c.exq emb q)) _
    unfold WCert.exq
    by_cases hq : q ∈ c.exits
    · rw [if_pos hq]
      exact XEX.rebaseR W.X _ _ (XEX.exlA_mem _ _ (V.hsub Ro q hq))
    · rw [if_neg hq]
      have hm : memK (2 * c.v + q.val) c.el = false := by
        cases e : memK (2 * c.v + q.val) c.el with
        | false => rfl
        | true => exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ q, e⟩) hq
      have hF := (V.E.slot q.val (V.qlt q)).2.1 hm
      rw [Ro.num.hs q]
      exact ((W.full _ (by rw [V.dim, Fintype.card_fin]; exact hF)).trans
        (W.topN _ (SLbl.top_dim _))).cast (fun φ => by simp)
  · exact GReach.refl _

/-- **the clean route** of a valid warp certificate in orientation `o`, end rows `R'` -/
theorem WValidS.clean (V : WValidS c) (Ro : WRoles c emb un) (W : GWin (Fin c.p.h) α)
    (WS : WarpSem c.p.h c.wt W.X) (o : Bool) (evs : List WEv) (hL : RunW c.p c.wt c.S0 evs c.SF c.rs)
    (R' : RT) (hSc : ScalOK c.q o evs c.R0 R')
    (hw : RT.wfK R' c.q.d = true) (hsh : shKn c.q c.v o R' (2 * c.v + c.R) = true) (hfr : freeK c.q R' = true)
    (c0 c1 : Fin c.nc → CMat α) :
    GRoute (iin W.Xm c.tv (fun q => W.X.Φ (c.ent emb q)) c0) (iout W.Xm c.tv (fun q => W.X.Φ (c.exq emb q)) c1)
      (Bool.rec (motive := fun _ => (Box (Fin c.v) (Fin c.R) (Fin c.nc) → ℂ) → (Box (Fin c.v) (Fin c.R) (Fin c.nc) → ℂ))
        shearF shearB o) (fun φ => rcost φ c.rs) := by
  have hq := Ro.sctx V.nr
  have hR' := RT.wfK_sound R' c.q.d hw
  have hD : 1 ≤ c.q.D := V.par.2.2.2.2
  have e0 : GRoute (iin W.Xm c.tv (fun q => W.X.Φ (c.ent emb q)) c0)
      (stamp (fun t => W.Xm.Φ (tt (c.tv t))) (fun _ => W.Xm.Φ 0) (fun q => W.X.Φ (c.ent emb q))
        (fun k => Lf c.p emb W.X c.S0 (bC k))) eraseC (fun _ => 0) :=
    GRoute.ofX (xerase (fun t => rfl) (fun t => rfl) (fun q => rfl))
  have m := warp_grouteS Ro.C W.X (lt_of_eq_of_lt (Fintype.card_fin _).symm W.big) WS o hL V.E.w0 c.q V.par hq hR'
    V.id0 hfr hSc
  have e1 : GRoute (stamp (fun _ => W.Xm.Φ 1) (fun t => W.Xm.Φ (1 + tt (c.tv t))) (fun q => W.X.Φ (c.exq emb q))
        (fun k => Lf c.p emb W.X c.SF (bC k)))
      (iout W.Xm c.tv (fun q => W.X.Φ (c.exq emb q)) c1) eraseC (fun _ => 0) :=
    GRoute.ofX (xerase (fun t => rfl) (fun t => rfl) (fun q => rfl))
  have tot := (((e0.trans (V.a0 Ro W)).trans m).trans (V.aF Ro W)).trans e1
  refine (tot.castg (funext fun z => ?_)).cast (fun φ => by simp)
  have := rows_shear hq Ro.num hD o (shKn_sound c.q c.v o R' hR' _ hsh) z
  cases o <;> exact this

/-- **THE WARP INVOCATION THEOREM**: a valid warp certificate is an exit-frame package, with price `rcost rs`,
for warp meanings of every frame map (forward `WSf`, backward `WSb`) -/
noncomputable def WValidS.inv (V : WValidS c) (Ro : WRoles c emb un)
    (WSf : ∀ {α : Type} [Fintype α] [DecidableEq α] (X : BXMap (Fin c.p.h) α), WarpSem c.p.h c.wt X)
    (WSb : ∀ {α : Type} [Fintype α] [DecidableEq α] (X : BXMap (Fin c.p.h) α), WarpSem c.p.h c.wt X) :
    GInvX (Fin c.p.h) (Fin c.v) (Fin c.R) (Fin c.nc) where
  tv := c.tv
  hunit := fun t => (V.E.port t.val t.isLt).unit
  hgap := fun t => (V.E.port t.val t.isLt).gap
  cost := fun φ => rcost φ c.rs
  ent := c.ent emb
  ex := c.exq emb
  hexG := V.hexG Ro
  hexs := V.hexs Ro
  fwd := fun W N Wn hN hW Z c0 c1 =>
    gdirtyE W.Xm c.tv _ _ N Wn hN hW Z c0 c1
      (V.clean Ro W (WSf W.X) false c.evs V.run c.RF V.scF V.wfF V.shF V.frF c0 c1)
      (shearF_comm (fun _ => 1) (fun q => N q * Z q) (fun _ => 1))
  bwd := fun W N Wn hN hW Z c0 c1 =>
    gdirtyE W.Xm c.tv _ _ N Wn hN hW Z c0 c1
      (V.clean Ro W (WSb W.X) true c.evsB V.runB c.RB V.scB V.wfB V.shB V.frB c0 c1)
      (shearB_comm (fun _ => 1) (fun q => N q * Z q) (fun _ => 1))

/-- **an exit-frame package for the windows satisfying `Ok`** (`GInvX` with a window condition): what a warp word
gives when the warp meaning exists only for some frame maps (p-warpsem: every `X` with a `WLift`, e.g. the windows
`gwinB` of the bridged geometry, `BXMap.refl`) -/
structure GInvXW (H T Sl C : Type) [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
    [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]
    (Ok : ∀ {α : Type} [Fintype α] [DecidableEq α], GWin H α → Prop) where
  tv : T → Space H
  hunit : ∀ t, dot (tv t) (tv t) = 1
  hgap : ∀ t, ∃ p, tv t p = 0
  cost : (ℕ → ℝ) → ℝ
  ent : Sl → SLbl H
  ex : Sl → SLbl H
  hexG : ∀ q, (ex q).G = (ent q).G
  hexs : ∀ q, (ent q).s ⊆ (ex q).s
  fwd : ∀ {α : Type} [Fintype α] [DecidableEq α] (W : GWin H α), Ok W → ∀ (N Wn : Sl → CMat α),
    (∀ q, W.X.Φ (ent q) * N q = 1) → (∀ q, W.X.Φ (ex q) = Wn q * W.X.Φ (ent q)) →
    ∀ (Z : Sl → CMat α) (c0 c1 : C → CMat α),
    GRoute (iin W.Xm tv Z c0) (iout W.Xm tv (fun q => Wn q * Z q) c1) shearF cost
  bwd : ∀ {α : Type} [Fintype α] [DecidableEq α] (W : GWin H α), Ok W → ∀ (N Wn : Sl → CMat α),
    (∀ q, W.X.Φ (ent q) * N q = 1) → (∀ q, W.X.Φ (ex q) = Wn q * W.X.Φ (ent q)) →
    ∀ (Z : Sl → CMat α) (c0 c1 : C → CMat α),
    GRoute (iin W.Xm tv Z c0) (iout W.Xm tv (fun q => Wn q * Z q) c1) shearB cost

/-- every window is fine: the package is a `GInvX` -/
def GInvXW.toX {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
    [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]
    {Ok : ∀ {α : Type} [Fintype α] [DecidableEq α], GWin H α → Prop} (I : GInvXW H T Sl C Ok)
    (hOk : ∀ {α : Type} [Fintype α] [DecidableEq α] (W : GWin H α), Ok W) : GInvX H T Sl C where
  tv := I.tv
  hunit := I.hunit
  hgap := I.hgap
  cost := I.cost
  ent := I.ent
  ex := I.ex
  hexG := I.hexG
  hexs := I.hexs
  fwd := fun W => I.fwd W (hOk W)
  bwd := fun W => I.bwd W (hOk W)

/-- **THE WARP INVOCATION THEOREM, window form**: warp meanings only for the windows with `Ok` -/
noncomputable def WValidS.invW (V : WValidS c) (Ro : WRoles c emb un)
    (Ok : ∀ {α : Type} [Fintype α] [DecidableEq α], GWin (Fin c.p.h) α → Prop)
    (WSf : ∀ {α : Type} [Fintype α] [DecidableEq α] (W : GWin (Fin c.p.h) α), Ok W → WarpSem c.p.h c.wt W.X)
    (WSb : ∀ {α : Type} [Fintype α] [DecidableEq α] (W : GWin (Fin c.p.h) α), Ok W → WarpSem c.p.h c.wt W.X) :
    GInvXW (Fin c.p.h) (Fin c.v) (Fin c.R) (Fin c.nc) Ok where
  tv := c.tv
  hunit := fun t => (V.E.port t.val t.isLt).unit
  hgap := fun t => (V.E.port t.val t.isLt).gap
  cost := fun φ => rcost φ c.rs
  ent := c.ent emb
  ex := c.exq emb
  hexG := V.hexG Ro
  hexs := V.hexs Ro
  fwd := fun W hW0 N Wn hN hW Z c0 c1 =>
    gdirtyE W.Xm c.tv _ _ N Wn hN hW Z c0 c1
      (V.clean Ro W (WSf W hW0) false c.evs V.run c.RF V.scF V.wfF V.shF V.frF c0 c1)
      (shearF_comm (fun _ => 1) (fun q => N q * Z q) (fun _ => 1))
  bwd := fun W hW0 N Wn hN hW Z c0 c1 =>
    gdirtyE W.Xm c.tv _ _ N Wn hN hW Z c0 c1
      (V.clean Ro W (WSb W hW0) true c.evsB V.runB c.RB V.scB V.wfB V.shB V.frB c0 c1)
      (shearB_comm (fun _ => 1) (fun q => N q * Z q) (fun _ => 1))

@[simp] theorem WValidS.inv_cost (V : WValidS c) (Ro : WRoles c emb un) (WSf WSb) (φ : ℕ → ℝ) :
    (V.inv Ro WSf WSb).cost φ = rcost φ c.rs := rfl
@[simp] theorem WValidS.inv_ent (V : WValidS c) (Ro : WRoles c emb un) (WSf WSb) :
    (V.inv Ro WSf WSb).ent = c.ent emb := rfl
@[simp] theorem WValidS.inv_ex (V : WValidS c) (Ro : WRoles c emb un) (WSf WSb) :
    (V.inv Ro WSf WSb).ex = c.exq emb := rfl

/-- the bank residual of a slot: `dim(end) - dim(start)` for an exit slot, `h - dim(start)` otherwise -/
theorem WValidS.inv_res (V : WValidS c) (Ro : WRoles c emb un) (WSf WSb) (q : Fin c.R) :
    ((V.inv Ro WSf WSb).ex q).dim - ((V.inv Ro WSf WSb).ent q).dim
      = Bool.rec (motive := fun _ => Nat) (c.p.h - cdim (c.p.tab.get (c.S0.get (2 * c.v + q.val))))
          (cdim (c.p.tab.get (c.SF.get (2 * c.v + q.val))) - cdim (c.p.tab.get (c.S0.get (2 * c.v + q.val))))
          (memK (2 * c.v + q.val) c.el) := by
  show (c.exq emb q).dim - (c.ent emb q).dim = _
  have hU : (c.L emb c.S0 (CR.lS q)).dim = cdim (c.p.tab.get (c.S0.get (2 * c.v + q.val))) := by
    show (GLab.lab c.p.h (c.p.tab.get (c.S0.get (emb (bS q))))).dim = _
    rw [Ro.num.hs q, V.dim]
  have hV : (c.L emb c.SF (CR.lS q)).dim = cdim (c.p.tab.get (c.SF.get (2 * c.v + q.val))) := by
    show (GLab.lab c.p.h (c.p.tab.get (c.SF.get (emb (bS q))))).dim = _
    rw [Ro.num.hs q, V.dim]
  unfold WCert.exq WCert.ent
  cases hm : memK (2 * c.v + q.val) c.el with
  | false =>
    have hq : q ∉ c.exits := fun h => by
      have := (Finset.mem_filter.mp h).2; rw [hm] at this; exact Bool.false_ne_true this
    rw [if_neg hq, SLbl.top_dim, Fintype.card_fin, XEX.lab0X_nE _ _ _ hq, hU]
  | true =>
    have hq : q ∈ c.exits := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩
    rw [if_pos hq, XEX.lab0X_E _ _ _ hq, XEX.exlA_dim _ _ (V.hsub Ro q hq), XEX.entA_dim _ _ (V.hsub Ro q hq),
      hU, hV]

/-! ## the same from the kernel facts -/

noncomputable def WValid.inv (V : WValid c) (Ro : WRoles c emb un)
    (WSf : ∀ {α : Type} [Fintype α] [DecidableEq α] (X : BXMap (Fin c.p.h) α), WarpSem c.p.h c.wt X)
    (WSb : ∀ {α : Type} [Fintype α] [DecidableEq α] (X : BXMap (Fin c.p.h) α), WarpSem c.p.h c.wt X) :
    GInvX (Fin c.p.h) (Fin c.v) (Fin c.R) (Fin c.nc) :=
  V.toS.inv Ro WSf WSb

noncomputable def WValid.invW (V : WValid c) (Ro : WRoles c emb un)
    (Ok : ∀ {α : Type} [Fintype α] [DecidableEq α], GWin (Fin c.p.h) α → Prop)
    (WSf : ∀ {α : Type} [Fintype α] [DecidableEq α] (W : GWin (Fin c.p.h) α), Ok W → WarpSem c.p.h c.wt W.X)
    (WSb : ∀ {α : Type} [Fintype α] [DecidableEq α] (W : GWin (Fin c.p.h) α), Ok W → WarpSem c.p.h c.wt W.X) :
    GInvXW (Fin c.p.h) (Fin c.v) (Fin c.R) (Fin c.nc) Ok :=
  V.toS.invW Ro Ok WSf WSb

@[simp] theorem WValid.inv_cost (V : WValid c) (Ro : WRoles c emb un) (WSf WSb) (φ : ℕ → ℝ) :
    (V.inv Ro WSf WSb).cost φ = rcost φ c.rs := rfl

theorem WValid.inv_res (V : WValid c) (Ro : WRoles c emb un) (WSf WSb) (q : Fin c.R) :
    ((V.inv Ro WSf WSb).ex q).dim - ((V.inv Ro WSf WSb).ent q).dim
      = Bool.rec (motive := fun _ => Nat) (c.p.h - cdim (c.p.tab.get (c.S0.get (2 * c.v + q.val))))
          (cdim (c.p.tab.get (c.SF.get (2 * c.v + q.val))) - cdim (c.p.tab.get (c.S0.get (2 * c.v + q.val))))
          (memK (2 * c.v + q.val) c.el) :=
  V.toS.inv_res Ro WSf WSb q

end
end KLW

#print axioms KLW.WValidS.clean
#print axioms KLW.WValid.inv
#print axioms KLW.WValid.inv_res
#print axioms KLW.WValidS.inv
#print axioms KLW.WValid.invW
#print axioms KLW.GInvXW.toX
