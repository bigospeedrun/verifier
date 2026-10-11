/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.AllEdges.Host
public import Submission.ThreeSumApsp.Programs.Sec3.Theorem17.ClaimAtParameters

/-!
# Theorem 17 for the all-edges host

The all-edges host obeys the bound of Theorem 17 with the parameters `D = ⌊n^{1/18}⌋`,
`g = ⌈D^{0.0315}⌉`: `claim_ae_theorem_17₂₆ : Claim.Theorem_17 aeModel strassen paramD₂₆ paramG₂₆`.
Beside the host of Theorem 17 it fills the `n²` marks, `O(n²)`, and makes at most `n²` more scans
of `O(√D/g)` steps, `O(n² √D/g)`; both are within the third term `n² D g`.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## From a host to the claim -/

/-- `claim17_of_host` for the all-edges task. -/
theorem aeClaim17_of_host (MM : ℕ → ℝ) (D g : ℕ → ℕ) (time : (List ℕ → ℕ) → ℕ → ℕ → ℕ)
    (need : (List ℕ → Need) → ℕ → ℕ → Need)
    (host : ∀ (Q : Program) (pS : ℕ) (Tn : List ℕ → ℕ) (r : List ℕ → Need), PolyNeedN r →
      SolvesN lopDetectTask Q pS Tn r →
      ∃ (R : Program) (p' : ℕ), Solves aeTask (Q ++ R) p' (time Tn) (need r) ∧ PolyNeed (need r))
    (bound : ObeysBound17 MM D g time) :
    Claim.Theorem_17 aeModel MM D g := by
  obtain ⟨C, hC, bound⟩ := bound
  refine ⟨C, hC, fun T hT => ?_⟩
  obtain ⟨Q, pS, Tn, r, hpoly, hsolves, hle⟩ := hT
  obtain ⟨R, p', hs, hp⟩ := host Q pS Tn r hpoly hsolves
  exact ⟨timeUpTo (time Tn), hs.solvedIn hp, fun n κ u h16 hDn hg1 hg hκ hu =>
    timeUpTo_le fun U hU =>
      bound Tn T hle n U κ h16 hDn hg1 hg hκ (hU.trans (max_le hu (by positivity)))⟩

/-! ## The need -/

/-- The need of the all-edges host is polynomial if that of the host of Theorem 17 is. -/
theorem aeHostNeed_poly {Dfun Gfun wD wG : ℕ → ℕ} {need : List ℕ → Need}
    (h : PolyNeed (hostNeed Dfun Gfun wD wG need)) :
    PolyNeed (aeHostNeed Dfun Gfun wD wG need) := by
  have hw : PolyBounded fun n U => (hostNeed Dfun Gfun wD wG need n U).word :=
    h.word PolyBounded.fst PolyBounded.snd
  have hc : PolyBounded fun n U => (hostNeed Dfun Gfun wD wG need n U).cells :=
    h.cells PolyBounded.fst PolyBounded.snd
  have hd : PolyBounded fun n U => (hostNeed Dfun Gfun wD wG need n U).depth :=
    h.depth PolyBounded.fst PolyBounded.snd
  unfold aeHostNeed
  poly_need [hw, hc, hd, PolyBounded.fst]

/-! ## The time -/

private theorem steps_tScanCall :
    Steps (fun θ => tScanCall (pieceSizeNat θ.D θ.g)) fun θ => Real.sqrt θ.D / θ.g := by
  have hone : ∀ θ : CostParams, θ.Hyp → 1 ≤ Real.sqrt θ.D / θ.g := fun θ hθ =>
    (one_le_div hθ.g_pos).2 hθ.hgD
  have hpiece : Steps (fun θ => pieceSizeNat θ.D θ.g) fun θ => Real.sqrt θ.D / θ.g := by
    refine Dominated.of_le_const_mul (C := 2) (by norm_num) fun θ hθ => ?_
    have hlt : (pieceSizeNat θ.D θ.g : ℝ) * θ.g < (Nat.sqrt θ.D : ℝ) + θ.g := by
      exact_mod_cast Nat.ceilDiv_mul_lt (a := Nat.sqrt θ.D) hθ.hg
    rw [← mul_div_assoc, le_div_iff₀ hθ.g_pos]
    linarith [hlt, Real.nat_sqrt_le_real_sqrt (a := θ.D), hθ.hgD]
  exact (hpiece.const_mul.add (.const hone)).add (.const hone)

/-- A scan with the bookkeeping of the marks. -/
private theorem steps_tScanCall20 :
    Steps (fun θ => tScanCall (pieceSizeNat θ.D θ.g) + 20) fun θ => Real.sqrt θ.D / θ.g :=
  steps_tScanCall.add (.const fun θ hθ => (one_le_div hθ.g_pos).2 hθ.hgD)

private theorem kappaOf_le_of_hyp {θ : CostParams} (hθ : θ.Hyp) : kappaOf θ.n θ.U ≤ θ.κ := by
  rcases Nat.eq_zero_or_pos θ.U with hU | hU
  · simp [kappaOf, hU, hθ.hκ]
  · exact kappaOf_le ((by norm_num : 2 ≤ 16).trans hθ.sixteen_le_n) hU hθ.hκ hθ.hUn

private theorem steps_falsePositiveBound :
    Steps (fun θ => falsePositiveBound θ.n θ.U θ.D + 1) fun θ =>
      θ.κ * (θ.n : ℝ) ^ 3 * Real.log θ.n / Real.sqrt θ.D := by
  have hconst : 0 ≤ Hashing.falsePositiveConst :=
    zero_le_one.trans Hashing.one_le_falsePositiveConst
  refine Steps.add ?_ (.const fun θ hθ => ?_)
  · refine Dominated.of_le_const_mul hconst fun θ hθ => (Nat.floor_le ?_).trans ?_
    · have hκ' : 0 ≤ kappaOf θ.n θ.U := zero_le_one.trans (one_le_kappaOf θ.n θ.U)
      positivity
    · gcongr
      exact kappaOf_le_of_hyp hθ
  · rw [one_le_div hθ.sqrt_pos]
    calc Real.sqrt θ.D ≤ mon 1 0 0 θ := by simpa [mon_eq] using hθ.sqrt_le_n
      _ ≤ mon 3 0 1 θ := Scale.mon_le_mon (by decide) hθ
      _ = θ.κ * (θ.n : ℝ) ^ 3 * Real.log θ.n := by
          rw [mon_eq]
          ring

/-- `n²` steps of `O(√D/g)` are within `n² D g`. -/
private theorem sqrt_div_mul_le_termBuild {θ : CostParams} (hθ : θ.Hyp) :
    Real.sqrt θ.D / θ.g * (θ.n : ℝ) ^ 2 ≤ termBuild θ.n θ.D θ.g := by
  have hg := hθ.one_le_g
  have hs := hθ.one_le_sqrt
  have hsq : Real.sqrt θ.D * Real.sqrt θ.D = θ.D := Real.mul_self_sqrt θ.D.cast_nonneg
  have h1 : Real.sqrt θ.D / θ.g ≤ Real.sqrt θ.D := div_le_self (by positivity) hg
  have h2 : Real.sqrt θ.D ≤ (θ.D : ℝ) * θ.g := by nlinarith
  rw [termBuild]
  have hn : 0 ≤ (θ.n : ℝ) ^ 2 := by positivity
  nlinarith

/-- **The scans of the all-edges host**: at most `F(p) + n²` scans of `O(√D/g)` steps. -/
private theorem steps_aeScans :
    Steps (fun θ => (tScanCall (pieceSizeNat θ.D θ.g) + 20) *
      (falsePositiveBound θ.n θ.U θ.D + θ.n * θ.n)) budget := by
  have h1 : Steps (fun θ => (tScanCall (pieceSizeNat θ.D θ.g) + 20) *
      (falsePositiveBound θ.n θ.U θ.D + 1)) budget := by
    refine (steps_tScanCall20.mul steps_falsePositiveBound).mono_right fun θ hθ =>
      le_trans (le_of_eq ?_) (termScans_le_budget θ)
    have hr : 0 < Real.sqrt θ.D := hθ.sqrt_pos
    have hg : (0 : ℝ) < θ.g := hθ.g_pos
    unfold termScans
    field_simp
  have hnn : StepsMon (fun θ => θ.n * θ.n) 2 0 0 := by growth [steps_n]
  have h2 : Steps (fun θ => (tScanCall (pieceSizeNat θ.D θ.g) + 20) * (θ.n * θ.n)) budget := by
    refine (steps_tScanCall20.mul (steps_of_softO hnn)).mono_right fun θ hθ => ?_
    have : costScale.mon ![2, 0, 0] θ = (θ.n : ℝ) ^ 2 := by
      simpa using mon_eq 2 0 0 θ
    rw [this]
    exact (sqrt_div_mul_le_termBuild hθ).trans (termBuild_le_budget hθ)
  refine (h1.add h2).mono_left fun θ hθ => ?_
  rw [← Nat.mul_add]
  gcongr
  have hn := hθ.one_le_n_nat
  have : 1 ≤ θ.n * θ.n := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  omega

private theorem steps_instances : Steps (fun θ => 4 * θ.n * θ.g) fun θ => (θ.n : ℝ) * θ.g :=
  (Steps.const_mul (Dominated.refl _ _)).mul (Dominated.refl _ _)

private theorem steps_tWrites :
    StepsMon (fun θ => tWrites θ.n θ.D (pieceSizeNat θ.D θ.g)) 1 2 0 := by
  unfold tWrites
  growth [steps_tWriteX, steps_tWriteY]

private theorem steps_instances_mul_tWrites :
    Steps (fun θ => 4 * θ.n * θ.g * tWrites θ.n θ.D (pieceSizeNat θ.D θ.g)) budget :=
  (steps_instances.mul (steps_of_softO steps_tWrites)).mono_right fun θ hθ =>
    le_trans (le_of_eq (by
      simp only [termBuild, mon_eq, pow_zero, mul_one, pow_one, Real.sq_sqrt θ.D.cast_nonneg]
      ring)) (termBuild_le_budget hθ)

/-- Reading the answers of one instance and setting the marks: a constant number of steps for each
query pair. -/
private theorem steps_tAEAnswers :
    Steps (fun θ => tAEAnswers (queryCapNat θ.n θ.D)) fun θ => (θ.n : ℝ) ^ 2 / Real.sqrt θ.D := by
  refine Steps.add (Steps.const_mul (Dominated.of_le fun θ hθ => cast_queryCapNat_le hθ))
    (.const fun θ hθ => ?_)
  rw [one_le_div hθ.sqrt_pos]
  exact hθ.sqrt_le_n.trans (le_self_pow₀ hθ.one_le_n two_ne_zero)

/-- The time of the all-edges host without the calls of the solver. -/
private noncomputable def aeRest (tD tG : ℕ → ℕ) (θ : CostParams) : ℕ :=
  fillTime (θ.n * θ.n) + 40 + hostSetup tD tG θ.n θ.D + aeHostMain (fun _ => 0) θ.n θ.U θ.D θ.g

private theorem supTime_zero (n D cap : ℕ) : supTime (fun _ => 0) n D cap = 0 := by
  simp [supTime]

private theorem not_smallCase_of_hyp {θ : CostParams} (hθ : θ.Hyp) : ¬ SmallCase θ.n θ.D θ.g := by
  have hg : θ.g ≤ Nat.sqrt θ.D := by
    rw [Nat.le_sqrt']
    exact_mod_cast (Real.le_sqrt θ.g.cast_nonneg θ.D.cast_nonneg).1 hθ.hgD
  have hD16 := hθ.hD16
  have hDn := hθ.hDn
  have hg1 := hθ.hg
  unfold SmallCase
  omega

private theorem aeHostTime_eq {θ : CostParams} (hθ : θ.Hyp) {Dfun Gfun : ℕ → ℕ} (tD tG : ℕ → ℕ)
    (Tn : List ℕ → ℕ) (hD : Dfun θ.n = θ.D) (hG : Gfun θ.D = θ.g) :
    aeHostTime Dfun Gfun tD tG Tn θ.n θ.U
      = 4 * θ.n * θ.g * supTime Tn θ.n θ.D (queryCapNat θ.n θ.D) + aeRest tD tG θ := by
  rw [aeHostTime, aeCoreTime, hD, hG, if_neg (not_smallCase_of_hyp hθ), aeRest, aeHostMain,
    aeHostMain, aeLoopBound, aeLoopBound, supTime_zero]
  ring

private noncomputable def restBound (θ : CostParams) : ℝ :=
  (θ.n : ℝ) * θ.g * ((θ.n : ℝ) ^ 2 / Real.sqrt θ.D) + budget θ

private theorem Steps.toRest {t : CostParams → ℕ} (h : Steps t budget) : Steps t restBound :=
  h.mono_right fun θ _ => le_add_of_nonneg_left (by positivity)

private theorem steps_hostSetup {tD tG : ℕ → ℕ} (hD : Steps (fun θ => tD θ.n) budget)
    (hG : Steps (fun θ => tG θ.D) budget) : Steps (fun θ => hostSetup tD tG θ.n θ.D) budget :=
  hD.add hG
  |>.add (by growth [steps_sqrt] : StepsMon _ 0 1 0).withinBuild
  |>.add (Scale.SoftO.const _).withinBuild

private theorem steps_aeLoopBound :
    Steps (fun θ => aeLoopBound (fun _ => 0) θ.n θ.U θ.D θ.g) restBound :=
  steps_instances_mul_tWrites.toRest
  |>.mul_add ((Scale.SoftO.const 0).withinBuild.toRest.mono_left fun θ _ => by
    rw [supTime_zero, Nat.mul_zero])
  |>.mul_add ((steps_instances.mul steps_tAEAnswers).mono_right fun _ hθ =>
    le_add_of_nonneg_right (budget_nonneg hθ))
  |>.add steps_aeScans.toRest
  |>.add (Scale.SoftO.const _).withinBuild.toRest

private theorem steps_fill : Steps (fun θ => fillTime (θ.n * θ.n)) budget := by
  have h : StepsMon (fun θ => 13 * (θ.n * θ.n) + 6) 2 0 0 := by growth [steps_n]
  exact h.withinBuild

private theorem steps_aeRest {tD tG : ℕ → ℕ} (hD : Steps (fun θ => tD θ.n) budget)
    (hG : Steps (fun θ => tG θ.D) budget) : Steps (aeRest tD tG) restBound :=
  (steps_fill.toRest.add (Scale.SoftO.const _).withinBuild.toRest).add
    (steps_hostSetup hD hG).toRest |>.add <|
    steps_chooseTime.toRest
    |>.add steps_tQueryCapNat.withinBuild.toRest
    |>.add steps_tCeilDiv_piece.withinBuild.toRest
    |>.add steps_tCeilDiv_num.withinBuild.toRest
    |>.add steps_tBitLen.withinScans.toRest
    |>.add steps_tDblTable.withinScans.toRest
    |>.add ((Scale.SoftO.const _).mul steps_tResidues).withinScans.toRest
    |>.add steps_tClasses.withinBuild.toRest
    |>.add steps_tChunks.withinBuild.toRest
    |>.add steps_aeLoopBound
    |>.add (Scale.SoftO.const _).withinBuild.toRest

private theorem cast_supTime_le {Tn : List ℕ → ℕ} {T : ℕ → ℕ → ℕ → ℝ}
    (hT : ∀ n D w w' : ℕ, 1 ≤ n → 1 ≤ D → w ≤ w' → (Tn [n, D, w] : ℝ) ≤ T n D w') {n D : ℕ}
    (hn : 1 ≤ n) (hD : 1 ≤ D) (cap : ℕ) : ((supTime Tn n D cap : ℕ) : ℝ) ≤ T n D cap := by
  obtain ⟨w, hw, hsup⟩ : ∃ w ∈ Finset.range (cap + 1),
      (Finset.range (cap + 1)).sup (fun w => Tn [n, D, w]) = Tn [n, D, w] :=
    Finset.exists_mem_eq_sup _ ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩ _
  rw [supTime, hsup]
  exact hT n D w cap hn hD (Nat.lt_succ_iff.1 (Finset.mem_range.1 hw))

/-- **The bound of Theorem 17 for the all-edges host.** -/
theorem obeysBound17_aeHostTime (D g : ℕ → ℕ) {Dfun Gfun tD tG : ℕ → ℕ}
    (hDf : ∀ n, Dfun n = D n) (hGf : ∀ n, 1 ≤ n → Gfun (D n) = g n)
    (hD : Steps (fun θ => tD θ.n) budget) (hG : Steps (fun θ => tG θ.D) budget) :
    ObeysBound17 strassen D g (aeHostTime Dfun Gfun tD tG) := by
  obtain ⟨C, hC, hsteps⟩ := steps_aeRest hD hG
  refine ⟨C, hC, fun Tn T hT n U κ h16 hDn hg1 hg hκ hU => ?_⟩
  have hθ : CostParams.Hyp ⟨n, D n, g n, U, κ⟩ := ⟨h16, hDn, hg1, hg, hκ, hU⟩
  have hn1 : 1 ≤ n := hθ.one_le_n_nat
  have hD1 : 1 ≤ D n := hθ.one_le_D_nat
  have hsolver := cast_supTime_le hT hn1 hD1 (queryCapNat n (D n))
  have hrest : (aeRest tD tG ⟨n, D n, g n, U, κ⟩ : ℝ)
      ≤ C * ((n : ℝ) * g n * ((n : ℝ) ^ 2 / Real.sqrt (D n)) + budget ⟨n, D n, g n, U, κ⟩) :=
    hsteps _ hθ
  have hquery : 0 ≤ C * ((n : ℝ) * g n * ((n : ℝ) ^ 2 / Real.sqrt (D n))) := by positivity
  rw [aeHostTime_eq hθ tD tG Tn (hDf n) (hGf n hn1)]
  rw [queryCapNat_eq n hD1] at hsolver ⊢
  push_cast
  calc 4 * (n : ℝ) * g n * (supTime Tn n (D n) (queryCap n (D n)) : ℝ)
        + (aeRest tD tG ⟨n, D n, g n, U, κ⟩ : ℝ)
      ≤ 4 * (n : ℝ) * g n * T n (D n) (queryCap n (D n))
        + C * ((n : ℝ) * g n * ((n : ℝ) ^ 2 / Real.sqrt (D n)) + budget ⟨n, D n, g n, U, κ⟩) := by
        gcongr
    _ ≤ bound17 strassen D g C T n κ := by
        unfold bound17 budget
        linarith [hquery]

/-! ## The parameter routines `D = ⌊n^{1/18}⌋`, `g = ⌈D^{0.0315}⌉` -/

private def paramProcs (o : ℕ) : Program :=
  [powLtBody, rootCeilBody o, d26Body (o + 1), g26Body (o + 1)]

private def wD26 (n : ℕ) : ℕ := (n + 1) * (paramD₂₆Nat n + 1) + 19

private def wG26 (D : ℕ) : ℕ := D ^ 63 * paramG₂₆Nat D + 2001

private theorem paramProcs_get (Q R : Program) {i : ℕ} {body : Stmt}
    (h : (paramProcs Q.length)[i]? = some body) :
    (Q ++ paramProcs Q.length ++ R)[Q.length + i]? = some body := by
  rw [List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
  exact getElem?_append_of_eq_some h R

private theorem paramProc_d26 (Q R : Program) :
    ParamProc (Q ++ paramProcs Q.length ++ R) (Q.length + 2) paramD₂₆Nat tD26 wD26 := by
  intro lim d x μ _ _ hw hd
  exact ⟨_, paramProcs_get Q R (i := 2) rfl, d26_spec (paramProcs_get Q R (i := 1) rfl)
    (paramProcs_get Q R (i := 0) rfl) hw (by omega)⟩

private theorem paramProc_g26 (Q R : Program) :
    ParamProc (Q ++ paramProcs Q.length ++ R) (Q.length + 3) paramG₂₆Nat tG26 wG26 := by
  intro lim d x μ hx _ hw hd
  exact ⟨_, paramProcs_get Q R (i := 3) rfl, g26_spec (paramProcs_get Q R (i := 1) rfl)
    (paramProcs_get Q R (i := 0) rfl) hx hw (by omega)⟩

private theorem polyBounded_paramD₂₆Nat : PolyBounded fun n _ => paramD₂₆Nat n :=
  PolyBounded.fst.of_le fun n _ => paramD₂₆Nat_le n

private theorem polyBounded_paramG₂₆Nat {D : ℕ → ℕ} (hD : PolyBounded fun n _ => D n) :
    PolyBounded fun n _ => paramG₂₆Nat (D n) :=
  (by growth_poly [hD] : PolyBounded fun n _ => D n + 1).of_le fun n _ => by
    rcases Nat.eq_zero_or_pos (D n) with h0 | hpos
    · simp [h0, paramG₂₆Nat, rootCeil]
    · exact (paramG₂₆Nat_le hpos).trans (Nat.le_succ _)

private theorem polyBounded_wD26 : PolyBounded fun n _ => wD26 n := by
  unfold wD26
  growth_poly [polyBounded_paramD₂₆Nat]

private theorem polyBounded_wG26 : PolyBounded fun n _ => wG26 (paramD₂₆Nat n) := by
  unfold wG26
  growth_poly [polyBounded_paramD₂₆Nat, polyBounded_paramG₂₆Nat polyBounded_paramD₂₆Nat]

private theorem steps_paramD₂₆Nat : StepsMon (fun θ => paramD₂₆Nat θ.n) 1 0 0 :=
  steps_n.of_le fun θ _ => paramD₂₆Nat_le θ.n

private theorem steps_tD26 : StepsMon (fun θ => tD26 θ.n) 1 0 0 := by
  unfold tD26
  growth [steps_paramD₂₆Nat]

private theorem steps_tG26 : StepsMon (fun θ => tG26 θ.D) 0 2 0 := by
  have hg : StepsMon (fun θ => paramG₂₆Nat θ.D) 0 2 0 :=
    steps_D.of_le fun _ hθ => paramG₂₆Nat_le hθ.one_le_D_nat
  unfold tG26
  growth [hg]

/-- **Theorem 17 for the all-edges host**, with `D := ⌊n^{1/18}⌋` and `g := ⌈D^{0.0315}⌉`. -/
theorem claim_ae_theorem_17₂₆ : Claim.Theorem_17 aeModel strassen paramD₂₆ paramG₂₆ := by
  refine aeClaim17_of_host strassen paramD₂₆ paramG₂₆
    (aeHostTime paramD₂₆Nat paramG₂₆Nat tD26 tG26)
    (aeHostNeed paramD₂₆Nat paramG₂₆Nat wD26 wG26) (fun Q pS Tn r hr hs => ?_)
    (obeysBound17_aeHostTime paramD₂₆ paramG₂₆ paramD₂₆Nat_eq (fun _ hn => paramG₂₆Nat_eq hn)
      steps_tD26.withinBuild steps_tG26.withinBuild)
  have h := ae_solves (P₀ := Q ++ paramProcs Q.length) (hs.append _) (paramProc_d26 Q)
    (paramProc_g26 Q) (fun _ hn => one_le_paramD₂₆Nat hn)
  rw [List.append_assoc] at h
  exact ⟨_, _, h, aeHostNeed_poly (hostNeed_poly polyBounded_paramD₂₆Nat
    (polyBounded_paramG₂₆Nat polyBounded_paramD₂₆Nat) polyBounded_wD26 polyBounded_wG26 hr)⟩

end Light.Sec3
