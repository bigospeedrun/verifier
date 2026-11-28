import Submission.PlanToWord
import Submission.EngineRecursion
import Submission.ReelCompile
import Submission.WalshTemplate
set_option linter.all false

/-! # Route B: ripple engine from a template family

The template's own strict call rate (`QCandidate.Good`, after OpenAI's `Candidate.Good`, KernelPassSearch) is the
moment condition of this tree's engine (`SlotEngine.RealisesRule.ripple_engine`) for a unit whose targets all have the same size: the unit's
block engine (`PlanUnit.engine`) has target multiset `rows × {2·arity}` and block multiset
`calls × {2}`, so no tensor power, padding or block cut is needed. -/

namespace OAI.PowerSaving.RouteB
open Binary GenMove RoleKernel RAM
open OAI.Computability.NearSquareRoot.KernelPass

noncomputable section

/-- The template's strict call rate, as the engine's moment condition. -/
lemma rate_of {calls rows A : ℕ} {z : ℝ} (hrate : (calls : ℝ) < rows * (A : ℝ) ^ z) :
    (calls : ℝ) * ((2 : ℕ) : ℝ) ^ z ≤ rows * (((2 * A : ℕ) : ℝ)) ^ z := by
  have hc := hrate.le
  have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ z := Real.rpow_nonneg (by norm_num) z
  calc (calls : ℝ) * ((2 : ℕ) : ℝ) ^ z ≤ (rows * (A : ℝ) ^ z) * (2 : ℝ) ^ z := by
        push_cast; exact mul_le_mul_of_nonneg_right hc h2
    _ = rows * (((2 * A : ℕ) : ℝ)) ^ z := by
        push_cast
        rw [Real.mul_rpow (by norm_num) (Nat.cast_nonneg A)]; ring

universe u

/-- The block engine of a unit: rows are the live roles, each with the full basis of `Bit A`
as its target block (`2·arity` coordinates). -/
def PlanUnit.engine {t : QCandidate} (P : PlanUnit t) (hA : 2 ≤ t.arity) (hW : 1 ≤ t.rows) :
    SlotEngine (Bit t.arity) P.ρ (Fin t.rows) :=
  have hX : (Layout.someLayout (Bit t.arity)).n = 2 * t.arity :=
    (Layout.someLayout _).card.symm.trans (cardBit _)
  ⟨Layout.someLayout _, Layout.someLayout _, Layout.someLayout _, hX ▸ (by omega),
    (Layout.someLayout (Fin t.rows)).card ▸ (by simp; omega), P.e, P.he, fun _ => 2 * t.arity,
    fun _ => hX.ge, fun _ => P.tz, fun _ => P.tind, P.wd, hX ▸ P.hP, P.hw⟩

/-- A unit built from a correct template whose strict call rate holds at `num/den` gives a
ripple engine at every larger exponent. -/
theorem rippleEngine_of_planUnit {num den : ℕ} {t : QCandidate} (hg : t.Good num den)
    (hθ : 0 < (num : ℝ) / den) (P : PlanUnit t) {zE : ℝ} (h12 : (num : ℝ) / den < zE)
    (hzE : zE ≤ 1) : RippleEngine.{u} zE := by
  obtain ⟨hA, hW, -, hrate⟩ := hg
  let E := P.engine (by omega) (by omega)
  have hX : E.mx = 2 * t.arity := (Layout.someLayout _).card.symm.trans (cardBit _)
  have hQ : E.W = t.rows := (Layout.someLayout (Fin t.rows)).card.symm.trans (Fintype.card_fin _)
  let R : EngineCost.Rule := ⟨E.W, E.mx, t.program.calls, 2, E.slots_pos, by omega, by omega⟩
  have H : E.RealisesRule R := ⟨rfl, rfl, P.hhist, fun _ => hX.symm⟩
  have hR : (R.P : ℝ) * (R.r : ℝ) ^ ((num : ℝ) / den) ≤ R.W * (R.m : ℝ) ^ ((num : ℝ) / den) := by
    show (t.program.calls : ℝ) * ((2 : ℕ) : ℝ) ^ _ ≤ (E.W : ℝ) * (E.mx : ℝ) ^ _
    rw [hQ, hX]; exact rate_of hrate
  exact ⟨hθ.le.trans h12.le, fun cl m ι k v =>
    H.ripple_engine _ le_rfl hR hθ.le h12 hzE m cl k v⟩

/-- The full standard basis of `Bit A`, indexed by `Fin (2*A)`. -/
def fullBasis2 (A : ℕ) : Fin (2 * A) → Space (Bit A) :=
  fun i => fullBasis (A := A) (Fin.cast (cardBit A).symm i)

lemma fullBasis2_indep (A : ℕ) : LinearIndependent F (fullBasis2 A) :=
  (fullBasis_indep (A := A)).comp _ (Fin.cast_injective _)

lemma blockMat_fullBasis2 (A : ℕ) :
    blockMat (fullBasis2 A) = blockMat (fullBasis (A := A)) :=
  congrArg walshConj (phaseOf_comp_equiv (finCongr (cardBit A).symm) fullBasis)

/-- The unit of any good template (generic in the template). -/
def planUnitOf {num den : ℕ} (t : QCandidate) (hg : t.Good num den) : PlanUnit t where
  ρ := Fin t.rows ⊕ Roles t.program
  e := Sum.inl
  he := Sum.inl_injective
  tz := fullBasis2 t.arity
  tind := fullBasis2_indep _
  wd := unitWord t.program
  hw := by
    rw [blockMat_fullBasis2]
    exact unit_live t.program hg.2.2.1
  hP := unitWord_proper t.program (by have := hg.1; omega)
  hhist := unitWord_ranks t.program

/-- A good template at exponent `num/den` gives a ripple engine at every larger exponent. -/
theorem rippleEngine_of_good {num den : ℕ} {t : QCandidate} (hg : t.Good num den)
    (hθ : 0 < (num : ℝ) / den) {z : ℝ} (h : (num : ℝ) / den < z) (hz : z ≤ 1) :
    RippleEngine.{u} z :=
  rippleEngine_of_planUnit.{u} hg hθ (planUnitOf t hg) h hz

/-- Rational templates at every exponent above `κ`: the single interface between the template
construction and everything downstream (engine, DFT, convolution, timing). -/
def TemplatesAbove (κ : ℝ) : Prop :=
  ∀ num den : ℕ, κ < (num : ℝ) / den → ∃ t : QCandidate, t.Good num den

/-- **Route B's global template threshold.** The Walsh template family proves templates above it
(`templates_wall`); everything downstream is stated against it, so a better template
theorem only has to lower this value and re-prove `templates_wall`. The two side facts below are
what downstream uses. -/
def templateWall : ℝ := 1/2

/-- Templates above the global threshold (the Walsh template family `walshTemplate_above_half`, i.e. `templates_of_rate` with
`rateOK_of_half`). -/
theorem templates_wall : TemplatesAbove templateWall := walshTemplate_above_half

lemma templateWall_nonneg : 0 ≤ templateWall := by norm_num [templateWall]
lemma templateWall_le_half : templateWall ≤ 1/2 := by norm_num [templateWall]

/-- A family of templates above `κ ≥ 0` has a member strictly below any real `z > κ`. -/
theorem exists_good_below {κ : ℝ} (hT : TemplatesAbove κ) (hκ : 0 ≤ κ) {z : ℝ} (hz : κ < z) :
    ∃ (num den : ℕ) (t : QCandidate), t.Good num den ∧ (0:ℝ) < (num : ℝ) / den ∧
      (num : ℝ) / den < z := by
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hz
  have hqpos : (0:ℚ) < q := by
    have : (0:ℝ) < (q:ℝ) := by linarith
    exact_mod_cast this
  have hcast : ((q.num.toNat : ℕ) : ℝ) / (q.den : ℝ) = (q : ℝ) := by
    have hn : ((q.num.toNat : ℕ) : ℤ) = q.num := Int.toNat_of_nonneg (Rat.num_nonneg.mpr hqpos.le)
    have : ((q.num.toNat : ℕ) : ℝ) = ((q.num : ℤ) : ℝ) := by exact_mod_cast hn
    rw [this]
    exact_mod_cast Rat.num_div_den q
  obtain ⟨t, hg⟩ := hT q.num.toNat q.den (by rw [hcast]; exact hq1)
  exact ⟨q.num.toNat, q.den, t, hg, by rw [hcast]; linarith, by rw [hcast]; exact hq2⟩

/-- Templates above `κ ≥ 0` give a ripple engine at every exponent `z ∈ (κ, 1]`. -/
theorem rippleEngine_of_templates {κ : ℝ} (hT : TemplatesAbove κ) (hκ : 0 ≤ κ) {z : ℝ}
    (hz : κ < z) (hz1 : z ≤ 1) : RippleEngine.{u} z := by
  obtain ⟨num, den, t, hg, h0, hlt⟩ := exists_good_below hT hκ hz
  exact rippleEngine_of_good hg h0 hlt hz1

end

end OAI.PowerSaving.RouteB
