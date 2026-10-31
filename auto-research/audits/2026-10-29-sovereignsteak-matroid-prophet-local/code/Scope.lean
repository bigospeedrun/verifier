import OAI.Probability.MatroidProphet.Main
import Lean.Util.CollectAxioms

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace OAI.MatroidProphet

universe u

-- Expanded comparator type: one sample, finite seed, prefix feasibility,
-- adaptive arrival order, and the 2^(-310) expected-reward guarantee.
example :
    ∀ (n : ℕ) (M : Matroid (Fin n)), M.E = Set.univ →
      ∃ (bits : ℕ) (ν : Measure (Seed bits)), IsProbabilityMeasure ν ∧
      ∃ (A : OnlineRule n bits), Feasible M A ∧
        ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (S V : Ω → Weights n) (R : Ω → Seed bits),
          Measurable S → Measurable V → Measurable R →
          (∀ᵐ ω ∂μ, ∀ e, 0 ≤ S ω e) →
          (∀ᵐ ω ∂μ, ∀ e, 0 ≤ V ω e) →
          iIndepFun (pairedCoordinates S V) μ →
          (∀ e, Measure.map (fun ω => S ω e) μ = Measure.map (fun ω => V ω e) μ) →
          IndepFun (fun ω => (S ω, V ω)) R μ →
          Measure.map R μ = ν →
          Integrable (fun ω => optimum M (V ω)) μ →
          ∀ (π : Ω → ArrivalOrder n), Measurable π →
            Integrable (fun ω => reward A (R ω) (S ω) (V ω) (π ω)) μ ∧
            ((2 : ℝ) ^ 310)⁻¹ * (∫ ω, optimum M (V ω) ∂μ) ≤
              ∫ ω, reward A (R ω) (S ω) (V ω) (π ω) ∂μ :=
  one_sample

end OAI.MatroidProphet

open Lean in
run_cmd do
  let name := `OAI.MatroidProphet.one_sample
  let axioms ← collectAxioms name
  for ax in axioms.toList do
    unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
      throwError "Unexpected axiom in {name}: {ax}"
  IO.println s!"AUDIT_AXIOMS_{name}={String.intercalate "," (axioms.toList.map toString)}"
  IO.println "AUDIT_SCOPE=passed"
