import OAI.Analysis.LiebThirring.Main
import Lean.Util.CollectAxioms

open OAI.SharpLiebThirring

-- Expand the comparator's MainClaim: full moment, sharpness, and attainment.
example :
    ∀ γ : ℝ, 1 / 2 < γ → γ < 3 / 2 →
      (∀ W : ℝ → ℝ, Admissible γ W →
        negativeMoment γ W ≤ ENNReal.ofReal (sharpConstant γ) * potentialMass γ W) ∧
      optimalConstant γ = ENNReal.ofReal (sharpConstant γ) ∧
      oneStateConstant γ = ENNReal.ofReal (sharpConstant γ) ∧
      Admissible γ (equalityPotential γ) ∧
      0 < potentialMass γ (equalityPotential γ) ∧
      negativeMoment γ (equalityPotential γ) =
        ENNReal.ofReal (sharpConstant γ) * potentialMass γ (equalityPotential γ) :=
  sharp_lieb_thirring

open Lean in
run_cmd do
  let name := `OAI.SharpLiebThirring.sharp_lieb_thirring
  let axioms ← collectAxioms name
  for ax in axioms.toList do
    unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
      throwError "Unexpected axiom in {name}: {ax}"
  IO.println s!"AUDIT_AXIOMS_{name}={String.intercalate "," (axioms.toList.map toString)}"
  IO.println "AUDIT_SCOPE=passed"
