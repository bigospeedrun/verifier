import OAI.Combinatorics.SphericalRamsey.Result
import Lean.Util.CollectAxioms

open OAI.GrahamSpherical

example :
    witness.ncard = 12 ∧
    witness ⊆ Metric.sphere (0 : Point 2) 1 ∧
    (∀ n : ℕ, 0 < n → ∃ color : Point n → Fin 50, AvoidsCopy witness color) ∧
    ¬ EuclideanRamsey witness :=
  OAI.GrahamSphericalReference.challenge

open Lean in
run_cmd do
  for name in [`OAI.GrahamSpherical.full_main,
      `OAI.GrahamSphericalReference.challenge] do
    let axioms ← collectAxioms name
    for ax in axioms.toList do
      unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
        throwError "Unexpected axiom in {name}: {ax}"
    IO.println s!"AUDIT_AXIOMS_{name}={String.intercalate "," (axioms.toList.map toString)}"
  IO.println "AUDIT_SCOPE=passed"
