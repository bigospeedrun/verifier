import OAI.Geometry.PlaneColoring.Five
import Lean.Util.CollectAxioms

namespace Audit

-- Literal definition from the pinned comparator, with its original binders.
def ComparatorProperColoring (colorCount : ℕ)
    (coloring : ℂ → Fin colorCount) : Prop :=
  ∀ point otherPoint : ℂ, ‖point - otherPoint‖ = 1 →
    coloring point ≠ coloring otherPoint

example : ¬ ∃ coloring : ℂ → Fin 5, ComparatorProperColoring 5 coloring := by
  simpa only [ComparatorProperColoring, OAI.EuclideanFiveColor.ProperColoring] using
    OAI.EuclideanFiveColor.no_proper_five_coloring

end Audit

open Lean in
run_cmd do
  let name := `OAI.EuclideanFiveColor.no_proper_five_coloring
  let axioms ← collectAxioms name
  for ax in axioms.toList do
    unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
      throwError "Unexpected axiom in {name}: {ax}"
  IO.println s!"AUDIT_AXIOMS_{name}={String.intercalate "," (axioms.toList.map toString)}"
  IO.println "AUDIT_SCOPE=passed"
