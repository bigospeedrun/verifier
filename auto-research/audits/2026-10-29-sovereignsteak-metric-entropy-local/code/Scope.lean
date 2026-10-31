import OAI.Analysis.MetricEntropy.Main
import Lean.Util.CollectAxioms

open OAI.MetricEntropyDuality
open scoped Pointwise

-- Check the full comparator statement, including finite covers on both sides.
example (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ∃ n : ℕ, 0 < n ∧ ∃ K : Set (RealSpace (Fin n)),
      IsSymmetricConvexBody K ∧
      Coverable K (cube (Fin n)) ∧
      Coverable (polar (cube (Fin n))) (a⁻¹ • polar K) ∧
      b * Real.log (coveringNumber (polar (cube (Fin n))) (a⁻¹ • polar K) : ℝ) <
        Real.log (coveringNumber K (cube (Fin n)) : ℝ) :=
  exists_entropy_duality_counterexample_with_covers a b ha hb

open Lean in
run_cmd do
  let name := `OAI.MetricEntropyDuality.exists_entropy_duality_counterexample_with_covers
  let axioms ← collectAxioms name
  for ax in axioms.toList do
    unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
      throwError "Unexpected axiom in {name}: {ax}"
  IO.println s!"AUDIT_AXIOMS_{name}={String.intercalate "," (axioms.toList.map toString)}"
  IO.println "AUDIT_SCOPE=passed"
