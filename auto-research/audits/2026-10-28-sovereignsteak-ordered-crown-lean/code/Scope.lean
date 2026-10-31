import OrderedRemoval.Crown.Complete
import Lean.Util.CollectAxioms

open OrderedRemoval OrderedRemoval.Crown

-- Check the literal nine-entry pattern, rather than relying on its name.
example : Crown.fixedH 0 0 = false := by decide
example : Crown.fixedH 0 1 = true := by decide
example : Crown.fixedH 0 2 = true := by decide
example : Crown.fixedH 1 0 = true := by decide
example : Crown.fixedH 1 1 = false := by decide
example : Crown.fixedH 1 2 = true := by decide
example : Crown.fixedH 2 0 = true := by decide
example : Crown.fixedH 2 1 = true := by decide
example : Crown.fixedH 2 2 = false := by decide

-- A concrete copy is counted by the ordered-copy definition.
example : Crown.copyCount (Crown.fixedH : BinaryMatrix 3) = 1 := by decide

-- Check the public mathematical scope and quantifier order by type checking
-- an independent statement against the author's capstone theorem.
example (c C ε₀ : ℝ) (hc : 0 < c) (hC : 0 < C) (hε₀ : 0 < ε₀) :
    ∃ ε : ℝ, 0 < ε ∧ ε < ε₀ ∧ ∀ N : ℕ,
      ∃ n : ℕ, max 1 N ≤ n ∧ ∃ A : BinaryMatrix n,
        (∀ B : BinaryMatrix n, Crown.HFree B →
          ε * (n : ℝ)^2 ≤ (hammingDistance A B : ℝ)) ∧
        (Crown.copyCount A : ℝ) < c * Real.rpow ε C * (n : ℝ)^6 := by
  exact no_polynomial_removal_bound c C ε₀ hc hC hε₀

open Lean in
run_cmd do
  let axioms ← collectAxioms `OrderedRemoval.Crown.no_polynomial_removal_bound
  IO.println s!"AUDIT_AXIOMS={String.intercalate "," (axioms.toList.map toString)}"
  IO.println "AUDIT_SCOPE=passed"
