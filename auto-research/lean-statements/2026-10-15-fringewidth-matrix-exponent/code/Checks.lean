import Statement

open OAI.MatrixMultiplication.Arithmetic
open BigOSpeedrun.MatrixMultiplication

-- Check exact rational substitution independently of the adapter's spelling.
example : Bound ((9 : Rat) / 4) ↔
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, 1 ≤ n → ∃ P : MatrixAlgorithm ℂ n n n,
        P.Correct ∧ (P.cost : ℝ) ≤ C * (n : ℝ) ^ ((9 : ℝ) / 4 + ε) := by
  norm_num [Bound, AdmissibleExponent]

-- A theorem at 9/4 cannot be reused verbatim as a theorem at 2.
-- This tests elaboration/type matching, not the production Comparator.
example (h : Bound ((9 : Rat) / 4)) : Bound ((9 : Rat) / 4) := by
  fail_if_success have : Bound (2 : Rat) := h
  exact h

example (h : Bound (2 : Rat)) : Bound ((9 : Rat) / 4) :=
  h.mono (by norm_num)

-- An actual one-by-one circuit: inputs are free, multiplication costs one.
def scalarAlgorithm : MatrixAlgorithm ℂ 1 1 1 where
  registers := 3
  program := .step (.step (.step .nil (.input (.inl (0, 0))))
    (.input (.inr (0, 0)))) (.mul 1 0)
  output := fun _ _ => 0

theorem scalar_correct : scalarAlgorithm.Correct := by
  intro A B
  ext i j
  fin_cases i
  fin_cases j
  change A 0 0 * B 0 0 = (A * B) 0 0
  simp [Matrix.mul_apply]

theorem scalar_cost : scalarAlgorithm.cost = 1 := by rfl

#print axioms BigOSpeedrun.MatrixMultiplication.Bound
#print axioms BigOSpeedrun.MatrixMultiplication.bound_iff
#print axioms BigOSpeedrun.MatrixMultiplication.Bound.mono
#print axioms scalar_correct
#print axioms scalar_cost
