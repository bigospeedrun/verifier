import MatrixMultiplication

/-!
Copyright 2026 fringewidth. Licensed under Apache-2.0.
Adapter by fringewidth with OpenAI Codex (GPT-6) assistance.
The arithmetic circuit model is OpenAI's unchanged MatrixMultiplication.lean.

Stage that file as module `MatrixMultiplication` and this file as `Statement`.
This is a proposed target, not an enabled proof-submission profile.
-/

namespace BigOSpeedrun.MatrixMultiplication

open OAI.MatrixMultiplication.Arithmetic

/-- Cost O(n^(r+ε)) for every positive ε, with a single positive constant
for all positive sizes. Smaller rational exponents are stronger.
The site accepts scores in [2, 3]; range validation belongs to the controller.
This target does not assert an attained O(n^r) running time. -/
def Bound (r : Rat) : Prop :=
  AdmissibleExponent ℂ (r : ℝ)

/-- The parameterized target expands to the site's circuit and slack contract. -/
theorem bound_iff (r : Rat) : Bound r ↔
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, 1 ≤ n → ∃ P : MatrixAlgorithm ℂ n n n,
        P.Correct ∧ (P.cost : ℝ) ≤ C * (n : ℝ) ^ ((r : ℝ) + ε) :=
  Iff.rfl

/-- Increasing an accepted exponent only weakens the claim. -/
theorem Bound.mono {r s : Rat} (hrs : r ≤ s) (h : Bound r) : Bound s := by
  have hrs' : (r : ℝ) ≤ (s : ℝ) := by exact_mod_cast hrs
  intro ε hε
  rcases h (ε + ((s : ℝ) - (r : ℝ)))
      (add_pos_of_pos_of_nonneg hε (sub_nonneg.mpr hrs')) with ⟨C, hC, h⟩
  refine ⟨C, hC, ?_⟩
  intro n hn
  rcases h n hn with ⟨P, hP, hcost⟩
  refine ⟨P, hP, ?_⟩
  have hexp : (r : ℝ) + (ε + ((s : ℝ) - (r : ℝ))) = (s : ℝ) + ε := by ring
  simpa only [hexp] using hcost

end BigOSpeedrun.MatrixMultiplication
