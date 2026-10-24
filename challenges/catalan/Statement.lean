module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Order.Filter.AtTopBot.Basic

@[expose] public section

/-!
# Catalan's constant: a parameterized upper bound on its irrationality exponent

New target adapter, Apache-2.0. Prepared for 1337isnot1337 with OpenAI Codex (GPT-6).
The literal series and approximation domain follow Sean Litsey's Challenge.lean,
commit 50672b810873d8371b2b6bdd0057bb6cb2e3da24. That statement template is
preserved, without importing its proof holes, in the accompanying research package.

The target quantifies over every exponent strictly above the submitted bound.
It does not demand an approximation inequality at the endpoint itself.
-/

namespace BigOSpeedrun.Catalan

noncomputable def constant : ℝ :=
  ∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2

/-- A strict, eventual approximation inequality, as in the pinned source. -/
def Endpoint (x s : ℝ) : Prop :=
  ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
    (b : ℝ) ^ (-s) < |x - (a : ℝ) / (b : ℝ)|

/-- The epsilon form of an upper bound on the irrationality exponent.

Exact rational equalities are excluded, as in the usual definition of the
irrationality exponent. All natural denominators and integer numerators are
allowed, without a coprimality requirement. For irrational x the exclusion is
automatic. The denominator threshold may depend on s, but is uniform in a.
-/
def UpperBoundFor (x r : ℝ) : Prop :=
  ∀ s : ℝ, r < s →
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      x ≠ (a : ℝ) / (b : ℝ) →
        (b : ℝ) ^ (-s) < |x - (a : ℝ) / (b : ℝ)|

/-- Proposed race target. Smaller nonnegative rational bounds are better.
There is no assumed proof of irrationality or of a finite exponent bound. -/
def Bound (r : ℚ) : Prop :=
  0 ≤ r ∧ UpperBoundFor constant (r : ℝ)

end BigOSpeedrun.Catalan
