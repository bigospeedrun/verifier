module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Order.Filter.AtTopBot.Basic

public section

/-!
# An irrationality measure for Catalan's constant

Catalan's constant is `G = ∑_{j ≥ 0} (-1)^j / (2j + 1)^2`; it is written out below as a `tsum`
(the series converges absolutely, so the `tsum` is its sum).

The statements say that for every sufficiently large denominator `b` and every integer
numerator `a`,

* `|G - a / b| > b ^ (-740)` and `> b ^ (-2220)` (Lemma U6 content);
* `|G - a / b| > b ^ (-759)` and `> b ^ (-2276)` (Lemma U3 content);
* `|G - a / b| > b ^ (-878)` (so the irrationality exponent of `G` is at most `878`), and
* `|G - a / b| > b ^ (-2632)`, using Chebyshev's estimates for final prime selection; and
* the retained historical statements with exponents `955`, `2864` and `3662`.

The denominator asymptotics and secondary content estimate still use the prime number theorem.

Reference: S. Litsey, *An irrationality measure for Catalan's constant* (2026), building on
OpenAI, *Catalan's constant is irrational* (2026).
-/

namespace CatalanIrrationalityMeasure

/-- **Irrationality measure for Catalan's constant, exponent `740`.** -/
theorem catalan_irrationalityMeasure_740 :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(740 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| := by
  sorry

/-- The same bound with exponent `2220`, using Chebyshev for final prime selection. -/
theorem catalan_irrationalityMeasure_2220 :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(2220 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| := by
  sorry

/-- **Irrationality measure for Catalan's constant, exponent `759`.** -/
theorem catalan_irrationalityMeasure_759 :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(759 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| := by
  sorry

/-- The same bound with exponent `2276`, using Chebyshev for final prime selection. -/
theorem catalan_irrationalityMeasure_2276 :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(2276 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| := by
  sorry

/-- **Irrationality measure for Catalan's constant.** The central-gap interpolation
and supplied analytic trials give the eventual approximation bound with exponent `878`. -/
theorem catalan_irrationalityMeasure_878 :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(878 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| := by
  sorry

/-- The same bound with exponent `2632`, using Chebyshev for final prime selection.
The denominator and content estimates retain their PNT dependence. -/
theorem catalan_irrationalityMeasure_2632 :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(2632 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| := by
  sorry

/-- **Irrationality measure for Catalan's constant.** For all sufficiently large natural
numbers `b` and all integers `a`, `b ^ (-955) < |G - a / b|`, where
`G = ∑_{j ≥ 0} (-1)^j / (2j + 1)^2`.  Hence `μ(G) ≤ 955`. -/
theorem catalan_irrationalityMeasure_955 :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(955 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| := by
  sorry

/-- The same statement with exponent `2864`, using Chebyshev for final prime selection.
The denominator and content estimates retain their PNT dependence. -/
theorem catalan_irrationalityMeasure_2864 :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(2864 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| := by
  sorry

/-- The retained statement with exponent `3662`, which the argument gives when the prime number
theorem is replaced by Chebyshev's bounds in the final step. -/
theorem catalan_irrationalityMeasure_3662 :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(3662 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| := by
  sorry

end CatalanIrrationalityMeasure
