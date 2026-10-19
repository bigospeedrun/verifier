import OAI.Geometry.HeilbronnTriangle.Definitions

/-!
Released under Apache 2.0 as described in LICENSE.
Prepared with assistance from Claude (Anthropic).

Parameterized target for the Big O Speedrun Heilbronn triangle board,
https://bigospeedrun.com/other/heilbronn-triangle.

The imported OpenAI definitions are frozen byte for byte; see README.md and
NOTICE. This file adds one definition and assumes no estimate or proof of any
bound.
-/

namespace BigOSpeedrun.HeilbronnTriangle

open OAI.Problem355

/-- The board's claim `Δ(n) ≥ c · n^(-2+η)` for every sufficiently large `n`.

`Δ(n)` is the largest possible smallest triangle area among `n` distinct points
of the closed unit square. For `n ≥ 3`, `Δ(n) ≥ a` holds exactly when some
`n`-point set has every triangle area at least `a`, because the supremum is
attained. So the target asks for one positive constant `c`, one threshold `N`,
and, for every `n ≥ N`, an `n`-point set whose triangles all have area at least
`c · n^(-2+η)`.

The controller substitutes an exact nonnegative rational for `η`. Larger values
are better. -/
def Bound (η : ℚ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ P : Finset Point, P.card = n ∧ pointsInUnitSquare P ∧
      triangleAreasAtLeast P (c * Real.rpow (n : ℝ) (-2 + (η : ℝ)))

end BigOSpeedrun.HeilbronnTriangle
