import OAI.Combinatorics.GotsmanLinial.Model

/-!
Copyright (c) 2026 Anchen0823. All rights reserved.
Released under Apache 2.0 as described in LICENSE.
Prepared with assistance from OpenAI Codex.

Parameterized target for the Big O Speedrun average-sensitivity board.
The imported OpenAI model is frozen byte for byte; see README.md and NOTICE.
No estimate or proof of a bound is assumed here.
-/

namespace BigOSpeedrun.AverageSensitivity

open OAI.LeanBlast.GotsmanLinial

/-- A universal, attained coefficient on the uniform sign cube. The controller
must supply an exact nonnegative rational `C`; smaller values are better.
The polynomial is arbitrary, not assumed multilinear. -/
def Bound (C : ℚ) : Prop :=
  ∀ (n d : ℕ), 1 ≤ n → 1 ≤ d → d ≤ n →
    ∀ p : MvPolynomial (Fin n) ℝ, p.totalDegree ≤ d →
      averageSensitivity (polynomialThreshold p) ≤
        (C : ℝ) * (d : ℝ) * Real.sqrt (n : ℝ)

end BigOSpeedrun.AverageSensitivity
