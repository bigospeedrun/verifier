import SubexponentialSATDefinitions

/-!
Released under Apache 2.0 as described in LICENSE.
Prepared with assistance from Claude (Anthropic).

Parameterized target for the Big O Speedrun 3-SAT board, https://bigospeedrun.com/3sat.

The imported OpenAI definitions are frozen byte for byte; see README.md and NOTICE. This file adds
four definitions and assumes no estimate, no hypothesis (in particular not the Exponential Time
Hypothesis) and no proof of any bound.
-/

namespace BigOSpeedrun.ThreeSat

open OAI.Algorithms.SubexponentialSAT

/-- Some assignment of the `n` variables makes every clause of `F` true. -/
def Satisfiable {n : ℕ} (F : SAT.CNF (Fin n)) : Prop :=
  ∃ a : SAT.Assignment (Fin n), SAT.CNF.eval a F = true

/-- `machine`, started with the encoding of `F` on its input tape and all other tapes blank, halts
after exactly `time` steps with the verdict `answer`. A halted machine makes no further step, so
`time` is its full running time. -/
def HaltsWith (machine : Computation.PrimitiveMachine) {n : ℕ} (F : SAT.CNF (Fin n))
    (time : ℕ) (answer : Bool) : Prop :=
  ∃ final : machine.Cfg,
    Computation.Trace machine.step time (machine.init (Encoding.encodeCNF F)) final ∧
      final.state = Sum.inl answer

/-- `K · (bits + 1)^d · 2^(n / (log₂(n + 2))^β)`. The factor `(bits + 1)^d` is the board's
`(n + m)^O(1)`; `log₂(n + 2) ≥ 1` for every `n`, so small `n` need no special case. -/
noncomputable def timeBound (K d : ℕ) (β : ℝ) (bits n : ℕ) : ℝ :=
  (K : ℝ) * ((bits : ℝ) + 1) ^ d * (2 : ℝ) ^ ((n : ℝ) / (Real.logb 2 ((n : ℝ) + 2)) ^ β)

/-- The board's claim for the exponent `α`: 3-SAT in time `(n + m)^O(1) · 2^(n / (log n)^(α − o(1)))`.

ONE machine and ONE degree `d` come first. Then for every rational `ε > 0` there is a constant
`K` such that, for every `n` and every CNF `F` on `n` variables with at most three literals per
clause, the machine started on the encoding of `F` halts with the correct verdict within
`K · (bits + 1)^d · 2^(n / (log₂(n + 2))^(α − ε))` steps, where `bits` is the length of the
encoding.

The controller substitutes an exact rational `α` with `0 ≤ α ≤ 100`. Larger values are better. -/
def SolvedInTime (α : ℚ) : Prop :=
  ∃ (machine : Computation.PrimitiveMachine) (d : ℕ),
    ∀ ε : ℚ, 0 < ε → ∃ K : ℕ,
      ∀ (n : ℕ) (F : SAT.CNF (Fin n)), SAT.WidthAtMost 3 F →
        ∃ (time : ℕ) (answer : Bool),
          (answer = true ↔ Satisfiable F) ∧ HaltsWith machine F time answer ∧
            (time : ℝ) ≤ timeBound K d ((α : ℝ) - (ε : ℝ)) (Encoding.formulaBitLength F) n

end BigOSpeedrun.ThreeSat
