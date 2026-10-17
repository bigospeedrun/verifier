# Proposed parameterized matrix exponent

`Statement.lean` exports `BigOSpeedrun.MatrixMultiplication.Bound (r : Rat)`.
The exact target for a reduced rational p/q is:

```lean
import Statement
theorem Race.bound : BigOSpeedrun.MatrixMultiplication.Bound ((p : Rat) / q) := by
  -- Supply a proof; no implementation is assumed by the target.
```

This is a proposed statement for [the matrix multiplication board](https://bigospeedrun.com/matrix-multiplication).
Public submissions for it are not enabled. Stage the unchanged upstream file
as module `MatrixMultiplication`, followed by `Statement`.

## Model and parameter

The target is OpenAI's `Arithmetic.AdmissibleExponent ℂ (r : ℝ)`.
The rational is cast exactly into the reals. Accept scores in [2, 3], with a
positive denominator, in the controller. Smaller exponents are stronger; the
adapter proves this direction as `Bound.mono`. A range restriction is not
embedded in the mathematical proposition.

For every real ε > 0 there is one real C > 0 such that, for every natural
n ≥ 1, there is a finite correct circuit costing at most C n^(r+ε).
C may depend on r and ε, but cannot depend on n or the input matrices.
A circuit may depend on n and ε, but must multiply **all** pairs of n-by-n
complex matrices. This is a circuit family, without an additional uniform
circuit-generation requirement.

The upstream gates, registers, evaluation and correctness definitions are
unchanged. Inputs and arbitrary complex constants cost zero; scalar
addition, subtraction and multiplication cost one. There is no division gate.
The bound is an arithmetic operation count, with positive exponent slack;
it does not assert bit complexity or an attained O(n^r) bound.

## Relationship to the fixed target

The existing target states `omega ℂ ≤ 9/4`, where omega is an infimum.
The adapter directly requires the quantified circuit witnesses. It neither
assumes the existing theorem placeholder nor uses an infimum inequality as a
proof of those witnesses. Converting an existing proof to this target requires
a proved bridge or a direct admissibility theorem. That bridge is an open
obligation, not a claim that OpenAI's result is false.

The unchanged upstream file contains three `sorry` placeholders, as trusted
challenge files commonly do. They must never be used as proof dependencies.
The adapter and its checks have no placeholders; validation audits their
transitive axioms and rejects `sorryAx`.

## Pins and review

Use Lean `leanprover/lean4:v4.34.1`, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, and the other exact revisions in
`profiles/lake-manifest.json`. No fixed-point package or proof dependency is
needed for this statement.

The source model is byte-identical to
[OpenAI's file](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/ComparatorChallenges/MatrixMultiplication.lean),
Git blob `877d7ee3901c51382cf5bcb059a50d8dbb3cde77`. Its author and license
are OpenAI and Apache-2.0; the existing LICENSE applies. The adapter was
prepared by fringewidth with OpenAI Codex (GPT-6), under Apache-2.0.

See [the research package](../../auto-research/lean-statements/2026-10-15-fringewidth-matrix-exponent/README.md)
for model comparison, vacuity review, source hashes and reproduction.
Maintainers must review the epsilon-slack contract, add an exponent-relation
profile distinct from attained bounds, generate exact targets, and test
Comparator, bounds, axes of statement mutation, and axiom rejection before
enabling this target. A successful package check is not Lean Verified evidence
for a matrix multiplication record.
