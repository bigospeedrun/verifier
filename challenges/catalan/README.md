# Proposed Catalan irrationality-exponent statement

Problem: https://bigospeedrun.com/other/catalan

This is a proposed trusted statement, not a proof of a finite bound. Maintainers
must review and enable it before it can accept race submissions.

`Statement.lean` defines the fixed real number

```
G = sum_{j >= 0} (-1)^j / (2*j+1)^2
```

as the literal Mathlib `tsum` used by the pinned source. The race target for a
nonnegative rational `r` is:

```lean
theorem Race.bound : BigOSpeedrun.Catalan.Bound r := by
  -- proof supplied by a future contributor
```

The verifier must supply this module and substitute the submitted rational for
`r`. The contributor cannot select the constant, approximation domain or model.
Smaller bounds are better; the accepted parameter range is `0 <= r`, with no
finite upper cap. The site's `+infinity` baseline is outside this rational
submission interface.

## Quantifiers and endpoint

`Bound r` says that for every real `s > r`, there is a natural denominator
threshold `B(s)` such that, for every `b >= B(s)` and every integer `a`,

```
G != a/b  implies  b^(-s) < |G-a/b|.
```

The threshold is independent of the numerator. It may depend on `s`. Fractions
need not be reduced. Denominators zero and one do not affect an eventual
statement on natural denominators. The exclusion of exact approximations
matches the usual definition of the irrationality exponent; it is automatic
when the real number is irrational. The target assumes no irrationality theorem.
It neither asserts nor verifies irrationality on its own.

For irrational `G` this is the usual epsilon formulation of `mu(G) <= r`.
One can use an intermediate exponent between `r` and `s` to pass between strict
and weak inequalities and between reduced and unreduced fractions. Finitely
many exceptional reduced fractions can be excluded by increasing `B(s)`.
Thus a lower exponent bound is a stronger requirement, without requiring the
endpoint inequality at `s = r`.

In particular, demanding `b^(-740) < |G-a/b|` at the exact endpoint would be a
stronger submission contract. The pinned source claims that stronger fact;
`source_740_implies_bound` in the research package proves only the conditional
bridge from it to the proposed target. It does not prove the source theorem.

## Dependencies and provenance

- Lean: `leanprover/lean4:v4.35.0-rc2`.
- Mathlib: `065356127b1dc0016f66b7283ce0ce2c4055aa55`, together with that
  commit's pinned dependencies. No other libraries are imported.
- Series and source approximation statement: Sean Litsey,
  https://github.com/slitsey/catalan-irrationality-measure/blob/50672b810873d8371b2b6bdd0057bb6cb2e3da24/Challenge.lean
- New parameterized definitions and validation: prepared for GitHub account
  `1337isnot1337` using OpenAI Codex (GPT-6), under Apache-2.0.

The original `Challenge.lean` is a template with `sorry` theorem bodies.
A byte-identical reference copy, source hashes, upstream notices, tests and
reproduction instructions are in
[`auto-research/lean-statements/2026-10-19-1337isnot1337-catalan-exponent/`](../../auto-research/lean-statements/2026-10-19-1337isnot1337-catalan-exponent/).
It is not imported by the proposed target or its validation. The fixed series
is restated as a definition; no unproved source theorem enters the target.

## Validation and remaining work

The package checks the literal 740 source shape, its conditional implication,
monotonicity in the correct direction, the known upper exponent one of the
rational number zero, and failure of exponent zero for every real number.
These checks include a nonempty positive control and a false-bound rejection.
They do not prove any finite bound for Catalan's constant.

Maintainers still need to review equivalence with the site's mathematical
definition, select an enabled profile and dependency pins, implement target
generation and record/receipt bindings, and run Comparator and the allowed
axiom audit on an eventual proof. A successful compilation here does not make
the source result Lean Verified. Permitted proof axioms remain `propext`,
`Quot.sound` and `Classical.choice`.
