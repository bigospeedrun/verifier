# Fixed targets

The entry point is `Submission.lean`, with theorem `Race.bound`. For a PR,
this file lives in its new submissions folder; for an issue, at the source
repository root. The verifier stages the chosen folder as the project root.
Extra modules must be below `Submission/`; import them with `Submission.Name`.
Copy needed proof sources there and update their import paths. The verifier
supplies pinned Mathlib, Lean, and build files. It does not use submitted Lake
files, fetch submitted dependencies, or run submitted setup scripts.

For 3SUM and APSP, use Lean `leanprover/lean4:v4.33.1` and the Mathlib pin in
`profiles/anthropic-lake-manifest.json`. Copy our unchanged `EndStatement.lean`
into `Submission/EndStatement.lean` in the proof repository. Import it from
`Submission.lean`. Its namespace remains `EndStatement`.

For a bound `p/q`, prove one of these targets:

```lean
import Submission.EndStatement

theorem Race.bound : EndStatement.ThreeSum.SolvedInTime ((p : Rat) / q) := by
  -- Supply the proof.
```

For APSP, replace `ThreeSum` with `APSP`. Replace `p` and `q` with the exact
numerator and positive denominator. The controller builds its target from our
unchanged statement file; it does not trust the submitted statement copy.

For DFT, use Lean `leanprover/lean4:v4.34.1` and the Mathlib pin in
`profiles/lake-manifest.json`. Keep OpenAI's `OAI.PowerSaving.DFTProgram`
definitions unchanged. For saving `p/q`, export:

```lean
open OAI.PowerSaving Filter Asymptotics

theorem Race.bound : ∃ order solve W, DFTProgram order solve W ∧
    (fun n : ℕ => (W n : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) * (Real.log (n : ℝ)) ^
        (1 - (p : ℝ) / q)) := by
  -- Supply the proof.
```

The DFT target covers all positive lengths and complex vectors in the exact
scalar/index RAM. Root-order selection, preparation, and polynomial bounds
are included. This is an operation-count model.

The historical `dft233` entry point is retained only for local receipt tests
and the existing manual verifier. The public issue form always uses
`Race.bound`. It accepts no entry-point, dependency, or toolchain override.

For average sensitivity (issue route only), use Lean `leanprover/lean4:v4.33.1` and
the Mathlib pin in `profiles/anthropic-lake-manifest.json`. The trusted statement is
`challenges/average-sensitivity/VerifierStatement.lean`: OpenAI's unchanged
`Model.lean` followed by `Statement.lean`. Keep those definitions unchanged in your
sources (namespaces `OAI.LeanBlast.GotsmanLinial` and `BigOSpeedrun.AverageSensitivity`),
and for a coefficient `p/q` export:

```lean
theorem Race.bound : BigOSpeedrun.AverageSensitivity.Bound ((p : ℚ) / q) := by
  -- Supply the proof.
```

`Bound C` states AS(sign p) ≤ C d √n for every real polynomial p of total degree at
most d in n variables, 1 ≤ d ≤ n, with sign(0) = 1. A smaller C is better.

## Catalan's constant

Issue route only. Use Lean `leanprover/lean4:v4.34.1` and the Mathlib pin in
`profiles/lake-manifest.json` (the DFT pin). The trusted statement is
`challenges/catalan/Statement.lean`, namespace `BigOSpeedrun.Catalan`. For an
exponent bound `p/q`, export:

```lean
theorem Race.bound : BigOSpeedrun.Catalan.Bound ((p : ℚ) / q) := by
  -- Supply the proof.
```

For an integer bound, write `q = 1`, for example `((1091 : ℚ) / 1)`. `Bound r` says
that `r ≥ 0` and that for every real `s > r`, for all large `b` and every integer `a`,
`b^(-s) < |G - a/b|`. A smaller `r` is better. See
[the statement README](../challenges/catalan/README.md) for the quantifiers.

A Catalan proof is large, so it runs as a
[split build](execution.md#split-build-for-large-proofs). Only the final result is
posted. Nanoda can end incomplete (time or memory limit); that does not prevent Lean Verified.

[Convert a proof repository to the Submission layout](convert-layout.md) explains how
to move an existing proof (for example, Sean Litsey's Catalan repository) into the
layout that the verifier reads.

## Integer factoring

Closed to issues and PRs. A maintainer can rerun Isaac Rudich and Louis-Martin
Rousseau's proof of score 0 (time `N^o(1)`) against their unchanged statement in
`challenges/integer-factoring/Challenge.lean`, with Lean `leanprover/lean4:v4.35.0`.
See [the statement README](../challenges/integer-factoring/README.md).

A maintainer can also rerun 1337isnot1337's claimed proof of score 1/2 (time
`2^O(n/√log n)`, their `Factoring.SqrtLogLogConjecture`) against the same statement with
one appended theorem, in `challenges/integer-factoring-sqrtlog/Challenge.lean`, with Lean
`leanprover/lean4:v4.33.1`. See [its README](../challenges/integer-factoring-sqrtlog/README.md).
There is no `Race.bound` target for other scores yet.

Integer multiplication and Subset Sum have no trusted statement in this gate.
SSSP is outside the site submission scope.
