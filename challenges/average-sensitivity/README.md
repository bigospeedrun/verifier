# Average sensitivity: proposed trusted statement

This proposes the missing trusted target for the
[average-sensitivity board](https://bigospeedrun.com/other/average-sensitivity).
It follows [the statement contribution guide](../../docs/new-statements.md).
This is a statement-review contribution, not a direct proof submission and not
a claim that the public automatic gate already accepts this problem.

## Model and coefficient

`BigOSpeedrun.AverageSensitivity.Bound C` means that for every pair of integers
`1 ≤ d ≤ n` and every real polynomial in `n` variables of total degree at most
`d`, the average sensitivity of its threshold function is at most `C d √n`.
No multilinearity hypothesis is imposed. This covers the board's polynomial
threshold functions without needing a separate representation assumption.

Vertices are `Fin n → Bool`, interpreted as the signs `−1,+1`. Each coordinate
flip changes exactly one Boolean coordinate. Sensitivity is the sum over all
coordinates of the number of vertices whose threshold value changes, divided
by `2^n`. Thus each summand is a probability under the uniform distribution on
the entire sign cube. The threshold is `1` for a nonnegative polynomial value
and `−1` otherwise; in particular `sign(0)=1`. Positive dimension and degree,
the degree bound, and `d ≤ n` are explicit hypotheses.

This is an exact finite-cube inequality, not an algorithm-runtime statement.
Arithmetic-operation counts, preprocessing, and asymptotic slack are not part
of this board's model. The bound must hold in every displayed dimension and
degree, not only eventually or at a fixed degree.

The controller should substitute a reduced nonnegative rational for `C`.
Smaller is better. The parameter changes only the coefficient, never the model,
the input domain, or the sign convention. No strict-frontier interpretation is
needed. For example, the eventual submission target at `1881/500` would be:

```lean
theorem Race.bound :
    BigOSpeedrun.AverageSensitivity.Bound (1881 / 500 : ℚ) := by
  -- Supply a proof; none is included in this trusted statement.
```

`Bound` and the frozen model contain definitions only. In particular,
`GotsmanLinialStatement` inside the upstream model is a proposition definition
for its original coefficient eight; no theorem proving it is imported or used
as a premise. The target has no assumed grading, energy bound, certificate,
coupling estimate, or assumed proof of the submitted bound.

## Toolchain and layout

- Lean: `leanprover/lean4:v4.33.1`.
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`.
- The exact package pins are the already reviewed
  [`profiles/anthropic-lake-manifest.json`](../../profiles/anthropic-lake-manifest.json)
  (subject to the maintainer's profile selection).
- All imports are Mathlib or the frozen model in this folder. There are no
  external libraries, Lake hooks, downloads, custom axioms, or compiled objects.

Stage this folder as a Lean source root: `Statement.lean` imports the enclosed
`OAI/Combinatorics/GotsmanLinial/Model.lean` under its original module name.
The verifier-owned profile can choose its trusted statement-module name. The
declaration names that Comparator must match remain fixed as shown above.

## Provenance and license

The model was authored by **OpenAI**, from
[`openai/math`](https://github.com/openai/math), fixed commit
`1581d4cbdd69a0faf34b2089614fe2a814316a6a`, original path
`lean/OAI/Combinatorics/GotsmanLinial/Model.lean`. It is frozen byte for byte in
the corresponding relative path below this folder. `provenance.json` records
its original Git blob and SHA-256; the Apache-2.0 license is preserved.

The separate parameterized adapter `Statement.lean` was authored by Anchen0823
with OpenAI Codex assistance, under Apache-2.0. It does not edit the upstream
definitions or attribute the new coefficient to OpenAI. See `NOTICE`.

## Evidence and remaining admission work

A complete proof of the stronger statement for all `n,d ≥ 1` (including
`d > n`) is public in
[`Anchen0823/average-sensitivity-lean`](https://github.com/Anchen0823/average-sensitivity-lean).
Its repository-root `Submission.lean` is a standalone candidate `Race.bound`
proof at `1881/500`, importing only Mathlib. It includes the same proposed
target and the full proof sources; the repository's GitHub Actions compiles
it and checks its final axiom list.

The [Prove2Me main theorem](https://prove2.me/theorems/e1a9c1cb-97c1-4ea0-a4ad-d43e8412ac61)
is Proved with accepted submission `0f539328-c783-4509-a78e-a86ac777468c`.
The proof integrates OpenAI's grading construction, the coupling refinement
of Lagdive, Aglave and Damre, and this development's coefficient extraction.
These checks and source references do not replace Big O's own admission gate.

As required by the contribution guide, maintainers must review this target
against the board, then add the verifier-owned profile, rational target
generator, public form option, and receipt/import bindings. Statement matching,
wrong-bound rejection, and the allowed-axiom audit must be checked in that
trusted pipeline. This PR changes none of the controller, workflows, public
submission options, current records, or evidence labels. Merging the statement
alone would not make any coefficient Lean Verified.
