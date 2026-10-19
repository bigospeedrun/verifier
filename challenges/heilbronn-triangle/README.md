# Heilbronn triangle: proposed trusted statement

This proposes the missing trusted target for the
[Heilbronn triangle board](https://bigospeedrun.com/other/heilbronn-triangle).
It follows [the statement contribution guide](../../docs/new-statements.md).
This is a statement-review contribution. It is not a proof submission, and it
does not claim that the public gate already accepts this problem.

## Model and saving

`Δ(n)` is the largest possible smallest triangle area among `n` distinct points
in the closed unit square. This is the definition in the board's baseline source,
OpenAI's preprint
([`01-introduction.tex`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-power-improvement-in-the-Heilbronn-triangle-lower-bound-September-25-2026/build/sections/01-introduction.tex)):
`P ⊂ [0,1]²`, minimum over unordered triples of distinct points, and maximum
over `|P| = n`. Its Theorem 1.1 has the same form as the board:
`Δ(n) ≥ c₁ n^(-2+η)` for every integer `n ≥ n₀`. The board records a saving
`η` in

    Δ(n) ≥ c · n^(-2+η)   for every sufficiently large n,

with an unspecified constant `c > 0` and threshold. A higher saving is better.

`BigOSpeedrun.HeilbronnTriangle.Bound η` says that there are a real `c > 0` and
a natural `N` such that, for every `n ≥ N`, some `Finset` of exactly `n` points
in `[0,1]²` has every triangle on three distinct points with area at least
`c · n^(-2+η)`. Area is the usual `|cross product| / 2`.

For `n ≥ 3` and `a > 0`, `Δ(n) ≥ a` is equivalent to the existence of such a
set. The preprint notes that the maximum exists: the smallest area is
continuous on a compact space, and a repeated point gives area zero. Even
without attainment, the constant would absorb a factor of 2. Stating the witness set directly avoids defining
`Δ` with `sSup`, whose Lean junk values on unbounded or empty sets could make a
target unintended. This equivalence is a standard argument and is not
formalized here.

This is a purely existential geometric statement. The board has no algorithm,
operation count or uniformity condition. The bound must hold for **every**
large `n`, not only along a subsequence.

The controller should substitute a reduced nonnegative rational for `η`. The
current Claimed board value `1/50893237` would give:

```lean
theorem Race.bound :
    BigOSpeedrun.HeilbronnTriangle.Bound (1 / 50893237 : ℚ) := by
  sorry -- placeholder; a submission supplies the proof
```

The parameter changes only the saving, never the model, the region or the
quantifiers. The meaningful range is `0 ≤ η ≤ 5/6`:

- `η = 0` is the classical bound. The package proves it in Lean.
- A larger saving implies every smaller one, also proved.
- Every `η > 5/6` is false by the known upper bound
  `Δ(n) ≪_ε n^(-7/6+ε)` (Cohen, Pohoata and Zakharov 2025, as cited in the
  preprint above). Every `η > 1` is already false by the elementary bound
  `Δ(n) = O(1/n)`. The Lean check only proves the trivial refutation for
  `η > 2`, where no triangle in the unit square has area above `1`.

No strict-frontier interpretation is needed.

## Difference from the upstream comparator target

OpenAI's comparator challenge `OAI.Problem355.heilbronn_power_lower_bound`
asserts point sets with smallest area at least `n_j^(-2+η₀)` only along some
sequence `n_j → ∞`, at the fixed exponent `η₀ = 1/(100000 K)`. The subsequence
is weaker than the board's "every sufficiently large `n`". Fixing the constant
at `1` is stronger than the board's unspecified `c > 0`. It also cannot take
the saving as a parameter. The community record repository
[littleBro/heilbronn-triangle-bounds](https://github.com/littleBro/heilbronn-triangle-bounds)
notes this too: "The original upstream Lean comparator uses a different
exponent and a subsequence statement." The adapter therefore reuses only
OpenAI's definitions, not its theorem statements.

## Toolchain and layout

- Lean: `leanprover/lean4:v4.34.1`.
- Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`. These are the pins in
  [`profiles/lake-manifest.json`](../../profiles/lake-manifest.json), which
  are also OpenAI's pins for the frozen file. The final choice of profile is
  the maintainer's.
- All imports are Mathlib or the frozen definitions in this folder. There are
  no external libraries, Lake hooks, downloads, custom axioms or compiled
  objects.

Stage this folder as a Lean source root. `Statement.lean` imports the enclosed
`OAI/Geometry/HeilbronnTriangle/Definitions.lean` under its original module
name.

Proof submissions put their modules below `Submission/` (`docs/targets.md`).
As with 3SUM and APSP, the maintainer can have a submission copy these two
files unchanged to `Submission/OAI/Geometry/HeilbronnTriangle/Definitions.lean`
and `Submission/Statement.lean`, with the import paths adjusted. Alternatively,
the profile can stage this folder next to the submission. A prover reusing
OpenAI's proof tree, which imports `OAI.Geometry.HeilbronnTriangle.Definitions`,
would need its imports rewritten under the chosen layout. This PR leaves that
choice to the maintainer. The declaration that Comparator must match is
`BigOSpeedrun.HeilbronnTriangle.Bound`, together with the frozen
`OAI.Problem355` definitions it uses: `Point`, `triangleArea`,
`pointInUnitSquare`, `pointsInUnitSquare` and `triangleAreasAtLeast`.

## Provenance and license

The definitions were authored by **OpenAI** in
[`openai/math`](https://github.com/openai/math) at fixed commit
`1581d4cbdd69a0faf34b2089614fe2a814316a6a`, original path
`lean/OAI/Geometry/HeilbronnTriangle/Definitions.lean`. They are frozen byte for
byte at the same relative path below this folder. `provenance.json` records the
original Git blob and SHA-256, and the Apache-2.0 license is preserved. The
frozen file has definitions only, with no theorem and no `sorry`.

The parameterized adapter `Statement.lean` is new and is released under
Apache-2.0. It was prepared with assistance from Claude (Anthropic). It does not
edit the upstream definitions, and it does not attribute the board's
parameterization to OpenAI. See `NOTICE`.

## Evidence and remaining admission work

Review evidence for this statement, including Lean proofs of `Bound 0`,
monotonicity and `¬ Bound η` for `η > 2`, is in
`auto-research/lean-statements/2026-10-19-joshuacortez-heilbronn-triangle/`.

As the contribution guide requires, maintainers must review this target against
the board. They then add the verifier-owned profile, rational target generator,
public form option and receipt/import bindings. Statement matching, wrong-bound
rejection and the allowed-axiom audit must be checked in that trusted pipeline.
This PR changes none of the controller, workflows, public submission options,
current records or evidence labels. Merging the statement alone would not make
any saving Lean Verified, and no current board record has a complete Lean proof.
