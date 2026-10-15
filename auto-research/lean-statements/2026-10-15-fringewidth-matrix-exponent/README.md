# Parameterized complex matrix multiplication exponent

**Status:** proposed statement. No new matrix multiplication bound is claimed.

**Hypothesis:** the existing OpenAI circuit model can express the site's
parameterized exponent guarantee directly, without changing its definitions
or assuming the fixed 9/4 theorem.

**Result:** `challenges/matrix-multiplication/Statement.lean` defines
`BigOSpeedrun.MatrixMultiplication.Bound (r : Rat)` using the existing
`AdmissibleExponent ℂ (r : ℝ)`. It includes definitional expansion and a proof
that increasing the exponent weakens the claim.

## Validation result

[GitHub Actions run 38687970915](https://github.com/fringewidth/verifier/actions/runs/38687970915)
passed at commit `f070391dbdb9399aee0cadad80562cd7d0cb33ea` with Lean 4.34.1.
The new statement and checks compiled with warnings as errors, and all five
audited declarations used only the permitted axioms. The 77 existing Python
tests also passed. See `evidence/validation.json` for hashes of the exact
tested code and `evidence/lean-checks.txt` for the relevant log excerpt.
The PR adds this validation metadata after the successful run; the tested
Lean sources, verification script, dependency pins and input data are unchanged.
This is research validation, not a production verifier receipt.

## Reproduce

From the repository root, with Python 3.12 or newer:

```sh
python3 auto-research/lean-statements/2026-10-15-fringewidth-matrix-exponent/verify.py
```

Expected output:

```text
PASS: package manifest, unchanged upstream model/license/dependency pins, challenge hashes
```

For the Lean checks, run the same command with `--lean` on an Ubuntu x86_64
GitHub Actions runner. This downloads checksum-pinned elan, Lean 4.34.1, the
repository's exact Mathlib dependencies and their build cache. It uses no
submission build hooks. The repository's AGENTS.md permits Lean execution
only on GitHub Actions; the script enforces that location.

The final lines after a successful Lean run are:

```text
PASS: Lean statement, rational substitution, wrong-bound type check, monotonicity, scalar circuit, allowed axioms
SCOPE: statement validation only; no production Comparator receipt or new matrix bound
```

The adapter and checks compile with warnings as errors. The unchanged source
model has three upstream theorem placeholders. The axiom audit covers the
adapter, its two theorems, and the actual scalar circuit checks, and rejects
all dependencies outside propext, Classical.choice and Quot.sound.

## Model comparison and vacuity review

| Site requirement | Target |
| --- | --- |
| Two n-by-n complex matrices | `MatrixAlgorithm ℂ n n n` |
| Correct for every input pair | `P.Correct` universally quantifies A and B |
| Finite division-free circuits | Existing `Program` and `Gate`; no division constructor |
| Inputs/constants free; +, −, × unit cost | Existing `Program.cost` |
| All positive sizes | `∀ n, 1 ≤ n → ...` |
| One C for all sizes | `∃ C` appears before `∀ n` |
| Every positive epsilon | `∀ ε, 0 < ε → ...` outside C and n |
| Exact exponent parameter | Rational-to-real cast, score range [2, 3] checked by controller |
| Smaller exponent is better | `Bound.mono` proves the direction |

The adapter avoids these weak statements: checking only n = 0, choosing C
after n, choosing a circuit after A/B, supplying just one positive epsilon,
and treating an arbitrary empty-set infimum as an algorithm witness.
Circuit generation is not required to be uniform: the site uses arithmetic
circuits, and C alone must be uniform across sizes.

The checks instantiate 9/4 independently, reject using a 9/4-typed hypothesis
verbatim at 2, prove monotonicity, and build a correct one-by-one multiplication
circuit with cost exactly one. The wrong-bound check is Lean type matching,
not a production Comparator check. The scalar check covers n = 1 only.
A full all-size cubic baseline and an impossible-exponent lower bound remain
formal review obligations. No finite check is presented as an asymptotic proof.

## Selection and current state

OS randomness selected seed **11**, assigning the lean-statements track.
Three candidates and their decisions are recorded in `data/inputs.json`.
Matrix multiplication was preferred because the missing parameterized
statement is an explicit track target and the model already exists.
There were no earlier packages in this track at base commit
`51489ee2ac82596a41375e92ea8108814f931242`. The only open PR was the DFT proof PR #10;
the recent issues and PRs did not duplicate this statement.

One request to chat-knowledge.json returned a cached, truncated response.
The selected row was checked against the pinned site data included in
`data/matrix-record.json`: OpenAI's 9/4 record has a passed Lean/nanoda
receipt, whereas the older track README calls its evidence Claimed.
The package uses **Lean Verified** for that record and does not downgrade it.
This observation is tied to the source snapshot, not a promise of a live record.

Initial source reads used the GitHub connector and were checked against blob
IDs. Validation and submission use a full clone at the exact upstream base
commit. Discord discussion could not be accessed.

## Scope and remaining work

This adds a reviewable target and its checks. It does not enable public matrix
submissions, prove a faster algorithm, convert the existing infimum theorem,
or produce a production verifier receipt. Maintainers need to review the
epsilon-slack relation, prove or select the infimum/admissibility bridge,
complete the baseline/lower-bound checks, and enable profiles, target
generation, record gates and Comparator mutation tests.

All files outside this package and the two new challenge files remain at the
base revision. The temporary validation workflow lives on a separate fork
branch and is excluded from the proposed upstream diff.

`MANIFEST.json` hashes every other package file; it excludes itself to avoid
self-reference. `data/challenge-hashes.json` additionally hashes the new
challenge files and the frozen model/license. No package code runs in the
production verifier.
