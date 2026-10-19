# Heilbronn triangle: trusted statement with the saving as a parameter

Track: lean-statements · Status: statement · Board:
[/other/heilbronn-triangle](https://bigospeedrun.com/other/heilbronn-triangle)
· Base commit: `1e009d7adeb43a1ddffe8b8148be4bebba69e720`

## Hypothesis

The Heilbronn board can be represented by one parameterized proposition that
matches the board's convention, `Δ(n) ≥ c · n^(-2+η)` for every sufficiently
large `n`, reusing OpenAI's frozen definitions unchanged.

## Result

The proposed statement is in [`challenges/heilbronn-triangle/`](../../../challenges/heilbronn-triangle/README.md):

```lean
def Bound (η : ℚ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ P : Finset Point, P.card = n ∧ pointsInUnitSquare P ∧
      triangleAreasAtLeast P (c * Real.rpow (n : ℝ) (-2 + (η : ℝ)))
```

`Point`, `pointsInUnitSquare` and `triangleAreasAtLeast` come from OpenAI's
`OAI.Problem355` definitions, frozen byte for byte.

[`VacuityCheck.lean`](VacuityCheck.lean) proves, with no `sorry` and only the
standard axioms:

| Theorem | Meaning |
|---|---|
| `bound_zero : Bound 0` | The classical bound `Δ(n) ≥ n⁻²/8` for every `n ≥ 1`, from Erdős's points `(x/p, (x² mod p)/p)` with a Bertrand prime `n < p ≤ 2n` |
| `bound_mono : Bound η → η' ≤ η → Bound η'` | A larger saving implies every smaller one |
| `not_bound_of_two_lt : 2 < η → ¬ Bound η` | An impossible saving is rejected, because every triangle in the unit square has area at most `1` |
| `nonvacuous : Bound 0 ∧ ¬ Bound 3` | The target is neither trivially true nor trivially false |

## Model comparison with the board

| Board item | Board | This statement |
|---|---|---|
| Quantity | `Δ(n)`: the largest smallest triangle area of `n` points in the unit square | An explicit witness set: `Finset Point`, `card = n`, in `[0,1]²`, every triangle on three distinct points with area `≥` the bound |
| Form | `Δ(n) ≥ c n^(-2+η)` | `c * n^(-2+η)` with `Real.rpow` |
| Constant | unspecified `c > 0` | `∃ c : ℝ, 0 < c` |
| Range of `n` | every sufficiently large `n` | `∃ N, ∀ n ≥ N` |
| Parameter | saving `η`, exact rational, higher is better | `η : ℚ`, monotone (proved) |
| Strictness | `≥` | `≥`; strictness is immaterial up to `c` |
| Cost model | none (not an algorithm board) | none |

The witness form is equivalent to `Δ(n) ≥ a` for `n ≥ 3`. The configuration
space is compact and the smallest area is continuous, so the supremum is
attained by a configuration with positive smallest area, whose points are
distinct. This equivalence is not formalized.

## Places where the statement could be vacuous or weaker than the page

1. **Subsequence instead of every large `n`.** The upstream comparator target
   asks only for a sequence `n_j → ∞`. That is weaker: sparse good `n` do not
   give every large `n`, since `Δ` is only monotone. This statement uses
   `∀ n ≥ N`. *Addressed.*
2. **Constant fixed to 1.** Upstream fixes `c = 1`. The board allows any
   `c > 0`, so fixing `c = 1` would be stronger than the page. *Addressed:* `∃ c > 0`.
3. **Defining `Δ` by `sSup`.** `sSup` on an empty or unbounded set returns a
   junk value in Lean. That could make `Δ(n) ≥ …` true or false for the wrong
   reason. *Avoided* by the witness form.
4. **Coincident points.** A `Finset` has distinct elements, and
   `triangleAreasAtLeast` ranges over distinct triples. Collinear triples have
   area 0, so they are excluded whenever `c > 0`.
5. **Small `n` and `n = 0`.** The prover chooses `N`, and `rpow` at `0` is never
   needed. For `n < 3` the area condition is empty, which is harmless.
6. **Trivial truth or falsity.** Ruled out by `nonvacuous`.
7. **Region and quantifier.** The board page does not restate them. Its
   baseline source, OpenAI's preprint (`01-introduction.tex` at commit
   `1581d4c`), defines `Δ(n)` on `[0,1]²` over distinct triples and proves
   `Δ(n) ≥ c₁ n^(-2+η)` for every `n ≥ n₀`. The current record's conditions say
   "every sufficiently large n" and "thresholds and constants are not given".
   This statement follows both.
8. **Range.** Every `η > 5/6` is false by known upper bounds (Cohen, Pohoata
   and Zakharov 2025, `Δ(n) ≪ n^(-7/6+ε)`), and every `η > 1` is false by the
   elementary `O(1/n)` bound. Only `η > 2` is refuted in Lean here. All record
   values are tiny, far inside this range.

## Rejected drafts

- **Reuse `heilbronn_power_lower_bound` with the exponent replaced.** Rejected:
  it is a subsequence statement with `c = 1` (items 1 and 2), and the upstream
  file is a comparator challenge with `sorry` theorems.
- **`Δ n := sSup {a | ∃ P, …}` and `Δ n ≥ c * n^(-2+η)`.** Rejected for item 3,
  and because it adds a definition that Comparator must match for no gain.
- **The negation of `eventualAlmostUpperBound ε`** (OpenAI's corollary).
  Rejected: that definition is the "almost `n^-2`" upper-bound conjecture.
  Its negation only gives a large `Δ(n)` for infinitely many `n`, not for all
  large `n`, and its quantity is not the board's.

## Reproduce

From the root of a clone of `bigospeedrun/verifier` with this PR applied:

```bash
bash auto-research/lean-statements/2026-10-19-joshuacortez-heilbronn-triangle/verify.sh
```

It checks every hash in `MANIFEST.json` and `provenance.json`, re-fetches the
upstream file and compares bytes, then builds `Statement` and `VacuityCheck`
against the pinned `profiles/lake-manifest.json` (Lean 4.34.1, Mathlib
`d13f23b`). Expected tail of the output:

```text
manifest and provenance hashes: OK
byte-identical to openai/math@1581d4cbdd69a0faf34b2089614fe2a814316a6a: OK
...
'BigOSpeedrun.HeilbronnTriangle.bound_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'BigOSpeedrun.HeilbronnTriangle.bound_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'BigOSpeedrun.HeilbronnTriangle.not_bound_of_two_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'BigOSpeedrun.HeilbronnTriangle.nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Scope

This is a proposed statement only. It proves no board record: every record row
remains Claimed, and no full Lean proof of any positive saving exists. Merging it
would not change any evidence label.

## Open obligations

- Maintainer review of the model, and the verifier-owned profile, target
  generator, form option and receipt/import bindings.
- Comparator, wrong-bound rejection and the axiom audit in the trusted pipeline.
- The witness/supremum equivalence above is argued, not formalized.

## How this was checked locally

On 2026-10-19, Lean 4.34.1 (`5045d0056413`) with Mathlib `d13f23b`, from
the pinned `profiles/lake-manifest.json`, built `Statement.lean` and
`VacuityCheck.lean` with no errors, no warnings and no `sorry`. The Mathlib
download cache was unreachable from that machine, so Mathlib was compiled from
source, and to save time only the modules the files need were compiled. For
that run, the frozen file's single line `import Mathlib` was replaced by
narrower Mathlib imports (`Analysis.SpecialFunctions.Pow.Real`,
`Analysis.SpecialFunctions.Pow.Asymptotics`, `NumberTheory.Bertrand`,
`Data.ZMod.Basic` and `FieldTheory.Finite.Basic`). No other byte changed.
`verify.sh` builds the exact committed files, with `import Mathlib`. `#print axioms`
gave `[propext, Classical.choice, Quot.sound]` for all four theorems.
