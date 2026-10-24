# Statement: Catalan's irrationality-exponent upper bound

Track seed: **12**, drawn once with Python's `secrets.randbelow(100)`.
Base commit: `1e009d7adeb43a1ddffe8b8148be4bebba69e720`.

Hypothesis: a Mathlib-only, parameterized target can represent the site's
irrationality-exponent upper bound without assuming the published proof or
requiring a stronger inequality at the exact submitted exponent.

Result: the proposed target in `challenges/catalan/Statement.lean` uses all
real exponents strictly greater than the submitted rational bound. It fixes
Catalan's literal series, quantifies uniformly over integer numerators, and
allows unreduced fractions. It excludes exact equalities, as in the usual
irrationality-exponent definition. The source's endpoint inequality implies
this target, but its proof is not part of this contribution.

## Reproduce

From the repository root, using Python 3 and its standard library:

```
python3 auto-research/lean-statements/2026-10-19-1337isnot1337-catalan-exponent/verify.py
```

This checks file hashes, plain-file requirements, source/dependency pins,
absence of proof holes in the target and validation, and the recorded Lean
check's correspondence to the delivered source files. It does not run Lean.
Expected output is documented in the verifier itself; success ends with
`PASS: package integrity and recorded Lean source correspondence`.
`MANIFEST.json` hashes every package file except itself; `data/TARGETS.json`
also hashes the three companion files under `challenges/catalan/`.

Lean is run on a contributor-owned GitHub Actions runner, in accordance with
AGENTS.md. `code/check-catalan.yml` is a reproducible workflow template. Install
it only in the reviewer's own fork at `.github/workflows/check-catalan.yml`.
The workflow or another GitHub Actions job runs:

```
bash auto-research/lean-statements/2026-10-19-1337isnot1337-catalan-exponent/code/verify-lean.sh
```

The script stages a clean Lake project outside the checkout, pins Lean and
Mathlib, obtains Mathlib's cache, builds `Statement`, compiles `Validation`,
and prints axiom dependencies. It imports no source proof template. The CI
workflow is kept outside `.github/` in this contribution; no production
workflow, profile, script or enabled target is changed.

## Tested claims

[Successful contributor-owned GitHub Actions check](https://github.com/1337isnot1337/verifier/actions/runs/39293900600),
tested commit `b8a7ab794fed5f624467249b59bc73f6ce561c55`.
`evidence/lean-check.json` hashes the four tested source/runner files, and
`evidence/axioms.txt` records the five printed axiom reports. Each report
contains only `propext`, `Classical.choice` and `Quot.sound`.

The Lean validation contains:

1. A definitional equality with the literal series and all quantifiers in
   Litsey's pinned 740 statement. The upstream file is retained byte for byte
   as `data/Challenge.lean`, never imported.
2. A conditional implication from an exact endpoint inequality to the target.
   Its hypothesis is explicit; it does not prove the endpoint.
3. Monotonicity: a larger upper-bound parameter gives a weaker proposition.
4. A positive control: zero, as a rational real number, has upper exponent at
   most one. This tests the exact-equality exclusion and establishes that the
   generic definition can be satisfied.
5. A wrong-bound rejection: no real number has the proposed upper bound zero.
   For each positive denominator `b`, `floor(b*x)+1` gives a nonzero error at
   most `1/b`, contradicting the required inequality at exponent one. In
   particular, `Bound 0` is false for the actual Catalan series.

The `+infinity` baseline cannot be submitted through a rational parameter.
No finite Catalan bound is proved here. These controls test the statement,
not the published determinant/PNT proof.

The rejected draft was to use `Endpoint constant r` itself as the race target.
It demands the separation inequality at `r`, which is stronger than the
page's upper-exponent claim. It remains only as the source bridge predicate.
Setup failures and unfinished proof-development checks are recorded separately
in `evidence/check-history.json`; neither is a mathematical counterexample.

## Selection and prior work

The candidate tasks were: parameterize Catalan's exponent, formalize the
uniform coefficient for van der Waerden numbers, or formalize the conditional
unit-distance grid count. Catalan was selected because its current source
already isolates a Mathlib-only literal statement, while the other two
require substantial upstream transfer hypotheses.

At the base commit the track had no previous packages. The open PRs were
#11 (matrix exponent), #12 (Subset Sum statement), #15 (average sensitivity),
#17 (Subset Sum lemma) and #20 (Heilbronn statement); none covered Catalan.
The live site response was updated `2026-10-19T15:17:24Z`, with current Catalan
bound 740, evidence Claimed. `evidence/site-row.json` records the row and the
hash of the complete response. It is a dated snapshot, not a live record gate.

Initial board requests without the `other-` slug prefix returned 404. Reading
the board index resolved the names. The feeds for `other-catalan`,
`other-van-der-waerden` and `other-unit-distance-grid` had no posts.
`evidence/board-before.md` records the selected board. No Discord discussion
was inspected: no authenticated Discord connector was available, and the
public invite did not expose channel history.

The source repository's then-current HEAD was
`732e9d44657ca9d3201f132e50afe7abade297dc`; its newest change concerned a
different constant. This package keeps the site's explicitly pinned Catalan
source commit `50672b810873d8371b2b6bdd0057bb6cb2e3da24`.

## Scope and open obligations

This is a statement proposal. It supplies no proof of 740, no irrationality
proof, no independent audit of the source's proof, and no improved record.
The definitions contain no assumed proofs and no custom axioms. The reference
template's nine proof holes remain only in the unimported provenance copy.

Mathematical review of the standard epsilon/irrationality-exponent equivalence
remains a maintainer obligation; its proof is explained in the challenge
README, rather than claimed as a formal theorem in this package. The `tsum`
is fixed rather than chosen by a submitting proof. A convergence proof is
not included; it is the same absolutely convergent series as the source.

Maintainers must enable a profile, exact target generation, allowed-axiom and
Comparator checks, and site bindings. Compiling this proposal does not change
the site's evidence level. See `NOTICE.md` for authorship and licensing.
