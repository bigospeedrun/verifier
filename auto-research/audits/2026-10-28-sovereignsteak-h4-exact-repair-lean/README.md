# Independent Lean rebuild: exact 4×4 host repair distance

## Claim and result

The pinned Erebos Labs follow-up claims an exact unrestricted repair distance
for a concrete ordered 4×4 binary pattern. Its host at depth `h ≥ 1` has
`m = 2^h` and order `n = (14h+2)m`. A terminal-anchor repair changes exactly
`m²` physical cells and is pattern-free; every pattern-free binary matrix of
the same order differs from the original host in at least `m²` cells. Hence
the normalized minimum distance is `1/(14h+2)²`.

The local Lean audit passed: all **40** primary project modules compiled from
source, the separate literal-pattern and quantified-scope probe passed, the
author's semantic checker compiled, and Lean's kernel replayed the capstone
and semantic-checker modules. The capstone's transitive axiom set was exactly
`Classical.choice`, `Quot.sound`, and `propext`. The audit checked all **153**
tracked source files against the pinned Git checkout. The machine-readable
run is `evidence/run.json`; all 40 compiled module digests are in
`evidence/compilation.json`.

The release's finite terminal-anchor scanner also passed at depths 1–4,
checking repair freeness and physical edit counts 4, 16, 64, and 256. Its
output is `evidence/finite.json`. This finite check corroborates the general
proof but does not establish the all-depth theorem by itself.

The audited theorem is
`OrderedMatrixRemoval4.Host.TerminalAnchorRepair.exact_minimum` in
`OrderedMatrixRemoval4/TerminalAnchorCount.lean`. `code/Scope.lean` checks all
sixteen bits of the target pattern and type-checks the theorem's unrestricted
quantifier over alternative binary matrices. The upstream
`checkers/ExpectedTerminalStatement.lean` separately interprets edits as all
unequal physical cells, proves an attaining repair, and derives the normalized
distance. The audit compiles and kernel-checks that module as well.

## Reproduce

From a fresh clone of `bigospeedrun/verifier`, with Git, Python 3.12+, Lean
4.34.1, Lake, and `leanchecker` on `PATH`:

```sh
python3.12 auto-research/audits/2026-10-28-sovereignsteak-h4-exact-repair-lean/verify.py
```

The script checks its manifest, clones the exact source commit, verifies all
tracked source hashes and the upstream release manifest, restores the pinned
Mathlib and eight dependency source trees, obtains the pinned Mathlib build
cache, re-elaborates every primary project module, checks the separate scope
probe and axiom set, and replays the two relevant modules with `leanchecker`.
It needs network access and several gigabytes of disk space. A prepared local
checkout can be supplied with `--source PATH`. On FreeBSD without `procfs`,
Lean needs a procfs mount or an equivalent application-path shim.

The recorded FreeBSD run used `--source /tmp/ordered-4x4 --reuse-build` after
the complete source rebuild, with pinned dependency source trees and Mathlib
cache objects reused from the preceding Lean audit. The toolchain was the
FreeBSD Lean 4.34.1 package. It had normal scheduling priority (`nice 0`),
above the host's `worker` processes (`nice 19`) and `xmrig` (`nice 10`).

## Sources and limits

- Verifier base: `49533557838fde36981606aa2098374b09ea8649`.
- Claim source: `erebos-labs/ordered-matrix-removal-4x4` at
  `0d43f182f2ee12e27419ac4d5e32fd2d9b68ab43`.
- Toolchain: Lean 4.34.1; Mathlib
  `d13f23b723b8a846827a245b89c10fc7d3f11612` and the eight dependency
  revisions in the source's `DEPENDENCIES.json`.
- The site's 2026-10-28 ordered-matrix row is stored in
  `data/site-record.json`. Its current leader is a distinct 3×3 pattern;
  this 4×4 result is a related, weaker-size claim.

This checks the pinned formal exact-distance theorem and its literal pattern
under Lean's standard axioms, assuming the Lean kernel and pinned imports.
It does not prove that the source's informal host description captures every
possible interpretation of the problem or establish novelty or priority.
The published release already contains author-supplied Lean and audit
checkers; this package is a separate-machine rerun with its own scope probe,
not a new proof. It does not change the site's evidence level or pass the
direct proof-submission verifier.
