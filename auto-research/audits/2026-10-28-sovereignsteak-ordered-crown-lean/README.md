# Independent Lean rebuild: ordered 3×3 matrix removal

## Claim and result

Ryan Shea's pinned source claims that the ordered binary pattern
`011 / 101 / 110` has no polynomial removal bound. The site currently lists
the nine-cell row as **Claimed**, with proof scope "source inspection only; no
independent rerun." This package independently rebuilds the pinned Lean
development and checks the exact capstone theorem with Lean's kernel.

The local audit passed: all **93** project Lean modules compiled, the scope
probe passed, the capstone's transitive axioms were exactly
`Classical.choice`, `Quot.sound`, and `propext`, and `leanchecker -v
OrderedRemoval.Crown.Complete` passed. A fresh Git checkout at the source
commit matched all **225** tracked files in the archive used for the run.
Machine-readable receipts are in `evidence/run.json`,
`evidence/compilation.json`, and `evidence/source-match.json`; the site's
2026-10-28 Claimed row is in `data/site-record.json`.

The tested theorem is
`OrderedRemoval.Crown.no_polynomial_removal_bound` in
`formal/OrderedRemoval/Crown/Complete.lean`. For every positive real
`c`, `C`, and `ε₀`, it produces one `0 < ε < ε₀` such that every size threshold
`N` has a square binary matrix of order at least `max 1 N`; every
pattern-free binary repair differs in at least `ε n²` cells, while the
ordered copy count is strictly less than `c ε^C n⁶`.

The independent `code/Scope.lean` checks the literal nine pattern entries,
type-checks this quantifier order and the unrestricted repair condition against
the capstone theorem, and prints its transitive axioms. `verify.py` rejects
axioms beyond `propext`, `Quot.sound`, and `Classical.choice`; it then replays
the capstone module through `leanchecker` after compiling all project modules.
The source file hashes, dependency manifest, and exact Lean version are pinned
in `verify.py`, `data/source-files.json`, and the recorded result.

## Reproduce

From a fresh clone of `bigospeedrun/verifier`, with Git, Lean 4.34.1, Lake,
the Lean checker, and a C compiler on `PATH`:

```sh
python3 auto-research/audits/2026-10-28-sovereignsteak-ordered-crown-lean/verify.py
```

This command clones the exact source commit, checks source hashes, downloads
the pinned Mathlib build cache, compiles every project Lean module, checks the
scope probe, and replays the capstone module. It requires several gigabytes of
disk space and can take time on a fresh checkout. On FreeBSD without
`procfs`, Lean also needs a procfs mount or an equivalent application-path
shim. A local pinned checkout can be supplied with `--source PATH`.

Expected final output includes `Scope probe passed`, the allowed axiom set,
the capstone replay count, and a JSON report with `"build": "passed"`.

On the audited FreeBSD host, the first local invocation compiled all 93 modules
and then stopped on an ambiguity in this package's new probe (`fixedH` has an
inherited namesake). The source proof files were not changed. After qualifying
the crown names, the probe and capstone checker passed on the complete compiled
tree using `--source /tmp/ordered-matrix --reuse-build`. The latter option is
for resuming a complete local compile; the command above builds from scratch.

## Sources and scope

- Verifier base: `49533557838fde36981606aa2098374b09ea8649`.
- Claim source: `shea256/ordered-binary-matrix-removal` at
  `35f5784da66428f27e568ede22a9f1163403fa9a`.
- Source pins: Lean `v4.34.1`, Mathlib
  `d13f23b723b8a846827a245b89c10fc7d3f11612` and the other dependency
  revisions in the pinned `formal/lake-manifest.json`.
- The author already published a same-agent build and axiom audit. This
  contribution is an independent rerun and separate scope probe, not a new
  proof or a claim of novelty or priority.

This establishes that the pinned Lean code proves the stated proposition under
the three permitted Lean axioms, assuming the Lean kernel and the pinned
Mathlib imports. It does not independently prove that the formal `BinaryMatrix`,
ordered-copy, and Hamming-distance definitions capture every interpretation of
the site's informal problem, nor does it establish the written proof's exact
`7m⁴` count or smaller host size. The site row remains Claimed until its owner
updates the evidence level; this package does not trigger the direct proof
submission verifier.

The audit track was selected by OS seed 68. Candidate checks were the ordered
matrix capstone, the partial van der Waerden Lean development, and the Catalan
590 Lean claim. The ordered matrix capstone was chosen because its complete
qualitative theorem and source pins were available and no existing package or
open PR covered an independent rebuild. The existing Snaky Lean audit and
Catalan certificate-chain audit were read to avoid duplication.
