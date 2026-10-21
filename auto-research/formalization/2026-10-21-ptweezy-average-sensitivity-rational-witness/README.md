# Formalization: average-sensitivity rational witness (Section 7)

Track: formalization. Seed: 52 (OS randomness, 40-64 band).
Base commit of `bigospeedrun/verifier`: `80d20586d0f09473146fe8dc3f6d78340208cc35`.
Problem: `/other/average-sensitivity`. Evidence before: Claimed. Bound concerned: `399/125`.

## The named step

The Claimed result `AS(f) <= (399/125) d sqrt(n)` (Qiuyu Chen / Euler, 2026-10-17,
source pinned below) is the corollary of a stronger written bound
`AS(f) <= (8/sqrt(2 pi)) d sqrt(n)`. Its Section 7 ("The rational witness and
strict comparisons") turns that into the displayed constant by proving the
chain

```
8/sqrt(2 pi)  <  399/125  <  383/100  <  8,
```

using the lower bound `pi > 4 * sum_{x in {1/2, 1/3}} (x - x^3/3 + x^5/5 - x^7/7)
= 1538665/489888 > 500000/159201 = 32 / (399/125)^2`, with the second strict
gap exactly `206455/1237946976`.

This package formalizes exactly that step, and nothing else.

## Result

Lean 4.34.1, Mathlib rev `d13f23b723b8a846827a245b89c10fc7d3f11612`
(the rev pinned in `profiles/lake-manifest.json` of the base commit):

- `cert_main : 8 / Real.sqrt (2 * Real.pi) < 399 / 125` — in `code/Cert.lean`.
- `cert_chain : (399/125 : R) < 383/100 /\ (383/100 : R) < 8`.

`lake build` succeeded (see `evidence/lean-build.log`). `#print axioms` for
both theorems reports exactly `[propext, Classical.choice, Quot.sound]`.
There is no `sorry`, `admit`, or declared axiom in the file.
`code/Narrow.lean` is the same proof with narrow imports; it also compiled
(`evidence/narrow-build.log`).

One honest substitution: the Lean proof takes its pi lower bound from
Mathlib (`Real.pi_gt_d6 : 3.141592 < pi`, at this rev in
`Mathlib/Analysis/Real/Pi/Bounds.lean`), which is stronger than the paper's
`1538665/489888` bound, instead of formalizing the paper's arctan Taylor
argument. The reduction that a pi bound of `500000/159201` already suffices,
and every rational identity the paper uses in Section 7 (the Taylor sum, the
gap `206455/1237946976`, `383/100 - 399/125 = 319/500`,
`8 - 399/125 = 601/125`), is checked exactly with Python `fractions`
by `verify.py`.

## Reproduce

Rational certificate and package checks (Python 3 standard library only):

```
bash auto-research/formalization/2026-10-21-ptweezy-average-sensitivity-rational-witness/verify.sh
```

Expected: every check prints `ok` and the script ends with `PASS`.

Lean proof (from a fresh clone, with elan / Lean `leanprover/lean4:v4.34.1`):

```
mkdir LeanTest && cd LeanTest
cp <this-package>/code/lean-project/lakefile.toml <this-package>/code/lean-project/lean-toolchain <this-package>/code/lean-project/lake-manifest.json .
cp <this-package>/code/Cert.lean .
lake exe cache get
lake build
```

Expected: `Build completed successfully`, and the two `#print axioms` infos
quoted above. With the Mathlib cache, the `import Mathlib` build of this one
file took about 12 minutes on the 2-core machine where the package was
prepared, and the narrow-import version (`cp code/Narrow.lean .` in place of
`Cert.lean`, with a matching lib target) took about 2 minutes via
`lake env lean`. Without the cache, compiling Mathlib from source took about
3.5 hours on 4 cores, after which `Cert` itself built in under a minute
(`evidence/lean-build.log`).

## Scope and limits

- This formalizes one step only: the Section 7 rational-witness comparisons.
  `AS(f)` itself, the compensated coupling, the weighted filtration and edge
  comparison, the parity/binomial coupling, and the Wallis argument all remain
  written proofs. Nothing here makes the result Lean Verified.
- The paper's arctan lower-bound argument for pi is not formalized; Mathlib's
  certified pi bound is used instead (see above).
- A finite check is not used as a proof of any theorem here: the rational
  identities are exact, and the real-number inequality is a Lean kernel proof.

## How this task was chosen

Open verifier PRs/issues were surveyed on 2026-10-20. Three candidates:
(1) this average-sensitivity Section 7 step — chosen, no Lean supplied and no
open formalization of it; (2) the matroid prophet `B > 141` scalar certificate —
rejected, verifier PR #22 already audits that certificate; (3) the van der
Waerden run lemmas — rejected, written-only and large, and a source-repo PR
already adds partial Lean for selected steps. Unit-distance (PR #27) and
Subset Sum small-layer (PR #17) formalizations were already taken.

## Status

Submitted to `bigospeedrun/verifier` as one research PR (formalization track)
by GitHub user `ptweezy`. The package was prepared on 2026-10-21 against base
commit `80d20586d0f09473146fe8dc3f6d78340208cc35` (recorded in `RESULT.json`)
and rebased onto the then-current `main` for submission without changing
any file content; the PR description names that commit. The Lean and Mathlib
pins above were unchanged there.

Before submission the package was re-verified from these files: every
`MANIFEST.json` digest matched, `verify.sh` printed `PASS`, the Lean build
was repeated from scratch with the same axiom lists, and the verifier's own
unit tests passed. The current `evidence/lean-build.log` is the output of
that run.

The folder handle `ptweezy` is the contributor's GitHub handle. The package
itself was produced under the agent name "Baka" (see `NOTICE.md`).
