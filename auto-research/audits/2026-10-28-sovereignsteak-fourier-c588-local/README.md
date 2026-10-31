# Independent local Lean replay: exact Fourier C588

## Claim and scope

The pinned formalization proves an exact discrete Fourier transform and an
exact convolution program for every positive length in its supplied-root,
unrestricted-coefficient complex RAM model. Its work bound is
`O(n (log n)^(1 - 12331685/10^10))`, including root selection and scalar
preparation. The Lean capstones are `OAI.PowerSaving.transform_mainC588` and
`OAI.PowerSaving.convolution_mainC588`. This is an arithmetic-operation
bound, not a numerical FFT benchmark.

The [site's Fourier page](https://bigospeedrun.com/exact-dft) already labels
this saving Lean Verified and ranks larger savings above it. This package is
an independent local reproduction of that existing entry; it does not change
the site's bound or evidence level.

## Independent check

The source is `shea256/fourier-transform-below-nlogn` at
`0e61af6ce0ef712494c93c902baefa314ef7e23c`. All 1,004 Git-tracked
files match the aggregate path-and-content digest in `data/source.json`.
The source pins Lean 4.34.1 and its Lake dependencies; its provenance script
checks 425 hashes and upstream import-prefix identities.

On the user's FreeBSD 15.1 machine, the source's `build_and_check.sh` rebuilds
the proof, checks three theorem axiom lists, compares the positive result to
the adapted challenge, and rejects a deliberately stronger exponent as a
negative control. The separate `code/Scope.lean` checks the exact decimal
exponent, both theorem types, and their axiom closures; `leanchecker` replays
the capstone module through Lean's kernel. The completed local run passed all
checks; `evidence/local-run.json` records its result.

## Reproduce

With Git, Bash, Python 3.12, Lean 4.34.1, Lake, `leanchecker`, and sufficient
network, disk, and compute capacity:

```sh
python3.12 auto-research/audits/2026-10-28-sovereignsteak-fourier-c588-local/verify.py
```

The verifier fetches the exact source commit, checks every tracked file,
runs the source's full script, checks its positive and negative comparison
logs, checks the independent scope probe, and replays the capstone module.
`verify.py --help` documents an existing-checkout mode.

This audit trusts Lean's kernel, the three standard axioms if found, the
pinned imported libraries, and the formal model. It does not establish
historical priority or software runtime performance.
