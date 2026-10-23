# Sources, credit and AI disclosure

Audit prepared for GitHub user `ptweezy` using Muse Spark via Muse.
The audit was designed and the package assembled by that agent; every number
reported was produced by the bundled program (`code/sidorenko_audit.py`),
not by the model. No additional AI models were used. New audit text and
code are contributed under this repository's Apache-2.0 license.

The Sidorenko counterexample construction is due to OpenAI. The residual
refinements 1641 → 1032 → 978 → 189, including the sequential basis count
audited here, are due to the author of
`rohanarun/sidorenko-template-refinements`. This audit claims no authorship
of those results.

Sources inspected:

- rohanarun/sidorenko-template-refinements, commit
  `5ca68cb81cfcd7f1b32102b93e186b2b51d5e2f8`, in particular
  `sequential-refinement.md`, `proof.tex` (Lemma
  `lem:sequential-accounting`, Proposition `prop:residual-189`),
  `experiments/original-baseline.json` (the saved faces and cut bits; the
  only substantive input to this audit, extracted into
  `data/baseline-faces-bits.json`), `experiments/sequential-expected.json`,
  and `audit_sequential.py` (read to pin the claim's definitions; run once,
  separately, as a cross-check — it is not an input to the independent
  recomputation and is not redistributed here). Per-file SHA-256 pins are
  in `data/source-pins.json`. No source code from that repository is
  redistributed in this package; the bundled data file contains only the
  extracted numerical complex data (22 triangles, 22 cut vectors, and the
  pair-separation record) needed to reproduce the audit offline.
- The upstream complex table is pinned by the source repository's
  `source-manifest.json` to openai/math,
  commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`,
  `preprints/A-counterexample-to-Sidorenkos-conjecture-September-23-2026/build/sections/complex.tex`.
  This is an inherited dependency; its correctness as the construction's
  complex was not independently verified here.
- bigospeedrun/verifier, base commit
  `106c0f1b12f14c2dc735e7c35636e94a382fe858`.
- The Big O Speedrun Sidorenko row (https://bigospeedrun.com/other/sidorenko),
  retrieved 2026-10-23: bound 189, evidence Claimed. This is mutable
  snapshot evidence; the retrieval date is recorded in
  `data/source-pins.json`.

The independent implementation was written from the written definitions in
`sequential-refinement.md` and `proof.tex`. Agreement with the author's
saved output was checked only after the independent recomputation was
complete.
