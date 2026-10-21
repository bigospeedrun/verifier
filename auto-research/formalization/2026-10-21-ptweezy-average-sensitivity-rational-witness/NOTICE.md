# Sources, credits and disclosure

## Source of the formalized step

- Qiuyu Chen (Euler), "A uniform average sensitivity bound", 17 October 2026,
  in `canghaimeng/openai-math-improvement` at commit
  `b3c7abea0d5e392777498816ca837eded8b85669`, file
  `problems/bound-127/paper.pdf`, Section 7 (and Theorem 1, equation (4)).
  Pinned URL:
  https://github.com/canghaimeng/openai-math-improvement/blob/b3c7abea0d5e392777498816ca837eded8b85669/problems/bound-127/paper.pdf
  The step formalized here is that paper's rational-witness corollary.
  Its ingredients are credited there to: OpenAI (coefficient 8 and the operator
  reduction; preprint pinned at `openai/math` commit
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`) and Prathmesh Lagdive, Vaibhav
  Aglave and Suraj Damre (compensated coupling and the intermediate
  coefficient 383/100; https://doi.org/10.21203/rs.3.rs-11323154/v1 and
  https://doi.org/10.5281/zenodo.23269472).

## Target repository

- `bigospeedrun/verifier` at base commit
  `80d20586d0f09473146fe8dc3f6d78340208cc35`, Apache-2.0 (see its LICENSE and
  NOTICE). Site data: `https://bigospeedrun.com/chat-knowledge.json`,
  retrieved 2026-10-21, `updatedAt` 2026-10-21T02:20:52Z.

## Lean dependencies

- Lean `leanprover/lean4:v4.34.1`.
- Mathlib rev `d13f23b723b8a846827a245b89c10fc7d3f11612`, as pinned in
  `profiles/lake-manifest.json` of the base commit (all other packages in
  `code/lean-project/lake-manifest.json` are that manifest's pins).
  Mathlib is Apache-2.0. No Mathlib code is copied into this package; the
  package's Lean file only imports it and uses `Real.pi_gt_d6`,
  `Real.lt_sqrt`, `div_lt_iff0`, `norm_num`, `nlinarith` and `positivity`.

## AI-assistance disclosure

This package was produced by an AI agent (Muse Spark, operating as "Baka")
at the request of its user, Parker, following
`auto-research.md` in the verifier repository (seed 52, formalization track).
All rational identities were checked exactly with Python's standard-library
`fractions` module, and the Lean proof was compiled locally with the output
recorded under `evidence/`.

Re-verification and upload were done with Claude Code at the same user's
request. It re-checked the manifest digests and `verify.sh`, rebuilt the Lean
proof (the current `evidence/lean-build.log`), renamed the folder from `baka`
to the user's GitHub handle `ptweezy`, updated the README status, and
prepared the PR. It did not change the proof or the research content; see the
"Status" section of README.md.
