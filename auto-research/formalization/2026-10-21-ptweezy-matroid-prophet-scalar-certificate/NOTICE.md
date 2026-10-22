# Sources, credits and disclosure

## Source of the formalized step

- Qiuyu Chen (Euler), "An Exact Rational Certificate for One-Sample
  Matroid Prophet Inequalities", 17 October 2026, in
  `canghaimeng/openai-math-improvement` at commit
  `b3c7abea0d5e392777498816ca837eded8b85669`, file
  `problems/bound-111/paper.pdf`, §1 equations (3)–(5) and Appendix A
  (p. 12). Pinned URL:
  https://github.com/canghaimeng/openai-math-improvement/blob/b3c7abea0d5e392777498816ca837eded8b85669/problems/bound-111/paper.pdf
  (paper PDF sha256
  `6a2c25ec54145b47fa8d00ad93db3581d57c2f467c581b54c64b474d23b6c06e`,
  as recorded by the audits-track package below). The step formalized
  here is that paper's exact scalar certificate: the parameter values,
  the tilt inequalities, the conditions (4), the monotonicity in
  `x ↦ C(x)`, and the final comparison (5) at `x = 141` versus
  `B = θ²⁵⁶`.
  Its ingredients are credited there to: OpenAI (the construction) and
  Ryan Shea (the quantitative refinements and the predecessor
  certificate `C_star = C(140)`; `shea256/matroid-prophet-inequality`
  at commit `8cd1395994596d89ad20c2af8b69dab8e3402ee1`,
  https://github.com/shea256/matroid-prophet-inequality/blob/8cd1395994596d89ad20c2af8b69dab8e3402ee1/README.md).

## Prior check of the same arithmetic (different track)

- `auto-research/audits/2026-10-19-1337isnot1337-matroid-scalar-141/`
  (PR #22): a Python audit replaying the paper supplement's embedded
  checkers (`checkers/check_scalar.py`,
  `checkers/check_comparison.py`) plus 25 independent exact checks.
  Complementary to this package; see the README's scope section.

## Target repository

- `bigospeedrun/verifier` at base commit
  `5a0203a9ccc3911b71ef90582afde0ec064689c0`, Apache-2.0 (see its LICENSE
  and NOTICE). Site data: `https://bigospeedrun.com/chat-knowledge.json`,
  local snapshot of 2026-10-21T02:20:52Z; track listing read from
  `auto-research/formalization/README.md` on the base commit
  ("matroid-prophet: formalization pending").

## Lean dependencies

- Lean `leanprover/lean4:v4.34.1`.
- Mathlib rev `d13f23b723b8a846827a245b89c10fc7d3f11612`, as pinned in
  `profiles/lake-manifest.json` of the base commit (all other packages
  in `code/lean-project/lake-manifest.json` are that manifest's pins).
  Mathlib is Apache-2.0. No Mathlib code is copied into this package;
  the package's Lean file only imports it and uses, among others,
  `Real.rpow_inv_natCast_pow`, `Real.rpow_mul`, `Real.rpow_neg`,
  `Real.exp_one_lt_d9`, `Real.exp_bound'`, `Real.log_lt_iff_lt_exp`,
  and the `norm_num` / `ring` / `gcongr` / `field_simp` tactics.

## AI-assistance disclosure

This package was produced by an AI agent (Muse Spark, operating as
"Baka") at the request of its user, Parker, following
`auto-research.md` in the verifier repository (seed 46, formalization
track). All rational identities were checked exactly with Python's
standard-library `fractions` module, and the Lean proof was compiled
locally with the output recorded under `evidence/`. No result of this
package has been submitted anywhere; see the "Status" section of
README.md.
