# Sources, credits and disclosure

## Source of the formalized step

- DaysSky, "Two refinements of the October 2026 OpenAI math release"
  (research note, 9 October 2026; described in its repository as an
  AI-generated research draft prepared with Codex), in
  `DaysSky/van-der-waerden-refinement` at commit
  `54ac9715fceab938ca77d5980c36ab691765a04d`, file `research-note.tex`
  (sha256
  `700a23a04b9ac5845fd961366c02fcf781c57334bd1af28a99b41130d28172c2`),
  section "A sharper norm-band multiplicity": Lemma `lem:band`
  (lines 49–53) and its proof (lines 54–63); invoked at lines 79, 140,
  213 and 275. Pinned URL:
  https://github.com/DaysSky/van-der-waerden-refinement/blob/54ac9715fceab938ca77d5980c36ab691765a04d/research-note.tex
  The companion repository `rohanarun/van-der-waerden-refinement` at
  commit `63bef9ca996786a41169de4a0c3d6b3b47b0fe96` was also inspected
  for the overlap check (no Lean files).
- The note's ingredients are credited there to OpenAI's manuscript
  *Quantitative Superexponential Bounds for van der Waerden Numbers*
  (23 September 2026), in `openai/math` at commit
  `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`:
  https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Quantitative-Superexponential-Bounds-for-van-der-Waerden-Numbers-September-23-2026

## Target repository

- `bigospeedrun/verifier` at base commit
  `106c0f1b12f14c2dc735e7c35636e94a382fe858`, Apache-2.0 (see its
  LICENSE and NOTICE). Site data: `https://bigospeedrun.com/other/van-der-waerden`
  and `https://bigospeedrun.com/chat-knowledge.json`, read on
  2026-10-23; track listing read from
  `auto-research/formalization/README.md` at the base commit
  ("van-der-waerden" under "Other bounds rows with no Lean proof").

## Lean dependencies

- Lean `leanprover/lean4:v4.34.1`.
- Mathlib rev `d13f23b723b8a846827a245b89c10fc7d3f11612`, as pinned in
  `profiles/lake-manifest.json` of the base commit (the package's
  `code/lean-project/lake-manifest.json` is that manifest). Mathlib is
  Apache-2.0. No Mathlib code is copied into this package; the
  package's Lean file only imports it and uses, among others,
  `norm_add_sq_real`, `real_inner_smul_right`, `norm_smul`,
  `dist_eq_norm`, `Finset.card_erase_of_mem`, `Finset.one_lt_card`,
  and the `linarith` tactic.

## AI-assistance disclosure

This package was produced by an AI agent (Muse Spark, operating as
"Baka") at the request of its user, Parker, following
`auto-research.md` in the verifier repository (seed 56, formalization
track). The proof's arithmetic core was sanity-checked exactly with
Python's standard-library `fractions` module (see `verify.py`), and
the Lean proof was compiled locally with the output recorded under
`evidence/`. No result of this package has been submitted anywhere;
see the "Status" section of README.md.
