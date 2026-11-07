# Sources, credits, and AI assistance

The Subset Sum algorithm and its research claims belong to their original
authors. This package contributes an independently implemented, limited audit.

- Yanni Bills: conditional exponent 0.4876723 and the filter-3 boundary argument,
  [commit bf1f50f066f2c71a53293791f693f505a67a1540](https://github.com/yannouli/subset-sum-conditional-refinement/tree/bf1f50f066f2c71a53293791f693f505a67a1540).
  Inspected `paper.tex` (especially the moved-boundary lemma),
  `candidate-data.tex`, `certificate-appendix.tex`, `numerics/data/candidate.json`,
  `numerics/README.md`, and `references.bib` through web text views.
- Joshua Wharton: predecessor transfer/refinement,
  [commit dcb002174cb1e06213e171c9f5ff6b063fdf2c40](https://github.com/JoshuaQFEX/subset-sum-bound/blob/dcb002174cb1e06213e171c9f5ff6b063fdf2c40/paper.tex).
- Annanay Kapila: underlying construction and finite certificate data,
  [commit 44c34961b56784c220a6e913cc068d57dc37c5a3](https://github.com/a-kapila/maths-proofs/blob/44c34961b56784c220a6e913cc068d57dc37c5a3/subset-sum/PROOF_0.4877.tex).
  This baseline was not downloaded or independently hashed in this audit.
- OpenAI: original framework,
  [commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Subset-Sum-in-Time-2-power-0-49n-October-4-2026).

Only finite mathematical facts and formulas are transcribed. No full upstream
manuscript, source implementation, or third-party license grant is reproduced
or asserted. The original implementation and documentation in this package
are offered under Apache-2.0, consistent with the intended verifier repository.
This does not relicense any upstream work.

Prepared using OpenAI Codex, identified in this session as GPT-6. The harness
used public web read tools, Python 3.15.2, and local PowerShell/file tools.
No additional agent, human mathematical review, Lean run, or external proof
service was used. The configured GitHub account was not successfully
authenticated; authorship is not attributed to that account in this draft.
