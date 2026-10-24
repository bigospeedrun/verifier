# Sources and credit

New parameterized statement, validation and packaging: prepared for GitHub
account `1337isnot1337` with OpenAI Codex (GPT-6), using the Codex shell/tool
harness. No subagents were used. New files are licensed Apache-2.0 under this
repository's LICENSE. This contribution makes no claim to Litsey's proof or
to an improved irrationality exponent.

Sean Litsey's source:
https://github.com/slitsey/catalan-irrationality-measure/tree/50672b810873d8371b2b6bdd0057bb6cb2e3da24

- `Challenge.lean` is preserved byte-identically in `data/Challenge.lean`.
  It is an unimported statement template containing nine `sorry` bodies.
- `lake-manifest.json` is preserved byte-identically in
  `data/source-lake-manifest.json` solely as provenance for the Mathlib pin.
  The test project depends only on Mathlib and its own pinned dependencies;
  it does not reuse the source project's extra libraries.
- `NOTICE` is preserved byte-identically as `data/NOTICE.upstream`.
- The source's Apache-2.0 `LICENSE` is preserved byte-identically as
  `challenges/catalan/LICENSE`.
- File hashes are recorded in `data/SOURCES.json`.

The literal Catalan series and integer/natural rational-approximation domain
are taken from that source. Litsey's work builds on OpenAI's irrationality
formalization and uses Claude and Codex assistance, as detailed by the
upstream notices. No part of that proof is imported or verified here.

Mathlib pin:
https://github.com/leanprover-community/mathlib4/tree/065356127b1dc0016f66b7283ce0ce2c4055aa55

Verifier base and contribution contract:
https://github.com/bigospeedrun/verifier/tree/1e009d7adeb43a1ddffe8b8148be4bebba69e720

The site's dated record is in `evidence/site-row.json`; board text is in
`evidence/board-before.md`. These are short attribution-bearing research
snapshots, not instructions, proofs or assertions of independent verification.
