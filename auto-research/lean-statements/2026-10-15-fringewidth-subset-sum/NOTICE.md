# Credits and license

- Model of computation and Theorem 1.1: OpenAI, «Subset Sum in Time
  O(2^0.49n)», 4 October 2026, preprint
  https://github.com/openai/math/blob/main/preprints/Subset-Sum-in-Time-2-power-0-49n-October-4-2026/subset-sum.pdf
  (sha256 of the PDF read: d5558cd419c8d46bdc958064cb97f963d1ea793866414c025906ec15033512ed).
  The statement's comments quote short phrases of Section 1.1.
- Shape of the instruction set, execution function and `BigO` encoding:
  Anthropic, `EndStatement.lean` of anthropics/formal-math commit
  e1a4e6508154ea59f030480661590a9fe3018011, Apache-2.0, present unchanged in
  `challenges/3sum-apsp/`. No text of that file is copied; the new file is a
  rewrite for a different machine and problem.
- Problem page wording and record snapshot: Big O Speedrun contributors,
  https://bigospeedrun.com/subset-sum and chat-knowledge.json, site
  repository commit 000c32d3249b7d7bbde0278ba62cb51a576bfd60.
- Current Claimed result consulted for the model clauses: Annanay Kapila,
  a-kapila/maths-proofs commit 44c34961b56784c220a6e913cc068d57dc37c5a3.
  Nothing of that proof is used or claimed.
- Verifier contribution contract: Big O Speedrun contributors, Apache-2.0,
  https://github.com/bigospeedrun/verifier/tree/51489ee2ac82596a41375e92ea8108814f931242
- New statement, checks and research package: fringewidth, Apache-2.0.
  AI assistance: Claude Fable 5.1 in Claude Code, which drafted the statement,
  the proofs and this package under the contributor's account. No other agent
  or model was used.

This package claims no authorship of OpenAI's algorithm or model, and no
Subset Sum bound.
