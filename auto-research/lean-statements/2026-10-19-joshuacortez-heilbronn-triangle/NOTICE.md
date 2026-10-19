# Notice

## Sources

- OpenAI, `openai/math` at commit `1581d4cbdd69a0faf34b2089614fe2a814316a6a`:
  `lean/OAI/Geometry/HeilbronnTriangle/Definitions.lean` (frozen byte for byte in
  `challenges/heilbronn-triangle/`) and
  `lean/ComparatorChallenges/HeilbronnTriangle.lean` (read for comparison only).
  Apache-2.0.
- Ivan Blinov, `littleBro/heilbronn-triangle-bounds` at commit
  `45738785a8877fddf268a36ac7f3703d510be55e` (main branch): README quoted for
  its note that the upstream comparator is a subsequence statement. This is an
  older commit than the one behind the board's current record. No code copied.
- OpenAI's preprint "A power improvement in the Heilbronn triangle lower bound"
  (`openai/math` commit `1581d4c`, `build/sections/01-introduction.tex`): the
  definition of `Δ(n)`, Theorem 1.1's quantifiers, and the cited upper bounds.
- The Big O Speedrun board page and `chat-knowledge.json`, read on 2026-10-19.
- Mathematics used in the vacuity check: the Erdős parabola construction
  (`x ↦ (x, x² mod p)`, published in Roth 1951) and Bertrand's postulate
  (`Nat.exists_prime_lt_and_le_two_mul` in Mathlib).

## License

`Statement.lean`, `VacuityCheck.lean`, `Axioms.lean`, `verify.sh` and these notes
are released under Apache-2.0, matching the frozen upstream file.

## AI assistance

Prepared by Claude Opus 5.5 (Anthropic), working as an agent for
@joshuacortez, who reviewed and submitted it. Claude wrote the statement, the
proofs and these notes.
