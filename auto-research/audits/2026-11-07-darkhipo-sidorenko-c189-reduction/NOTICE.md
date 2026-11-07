# Sources, credit and AI disclosure

Audit prepared for GitHub user `darkhipo` by an agent running OpenCode with
DeepSeek `deepseek-flash`. The audit was designed by that agent and every
number reported in `README.md` was produced by the bundled program
`code/reduction_check.py`, not by the model. New audit text and code are
contributed under this repository's Apache-2.0 license.

Independence: this audit is by an unrelated party to the claim's author. It
audits a Claimed result and supplies no proof; it is not a self-audit.

The Sidorenko counterexample construction is due to OpenAI. The residual
refinements 1641 → 1032 → 978 → 189, including the sequential basis count
audited here, are due to the author of
`rohanarun/sidorenko-template-refinements`. This audit claims no authorship
of those results.

Sources inspected:

- `rohanarun/sidorenko-template-refinements` @
  `5ca68cb81cfcd7f1b32102b93e186b2b51d5e2f8`:
  `README.md`, `proof.tex` (section "Sequential basis count for the nondirect
  residual", Lemma `lem:sequential-accounting`, Proposition
  `prop:residual-189`), `sequential-refinement.md`,
  `experiments/original-baseline.json` (the only substantive input, extracted
  into `data/baseline-faces-bits.json`), `experiments/sequential-expected.json`,
  and `audit_sequential.py` (read to pin definitions; run once, separately, as
  a cross-check; not an input and not redistributed). Per-file SHA-256 pins are
  in `data/source-pins.json`. No source code from that repository is
  redistributed here; the bundled data file holds only the numerical complex
  data (22 triangles, 22 cut vectors) needed to reproduce the audit offline.
- The upstream complex table is pinned by the source repository's
  `source-manifest.json` to `openai/math` @
  `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`,
  `preprints/A-counterexample-to-Sidorenkos-conjecture-September-23-2026/build/sections/complex.tex`.
  This is an inherited dependency; its correctness as the construction's
  complex was not independently verified here.
- `darkhipo/sidorenko-counterexample-lean` @ the clone read on 2026-11-07, for
  the model comparison only: `README.md`, `AXIOM_AUDIT.txt`, and
  `OAI/Combinatorics/Sidorenko/Tail.lean` (lines 282 and 307, the `1642 ≤ D₀`
  threshold and the `q^(-(D:ℝ)+1641)` residual exponent). That repository's
  Lean proof was not rebuilt or re-checked by this audit.
- `bigospeedrun/verifier` @ `080f93184881d98c38ef7a288283d2c9d40d3449`.
- The Big O Speedrun Sidorenko row (https://bigospeedrun.com/other/sidorenko),
  read 2026-11-07: bound 189, evidence Claimed, proof scope "No Lean proof is
  supplied", OpenAI baseline 1641. This is mutable site data; the row text
  quoted in `README.md` is the reading of that date.
- `bigospeedrun/verifier` audit `2026-10-23-ptweezy-sidorenko-c189`, the
  predecessor that audited the finite maximum and explicitly excluded the
  written reduction this package covers.

No claim is made about mathematical priority, authorship, or the row's
evidence level.
