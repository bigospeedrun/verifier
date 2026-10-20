# Credits and license

This package builds on amachino/haldane-gap-refinement, pinned at
[15909bdc15e947795b6fba946008dd8530bb3477](https://github.com/amachino/haldane-gap-refinement/tree/15909bdc15e947795b6fba946008dd8530bb3477).
The source credits GPT-6 Astra Max for its refinements and certificate code.
Its original `NOTICE`, `AUTHORSHIP.md`, and Apache License 2.0 are retained
under `upstream/`. The individual vendored files are unmodified and pinned
by SHA-256 in `SOURCE-PINS.json`.

The underlying spatial-transfer construction, periodic reseeding, gap
criterion, and original finite inputs are credited to OpenAI's math
collection at
[adc7f1241b42e322a6451854ab7e4b4c146bf78a](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a).
The source identifies the periodic spin-one Haldane-gap paper and its
boundary-field companion as the analytic predecessors. This package does
not establish those inputs independently.

`code/verify_quarter_tightened.py` is a modified copy of the pinned
`verify_quarter_refinement.py`. The changes were made on 20 October 2026:
the target becomes 1517/10000, the tail invariant retains a spatial
prefactor 1/100, its constants become C=B=201/100, and output metadata
records those changes. `code/quarter-tightening.patch` gives the complete
diff. The finite and scalar certificate methods remain credited to their
predecessors.

The new invariant argument, independent replay wrapper, and documentation
were produced with OpenAI Codex GPT-6 in the Codex harness. No subagents or
other models were used in this session. The user selected Big O Speedrun
and requested focus on the oldest updates. The same model subsequently
formalized the added scalar inequalities in Lean and wrote the axiom-audit
script. The backend snapshot identifier
was not exposed. This assistance disclosure does not imply endorsement
by OpenAI or by any predecessor author.

New package material is offered under Apache License 2.0, with the license
text in `upstream/LICENSE`. Original notices remain applicable. The bound
is conditional, unreviewed, and not Lean Verified.
