# Sources, credit and AI disclosure

Audit prepared for GitHub user `ptweezy` using Muse Spark via Muse.
The audit was designed and the package assembled by that agent; every
number reported was produced by the recorded programs (the author's
`build.py` and `reproduce.py`, and the auditor's probe `code/extract.lean`)
run on this machine, not by the model. No additional AI models were used.
New audit text and code are contributed under this repository's
Apache-2.0 license.

The Snaky 19-move result, its Lean formalization, the card certificate
and the audit tooling are due to the author of `shjvandekamp/math`. Per
the source's own provenance note, `Snaky/Game.lean`, `Cards.lean`,
`Controls.lean`, `Bounded.lean`, `CardsSound.lean`, `CardCheck.lean`,
`lean-toolchain` and `tools/cards2lean.py` are copied in that repository
from `gotrevor/snaky-15x15` at `b18ed32473a6a22ebfdda98da62d61b8b1590c1e`
under the Apache-2.0 license; `Plane.lean`, `Result19.lean`, `Audit.lean`
and `build.py` are the Snaky project's new work. This audit claims no
authorship of any of those results.

Sources inspected:

- shjvandekamp/math, commit
  `db6e1d89a0637b013a86464bd766c0a5120e454e`, in particular
  `topics/snaky/formal/README.md`, `topics/snaky/formal/build.py`,
  `topics/snaky/formal/kernel-audit.json` (the recorded audit; a byte
  copy is bundled as `data/kernel-audit-recorded.json` for offline
  comparison), `topics/snaky/formal/Snaky/Audit.lean`,
  `topics/snaky/certificate/snaky19.cards.txt`, and
  `topics/snaky/reproduce.py`. Per-file SHA-256 pins are in
  `data/source-pins.json`. No source code from that repository is
  redistributed in this package; the only bundled source-derived file is
  the recorded audit JSON named above.
- The Lean 4.34.1 toolchain (elan, `leanprover/lean4:v4.34.1`), reporting
  commit `5045d0056413266e57c625dcd7c365b10e377c52`, identical to the
  author's recorded official-release builds.
- bigospeedrun/verifier, base commit
  `817a8bb03d599860804c0843e8bd9b356efcbe83`.
- The Big O Speedrun Snaky row (https://bigospeedrun.com/other/snaky),
  read 2026-10-23: bound 19, evidence Claimed, proof scope noting the
  audit was author-run with no independent rerun. This is mutable
  snapshot evidence; the retrieval date is recorded in
  `data/source-pins.json`.

The audited source tree was never modified: the clone was checked out at
the pinned commit, the build wrote only to git-ignored paths, and
`git status` was clean after the run.
