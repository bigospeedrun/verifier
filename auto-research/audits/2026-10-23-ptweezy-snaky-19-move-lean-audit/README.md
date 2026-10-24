# Audit: independent rebuild of the Snaky 19-move Lean kernel audit

The Snaky row leader's only evidence was an **author-run** Lean audit; the
site row says so, ending "no independent rerun". This package is the
independent rerun. On a fresh machine (Linux x86_64, this audit's own
checkout and toolchain), the author's dedicated kernel-audit target was
rebuilt from the site-pinned source commit, and the output reproduces the
author's recorded audit **exactly**:

- All **1,182 modules** of the `Snaky.Audit` dependency closure compiled
  with the pinned Lean 4.34.1 (serial, one thread, 4,096 MB per-process
  cap, 180 s per module — the author's own build discipline). Slowest
  module: `Snaky.Gen19.Data06` at 133.2 s, inside the cap.
- The headline theorem is among the audited theorems, with the recorded
  type, verbatim:

  ```text
  Snaky.snaky_wins_plane_in_19 : Snaky.PlaneBlackWinsIn 19 [] []
  ```

  together with its finite-board companion

  ```text
  Snaky.snaky_wins_17x17_in_19 : Snaky.BlackWinsIn (Snaky.placements 17 17 Snaky.snaky) (17 * 17) 19 [] []
  ```

- Both theorems depend on exactly `[propext, Classical.choice, Quot.sound]`
  — the standard axioms, no `sorryAx`, nothing else — confirmed three
  ways: the author's recorded `kernel-audit.json`, the `Snaky.Audit`
  module's own output during this rebuild, and an auditor-written probe
  (`code/extract.lean`) run against the freshly compiled oleans.
- The certificate's SHA-256
  (`baf8774e1fc6eea60b1756437e8b3caae0ede5e001b10c0c3787aab51840782e`)
  matches the recorded value, and the SHA-256 values of `build.py`,
  `Plane.lean`, `Result19.lean` and `Audit.lean` match the author's own
  `new_formal_source_sha256` entries in `kernel-audit.json`.
- Second phase: `reproduce.py --reconstruct` also passes here — 31 unit
  tests, the Python card checker verifies all 3,468 cards, both candidate
  corruption controls are rejected, and the bounded construction
  regenerates the certificate **byte-for-byte identical** (36,084
  constructor calls; 18.1 s here, 13.7 s recorded).

So the recorded kernel audit is **confirmed by independent reproduction**:
the 19-move upper bound for the infinite board (19 actual Maker claims,
including the winning claim, from the empty board) and the 17×17 companion
rest on a Lean kernel check that a third party has now rerun end to end.
This package supplies no new proof and makes no optimality claim (the
source claims none); it does not by itself change the site's evidence
level.

## Pins and selection

- Verifier base: `817a8bb03d599860804c0843e8bd9b356efcbe83`.
- Claim source: [`shjvandekamp/math` at
  `db6e1d89a0637b013a86464bd766c0a5120e454e`](https://github.com/shjvandekamp/math/tree/db6e1d89a0637b013a86464bd766c0a5120e454e),
  `topics/snaky/` — the commit the site row links. Per-file SHA-256 pins
  are in `data/source-pins.json`; `data/kernel-audit-recorded.json` is a
  byte copy of the pinned commit's `topics/snaky/formal/kernel-audit.json`.
- Site snapshot: the [Snaky row](https://bigospeedrun.com/other/snaky),
  read 2026-10-23, lists the 19-move result as rank 1, **Claimed**, with
  proof scope "Author-run Lean 4.34.1 audit: Snaky.snaky_wins_plane_in_19
  (every legal Breaker reply on the infinite board) and the 17×17 theorem
  use only the standard axioms; **no independent rerun**."
- Overlap check (2026-10-23): in the verifier, "snaky" occurs only in the
  formalization and lean-statements track READMEs' open-target lists; no
  package in any track, and no pull request open or closed, touches this
  row. Both recorded runs of the audit target (the macOS main run in
  `kernel-audit.json` and the Linux tarball rebuild described in
  `formal/README.md`) are the author's.
- Toolchain: Lean **4.34.1** via elan (`leanprover/lean4:v4.34.1`),
  reporting `Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit
  5045d0056413266e57c625dcd7c365b10e377c52, Release)` — the same version
  string and commit as the author's official-release builds. No Mathlib
  or external Lean packages are involved; the development is Lean-core
  only, and every data check is `decide +kernel` (per the source).

## The claim, pinned exactly

Maker (Black) wins the placement game on the infinite integer board
within **19** of its own claims, including the winning claim, from the
empty board, against every legal Breaker reply. In Lean this is the
single theorem `Snaky.snaky_wins_plane_in_19` above:
`Snaky/Plane.lean` defines cells as `Int × Int`, requires every claim to
be fresh, quantifies over every legal integer-pair Breaker reply, and
counts Maker claims including the winning claim; a direct plane soundness
theorem connects the finite card checks to legal play on the infinite
board (no unformalized finite-to-infinite transfer). The companion
theorem states the same 19-move win on the empty 17×17 board. The
certificate is the 3,468-card file `topics/snaky/certificate/snaky19.cards.txt`,
from which `build.py` generates the `Snaky.Gen19` Lean modules
(7 `Data` modules and 1,165 `Chunk` modules) that the kernel checks one
by one.

What a pass means here, precisely: the Lean kernel accepted every
generated card obligation and both final theorems, with the recorded
types and the standard three axioms. The card *generator* is untrusted
by design — each obligation is reduced by the kernel — so the rebuild
does not need to trust `cards2lean.py`, only the kernel, the pinned
compiler, and the soundness theorems, which are part of the compiled
closure.

## How this audit ran

Working directory `~/workspace/bigospeedrun/snaky-audit/` (local): a clean
clone, checked out at the pinned commit, never modified (`git status`
clean after the run; build artifacts live in git-ignored paths). Machine:
Linux 7.0.0-39-generic x86_64, AMD EPYC 9D64, 2 cores, ~7.9 GB RAM.

Timed dry run (first modules, author's command and caps): base modules
1.1–14.3 s; generated `Data` modules 43–133 s; `Chunk` modules mostly
0.5–13 s. The worst module (133.2 s) sat inside the 180 s cap with 26%
headroom and peak RSS (~2.37 GiB) matched the author's 2.36 GB, so the
full pass proceeded.

Full run, in two attempts (details in `evidence/build-summary.json`):

1. Attempt 1 (start 2026-10-23T22:58:53Z) compiled **419** modules, then
   the process died at about 23:36Z when its launcher session ended — no
   Lean error, no module failure, no exit record. The 419 compiled
   modules were preserved in `build.py`'s resumable per-module state.
2. Attempt 2 (2026-10-24T00:05:53Z → 00:35:52Z, exit 0) resumed in a
   detached session: the 419 cached modules were digest-verified and
   reused (not recompiled — resumption is `build.py`'s own design), and
   the remaining **763** modules compiled in 1,796.0 s, completing all
   1,182. Build.py's own report for the completing run is the final JSON
   line of `evidence/build-log.txt`.

Across both attempts this audit itself compiled every one of the 1,182
modules exactly once, for 4,048.5 module-seconds total. Peak child RSS:
2,490,308 KiB (2.37 GiB, build.py's own `ru_maxrss` for the completing
run), against the author's recorded 2,360,246,272 bytes (2.20 GiB) on
macOS arm64.

The only log noise: two pre-existing linter warnings in the author's
`Snaky/CardsSound.lean` ("This simp argument is unused"). No errors, and
no `declaration uses 'sorry'` in any module log (`build.py` aborts on
one, and never did).

## Comparison against the recorded audit

Item-by-item, from `evidence/comparison.json`:

| Item | Recorded (author) | This rebuild | Match |
|---|---|---|---|
| `snaky_wins_plane_in_19` type | `Snaky.PlaneBlackWinsIn 19 [] []` | identical | yes |
| `snaky_wins_plane_in_19` axioms | `[propext, Classical.choice, Quot.sound]` | identical | yes |
| `snaky_wins_17x17_in_19` type | `Snaky.BlackWinsIn (Snaky.placements 17 17 Snaky.snaky) (17 * 17) 19 [] []` | identical | yes |
| `snaky_wins_17x17_in_19` axioms | `[propext, Classical.choice, Quot.sound]` | identical | yes |
| Certificate SHA-256 | `baf8774e…40782e` | identical | yes |
| Modules in `Snaky.Audit` closure | 1,182 | 1,182 | yes |
| Missing / extra theorems | — | none | yes |
| `sorryAx` or unexpected axioms | none | none | yes |

The author's second recorded run was itself author-run (official Linux
tarball, per `formal/README.md`); this package is the first third-party
reproduction of the kernel audit.

## Scope and limits

Covered: the Lean kernel audit of the two named theorems at the pinned
commit, and the certificate byte-reconstruction. Not covered: the
15×15/24-move subtopic and the board-size closeout (separate results in
the same repository); any optimality statement (none is claimed — 19 is
an upper bound); the game-theoretic prose in the source manuscript
beyond what the two theorems state. The author's separate Python card
checker (`topics/snaky/verification/verify_cards.py`, exercised here via
`reproduce.py`) checks finite-board card semantics; it is **not** a
substitute for the kernel rebuild, and this package's headline result is
the kernel rebuild, not the checker pass. Timing and RSS figures are
single-run measurements on this machine.

## Reproduce

Full independent rebuild (about 1–1.5 h on a 2-core machine; the author's
pass was 1,832 s on an arm64 Mac):

```sh
git clone https://github.com/shjvandekamp/math
cd math && git checkout db6e1d89a0637b013a86464bd766c0a5120e454e
# install the official Lean 4.34.1 release (or elan toolchain leanprover/lean4:v4.34.1)
python3 topics/snaky/formal/build.py --lean /path/to/lean --target Snaky.Audit
python3 topics/snaky/reproduce.py --reconstruct   # optional second phase
```

Package verification (fast; validates this package's files and the
recorded evidence of the run above — it does **not** rerun the Lean
build):

```sh
python3 -I -B auto-research/audits/2026-10-23-ptweezy-snaky-19-move-lean-audit/verify.py
```

## Package contents

- `README.md` — this file.
- `RESULT.json` — track metadata.
- `NOTICE.md` — sources, credit and AI disclosure.
- `MANIFEST.json` — SHA-256 of every file in the package.
- `verify.py` — package integrity + evidence/comparison validation
  (see the Reproduce section for what it does and does not rerun).
- `code/extract.lean` — the auditor-written probe used for the
  independent theorem/axiom extraction.
- `data/source-pins.json` — source repo, commit, per-file SHA-256 pins.
- `data/kernel-audit-recorded.json` — byte copy of the author's recorded
  audit at the pinned commit (the comparison baseline).
- `evidence/build-summary.json` — machine-readable run record:
  environment, both attempts, timings, slowest modules, reconstruction.
- `evidence/comparison.json` — item-by-item theorem/axiom diff.
- `evidence/build-log.txt` — the complete `build.py` log of both
  attempts, including the `Snaky.Audit` output and the completing run's
  JSON report.
- `evidence/independent-extraction.txt` — the probe's output.
- `evidence/reproduce-output.txt` — the full `reproduce.py --reconstruct`
  output.
