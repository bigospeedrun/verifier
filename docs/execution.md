# Big O Speedrun verifier

This repository runs public Lean proof checks on a fresh GitHub-hosted VM.
A maintainer starts **Verify a Lean proof** from the Actions tab. The workflow
uploads full logs and a JSON receipt, including failed and incomplete checks.
No leaderboard file is changed by a run.

## Start a run

The workflow has five inputs:

| Input | Meaning |
|---|---|
| `repo_url` | Public `https://github.com/OWNER/REPO` submission URL |
| `commit` | Complete 40-digit commit SHA; branch names are rejected |
| `challenge_file` | Registered statement file in **this verifier repository** |
| `theorem_names` | Comma-separated names allowed by that statement's profile |
| `lean_toolchain` | Toolchain pinned by the reviewed profile |

The first profile is `challenges/dft/UniformFourier233.lean`, Lean 4.34.1.
It checks `OAI.PowerSaving.transform_mainY` and
`OAI.PowerSaving.convolution_mainY` at saving `7547360/10^10`.
The dispatch defaults pin Chafik Boukhalfa's (`chafreaky`) [PR #2](https://github.com/jacobalansussman/wht-power-saving-lean/pull/2)
head `837dc3130adc79f7b7ab4ddd56c15576bbd766b0`, observed 2026-10-10.
A new challenge or toolchain requires a reviewed repository change.

## Patched lean4export

`profiles/tools.json` pins lean4export `076e8e5` plus two patches, each pinned by sha256 in
`lean4export_patches` and applied in order with `git apply --check` first:

- `patches/lean4export-pr52-natlit-print.patch`: [lean4export PR #52](https://github.com/leanprover/lean4export/pull/52)
  by lordwilsonDev as is (upstream head `21deacbe`). `Nat.repr` prints a natural number one digit at a time,
  which is quadratic; the PR prints by divide and conquer, byte for byte the same output.
- `patches/lean4export-natlit-parse.patch`: [lean4export PR #60](https://github.com/leanprover/lean4export/pull/60),
  the parse side of #52 (our PR). Comparator parses the export with `String.toNat?`, also quadratic;
  `parseDecNat?` gives the same result on every string.

Why: verifier#187 has natVal literals of 1.9 M digits. Without the patches, its export did not end in 5 h 14 min
(about 810 s per literal); with them, the export took 19-28 min and the full Lean check passed in 3 h 13 min
(task b1457f08, Measurements 1b-1d, 2026-11-11/12). After `build-comparator`, setup builds
`tests/lean/NatTest.lean` against a copy of the patched source and runs it (`nattest`): both functions must equal
Lean's own on edge cases, values next to powers of ten and random digit strings, and a 1.9 M-digit value must
print and parse in at most 60 s each. A failure stops setup before any submission code. Other tool files keep
unpatched lean4export. When upstream merges both PRs, move the pin past them and delete the patches, the
`lean4export_patches` entry and the self-test.

## What the workflow checks

1. Fetch the pinned submission without running its scripts or Lake file.
2. Build pinned Comparator, exporter, nanoda, and landrun tools. Fetch the
   pinned Mathlib cache in a separate trusted setup step.
3. Copy regular Lean source files into a fresh project with our Lake config.
   Comparator first builds and exports our trusted challenge. Its solution
   build then compiles dependency chains from source, one new module at a time.
4. Compare the solution statement and its dependencies with our challenge,
   check permitted axioms, and replay the proof in Lean's kernel.
5. Run `#print axioms` for each target. Run Comparator again with nanoda enabled;
   that pass also repeats Lean's kernel check.
6. Upload `receipt.json`, source/tool hashes, per-stage logs, times, and
   sampled cgroup memory peaks as `verifier-receipt-and-logs-…`.

The receipt reports each theorem and kernel separately. The theorems in one
request share a proof closure, so their time and memory measurements are shared.
A complete pass requires both kernels and the axiom audit. A failed workflow
can still contain a completed Lean-kernel pass; read the per-kernel receipt.
A timeout or resource limit gives no mathematical verdict.

The trusted DFT statement is based on our saved OpenAI challenge, not the
submission's challenge. It covers every positive length and every complex
input in the same exact scalar/index RAM, including root-order selection,
supplied canonical root, preparation cost, and polynomial integer/work bounds.
It is an operation-count theorem, not a bit-complexity claim.

## Isolation and resource limits

- `permissions: contents: read`; checkout does not retain credentials. The
  workflow uses no repository secrets and no Actions cache upload/save action.
- A new VM runs each job. Network access is used only for public source fetches
  and trusted tool/dependency setup. No submission code runs during setup.
  Setup loads Ubuntu's packaged `bwrap-userns-restrict` AppArmor profile so
  bubblewrap can create its namespaces; global userns restrictions stay enabled.
- Submission compilation, export, kernel checks, and audit run in a bwrap
  namespace with no network, a private process namespace, and an empty
  environment except for explicit tool paths. Comparator also retains landrun
  and its AF_UNIX restriction. Missing isolation causes a failure.
- Only public system executables/libraries, the toolchain/tools, the fixed
  dependency cache, staged sources, and trusted control files are readable.
  Only the run's build directory and temporary directory are writable.
  The workflow checkout, credentials, host process tree, receipts, and cache
  are outside the submission's writable namespace.
- Submission Lake files, hooks, generators, submodules and compiled objects are
  not used. The trusted challenge imports only fixed Mathlib. Its compiled
  outputs are removed inside the sandbox before each Comparator call so an
  earlier submission build cannot replace the statement used for comparison.
- One workflow runs at a time. New modules compile in dependency order using
  four Lean threads, nice 10, a 4-CPU quota and a 14 GiB RAM cgroup maximum. Builds and the Lean
  check of a one-job run have no swap, so an oom-kill during a build still restarts it with fewer Lake
  workers. The nanoda phase, and the Lean check of a split run (its build is done in job 1), get 16 GiB of
  swap on the disposable VM: Comparator retains its parsed proof while the external kernel runs, and the
  builtin replay of one large declaration can pass the 14 GiB cap (verifier#187: one declaration took
  Comparator to 11.6 GB, unit peak 13.2 GB, 0.3 GB swap used). The swap file is on the runner's /mnt disk
  when it has room, else on the work disk, outside the submission mounts; receipts record sampled swap
  use separately. This uses the standard free public runner.
  There is no soft memory limit that would force prolonged reclaim.
- The job timeout is **350 minutes**. Verification stops at a 335-minute total
  deadline, leaving time to save artifacts. Tool setup has a 45-minute limit.
  The controller also stops a check if free disk falls below 1 GiB.
- Setup removes only known preinstalled SDK folders on the disposable runner
  to make room for Lean and Mathlib. It does not reuse proof objects or publish
  cache entries from an untrusted build.

## Split build for large proofs

A profile with `"runner": "github-split"` runs in two hosted jobs of one
workflow run. Today `catalan` and `3sum` have it. Catalan opened on 2026-10-27, after
the maintainer smoke below passed (run 40497685416, issue #68). 3SUM issues run split
since 2026-11-02: issue #99 compiled one module at a time for 5 h 16 min in one job
and ran out of time (run 41393097953). Each job has the 350-minute job timeout and its
own 335-minute deadline from its own `prepare`. Both issue jobs set `BOS_SPLIT`
from the matrix entry; their unit-test steps clear it, and the suite also passes with
`BOS_SPLIT=true` (rerun 41494392206 of #99 failed there). The PR route has no
build job and never splits: a 3SUM PR runs as one job, as before, and keeps the chain build. A Catalan PR starts no job
(the PR route admits only `dft`, `3sum` and `apsp` folders).

1. Job `build` (`contents: read`, `issues: read`, no secrets) runs the same
   gate, tests, `prepare` and `setup`. Then `verifier.py build` runs one
   parallel `lake build <solution module>` with the real Lake (not the chain
   shim) in the same bwrap sandbox, in the unit `bos-verifier-build`. The unit
   has the same caps as the checks and no swap. It stops 15 minutes before the
   deadline. A failed or partial build does not stop the job. The receipt
   records the exit code, the unit result and the sampled peak memory.
   Lake builds 4 modules at once (`LEAN_NUM_THREADS=4` for Lake), or the profile's
   `lake_workers_start` (Catalan: 1; on verifier#187 the 4, 3 and 2 attempts cost 85 min, darkhipo). After an
   `oom-kill`, the build continues in a new unit with 3, then 2, then 1
   modules at once, until it stops for another reason or the deadline comes.
   Lake keeps each finished module. The receipt records each attempt
   (`build.attempts`), and `build.log` holds all of them (verifier#182).
   Job 2 uses the same rule when its Lean or nanoda check continues the build:
   the shim reads the count from `control/lake-workers.txt`, which the
   verifier writes before each check. The first check starts at the count of
   job 1's last attempt, and the nanoda check at that of the Lean check. After
   an `oom-kill` before the shim reports each chain done (`exit=0`), the check
   starts again in a new unit with the next count, inside the job's deadline.
   The check record keeps each attempt (`attempts`), and its outcome comes
   from the last attempt only.
2. `verifier.py pack` (trusted, rule S2) runs after the unit has stopped. It
   walks `.lake/build` with `lstat` and never follows a symlink. It keeps only
   the allow-list below (regular files with one link, and directories) and
   records the count and the first 20 names of the other paths. It refuses more
   than 40 GiB of file bytes (`BUILD_MAX_RAW_BYTES`) or 200,000 members. It writes a sorted tar with fixed owners and
   modes and the real mtimes, to the nanosecond, as a stream into `zstd -3 -T4`
   (`build.tar.zst`; Lead, 2026-11-11: `ir/` travels in the pack, and the generated C
   compresses about 36 times). It refuses a compressed file over 8 GiB (`BUILD_MAX_BYTES`).
   The job uploads that file, never the raw folder, as `verifier-build-<run>-<attempt>-<issue>` (1 day). Its
   sha256 is the job output `build_sha256`. That hash covers only `build.tar.zst`.
   `build.json` and `build.log` are data from a trusted step of the same run
   (only that run's jobs can upload to it), and they go to the receipt as data only.
3. Job `verify` has `needs: build`. Its gate also stops (claimed only) when
   job 1's gate said `false`. Its `if:` uses `!cancelled()`, because
   GitHub skips a job whose needed job was skipped unless a status function is
   used. So a run without split works as before. After `setup`, a split run
   downloads the tar and runs `verifier.py unpack` (trusted, rule S1). The build
   job must have succeeded, the file must be at most 8 GiB, and `BOS_BUILD_SHA256` must equal its
   sha256. Unpack then decompresses it to a tar on the work disk and stops when the output passes
   the raw cap plus the tar headers (a decompression bomb cannot fill the disk). It checks every member before it writes a file. Only regular files
   and directories with relative UTF-8 names in the allow-list are permitted.
   One other member refuses the whole archive. A source root may not have the
   name of an entry in the toolchain's `lib/lean`. Unpack writes into the empty
   build folder from `prepare`, with `O_EXCL` and `O_NOFOLLOW`, and sets the
   mtimes. If unpack fails, no check runs, and the receipt ends as
   `setup_failed`. The report job runs as before.
4. In a split run (`BOS_SPLIT`), `prepare` writes one chain target, the solution module.
   So Comparator's solution build is one Lake call through the shim. It finds
   the restored files up to date, or rebuilds at the submission's own time cost.
   The kernel checks, the audit and the nanoda pass do not change. Nanoda gets
   the time that is left. For Catalan it can end incomplete (time or memory limit);
   that does not prevent Lean Verified.

The allow-list (`verifier.build_allowed`, one function for pack and unpack),
for each source root R of the profile and its solution dependencies:
`lib/lean/R.<ext>`, `lib/lean/R/…`, `ir/R.<ext>` and `ir/R/…`. Nothing else:
no `VerifierChallenge*`, no `VerifierAudit*`, no `Mathlib/…`, no other folder.
A source root cannot be `Init`, `Std`, `Lean`, `Lake` or `Verifier*`.

### Why the restore is safe: the LEAN_PATH order

In one job, Comparator builds and exports the challenge before submission code
runs. In job 2, the restored files are there before the challenge build. Lake
source at Lean v4.34.1 and v4.33.1 (the same lines in both tags):

- `src/lake/Lake/Config/Workspace.lean:356-357`: `leanPath` is
  `packages.foldl (fun dirs pkg => pkg.leanLibDir :: dirs) []`. The root package
  is `packages[0]` (line 105; `Load/Workspace.lean:37` makes it with index 0).
  So the root's `.lake/build/lib/lean` comes after every dependency package's
  lib folder.
- `Workspace.lean:391-392` and `:422`: `lake env` sets `LEAN_PATH` to
  `leanPath ++ lakeEnv.leanPath`. `Config/Env.lean:255` puts Lake's `libDir`
  first in `lakeEnv.leanPath`. For the toolchain's own Lake,
  `Config/InstallPath.lean:195-199` (`LakeInstall.ofLean`, used at :423-427)
  sets it to the toolchain's `lib/lean`. So the root's lib folder comes before the
  toolchain's lib folder (`Init`, `Std`, `Lean`, `Lake`).
- `src/Lean/Util/Path.lean:61-64` (`SearchPath.findWithExt`) takes the first
  entry that has a folder or `.olean` file named after the first component of
  the module name. `findOLean` (line 117) uses it and does not check that the
  module file exists. `Path.lean:102` and `:109` put `LEAN_PATH` before the
  built-in toolchain path.

So files in the root build folder cannot shadow Mathlib or another dependency
package. They can shadow the toolchain's own modules: a `lib/lean/Init/` folder
there would replace `Init` for every later Lean process. Rule S1 is the reason
that the split is safe: job 2 restores only the solution's own roots, and a
root cannot be `Init`, `Std`, `Lean`, `Lake` or `Verifier*`. The challenge
imports only Mathlib. Before it restores a file, unpack runs `lake env printenv
LEAN_PATH` in the sandbox (our Lake config only, no submission code) and saves
the result as `lean_path` in the receipt, so each split run records the order.

Shared libraries: `lake env` also sets `LD_LIBRARY_PATH`
(`Workspace.lean:372-373`, `:409-410`, `:431`; `Package.lean:374-375`;
`InstallPath.lean:160-164`). The order is the toolchain's `lib/lean` and `lib`,
then each package's `.lake/build/lib` (the root first), then the initial value.
The root folder comes after the toolchain, but the Linux loader reads
`LD_LIBRARY_PATH` before `/etc/ld.so.cache` and the system folders. So a
library that the toolchain does not ship, for example `libc.so.6`, in the root
`.lake/build/lib` would load in each later process that `lake env` starts. S1
also keeps shared libraries out of those folders: it restores nothing directly
in `lib/` or `lib/lean/`.

Note on the existing single-job path (not changed here): the nanoda pass and
the axiom audit start after the submission build of the same job. So their
processes can load a planted library or a shadowed `Init`. The Lean pass verdict
is not affected: Comparator exports the challenge before the solution build,
and it checks the axioms and replays the kernel in its own process, which
started before the build. The same applies to job 2 when its one Lake call
rebuilds a module.

### Catalan smoke (maintainers only)

A `test_only` artifact makes the site exclude the claim of its issue, so the
smoke must never run on another person's issue. A maintainer opens a test
issue with the form of `smoke.CATALAN_FIXTURE`: problem `catalan`, the fixture
repository URL, commit `a3d48494df743e8dbf2dd5acb70dbe27759069e0`, bound
`1091`, and the label `test` (a label needs triage rights). Then dispatch
**Verify direct submissions** with `smoke_route: issue` and that issue number.
Dispatch refuses an issue without the label, and an issue whose author is not
the user who dispatches the run (`GITHUB_ACTOR`). It does not check the author
association: the job token sees a private organization member as
`CONTRIBUTOR` (issue #68, 2026-10-27). The acknowledgement pass
and the scan skip issues with the label `test`, so only the dispatch runs a test
issue. The run is `test_only` and never imported. It posts no result comment,
no Lean checkpoint comment and no label. Read the artifacts.

The smoke of 2026-10-27 (verifier 6032768): job 1 built in 6178 s with a peak of
9.79 GB and packed 23,792 files (2.94 GB, 0 skipped). In job 2, the Lean kernel
and the axiom audit ended 142 minutes after `prepare`, so 178 minutes of the
320-minute deadline were left for nanoda.

### Subset Sum smoke (maintainers only)

Subset Sum opens only after this smoke passes (`submissions.CLOSED`). It runs
the same way as the Catalan smoke, on one job (no split build). A maintainer
opens a test issue with the form of `smoke.SS_FIXTURE`: problem `subset-sum`,
repository URL `https://github.com/darkhipo/subset-sum-mitm`, commit
`8b105f01848fc0e370abfa3a23ed5c3de463f321`, bound `3/4`, and the label `test`.
Then dispatch **Verify direct submissions** with `smoke_route: issue` and that
issue number. The run clones the repository of the author (verifier issue
#94); do not copy its files into a `bigospeedrun` repository, because it has
no license. It posts nothing. Read the artifacts.

### Snaky statement-mismatch runs (maintainers only)

Snaky opened on 2026-11-03 after these runs and the Snaky smoke with a real proof
(issue #113, run 41548037272). They run the same way as the Subset Sum smoke, one test
issue per entry of `smoke.SNAKY_MUTATIONS`, on the repository
`https://github.com/bigospeedrun/verifier-smoke-snaky` (our own files; the
proofs are `sorry`). Every run must be refused. Comparator compares the
statement before it checks axioms, so:

- the control (commit `c89f809`, bound `20`: an exact statement copy) must fail
  on the axiom check (`sorryAx`), not on the statement;
- each other entry must end with the Lean reason `statement_mismatch`: the
  bound `19` for the theorem about 20 (`c89f809`), one Snaky cell moved
  (`eca2430`), one symmetry dropped (`73041ba`), the freshness condition removed
  (`299e232`), and Breaker's reply legality for `k < N` (`9ddfaee`).

Comparator refuses a changed theorem type with "Challenge and solution theorem
statement do not match", and a changed definition that the theorem uses with
"Const does not match between challenge and target '<name>'". Both are the
compare step, and both give the reason `statement_mismatch` (a changed
definition also has `mismatch: definition`). The runs of 2026-11-02 were made
before the second message had this reason: their receipts say
`ambiguous_failure`, so read their `lean.log` (Lead, 2026-11-02: those runs are
accepted from the log line).

They post nothing. Read the receipts.

The Snaky smoke itself must pass: a test issue with the form of
`smoke.SNAKY_FIXTURE` (problem `snaky`, repository
`https://github.com/darkhipo/snaky-twenty`, commit
`f6248dc39a05a6c5665240d860d2dbb95db707d9`, bound `20`, label `test`). The run
clones the author's repository (verifier issue #106, Apache-2.0). It posts
nothing. Read the artifacts, and check the log for `autoImplicit` errors (the
profile builds with `autoImplicit = false`).

### Heilbronn triangle runs (maintainers only)

Heilbronn opened on 2026-11-03 after these runs (smoke: issue #123, run
41571110767), all on our own
repository `https://github.com/bigospeedrun/verifier-smoke-heilbronn`, one test
issue per entry, as for Snaky:

- the smoke (`smoke.HB_FIXTURE`, commit `42a4e7a`, bound `0`) must pass: the
  classical saving from `bound_zero` of `challenges/heilbronn-triangle/Validation.lean`.
  The public form refuses `0` (`submissions.ZERO_REFUSED`); only this pinned
  smoke reads it, and its result is `test_only` and never imported;
- the control (`c471bc6`, bound `1/50893237`, an exact statement copy and
  `sorry`) must fail on the axiom check (`sorryAx`);
- each mutation (`smoke.HB_MUTATIONS`) must end with the Lean reason
  `statement_mismatch`: the bound `1/50893238` for the theorem about
  `1/50893237` (`c471bc6`), the area divided by 3 (`c869f25`), the square
  `[0,1] x [0,2]` (`27734ae`), the condition `0 < c` removed (`6c77d88`), and the
  distinctness `q ≠ r` removed (`9a86923`).

They post nothing. Read the receipts.

### Prime gaps runs (maintainers only)

Prime gaps opened on 2026-11-07 after these runs (smoke: issue #172, run
42305726764 at verifier 2d44726), all on our own repository
`https://github.com/bigospeedrun/verifier-smoke-prime-gaps` (darkhipo's
`prime-gaps-246-lean` at `ac0eb01b` under `Submission/`, with only the imports
renamed), one test issue per entry, as for Snaky:

- the smoke (`smoke.PG_FIXTURE`, commit `abc6a6e`, bound `246`) must pass. It
  passed as a split run: build job 34 minutes, Lean 890 s (peak 6.6 GB), nanoda
  1211 s. Its first run (42301733703 at 18158dd) failed to build LeanArchitect,
  which needs Lean's default `autoImplicit = true` (fixed in 2d44726);
- the control (`1b31b82`, bound `246`, an exact statement copy and `sorry`)
  must fail on the axiom check (`sorryAx`);
- each mutation (`smoke.PG_MUTATIONS`) must end with the Lean reason
  `statement_mismatch`: the bound `245` for the theorem about `246` (`1b31b82`),
  `<` for `≤` (`ff005c1`), `∀ᶠ` for `∃ᶠ` (`f707281`), `m + 2` for `m + 1`
  (`ce76e48`), and `Prime` for `Nat.Prime` (`de38d4d`).

They post nothing. Read the receipts.

### Known limits

- The Lean checkpoint watcher (`live_publish.watch`, 330 minutes) cannot see the
  Lean checkpoint of a split run, which comes about 6-7 hours after the start.
  So only the final report posts.
- The queue lease is held for the whole split run: `queue_lease.acquire` has no
  time limit, and the run takes up to about 2 x 350 minutes.
- Nanoda can end incomplete (time or memory limit); that does not prevent Lean
  Verified. Comparator replays the proof again in the nanoda pass. In the smoke,
  nanoda passed in 9164 s with a peak of 11.69 GB of the 14 GiB limit, and 25
  minutes of the deadline were left.

GitHub's [runner reference](https://docs.github.com/en/actions/reference/runners/github-hosted-runners)
lists public `ubuntu-latest` as **4 vCPU, 16 GB RAM and 14 GB SSD**, checked
2026-10-10. These are the documented standard-runner specifications; receipts
record the run's measured usage. A proof can exceed those resources.

## Check chain for proofs that need more than one job

A profile with `"runner": "github-chain"` runs as a chain of hosted jobs in one workflow
run (task b1457f08): `build1`..`build4`, `export`, `check1`..`check4` and `final`
(`.github/workflows/submission-check.yml`, `scripts/chain.py`). No profile uses it yet.
It is for proofs whose build, or whose kernel check, does not fit one 350-minute job
(verifier#182: about 14 h of single-stream build left; the OpenAI 3-SAT proof: 3,091
modules, 23 GB of build output). Every job is a standard free `ubuntu-latest` runner with
read-only permissions, the 14 GiB unit cap and its own 335-minute deadline from its own
`prepare`. Each job runs its own `prepare` and `setup` (about 5 minutes) before any
submission file is built or loaded, so no tool comes from a job where submission code ran.

- **Build jobs.** `build1` gates like a split run's build job. Each later build job
  restores the pack of the job before it (`unpack`, the pin is that job's `build_sha256`
  output), continues the Lake build from the Lake worker count of the last attempt before it,
  and packs again. Lake keeps each finished module, so a job loses at most the modules
  that were in progress at its deadline. A job starts the next one only when its build
  reached the deadline (or the deadline cut the out-of-memory back-off), it made a new
  pack, and the caps allow it.
- **Export job.** It gates again (as a split run's check job), restores the pack of the
  build job that says `done` (`chain.py pick`: the build jobs that ran are `build1`..`buildK`
  in order, and only the last one is done), and runs Comparator `--bos-export` in the
  sandbox: the same challenge build and export, then the solution build (Lake finds it up to
  date) and export, written to two files. No comparison and no kernel runs in that unit.
  Then the axiom audit runs as usual. The controller moves both files out of the sandbox
  `/tmp`, compresses them (`zstd -3`) and uploads them; the sha256 of each compressed file
  is a job output.
- **Segments.** The export job and each check job run one segment of the kernel check:
  Comparator `--bos-check` (patches/comparator-segmented-check.patch, in
  `profiles/tools-chain.json`) in a new unit with a new empty `/tmp`. No Lake, no build and
  no submission code runs in it. The segment at 0 parses both files and runs Comparator's
  statement and axiom checks (`compareAt`, `checkAxioms`) first, so the bytes that it
  compares are the bytes that every segment replays. The replay is a copy of Lean
  v4.34.1's `Kernel.Environment.replay` (src/Lean/Replay.lean) with an index for each
  `addDecl` call in the fixed walk order. A segment adds the declarations before its start
  with `addDeclWithoutChecking`, sends each later one to `addDeclCore` (the full kernel
  check), and stops between two declarations at its deadline, after at least one check. The
  kernel adds an inductive type or the quotient in full in both cases (src/kernel/environment.cpp,
  `environment::add`). The segment that ends the walk runs the postponed constructor and
  recursor checks and Comparator's quotient post-check. A running hash of the added names
  links the segments. Each segment writes one JSON receipt.
- **Why the result is the same as one replay.** A full replay checks declaration *i*
  against the environment of declarations 0..*i*−1. A chain checks declaration *i* in exactly
  one segment, against declarations 0..*i*−1 added from the same export bytes (one sha256)
  in the same order, and each of those was checked in an earlier segment of the same chain.
  `setup` tests this before any submission code (`--bos-selftest`): on an export of about 630
  constants of Lean's `Init`, Lean's own `replay` and the segmented replay with one segment
  and with segments of 7, 23 and 97 declarations accept the export as it is and reject three
  tampered copies (a theorem with another theorem's proof, a definition with an ill-typed
  value, a constructor with a wrong field count), at the same declaration. It also tests a
  deadline stop after one declaration and its continuation.
- **Final job.** It reads each chain job's receipt by the `leg_sha256` that the job wrote
  as an output, and accepts the kernel check only when the segments, in job order, all
  replay the export with the export job's sha256, each starts where the one before it
  stopped and with its hash, the first one ran the statement checks, and the last one ended
  the walk with the postponed and quotient checks. Any gap, overlap or mismatch gives
  `incomplete` (`chain_coverage`), never `passed`. It writes one receipt with the provenance
  of the chain (`chain.legs`; darkhipo's merged-receipt idea from PR #191) and uploads it
  under the normal receipt name, so the report job does not change.
- **Caps.** The profile's `chain` object: `max_build_jobs` and `max_check_jobs` (1 to 4,
  default 1) and `max_hours` (at most 30, from the start of `build1`). The queue lease has no
  time expiry, so a chain holds the queue for all its time. A chain that reaches a cap ends
  `incomplete` (`build_chain_cap`, `check_chain_cap`), never rejected.
- **nanoda.** A chain runs no nanoda pass. On #187 it needed more than 26 GB. The receipt
  says `nanoda: incomplete (not_run_chain)`, which the verdict rule treats like its other
  incomplete reasons (advisory).
- **Re-runs.** The queue lease belongs to one run attempt (`queue_lease.assert_owner`), so a
  failed chain is run again as a whole, never as one job.

## Trust and credit

OpenAI wrote the exact RAM formalization and all-length DFT reduction at
`openai/math` commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.
Our challenge changes seven names with suffix `Y` and changes the decimal
saving. All machine definitions and quantifiers remain unchanged. See `NOTICE`.

The submitted proof builds on Jacob Sussman's checker and framework and the
community circuit credited in PR #2. Authorship of that proof stays with its
authors. Comparator, Lean, nanoda, landrun, bwrap, the OS, and the pinned
Mathlib cache are part of the checking environment. Tool and source hashes
are included for audit. This runner does not perform line-by-line human review.

Logs can contain untrusted submission output. The controller does not stream
that output as Actions workflow commands. The authoritative gate is the exit
status of the pinned Comparator plus its completed acceptance output.

Local controller tests require only Python:

```sh
python3 -m unittest discover -s tests -v
```

Lean compilation runs in GitHub Actions, not on the office host.
