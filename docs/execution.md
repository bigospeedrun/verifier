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
  four Lean threads, nice 10, a 4-CPU quota and a 14 GiB RAM cgroup maximum. Builds and the first Lean
  check have no swap. The nanoda phase gets 16 GiB of swap on the disposable VM
  because Comparator retains its parsed proof while the external kernel runs.
  The swap file is outside the submission mounts; receipts record sampled swap
  use separately. This uses the standard free public runner.
  There is no soft memory limit that would force prolonged reclaim.
- The job timeout is **350 minutes**. Verification stops at a 320-minute total
  deadline, leaving time to save artifacts. Tool setup has a 45-minute limit.
  The controller also stops a check if free disk falls below 1 GiB.
- Setup removes only known preinstalled SDK folders on the disposable runner
  to make room for Lean and Mathlib. It does not reuse proof objects or publish
  cache entries from an untrusted build.

## Split build for large proofs

A profile with `"runner": "github-split"` runs in two hosted jobs of one
workflow run. Today only `catalan` has it. Catalan opened on 2026-10-27, after
the maintainer smoke below passed (run 40497685416, issue #68). Each job has the 350-minute job timeout and its
own 320-minute deadline from its own `prepare`. The PR route has no build job,
so a PR for a split profile starts no job.

1. Job `build` (`contents: read`, `issues: read`, no secrets) runs the same
   gate, tests, `prepare` and `setup`. Then `verifier.py build` runs one
   parallel `lake build <solution module>` with the real Lake (not the chain
   shim) in the same bwrap sandbox, in the unit `bos-verifier-build`. The unit
   has the same caps as the checks and no swap. It stops 15 minutes before the
   deadline. A failed or partial build does not stop the job. The receipt
   records the exit code, the unit result and the sampled peak memory.
2. `verifier.py pack` (trusted, rule S2) runs after the unit has stopped. It
   walks `.lake/build` with `lstat` and never follows a symlink. It keeps only
   the allow-list below (regular files with one link, and directories) and
   records the count and the first 20 names of the other paths. It refuses more
   than 8 GiB or 200,000 members. It writes a sorted tar with fixed owners and
   modes and the real mtimes, to the nanosecond. The job uploads that tar, never
   the raw folder, as `verifier-build-<run>-<attempt>-<issue>` (1 day). Its
   sha256 is the job output `build_sha256`. That hash covers only `build.tar`.
   `build.json` and `build.log` are data from a trusted step of the same run
   (only that run's jobs can upload to it), and they go to the receipt as data only.
3. Job `verify` has `needs: build`. Its gate also stops (claimed only) when
   job 1's gate said `false`. Its `if:` uses `!cancelled()`, because
   GitHub skips a job whose needed job was skipped unless a status function is
   used. So a run without split works as before. After `setup`, a split run
   downloads the tar and runs `verifier.py unpack` (trusted, rule S1). The build
   job must have succeeded, and `BOS_BUILD_SHA256` must equal the sha256 of the
   tar. Unpack checks every member before it writes a file. Only regular files
   and directories with relative UTF-8 names in the allow-list are permitted.
   One other member refuses the whole archive. A source root may not have the
   name of an entry in the toolchain's `lib/lean`. Unpack writes into the empty
   build folder from `prepare`, with `O_EXCL` and `O_NOFOLLOW`, and sets the
   mtimes. If unpack fails, no check runs, and the receipt ends as
   `setup_failed`. The report job runs as before.
4. `prepare` writes one chain target for a split profile, the solution module.
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
