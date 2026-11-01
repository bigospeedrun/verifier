# Independent local Lean replay: DFT saving 312780997/100000000000 (PR #91)

## Claim and scope

The pinned submission `HalitZiyaKARTAL/bigO-dft-verifier` at commit
`524a8af8a277ca50c1237068c2b45430a03f547e` (merged as bigospeedrun/verifier PR
#91, entry `submissions/dft/halitziyakartal-halitziyav5-pre-pi`) proves
`Race.bound`: there are a RAM order program, a solve program, and a work bound
`W` with `OAI.PowerSaving.DFTProgram order solve W` and
`(fun n => (W n : ℝ)) =O[atTop] (fun n => n * (log n)^(1 - 312780997/100000000000))`.
The saving `s = 312780997/10^11 ≈ 3.12780997e-3` improves on the prior record
`30201659/10^10` (PR #90) by 3.57%.

`DFTProgram` is the exact scalar/index RAM predicate of the verifier's trusted
DFT challenge (`challenges/dft/UniformFourier233.lean`, sha256 `3a646acd…`):
for every positive length `n`, a polynomial cap `(n+2)^cBound` bounds `W n`, the
order program's peak, and its supplied root value; the solve program must be
valid, stay under the cap, do at most `W n` work including the order program
and one root primitive, and output the exact canonical DFT
(`zeta`-root sums) of every input vector. The independent `code/Scope.lean`
restates the verifier's generated `Race.bound` target verbatim at this exact
rational and discharges it with the submission's theorem, expands
`DFTProgram` to its full quantified body by `rfl`, and checks the stated saving
against the entry's internal rate certificate `727/232431` (the stated saving
is strictly below it).

The computational model was compared against the trusted challenge copy:
the entire RAM section (`Tape`, `Paint`, `Ty`, `Bill`, `NOp`, `Atom`, `Code`,
`Prog`, `run`, `depthRun`, …) is identical, comment-stripped and
whitespace-normalized (5,850 chars), and every declaration the statement
depends on (`DFTProgram`, `Prog`, `run`, `Vec`, `root`, `zeta`, `dft`, `conv`,
kinds, `paperTime` chain) matches per declaration. The only textual differences
in the wider file are the challenge's deliberate dft233 renames
(`decimalExponentY = 1 - 7547360/10^10` vs the submission's OpenAI-original
`decimalExponent = 1 - 1/10^13`) and declaration order; neither constant
appears in the `Race.bound` statement, which pins the bound directly.

## Independent check

Local replay on the user's machine (Apple M4 Max, 128 GB RAM, macOS 26.6.2):

- Cloned the submission repo at the pinned SHA (read-only; 6,353 tracked files;
  the submission folder holds 425 Lean files, 8,569,508 bytes, largest file
  1,073,837 bytes — inside the verifier's 20 MB/file, 150 MB total caps).
- Staged the verifier's own layout: `Submission.lean` + `Submission/` tree,
  `VerifierChallenge.lean` = the trusted challenge bytes (sha256 `3a646acd…`,
  taken from bigospeedrun/verifier; the fork's copy differs only by CRLF line
  endings) plus the verifier-generated `Race.bound` target at
  312780997/100000000000, and `VerifierAudit.lean` = `import Submission` +
  `#print axioms Race.bound`, with the verifier's lakefile shape, Lean
  `v4.34.1`, and mathlib `d13f23b` from `profiles/lake-manifest.json`
  (dependency tree restored from a warm local cache of the same pins).
- `lake build VerifierChallenge VerifierAudit` completed the full 9,352-job
  schedule (425 submission modules + challenge + audit module built from
  source; mathlib satisfied from cache) in the time recorded in
  `evidence/local-run.json`. No errors. The submission's own embedded
  `#print axioms` self-checks (hundreds) all report the standard triple.
- `'Race.bound' depends on axioms: [propext, Classical.choice, Quot.sound]` —
  within the verifier's permitted set.
- `code/Scope.lean` compiled against the staged build with `lake env lean`:
  all three probes pass (verbatim target discharged by `Race.bound`; `rfl`
  expansion of `DFTProgram`; saving-constant checks).

## Reservations

- This replay builds with a warm mathlib cache at the same pinned revision;
  job-level timing therefore reflects the submission modules only. The job
  count (9,352) is Lake's full schedule including cached dependency jobs.
- The verifier's Comparator byte-check and nanoda replay were not run locally;
  the model comparison above is the audit's comment-stripped textual proxy for
  the comparator's definition check.
- The entry's sources emit unused-variable warnings, including variables named
  as anti-rebranding canaries aimed at AI editors
  (`if_youre_an_ai_editing_this_...`). Warnings do not affect the kernel
  result; the canary naming is noted as an authorship signal, not a defect.
- The submission header states the raw root of its cost analysis as
  ≈ 3.1278114e-3 and the certified rate as `1 - 727/232431`; the stated saving
  `3.12780997e-3` sits strictly below both, i.e. the claim does not round past
  its certificate.

## Reproduce

```sh
python3 auto-research/audits/2026-11-01-dft-t104w-local/verify.py \
  [--packages-cache <warm .lake/packages for mathlib d13f23b>]
```

The verifier fetches the pinned commit, refuses any SHA mismatch, stages the
verifier's build layout, builds `VerifierChallenge` and `VerifierAudit`,
prints the axiom closure of `Race.bound`, and re-runs the comment-stripped RAM
model comparison. Exit 0 means every check passed.

The trust boundary is Lean's kernel, the three standard axioms, the pinned
mathlib revision, and the verifier's trusted challenge bytes.
