/-!
written with help of ai↓

# Bottlenecks: where build time and memory go, and what was tried

This module has no code. It records where the time and memory of building the tree go, what was
changed to cut them, and what did not help. Nothing here is needed for correctness. All numbers
are measurements on one machine (4 cores, Xeon 2.1 GHz, 15 GB RAM, Lean 4 with a prebuilt
Mathlib), the same machine for the gate rows of §1, the per-module table of §2 and the older
per-declaration profile of 7fa1528 quoted in §2; they were taken on 2026-11-27. A "fresh build" is
`lake build Submission` from an empty build directory with Mathlib already built. Two fresh builds
of the same commit differ by up to about ±10 s of wall time on this machine (other jobs share
it), so only paired runs and large differences mean something.

---------------------------------------------------------------------------------------------

## 1. The tree now

16 code modules plus `Submission.lean` (about 1.0 MB of Lean source, of which `WalshTemplate.lean` is
315 KB), no generated data, no `decide` on large data, no `native_decide`.

Fresh build of this tree: **45.4 s wall, 138.9 s user, peak 3.14 GB**, 2278 jobs
(almost all of them prebuilt Mathlib modules that are only loaded).

History of the same measurement (the fresh gate) over the redesign of 2026-11-27, one row per commit
of this tree's history (the hash names the commit; the second column says what it changed):

| commit | what changed | wall s | user s | peak GB |
|---|---|---:|---:|---:|
| 9480f52 | before the redesign (23 modules) | 81.5 | 228.7 | 2.81 |
| 7fa1528 | the cost-calculus file split in six | 73.5 | 201.7 | 2.81 |
| 790b5b5 | modules merged to 17; slow proofs rewritten | 55.0 | 155.2 | 3.18 |
| baeba28 | four files partly rewritten | 58.3 | 156.6 | 3.18 |
| 637e41b | folders flattened, files renamed | 59.7 | 151.6 | 3.18 |
| 806b841 | unreached declarations removed; 12 proofs rewritten | 53.4 | 150.4 | 3.18 |
| 5aad7e6 | explanation texts rewritten, stale headers and docstrings fixed | 62.5 | 155.5 | 3.17 |
| ce445ea | duplicates, wrappers and unused fields removed; credits by what is left | 63.8 | 154.8 | 3.18 |

(9480f52 was also measured once at 71.3 s / 200.0 s; that run is the reason for the ±10 s remark.
5aad7e6 changed no proof, so its +9 s wall over 806b841 at nearly the same user time is that
noise. For 7fa1528 the row is the gate run; a separate fresh run gave 82.1 s / 233.6 s,
and the build simulator of the profile notes predicted 70–74 s wall, 211 s user (+30 s sys).)

## 2. Per module

Each module compiled alone on 806b841 with `lake env lean <file>` (this includes about 2 s of
`lake env` start-up per call; the machine was shared with other jobs, so read these as upper
bounds). `user > wall` because Lean elaborates the proofs of one file on several threads.
ce445ea differs from 806b841 by small deletions only; it was not re-measured per module.

| module | wall s | user s | peak RSS GB |
|---|---:|---:|---:|
| `WalshTemplate` | 20.5 | 45.1 | 3.10 |
| `ReelKit` | 8.8 | 13.2 | 2.73 |
| `EngineRecursion` | 8.4 | 14.9 | 2.75 |
| `EngineCost` | 8.2 | 8.1 | 2.61 |
| `EngineMoves` | 8.2 | 10.2 | 2.65 |
| `ReelCompile` | 7.6 | 10.0 | 2.69 |
| `DFTPrograms` | 7.3 | 9.9 | 2.69 |
| `CostCalculus` | 6.6 | 8.3 | 1.94 |
| `WorkModulus` | 6.5 | 6.0 | 2.65 |
| `EngineSetup` | 6.2 | 6.2 | 2.63 |
| `PlanToWord` | 5.9 | 8.5 | 2.76 |
| `DFTIdentities` | 4.8 | 5.1 | 2.61 |
| `EngineFromTemplates` | 4.4 | 3.5 | 2.70 |
| `Submission` | 4.3 | 3.3 | 2.70 |
| `RAM` | 4.2 | 3.1 | 1.71 |
| `BinaryKernel` | 4.2 | 4.0 | 2.02 |
| `Goal` | 4.0 | 2.7 | 2.45 |

What sets the wall time of a fresh build: the longest import chain, with 4 workers.
`WalshTemplate` (Mathlib only) runs beside everything else from the start and is the single longest
job. The chain `RAM → CostCalculus → EngineMoves → EngineSetup → EngineRecursion → EngineFromTemplates → Submission` and the chain
`… → ReelKit → ReelCompile → DFTPrograms → Submission` are each a little over 40 s of the per-module
numbers above.

### Hot spots inside the modules (7fa1528 profile)

The only per-declaration profile is of tree 7fa1528 (28 modules, before the merges), taken with
`trace.profiler`. Its modules had other names; the entries below are listed under the present files
that hold their code (roughly, not checked one to one). All times in this subsection are 7fa1528 numbers.

* `WalshTemplate.lean`. In 7fa1528 its four parts cost 5.4+7.6+8.0+10.9 s wall and
  8.8+14.1+16.5+23.4 s user as separate jobs (about 62 s user together). Heavy declarations
  there: `templates_of_rate` 2.74 s, `calls_le` 2.26 s, `one_side` 0.85 s, `params_rate_side` 0.84 s,
  `hornerP_calls` 0.79 s, `window_params` 0.79 s, `template_calls` 0.78 s, `tgtL_eq` 0.75 s,
  `division_repair_mat` 0.67 s, `rowBank_calls` 0.60 s. Why: `templates_of_rate` builds the whole
  candidate with `choose` and many large `have` terms; `calls_le` is a long chain of `gcongr`
  and `omega` on big power expressions; the rest are `simp only` with large lemma sets over
  matrix entries, `fin_cases` and `decide` on `ZMod 2`. It imports only Mathlib, so it can start
  at once.
* `DFTPrograms.lean`. In 7fa1528 the main module was the slowest single job (16.7 s wall,
  21.8 s user) and the last on the critical path. One declaration, the `freq_moves` body
  (then a separate lemma), took 12.24 s, mostly `refine` (9.7 s): a long
  `Can.bind` chain where every step elaborates a `Bench.extend` of a growing tuple type and
  unifies large `FreeReads`/`Moves` terms. Next: `axisData_dry` 1.32 s, `axisDFTCost_le` 0.64 s,
  `envelope_lim` 0.63 s, the time bound now folded into `hadamard_exp` 0.61 s.
* `EngineCost.lean`. 15.3 s wall / 18.1 s user in 7fa1528; the budget proof (now
  `budget_exists`) 13.5 s, a top-cost bound (since removed) 2.09 s, the step bound (now
  `step_of_cover`) 1.48 s. Why: real-number inequality chains closed by
  `linarith only` / `nlinarith` with many hypotheses, plus `field_simp` and `rpow` rewriting.
  `nlinarith` alone showed 1.6–2.1 s in the trace. (Since then the `nlinarith` calls are gone,
  see §4.)
* `ReelKit.lean`. 10.1 s wall / 16.3 s user in 7fa1528; `grid_gains` 1.31 s,
  `cell_zones` 1.00 s, `blockFilter_cyclic` 0.55 s, `naive_gains` 0.53 s, `toeplitzReel_go` 0.40 s.
  Why: `cell_zones` then discharged ~14 zone separation goals with `omega` on nonlinear-looking
  terms after `generalize`; `grid_gains` sums over `tripleConcat` with `sum_blocks` rewriting.
* `WorkModulus.lean`: `modulusAxes_in` 1.08 s, `modulusAxes_spec` 0.63 s,
  `oddPrime_count_ge` 0.45 s, `oddPrime_word` 0.36 s.
* `ReelCompile.lean`: `ReelComputes.toeplitzReel` 0.44 s, `LineConj.blockFilter` 0.39 s, `LineComputes.toeplitzInv`
  0.38 s, `blockRippleMat_mul` 0.37 s.
* `EngineMoves.lean`: `naive_high_can` 0.90 s, the splitting lemma (now `Cleave.adapted`) 0.42 s, `xor_prepare` 0.40 s,
  `sky_bool` 0.39 s.
* `PlanToWord.lean`: `rowSum_correct` 0.41 s, `unit_live` 0.35 s, `mixG_out` 0.34 s.
  The `pairMat_entry`, `littleC_pair`, `littleC_phase` case splits use `decide := true` and `linear_combination`
  (not checked as hot spots).
* `EngineRecursion.lean`: no single hot declaration in the older profile; its cost is many medium proofs
  with long `linarith only` / `omega` closures (in what is now `tree_able`,
  `RealisesRule.ripple_engine`, `top_able`).

## 3. What the memory is

Peak memory is not our proofs; it is Mathlib being loaded. A module that imports analysis
(`Real.rpow`, asymptotics) holds about 2.6–2.8 GB while it compiles, whatever its own size;
`RAM.lean`, which imports only the complex numbers, holds 1.7 GB. With 4 workers the build peak
(3.18 GB, as reported by the gate) is the largest single process plus shared pages. It rose from
2.81 to 3.18 GB in the same commit (790b5b5) as the template merge, when the four template files
became one 315 KB module; that the merge is the cause is a guess, not a measurement.

## 4. What helped, in order of effect

1. **Rewriting slow proofs.** The build is CPU-bound on a few declarations, not on module count.
   Before the redesign two declarations took most of the CPU of their files:
   the axis transform lemma in `DFTPrograms` (12.2 s, now replaced by `gather_moves` /
   `spread_moves` with an explicit proof) and the budget proof (now `Rule.budget_exists`) in `EngineCost` (13.5 s,
   now about 4 s after replacing large `nlinarith` calls by explicit steps). After the rewrite no
   declaration in `ReelKit` or `ReelCompile` takes more than 0.74 s.
2. **Removing what the theorems do not need.** The depth-general engine setup, the two-halves
   adapter around the engine, the recursive "rest" jobs, the Gaussian elimination in the template
   and the declarations no public theorem reaches were deleted (their text is kept outside the
   submission build). This is where the size went down.
3. **Fewer modules.** Each module costs about 1.2–2.2 s of import loading (measured with an
   import-only file). Merging 28 modules into 17 saved that many loads. Splitting a file only
   pays when it shortens the longest chain: moving the pure cost arithmetic to `EngineCost` did;
   splitting the cost calculus in six did not (and was merged back into `CostCalculus`).

## 5. Measured and ruled out

| idea | what was measured | why it is out |
|---|---|---|
| many small modules for parallel build | 5 extra modules: about +1 s wall, +4 s user in the simulator; no gain on the chain | import loading is paid per module; the verifier uses 4 workers |
| narrowing Mathlib imports | import-only time is 1.2–2.2 s per module whatever the imports | at most about 0.4 s per module |
| `-DElab.async=false` | about 8 % less CPU, but the file's wall time doubles | wall time is what the gate measures |
| heartbeat settings | a limit costs no time | no effect |
| bundling the reel soundness and beat-count lemmas into one record | every such lemma has a user in the reel proofs or in `DFTPrograms` | deletes nothing |

## 6. Levers that remain

* `WalshTemplate.lean` is one third of the source and of the CPU (45 s user). It is pure mathematics
  over ℚ with no dependency on the rest, so it could be cut in two or three modules along its
  import-free chunks if wall time ever depends on it; today it runs in parallel with the main
  chain and does not set the wall time alone.
* `templates_of_rate`, `calls_le` (WalshTemplate): move the arithmetic side goals into small lemmas over
  abstract `q`, `n`; `simp only [pD, pL, pq]` occurs once, in `templates_of_rate` (WalshTemplate.lean),
  and unfolds the parameters on large terms.
* `axisData_dry` and `bluestein_moves` (DFTPrograms): split their `Can.bind` chains into named
  lemmas with explicit bench types, as was done for `freq_moves` (`gather_moves` /
  `spread_moves`), so that each unification stays small.
* Replace `decide` on `ZMod 2` with `fin_cases`/`rfl` tables or precomputed lemmas where it is
  used in hot proofs (not checked whether this helps).
* No per-declaration profile was taken on the final tree; the last one (commit 7fa1528, before
  the merges) is what item 1 of §4 and the hot-spot list of §2 report. Re-profile the current
  tree with `trace.profiler` (threshold 300 ms) before acting on any of the levers above.
* For a verifier that replays the proof terms (nanoda), what matters is the size of the exported
  terms, not the source: heavy `nlinarith`, large `simp` sets and any `decide` on data produce
  large terms. The tree has no certificate data any more, which was what drove replay memory in
  the earlier entries.

## 7. From the earlier trees (still true, kept for the record)

* The earlier entries of this line carried a generated certificate (a 1,291-field word, about two
  million packed digits) that was checked by kernel replays; those modules took most of the build
  time and memory. Route B has no certificate: the unit comes from a proved template family.
  The old analysis of that data (codec limits, cut counts, replay memory) no longer applies and is
  in the git history of this file.
* File merges or splits for their own sake change nothing; only the heavy declarations matter.
* The verifier builds with 4 Lake workers and backs off after an out-of-memory kill; its replay
  runs with 4 threads and restarts with fewer after an out-of-memory kill (board thread #209).

## 8. Exact 1/2

Exact 1/2, an n·√log n bound, is an open problem. A check of this tree found it not feasible from here. It would need three losses removed: template calls ≤ K·√A, an engine that loses only a constant at equal exponents, and the (log log n)² factor in the general-n reduction.

Where the three losses sit in the present tree:
* Template calls. `calls_le` (WalshTemplate) bounds the calls per row by `q^(n+5)` against an arity
  `A ≥ q^(2n)`, so the rate is about `√A` times a factor that grows with `A`; `params_rate_side`
  and `walshTemplate_above_half` therefore reach every exponent above 1/2 only. `QCandidate.Good` asks for the
  strict rate `calls / rows < arity ^ (num/den)`, so no fixed template has exponent exactly 1/2.
* Equal exponents in the engine. `Rule.budget_exists` (EngineCost) needs `z1 < z` strictly: the gap gives the factor
  `(r/m)^(z - z1) < 1` that pays for the lower-order terms. `rippleEngine_of_planUnit`
  (EngineFromTemplates) passes this on as `num/den < zE`.
* The general-n reduction. `axisDFTCost` (DFTPrograms) is `(vandermondeBeats e + 1)` times the axis
  volume times `envelope zE l`, with `e = axisLogBound n` of order `log log n` and
  `vandermondeBeats e = 2·toeplitzBeats e + 7` (ReelKit) of order `e²`; `targetTime` is
  `n (log n)^zE (log log n)²`, and that factor is absorbed only through `zE < p` in
  `targetTime_le_eventually`.
The lower bound `Ω(n·√log n)` is mentioned here without a source; the known source is for the
template side only: `calls / rows ≥ √A` for every correct template, from OpenAI's lower bound.
-/
