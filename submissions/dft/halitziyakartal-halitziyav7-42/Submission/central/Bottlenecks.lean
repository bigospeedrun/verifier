/-!
written with help of ai↓

# Bottlenecks: where build time and memory go, and what could change

This module has no code. It records where the time and memory of building and verifying the
tree go, why, and which changes would cut them. Nothing here is needed for correctness; every
change listed keeps every theorem statement (`Race.bound`, the pinned files, every name). Numbers
are measurements unless marked [EST] (an estimate, to be measured before it is relied on).
Memory is peak RSS in KB divided by 10^6 and written "GB" (so 4,120,000 KB is "4.12 GB", that is
3.84 GiB); verifier numbers are given in GiB, as the verifier reports them.

Reading order: §1 gives this package's numbers, §2 explains why the #8027 word makes the data
modules heavy (the word section), §3 walks the cost of each heavy module, §4 lists the levers
that remain, §5 the ideas that were measured and ruled out, with the reason, and §6 keeps the
history (the earlier trees and what each change bought).

---------------------------------------------------------------------------------------------

## 1. This package (#8027 word 38d2b3a2, layout 0ce3f9e3)

Local build of the 23 modules that the word touches and their dependents: one `lean` process per
module, in dependency order, over the oleans of the previous package; a 15 GiB, 4-core box that
other jobs kept loaded (about 4.5 GB and steady CPU), so wall times run above user times. The
build was done twice from scratch on the same source; the two agree to a few seconds.

| module | user s | wall | peak GB | note |
|---|---|---|---|---|
| `Data/StageRoute/ScalarRun` | 390 / 400 | 6:49 | 3.07 (2.86 GiB) | 100 `decide +kernel` segment checks |
| `Data/StageRoute/LabelRun` | 267 / 266 | 6:12 | 2.21 | 33 segment checks |
| `Data/StageRoute/Events` | 195 / 202 | 3:18 | 4.12 (3.84 GiB) | olean 384.7 MB; no `decide` |
| `Cert/Batch/Word` | 20.2 | 0:22 | 3.08 | |
| `Cert/Stage/Window` | 18.4 | 0:24 | 2.65 | |
| `Cert/Base/Ops` | 15.7 | 0:17 | 3.41 | the largest Mathlib module |
| `Engine/TensorPower` | 16.2 | 0:17 | 2.64 | |
| `Work/U7604/Chain/FourierTB/Main` | 14.8 | 0:11 | 2.98 | |
| `Data/Batch/TplR` | 11.8 | 0:14 | 1.05 | |
| `Cert/Warp/Shear` | 11.0 | 0:13 | 2.66 | |
| `Data/StageRoute/Residual` | 10.0 | 0:12 | 1.55 | 9 checks |
| every other of the 23 | < 10 | | 0.5 to 2.9 | |
| all 23, summed user time | 1023 | | | previous package: 816 s |

Single-decide probes (a scratch file that imports Events and proves one theorem; the import base
alone is 1.01 GB):

| probe | user s | peak GB (GiB) |
|---|---|---|
| `scalarSeg92` (largest row-bits proxy: 1.905·10^9 row bits read, 3,429 adds) | 4.3 | 2.97 (2.77) |
| `scalarSeg89`, `scalarSeg87` (next two) | 4.4 to 4.5 | 2.94 to 2.95 |
| `wrEnd0`, `wrEndF` | 1.8 to 1.9 | 1.82 to 1.83 |
| `labelSeg23` (10,500 events, 1,650 ranks, the most of any label segment) | 7.5 | 2.02 (1.88) |

So one scalar decide sits about 1.9 GB above the import base, and the ScalarRun module (3.07 GB) is
one decide above the base: the 100 decides do not accumulate memory. The largest module of the
package is now Events (meta replay of the word), then `Cert/Base/Ops` (3.41 GB, Mathlib).
`#print axioms` of `Race.bound`, `transform_main`, `convolution_main` and `WHT.wht_main_sharp`:
`propext, Classical.choice, Quot.sound`.

Board verifier (stock harness, this package): Lean phase pass in 2277.3 s, tree peak 8.23 GiB
(largest process 6.69 GiB). Heavy modules there (VmHWM): Events 4.13 GB (214 s), `Cert/Base/Ops`
3.42, `Cert/Batch/Word` 3.09, ScalarRun 3.07 GB (397 s), `FourierTB/Main` 2.97, `Cert/Batch/Park`
2.89, `Reel/Machinery` 2.83, `Engine/Seam` 2.83, LabelRun 2.21 GB (276 s), `Data/Batch/Sched`
1.76 GB (43 s). Export 438,857,291 bytes, 40,651 declarations; the largest are `wrE_evs` 3.11 MB
(2.19 MB in the previous package), `clsLoc_le` 1.32 MB, `Sched.vis` 0.78 MB. nanoda (4 threads)
accepts in 1222.8 s at a peak of 8.24 GiB, no swap (previous package: 835.7 s at the same peak);
with 1 thread 761 s at 2,145 MB. So the word's growth shows in the verifier as time (Lean phase
+555 s against 1722.5 s, nanoda +387 s), not as memory: every peak stays where it was.

---------------------------------------------------------------------------------------------

## 2. The word section: why the #8027 word makes Events and ScalarRun heavy

The word is the list of events that the stage route replays (`Tree_explanation.lean` §6b, §7).
Everything heavy in the tree scales with it, through three different quantities: the number of
events, the information in the coefficients, and the width of the packed scalar rows.

### 2a. What the word carries

| quantity | previous word (#7830) | #8027 word | ratio |
|---|---|---|---|
| events | about 239,000 | 341,925 | 1.43 |
| events that carry a coefficient | | 323,584 | |
| distinct coefficient pairs `(num, den)` | 4,394 | 51,013 | 11.6 |
| pairs that occur exactly once | | 36,117 | |
| distinct denominators / numerators | | 1,587 / 32,227 | |
| largest numerator, denominator | below `2^57`, `2^53` (`Kn`, `Kd`) | | |
| packed digits of the `decode_events` strings | 818,583 | 2,005,607 | 2.45 |
| `Events.lean` bytes | 828,896 | 2,016,152 | 2.43 |
| scalar row width | 1290 digits × 179 bits | 1292 digits × 215 bits | 1.20 |

The saving of the stated exponent is what the #8027 word buys: its stage price
(`3809·φ1 + 792·φ2 + 480·φ3 + 226·φ4 + 314·φ5 + 41·φ6 + 10·φ7 + 2·φ8`) is what lets the rate
point reach `u = 194924072327/(5·10^13)`. The cost is that its gate coefficients are many,
different and large: the information is real, not an encoding waste.

### 2b. Where the 2.0 million packed digits go

The event codec (`decode_events`, `Cert/Scalar/Decode.lean`) codes each event's kind and frame,
its registers (by position among the 15 most recent registers, or a short difference) and its
coefficient (by index into a growing dictionary of the pairs seen so far: indices 1 to 14 directly,
later indices by an Elias-gamma code, and new pairs raw). Its own cost model reproduces the file
(2,004,896 digits against the real 2,005,607):

| part | share | digits |
|---|---|---|
| new coefficient pairs (raw `num`, `den`) | 35.6 % | 714 K |
| references to pairs at dictionary index ≥ 15 | 32.9 % | 660 K |
| registers | 21.7 % | 435 K |
| references to pairs at index < 15 | 5.3 % | 107 K |
| kind and frame | 4.4 % | 89 K |

Three quarters of the file is coefficients. The 36,117 singleton pairs alone are 1.61 Mbit of raw
bits (about 485 K digits), and no coding of a pair stream can avoid sending them: an ideal static
order-0 code of the pair stream plus a raw dictionary needs at least about 1.53 M digits for the
coefficients, about what the codec spends today (about 1.48 M). So the ×2.4 of the source is the
word's information content, and the codec is already near its floor.

### 2c. Why the olean grows less than the source, and what it is made of

Each decoded event becomes its own `WEv` term, added by `addDecl` inside chunk definitions
`ev<s>_<j>` of 150 events. The olean holds those terms, not the decimal strings: 384.7 MB for
341,925 events is about 1.1 KB per event, the same per-event size as before (254 MB for the
previous word, 1.07 KB per event). A coefficient is two `Nat` literals in an `Expr` either way, so
the extra coefficient information changes the olean little; the event count does. That is why the
olean grew ×1.5 while the source grew ×2.4, and why the lever for the olean (§4a) is the shape of
the event terms, not the codec. The rest of the olean is the generated states: 101 scalar
checkpoints with 9,597 leaf constants (16.4 MB of leaf literals, against 9.2 MB before; the largest
checkpoint changes 669 leaves, 1.80 MB) and 34 label states.

### 2d. Why the scalar rows are wider, and how the cut count follows

The scalar checker packs a register row into one number of `n` digits base `X` and adds rows with
GMP, so it must never let a digit carry. The no-carry lemma needs
`Kd·2H + Kd + Kn·H ≤ X`: denominators below `Kd = 2^53`, numerators below `Kn = 2^57`, and row
entries inside the offset digit `H = 2^157` (the entries are integers scaled by the common
denominator `D ≈ 2^117`, and grow in the middle of the word). That gives `X = 2^215` against `2^179`
before. The digit count follows the keys: 1291 port and slot registers (`2·200 + 891`) plus the
ghost digit, 1292 digits; the 733 copy registers start empty and need no key.

The cost of one segment check is set by the row bits it reads, about (adds in the segment) × (row
width). Both grew: adds ×1.43 and width ×1.20. With the previous cut count (48 segments) the
largest segment would read 3.97·10^9 row bits (1.72×) and 7,150 adds. The cut count was raised to
C = 100 (`gen_scalar_checkpoints … 100`), which brings the largest segment to 1.905·10^9 row bits
(0.82× the previous package's largest) and 3,429 adds, and keeps every decide under 2.8 GiB. A cut
count chosen by adds alone (C = 82) would match the previous row-bits peak (1.00×) with 18 fewer
checkpoints.

### 2e. Events time

Events does no `decide`. Its 195 to 202 s are: decoding 228 strings into 341,925 terms and their
`addDecl`, and two meta replays of the whole word at elaboration time, `gen_scalar_checkpoints`
(packed rows of 1292 × 215 bits, 100 cuts) and `gen_label_states` (33 cuts). Both replays grow
with the events and the scalar one also with the row width, so Events grew ×1.9 in time against
×1.43 in events. Its 4.12 GB peak is the decoded word plus the checkpoint leaves held at once.

---------------------------------------------------------------------------------------------

## 3. The heavy modules, one by one

* **ScalarRun (390 to 400 s, 3.07 GB).** 100 segment checks `scalarSeg1..100`, each replaying its
  events from checkpoint `wrS(i-1)` and comparing with `wrS i` (`ScalarCheck.checkSeg`), plus
  `wrEnd0`, `wrEndF`, `wrPar`; `scalar_ref` glues them through `wrE_evs` without unfolding the
  chunk lists. About 1.14 ms per event (1.12 ms in the previous package, rows of 1290 × 179 bits). The time is GMP work on rows
  of about 278 Kbit, plus the per-add digit-overflow test (`goodB`: one `&&&` with `MASK` and one
  comparison with `XN`; earlier profiles put it at about half the scalar kernel time) and the fixed
  per-decide cost of forcing and comparing the start and end checkpoints.
* **LabelRun (267 s, 2.21 GB).** 33 segment checks `labelSeg0..32` of at most 10,500 events, about
  0.78 ms per event; linear in the events. `set_option Elab.async false` makes them run one after
  another in one process.
* **Events (195 to 202 s, 4.12 GB, olean 385 MB).** §2c and §2e.
* **Residual (10 s), TplR (12 s), Sched (5 s), Rate (6.5 s), Word (20 s), Ops (16 s).** The other
  kernel replays are small. Ops and Word are set by the Mathlib floor (2.5 to 3.4 GB) more than by
  their checks.
* **The Mathlib floor.** Any module whose closure reaches `Core.lean`'s
  `Mathlib.Analysis.SpecialFunctions.Log.Base` starts at about 2.5 GB; the core-only checker and
  data modules start at about 0.5 GB (`Cert/Label/Trie` 0.54 GB). The pinned files fix that floor
  for everything downstream of `Goal.lean`. The heavy work stays in the 10 core-only modules,
  where a Mathlib import would add about 2 GB to each heavy module.

---------------------------------------------------------------------------------------------

## 4. Levers that remain

### 4a. Compact event terms (the lever on the olean, the export and nanoda)

Keep `WEv`, `evs`, every segment list and every statement. Ship each 150-event chunk not as 150
`WEv` terms but as one fixed-width natural number: the events' fields (kind, frame, registers, an
index into one shared coefficient-pair table) packed side by side, and define the chunk as
`unpackChunk N`, a recursor-only decoder by `Nat.div` / `Nat.mod` (GMP in the kernel). The pair
table is one list of the 51,013 pairs. The decoder in `Cert/Scalar/Decode.lean` would emit these
numbers instead of terms; the checkers are unchanged, and each `decide` unfolds `unpackChunk` for
the events it reads.
[EST] Events.olean 385 MB → 20 to 40 MB; export and the nanoda parse base about 300 MB smaller,
a shorter nanoda parse and replay (its peak, 8.24 GiB, did not grow with the word, so the gain
is time); Events elaboration much faster (no 341,925-term `addDecl`); each LabelRun
and ScalarRun decide +5 to 15 % for the unpacking, small in memory. Source about the same size.
A redesign of the decoder output and the chunk definitions with a full rebuild and a board run:
about 0.5 to 1 day. This is the one lever that answers the word's olean cost (§2c).

### 4b. Parallel replay modules

The checkpoints `wrS i` and label states `labS i` already exist in Events, so LabelRun's 33 and
ScalarRun's 100 theorems can be split into several modules, each importing Events only, with the
glue (`label_run`, `scalar_ref`) moved into `Cert/StageRoute.lean`. The verifier builds each module
as its own chain, so the split turns the two longest serial chains into parallel ones. Adds 4 to 6
files; within the cap of 42 they must be offset by merges elsewhere (for example the small data
modules). [EST] LabelRun and ScalarRun chain wall time halved or better, per-module peak unchanged
(one decide above the base).

### 4c. A denominator dictionary in the codec (source size only)

Code a new pair's denominator as a move-to-front index into the 1,587 denominators seen, then the
numerator. [EST] coefficient bits −14 % (4.92 → 4.21 Mbit), Events.lean about −210 K digits
(−10 %). The decoded terms are the same, so no olean, memory or verify time changes. Three codecs
must agree (the meta decoder, the encoder, the port used to replay it), so it is worth it only if
the source size itself matters (a file or token cap).

### 4d. Small knobs

* C = 82 instead of 100: 18 fewer start-and-end comparisons per check of the whole state; per-decide
  memory about ×1.2 (back to the previous package's peak). Only Events and ScalarRun rebuild.
  [EST] ScalarRun −5 to −10 %.
* Column split of the scalar check (`Spec.Step` is pointwise in the key, so a run holds iff it
  holds on every key group): per-decide memory ÷G on the state, but every group replays every
  event, so time rises. A memory lever only, for a board memory problem should one appear.
* Fused label and scalar replay (one fold with a paired state): saves one traversal and decode of
  the events; the scalar bignum work dominates. [EST] 5 to 15 % of the two modules, at high risk
  (two checkers merged), and it conflicts with 4b.
* Mathlib trims (each small and to be measured): `Main` imports
  `Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics`; `Reel/Machinery` imports
  `Mathlib.Data.Nat.Choose.Factorization` only for the prime count; `Engine/ClassSetup` imports
  `Mathlib.Tactic.Ring`, likely already in its closure.

---------------------------------------------------------------------------------------------

## 5. Measured and ruled out

| idea | what was measured or shown | why it is out |
|---|---|---|
| a coefficient rescale or renormalisation | 51,013 distinct pairs, 36,117 of them used once | a common rescale cannot merge distinct rationals; only a different word reduces the information |
| move-to-front for pair references | coefficient bits 4.92 → 4.82 Mbit (−2 %) | too small |
| any better pair codec | the order-0 floor is about 1.53 M digits, today about 1.48 M | the codec is already at the information content (§2b) |
| full in-kernel ANS decode of the strings | needs an adaptive context map inside the kernel | [EST] ×2 to 5 decide time; 4a gets the olean gain with a trivial decoder |
| derive the scalar facts from the label run | `checkGate` and `Moves` read registers and GF(2) frames only, never `Co` | the scalar check is the only place the gate coefficients are certified, and `CertValid.clean` needs the exact shear (`esMap_shear`), not a shear up to a free factor |
| per-port or per-column factorisation of the scalar check | symbolic row supports turn global after about 250 K events: the largest row touches 1092 of 1291 keys | the word's final rows are sparse only by cancellation, so there is no block structure to split on |
| sparse rows instead of packed rows | coefficient operations would be 0.118× | a kernel list entry costs tens of `whnf` steps, a 215-bit GMP digit a few words, so the factor 8.5 does not pay for the list overhead (an earlier sparse re-synthesis of the checkpoints also failed) |
| skipping the overflow test between checkpoints | one step from good operands cannot overflow, but its result may leave the digit range | skipping `k` tests needs about 57 more bits of headroom per skipped step, a wider `X` that costs what it saves |
| a smaller cut count for leaf size | C = 82: 9,463 leaves against 9,597 (−1.4 %) | negligible size gain for ×1.2 per-decide memory |
| file merges or splits for their own sake | the heavy modules stay the same | ≈ 0 s |
| heartbeat settings | a limit costs no time | no effect |
| a smaller supplier word | restores the old times | loses the saving |

---------------------------------------------------------------------------------------------

## 6. History: earlier trees and what each change bought

### 6a. tree52 (W7786 word, 238,628 events) and its board run

Board verifier, stock harness: Lean phase 1507.0 s at 10.2 GiB; audit 2.3 s; nanoda killed out of
memory at 13.2 GiB on a 16 GB box (the harness fell back to the Lean kernel, which accepted). The
heavy local modules then: ScalarRun 248.6 s at 9.3 GB (12 segments over rows of 2025 digits, about
45 KB each; the memory came from `scalar_ref` rewriting the whole event list), LabelRun 208.9 s,
Events 146.4 s at 4.0 GB (olean 370.4 MB), Sched 114.4 s at 4.5 GB (nested `List.getD` over the
visit and occupancy tables). The verifier time had doubled against the earlier W7604 word (76,666
events, 776 s), because it pays for the word twice (elaborating the replays and replaying the
exported environment) and builds the chains serially.

### 6b. The changes and what they bought

* **S7 (checkpoint cuts and shared leaves).** `gen_scalar_checkpoints` takes a cut count and makes
  a new leaf constant only for rows a segment changed, and it emits `wrE_evs`, so `scalar_ref` no
  longer rewrites the event list. ScalarRun memory 9.3 GB → under 3 GB together with T1.
* **T1 (copy keys removed).** The copy registers start with empty rows (`idCK`), so a row has a
  digit per port and slot register only: 1290 digits instead of 2025.
* **R2 (linear schedule checks).** Single linear walks with recursor helpers, and occupancy and
  visits derived from one bitmap check `distinct_ok` by pigeonhole: Sched 114.4 s, 4.5 GB → 6.5 s,
  1.8 GB, and the occupancy table is gone.
* **§7c (dead definitions removed).** The unused block `wsumK_eq` / `wEq_apply` / `rcost_wsumK` of `Cert/StageRoute.lean` and the
  per-rank count facts were replaced by `rankBound` / `rankCounts`; Residual has 9 checks.

### 6c. The previous package (pkg-rel: tree52 + S7, R2, T1; #7830 word 7660985e)

Local: Events 101 s, 3.0 GB, olean 254.1 MB; ScalarRun 267 s, 2.9 GB (48 checks); LabelRun 205 s,
2.1 GB (23 checks); `Cert/Base/Ops` 18.9 s, 3.3 GB; 22 modules 816 s summed. The same tree before T1
passed the board verifier: Lean phase 1722.5 s at 8.23 GiB; nanoda with 4 threads accepted in
872 s at 8.24 GiB (1 thread: 541 s, 2.2 GB); export 314.8 MB, 39,251 declarations, the largest
`wrE_evs` at 2.19 MB.
-/
