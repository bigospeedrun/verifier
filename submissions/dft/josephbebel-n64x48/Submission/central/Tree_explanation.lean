/-!
written with help of ai↓

# Tree explanation: the flow of the proof, from `Race.bound` down to the data

Updated for the native 64 x 48-call submission (Joseph Bebel, prepared with Claude (Anthropic) and
OpenAI Codex; see Submission.lean and Credits.lean): the numbers below describe this tree. The text
is Halit Ziya KARTAL's, from PR 209 (bigospeedrun/verifier #209), with only the numbers and the
parts on the native 64 word and the key-split scalar check changed.

This module has no code. It follows one thread: what `Race.bound` promises, which theorem
delivers each part of the promise, and why each stage of the tree exists (what problem it
solves for the stage above it). Paths are relative to `Submission/`. The files one by one are in
`Code_explanations.lean`; build cost is in `Bottlenecks.lean`; who the ideas come from is in
`Credits.lean`. Every name below is a name of this tree, so a search for it lands on its
definition.

Reading order: §1 says what is promised, §2 gives the whole flow on one page, §3 to §7 walk it
stage by stage (each stage: what it receives, what it proves, why it is there), §8 shows how the
39 files are cut and why, §9 lists the numbers, §10 the trust boundary.

---------------------------------------------------------------------------------------------

## 1. The promise

`Race.bound` (`Submission.lean`, the only theorem there) states

    ∃ order solve W, DFTProgram order solve W ∧
      W =O(n (log n)^(1 - 1957647056737859/500000000000000000))

`DFTProgram` is OpenAI's definition, in the pinned file `OAI/Computability/FourierTransform/Goal.lean`
(kept byte-identical). For every length `n > 0`:

* `order` is run on `n` alone and returns a number `d` with `0 < d < 1024 n^3`, polynomially
  bounded work and peak, and a valid run;
* `solve` is then run on `(n, root d, x)`, where `root d = exp(2πi/d)` is handed to it as an
  input (the root is not part of the definition of `DFTProgram`; only `d` is), and must return
  `dft n x` exactly, with a valid run and polynomial peak;
* the total work `order + 1 + solve` is at most `W n`.

The model is `OAI/Computability/FourierTransform/RAM.lean` (pinned). Two of its rules shape the
whole tree:

* values are *painted*: the input vector is `left`, constants such as the root are `scalar`.
  `scale` multiplies a scalar by any value, `add`/`sub` combine values of one paint, and the only
  product of two non-scalar values is `cross`, which is allowed only in convolution programs
  (`Prog true`). So a DFT program is a linear straight-line computation in the data, with scalar
  coefficients; it can never multiply two data values.
* work is counted per constructor (`Code.run`), and index arithmetic (`NOp` on words) costs the
  same as complex arithmetic, so every table, layout and loop counter in the proof is paid for.

`Race.bound` itself is four lines: it takes `transform_mainTB19 : DFTGoalSharp`
(`Work/U7604/Chain/FourierTB/Main.lean`) and rewrites `decimalTimeTB19` into the literal
exponent, using `statedSavingTB19 = 1957647056737859/(5·10^17)`.

---------------------------------------------------------------------------------------------

## 2. The whole flow on one page

```
Race.bound                                            Submission.lean
 └ transform_mainTB19 : DFTGoalSharp                  FourierTB/Main
    └ transform_main_order_sharp                      (order = workModulus, < 8 n^3)
       ├ dft_program rippleEngine_base                FRONT END (§3): any engine ⇒ a DFT program
       │   ├ assemble_program                         order program, one polynomial cap
       │   └ dft_solve_program → Nick.dft_moves → LenCtx.dft_moves
       │       ├ small n: Dry.naive_freq              (finitely many lengths, naive DFT)
       │       └ large n: dft_moves_large → BluesteinCtx.bluestein_moves
       │           └ modulusFreq_moves_of_axes → AxisReels.freq_moves   (CRT: N = ∏ axes)
       │               └ AxisReels.kron_moves / run_moves               (all axes in lockstep)
       │                   └ AxisStroke.beat_moves = perm_moves ; mix_moves
       │                       └ BlockCover.patchRipple_moves → blockRipple_moves
       │                           └ hE : RippleEngine z                (THE SEAM, §4)
       └ timeBounds_baseEngineExp                     TIMING (§3e): exponent ⇒ O-bounds
rippleEngine_base : RippleEngine baseEngineExp        Transform/EngineUse.lean
 ├ Batch48.rawCert_exists_B48                         CERTIFICATE (§6): one finite unit
 └ TensorPower.ripple_program_of_rawCert              ENGINE (§5): unit ⇒ fast ripple
     └ ripple_program_of_hist → _of_hist_pow (12800 factors)
         ├ TensorMoment.BaseRate.strict_moment        Data/BaseUnit/Rate.lean (the rate)
         └ BundledUnit.ripple_program                 pow, pad, cut, rule_of_moment
             └ BlockEngine.ripple_program             Engine/Seam.lean
                 ├ Rule.jobCost_bound                 cost recurrence ⇒ O(2^n (n+1)^z)
                 ├ EngRecursion.ripple_split_program
                 └ sim_program_of_port ← port_top_can ← job_body (ClassBody, Recursion, ClassSetup)
rawCert_exists_B48                                    Cert/Batch/Word.lean
 └ raw_B48: 48 calls (run_spec), prep/end/shift moves, counting (pay_ok, tgt_ok48)
     ├ call_spec → stage_op' → StageRoute.invariant   the certified stage route (§6b)
     │   └ CertValid: label_run, scalar_ref, ends_ok, … all kernel replays (§7)
     └ templates: TplA/TplR acts_diag → ctrl_diag → seg_realised   (§6c)
```

The tree is therefore three programs stacked on one finite object:

1. a *front end* that turns "a ripple on `k` bits costs `2^k (k+1)^z`" into "a DFT of length `n`
   costs `O(n (log n)^z (log log n)^2)`";
2. an *engine* that turns "a finite unit whose block moments beat its target moments" into "a
   ripple on `k` bits costs `O(2^k (k+1)^z)`";
3. a *certificate* that builds one such unit and proves its two rank histograms, by kernel
   replays of generated data.

The seam between 1 and 2 is the single proposition `RippleEngine z`
(`Transform/EngineUse.lean`, OpenAI's `hills_program` statement with `envelope z k = ⌈(k+1)^z⌉`).
The front end never sees the certificate, and the certificate never sees the DFT. That is why a
new unit or a new word changes only the certificate side and two exponent literals.

---------------------------------------------------------------------------------------------

## 3. The front end: from a fast ripple to a fast DFT

**What it receives:** `hE : RippleEngine z` for some `0 ≤ z ≤ 1`: for every batch of inputs, a
RAM program computing `ripple k v = kernel (Fin k) *ᵥ v` in work `2^k · envelope z k`. Here
`kernel = digitProd littleC` is the `k`-fold tensor power of the 2×2 matrix
`littleC = [[ca, cb], [cb, ca]]`, `ca = (1+i)/2`, `cb = (1-i)/2` (`Reel/Machinery.lean`).
Done naively the ripple costs `2^k (2k+1)` (`ripple_naive_can`, `Ripple/RoleMoves.lean`).

**What it proves:** `dft_program_of_engine` / `dft_program` (`Main.lean`): a `DFTProgram` whose
work is `totalCost`, and `totalCost_isBigO`: `totalCost = O(n (log n)^z (log log n)^2)`
(`targetTime`, `Main.lean`).

**Why it is built the way it is.** A DFT program may only take linear combinations with scalar
coefficients (§1). The front end therefore rewrites the DFT, step by step, into a long product
of very simple linear maps, until the only expensive map left is the ripple:

(a) *The length.* `Bluestein` (`Algebra/DFTIdentities.lean`, `bluestein_freq`): a DFT of length
`n` is a cyclic convolution of length `N ≥ 2n` between chirps `z^(i²)`. `N` is chosen as
`(modulusAxes n).vol`, a product of distinct odd primes and one power of two with
`2n ≤ N < 4n` (`modulusAxes_spec`, `Reel/Machinery.lean`). Why: a product of coprime
factors lets the CRT split one DFT of length `N` into a tensor product of small DFTs
(`crt_freq`, `CoprimeAxes`), one per *axis*. There are at most `axisBudget n = log₂(2n) + 1`
axes, each of size at most `2^axisLogBound n = O((log n)^2)` (primes are searched below
`(16(k+4))^2`; enough exist by a central-binomial count).

(b) *The order and the root.* `workModulus n = 2n · N · 2^axisLogBound n` for large `n`, and `n`
itself for the finitely many small `n` (`Machinery.lean`), with
`workModulus n < 8 n^3` (`receipt_bound`), well inside `1024 n^3`. Why a product: `solve` gets
only `root d`; because `n`, `2n`, `N` and every axis size divide `d`, all the roots it needs
are powers of the one root it is handed, computed by fast powering (`shiftP`, `halveP`,
`LenCtx`, `Main.lean`).

(c) *One axis.* Each axis DFT is a Vandermonde matrix on a root. It is factored as
`L · D⁻¹ · Lᵀ` with Toeplitz factors (`rootVandermonde_factor`, `DFTIdentities.lean`) and
written as a *reel* (`vandermondeReel`): a list of *strokes*, each a permutation with diagonal
scaling (`ix`, `dye`) followed by `littleC` on pairs of positions (`partner`; `Stroke.applyC`,
`Machinery.lean`). It has `vandermondeBeats e = 2·chorus e + 7 = O((e+1)^2)` strokes with
`e = axisLogBound n = O(log log n)` (`beats_ballad`). Why only `littleC`: the reel kit builds
everything (add-a-scaled-copy, radix-2 FFT, cyclic convolution, Toeplitz products) out of
monomial steps and `littleC` pairs, so that step (d) below sees only `littleC`.

(d) *All axes at once.* The axes run in lockstep, beat by beat (`axisRun_eq_kron`). On the tensor
product, one beat is a monomial step on all `N` entries (cost `N`) and a mixing step that is a
tensor product of `littleC` pairs across the axes. Such a product of `2×2` blocks, regrouped into
power-of-two blocks (`strokeBlocks`, `PowBlockCover`, `mosaic_quilt`), is on each block exactly a
ripple on at most `l` bits (`mix_eq_patchRipple`, `Transform/ReelCompile.lean`). This is
where `hE` is used (`blockRipple_moves`, `Transform/EngineUse.lean`): one beat costs
`N · envelope z l`, and one axis DFT costs
`axisDFTCost = (vandermondeBeats + 1) · N · envelope z l` (`Main.lean`). With `l = O(log n)` and
`O((log log n)^2)` beats this is `O(N (log n)^z (log log n)^2)`.

(e) *The assembly and the timing.* The RAM programs are built with the judgment calculus of
`Compiler/Judgment.lean` and `Compiler/Layout.lean` (`Can`, `Moves`, `Dry`, with polynomial peak
bounds), and the reels are turned into RAM data by `Transform/ReelCompile.lean` (`publish`:
every reel up to `vandermondeReel` is engraved by a polynomial program). `assemble_program`
(`Main.lean`) joins the order program and the solve program under one cap
`(n+2)^c`. `timeBounds_of_exp` (`Main.lean`) then turns `targetTime zE` into the three
bounds of `TimeBoundsSharp` (paper exponent `theta`, the stated decimal exponent, `o(n log n)`).
It needs `zE < theta` and `zE < decimalExponentTB19`: the strict gap absorbs the
`(log log n)^2` factor (`targetTime_le_eventually`).

The convolution theorems (`conv_program`, `convolution_main_sharp`) reuse the same chain: pad to
`2n-1`, two forward DFTs, one `cross` product, one inverse DFT (`conv_solve_program`). The
Walsh-Hadamard theorem (`wht_main`, first section of `Main.lean`) uses the same engine through
`wal_ripple`: the Walsh matrix is the kernel conjugated by `diag(lum)`, up to `(1-i)^k`.

---------------------------------------------------------------------------------------------

## 4. The seam and the three exponents

`rippleEngine_base : RippleEngine baseEngineExp` (`Transform/EngineUse.lean`) is two lines: it
unpacks `Batch48.rawCert_exists_B48` and feeds it to `TensorPower.ripple_program_of_rawCert`.

Three numbers appear, each strictly between its neighbours, and each gap pays for one loss:

| number | name, file | what the gap after it pays for |
|---|---|---|
| `0.003915294113475719 = 3915294113475719/10^18` | rate point `u`, `Data/BaseUnit/Rate.lean` | `jobCost_bound` needs `z1 < z` strictly |
| `0.0039152941134757185 = 7830588226951437/(2·10^18)` | `1 - baseEngineExp`, `Transform/EngineUse.lean` | `timeBounds_of_exp` needs `zE < decimalExponentTB19`, absorbing `(log log n)^2` |
| `0.003915294113475718 = 1957647056737859/(5·10^17)` | `statedSavingTB19`, `Main.lean`; `Race.bound` | the statement |

`baseEngineExp_lt_theta` (`Main.lean`) also checks `baseEngineExp < theta < 1`, so the
paper-exponent bound holds too.

---------------------------------------------------------------------------------------------

## 5. The engine: from a finite unit to a fast ripple

**What it receives** (`ripple_program_of_rawCert`, `Engine/TensorPower.lean`): a word `wd` of
moves on a finite binary space `α` with `|α| = 137`, roles `ρ`, live roles `e : σ → ρ`, and for
each live role a target family `tz l` of `tr l` independent vectors, such that

* `GLiveKernelM e (fun l => blockMat (tz l)) wd` (`Engine/Moves.lean`): on every input that is
  zero off the live roles, the word leaves `blockMat (tz l)` (a ripple on `tr l` bits along the
  span of `tz l`) of the input on live role `e l`;
* the word is proper (every block has rank `1 ≤ r < 137`);
* its block histogram is `G · blockHist` and its target histogram is `G · targetHist`
  (the lists in `Data/BaseUnit/Rate.lean`, `G ≥ 1` any factor).

**What a move is** (`Engine/Moves.lean`). Free moves cost nothing in the engine's
account: role-local matrices with rational entries (`localM`, `localG` with a Gaussian part),
shifts, linear permutations (`perm`) and phases (`phase`). A *block* `block l r z` is a ripple
of rank `r` along `r` independent directions on role `l`; it is the only paid move, and the
engine pays it by a recursive call on `r` bits. So a unit converts paid blocks of small ranks
into targets of larger ranks.

**Why a tensor power.** The engine recursion (below) needs two things that a raw unit does not
give: *separation* (every paid rank strictly below every target rank, so the recursion goes
down) and a *moment rate* `Σ paid^z1 ≤ Σ target^z1` for some `z1 < 1`. Tensoring a unit with
itself multiplies both histograms (`BundledUnit.prod`, `tens`, `mom_tpow`: moments multiply),
so the ratio of moments is raised to the power `v`. After `v` factors, targets below
`L = 13^v` are padded up to `L` by extra paid blocks of rank `L - K` (`padTargets_exists`, `comp`)
and paid blocks above `J = 12^v` are cut into pieces of at most `J` (`cut_blocks_exists`,
`splitAll`). That gives separation (`J < L`), and `strictify` (`Engine/Moves.lean`) shows that
the padding and cutting cost less than the gain as soon as
`α^v + 2γ^v + 2δ^v ≤ 1`. `BundledUnit.pow n` is the `(n+1)`-fold product (`pow 0 = A`,
`Engine/TensorPower.lean`), so `ripple_program_of_hist` calls `_of_hist_pow` with
`n = 12799`: 12800 factors. `strict_moment` (`Data/BaseUnit/Rate.lean`) proves the inequality
for this `v` at `t = 1 - u`, with every `r^(1-u)` bounded by an integer decimal-root certificate
(`qCert`, `qWalk`) and the final comparison
`(10097·SA)^12800 + 4·e^12800 ≤ (10097·SB)^12800` decided by the kernel. The factor `G` cancels
(`mom_nsmul`).

**The recursion** (`Engine/ClassSetup.lean`, `ClassBody.lean`, `Recursion.lean`, `Seam.lean`).
`BlockEngine.ripple_program` (`Seam.lean`) builds, for every `k`, a RAM program for
`ripple k`. A ripple on `n` bits is split into its low part (a *class job*) and leftover
ripples on fewer bits (`hlow`, `hhigh`). A class job loads many independent jobs onto the
unit's data, runs the word move by move (free moves in place; each block move becomes a child
class job one level lower, or an exit job), and unloads. All jobs are encoded as one RAM type
(`EngJob`: `top n B v` or `cls n h μ o BS J sup`) and the whole recursion is one open body
(`job_body`) closed by bounded `descend` (`EngRecursion.closed`, `closed_inv`). Why one body: the
RAM model has exactly one recursion construct, with one port.

**The cost** (`Seam.lean`). The abstract shape of the recursion is a `Rule` (target ranks `tq`,
paid ranks `rk`, `rmax < kmin`), its cost the least solution `jobCost` of `JobCostRec`.
`Rule.jobCost_bound` (`Seam.lean`): if `MomentRate z1 1` and `z1 < z ≤ 1`, then
`jobCost n ≤ C · 2^n (n+1)^z`. The proof is a potential argument: sources of the call tree have
size in `(n/m, n]` (Lemma C, `src_size`), the moment `Phi` does not grow down the tree
(`phi_out_le`, `phi_exT_le`), exits carry an arbitrarily small share of it for large `n`
(`exits_small`; this is what removes the extra log factor), and `recurrence_bound` (Lemma A)
with `eta_step` closes the induction. `RealisesRule` ties a concrete `BlockEngine` to its rule;
`TensorPower.rule_of_moment` produces both from the padded, cut tensor power.

---------------------------------------------------------------------------------------------

## 6. The certificate: the B48 unit

`rawCert_exists_B48` (`Cert/Batch/Word.lean`) builds the unit on
`Lb = LC (Fin 16) (Fin 9) 0`, the 137-dimensional binary space `Fin 9 ⊕ (Fin 16 × (Fin 9 ∖ {0}))`:
a 9-dimensional core plus 16 banks of 8 (`Cert/Base/Ops.lean`, `card_LC137`). Every role
exists once per element of the gauge `Gm = Orth Lb` (all orthogonal 137×137 matrices over
`F₂`), so `G = |Gm|`. Why gauges: each call's frames are the relabelled frames of one stage
route (`BBC_rho`, `Word.lean`), so one certified route serves every call; the price is the
common factor `|Gm|`, which cancels in the moment inequality.

### 6a. The shape of the unit

* 312 *roots*: 120 of kind A (template `TplA`, 34 registers) and 192 of kind R (template `TplR`,
  30 registers). They are the main live roles.
* 48 *calls* `τ < 48`. Call `τ` runs the stage route at sub-stage `kτ τ = τ % 16 + 1 ∈ 1..16`
  (`Word.lean`; `Data/Batch/Sched.lean`). Each call's 891 helper slots are live roles too
  (`KB = KR ⊕ (Fin 48 × Fin 891)`).
* A *schedule* (`Data/Batch/Sched.lean`): each root visits 16 calls, at one port each; each call
  has 104 ports. Its 7 kernel-decided facts are shape, range, chronology, slots, inverse slots,
  port kinds and distinct visit codes. Occupancy and visits (`occ_P`, `vis_P`) are derived, not
  decided: the 312·16 = 4992 codes `call·104 + port` are distinct and below 48·104 = 4992, so by
  pigeonhole every port of every call is visited exactly once, and the owner of a port is the
  inverse of the visit map (no occupancy table is shipped).
* Between visits each root runs its template's local events: free row moves, swaps, monomial
  phases and *bank masks* (frames on unions of 8-dimensional banks, the template's paid blocks).
* At the end a root holds `q^phase · Pf(bank set)`; one free shift turns it into its target
  block of rank `1 + 8·(number of banks)` (`root_fin`, `tgt_eq`). Each helper slot ends at its
  stage residual and is padded to its target rank (`ex_Z`, `HostPad.host_pad`).

The counting is two kernel facts (`Word.lean`):
`pay_ok`: `blockHist = 48 · (stage price) + 120 · PT_A + 192 · PT_R`, and
`tgt_ok48`: `targetHist = 120 · TT_A + 192 · TT_R + 48 · schedRes` (so 52,608 live roles per gauge
copy: `120·34 + 192·30 + 48·891`).

### 6b. The stage route (one call)

`StageRoute.invariant : StageInvariant (Fin 9) (Fin 200) (Fin 891) (Fin 1520)`
(`Cert/StageRoute.lean`). In words: for every window (a way of placing the 9-bit labels in a
larger space), there is a route from the stage's entry frames to its exit frames that acts on
the 200 ports as the shear `(X, Y) ↦ (X + αY, βX + (1+αβ)Y)` with `(α, β)` = `(0, 1)` on the 96
`F` ports, `(-1, 0)` on the 96 hosted `Bk` ports and `(-1, 1/2)` on the 8 `M` ports
(`portShears`), keeps the slots, clears the 1520 scratch copies, and pays exactly
`price φ = 2·φ8 + 10·φ7 + 41·φ6 + 314·φ5 + 226·φ4 + 484·φ3 + 848·φ2 + 3685·φ1`
(`invariant_price`). Why a shear: two shears with matching `(α, β)` compose with the template
moves to a diagonal on each root (§6c), which is what lets a root's data come back clean.

It is proved from `cert_valid : CertValid cert abT` (`StageRoute.lean`), a record of checker
facts about the native 64 word 27f6a6b9 (derived from the #8027 word 38d2b3a2): the label run (`label_run`, the 33 label segments glued), the scalar
run (`scalar_ref`), the end conditions (`ends_ok`), erased identity start rows (identity on the
1291 = 2·200 + 891 port and slot registers, empty rows on the 1520 copy registers: `idCK`),
shear end rows and their freeness (`id0_ok`, `shear_ok`, `frF_ok`). `CertValid.clean` / `invAB` / `invCtr`
(`Cert/Warp/Shear.lean`) turn these facts into routes. `hent` gives each slot's
residual `9 - dim (ent q) = schedRes q`, the helper targets of §6a.

### 6c. The templates and the call machinery

The templates are checked by a third checker, the *control check*: `acts_diag` (`Data/Batch/TplR.lean`,
once for `TplA`, once for `TplR`) says, in any `Lean.Grind.CommRing` with `q⁴ = 1`, `L² = q²` and
`ι² = -1`, that the template's event list (with the HOST visits lowered to events) multiplies
every register by one monomial (`diag`). `Cert/Batch/Park.lean` turns this into Mathlib
semantics (`ctrl_diag`) and realises every template event as gated park moves with its block
cost (`ev_realised`, `seg_realised`). `Word.lean` then defines one call (`cOp`: pull the visiting
roots' HOST registers onto the ports, run `stOp'` at sub-stage `kτ`, pull back), proves its
specification (`call_spec`), composes the 48 calls (`run_spec`) and adds the prep, end and shift
moves (`prepB`, `endB`, `shiftB`) to get `raw_B48`.

---------------------------------------------------------------------------------------------

## 7. The data and the kernel replays

Every large fact of §6 has the same three-part shape, and the parts sit in different files on
purpose:

1. a *specification* that is easy to read and to use (a `Prop` over `Nat → Nat → Int` states,
   frames, or a ring);
2. a *checker*: a `Bool` function written with raw recursors and `Nat` operations, so that the
   kernel (whose `Nat` is GMP-backed) evaluates it fast under `decide +kernel`;
3. a *soundness theorem*: checker `= true` implies the specification.

The data (event lists, frame tables, rows, schedules) is shipped as packed decimal strings and
expanded at elaboration time by commands (`decode_events`, `decode_frames`, … in
`Cert/Scalar/Decode.lean`; `bpack_*` in `Data/Batch/Pack.lean`); each decoded list goes through
`addDecl`, so every one of the 380,696 events of the word becomes its own `WEv` term in
`Data/StageRoute/Events` (about 1.1 KB of olean per event; `Bottlenecks.lean` §2 says what that
costs and why the #8027 word made it heavier). The intermediate states that the chunked replays start and end at are *generated*
during elaboration by replaying the word in meta code (`gen_scalar_checkpoints`,
`gen_label_states`). Neither the decoder nor the generator is trusted: a wrong datum or state
makes a `decide +kernel` fail; it cannot make a false theorem.

| fact | specification | checker (file) | soundness | replays |
|---|---|---|---|---|
| label run of the word | `WarpCheck.WarpRun` (frames, ranks) | `WarpCheck.checkSeg`, `checkGate` (`Cert/Label/Trie`) | `WarpRun.of_checkSeg_nil` (`Cert/Warp/Shear`); `gate_sound`, `checkEnds_sound` (`Cert/Label/Sound`) | `labelSeg0..32` (`Data/StageRoute/LabelRun`), `tab0_ok..tab3_ok` (`Cert/StageRoute.lean`) |
| scalar run of the word | `ScalarCheck.Spec.RefOk` / `Run` | `ScalarCheck.checkSeg`, `checkEnd` (`Cert/Scalar/Checker`) | `checkSeg_sound` (`Cert/Scalar/Checker.lean`, core Lean), `refOk_of_checks`; then `ScalOK.of_refOk` (`Cert/Warp/Shear.lean`) | `scalarSegA1..100`, `scalarSegB1..100`, `wrEnd0A`, `wrEndFA`, `wrEnd0B`, `wrEndFB`, `wrPar`, glued by `ScalarCheck.Split.refOk_glue` (`Cert/Scalar/Split.lean`) (`Data/StageRoute/ScalarRun`) |
| ends, residuals, rows | `checkEnds`, residual list | `chk`, `idCK`, `shKnAB`, `freeK` | `checkEnds_sound`, `res_of_chk`, `idCKn_sound`, `shKnAB_sound` | `Data/StageRoute/Residual` (9) |
| templates act diagonally | `semEvs … = mono(diag) · u` | `ControlCheck.checkSegI`, `checkLastI` (`Cert/Control/Checker`) | `checkEventsI_sound` (`Cert/Control/Checker.lean`, core Lean, row lemmas `rz`/`ri`/`rm`); `Park` only bridges `acts_diag` to `ctrl_diag` | `seg*` in `Data/Batch/TplR` (15) |
| schedule | `range_P … kind_P`, `occ_P`, `vis_P` | `shape_ok`, `range_ok … kind_ok`, `distinct_ok` (single linear walks with recursor helpers `lg`, `allI`, `all2`, `len`, `memB`) | the walker lemmas (`allI_getD`, `all2_getD`, `lg_eq`, …); `distB_nodup`, then pigeonhole (`gx_inj`, `gx_surj`, `inv_spec`) | `Data/Batch/Sched` (7) |
| packing parameters | `Cx.OK params` (offset, mask, `X^647`) | `cx_off`, `cx_mask`, `cx_xn` (`Cert/Scalar/Decode`) | `params_ok`, `good_of_mask` | `Cert/Scalar/Decode` (3) |
| rate | `strict_moment` | `qCert`, `qOk` | `qWalk_sound`, `rank_bnd` | `Data/BaseUnit/Rate` (5) |
| counting, layout | `pay_ok`, `tgt_ok48`, `host_ok`, `port_ok`, … | list equalities | — (the statement is the check) | `Cert/Batch/Word` (8), `Cert/Base/Ops` (5) |

So the kernel replays are not confined to the data modules: `Cert/Scalar/Decode`, `Cert/StageRoute`,
`Data/BaseUnit/Rate`, `Cert/Base/Ops` and `Cert/Batch/Word` also run `decide +kernel`. The
heavy replays (LabelRun, ScalarRun, Residual, TplR) are in Mathlib-free modules; `Data/Batch/Sched`
imports only `Mathlib.Data.Fintype.EquivFin`, for the pigeonhole step behind `occ_P`.

Three kernel tricks recur, and they are why the checkers look unusual:

* *raw recursors* instead of `match`/`if`/`Option` helpers (each helper costs the kernel extra
  unfoldings on the hot path);
* *forced literals* (`forceN`, `forceO`): `Nat.rec` on `succ x` hands on a literal, so states
  never fill with unevaluated thunks (measured about 100× slower without);
* in the scalar checker each register row is one natural number in base `X = 2^426`
  (647 digits: one half of the 1291 keys plus a *ghost* digit 0; the keys below 646 and the keys
  from 646 are checked as two separate runs and glued, `Cert/Scalar/Split.lean`). A key is a start
  register, and only the 1291
  port and slot registers start with a nonzero (identity) row; the 1520 copy registers start
  empty (`idCK spw rf0 1291`), so no row ever carries a copy key. The ghost digit makes the low 64 bits of the
  big literals differ, because the kernel's `whnf` cache keys `Nat` literals by those bits and
  degrades to a linear scan when thousands share them. An add `t += c·s` is a few GMP
  operations, and one `&&&` with `MASK` checks that no digit overflowed (`good_of_mask`).

A detail that removes a whole case: the label checker has a warp event `.w`, but the word's
warp table is empty (`wt_ok : wt = []`), and `evW` requires `|a| ≤ |wt|` with `a ≠ 0`, so any
warp event fails the check. The scalar spec makes `.w` step to `False` as well.

---------------------------------------------------------------------------------------------

## 8. How the 38 files are cut, and why

Import graph (only `Submission.*` imports; each line reads "imported ── importer"):

```
 pinned:    FourierCircuit/Core ─┐
            FourierTransform/RAM ┴─ FourierTransform/Goal ── Algebra/DFTIdentities
 compiler:  RAM ── Compiler/Judgment ── Compiler/Layout
 reels:     Layout + DFTIdentities ── Reel/Machinery ── Ripple/RoleMoves
 engine:    RoleMoves ── Engine/Moves;  Moves + DFTIdentities ── Engine/ClassSetup
            ClassSetup ── Engine/ClassBody, Engine/Recursion;  ClassBody + Recursion ── Engine/Seam
            Moves ── Data/BaseUnit/Rate;  Seam + Moves + Rate ── Engine/TensorPower
 checkers:  Cert/Label/Trie (no imports) ── Cert/Control/Checker, Cert/Scalar/Checker
            Scalar/Checker ── Cert/Scalar/Decode, Cert/Scalar/Split;  Control/Checker ── Data/Batch/Pack
            Moves ── Cert/Clifford/LabelMoves
            Trie + LabelMoves ── Cert/Label/Sound;  LabelMoves ── Cert/Stage/Window
            Sound + Window + Scalar/Checker ── Cert/Warp/Shear
 word:      Decode + Trie + Split ── Data/StageRoute/Events ── LabelRun (+Trie), ScalarRun, Residual (+Trie)
            Shear + LabelRun + ScalarRun + Residual ── Cert/StageRoute
 batch:     Control/Checker + Pack ── Data/Batch/TplR;  Pack (+ Mathlib EquivFin) ── Data/Batch/Sched
            Control/Checker + Rate + StageRoute ── Cert/Base/Ops
            Ops + TplR + Sched ── Cert/Batch/Park ── Cert/Batch/Word
 top:       Judgment + RoleMoves ── Transform/ReelCompile
            ReelCompile + TensorPower + Batch/Word ── Transform/EngineUse
            Goal + EngineUse ── Work/U7604/Chain/FourierTB/Main ── Submission
```

The engine branch and the certificate branch meet as *theorems* only in
`Transform/EngineUse.lean` (`rippleEngine_base`), but they share definitions earlier:
`Cert/Clifford/LabelMoves` imports `Engine/Moves` (moves, frames, `Free`), and `Cert/Base/Ops`
imports `Data/BaseUnit/Rate` (the histograms it must match). The front end meets them in `Main`.

**Mathlib and core.** The 11 modules without Mathlib in their import closure are
`Cert/Label/Trie`, `Cert/Control/Checker`, `Cert/Scalar/Checker`, `Cert/Scalar/Decode`, `Cert/Scalar/Split`,
`Data/Batch/Pack`, `Data/Batch/TplR` and the four `Data/StageRoute/*`; the other 28 have Mathlib
(`Data/Batch/Sched` only through `Mathlib.Data.Fintype.EquivFin`). Why: these modules carry the data and the heavy kernel work, and keeping
Mathlib out keeps their elaboration small (see `Bottlenecks.lean`). Soundness is split by need,
not by a rule: the label checker's soundness is in Mathlib modules (`Cert/Label/Sound`,
`Cert/Warp/Shear`, because it speaks about frames over `ZMod 2`), while the scalar checker's
(`ScalarCheck.checkSeg_sound`) and the control checker's (`checkEventsI_sound`, over any
`Lean.Grind.CommRing`) are core Lean; `Cert/Batch/Park` only identifies the core statement
`acts_diag` with the Mathlib semantics `ctrl_diag`. `Data/BaseUnit/Rate` is under `Data/` but has
Mathlib (through `Engine/Moves`).

**Why 38 files.** The former modules were merged so that the submission fits the file cap of
42: 38 proof files (37 under `Submission/` plus `Submission.lean`) and 4 central files.
(This submission adds one proof file, `Cert/Scalar/Split.lean`: 39 proof files and 4 central files,
43 in all.)
A merged file keeps its former parts as consecutive
sections, each in its old namespace, so no name changed; `Code_explanations.lean` lists the
former parts each file holds.

---------------------------------------------------------------------------------------------

## 9. Where the numbers come from

| number | meaning | where |
|---|---|---|
| `1957647056737859/(5·10^17) = 0.003915294113475718` | stated saving | `Race.bound`; `statedSavingTB19` (`Main.lean`) |
| `7830588226951437/(2·10^18)` | `1 - baseEngineExp`, the engine exponent | `Transform/EngineUse.lean` |
| `3915294113475719/10^18 = 0.003915294113475719` | certified moment rate `u` | `Data/BaseUnit/Rate.lean`, `ripple_program_of_hist_pow` |
| 12800, `12^12800`, `13^12800` | tensor factors `v`, cut `J`, pad `L` | `ripple_program_of_hist_pow`, `strict_moment` |
| `1 - 2/10^11` | Walsh-Hadamard goal exponent `goalExponent` | `Main.lean` |
| `< 8 n^3` | the order `workModulus n` (allowed: `< 1024 n^3`) | `receipt_bound` |
| 137 = 9 + 16·8 | dimension of `Lb` | `Cert/Base/Ops.lean`, `card_LC137` |
| 17 frames, stages 1..16 used | `setX k`, `setY k` (sizes `1+8k`, `8k`); `kτ τ = τ % 16 + 1` | `Cert/Stage/Window.lean`, `Word.lean` |
| 200 ports = 96 F + 8 M + 96 hosted Bk; 891 slots; 1520 copies; 2811 registers | the stage route | `Cert/StageRoute.lean`, `Data/StageRoute/Events.lean`, `Residual` |
| 380,696 events | the native 64 word 27f6a6b9 (layout 0ce3f9e3) | `Data/StageRoute/Events.lean` (`evs`) |
| 277 strings; chunks of 150 events | packed event data | `Data/StageRoute/Events.lean` (`decode_events 150`) |
| 33 label segments / 34 states; 2 × 100 scalar segments / 2 × 101 checkpoints (key halves A, B) | the chunked replays | `LabelRun`, `ScalarRun`, `Events` |
| `X = 2^426`, 647 digits per key half, offset digit `2^223` | scalar packing | `ScalarCheck.params` (`Cert/Scalar/Decode.lean`) |
| 48 calls × 104 ports; 312 roots = 120 A (34 regs) + 192 R (30 regs) × 16 visits | the B48 batch | `Data/Batch/*`, `Cert/Batch/Word.lean` |
| 3685, 848, 484, 226, 314, 41, 10, 2 at ranks 1..8 | price of one stage route | `StageRoute.price`, `stageBlockHist` |
| 52,608 targets, block moment `mom 1 = 742,704` | per gauge copy | `strict_moment` (`Rate.lean`) |

---------------------------------------------------------------------------------------------

## 10. The trusted part and the checked part

* Trusted: Lean's kernel, the axioms `propext`, `Classical.choice`, `Quot.sound` (the axiom report
  for `Race.bound` lists exactly these), and the pinned files `OAI/Computability/FourierCircuit/Core.lean`,
  `OAI/Computability/FourierTransform/RAM.lean`, `OAI/Computability/FourierTransform/Goal.lean`.
  There is no `sorry` and no `native_decide` in the tree.
* Untrusted input: all packed data, the decoders, and the generated checkpoints and states (§7).
* The `private theorem marker_…` lines are the author's notices; each proves `True`.
-/
