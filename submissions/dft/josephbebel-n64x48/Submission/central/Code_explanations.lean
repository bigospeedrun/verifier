/-!
written with help of ai↓

# Code explanations, by semantic segment

Updated for the native 64 x 48-call submission (Joseph Bebel, prepared with Claude (Anthropic) and
OpenAI Codex; see Submission.lean and Credits.lean): the numbers below describe this tree. The text
is Halit Ziya KARTAL's, from PR 209 (bigospeedrun/verifier #209), with only the numbers and the
parts on the native 64 word and the key-split scalar check changed.

This module has no code. For each segment of the tree it lists the files, then says what the
segment provides, the ideas and data that make it work, why it exists, and which segment uses
it. The flow through all segments is in `Tree_explanation.lean`; build cost is in
`Bottlenecks.lean`; sources of the ideas are in `Credits.lean`. Paths are relative to
`Submission/`. Every name below is a name of this tree.

Segments (39 files), in the order the proof is built:

* A. The goal and the cost model (4 files: 3 pinned, plus `Submission.lean`)
* B. Algebra of the DFT (1)
* C. The RAM compiler calculus (2)
* D. Reels, the binary Clifford toolkit and the CRT modulus (1)
* E. The ripple and role data (1)
* F. Engine moves, routes, moments and splits (1)
* G. The block engine (4)
* H. Tensor powers and the certified rate (2)
* I. The certificate checkers and their soundness (9)
* J. The stage route: word data and its replays (5)
* K. The B48 base unit (6)
* L. From the engine to the DFT (3)

---------------------------------------------------------------------------------------------

## A. The goal and the cost model

Files:
* `OAI/Computability/FourierCircuit/Core.lean` (pinned)
* `OAI/Computability/FourierTransform/RAM.lean` (pinned)
* `OAI/Computability/FourierTransform/Goal.lean` (pinned)
* `Submission.lean`

What it states.
* `Core.lean`: the circuit statement the RAM goal grew from. A `Gate` is one charged scalar gate
  (`add`, `sub`, `scale c`) that references only values already available; a `Program` is a
  topologically ordered DAG whose values are never consumed; a `Circuit` names its outputs among
  the available values, so permutations and fan-out cost nothing. It also defines
  `zeta n = exp(2πi/n)` and `fourierMatrix`, which `Goal.lean` uses as `root` and `dftMatrix`.
* `RAM.lean`: the exact scalar-and-index RAM. Types `Ty` are words `w`, complex values `c paint`,
  pairs and tapes (arrays). The cost record `Bill` holds the value, the work, the `peak`
  (largest integer produced or needed, beyond the inputs) and a validity `Prop`. Atoms: word
  arithmetic `NOp` (`add sub mul div mod lt`, with Lean's conventions at 0), complex `add`/`sub`
  within one paint, `scale` (a scalar times a value), `inv` of a scalar (valid only if nonzero),
  `cross` (product of a `left` and a `right` value, only when `allow = true`), projections, tape
  length and lookup. Programs `Code`: composition, `fork`, `ifz`, `loop`, `tab`, `sow` (build a
  tape by a loop of writes), `importClosed`, and one bounded recursion `descend` with its `call`
  port. One basic work unit pays for O(1) primitive operations, loop and stack overhead included.
* `Goal.lean`: `dft`, `conv`, the exact paper exponent `theta` (from `paperM`, `paperW`,
  `paperDelta`), `paperTime`, `decimalTime`, `nlogn`, and the program specifications
  `DFTProgram` and `ConvProgram`: an order program on the length alone, whose result `d`
  (below `1024 n^3`, polynomially bounded) fixes the root `root d` that the solve program
  receives as input; the work allowance `W n` covers the order program, one root and the
  transform. `TimeBounds`, `DFTGoal`, `ConvGoal`.
* `Submission.lean`: the entry headers, the licences and notices, and `Race.bound`, which reads
  the decimal-exponent bound off `transform_mainTB19` (segment L).

Why it matters downstream. The paint discipline means a DFT program is linear in the data with
scalar coefficients, which is why every later program is a sequence of linear maps (reels,
moves). Because index arithmetic is charged, every table and layout later has a cost proof.

Feeds: every segment builds programs and costs in this model.

---------------------------------------------------------------------------------------------

## B. Algebra of the DFT

Files:
* `Algebra/DFTIdentities.lean` (namespaces `Spectral.PrimRoot`, `Spectral`)

What it proves, with no programs in it:
* primitive roots (`Spectral.PrimRoot`: powers, inverse, `pow_of_dvd`, `pow_inj`);
* the frequency map `freq n u x i = Σ_j u^(ij) x_j` on `Line = ℕ → ℂ`, `front` (a line cut to a
  vector), cyclic convolution (`cyclic`, `predAt`) and the convolution theorem;
* `signedRoot`, chirps `chirp z i = z^(i·i)`, `chirpFilter`, and Bluestein's identity
  `bluestein_freq`: for `N ≥ 2n` a length-`n` DFT is a cyclic convolution of length `N`;
* the Vandermonde factorization `rootVandermonde_factor`: `rootVandermonde` on a
  primitive root is `L · D⁻¹ · Lᵀ` with `L = vandLower = diag(gap) · stairs(floorH) · diag(roof)`
  (a lower triangular Toeplitz matrix between two diagonals) and `D = diag(vandDiag)`; the proof
  identifies `vandLower` with `nodeMat` through Newton's basis (`newt`, `newtMat`); and the
  triangular Toeplitz inverse `toeplitzInv` (`recoilTo`).

Why: these are exactly the matrices the reels of segment D realise, and the two reductions
(Bluestein, Vandermonde) are what lets a DFT of any length be built from power-of-two pieces.

Feeds: D (reels), G (`ClassSetup` imports it), L (Bluestein).

---------------------------------------------------------------------------------------------

## C. The RAM compiler calculus

Files:
* `Compiler/Judgment.lean`
* `Compiler/Layout.lean` (it begins with the core-Lean `DigitArith` helpers)

What it provides. A calculus for building one RAM program for a whole family of inputs indexed
by a type `ι`, so a single proof yields a single program:
* `Bill.OK b x w p`: the run computes `x`, with work `≤ w`, peak `≤ p`, and is valid;
* `Small B F` (`F i ≤ (B i + 2)^d`) and `Dom W F` (`F = O(W)`);
* `Bank`, `Able m b s t x y W Z` (a program with a call port and a charge `Z`), and
  `Can m B s t x y W`: a closed program from type `s` to `t` mapping `x i` to `y i` in work
  `O(W i)` and peak polynomial in `B i`; `PolyCan` for polynomial work;
* combinators for the `Code` constructors and the atoms (`pipe`, `pair`, `loop`, `tab`, `sow`,
  `testz` at `Judgment.lean`, ...);
* `Bench` (an environment: a size, a tray type and its value per index) and, in
  `Judgment.lean`, the bench judgments `Makes`, `Digit` and `Study` (a
  decidable predicate read off a computed digit), with `branchM`.

`Layout.lean` adds:
* `Layout α`: a bijection of a finite type with `Fin n`, with `pair`, `cat`, `vecFin`, `digits`
  and `someLayout`; tapes of functions on a layout (`Can.layout`, `Can.fetch`), `cases_code`;
* programs for `log₂`, powers, numerals and rational constants (`logC`, `wpow_fixed`, `rat`);
* the remaining bench judgments: `Moves` (a value computed from the bench in work `W`),
  `Nick` (a word computed for free and polynomially small), `Instant` (a new bench
  prepared for free), `Dry` (a value in polynomial work) and `Grain` (a word in
  polynomial work, polynomially small).

Why: a DFT program is one fixed program for all `n`, so costs must be proved uniformly in `n`.
The judgments let each later lemma state "this value can be computed from what we already have
within this budget" and compose such facts without ever writing a `Code` term by hand.

Feeds: every program in D, E, G and L is assembled with these lemmas.

---------------------------------------------------------------------------------------------

## D. Reels, the binary Clifford toolkit and the CRT modulus

Files:
* `Reel/Machinery.lean`

What it proves. Five kits in one module:
1. `digitProd` (the tensor product of matrices indexed by functions) and its algebra.
2. `Binary`: the space `Space α = α → ZMod 2`, `dot`, orthonormal bases `OBase` with `mat`,
   `proj`, `adapt`; the 2×2 matrices `littleH` (Hadamard) and `littleC`
   (`ca = (1+i)/2`, `cb = (1-i)/2`), their tensor powers `wal` and `kernel`; `lum x = ∏ tint (x i)`
   (`tint 1 = i`); `wrap f = wal · diag f · wal⁻¹` (the matrices diagonal in the Walsh basis);
   `shift`, `dir z = ca·1 + cb·shift z`, and the frames `frame A s = wrap (lum ∘ proj_s)`. A frame
   on an `r`-dimensional subspace is, up to free factors, a ripple on `r` bits: this is the
   "block" of the engine.
3. `ReelKit`: a *stroke* is one parallel step (`ix`: an index map, `dye`: a diagonal scale,
   `partner`: an involution; `applyC` mixes each pair `i ≠ partner i` by `littleC`); a *reel* is a
   list of strokes (`stack`, `parallel`, `wait`, `tick`). From strokes it builds an exact
   add-a-scaled-copy gadget (`addScaledReel` through `butterflyReel`, `brick`, `spark`), the
   radix-2 FFT reel (`fftReel`), cyclic convolution (`cyclicConvReel`), blocked and naive Toeplitz
   products (`toeplitzGridReel`, `naiveToeplitzReel`), the recursive-doubling Toeplitz reel
   (`toeplitzReel`) and the Vandermonde reel (`vandermondeReel`) with
   `beats_ballad`: `vandermondeBeats e = 2·chorus e + 7` beats for size `≤ 2^e`, at most
   `20000000·(e+1)^2 + 7` (`score_le`).
4. `AxisTensor`: running reels on all axes of a tensor product at once (`axisRun_eq_kron`);
   power-of-two block covers of the mixing step (`PowBlock`, `PowBlockCover`,
   `PairBlocks`, `strokeBlocks`); the CRT index map (`crtIndex`, `CoprimeAxes`) and `crt_freq`.
5. `Modulus`: `axisBudget n = log₂(2n) + 1`; primes searched below `(16(k+4))^2`
   (`primeSearchBound`) with enough of them by a central-binomial count; `greedyPrimes`,
   `oddPart`, `twoPart`, `modulusAxes n` with `modulusAxes_spec` (squarefree,
   `2n ≤ vol < 4n`, at most `axisBudget n` axes, each `≤ 2^axisLogBound n`); `IsLargeLen`,
   `workModulus` and `receipt_bound` (`0 < workModulus n < 8 n^3`); RAM contexts
   `Lade`, `LenCtx` that compute these.

Why reels use only `littleC`: when all axes run the same beat, the mixing across axes is a tensor
product of `littleC` pairs, which is a ripple on each power-of-two block (segment L). Any other
2×2 mixing would not reduce to the one map the engine makes fast.

Feeds: E (bits and kernels), L (axis reels and the modulus), F and I (frames and bases).

---------------------------------------------------------------------------------------------

## E. The ripple and role data

Files:
* `Ripple/RoleMoves.lean`

What it provides:
* data on roles: `Sky α f` (`f` copies of `Space α`), `Data α ρ f = ρ → Sky α f → ℂ`; a matrix on
  every copy (`matAct`), per role (`multiAct`, `roleAct`), pointwise role mixing (`point`); the
  first move type `Move` and words `PWord`;
* bit layouts `bits k`, `serial` (a grid of roles and copies flattened to bits), and the
  definition `ripple k x = kernel (Fin k) *ᵥ x`;
* RAM contexts that read tapes of such data (`BitCtx`, `RoleTapeCtx`, `xorTab`), the batch
  input format of the engine (`simIn`, `bundle`, `givenBits`, `loaded`, `whole`), and the
  baseline `ripple_naive_can`: the ripple in work `2^k (2k+1)`.

Why: this fixes once what "a ripple on `k` bits" means as RAM input and output, so the engine
(segments F to H) and the front end (L) agree on the seam statement `RippleEngine`.

Feeds: F and G (moves act on this data), L (`RippleEngine` is stated with `ripple`).

---------------------------------------------------------------------------------------------

## F. Engine moves, routes, moments and splits

Files:
* `Engine/Moves.lean` (namespaces `TensorMoment`, `Histogram`, `Binary.Split`, `BMove`,
  `GenMove`, `GRoute`, `LiveKernel`, `StageBox`, `RankCost`)

What it provides:
* `TensorMoment` (Mathlib only): the moment `mom t s = Σ r^t` of a multiset of ranks; `tens`,
  `tpow` with `mom_tpow` (moments multiply); `pieces`/`splitAll J` (a rank `R > J` becomes
  pieces of at most `J`); `padT`/`comp L` (a target `K < L` is completed to `L` by a paid job of
  rank `L - K`); `strictT`, `strictP`; `strictify_mom` and `strictify`: the completed,
  split `v`-fold product has moment surplus as soon as `α^v + 2γ^v + 2δ^v ≤ 1`. `envelope z k =
  ⌈(k+1)^z⌉` and `histFn` also live here;
* `Split`: an additive splitting `Space α ≃ Space β × Space γ`; `blockMat z` for an independent
  family `z` equals a lifted kernel (`blockMat_eq_lift`, `exists_split`); `Split.product`;
* `BMove`: `localM`, `shift`, `block l r z ind` (a rank-`r` block on role `l`), `rk?`, `Proper`,
  `costR φ` and the histogram `hist`;
* `GenMove`: `GMove` adds `perm`, `phase`, `localG` (a rational matrix with a Gaussian part);
  `gwalk` (the semantics of a word), `GStep`, `Free` (the matrices one role gets for free: one
  linear pass, no recursive call), `gstep_free`, `gstep_block`, `gstep_of_factor` (a transition
  that factors as free · block of rank `r` · free costs one block of rank `r`); routes `GRoute`
  (`trans`, `gate`, `on_role`, `parallel`, `lift`, `GMove.over`);
* `LiveKernel`: `GLiveKernelM e T w`: on every input that is zero on the scratch roles,
  the word leaves `T l` of the input on live role `e l`, for every number of copies;
* `StageBox`/`RankCost`: the role boxes `Box T Sl C` (X and Y per port, slots, copies), `stamp`,
  `rcost`/`bcost` (the cost of a rank list under `φ`), `XMap`.

Why: one vocabulary of moves and costs serves both the engine (which executes words) and the
certificate (which proves that a word realises its targets at a known price).

Feeds: G (words of `GMove`), H (moments), I (routes certify stages), K (the unit is a
`GLiveKernelM` word).

---------------------------------------------------------------------------------------------

## G. The block engine

Files:
* `Engine/ClassSetup.lean`
* `Engine/ClassBody.lean`
* `Engine/Recursion.lean`
* `Engine/Seam.lean`

What it proves. Given a `BlockEngine α ρ σ` (`ClassSetup.lean`: layouts `X R Q`, live roles
`e`, target ranks `tr` and families `tz`, a proper word `wd` whose block ranks are below every
target (`sep`), and `hw`, the live-kernel property), a RAM program for `ripple k` for every `k`
in work `O(2^k (k+1)^z)` (`BlockEngine.ripple_program`, `Seam.lean`).

The recursion. A ripple on `n` bits is split by `hlow`/`hhigh`: the low part is a *class job*,
the high part leftover ripples on fewer bits. A class job at height `h` with multiplier `μ` runs
the units `UnitClass.U` (class words `s` with `mx·μ·colS ≤ n`): it loads the jobs onto the unit's
data (`V0`, `placeT`; `placeS` puts block coordinates low, the rest of the label next, the
instance number on top), runs the word move by move (free moves in place; block moves become
child class jobs at height `h-1` with multiplier `μ·r`, or exit jobs at height 0), and unloads
(`unl_run`: slot `t` ends with its job answer on its low bits, from `hw` and `blockMat_eq_lift`).
Jobs are one RAM type (`EngJob`: `top n B v`, i.e. `B` ripples on `n` bits, or a class
`cls n h μ o BS J sup`).
* `ClassSetup.lean`: tables in linear work: `doublingTable` (level `j+1` read off level `j` at
  `r/2`; all `2^k` entries in `O(2^k)`), `pylon`, `LumTable.weight_table` (the digit-product weights `∏ᵢ (if y i = 0 then e else o)`), `lum_tables`,
  `tablePow`; `UnitClass` (`colS`, `inRS`, `NU`, `U`), `EngJob`, the contexts `CCtx`/`CIn` (sizes,
  the imaginary unit, per-unit tables, the fit equation), `Can.jobsTable`, `BlockEngine`.
* `ClassBody.lean`: `class_body`, the program of one class job (valid descriptions only: positive
  scale, room for `h` more levels, supplied jobs cover what the class consumes), with its sweeps
  and their costs.
* `Recursion.lean`: `EngRecursion.closed`/`closed_inv`: from ONE open body that
  answers its calls through a handler, with calls going down in rank and preserving an
  invariant, to a closed program by `descend` with fuel; `closed_list` (charges as lists of
  calls); the counting of sources (`cs_body`, `can_cons`) and the top job (`top_body`: naive
  below `n0` or with too few vectors, else tree copies over the root class plus rest calls).
* `Seam.lean`: `job_body`, the one open body of the lockstep program; the abstract shape
  `EngShape.Rule` with `Shape`, `kidsS`, `locS`, `costS`, `topCost`, `treeCost`, the
  recurrence `JobCostRec` and its least solution `jobCost`; the lemmas of the cost proof:
  `recurrence_bound` (Lemma A), `balance` (Lemma B: a child's inputs are its parent's outputs
  plus its own sources), `src_size` (Lemma C: sources have size in `(n/m, n]`), `exit_size` and
  `phi_exT_le` (Lemma D), `units_le` (Lemma E), `exits_small` (exit decay; this replaces the log
  factor) and `eta_step`; the bound `Rule.jobCost_bound`: `MomentRate z1 1` with
  `z1 < z ≤ 1` gives `jobCost n ≤ C·2^n (n+1)^z`; `RealisesRule` ties a concrete engine to a rule;
  `ripple_split_program` (halves and transposes), `sim_program_of_port`, `port_top_can`, and
  `BlockEngine.ripple_program`.

Why one open body closed by `descend`: the RAM has exactly one recursion construct, with one call
port, so all job kinds must share one encoding and one body.

Feeds: H (`BundledUnit.ripple_program` builds a `BlockEngine` from a tensor power).

---------------------------------------------------------------------------------------------

## H. Tensor powers and the certified rate

Files:
* `Engine/TensorPower.lean` (namespaces `TensorPower`, `TensorPower.RawCert`)
* `Data/BaseUnit/Rate.lean` (namespaces `BaseUnit`, `TensorMoment.BaseRate`)

What it proves.
* `KernelUnit` (a unit without layouts) and `KernelUnit.prod_exists`: the product of two units is
  a unit whose block ranks and targets are the products (`pstep`, `liftM`, `colL`, `frame`).
* `BundledUnit` (a unit with its types packed) and `BundledUnit.pow`: `pow 0 = A`,
  `pow (n+1) = (pow n).prod A`, so `pow n` is the `(n+1)`-fold product (
  `ranks_pow`, `tgts_pow`, `card_pow` all use `n + 1`).
* `padTargets_exists` (raise targets to `L` with complement blocks), `cut_blocks_exists` (cut
  blocks above `J`), `rule_of_moment` (a moment inequality gives `MomentRate`), and
  `BundledUnit.ripple_program`.
* `ripple_program_of_hist_pow` (with `n + 1 = 12800`), `ripple_program_of_hist` (calls it
  with `n = 12799`), `ripple_program_of_rawCert`: from a raw certificate with
  `|α| = 137`, block histogram `G·blockHist` and target histogram `G·targetHist`, an engine at
  every `zE > 1 - 3915294113475719/10^18`.
* `Rate.lean`: the two inventories `targetHist` and `blockHist` (generated lists of
  `(rank, count)`), and `strict_moment`: the moment inequality for 12800 factors with
  `J = 12^12800`, `L = 13^12800` at `t = 1 - u`, `u = 3915294113475719/10^18`. Each `r^(1-u)` is
  bounded by an integer certificate: `qWalk` takes `r^(1/10^j)` by integer tenth roots
  (`qRoot`, integer Newton from an overestimate) and multiplies in the decimal digits `qDig` of
  `u`, all at scale `Kc = 10^22`, and `qOk` re-checks every step (the computed values are never
  trusted). `w_ge` bounds `12^u ≥ 10097/10000`, and `fin` reduces everything to one integer
  inequality, decided by the kernel.

Why 12800 factors and the two bases 12 and 13: separation needs every paid rank below every
target, and the padding/cutting costs (`γ`, `δ`) must be outweighed by the moment gain; both
improve geometrically with the number of factors, and 12800 is the count at which the
inequality is checked.

Feeds: L (`rippleEngine_base`).

---------------------------------------------------------------------------------------------

## I. The certificate checkers and their soundness

Files:
* `Cert/Label/Trie.lean` (no imports; namespaces `TrieCheck`, `CertData`, `WarpCheck`,
  `ControlCheck`, `LabelCheck`)
* `Cert/Control/Checker.lean` (core Lean)
* `Cert/Scalar/Checker.lean` (core Lean)
* `Cert/Scalar/Decode.lean` (core Lean plus `Lean.Elab.Command`)
* `Cert/Scalar/Split.lean` (core Lean; new in this submission: the key-range split `glue`,
  `st_split`, `refOk_glue`, which combines two `RefOk` runs on the keys `< m` and `≥ m`)
* `Cert/Clifford/LabelMoves.lean`
* `Cert/Label/Sound.lean`
* `Cert/Stage/Window.lean`
* `Cert/Warp/Shear.lean`

The data types (`Trie.lean`). A coefficient `Co` is `(neg, num, den)`. A gate `Gate` is `out`
(one source added into several targets, plus extra registers that move) or `inn` (several sources
into one target); every register a gate names first moves to the gate's frame, then the adds
happen in order. An event `WEv` is a gate `g`, a scale `sc`, a warp `w`, the zero buffers `za`
and `zf`, or a down move `dn`. A frame is one natural number, its *code*:
`code = dim + 2^8·M + 2^(8+h)·P`, with `M = Σ 2^p` over the pivots of a reduced echelon basis and
`P = Σ b_p·2^(h·p)` (basis vector of pivot `p` is digit `p`); `cdim c = c &&& 255`. The frame
table `tab` and the register states are binary tries `TrieCheck.Trie`. Controller events `CEv`
are `add t s co e`, `mul`, `mon` (times a monomial) and `swp`.

The kernel checkers (core Lean, raw recursors and raw `Nat`):
* label check (`LabelCheck.checkGate`, `checkEnds`, `checkTable`, `WarpCheck.checkSeg`): a gate
  moves each named register up into its frame, records the rank `dim f - dim old`, and checks by
  one packed Gaussian elimination (`elimT`) that the old frame lies inside the new; a `dn` event
  checks a strict dimension drop and the span inclusion; `checkEnds` checks ports, slots (start
  at frame 0 or gauged; an exit slot ends in a frame containing its start frame; every other slot
  ends at full dimension) and returns. The warp event `.w` is checked against the warp table, and
  since the word's table is empty (`wt_ok`) no warp event can pass;
* scalar check (`ScalarCheck`, `Cert/Scalar/Checker.lean`): the specification `ScalarCheck.Spec`
  is a plain relation on states `Nat → Nat → Int` (`AddStep`, `Step`, `Run`, `RefOk`);
  the checker packs each register row into one number in base `X = 2^426` with offset digits
  (`offN`, `Good`, `dec`, `lin_dec`, `ins_dec`), keeps rows in a trie `PT`, and checks digit
  overflow with one `&&&` against `MASK` (`good_of_mask`); `checkSeg_sound` and
  `refOk_of_checks` connect it to the spec. Digit 0 of every row is a ghost (key `k` lives at
  digit `k+1`): it makes the low 64 bits of the big literals differ, because the kernel caches
  `Nat` literals by those bits and slows down more than 100× when thousands share them.
  `forceO` evaluates to a literal before continuing, so the state never holds deep thunks;
* control check (`ControlCheck`, `Cert/Control/Checker.lean`): sparse rows `Row` of
  `(key, integer)` with `insK`/`mergeK`/`scaleK`; a key is `(code/8 · N + col)·8 + code%8`
  (`kmk`), so multiplying by a monomial only reorders entries inside a block of 8; Gaussian
  monomial codes with an `ι` bit (`monoI`, `cmI`, `mmKI`); `checkSegI`, `checkLastI`; and its
  soundness `checkEventsI_sound` in any `Lean.Grind.CommRing` under `SemHyp`
  (`q^4 = 1`, `L^2 = q^2`, exact rational coefficients), via the row lemmas `rz`, `ri`, `rm`.
  Core Lean throughout;
* row tries `RT` with the identity, shear and freeness checks `idK`, `shKnAB`, `freeK`, and the
  erased identity check `idCK q R m` (identity rows below `m`, empty rows from `m` on).

The decoders (`Decode.lean`). Every packed string is one decimal number, read by an adaptive
binary model (a context holds the chance `p` of a 0 out of 4096; a bit is decided by the residue
of the number mod 4096, big-number ANS). Commands `decode_events c` (chunks `ev<s>_<j>` of `c`
events, segments `ev<s>`, and `evs`), `decode_frames`, `decode_nats`, `decode_nat_trie`,
`decode_row_trie`, `decode_id_rows`, `decode_shear_rows`; registers are coded by their position
among the 15 most recent ones (per frame or overall) or by a short difference; numbers by an
Elias-gamma style length. Every definition goes through `addDecl`. `gen_scalar_checkpoints` and
`gen_label_states` replay the word at elaboration time from the decoded meta values and emit the
intermediate states (and, for labels, the rank list `rAll`, `stF`, `gl`, `exits`, `resW`); all of
these are untrusted, since the kernel re-checks every chunk. `gen_scalar_checkpoints` takes a cut
count (100), cuts the chunk list at chunk boundaries into segments of about equal event count, and
shares leaves: each checkpoint `wrS<i>` is a trie over one constant per leaf (`wrS<i>_<r>`), and a
new leaf constant is made only for the rows that segment `i` changed. It also emits `wrE_evs`, the
equation that the segment lists `wrE0 ++ … ++ wrE99` make up `evs` (proved by `delta` on the
segment-level definitions and `List.append_assoc`, without unfolding the chunk lists).
`params` fixes the packing: digits of 426 bits, offset digit `2^223`, denominators below
`2^195`, numerators below `2^202`, 647 digits: one key half plus the ghost digit (the 1291 keys are
checked as the halves below 646 and from 646, `gen_scalar_checkpoints_keys`, glued by
`ScalarCheck.Split.refOk_glue`; the 1520 copy registers start empty, so they need no key). Three
kernel checks (`cx_off`, `cx_mask`, `cx_xn`) tie these literals to `offN`, `maskN 426 224 647` and
`(2^426)^647`, and `params_ok` gives `Cx.OK params`. The widths are forced by the word: a no-carry
add needs `Kd·2H + Kd + Kn·H ≤ X` (`2^419 + 2^195 + 2^425 ≤ 2^426`). The native 64 word's
coefficients (numerators below `2^202`, denominators below `2^195`) fix `Kn` and `Kd`. The real row
entries stay below `2^203`, but the salted ghost digit reaches `2^223`, and that fixes the offset
digit `H`.

The soundness on the Mathlib side:
* `LabelMoves.lean`: the Clifford normal form. Coordinate frames `coordFrame s`, core frames
  `coreFrame G s` conjugated by phased permutations; `repChange_core` (a subspace determines its
  core frame up to a `Free` factor), `exists_common_base` (nested subspaces share a base),
  `frame_core`; then `FrameMove` (a frame matrix moves by free matrices and blocks of listed
  ranks), `SubspaceLabel` (a subspace `InSub G s` with its exact representative), `LabelMove`,
  `LabelLift` (a map from the label space `H` into the larger address space `α`), and
  `LabelMove.of_sub`/`of_sup`: moving a label from `U` to `V ⊇ U` needs only the inclusion, and
  costs one block of rank `dim V - dim U` plus free moves.
* `Sound.lean`: the `Nat`-level specification of the label checkers (`InSpan h c x`: every
  xor-closed set containing the words of code `c` contains `x`; `GoodN`), and their soundness
  (`elimT_sound`, `tabK_good`, `gate_sound`, `checkEnds_sound`), decoded to subspaces by
  `labelOf`.
* `Window.lean`: the stage geometry, independent of the certificate format. Role boxes per gauge
  (`SRole`, `sem`), `GReach`, `gsstage`; label lifts by conjugation (`LabelLift.ofConj`);
  `Window` (an `XMap` with a `LabelLift`); `StageInvariant` (per window, a route from the
  entry frames to the exit frames realising `shear al be`, at cost `cost`) and its exit normal form
  (`exRouteE`, `toExit`); `Orth`; the 137-dimensional space
  `LC (Fin 16) H l = H ⊕ (Fin 16 × (H ∖ {l}))` with banks (`blkC`, `PhiC`, `piC`, `BBC`); and
  `StageFrames`: the 17 frame pairs `setX k`, `setY k` (sizes `1+8k` and `8k`, `k = 0..16`),
  `gaugePerm`, `window`.
* `Shear.lean`: the `Nat`-level spec of the warp-segment checker (`WarpRunN`,
  `WarpRun.of_checkSeg_nil`), the route of a run (`run_route`: a checked label run is a route
  whose cost is the `rcost` of its ranks), the scalar meaning of events (`eMap`, `esMap`, `vecR`,
  `ScalOK`; bridge `ScalOK.of_refOk` from the packed checker's `RefOk`), the shear
  (`PortShear` F/Bk/M, `esMap_shear`), and `CertValid` with `clean`, `invAB`, `invCtr`: a valid
  route certificate gives a `StageInvariant`.

Why the split between checker and soundness: the checkers must be cheap for the kernel, so they
avoid Mathlib types; the facts the unit needs are about matrices over `ℂ` and subspaces over
`ZMod 2`, which need Mathlib for the label side. The scalar and control soundness need only ring
facts, so they stay in core Lean.

Feeds: J (the checks run on the word), K (the invariant is used 48 times; the control check on
the templates).

---------------------------------------------------------------------------------------------

## J. The stage route: word data and its replays

Files:
* `Data/StageRoute/Events.lean` (generated data)
* `Data/StageRoute/LabelRun.lean`
* `Data/StageRoute/ScalarRun.lean`
* `Data/StageRoute/Residual.lean`
* `Cert/StageRoute.lean`

What it proves. `StageRoute.invariant : StageInvariant (Fin 9) (Fin 200) (Fin 891) (Fin 1520)`
(`Cert/StageRoute.lean`) with cost
`price φ = 2·φ8 + 10·φ7 + 41·φ6 + 314·φ5 + 226·φ4 + 484·φ3 + 848·φ2 + 3685·φ1`.
* `Events.lean`: 277 packed strings decoded (`decode_events 150`, so chunks of 150 events) into
  `evs` on 2811 registers; the erased identity start rows `rf0` (identity rows on the 1291 port
  and slot registers, empty rows on the copy registers), the shear end rows `rfF`, the 200
  `ports`, the frames and their code trie `tab`, the start labels `st0` (register tries of depth 12); the two chains
  of 101 scalar checkpoints `wrSA0..wrSA100` and `wrSB0..wrSB100`, one per key half (leaf constants
  shared between checkpoints), with their segment lists `wrEA*`, `wrEB*` and equations; the 34 label states
  `labS0..labS33` with segment lists `labE*` and rank lists `labR*`; the parameters `par`, `pe`,
  `spw`; and `schedRes`, the residuals of the 891 slots.
* `LabelRun.lean`: 33 theorems `labelSeg i` by `decide +kernel` (the native 64 word 27f6a6b9 has
  380,696 events).
* `ScalarRun.lean` (generated): 200 theorems `scalarSegA i`, `scalarSegB i`, the four end packings
  `wrEnd0A`, `wrEndFA`, `wrEnd0B`, `wrEndFB`, `wrPar`, `scalar_refA`, `scalar_refB` (each from its
  100 segment runs appended), and `scalar_ref : ScalarCheck.Spec.RefOk spw evs rf0 rfF` by
  `ScalarCheck.Split.refOk_glue 646` (the same statement as in PR 209).
* `Residual.lean`: fast recursor-only evaluators with equality lemmas, the contract list
  `portShears` (`M` on the 8 B ports, `F` on the other ports below 104, `Bk` on the hosted ports
  from 104), the residual check (`res_chk`, `residual_ok`), the identity, shear and freeness of
  the row tries (`id0_ok` by `idCK spw rf0 1291`, `shear_ok`, `frF_ok`, `wfF_ok`), the end conditions `ends_ok`, and the
  rank facts `rankBound` (every rank is below 9) and `rankCounts` (3685, 848, 484, 226, 314, 41,
  10, 2 at ranks 1..8); 9 facts by `decide +kernel` in all.
* `Cert/StageRoute.lean`: `price`, `rankCost_eq_price`, the gauged stage run (`GAB`,
  `gauge_route`), `tab0_ok..tab3_ok` (four kernel checks of the frame table) and `tab_ok`,
  `label_run` (the 33 segments appended), `cert_valid`, `roles_ok`, `invariantRaw`, the exit form
  `invariant`, `invariant_price`, `hent`.

Why the chunking: one `decide` over the whole word would be one enormous kernel term; chunks with
generated boundary states keep each check independent and the composition (`label_run`,
`scalar_ref`) a short proof by `append`.

Feeds: K (the stage operator of every call is `StageRoute.invariant`).

---------------------------------------------------------------------------------------------

## K. The B48 base unit

Files:
* `Cert/Base/Ops.lean`
* `Data/Batch/Pack.lean` (the `bpack_*` decoders; used by TplR and Sched)
* `Data/Batch/TplR.lean` (generated data; namespaces `ControlCheck.TplA` and `ControlCheck.TplR`)
* `Data/Batch/Sched.lean` (generated data)
* `Cert/Batch/Park.lean`
* `Cert/Batch/Word.lean`

What it proves. `Batch48.rawCert_exists_B48` (`Word.lean`): on `α = Lb`
(`Lb = LC (Fin 16) (Fin 9) 0`, `|Lb| = 137`) with gauge `Gm = Orth Lb`, a proper word that acts as
`blockMat (tzB l)` on its live roles, with `hist r = |Gm|·histFn blockHist r` and
`#{l | trB l = r} = |Gm|·histFn targetHist r`.

How the unit works. Each call `τ < 48` runs the stage route at sub-stage `kτ τ = τ % 16 + 1`
(`Word.lean`), on the ports of the roots that visit it. Between calls every root runs its
template's local events (A roots: `TplA`, 34 registers; R roots: `TplR`, 30 registers): free row
moves, swaps, monomial phases and bank masks (a D mask over any set of slots is one frame over a
union of banks). The schedule says which root visits which call at which port (312 roots × 16
visits, 48 calls × 104 ports). At the end each root's register holds `q^phase · Pf(bank set)`
(`root_fin`, `mono_val`), one free shift turns it into its target block (`tgt_eq`), and each
call's 891 helpers are padded from their stage residuals to their target ranks (`ex_Z`,
`HostPad.host_pad`).
* `Ops.lean`: realised operators (`RealisedOp`, `steps`, `groute`, `ext`), the Walsh view `wl`,
  the ring elements `qv`, `Lv`, `Dv`, `Pf`, `Pv`, the controller semantics (`monoV`, `semEvs`,
  `jEvs`), the JCALL lowering, copy layout and price tables (`stageBlockHist`, matching `price`),
  the port layout (every port is the primary of its copy, or the host port `104 + c` of an A copy;
  hosted ports share the line of their copy primary), the stage roles `SR` and the stage
  operator `stOp` with its view.
* `Pack.lean`: base-5 packed lists (one decimal digit per base-5 digit, `5..9` ending a number),
  dictionaries for codes and values; `bpack_cevs`, `bpack_rows`, `bpack_nats`, `bpack_natss`,
  `bpack_pairss`. Every list goes through `addDecl`.
* `TplR.lean`: the two templates. `TplA`: 1064 events, 34 registers, `Dn = 2`, replayed in 2
  chunks; `TplR`: 4590 events, 30 registers, `Dn = 4`, replayed in 11 chunks. Each event list is
  `loc 0 ++ hostEv 0 ++ … ++ hostEv 15 ++ loc 16` (`evs_split`), and `acts_diag` follows from the
  chunk checks `seg*`.
* `Sched.lean`: the tables `vis` and `sinv` (packed data), `vCall`, `vPort`, `slot`, and
  `owner`, which is not a table: it is the inverse of the visit map `gx x = vCall·104 + vPort`
  (`inv`, `oRoot`, `oSlot`, by `Classical.choose`). Seven facts by `decide +kernel` (`shape_ok`,
  `range_ok`, `chrono_ok`, `slot_ok`, `slot_inv_ok`, `kind_ok`, `distinct_ok`), each one linear
  walk with recursor helpers (`lg`, `allI`, `all2`, `len`, `memB`). `distinct_ok` (a bitmap walk)
  shows the 4992 visit codes are distinct, so `gx` is injective and, by pigeonhole
  (`Mathlib.Data.Fintype.EquivFin`), onto (`gx_inj`, `gx_surj`, `inv_spec`); this gives `occ_P`
  and `vis_P`. Their `Prop` forms and `Fin` wrappers (`owner_visit`, `slot_colour`). Roots
  `r < 120` are A roots; for `r ≥ 120`, `r - 120 = 8 s + m` is a rotated mixed root.
* `Park.lean`: the Gaussian semantics of I-codes (`monoVI`, `semEvsI`, identified with the core
  checker's `monoI`, `semEvsG`), `ctrl_diag` for both templates from `acts_diag`, bank masks
  (`mask_frame`), park roles (root blocks `Fin 312 × Fin 40`, `NQ = 891` helpers per call), free
  row and swap moves and paid frame moves on gated roots, and every template event realised as
  gated park moves with its block cost (`ev_realised`, `seg_realised`, by list induction).
* `Word.lean`: copy relabel (`rho`, `BBC_rho`), free pulls (`pullM`, one `localG` move), the stage
  operator on park roles (`stOp'`, `stage_op'`), HOST lowering, one call (`cOp`, `call_spec`),
  the run of 48 calls (`run_spec`), prep, end and shift moves (`prepB`, `endB`, `shiftB`), the
  counting facts by `decide +kernel` (`dg_ok`, `pay_ok`, `tgt_ok48`, `n_ok`, `host_ok`, `loc_ok`,
  `port_ok`, `pt_lt`), `raw_B48` and `rawCert_exists_B48`.

Why a batch: every port of every call is owned by exactly one root visit (`occ_P`,
`owner_visit`), and `48 · 104 = 312 · 16`, so each call's price is shared by the 104 visits it
serves, and each root gathers its 16 visits into one target of high rank. The histograms that
result are the ones `Data/BaseUnit/Rate.lean` certifies (`pay_ok`, `tgt_ok48`).

Feeds: L (`rippleEngine_base`).

---------------------------------------------------------------------------------------------

## L. From the engine to the DFT

Files:
* `Transform/ReelCompile.lean`
* `Transform/EngineUse.lean`
* `Work/U7604/Chain/FourierTB/Main.lean`

What it proves.
* `ReelCompile.lean`: reels as RAM data (`film`, `treeT`, `Engrave`, `Play`, `Fen`): every reel
  of segment D up to `vandermondeReel` is engraved by a polynomial program (`publish`);
  the beat of a tensor of strokes reads its blocks and seats (`survey`, `AxisStroke`), and
  `mix_eq_patchRipple`: the mixing part of a beat is a ripple on each power-of-two block
  (`blockRipple`, `gleam_loc`, `patchRipple`).
* `EngineUse.lean`: `baseEngineExp = 1 - 7830588226951437/(2·10^18)`, the seam statement
  `RippleEngine z` (OpenAI's `hills_program` statement with `envelope z`), `rippleEngine_base`
  (segments H and K), `RippleEngine.mono`, and, for any engine, the programs
  `blockRipple_moves`, `BlockCover`/`StowedCover.patchRipple_moves`,
  `AxisStroke.mix_moves`/`beat_moves`, `AxisReels.run_moves`/`kron_moves`.
* `Main.lean`, in order:
  * `WHT`: the Walsh-Hadamard statement (`WHTProgram`, `goalExponent = 1 - 2/10^11`,
    `WHTTimeBounds`: `O(2^k (k+1)^goalExponent)` and `o(2^k k)`), `wal_eq_kernel`
    (`H^{⊗α} = (1-i)^{|α|} · diag(lum) · C^{⊗α} · diag(lum)`), `wal_ripple`, `wht_can`, `wht_main`,
    `wht_main_sharp`;
  * the sharp goal: `statedSavingTB19`, `decimalExponentTB19`, `TimeBoundsSharp`, `DFTGoalSharp`,
    `ConvGoalSharp`;
  * the CRT chart (`crtChart_moves`) and `AxisReels.freq_moves` (a DFT of length `N` from axis
    reels);
  * the axis data (`twoPowRoots`, `axisData`, `axisReels`) and `modulusFreq_moves_of_axes`;
  * fast powers (`shiftP`, `halveP`), `LenCtx`, `axisDFTCost`;
  * `budget`, `BudgetMoves`, `BluesteinCtx` (`chirp_moves`, `bluestein_moves`),
    `LenCtx.dft_moves_large`;
  * small lengths (`Dry.naive_freq`), `LenCtx.dft_moves`, `Nick.order_moves`, `Nick.dft_moves`;
  * convolution helpers (`convLen`, `padLine`, `freq_pad_conv`, `cross_moves`);
  * `CostWitness`, `stageCost`, `totalCost`, `assemble_program`, `dft_solve_program`,
    `conv_solve_program`, `dft_program`, `conv_program`;
  * `Timing`: `targetTime z n = n (log n)^z (log log n)^2`, `totalCost_isBigO`;
  * `baseEngineExp_lt_theta`, `timeBounds_of_exp`, `timeBounds_baseEngineExp`,
    `dft_program_of_engine`, `conv_program_of_engine`, `transform_main_order_sharp`,
    `transform_mainTB19`, `convolution_main_sharp`;
  * restored forms: `timeBounds_of_saving_le` (every saving `s ≤ 1957647056737859/(5·10^17)`),
    `transform_main_saving`, `convolution_main_saving`, `transform_main_order`, `transform_main`,
    `convolution_main`.

Why the engine is a hypothesis everywhere here: every lemma of the front end takes
`hE : RippleEngine z` as an argument, so the front end is proved once for all exponents, and the
only place a concrete exponent enters is `transform_main_order_sharp`, which plugs in
`rippleEngine_base`.

Feeds: `Race.bound` in `Submission.lean`.
-/
