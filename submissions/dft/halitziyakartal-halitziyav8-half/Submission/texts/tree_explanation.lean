/-!
written with help of ai↓

# Tree explanation: what the tree proves and how the proof flows, from `Race.bound` down

credits and notices: texts/credits.lean

This module has no code. Paths are relative to `Submission/`. The files one by one are in
`texts/code_explanations.lean`; build cost is in `texts/bottlenecks.lean`. Every name below is a
name of this tree, so a search for it lands on its definition.

Reading order: §1 the headline results, §2 the challenge statement and the machine, §3 the three
layers (templates, why 1/2 is the wall, the engine and the seam, the front end), §4 the chain of
named results, §5 the import graph and the files, §6 the namespaces, §7 the trusted part.

---------------------------------------------------------------------------------------------

## 1. The headline results

The public theorems are in `Submission.lean` (namespace `OAI.PowerSaving`, plus the two `Race.*`
theorems at top level); the template family and the engine bridge they rest on are in
`WalshTemplate.lean` and `EngineFromTemplates.lean`.

* `Race.bound` : there are `order solve W` with `DFTProgram order solve W` and
  `W n = O(n * (log n)^(1 - s))` for `s = 4999…9 / 9999…9`, a rational just below 1/2.
  With `D = 10^40 - 1` (the denominator) the numerator is `(D - 1)/2`, so `s = 1/2 - 1/(2D)`,
  just below one half.
* `Race.bound_base` : the same with `s = 389848144653 / 10^14` (about 0.0039, the previous
  entry's saving).
* `OAI.PowerSaving.RouteB.routeB_all s (hs : s < 1/2)` : the general form. Both `Race.*` theorems
  are `routeB_all _ (by norm_num)`.
* `OAI.Computability.NearSquareRoot.KernelPass.walshTemplate_above_half` (in `WalshTemplate.lean`) : for every rational
  exponent `num/den > 1/2` there is a `QCandidate` `t` with `t.Good num den`, that is a verified
  Walsh-type "template" plan whose number of child calls is below `rows * arity^(num/den)`.
  This is the source of the saving.
* The saving itself: `RouteB.templates_wall : TemplatesAbove templateWall := walshTemplate_above_half`
  (`templateWall = 1/2`), and `routeB_all` uses it. Given any family of templates above a wall
  `κ` (`RouteB.TemplatesAbove κ`, `0 ≤ κ < 1`) the theorems below give a DFT program with cost
  `O(n (log n)^(1-s))` for every `s < 1 - κ`. With `κ = 1/2` this is every `s < 1/2`.

Further theorems in `Submission.lean`, stated for any such `κ`:
* `transform_order_saving_of` : DFT program, the `O(n (log n)^(1-s))` bound, `o(n log n)`, and
  `O(paperTime)` when `κ < theta`; plus `run order n = workModulus n < 8 n^3`.
* `convolution_order_saving_of` : the same for linear convolution (`ConvProgram`, length `2n-1`).
* `WHT.wht_exp` : Walsh–Hadamard transform on `2^k` points in `O(2^k (k+1)^z)` and `o(2^k k)`
  for every `z` in `(κ, 1)`.

## 2. The challenge statement and the machine

`Submission/Goal.lean` holds the statement: `root n = exp(2πi/n)` (`ExactFourier.zeta`),
`dft n x j = Σ_k root n^(j k) x_k`, the program types
`dftInKind = w × ℂ (scalar) × Tape ℂ (left paint)` and `dftOutKind = Tape ℂ`.
`DFTProgram` is OpenAI's definition (`Goal.lean`; full name and term unchanged). For every `n > 0`:

* `order` runs on `n` alone and returns a number `d` with `0 < d < 1024 n^3`, polynomially bounded
  work and peak, and a valid run;
* `solve` then runs on `(n, root d, x)`, where `root d = exp(2πi/d)` is handed to it as an input,
  and must return `dft n x` exactly, with a valid run and a peak under the polynomial cap
  `(n+2)^cBound`;
* the total work `d.work + 1 + result.work` is at most `W n`.

The machine is `RAM.lean` (reached declarations unchanged): `Tape`, value types `Ty` (`w` words,
`c` complex with a `Paint` tag, pairs `p`, arrays `a`), `Bill` (value, work, peak, validity),
atoms (`Atom`: word arithmetic, complex add/sub/scale/inv, `cross` only when allowed, `len`,
`look`), and `Code` with `comp`, `fork`, `ifz`, `loop`, `tab`, `sow`, `importClosed`, `call`,
`descend`. `descend` is depth-bounded recursion through a handler port (`depthRun`).

Two of its rules shape the whole tree:

* values are *painted*: the input vector is `left`, constants such as the root are `scalar`.
  `scale` multiplies a scalar by any value, `add`/`sub` combine values of one paint, and the only
  product of two non-scalar values is `cross`, allowed only in convolution programs (`Prog true`).
  So a DFT program is a linear computation in the data with scalar coefficients.
* work is counted per constructor (`Code.run`), and index arithmetic on words costs the same as
  complex arithmetic, so every table, layout and loop counter in the proof is paid for.

## 3. Flow from the statement to the engine, the templates and the front end

The proof has three layers: templates (3a, with the reason for the wall in 3b), the engine that
turns a template into a fast ripple (3c), and the front end that turns a fast ripple into a fast
DFT (3d).

### 3a. Templates (pure linear algebra over `ℚ`): `WalshTemplate.lean`
* `QPlan A i o` is a tiny plan language on rows of `Addr A h = Fin h → Column A`
  (`Column A = Fin A → Fin 2 → ZMod 2`): `mix`, `perm`, `scale`, `child` (one call of the
  2-point Walsh kernel on one axis), `seq`, `parallel`. `QPlan.eval` gives its matrix,
  `QPlan.calls` counts `child` calls, `QCorrect p` says `p.eval h = target A W h` (the Walsh
  transform `walshCol` applied coordinatewise, on every row) for every `h`.
* `QCandidate.Good num den` : `5 ≤ arity`, `2 ≤ rows`, correct, and
  `calls < rows * arity^(num/den)`.
* The construction: `template_correct` rewrites the Walsh kernel as
  `diag(qtot) · (W · diag(qtot) · W) · diag(qtot) · swap` (`walsh_of_WDW`, `query_pairs`), so it
  is enough to build the diagonal "sign" operator `specR (fun v => (∏ qtot) • 1)`.
  That operator is built by `horner_template` as a polynomial (`upred`, Horner form `hornerP`) in a
  routed "shift" stage (`routed`, `liftCh`, `liftFr`, `shift_stage_spec`), then fixed up on the
  few bad rows by `repairOut` / `division_repair_mat` using a Vandermonde left inverse
  (`intNodes_leftInverse`).
  On a window `u ≤ cnt ≤ u + D` the parity is a polynomial of degree `D` in `cnt`
  (`upred_exact`), evaluated by Horner steps (`hornerP`); one step applies "the sum of all
  queries" once (`hornerPb_spec`).
* The bad-row count is bounded by a Chernoff-type window count (`window_count`,
  `window_fraction`, `shift_count`, `pencilOrder`): `D = 2·pencilOrder M ≈ 2√(32 M log M)` leaves
  a fraction at most `1/(2M³)` of the rows outside (`window_params`, `window_fraction`).
* The routing pieces: charged rectangles (`ChRect`, `charged_routed`, `comQ`) and free cut
  rectangles (`CutRect`, `free_hfr`, `free_geom`, `free_kernel`) with the weight identity
  `label_identity_even` (built from `gch`, `Pch`, `Gint`).
  Why labels and rectangles: one stage "sum of all queries on every row" would cost
  `2M` calls per row. Labels (words of length `L = 4n` over `2^b` letters) and two kinds of
  rectangles make it cost a power of `q = 2^b` per row: *charged* rectangles share one common
  query transform between rows that agree on a set of positions (`ChRect`, `charged_routed`), and
  *free* rectangles connect rows that differ at cut positions through a factorisation with no
  calls in the middle (`CutRect`, `free_kernel`, `free_geom`, `free_hfr`). The rational weights
  `gch` make the weighted rectangles sum to the identity (`label_identity_even`). `routed_calls`
  bounds the calls of a stage.
* `template_of_routing` assembles one candidate; `templates_of_rate` picks parameters
  (`params_rate_side`, `pq`, `pL`, `pN`, `pm`, `pD`, `pA`) and checks the call count
  (`calls_le`); `walshTemplate_above_half` covers every exponent above 1/2 (`rateOK_of_half`).
* The count and the wall: `calls_le`: total calls `≤ q^(n+5)` per row, against arity `≥ q^(2n)`
  (`params_rate_side`), so the rate exponent is `(n+5)/(2n) → 1/2`. `RateOK θ` is the one
  numeric condition (`∃ n, n + 5 < 2nθ`), true for every `θ > 1/2` (`rateOK_of_half`).

### 3b. Why 1/2 is the wall

Formally the exponent 1/2 enters through `RateOK`: the calls per row are at most `q^(n+5)` and
the arity is at least `q^(2n)`, so the rate exponent `(n+5)/(2n)` tends to 1/2 from above and
never reaches it. Behind the `n + 5` is the predictor: its degree must cover the spread of `cnt`
over the shifts, which is the standard deviation of a sum of `M` signs, about `√M`; that is why
there are about `√(M log M)` stages, each costing a fixed power of `q` per row, against an arity
of about `2M`.
`RouteB.templateWall = 1/2` records this; `templates_wall` is `walshTemplate_above_half`. The chain after it is
parametric: a template family above a smaller wall, proved as a new `templates_wall`, would move
every theorem of `Submission.lean` with it. Reaching `s = 1/2` exactly would need a wall strictly
below 1/2, because of the strict steps at the seam (end of §3c).

### 3c. The engine (recursive ripple): `PlanToWord.lean`, `EngineMoves.lean`, `EngineSetup.lean`, `EngineRecursion.lean`, `EngineCost.lean`,
`EngineFromTemplates.lean`
* `PlanToWord.lean` translates a correct `QPlan` into a word of RAM-level moves `Script`
  (`toWord`, `realise`, `unitWord`, `unit_live`) whose block moves have rank 2 and number
  `t.program.calls` (`unitWord_ranks`). The bundle is `PlanUnit t`.
  - `toWord` maps each instruction to moves on its own scratch roles (`Roles`): `mix` to one
    `Move.mix`, `perm` to a copy and a `perm`, `scale` to its Fourier expansion over parity vectors
    (copies, one `sgn` each, one recombining mix), `child` to a rank-2 `kern` between phase
    moves.
  - The template's child and target are the real ±1 Walsh matrices; the engine's block and target
    are the complex kernel. `child_col` and `rippleMat_col` are the two identities between them (the
    kernel is the Walsh matrix between phases `phaseI`), and `unitWord` wraps the plan's word in the
    phase moves `preZ`, `postZ`.
* `EngineMoves.lean` holds the binary-space linear algebra (`Binary.*`: `rippleMat`, `ripple`, `Cleave`,
  `blockMat`, `Cleave.adapted`), the move language `GenMove.Move` / `Script.exec`, the bit-address
  machinery (`BitCtx`, `RoleTapeCtx`, ferry lemmas) and the direct ripple
  `naive_high_can` (work `2^k (2k+1)`). It also defines `envelope z k = ⌈(k+1)^z⌉`.
  Free moves cost one pass over the data: rational mixes of roles (`mix`), additive
  permutations of `Space α` (`perm`), phases along a linear functional (`phase`) and phases by any
  Boolean function (`sgn`). A *block* `kern l r z` is a ripple of rank `r` along `r`
  independent directions on role `l`; it is the only paid move, and the engine pays it by a
  recursive call on fewer bits.
* `EngineSetup.lean` and `EngineRecursion.lean` build `SlotEngine`: one job class (`EJob.cls`) runs the
  move word on a layout of bit tapes (`class_able`), block moves become
  child jobs (`moveKids`, `leafKids`), top jobs batch them (`top_able`, `tree_able`), and
  `EngineRecursion.closed_of_body` / `RealisesRule.answers` close the recursion through `Code.descend`.
  The two kinds of job go through one recursive port (`EJob`):
  - `⟨false, n, B, v⟩`: ripple each of `B` vectors of `n` bits. If `n` is below a cutoff or `B < W`, do
    it directly (`naive_can`). Otherwise take the vectors `W` at a time; each group is one class
    job with letter width `μ = n / m`, which ripples the low `m·μ` bits (`partRip`), and the remaining
    `n mod m < m` high bits are finished by a direct pass (`rippleHigh_moves`, from `hhigh_eq_ws`).
  - `⟨true, n, μ, J⟩`: load the `W` vectors onto the `W` live roles of the unit, as functions on
    `μ` letters of `Space α` (`load_can`, `slotPlace`); run the word move by move. A free move is one
    pass (`free_able`). A block of rank `r` becomes one child top job on `r·μ` bits with
    `2^(n - r·μ)` vectors (`move_able`). Then unload (`drain_can`, `unload_rack`).

  Since `r < m`, a class job on `n` bits calls top jobs on at most `(r/m)·n` bits: the size falls
  geometrically. All jobs are one RAM type because the machine has exactly one recursion construct
  with one port; `closed_of_body` closes the open body `body_able` by bounded descent on a rank.
  `RealisesRule.ripple_engine` then is one top job: `W` copies of the input vector.
* `EngineCost.lean` (`EngineCost.Rule`, `budget_exists`) solves the cost recurrence: if
  `P * r^z1 ≤ W * m^z1`, then for every `z` with `z1 < z ≤ 1` (and `0 ≤ z1`) there is a cutoff
  `N ≥ n0` and a constant `C` for which the budget `J` pays for every step at cutoff `N`.
  The proof takes `J n = C 2^n ⌈(n+1)^z⌉` and checks the recurrence for large `n`: the children
  contribute `P (k r)^z ≤ λ · W · n^z` with `λ = (r/m)^(z - z1) < 1`, and the strict gap pays for
  every lower-order term.
* `SlotEngine.RealisesRule.ripple_engine` gives the engine bound, and `EngineFromTemplates.lean` packs it as
  `RippleEngine z` (defined in `ReelCompile.lean`): a closed program computing
  `ripple k v` (the 2^k-point twisted Walsh kernel) in work `2^k * envelope z k`.
  `rippleEngine_of_planUnit`, `planUnitOf`, `rippleEngine_of_good`,
  `exists_good_below`, `rippleEngine_of_templates` lead from `TemplatesAbove κ` to
  `RippleEngine z` for every `z ∈ (κ, 1]`.
  `planUnitOf` packs the translated plan as a `PlanUnit`, and `PlanUnit.engine` as a `SlotEngine`
  with `W = rows`, `m = 2·arity`, `P = calls`, `r = 2`. The template's rate
  `calls < rows · arity^θ` is the engine's `P · 2^θ ≤ W · (2·arity)^θ` (`rate_of`).
* The seam. `RippleEngine z` is the only thing the front end knows about the engine, and the only
  thing the engine has to deliver. `RouteB.rippleEngine_of_templates` delivers it for every `z`
  above the wall: it picks a rational `num/den` strictly between `κ` and `z`
  (`exists_good_below`), takes a template that is `Good` at `num/den`, turns it into a unit
  (`planUnitOf`) and runs the engine with `z1 = num/den < z`. Both steps are strict (`κ < num/den`,
  `num/den < z`), and the timing step is strict once more (`z < 1 - s`); this is why the theorem
  reaches every `s < 1/2` but not `s = 1/2`.

### 3d. The front end (DFT from ripples): `CostCalculus.lean`, `DFTIdentities.lean`, `BinaryKernel.lean`,
`ReelKit.lean`, `WorkModulus.lean`, `ReelCompile.lean`, `DFTPrograms.lean`

**What it receives:** `hE : RippleEngine z` (`ReelCompile.lean`) for some `0 ≤ z ≤ 1`: for every
batch of inputs, a RAM program computing `ripple k v = rippleMat (Fin k) *ᵥ v` in work
`2^k · envelope z k`, with `envelope z k = ⌈(k+1)^z⌉`. Here `rippleMat = digitProd littleC` is the
`k`-fold tensor power of the 2×2 matrix `littleC = [[ca, cb], [cb, ca]]`, `ca = (1+i)/2`,
`cb = (1-i)/2` (`BinaryKernel.lean`). Done directly the ripple costs `2^k (2k+1)`
(`naive_high_can`, `EngineMoves.lean`).

**What it proves:** `dft_program` and `conv_program` (`DFTPrograms.lean`): programs whose work is
`totalCost`, and (`bounds_of_exp`) `totalCost = O(n (log n)^p)` for every `p > z`.

The files:
* `CostCalculus.lean` is the program-building calculus: `Bill.OK`, `Small`, `Dom`, `Able`/`Can`
  (programs with a cost bound, in a bank / closed), `PolyCan`, `Bench` (an input bench with
  `Moves`, `PolyMoves`, `Computes`, `WordIn`, `FreeWord`, `PolyWord`, `FreeReads`, `PolyReads`, `Decides`), layouts
  (`Layout`), and `DigitArith`.
* `DFTIdentities.lean` proves the algebra: inverse DFT (`freq_inv`), convolution theorem
  (`freq_cyclic`, `cyc_formula`), Bluestein (`bluestein_freq`), radix-2 split (`freq_eo`),
  Toeplitz inverse (`toeplitzInv`, `toeplitzInv_left_inv`) and the Vandermonde factorization
  `rootVandermonde_factor`.
* `ReelKit.lean` builds "reels" (`Reel`, `Stroke`): straight-line programs of permutations,
  diagonal scalings and 2x2 butterflies, with FFT (`fftReel`, `fftReel_go`), cyclic convolution
  (`cyclicConvReel`, `conv_acts`), Toeplitz doubling reels (`toeplitzReel`, `toeplitzReel_go`) over grid
  reels (`toeplitzGridReel`) and `vandermondeReel_creates`. It also has `AxisTensor` (mixed-radix
  CRT index `crtIndex`, `crtIndex_reloc`, `crt_freq`, `axisRun_eq_kron`) and the power-of-two block
  cover (`PowBlockCover`, `strokeBlocks`, `strokeBlocks_cover`).
* `WorkModulus.lean` picks the axes: `modulusAxes n` = greedy odd primes plus a power of two,
  with `2n ≤ vol < 4n` (`modulusAxes_spec`); `workModulus n` (`workModulus_bound`: `< 8 n^3`);
  `LenCtx`, `PrimeListIn` and the RAM programs that compute them.
* `ReelCompile.lean` has `ReelComputes` (a reel whose strokes are computable in polynomial time), `reelTape`,
  `reelBlocksT`, and `vandermondeReel_blocks`, which writes the tree tapes; it runs one Kronecker step per beat with the
  ripple engine doing the 2x2 parts (`cover_ripple`, `AxisStroke.step_moves`,
  `AxisReels.kron_moves`, `engine_tab`).
* `DFTPrograms.lean`: `AxisReels.freq_moves` (CRT gather, per-axis Vandermonde reels, scatter),
  `modulusFreq_moves_of_axes`, Bluestein on top (`BluesteinCtx.bluestein_moves`), the small-n
  naive DFT (`PolyMoves.naive_freq`), the case split (`LenCtx.dft_moves`), and the final programs
  `dft_program`, `conv_program`, `hadamard_exp`. `Timing.*` proves the asymptotics
  (`budget_isBigO`, `totalCost_isBigO`), and `bounds_of_exp`, `exists_exp`, `theta_lt_one`
  turn them into the stated bounds.

**Why it is built this way.** A DFT program may only take linear combinations with scalar
coefficients. The front end rewrites the DFT, step by step, into a long product of very simple
linear maps, until the only expensive map left is the ripple.

(a) *The length.* Bluestein (`DFTIdentities.lean`, `bluestein_freq`): a DFT of length `n` is a
cyclic convolution of length `N ≥ 2n` between chirps `z^(i²)`. `N = (modulusAxes n).vol` is a
product of distinct odd primes and one power of two with `2n ≤ N < 4n` (`modulusAxes_spec`,
`WorkModulus.lean`). A product of coprime factors lets the Chinese remainder theorem split one
DFT of length `N` into a tensor product of small DFTs, one per *axis* (`crt_freq`, `CoprimeAxes`,
`ReelKit.lean`). There are at most `axisBudget n = log₂(2n) + 1` axes, each of size at most
`2^axisLogBound n = O((log n)^2)`; enough primes exist by a central-binomial count
(`oddPrime_count_ge`).

(b) *The order and the root.* For large `n`, `workModulus n = 2n · N · 2^axisLogBound n`; for the
small `n` (`¬ IsLargeLen n`) it is `n` itself and the DFT is the direct sum (`PolyMoves.naive_freq`).
`workModulus n < 8 n^3` (`workModulus_bound`). `solve` is handed only `root d`; since `2n`, `N`, every
axis size and every needed power of two divide `d`, every root it needs is a power of that one
root, computed by square-and-multiply (`powByBits`).

(c) *One axis.* An axis DFT is a Vandermonde matrix on a root. It is factored as `L · D⁻¹ · Lᵀ`
with Toeplitz factors (`rootVandermonde_factor`, `DFTIdentities.lean`) and written as a *reel*
(`vandermondeReel`, `ReelKit.lean`): a list of *strokes*, each a permutation with a diagonal
scaling (`ix`, `dye`) followed by `littleC` on disjoint pairs of positions (`partner`). It has
`vandermondeBeats e = 2·toeplitzBeats e + 7 = O((e+1)^2)` strokes, `e = axisLogBound n = O(log log n)`.
The reel works *in place* on the axis' own `r` positions, because the tensor structure leaves no
workspace; that is why the Toeplitz products are done by a halving recursion with borrowed zones
(`toeplitzReel`, `toeplitzBridge`, `Acts.conjugateReel`) and not by a padded convolution.

(d) *All axes at once.* The axes run in lockstep, beat by beat (`axisRun_eq_kron`). On the tensor
product one beat is a permutation with scaling on all `N` entries (cost `N`, `perm_moves`) and a
mixing step that is a tensor product of `littleC` pairs across the axes. Regrouped into
power-of-two blocks (`strokeBlocks`, `PowBlockCover`, `strokeBlocks_cover`), the mixing step is on each
block a ripple on at most `l` bits (`idxApply_eq_blockAtRipple`). `cover_ripple` runs the engine once per
block; one beat costs `N · envelope z l`, and the whole transform
`axisDFTCost = (vandermondeBeats + 1) · N · envelope z l`. With `l = O(log n)` and
`O((log log n)^2)` beats this is `O(n (log n)^z (log log n)^2)`. Around it, `gather_moves` and
`spread_moves` relabel the table by the CRT index (`crtIndex`).

(e) *The programs.* Every step above is a RAM program built in the cost calculus of `CostCalculus.lean`
(`Can`, `Able`, `Bench.Moves`, with polynomial word bounds). The reels themselves are data the
program must produce: `ReelCompile.lean` shows that every reel up to `vandermondeReel` has strokes
computable in time polynomial in `log n` (`ReelComputes`), and `vandermondeReel_blocks` turns them into tables.
`assemble_program` joins the order program and the solve program under one cap `(n+2)^c`.

(f) *The timing.* `totalCost_isBigO`: `totalCost = O(targetTime z)` with
`targetTime z n = n (log n)^z (log log n)^2`. `bounds_of_exp` turns that into `O(n (log n)^p)`
for any `p > z` (the strict gap absorbs `(log log n)^2`), `o(n log n)`, and `O(paperTime)` when
`z < theta`.

Convolution (`conv_program`) reuses the chain: pad to `2n-1`, two forward DFTs, one `cross`
product, one inverse DFT. The Walsh-Hadamard transform (`walsh_tab`, `wht_moves`) is one block
ripple between two weight tables (`walsh_eq`).

## 4. Where each step lives (chain of named results)

1. `walshTemplate_above_half` (WalshTemplate) → `templates_wall` (EngineFromTemplates).
2. `rippleEngine_of_templates` (EngineFromTemplates) ← `exists_good_below`, `rippleEngine_of_good`
   ← `rippleEngine_of_planUnit` applied to `planUnitOf` (← `unit_live` (PlanToWord) ← `realise`,
   `rowSum_correct`, `rippleMat_col`); `rippleEngine_of_planUnit` ← `SlotEngine.RealisesRule.ripple_engine`
   (EngineRecursion) ← `RealisesRule.answers` (← `closed_of_body` ← `body_able` ← `top_able`,
   `class_able`) and `budget_exists` (EngineCost).
3. `dft_program` (DFTPrograms) ← `dft_solve_program` ← `FreeWord.dft_moves` ← `LenCtx.dft_moves`
   ← `LenCtx.dft_moves_large` ← `bluestein_moves` ← `modulusFreq_moves`
   ← `modulusFreq_moves_of_axes` ← `freq_moves` (= `gather_moves` ; `kron_moves` ;
   `spread_moves`); `kron_moves` (ReelCompile) ← `AxisStroke.step_moves` (= `perm_moves` ;
   `cover_ripple`) ← `engine_tab` (uses the `RippleEngine`).
   Beside it: `assemble_program` (the order program and the solve program under one cap) and,
   for small `n`, the branch `PolyMoves.naive_freq`.
4. `bounds_of_exp` (DFTPrograms) ← `totalCost_isBigO` ← `budget_isBigO` ← `axisDFTCost_le`,
   with `envelope_lim` giving the `(log n)^z` factor.
5. `transform_order_saving_of` (Submission.lean) combines 2–4; `routeB_all` instantiates
   `κ = 1/2`; `Race.bound`, `Race.bound_base` instantiate `s`. `exists_exp` picks `z` with
   `κ < z < 1 - s`.

So the tree is three constructions stacked on one finite object:

1. a *front end* that turns "a ripple on `k` bits costs `2^k · envelope z k`" into "a DFT of length
   `n` costs `O(n (log n)^z (log log n)^2)`";
2. an *engine* that turns "a finite unit with `P` paid blocks of rank `r` and `W` rows of rank `m`,
   where `P · r^z1 ≤ W · m^z1`" into "a ripple on `k` bits costs `O(2^k (k+1)^z)`" for `z > z1`;
3. a *template family* that, for every rational `θ > 1/2`, builds such a unit with rate exponent
   `θ` (rows `W`, arity `A`, calls `< W · A^θ`), and a translation of templates into units.

The front end never sees the template; the template never sees the DFT or the RAM.

## 5. Import graph (17 modules; Mathlib imports omitted)

```
RAM            : (Mathlib.Basic.Complex.Basic only)
Goal           : RAM
BinaryKernel  : RAM
CostCalculus           : RAM
DFTIdentities  : Goal
EngineCost     : (Mathlib only)
WalshTemplate       : (Mathlib only)
ReelKit        : BinaryKernel, CostCalculus, DFTIdentities
EngineMoves          : BinaryKernel, CostCalculus, DFTIdentities
WorkModulus    : ReelKit, CostCalculus
EngineSetup          : EngineMoves, CostCalculus
PlanToWord    : WalshTemplate, EngineMoves
EngineRecursion          : EngineSetup, EngineCost
ReelCompile    : CostCalculus, EngineMoves, ReelKit, EngineSetup
DFTPrograms        : Goal, ReelCompile, WorkModulus
EngineFromTemplates   : PlanToWord, EngineRecursion, ReelCompile, WalshTemplate
Submission     : EngineFromTemplates, DFTPrograms
```
`WalshTemplate` and `EngineCost` import no tree module, so they can build first in parallel with
`RAM`. The longest chain is RAM → CostCalculus/BinaryKernel → (Goal → DFTIdentities) → ReelKit /
EngineMoves → EngineSetup → ReelCompile → DFTPrograms → Submission (a chain of the import graph; see
bottlenecks for timed chains).

What each file holds:
* `RAM.lean`, `Goal.lean`: the machine and the statement (OpenAI's, reached part).
* `CostCalculus.lean`: tape and digit lemmas, layouts, the cost calculus, layout and integer programs,
  benches.
* `DFTIdentities.lean`: inverse DFT, cyclic convolution, Bluestein, Toeplitz, the Vandermonde
  factorisation.
* `BinaryKernel.lean`: digit-wise matrix products, the binary kernel and its conjugation by Walsh.
* `EngineCost.lean`: the engine's cost recurrence (pure arithmetic).
* `WalshTemplate.lean`: the template family `walshTemplate_above_half` (pure mathematics over ℚ).
* `EngineMoves.lean`: bit layouts, the direct ripple, bit and role contexts, splits, engine moves.
* `EngineSetup.lean`: doubling tables, weight tables, masks and placements, jobs, `SlotEngine`, class
  setup.
* `EngineRecursion.lean`: the class job, the top job, the recursion and `ripple_engine`.
* `PlanToWord.lean`: plan ⇒ engine word (`unit_live`).
* `ReelKit.lean`: strokes, reels, the in-place FFT/convolution/Toeplitz/Vandermonde reels, axis
  tensors, block covers, CRT.
* `WorkModulus.lean`: the modulus (primes, axes, `workModulus`) and its programs.
* `ReelCompile.lean`: reels as computable tables (`ReelComputes`, `vandermondeReel_blocks`), axis strokes,
  `RippleEngine`, `cover_ripple`, `kron_moves`.
* `EngineFromTemplates.lean`: template family ⇒ `RippleEngine`.
* `DFTPrograms.lean`: Walsh-Hadamard, the axis transform, Bluestein, the programs, the timing.
* `Submission.lean`: the public theorems.

## 6. Namespace map

* `OAI.PowerSaving.RAM` (machine, calculus, engine, front end), `OAI.PowerSaving.Binary`,
  `GenMove`, `RoleKernel`, `Spectral`, `ReelKit`, `AxisTensor`, `Modulus`, `EngineCost`,
  `EngineRecursion`, `WeightTable`, `WHT`, `Timing`, `RouteB`, `DigitArith`.
* `OAI.Computability.NearSquareRoot.KernelPass` (and `.Free`): the template layer.
* `OAI.ExactFourier.zeta`: the root of unity of the statement.

## 7. The trusted part and the checked part

* Trusted: Lean's kernel and the axioms `propext`, `Classical.choice`, `Quot.sound`. The axiom
  report of `Race.bound`, `Race.bound_base`, `routeB_all` and `walshTemplate_above_half` lists exactly these, and
  the statement itself already needs all three (the type `Real` depends on them).
* The statement: `RAM.lean` and `Goal.lean`. Every constant the type of `Race.bound` reaches has
  its full name and its term unchanged from OpenAI's files; the files hold only these
  declarations, and `Tape.sow` (unreached, kept because `Bill.steps` reuses its matcher).
* There is no `sorry` and no `native_decide` in the tree, and no generated data: every proof is
  elaborated from source.
* The `private theorem marker_…` lines (in `DFTPrograms.lean` and `ReelCompile.lean`) are the
  author's notices; each proves `True`.
-/
