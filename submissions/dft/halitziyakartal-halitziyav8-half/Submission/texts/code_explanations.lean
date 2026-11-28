/-!
written with help of ai↓

# Code explanations: one section per code file

credits and notices: texts/credits.lean

This module has no code. For each file of the tree it says what the file provides, the main
statements in words, the ideas that make the proofs work, and who uses it. The flow through all
files is in `texts/tree_explanation.lean`; build cost is in `texts/bottlenecks.lean`. Paths are
relative to `Submission/`; every name below is a name of this tree.

Common points. Every file except `RAM.lean`, `Goal.lean` and `Submission.lean` has
`set_option linter.all false` after its imports. Most files wrap their content in plain
`section … end` blocks and reopen the same namespaces several times; a file with several parts
marks them with `===== begin … =====` / `===== end … =====` comments.

Files, in the order the proof is built:

* `RAM.lean`, `Goal.lean`: the machine and the statement
* `CostCalculus.lean`: tapes, layouts, the cost calculus, benches
* `DFTIdentities.lean`: algebra of the DFT
* `BinaryKernel.lean`: the binary kernel
* `EngineMoves.lean`: bits, the direct ripple, contexts, splits, moves
* `EngineSetup.lean`: tables, masks and placements, jobs, the block engine's data
* `EngineCost.lean`: the cost recurrence
* `EngineRecursion.lean`: the engine
* `WalshTemplate.lean`: the template family
* `PlanToWord.lean`, `EngineFromTemplates.lean`: template ⇒ unit ⇒ ripple engine
* `ReelKit.lean`, `WorkModulus.lean`: reels, axes, the modulus
* `ReelCompile.lean`: reels as programs; the use of the engine
* `DFTPrograms.lean`: the transforms and the timing
* `Submission.lean`: the public theorems

## Submission.lean
Role: the top theorems.
* `WHT.wht_exp` : WHT program, `O(2^k (k+1)^z)` and `o(2^k k)`, for `z ∈ (κ,1)`.
* `transform_order_saving_of` : DFT program with `O(n log^(1-s) n)`, `o(n log n)`,
  `O(paperTime)` if `κ < theta`, and the modulus facts.
* `convolution_order_saving_of` : the same for `ConvProgram`.
* `RouteB.routeB_all` : every `s < 1/2`, from `templates_wall`.
* `Race.bound_base`, `Race.bound` : the two race statements, outside any namespace.
Imports: `EngineFromTemplates`, `DFTPrograms`. Used by: nothing (root).
Unusual: `Race.bound` carries 40-digit numerals checked by `norm_num`.
The comment blocks before the imports are the headers of the earlier entries of this line, kept
as the record of where the tree came from.

## Submission/RAM.lean
Role: the machine model of the challenge (`Tape` in `OAI.PowerSaving`; `Ty`, `Bill`, `Atom`,
`Code`, `run` in `OAI.PowerSaving.RAM`). OpenAI's exact computational model, reduced to what the
type of `Race.bound` reaches.
* `Tape`, `Tape.tab`, `Tape.look`, `Tape.set`, `Tape.sow` : finite arrays and writes.
* `Paint`, `Ty`, `Ty.T`, `Ty.blank` : value types; `sc = c .scalar`.
* `Bill`, `Bill.pay`, `Bill.pass`, `Bill.one`, `Bill.word`, `Bill.steps`, `Bill.sow`,
  `Bill.tab` : cost accounting (value, work, peak, validity).
* `NOp`, `Atom`, `Atom.run` : primitive operations; `Atom.cross` needs `allow = true`.
* `Port`, `Code`, `Handler`, `depthRun`, `Code.run`, `Prog`, `run` : programs and their semantics.
  `descend` is the one recursion construct: bounded-depth recursion through a single port
  (`depthRun`).
Imports: `Mathlib.Basic.Complex.Basic` (as written in the file). Used by: `Goal`, `CostCalculus`,
`BinaryKernel`, and through them everything.
Why it matters downstream: `inv` is valid only on a nonzero scalar; `cross` needs the flag
`allow = true`; every word produced must stay below a polynomial cap; and there is exactly one
port for recursion.

## Submission/Goal.lean
Role: the challenge statement.
* `ExactFourier.zeta`, `root`, `Vec`, `dft`, `dftInKind`, `dftOutKind`, `DFTProgram`.
Imports: `RAM`, Mathlib trigonometry. Used by: `DFTIdentities`, `DFTPrograms`.

## Submission/CostCalculus.lean
Role: the general program-building calculus.
* `Tape.look_of_lt`, `ext_look`, `look_tab`, `sow_look_written`, `sow_tab` : tape facts.
* macro `ar` : `omega`, or `ring_nf; omega`.
* `Bill.OK` and its rules (`mono`, `pay`, `pass`, `tick`, `steps_ok`, `sow_ok`, `tab_ok`).
* `Small B F` (polynomially bounded), `Dom W F` (linearly dominated), with algebra lemmas.
  `Small B F`: `F i ≤ (B i + 2)^d` for some `d`, closed under `+`, `*`, powers, composition.
  `Dom W F`: `F i + 1 ≤ C (W i + 1)`.
* `Bank`, `Able` (program with cost `C*(W+1)+Z` and peak `cap`), `Can` (closed `Able`),
  `During`, and the combinators `Able.comp/fork/save/ifz/loop/tab/sow`, `Can.*` mirrors
  (`pipe`, `pair`, `bind`, `look`, `len`, `wadd`…`wlt`, `branch`, `loop`, `tab`, `sow`).
  The point of the indexed family: one program, one constant `C`, one degree `d` for all inputs
  at once.
* `Can.Within`, `PolyCan` (cost polynomial in a size `S`), `Can.toPoly`, `Code.inert`.
  The `PolyCan` rules (`lift2`, `testz`) take the sum of the degrees.
* `DigitArith` (`div_join`, `mod_join`, `lt_join`, `split3_*`).
* `Layout` (bijective indexing of a finite type, `pair`, `vecFin`, `digits`, `digits_code`).
* Layout programs (`Able.layout`, `Can.layout`, `Can.fetch`, `Can.cases_code`, `Can.sum_*`),
  `log_step`, `Can.logC`, `Can.wTwo`, `Can.natC`, `Can.rat`, `Can.addr_join/high/low`.
  `Can.layout` fills an array along a layout, `cases_code` branches on a finite code, `wTwo`
  computes powers of two, `logC` the binary logarithm, `rat` a rational constant, and
  `addr_join`/`addr_high`/`addr_low` addresses in a pair layout.
* `Bench` with `Moves`, `PolyMoves`, `Computes`, `WordIn`, `FreeWord`, `PolyWord`, `FreeReads`, `PolyReads`,
  `along`, `extend`, `scan`, `climbs`, `loopPoly`, `tabPoly`, `tab`, `loop`, `arrayM`,
  `arrayNow`, `scatterNow`, `repeatM`, `FreeWord.logM`, `FreeWord.numeralM`, `Decides`, `branchM`,
  `branchN`, `iteN`.
  `Bench m ι` is a size, a tray type and an environment. `Moves W t f` is `Can` from the
  tray; `PolyMoves S` and `Computes` are the polynomial versions; `FreeWord` is "a word known at zero cost and
  small"; `WordIn`/`PolyWord` the polynomial ones. `FreeReads` and `PolyReads` move facts between benches
  (`along`, `extend`, `scan`, `climbs`). `arrayNow`, `scatterNow`, `repeatM`, `loopPoly`, `branchM`
  are the loop and branch rules in this vocabulary.
Imports: `RAM`, small Mathlib pieces. Used by: `EngineMoves`, `EngineSetup`, `ReelKit`, `WorkModulus`,
`ReelCompile`.

## Submission/BinaryKernel.lean
Role: basic linear algebra for binary spaces.
* `digitProd` (coordinatewise Kronecker product) with `_apply`, `_diagonal`, `_one`, `_mul`,
  `_smul`, `prod_ite_eqs`, `prod_delta`.
* `Binary.F = ZMod 2`, `Space`, `bit_cases`, `dot`, `eu`, `sign`, `phaseI`, `phaseProd`, `littleH`,
  `ca`, `cb`, `littleC`, `rippleMat`, `walshMat`, `walshConj` (conjugation by the Walsh matrix),
  `walshConj_phaseProd` (the kernel is the Walsh conjugate of the `phaseProd` diagonal), `shift`, `dir`, `dir_phase`.
* `ReelKit.sum_blocks`.
The idea: `walshConj f = 2^{-n} · walshMat · diag f · walshMat`. Then `walshConj_phaseProd : walshConj phaseProd = rippleMat` (the kernel
is diagonal in the Walsh basis, with eigenvalues the products of `phaseI`), and
`dir_phase : dir z = walshConj (phaseI (dot z ·))`: one direction of the kernel is `ca·1 + cb·shift z`.
So products of directions are easy to handle (`walshConj_mul`).
Imports: `RAM`, Mathlib (ZMod field, central binomial factorization, matrices). Used by:
`EngineMoves`, `ReelKit`.

## Submission/DFTIdentities.lean
Role: DFT algebra over `ℂ` (namespace `Spectral`).
* `freq`, `rootVandermonde`, `front`, `root_primitive`, `root_four`, `root_factor`,
  `power_mod`, `conj_of_root`, `char_orth`, `freq_inv` : inverse DFT.
* `predAt`, `cyclic`, `cyc_reindex`, `freq_cyclic`, `cyc_formula` : convolution theorem.
* `sum_range_pairs`, `freq_eo`, `freq_eo'`, `even_prim` : radix-2 split.
* `signedRoot`, `chirp`, `chirpSeed`, `chirpFilter`, `chirp_pair`, `chirp_cyclic`,
  `bluestein_freq` : Bluestein.
* `dft_front`, `extendLine`, `front_exact` : link to `Goal.dft`.
* `rise`, `lowerToeplitz`, `gap`, `roof`, `floorH`, `vandDiag`, `vandLower`, `toeplitzApply(T)`,
  `toeplitzInvUpTo`, `toeplitzInv`, `toeplitzInv_left_inv`, `newtonBasis`, `newtonBasis_eval`, `rootVandermonde_factor` :
  Toeplitz inverse and an LDLᵀ-type factorization of the root Vandermonde matrix.
In words: `freq n u x` is the transform of a sequence on a root `u`. Proved here: inversion
(`freq_inv`), the convolution theorem (`freq_cyclic`, `cyc_formula`), the even/odd split for the
radix-2 step (`freq_eo`, `freq_eo'`), Bluestein's identity (`bluestein_freq`: a transform of
length `n` from a cyclic convolution of length `N ≥ 2n` with chirps), lower-triangular Toeplitz
operators and their inverse (`toeplitzApply`, `toeplitzInv`, `toeplitzInv_left_inv`), and
`rootVandermonde_factor`: the Vandermonde matrix on a primitive root is `L · D⁻¹ · Lᵀ` with `L` a
Toeplitz matrix between two diagonals. The last is proved through Newton's basis (`newtonBasis`,
`newtonBasis_eval`): `V · N` is the node matrix, which is the lower factor.
Imports: `Goal`, Mathlib (roots of unity). Used by: `EngineMoves`, `ReelKit`.

## Submission/ReelKit.lean
Role: reels and their meaning; axis tensors; block covers.
* `Stroke` (`applyM`, `applyC`, `send`, `Sound`), `idStroke`, `plain`, `sideBySide`.
* `Reel` (`reach`, `go`, `Sound`, `wait`, `tick`, `stack`, `parallel`, `atOffset`, `scaleReel`,
  `permReel`) with `go_*` lemmas.
* `Zone`, `conjugateReel`, `lift`, `Adds`, `Acts` (and `Acts.conjugateReel`), `scaleZones`, `mixZones`, `zoneSwap`,
  `butterflyReel`, `brickReel`, `addMulReel`, `onePlusNormSq`, `addScaledReel`, `PairMap` and
  `*_twin` lemmas, `addScaled_adds`, `addScaled_acts`.
  `Acts r rd wr D`: the reel adds a linear function `D` of the positions `rd` to the positions
  `wr`; `Acts.conjugateReel` runs four such reels (two and their negatives) so that borrowed zones come
  back unchanged.
* `fftReel`, `fftReel_go`, `inverseFftReel`, `inverseFftReel_go`, `cyclicConvReel`, `conv_acts`, `paddedConvReel`,
  `blockConvReel`, `blockFilter`, `toeplitzBlockReel`, `block_acts`, `concatReels`, `tripleConcat`, `Gains`,
  `toeplitzPairReel`, `toeplitzGridCell`, `toeplitzGridReel`, `naiveToeplitzReel`,
  `bridgeOp`, `naive_gains`, `cell_zones`, `grid_gains`, `bridgeBeats`, `toeplitzBridge`,
  `Springs`, `toeplitzBeats`, `toeplitzStep`, `toeplitzReel`, `toeplitzReel_go`, `sound_*` lemmas.
* `Creates`, `reverseReel`, `reversedReel`, `lowerPassReel`, `upperPassReel`, `vandermondeSteps`, `vandermondeReel`,
  `vandermondeReel_creates`, `vandermondeBeats`, `vandermondeBeats_le`.
* `AxisTensor`: `Axes`, `extent`, `Splits`, `IdxMat`, `idxMul`, `idxApply`, `frame`, `axisKron`,
  `leafM`, `leafC`, `reelMat`, `axisRun`, `axisRun_eq_kron`; `Reloc`, `seek`; `PowBlock`,
  `PowBlockCover`, `blockAt`, `blockMul`, `blockProduct_cover`, `PairBlocks` (`pairLead`, `block`, `pairBlocks_cover`),
  `strokeBlocks`, `strokeBlocks_cover`; `CoprimeAxes`, `crtJoin`, `crtIndex`, `axisRoot`, `powMat`,
  `axisRoot_primitive`, `crtIndex_reloc`, `axisKron_powMat`, `crt_freq`.
  `axisRun_eq_kron`: running the axis reels in lockstep is the tensor product of their matrices.
Imports: `BinaryKernel`, `CostCalculus`, `DFTIdentities`. Used by: `WorkModulus`, `ReelCompile`.
Unusual: the largest front-end file; many short zone/separation proofs with `omega`
(`cell_zones` has a long block of separation goals).

## Submission/WorkModulus.lean
Role: choice of the transform length and the RAM code computing it.
* `axisBudget`, `axisBudget_above`, `axisBudget_pow`, `axisBudget_le`, `primeSearchBound`, `OddPrime`, `oddPrimeCount`,
  `oddPrime_count_ge` (enough odd primes, via the central binomial bound).
* `PrimeList`, `pushQ`, `Square`, `greedyPrimes`, `GreedyState`, `greedyPrimes_state`, `oddPart`,
  `twoPartFill`, `twoPartFill_spec`, `twoPart`, `modulusAxes`, `axisLogBound`, `axisLogBound_pow`,
  `ModulusSpec`, `modulusAxes_spec`, `IsLargeLen`, `largeWorkModulus`, `workModulus`,
  `workModulus_bound`, the divisibility facts `eta_dvd_largeWorkModulus`, `vol_dvd_largeWorkModulus`,
  `twoPow_dvd_largeWorkModulus`, `four_dvd_largeWorkModulus`.
* RAM side: `primeListTy`, `primeListT`, `PrimeListIn`, `oddPrime_word` (primality test program), `pushQ_moves`,
  `LenCtx` (`modulusAxes_in`, `workModulus_grain`, `largeLen_word`, …),
  `FreeWord.axisBudget_moves`, `FreeWord.workModulus_moves`.
Imports: `ReelKit`, `CostCalculus`. Used by: `DFTPrograms`.

## Submission/EngineMoves.lean
Role: binary words, moves, bit-address programs, envelope.
* `Binary`: `Sky`, `Data`, `letterwise`, `roleAct`, `point`, `Bits`, `bits` (layout of `Bits k`),
  `skyLayout`, `gridLayout`, `gridToBits`, `bitFlat`, `rippleMat_skyBits`, `ripple`, `part`, `rippleUpTo` (partial ripple),
  `rippleUpTo_succ`, `bits_flip`, `add_step`; `Cleave`, `Cleave.widen`, `Cleave.widen_dir`, `phaseOf`,
  `blockMat`, `widen_kernel`, `Cleave.adapted`, `Cleave.byLetter`, `Cleave.peel`.
  `part` is the diagonal of `phaseI` signs on the bit positions `[lo, b)`; `rippleUpTo` applies its Walsh
  wrap, which is the kernel on those positions (`rippleUpTo_succ`: one more position is a two-term
  update).
  `Cleave α β γ` is an additive equivalence `Space α ≃+ Space β × Space γ`. `Cleave.widen` puts a
  matrix on the `γ` factor; `Cleave.adapted` extends independent vectors to such a splitting;
  `widen_kernel`: a block along `r` independent directions is the kernel on the `γ = Fin r`
  factor. `Cleave.byLetter`/`peel` carry this to letter grids.
* `RoleKernel`: `Drives`.
* `RAM`: `Has`, `Knows`, `Able.branch`, `xorTab`, `Can.xor_prepare`, `BitCtx` (with
  `sky_get/set/add/lin/map/bool`, `addr_xor/and`, `peel_known`, `gridLayout_glue`), `roleLayout`,
  `RoleTapeCtx`, `padwise`, ferry lemmas, `naive_high_can`, `givenBits`.
  `naive_high_can` is the program for the positions `lo ≤ c < k`: `2^k (2(k - lo)+1)` work (the
  whole ripple at `lo = 0`).
  `BitCtx` says a bench knows `f`, `2^f` and an xor table for `f`-bit words (`Can.xor_prepare`
  builds the table); with it, linear maps and Boolean functions of letters are computed on
  addresses at no extra work (`sky_map`, `sky_add`, `sky_bool`, with the top-level
  `knows_pair_iff`). `RoleTapeCtx` adds a tape of role data; `ferry_free` also takes the `phaseProd`
  table.
* `envelope`, `envelope_positive`, `envelope_monotone`, `envelope_le_of`, `natCeil_le_double`.
* `GenMove`: `Move`, `Script`, `Move.Bounded`, `Script.Fits`, `shuffleMat`,
  `actPointG`, `Move.act`, `Script.exec`.
  The `ferry_*` lemmas say each free move is one zero-cost-per-entry rewrite of a role tape
  (`RoleTapeCtx.mix` for mixes, `ferry_pointG`, `ferry_free` for every move without block rank).
  `Drives e T w`: on inputs supported on the live roles, the script `w` acts as `T l` on live
  role `e l`.
Imports: `BinaryKernel`, `CostCalculus`, `DFTIdentities`. Used by: `EngineSetup`, `PlanToWord`,
`ReelCompile`.

## Submission/EngineSetup.lean
Role: small bench tools and the engine data layout.
* Helpers `WordIn.branch`, `tape_congr_sized`, `pick_all`; power tables `tablePow`,
  `doublingTable`, `powTable_moves`, `square_pow`.
  `doublingTable`: a table of `2^k` values built by doubling, in `2^k` work; `powTable_moves` (powers of a
  root) and `weightTable` (products of per-bit weights) are instances.
* `WeightTable`: `digitWeight`, `digitWeight_bit`, `weightTable`, `digitWeight_tape`.
* `Can.rackOf`; `partKer`, `partRip`, `partRip_compl`, `bitsAppend`, `bitsCast`,
  `placeEquiv`, `placeEquiv_loc`, `placeEquiv_lowRipple`.
  `partKer`/`partRip`: the kernel on the bit positions selected by a predicate (the low `h` bits,
  or the rest), with `partRip_compl`: two complementary parts give `ripple v`. `bitsAppend` joins
  two bit vectors; `bitsCast` retypes along `a = b`.
  `placeEquiv`: the bijection that places a letter grid, split along a block's directions, into
  `Bits n` so that the block's `k·f` bits are the low bits; `placeEquiv_lowRipple` says that the
  low ripple through this placement is the block acting on the grid.
* `ClassCtx`, `readThrough`, `enginePort`, `headVal`, `lowHigh`, `sliceAddr`,
  `glueJob_ripple`, `EJob`, `SlotEngine` (structure), its `slotPlace`, `initState`,
  `stepState`, `runV`, `sliceJob`, `moveKids`, `leafKids`, `childJobs`, `jobEnc`, `jobRes`; `stateTab`,
  `can_stateTab`, `ClassCtx` lemmas, `can_iter`, `ClassIn`, `unitVal`, `gears_can`, `ctx_of_cin`.
  Jobs: racks `Tape.tab N fun t => (bits n).tape (J t)` (an array of vectors), `lowHigh`/`sliceAddr`
  (a vector of `n` bits as `2^(n-k)` vectors of `k` bits), `glueJob_ripple`.
  `EJob` (`⟨false, n, B, v⟩` top | `⟨true, n, μ, J⟩` class), `SlotEngine` (layouts, live roles,
  target bases, the script, its properties), `jobEnc`/`jobRes` (the port's input and output),
  `CState` (the role data of a class job), `initState` (load), `stepState`/`runV` (the script on
  the state), `moveKids` and `leafKids` (the child top jobs of the blocks of a script), `childJobs`.
  Class setup: `ClassIn`, `ClassCtx` (what a class job knows: `μ`, `2^μ`, `2^(n - mx·μ)` for the free bits,
  the xor and `phaseProd` tables), `unitVal`, `gears_can`, `ctx_of_cin`.
Imports: `EngineMoves`, `CostCalculus`, Mathlib. Used by: `EngineRecursion`, `ReelCompile`.

## Submission/EngineCost.lean
Role: the numeric cost recurrence, independent of RAM.
* `pow_eventually_le`, `Rule`, `JobForm`, `JobForm.weight`, `Rule.Fits`, `jobKids`,
  `jobLocalCost`, `jobTotalCost`, `jobTotalCost_block`, `step_of_cover`, `jobKids_ok`,
  `exists_N2`, `succ_rpow_le`, `budget_exists`.
`Rule` is `(W, m, P, r)` with `1 ≤ r < m`. `JobForm` is the size of a job; `jobKids`, `jobLocalCost`,
`jobTotalCost` its children, own cost and total cost; `step_of_cover` says own + 1 + children ≤ total
when `J` covers the naive price and each group of `W` vectors pays for its block; `jobKids_ok` says
the children keep the invariant (`Fits`) and have smaller weight. `budget_exists` is the analysis
(tree explanation §3c): from `P r^z1 ≤ W m^z1`, `0 ≤ z1 < z ≤ 1` and `m ≤ n0`: a cutoff
`N ≥ n0` and a constant `C` such that `J n = C 2^n ⌈(n+1)^z⌉` pays for every step at cutoff `N`.
Its main tools are `succ_rpow_le` (`(x+1)^z ≤ x^z + 1`) and `exists_N2`
(polynomials are below `2^(n/M)` eventually).
Imports: Mathlib only. Used by: `EngineRecursion`.
Unusual: `budget_exists` is one long real-number proof (many `have`, `linarith`).

## Submission/EngineRecursion.lean
Role: the engine proof.
* `lowHigh_symm_loc`, `BitCtx.place_enc`, `place_dec`.
  `place_enc`/`place_dec`: computing `placeEquiv` and its inverse on addresses.
* `SlotEngine`: `classCost`, `Valid`, `passCost`, `kidsC_valid`, `stateTape`, `can_tabEl`,
  `elemRig`, `can_free`, `can_roleSet`, `readSlot`, `unload`, `unload_rack`,
  `load_can`, `drain_can`, `prefix_can`, `free_able`, `read_placed`, `writeBack`,
  `move_able`, `sweep`, `class_able`.
  The class job: `load_can`, `free_able` (one free move, one pass), `read_placed`/
  `writeBack` (read the child job of a block off the role tape, write its answer back into
  the role tape), `move_able`, `sweep` (the whole script), `drain_can`, `class_able`.
* `EngineRecursion`: `Desc`, `descBank`, `closed_of_body` (recursion through `Code.descend`).
  The recursion principle `closed_of_body`: an open body that answers a job using a port for its
  children, with children of smaller rank and a cost that pays for each step, closes to a program
  for all jobs satisfying the invariant (bounded `descend`; the fuel is a function of the job
  with the rank below it).
* Top jobs: `sum_ite_lt`, `list_sum_map_range`, `walshConj_part_high`, `hhigh_eq_ws`, `rippleHigh_moves`, `topG`, `topLo`,
  `topCost`, `rip_naive`, `Can.splice`, `groups_left_le`, `tree_able`, `naive_can`, `top_able`.
* Glue: `jobBits`, `EJob.form`, `jobCount`, `jobBound`, `locD`, `allChildJobs`, `childSet`,
  `engBank`, `body_able`, `RealisesRule`, `kidsC_shape`, `RealisesRule.childForms`,
  `class_dom`, `RealisesRule.loc_dom`, `child_bound`, `child_ok`, `RealisesRule.answers`,
  `RealisesRule.ripple_engine`.
  `body_able` joins the two bodies by a test on the job kind; `RealisesRule` and the
  `kidsC_shape`, `childForms`, `child_*`, `*_dom` lemmas match the concrete jobs with `EngineCost`.
Imports: `EngineSetup`, `EngineCost`. Used by: `EngineFromTemplates`.
Unusual: long `linarith` / `omega` closures after `generalize` (`groups_left_le`, `RealisesRule.loc_dom`).

## Submission/ReelCompile.lean
Role: compile reels to RAM and run the ripple engine on them.
* `climb`, `survey`, `strokeCellTy`, `strokeTape`, `reelTape`, `blockCellTy`, `blockCell`, `strokeBlockCell`, `strokeBlocksT`, `reelBlocksT`.
* `Bench.ConjComputes`, `LineConjComputes`, `AxisCtx` (`climbAxes`, `stepBench`), `ExpWords`, `bridgeBeats_word`, `toeplitzBeats_word`, `LineComputes`
  (`pow`, `gap`, `roof`, `freq`, `rise`, `blockFilter`, `toeplitzInv`), `LineConj`, `ZoneWords`, `RootData`, `StrokeAt`,
  `ReelComputes` (`stack`, `par`, `ite`, `concatReels`, `tripleConcat`, `plain`, `scaleReel`, `scaleZones`, `mixZones`,
  `reelTape`, `tree`, `of_reelTape`, `butterflyReel`, `brickReel`, `addMulReel`, `addScaledReel`, `fftReel`,
  `cyclicConvReel`, `paddedConvReel`, `blockConvReel`, `toeplitzGridCell`, `toeplitzReel`, `vandermondeReel`),
  `vandermondeReel_blocks`.
  `LineComputes`/`LineConj` (a sequence computable pointwise in polynomial time, with its conjugate),
  `ReelComputes` (a reel whose strokes are so computable), one `ReelComputes` rule per reel constructor up to
  `ReelComputes.vandermondeReel`, `tree`, and `vandermondeReel_blocks` (the tree tapes of a Vandermonde reel).
  `AxisCtx` (the axes as bench data) and `AxisCtx.climbAxes`: a table over the mixed-radix index built level
  by level, used by `climbing`, which backs `survey_moves` and `blocks_moves`; `perm_moves` builds
  on `survey_moves`.
* `AxisTensor`: `rippleEntry`, `blockRippleMat`, `blockRipple`, `blockRippleMat_prod`, `blockRippleMat_mul`,
  `blockRipple_loc`, `blockKernel`, `permLine`, `lineFrom`, `blockAtRipple`, `leafC_hem`, `axisKron_leafC`,
  `idxApply_eq_blockAtRipple`, `headWidth`, `headWidth_sum`.
  `blockRipple`, `blockKernel`, `blockAtRipple`, `idxApply_eq_blockAtRipple`: the mixing step of a beat is a
  ripple on each block of the cover.
* `StrokeBlocks`, `AxisStroke`, `BlockFields`, `survey_lt`, `axisKron_leafM`, `idxApply_leafM`, `survey_moves`,
  `blocks_moves`, `perm_moves`.
* `RippleEngine z` (definition), `headRun`, `Tables`, `HasI`, `engine_tab`, `cover_ripple`,
  `AxisStroke.step_moves`, `axisReelBlocks`, `AxisReels`, `AxisReels.kron_moves`.
  `engine_tab`: the engine on a table; `cover_ripple`: pack by block, one engine call per block
  head, read back at the seat.
Imports: `CostCalculus`, `EngineMoves`, `ReelKit`, `EngineSetup`. Used by: `DFTPrograms`, `EngineFromTemplates`.
Unusual: six `private theorem marker_*` declarations at the end, each with one `Unit`
argument whose name is a long sentence; they prove `True`.

## Submission/DFTPrograms.lean
Role: the DFT, convolution and WHT programs, and the asymptotics.
* `conv`, `paperM`, `paperW`, `paperDelta`, `paperMultiplier`, `theta`, `paperTime`, `nlogn`,
  `convInKind`, `convOutKind`, `ConvProgram`.
* `WHT`: `SolvesFamily`, `hadamard`, `HadamardProgram`, `walshLine`, `sign_digit`, `walsh_eq`,
  `tab_mul`, `walsh_tab`, `whtInputs`, `wht_moves`, `SolvesFamily.of_can`, `rpow_isLittleO_id`,
  `hadamard_exp`.
* `AxisCtx.crtChart_moves`, `AxisReels.gather_moves`, `spread_moves`, `freq_moves`.
* `twoPowRoots`, `axisData`, `axisReels`, `reelTrees`, `axisData_words`,
  `modulusFreq_moves_of_axes`, `powByBits` (power by repeated squaring), `LenCtx.cubeExp`,
  `rootOfDvd`, `rootTwoN`, `rootVol`, `ratioSq`, `primeList_entry`, `axisData_dry`, `axisDFTCost`.
  `modulusFreq_moves_of_axes`: axis data ⇒ the transform of length `N`. `LenCtx.axisData_dry`
  is the whole axis-data program (sizes, `I`, two-power roots, axis roots).
* `budget`, `BudgetMoves`, `BluesteinCtx` (`modulusFreq_moves`, `chirp_moves`,
  `bluestein_moves`), `LenCtx.dft_moves_large`, `PolyMoves.naive_freq`, `LenCtx.dft_moves`,
  `FreeWord.order_moves`, `FreeWord.dft_moves`, `convLen`, `padLine`, `freq_pad_conv`, `cross_moves`.
  `BudgetMoves`: cost `budget z d n`, through `Can.Within`. `LenCtx.dft_moves` splits large and
  small `n`.
* `budget_small`, `Sizes`, `CostWitness`, `stageCost`, `BudgetMoves.ration`, `totalCost`,
  `lengthOnly`, `assemble_program`, `dftInputs`, `dft_solve_program`, `conv_solve_program`,
  `conv_program`, `dft_program`.
* `Timing`: `logN`, `logLogN`, `log2_min`, `targetTime`, `beats_poly`, `axisBudget_lim`,
  `order_pow_lim`, `order_lim`, `envelope_lim`, `axisDFTCost_le`, `targetTime_big`, `log_pow_le_rpow`,
  `logPow_eventually`, `largeLen_eventually`, `polylog_ev`, `budget_isBigO`, `totalCost_isBigO`.
* `theta_lt_one`, `targetTime_le_eventually`, `targetTime_nonneg`, `bounds_of_exp`, `exists_exp`.
Imports: `Goal`, `ReelCompile`, `WorkModulus`, Mathlib asymptotics. Used by: `Submission`.
Unusual: four `private theorem marker_*` (`marker_goal`, `marker_working`, `marker_merged2`,
`marker_main`) like in ReelCompile; `freq_moves` is one long `refine Can.bind …` chain;
`theta_lt_one` uses `norm_num` on the paper constants.

## Submission/PlanToWord.lean
Role: from a correct `QPlan` to an engine word (`Script`) that drives the live roles (`Drives`).
* `Bit A = Fin A × Fin 2`, `PlanUnit` (structure carrying the word and its facts).
* `toCol`, `toSp`, `toSky`, `toAddr`, `skyEquiv`; `rowSum` and its rules for each plan
  constructor, `rowSum_correct`.
* `Roles`, `rolesFintype`, `rolesDecEq`, `outR`; `mixG`, `mixG_out`, `mixG_keep`, `colPerm`.
* Identities: `pairEntry`, `chi_dot_half`, `littleC_split`, `pairEntry_eq`, `littleC_phase`, `pairMat_entry`, `dir_apply`, `dir_mul_dir`, `pairDirs`, `blockPair_apply`,
  `child_col`, `littleC_pair`, `rippleMat_col`.
* Words: `cpMove`, `childMat`, `childWord`, `gtest`, `hat`, `scaleWord`,
  `orth_sign`, `fourier`, `toWord`, `Realises`, `*_realises`, `realise`, `toWord_ranks`.
* Unit: `phWord`, `phVal`, `preZ`, `postZ`, `multi_walk`, `fullBasis`, `blockMat_full`,
  `copyBack`, `unitWord`, `unit_live`, `unitWord_ranks`, `unitWord_proper`, `cardBit`.
Imports: `WalshTemplate`, `EngineMoves`. Used by: `EngineFromTemplates`.
Unusual: the `littleC_split`/`littleC_phase`/`littleC_pair` lemmas do 4-way `bit_cases` splits with
`simp (config := {decide := true})` and `linear_combination … * I_mul_I`.

## Submission/EngineFromTemplates.lean
Role: the bridge from templates to `RippleEngine`.
* `rate_of`, `PlanUnit.engine`, `rippleEngine_of_planUnit`, `fullBasis2`,
  `fullBasis2_indep`, `blockMat_fullBasis2`, `planUnitOf`, `rippleEngine_of_good`,
  `TemplatesAbove`, `templateWall`, `templates_wall`, `templateWall_nonneg`,
  `templateWall_le_half`, `exists_good_below`, `rippleEngine_of_templates`.
Imports: `PlanToWord`, `EngineRecursion`, `ReelCompile`, `WalshTemplate`. Used by: `Submission`.

## Submission/WalshTemplate.lean
Role: the whole template layer (namespace `OAI.Computability.NearSquareRoot.KernelPass`),
pure ℚ-matrix algebra over `ZMod 2` indices.
* Basics: `chi`, `chi_add`, `chi_sum`; `Free.Src/Mid/Tgt`, `free_factor`, `phase_split`.
* Plans: `Column`, `Addr`, `RowMatrix`, `piMat`, `pairMat`, `walshCol`, `axisMat`,
  `rowTensor`, `directSum`, `QPlan`, `calls`, `eval`, `target`, `QCorrect`, `QCandidate`,
  `Good`, `eval_*_apply`, `directSum_*`, `piMat_mul/one/update`, `OneRow`.
* Small plans: `idPlan`, `chainPlan`, `rowPlan`, `chirp`, `swapPlan`, `queryPlan`
  (`query_col`), `rowBank`, `Kw`, `Fdr`, `specR`, `specR_mul`, `specR_const`, `spec_apply`.
  `specR`: conjugation by the Walsh matrix on every row.
* Routing algebra: `qadd`, `qSumL`, `qSumF`, `qSmul`, `qLin`, `qSide`, `qSandwich`, `qShare`,
  `qPair`, `QCharged`, `QFree`, `routed`, `routed_eval`, `routed_calls`.
* Letters and kernels: `Bits`, `LMat`, `lift`, `Implements`, `linMat`, `signMat`, `walshU`,
  `Free.Aux/Act/srcCo/srcSign/midSign`, `free_kernel_entry`, `free_kernel`, `V`, `pos1`,
  `pos2`, `act`, `spect`, `Uq`, `Chart`, `U`, `gl`, `U_eq_submatrix`, `bitsE`, `actLift`,
  `chartOf`, `free_letter`, `DistEq`, `theta`, `splitA`, `splitB`, `iota*`, `free_geom`,
  `exists_walshPlan`, `exists_walshConj`, `exists_monoPlan`, `onAux`, `walshU_aux`,
  `srcL_eq`, `exists_srcPlan`, `tgtL_eq`, `exists_tgtPlan`, `bT_ker`, `bS_ker`, `bTe`, `bSe`,
  `muE`, `midG`, `midL_eq`, `exists_midPlan`, `free_hfr`.
  `QPlan.perm` takes any additive permutation of columns, so a linear letter map is one plan
  (`linPlan`, `implements_lin`) with no elimination argument.
* Parameters: `pq`, `pL`, `pN`, `pm`, `pD`, `pA`, `sq_le_two_pow`, `exists_k`.
* Kernel rewriting: `target_eq_Kw`, `multiQuery`, `walshCol_apply`, `zipE`, `qtot`,
  `query_pairs`, `walsh_of_WDW`, `chirpAll`, `swapAllPlan`, `qp`, `sQ`, `colK`, `Kpair`,
  `colK_apply`, `piMat_colK`, `prod_sQ`, `comQ`, `charged_routed`, `label_self_spectral`,
  `qtot_spat`.
* Polynomial: `cstep`, `tprod`, `upred`, `upred_exact`, `tauQ`, `repairCheck`, `tableMat`,
  `division_repair_mat`, `intNodes_leftInverse`, `rowsOf`, `template`, `template_correct`,
  `checkLoop`, `repairOut`, `repairOut_spec`, `qentryScale`, `qfreqMat`, `aStep`, `bStep`,
  `hq`, `hornerP`, `hornerPb`, `lab`, `shf`, `liftSet`, `liftCh`, `liftFr`, `shift_eval`,
  `shift_calls`, `shift_stage_spec`, `csg`, `pOfH`, `InWin`, `hornerBankS`, `horner_template`.
* Counting: `hamming`, `sum_exp_hamming`, `cosh_le`, `one_side`, `window_count`, `window_fraction`,
  `pencilOrder`, `pencilOrder_window`, `RateOK`, `rateOK_of_half`, `params_rate_side`,
  `log_bound`, `two_pencilOrder_le`, `window_params`, `pA_le`, `calls_le`, `cnt_eq_hamming`,
  `shift_count`, `shiftEquiv`, `template_of_routing`, `pm_large`, `pm_odd`.
* Rectangles: `agree`, `ChRect`, `charged_sum`, `weight_identity`, `card_chRect_le`,
  `Letter`, `trunc`, `truncF`, `cutOf`, `CutRect`, `hdist`, `cut_sum`, `card_src`,
  `card_tgt`, `label_identity`, `mulLin`, `Gint`, `gch`, `Pch`, `label_identity_even`,
  `gLab`, `dLab`, `SpLab`, `nLab`, `exists_pivot`.
* Finale: `templates_of_rate`, `walshTemplate_above_half`.
Imports: Mathlib only (kronecker, block matrices, Vandermonde, fintype). Used by:
`PlanToWord`, `EngineFromTemplates`.
Unusual: by far the largest file; many `decide` facts on `ZMod 2`, `fin_cases`, large
`simp only` sets, and the long `templates_of_rate` proof that wires all choices together with `choose`.
-/
