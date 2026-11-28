/-!
written with help of ai↓
sending this fast and can send credit fix later,  almost everything below might be stale since i kinda redid the tree it compiles some order of magnitude faster with near 1 order smaller code size too like even llm models can fit their full context window, so probably no one elses code left except some openai codes (some were unchangable status)( currently mathlib etc consume most time and ram by the way)(more info in text folder)

# Credits

This module has no code. It credits, idea by idea, the people whose ideas this tree uses
("inspired/adapted from") and the people whose results showed that an idea works
("showed ideas are working"). Tags in (+...) are each source's own tool disclosure, where it is known.
Paths are relative to Submission/.

## Author

Halit Ziya KARTAL (https://github.com/HalitZiyaKARTAL, https://halitziyakartal.github.io): author and
supervisor; crediting myself for reorganizing whole thing so its easier to modify

credit:  organized whole thing while models like opus was making lots of retarded mistakes, or dumb limits at claude code, also including claude resetting the container that was just left for something like 15 mins  unused, which erased data like my record was ready so i made and used new tools that recover information with even automating mcp tools etc etc, well it add me experience at least,  i was also using opus deepseek hybrid since anthropic tokenizer and was too suboptimal like i had to use heater(my another tool to keep cache warm) etc,  anyway after meddling with claude code binary more i got more experience and sidestepped older limiters i got and used multiple containers to compile lean branches etc etc  which shown mathlib was very bad at lean and nanoda memory,
when i removed it i was able to compile something like 4 at once per container ( i was under 10 min for lean but new words i used had problematic events that soak ram and cpu so i optimized some more) also after reaching 500 file and one version was being 100mb i optimized hard so made whole lean tree able to fit something like 500-600k tokens of deepseek, which made it simpler since it meant no read requirement from now on(i was using my other tools like building agents copying rewinding, sending agents between sessions etc etc to handle them,  also weirdly i got lots of classifier false positives during math work where deepseek helped more, also fable had less false positives, but didn't add much since it didn't add much more to opus,  anyways basically i coordinated whole thing and handled bottlenecks,  tried to close weak local minima issues of models etc etc thus resulted in improvements, i also have lean for integer side too but i also waited it for credits which costs time, probably a bit dumb desicion to wait for them,
but math side have 6 open claims as axioms(i had proven it unconditional(3 classics) for 6e-5 and rest was upgrade package making something like 34/10000), i kinda half solved them too, soo if you have compute to share i can also list under compute sponsors if you want( tokens i meant, and not dumb ones like haiku considering even opus does random rm rf calls etc ) anyways trying to keep shorter now, i could send more to pr maybe but i have other projects to handle too so i am not sure, also i plan to redo whole tree a bit more since its still suboptimal for my taste, soo thats kinda it for now you and comment pr to reach, bye for now
(temporary(hopefully) placeholder credits etc)

## Models and harnesses used for this tree

primarily with heavily modified claude code and  opus 5.5 deepseek fable 5.2 hybrid and some other models-harnesses( if anyone wants to sponsor i can try to do some with their models or harness too, or if economic i can mention as sponsors in credits)

## Where the credited ideas are (read this first)

This section says, per source, where each credited idea is in the tree and how close the code is to the
source. Sources whose code is in the tree keep their credits and notices; sources with no code but an idea
that is used keep an idea credit only; sources with neither are not credited here (c. below). Every file
named is directly under Submission/. "Credits.lean" in the notice lines of the code files means this file.

By source (token-weighted share of each file with the named sources, measured on the tree with the present
file names, commit 637e41b; about 0.03 is the noise floor of the method):

a. OpenAI (openai/math, Apache-2.0).
   - RAM.lean 0.99, Goal.lean 0.90: OpenAI's model and statement, the reached declarations unchanged.
   - CostCalculus.lean 0.56 (the cost calculus, layouts, programs, benches): adapted from OpenAI, heavily modified.
     The proofs are this tree's own; the shared part is the definitions and the statements of the rules.
   - DFTPrograms.lean 0.38, EngineMoves.lean 0.40, EngineSetup.lean 0.43, BinaryKernel.lean 0.32, ReelKit.lean 0.28,
     DFTIdentities.lean 0.26: heavily inspired from OpenAI. In DFTPrograms the axis transform (`gather_moves`, `spread_moves`, `freq_moves`),
     the root powering (`powByBits`) and the eventual-bound lemmas are this tree's own proofs; the Bluestein
     and axis-data lemmas follow OpenAI's path closely.
   - ReelCompile.lean 0.14, WorkModulus.lean 0.13, EngineCost.lean 0.15, EngineRecursion.lean 0.17: inspired.
   - WalshTemplate.lean 0.04, PlanToWord.lean 0.04, EngineFromTemplates.lean 0.04: this tree's own code, written along
     the mathematical outline of OpenAI's binary kernel-pass template (items 17, 20 and 22 below); the
     plan-syntax chunk KP.Defs of WalshTemplate.lean is closer (item 22). The plan
     language `QPlan` follows OpenAI's `KernelPass.Plan` in shape; its `xor` move is widened here to `perm`
     (any additive permutation of columns).
b. Jacob Sussman (jacobalansussman) (+claude): idea credit only.
   - The engine idea (free moves and paid blocks on role data, one recursive port, the class job, the cost
     recurrence closed by a rate condition) and the Walsh-Hadamard transform as a corollary: inspired from.
     Where the ideas are used: EngineMoves.lean (engine moves), EngineSetup.lean (jobs, class setup), EngineRecursion.lean (class
     job, top job, recursion), EngineCost.lean (the recurrence), DFTPrograms.lean (the WHT section).
   - The mixed-target recursion, the seam adapter and the certificate checkers of his line are not used.
c. The integer-side sources (the supplier words, the batch callers, the certificate formats and the
   people who showed those ideas working): neither their code nor their ideas are in the tree (route B
   uses no certificate), so they are not credited here (items 4 to 14 are left empty). The headers of the
   earlier entries in Submission.lean name them, as the record of those entries.
d. bigospeedrun/verifier PR #223 (item 18): no code of it is in the tree; idea credit only.

## Ideas, per source

1. OpenAI (github.com/openai/math, family 130, commit fd4aeeb, Apache-2.0): the exact computational
   model, the DFT and convolution statements, the all-length reduction and the Fourier transform layer.
   adapted from OpenAI's OAI/Computability/FourierTransform/{Goal,RAM}.lean and FourierCircuit/Core.lean:
   Goal.lean and RAM.lean hold only the declarations the challenge statement reaches, each with OpenAI's full
   name and term (`OAI.ExactFourier.zeta` comes from Core.lean); imports are narrowed to the Mathlib modules
   needed. The unreached declarations this tree uses are unchanged under the same full names: the Goal ones
   (`conv`, `ConvProgram`, `convInKind`, `convOutKind`, `paperM`, `paperW`, `paperDelta`, `paperMultiplier`,
   `theta`, `paperTime`, `nlogn`) at the top of DFTPrograms.lean, `Tape.look_of_lt` in CostCalculus.lean
   (`Tape.sow` stays in RAM.lean: `Bill.steps` reuses its matcher). The unreached declarations the tree does
   not use (`TimeBounds`, `DFTGoal`, `ConvGoal`, `decimalExponent`, `decimalTime`, `dftMatrix`, `Tape.map`,
   `Tape.look_of_le`, the rest of Core.lean) are deleted; the general `transform_order_saving_of` /
   `convolution_order_saving_of` imply OpenAI's goal statements. This follows the #209 reviewer's rules: every
   declaration reached from the challenge statement keeps its full name and identical term (it may move between
   files), and unreached declarations may be deleted. The files are therefore NOT byte-identical to OpenAI's.
   adapted from OpenAI's FourierTransform/{WorkingTransform,WorkingPreparation,TransformProgram,Asymptotics}.lean:
   the modified copies in DFTPrograms.lean, each with its notice in the file; along the path of OpenAI's
   WorkingCompiler, ArbitraryLength, UniformBounds, ConvolutionProgram, Main and Goal files (DFTPrograms.lean,
   with this tree's exponents and declaration names). this tree's compiler and reel code, written along OpenAI's
   RAM-program path; token-weighted share of each part with OpenAI's files:
   adapted from OpenAI, heavily modified (share above 0.5): CostCalculus.lean part 1 0.64 (after Cost,
   PolynomialBounds, ProgramBounds, LoopBounds, ProgramConstruction, PolynomialPrograms, CompilerEnvironment),
   CostCalculus.lean part 2 0.59 (after Layout, LayoutPrograms, IntegerPrograms, WorkBounds,
   LocalPreparation, PowerTables).
   heavily inspired from OpenAI (share 0.1-0.5): BinaryKernel.lean 0.32 (the proofs are this tree's own; the
   shared part is the definitions and statements after ProductMatrix, BinaryFrames, BinaryBasis), EngineMoves.lean part 1 0.46 (DirectionalWords,
   BitLayout, ColumnAddresses, RoleArrays), ReelKit.lean 0.29 (SectorPacking, LayerWords, TensorIndexing,
   ToeplitzLayers), DFTIdentities.lean 0.27 (the proofs are this tree's own, at ~0.03; the
   shared part is the definitions and statements after FourierIdentities, ChirpConvolution, ToeplitzIdentities),
   ReelCompile.lean part 1 0.15 (TraversalPrograms, SectorPrograms, PackingPrograms), WorkModulus.lean 0.14
   (RootPreparation, PrimeSelection, LengthSelection).
   inspired by OpenAI (share below 0.15): ReelCompile.lean part 2 0.12 (this tree's own code along the plan of
   SectorAlgorithm and SynchronizedAlgorithm: pack by block, one engine call per block head, read back at the seat).

2. Jacob Sussman (jacobalansussman) (+claude): the engine design (free moves and paid blocks on role data,
   one recursive port, the class job, a cost recurrence closed by a rate condition) and the Walsh-Hadamard
   transform as a corollary of the ripple engine: inspired from. Idea credit only; see b. above for where the
   ideas are used. His label check, warp certificate format, stage/window geometry, mixed-target recursion,
   seam cost and exit frames are not used in the tree.

3. Ryan Shea (shea256) (+codex); Nil Mamano: the complex588 tree, upstream of Jacob Sussman's line (item 2).
   Idea credit only.

(Items 4 to 14 are left empty: they credited the integer-side certificate line; see c. above.)

15. The Boolean-function phase move `Move.sgn` (EngineMoves.lean part 2) with its RAM side `BitCtx.sky_bool`,
    `BitCtx.addr_and`, `matAct_bphase` and the `sgn` case of `RoleTapeCtx.ferry_free`: inspired from the `scale`
    instruction of OpenAI's binary Walsh template (github.com/openai/math,
    OAI/Computability/NearSquareRoot/KernelPass.lean, Apache-2.0); the code is this tree's own.

16. OpenAI's binary Walsh template (the closure of OAI/Computability/NearSquareRoot/KernelBinaryTemplate.lean,
    with OAI/LinearAlgebra/FiniteFourier), its gate-model Fourier complexity files (LinearAlgebra/FiniteFourier,
    Computability/FourierCircuit) and FourierTransform/RegisterBounds.lean (github.com/openai/math, Apache-2.0):
    none of them is in the submission; `Race.bound` and `routeB_all` do not use OpenAI's `binaryTemplate` (the
    template is this tree's own, item 22). Copies with OpenAI's notices unchanged are kept outside the
    submission build, in older_helpers/; the OpenAI attribution stands for them.

17. The route B unit and engine bridge (PlanToWord.lean part 1, EngineFromTemplates.lean): inspired from OpenAI's
    NearSquareRoot/KernelPassSearch.lean and KernelBinaryTemplate.lean (github.com/openai/math, Apache-2.0): the
    strict call rate (OpenAI's `Candidate.Good`; here this tree's own `QCandidate.Good`) as the condition that
    makes a template run as a fast ripple. This tree's own: the rate as the moment condition of this tree's
    engine (`rate_of`, `PlanUnit.engine`, `rippleEngine_of_planUnit`: untensored, targets of size 2·arity, blocks
    of rank 2; OpenAI's own path is its PrimeKernel recursion), the choice of one rational exponent
    (`exists_good_below`), and `Race.bound` as `routeB_all` at the saving ((D-1)/2)/D = 1/2 - 1/(2D), D = 10^40 - 1.
18. bigospeedrun/verifier PR #223 (Vladislav Kuznetsov, AnanasClassic, with OpenAI Codex): no code of it is in
    this tree. Ideas that also appear there: running OpenAI's binary Walsh template as a ripple engine, and the
    parameter D = 10^40 - 1. The convolution, WHT and paper-goal theorems in DFTPrograms.lean and Submission.lean
    are this tree's own code.
19. (left empty: RegisterBounds.lean, see item 16.)
20. The route B unit word (PlanToWord.lean part 2): inspired from OpenAI's NearSquareRoot/KernelPass.lean
    (github.com/openai/math, Apache-2.0): the template language `KernelPass.Plan` (mix, xor, scale, child, seq,
    parallel), its semantics `Plan.eval`, `target` and `Correct`, whose shape this tree's rational `QPlan`,
    `QPlan.eval`, `target`, `QCorrect` follow (chunk KP.Defs of WalshTemplate.lean, item 22; here `xor` is widened
    to `perm`, any additive column permutation). The rest is this tree's own: the entrywise reading `rowSum` of
    `QPlan.eval` on role data with one lemma per instruction (`rowSum_mix`, `rowSum_perm`, `rowSum_scale`,
    `rowSum_child`, `rowSum_mul`, `rowSum_sum_left/right`, `rowSum_correct`), the translation of plans into
    engine words (`toWord`, `realise`), the child-call conversion (`child_col`, `rippleMat_col`, on `littleC`
    and `blockMat`), and the unit word (`unitWord`, `unit_live`). The general theorems of Submission.lean
    (`transform_order_saving_of`, `convolution_order_saving_of`, `routeB_all`) are this tree's own.
21. (left empty: the gate-model files, see item 16.)

22. The rational binary Walsh template (WalshTemplate.lean; `walshTemplate_above_half`: for every num/den > 1/2 a
    Good rational candidate). This tree's own construction and proofs, written along the mathematical outline of
    OpenAI's kernel-pass template (github.com/openai/math, Apache-2.0, LinearAlgebra/FiniteFourier and
    Computability/NearSquareRoot). By closeness of path (chunk names are the `KP.<part>` markers of the file):
    adapted from OpenAI, heavily modified: chunk KP.Defs (`Column` .. `QCorrect`: the six-move plan syntax `QPlan`,
    `QPlan.eval`, `target`, `QCorrect`, `QCandidate`, `QCandidate.Good`), which matches OpenAI's
    NearSquareRoot/KernelPass.lean at 0.78 (token-weighted; restated over ℚ, the strict call rate after
    KernelPassSearch.lean's `Candidate.Good`); the Vandermonde checks of chunk KP.Repair (after
    PrimeRepairVandermonde).
    heavily inspired from OpenAI: the `tableMat` .. `division_repair_mat` block (chunks KP.Repair, KP.RepairQ; 0.43,
    after PrimeRepair.lean); the letter notions `Bits`, `lift`, `Implements` (KP.Letter, KP.LetterPlans); the
    rectangle interface shape and call bound (KP.QRouting, after KernelPassRectBank / KernelPassRectBudget
    `block_pencil`, `calls_pencil_le`); the charged-rectangle counting idea (KP.HammingWeights, after
    PrimeRectangleCharged); the cut rectangles (KP.CutRect, after PrimeBitLetter / PrimeBitRectangles); the label
    kernel, its charts and its charged and free factorizations (KP.FreeFactor, KP.LabelKernel, KP.LabelChart,
    KP.ExplicitChart, KP.KernelBridge, KP.ChargedPlan, KP.Free*, after PrimeCommonKernel, PrimeEndpoint*,
    KernelPassChargedLabels, KernelPassFreeGeometry: same mathematical statements, read from OpenAI's definitions
    and theorem statements; the proofs were written without OpenAI's proofs); the halves-exchange identity
    (KP.Pairs, after KernelBinaryQuerySigns); the frequency-table idea (KP.FreqTable, KP.QFreq, after
    KernelPassMatrixTable / KernelPassFrequency).
    this tree's own (not in OpenAI's path): rational plans (`QPlan`), the univariate Horner predictor
    (KP.Horner, KP.HornerStage, KP.HornerTemplate), the integer check nodes of the repair (`intNodes_leftInverse`,
    KP.RepairQ), the
    explicit rational interpolation weights (KP.Interp, KP.CutRectEven), the shift-row routing instance
    (KP.ShiftRows, KP.ShiftCount), the window count by elementary counting (KP.Window), the parameter and rate
    files (KP.Params, KP.ParamsQ, KP.Order), the assembly (KP.Assembly, KP.AssemblyRate, KP.LabelVec,
    KP.RoutingFinal, KP.AboveHalf). The rest of WalshTemplate.lean measures 0.02-0.04 against OpenAI (noise
    floor). No code of any bigospeedrun/verifier PR after #209 enters, other than OpenAI's.

## Notices

The line
`--might be  containing modified Apache-2.0 codes pieces from one or several sources; notices and credits: Credits.lean`
is carried by CostCalculus.lean only (at the head of each of its parts), the one code file whose text is more than
half the same as an Apache-2.0 source (OpenAI's openai/math, share 0.59; its OpenAI files are named in item 1 and
in a. above). Submission.lean spells it `-- might be containing modified Apache-2.0 code pieces ...`. Measured on
runs of ten or more consecutive identical lines, each line credited to the earliest source that holds it, every
code file other than RAM.lean and Goal.lean has under a tenth of its lines in such runs; the other code files
carry no such line.
DFTPrograms.lean keeps its own in-file notices on the blocks derived from OpenAI's files (A. below).
RAM.lean and Goal.lean are OpenAI's files (reduced to what the challenge statement reaches; their headers
say so) and carry no such line, so that their reached text stays OpenAI's.

### A. Files that hold OpenAI-derived blocks (share = fraction the same as the named OpenAI file)

DFTPrograms.lean:
  WorkingTransform 0.83 and WorkingPreparation 0.84: OpenAI, modified (notice in the file, "Derived from ...")
  TransformProgram 0.60 and Asymptotics 0.55: OpenAI, heavily modified (line and notice in the file)
  Goal definitions 0.47, WorkingCompiler 0.43, ArbitraryLength 0.45, UniformBounds 0.38,
  ConvolutionProgram 0.045, Main 0.11: OpenAI, adapted from (along OpenAI's path, with this tree's exponents,
  declaration names and proofs where they differ)
ReelCompile.lean part 2:
  this tree's own code (one general `cover_ripple` theorem), share 0.12: inspired by OpenAI's SectorAlgorithm and
  SynchronizedAlgorithm (item 1; the plan is named in the file's comment above `headRun`); the engine statement
  `RippleEngine` is inspired by OpenAI's `hills_program` (TensorProgram.lean), with this tree's envelope
  `envelope z k = ⌈(k+1)^z⌉` in place of `hills`.

Earlier versions of this tree carried further notices for modified copies of OpenAI files that are no longer in
the tree; those notices are in the repository's git history, with the files they belonged to.

From the earlier notice of the Vandermonde factorization, whose code is now in DFTIdentities.lean:

     Interface follows the OpenAI
    Computability/FourierTransform package (Apache-2.0), whose notices are retained in the
    release tree.

-/
