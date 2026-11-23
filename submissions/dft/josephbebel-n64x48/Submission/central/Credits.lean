/-!
written with help of ai↓

# Credits

This module has no code. It credits, idea by idea, the people whose ideas this tree uses
("inspired/adapted from") and the people whose results showed that an idea works
("showed ideas are working"). Tags in (+...) are each source's own tool disclosure, where it is known.
Paths are relative to Submission/.

## This submission (native 64 x 48-call)

Submitted by Joseph Bebel (GitHub josephbebel), prepared with Claude (Anthropic) and OpenAI Codex.

Derived from PR 209 (bigospeedrun/verifier #209, Halit Ziya KARTAL, submissions/dft/halitziyakartal-halitziyav7-42,
source cecd9d89). The rest of this file is PR 209's credit list, unchanged. Two additions mark this submission:
item 10a and the note on Cert/Scalar/Split.lean under Notices.
* the compact packed-row checker, the tree and its documentation, and the Lean formalisation of the closed
  48-call caller: Halit Ziya KARTAL (PR 209), with the sources he credits below;
* the native 64 word: OpenAI Codex, in research for this submitter, on Ali Romman's #8027 native (item 10).
  Codex added chain shortcuts to the #8027 word by exact rational construction, then twelve more found by a
  fresh scan of the completed word, each checked by exact endpoint and fractions.Fraction replays;
* the 48-call caller lineage: #7776 (Ali Romman; templates of #7756, Ali Romman, and #7700, SYLforge), item 11,
  formalised in PR 209. This submitter's issue-route entry (bigospeedrun/verifier issue #208) uses the same
  caller lineage in a separate Lean formalisation, which this tree does not use;
* the port of the native 64 word to PR 209's checker (Decode/Events for 2811 registers and depth 12, radix 2^426),
  the key-range split of the scalar check (Cert/Scalar/Split.lean), the rate certificate at
  1957647056737859/(5*10^17) (bases 12/13, Kc = 10^26, Kf = 10^18) and the packaging: Claude (Anthropic).

## Author

Halit Ziya KARTAL (https://github.com/HalitZiyaKARTAL, https://halitziyakartal.github.io): author and
supervisor; crediting myself for reorganizing whole thing so its easier to modify

credit:  organized whole thing while models like opus was making lots of retarded mistakes, or dumb limits at claude code, also including claude resetting the container that was just left for something like 15 mins  unused, which erased data like my record was ready so i made and used new tools that recover information with even automating mcp tools etc etc, well it add me experience at least,  i was also using opus deepseek hybrid since anthropic tokenizer and was too suboptimal like i had to use heater(my another tool to keep cache warm) etc,  anyway after meddling with claude code binary more i got more experience and sidestepped older limiters i got and used multiple containers to compile lean branches etc etc  which shown mathlib was very bad at lean and nanoda memory,
when i removed it i was able to compile something like 4 at once per container ( i was under 10 min for lean but new words i used had problematic events that soak ram and cpu so i optimized some more) also after reaching 500 file and one version was being 100mb i optimized hard so made whole lean tree able to fit something like 500-600k tokens of deepseek, which made it simpler since it meant no read requirement from now on(i was using my other tools like building agents copying rewinding, sending agents between sessions etc etc to handle them,  also weirdly i got lots of classifier false positives during math work where deepseek helped more, also fable had less false positives, but didn't add much since it didn't add much more to opus,  anyways basically i coordinated whole thing and handled bottlenecks,  tried to close weak local minima issues of models etc etc thus resulted in improvements, i also have lean for integer side too but i also waited it for credits which costs time, probably a bit dumb desicion to wait for them,
but math side have 6 open claims as axioms(i had proven it unconditional(3 classics) for 6e-5 and rest was upgrade package making something like 34/10000), i kinda half solved them too, soo if you have compute to share i can also list under compute sponsors if you want( tokens i meant, and not dumb ones like haiku considering even opus does random rm rf calls etc ) anyways trying to keep shorter now, i could send more to pr maybe but i have other projects to handle too so i am not sure, also i plan to redo whole tree a bit more since its still suboptimal for my taste, soo thats kinda it for now you and comment pr to reach, bye for now
(temporary(hopefully) placeholder credits etc)

## Models and harnesses used for this tree

primarily with heavily modified claude code and  opus 5.5 deepseek fable 5.2 hybrid and some other models-harnesses( if anyone wants to sponsor i can try to do some with their models or harness too, or if economic i can mention as sponsors in credits)

## Ideas, per source

1. OpenAI (github.com/openai/math, family 130, commit fd4aeeb, Apache-2.0): the exact computational
   model, the DFT and convolution statements, the all-length reduction and the Fourier transform layer.
   adapted from. Kept unchanged except their import lines (`Submission.` prefix; in RAM.lean and Core.lean
   `import Mathlib` narrowed to one Mathlib module): OAI/Computability/FourierTransform/{Goal,RAM}.lean,
   OAI/Computability/FourierCircuit/Core.lean. Modified copies: Transform/EngineUse.lean,
   Work/U7604/Chain/FourierTB/Main.lean (notices below). inspired/adapted from: Algebra/DFTIdentities.lean,
   Compiler/{Judgment,Layout}.lean, Reel/Machinery.lean, Transform/ReelCompile.lean, Ripple/RoleMoves.lean.

2. Jacob Sussman (jacobalansussman) (+claude): the Lean engine (frames, free moves, routes, `gstep_free`),
   the label check, the warp certificate format, the stage/window geometry, the mixed-target recursion,
   the seam cost, the exit frames (his XExit/KLow extension), his Fourier chain (submissions/dft/jacobalansussman-lever-2979-full-cut, Apache-2.0)
   and the Walsh-Hadamard corollary (wht-power-saving-lean, WHTCheck/Solution.lean). adapted from.
   Where: Engine/{ClassSetup,ClassBody,Moves,Recursion,Seam,TensorPower}.lean,
   Cert/{Label/Trie,Label/Sound,Warp/Shear,Stage/Window,Clifford/LabelMoves,StageRoute,
   Batch/Word}.lean, Transform/EngineUse.lean, Work/U7604/Chain/FourierTB/Main.lean (its first section,
   the Walsh-Hadamard transform, is modified from his WHTCheck/Solution.lean). His full header,
   with NOTICE.complex588 and LICENSE, is in Submission.lean.

3. Ryan Shea (shea256) (+codex); Nil Mamano: DFT Bridge3, the complex588 tree, gauged invocations and
   the bank adapters (`entW`, `entN`, `entW_form`; `host_adapt` follows their `bank_adapt`). adapted from.
   Where: Cert/Batch/Word.lean, Cert/Stage/Window.lean.

4. Dugongue #401 (CrocSwap/integer-mult-bounds): entrance gauges and residual banks (the idea that `entW`,
   `entN` implement). inspired/adapted from. Where: Cert/Stage/Window.lean, Cert/Base/Ops.lean, Cert/Batch/Word.lean.

5. Zhihao Chen (jacklightChen) (+codex), #377: the compressed nine-stage geometry and label layout.
   inspired/adapted from. Where: Cert/Stage/Window.lean (`Window137`).

6. George Lydakis (lydakis) (+codex), #275: bank patterns. inspired. Where: Cert/Stage/Window.lean (`Banks`).

7. DaysSky (+claude), #442 (and #363): idle-axis hosting. inspired. Where: Cert/Batch/Word.lean
   (`host_adapt`, `hostForm_frame`, built on Sussman's `frame_core_free` and Mamano/Shea's `bank_adapt`).

8. Cinna Davis (1337isnot1337) (+codex): strict tensor powers (PR4412, PR4414, PR4416); zxv (+codex):
   the higher-moment tail of PR4433. adapted from. Where: Engine/Moves.lean, Engine/TensorPower.lean.

9. Cinna Davis (+codex), #2226: borrowed helpers and their warps, replayed in the free warp algebra.
   adapted from. Where: Cert/Label/Trie.lean. Jeremy Kothe (#593 (+omp, opus 5.5), #799 lineage (+claude code))
   and DreamingOfClouds (#599) (+claude code, opus 5.5), with #604: hyperplane and cold exits and the tail-gate argument. inspired.
   Where: Cert/Stage/Window.lean (exit normal form; its Lean is Jacob Sussman's exit-frame extension, item 2).

10a. The supplier word of this submission, the native 64 word (canonical sha256
    27f6a6b9ed290fe69ab05e981981d7e51a5c7036146c278aaab244dc1a103306, layout sha256
    0ce3f9e383fc4bfdd22612b9e34fc9759d97204215937b82d23aec2cedd9b8ee, D=2 integer lowering sha256
    67a7fbf57464e8229093cfc9cbb6673b4fe9877731ba4bdfe3cf827bc396dd08): found with OpenAI Codex in research
    for this submitter. It adds chain shortcuts to the #8027 word of item 10 by exact rational construction
    with fractions.Fraction replays, the last twelve of them rank-preserving merges (eleven 1+1 -> 2, one
    2+1 -> 3). It keeps the 1,291 fields and pays 5,610 moves per call
    (1:3685 2:848 3:484 4:226 5:314 6:41 7:10 8:2). Where: the files of item 10.
    Item 10 below describes the word of PR 209's entry, from which this word is derived.

10. The supplier word of this entry, the #8027 rational consumer (word 38d2b3a2, PR head fb9b6a7b):
    adapted from Ali Romman (aliromman) (+codex), with the iterated-return programs supplied by Chris R
    (Clear1nsight) (+codex), per the #8027 README and PARENT-NOTICE. Where: Data/StageRoute/{Events,LabelRun,Residual,ScalarRun}.lean, Cert/StageRoute.lean,
    Cert/Scalar/{Decode,Checker}.lean, Data/BaseUnit/Rate.lean.
    Data provenance: research/p104-live-relative-gain/ of #8027 (head
    fb9b6a7b0d27da1cf98430893a3016bf811e2aa4). Its WORD.json.gz is the 1,289-field parent word 7e74ad15,
    which the PR's EVENTS.json (replay.py) rebuilds from #7830's double contraction word 7660985e (below);
    the PR's own journals rebuild the final word from it in the order WORD → BIDIRECTIONAL →
    BIDIRECTIONAL-QUOTIENT → HELPER-SPLITS (+2 fields) → BANK-FACTORS, giving the canonical word sha256
    38d2b3a2311a9ba5fee091cc7aa204c7ed95651aec95d75184b2391df090cbfb (1,291 fields, 5,674 paid moves per
    call) on the layout sha256 0ce3f9e383fc4bfdd22612b9e34fc9759d97204215937b82d23aec2cedd9b8ee; both
    hashes are the ones the PR states, and its APPLICATION-SOURCES.tar.gz has sha256
    d85d011ca74e8592c21c1e4db91a1a9021af26dcebc4dfdc2af7251f9c1bf968. The word was converted to the
    warp-certificate format W8027p.kfwd2.json (sha256
    680e3e006340b93f5297355201ed3754953e878b317dcfaee74f7848f5601932) and packed into the Lean data. The
    same rational word is carried by #8033 (its predecessor-8030 archive).
    The previous supplier word of this tree, the #7830 double contraction (word 7660985e, PR head
    87fbf4f7), adapted from Chris R (Clear1nsight) (+codex). Data provenance:
    research/p104-chart306-chain/DOUBLE-CANDIDATE.json.gz of #7830 (canonical word sha256
    7660985e0b618cdbee13e4190a4c6d5f91fbdf01a8f7a5186fdde8b980c19b48; word file sha256
    1b1b3294e86979f1f41076fb056f3c0a08ace6df7bf80f2886bc579a22962f4b; layout sha256
    f7de788c4a559282d35a9fce42f841a0e8de5a4015db871e718f9245569b0aa7, the layout of the #7786 continuation),
    converted to the warp-certificate format T1p.kfwd2.json (sha256
    80920a9a110b207fea0b2eb584d8d9398d043f1fd04f01c8cc9d99b0a6e0cdb5) and packed into the Lean data; it
    continues the #7786 word c447b6d5 (head 89a67c40), on #7781 and #7776's line.

11. The 48-call closed batch caller, its cyclic seam, placement and templates: adapted from Ali Romman
    (aliromman) (+codex), #7776. Where: Data/Batch/{Sched,TplR,Pack}.lean, Cert/Batch/{Park,Word}.lean,
    Cert/Control/Checker.lean, Data/BaseUnit/Rate.lean. Template R: Ali Romman's #7756 conjugate root and
    exact Gaussian proof. Template A: SYLforge's (+codex) #7700 A word. #7756 is also (+codex).

12. The signed caller (mirrored two-half construction) and its packed decoder: adapted from Rohan Arun
    (rohanarun) (+codex), #7113. Where: Cert/Control/Checker.lean, Cert/Base/Ops.lean.

13. The native word format (port classes, per-port contracts, invoice) and the two-class caller, which the
    controller language of Cert/Base/Ops.lean translates: adapted from Jerry Jiaheng Chen (@CubeJerry)
    (+codex), #7000 (BIT side #7001).

14. showed ideas are working (their words are behind #8027 or in my earlier entries, not in this tree's
    data): #7786 and #7781 Clear1nsight (+codex); #7774 Clear1nsight (+codex); #7604 Hao Yan (FanPUYen) (+codex);
    #7603 SYLforge (+codex); #7546 ToikY (+codex); #7605 Ali Romman (+codex); #7608/#7610/#7611/#7613 DreamingOfClouds (+claude code, opus 5.5);
    #7612 Chris R (Clear1nsight) (+codex, chatgpt pro, gpt-6.1-terra-high); owned772 CubeJerry (+codex);
    DreamingOfClouds (+claude code, opus 5.5) PR6143,
    PR6030, PR5907; Ali Romman (+codex) PR5827; Cinna Davis (+codex) PR4440, PR4470, PR4441, PR4447;
    zxv (+codex, chatgpt pro, astra 6.0, gpt-6.1 sol, opus 5.5) PR4359; the authors
    named in the older headers of Submission.lean; and the predecessors named in the #7776, #7830 and #8027
    NOTICEs. Douglas Colkitt/CrocSwap maintains the repository.

## Notices

These files hold code from, or merged with, Apache-2.0 sources and carry the line
`--might be  containing modified Apache-2.0 codes pieces from one or several sources; notices and credits: Credits.lean`:
  Algebra/DFTIdentities.lean, Compiler/{Judgment,Layout}.lean, Reel/Machinery.lean, Ripple/RoleMoves.lean,
  Transform/{ReelCompile,EngineUse}.lean (OpenAI);
  Engine/{ClassSetup,ClassBody,Moves,Recursion,Seam,TensorPower}.lean, Cert/Label/{Trie,Sound}.lean,
  Cert/Clifford/LabelMoves.lean, Cert/Stage/Window.lean, Cert/Warp/Shear.lean, Cert/StageRoute.lean,
  Cert/Batch/Word.lean (Jacob Sussman and the complex588 line);
  Work/U7604/Chain/FourierTB/Main.lean (OpenAI, Jacob Sussman).

These files hold only integer-side data (the #8027 word, the #7776 caller and their predecessors, whose
new material is Apache-2.0) and their own code; their use is credited in items 10-14, with no line in the
file: Data/Batch/{Pack,Sched,TplR}.lean, Data/BaseUnit/Rate.lean, Data/StageRoute/{Events,LabelRun,Residual,ScalarRun}.lean, Cert/Scalar/{Decode,Checker}.lean, Cert/Control/Checker.lean, Cert/Base/Ops.lean, Cert/Batch/Park.lean.
Cert/Scalar/Split.lean (new in this submission) holds only its own code (Claude, Anthropic). It builds on
the definitions of Cert/Scalar/Checker.lean (PR 209), and its header says so.

The notices are quoted word for word, each with the file it came from; "…" marks a cut working detail.

### A. Merged files, per merged block (share = fraction the same as the named source)

Work/U7604/Chain/FourierTB/Main.lean:
  Walsh-Hadamard section: Jacob Sussman, WHTCheck/Solution.lean, 0.78, modified (line in file)
  WorkingTransform 0.83 and WorkingPreparation 0.84: OpenAI, modified (notice in file)
  TransformProgram 0.60 and Asymptotics 0.55: OpenAI, heavily modified (line and notice in file)
  Goal definitions 0.47, WorkingCompiler 0.43, ArbitraryLength 0.45, UniformBounds 0.38,
  ConvolutionProgram 0.045, Main 0.11: OpenAI, inspired/adapted from (notices in B)
Transform/EngineUse.lean:
  SectorAlgorithm 0.72: OpenAI, modified (notice in file)
  SynchronizedAlgorithm 0.75: OpenAI, modified (line and notice in file)
  the seam 0.19 and the engine statement 0.0: inspired/adapted from OpenAI's hills_program (notices in B)
  (whole file: 0.67 the same as Jacob Sussman's lever-2979 Work/FourierL2979Fc/Merged1.lean, itself from OpenAI)

Blocks with an in-file line keep it there (and Submission.lean keeps Jacob Sussman's header, with the
upstream NOTICE.complex588 and LICENSE); the notices of the other blocks are in B.

Cert/Label/Trie.lean: checker definitions from Jacob Sussman's lever-2979 Work/GCert/Labels/Def.lean and
  Work/KLowW/{LabK,ScalK}.lean (best single source 0.15, whole file 0.57), heavily modified (line in file)

### B. Notices moved here from the files of this tree

These are the notices as they stood in earlier versions of the files. Where they say so, read them with
this tree's state: OpenAI's original files are not in this repository (only Goal, RAM and Core of
openai/math are); the `TB19` suffix is kept on some names only; the seam and the goal definitions are now
in Transform/EngineUse.lean and Work/U7604/Chain/FourierTB/Main.lean; and the comments of the copies have
been removed. The notices kept in the files (§A) state this directly.

From Transform/EngineUse.lean:

    New file, not a copy of an OpenAI file: … It contains lines 95-99 of
    lean/OAI/Computability/FourierTransform/TensorProgram.lean (the statement of `hills_program`) and line 114 of
    lean/OAI/Computability/FourierTransform/TensorSaving.lean (the definition of `hills`) of github.com/openai/math
    (commit fd4aeeb, Apache-2.0), with `hills`, `alpha` replaced by `baseEnvelope`, `baseEngineExp`.

From Transform/EngineUse.lean:

    New file, not a copy of an OpenAI file.  `EngShape.TB19.EngineStmt` is OpenAI's `hills_program` statement (lines 95-99 of
    lean/OAI/Computability/FourierTransform/TensorProgram.lean of github.com/openai/math, commit fd4aeeb, Apache-2.0) as a
    proposition, with the envelope `envelope z k = ⌈(k+1)^z⌉` at the seam exponent `z = 1 - 3880136443749/10^15` in the place
    of `hills`, for index types `ι` in one universe. …

From Transform/EngineUse.lean:

    (Copy of #41's file Work/T16A8Z/Stmt.lean, numbers changed.)

From Work/U7604/Chain/FourierTB/Main.lean:

    Modified copy of five definitions of lean/OAI/Computability/FourierTransform/Goal.lean of
    github.com/openai/math (commit fd4aeeb, Apache-2.0; lines 30, 35, 75-78, 80, 82), as in #41's file
    Work/FourierT16A8Z/Goal.lean. Changed for this repository:
      * the exponent `1 - 1/(10^(13:ℕ))` is replaced by `1 - statedSavingTB19`;
      * the five names have the suffix `TB19` (OpenAI's own definitions keep their names and values).
    Everything else they mention (`paperTime`, `nlogn`, `DFTProgram`, `ConvProgram`) is OpenAI's own,
    imported unmodified.

From Work/U7604/Chain/FourierTB/Main.lean:

    Modified copy of lean/OAI/Computability/FourierTransform/WorkingCompiler.lean of github.com/openai/math
    (commit fd4aeeb, Apache-2.0) …. OpenAI's file itself is
    unmodified in this repository and still imported. Changed for this repository, all mechanically:
      * every declaration of this file (and of the other 10 copied files) has the suffix `TB19`
        on its name, so that it does not collide with OpenAI's original;
      * OpenAI's exponent `alpha = 1 - 2/10^11` and envelope `hills` are replaced by
        `baseEngineExp = 1 - 3880136443749/10^15` and `baseEnvelope` (Work/U7604/Chain/FourierTB/Seam.lean), and the single use of
        OpenAI's `hills_program` by `baseEnvelope_program`;
      * `decimalExponent`, `decimalTime`, `TimeBounds`, `DFTGoal`, `ConvGoal` are replaced by their
        `TB19` versions from Transform/SavingGoal.lean (exponent `1 - statedSavingTB19`);
      * imports point to the copies.
      * (this copy) the suffix `T16A8Z` of #41's chain (Work/FourierT16A8Z) is now `TB19`, the seam
        `1 - 3880136443749/10^15` and the stated exponent `1 - statedSavingTB19` ….
    Comments and docstrings below are OpenAI's and describe OpenAI's network, not ours.

From Work/U7604/Chain/FourierTB/Main.lean:

    Modified copy of lean/OAI/Computability/FourierTransform/ArbitraryLength.lean of github.com/openai/math
    (commit fd4aeeb, Apache-2.0) …. OpenAI's file itself is
    unmodified in this repository and still imported. Changed for this repository, all mechanically:
      * every declaration of this file (and of the other 10 copied files) has the suffix `TB19`
        on its name, so that it does not collide with OpenAI's original;
      * OpenAI's exponent `alpha = 1 - 2/10^11` and envelope `hills` are replaced by
        `baseEngineExp = 1 - 3880136443749/10^15` and `baseEnvelope` (Work/U7604/Chain/FourierTB/Seam.lean), and the single use of
        OpenAI's `hills_program` by `baseEnvelope_program`;
      * `decimalExponent`, `decimalTime`, `TimeBounds`, `DFTGoal`, `ConvGoal` are replaced by their
        `TB19` versions from Transform/SavingGoal.lean (exponent `1 - statedSavingTB19`);
      * imports point to the copies.
      * (this copy) the suffix `T16A8Z` of #41's chain (Work/FourierT16A8Z) is now `TB19`, the seam
        `1 - 3880136443749/10^15` and the stated exponent `1 - statedSavingTB19` ….
    Comments and docstrings below are OpenAI's and describe OpenAI's network, not ours.

From Work/U7604/Chain/FourierTB/Main.lean:

    Modified copy of lean/OAI/Computability/FourierTransform/ConvolutionProgram.lean of github.com/openai/math
    (commit fd4aeeb, Apache-2.0) …. OpenAI's file itself is
    unmodified in this repository and still imported. Changed for this repository, all mechanically:
      * every declaration of this file (and of the other 10 copied files) has the suffix `TB19`
        on its name, so that it does not collide with OpenAI's original;
      * OpenAI's exponent `alpha = 1 - 2/10^11` and envelope `hills` are replaced by
        `baseEngineExp = 1 - 3880136443749/10^15` and `baseEnvelope` (Work/U7604/Chain/FourierTB/Seam.lean), and the single use of
        OpenAI's `hills_program` by `baseEnvelope_program`;
      * `decimalExponent`, `decimalTime`, `TimeBounds`, `DFTGoal`, `ConvGoal` are replaced by their
        `TB19` versions from Transform/SavingGoal.lean (exponent `1 - statedSavingTB19`);
      * imports point to the copies.
      * (this copy) the suffix `T16A8Z` of #41's chain (Work/FourierT16A8Z) is now `TB19`, the seam
        `1 - 3880136443749/10^15` and the stated exponent `1 - statedSavingTB19` ….
    Comments and docstrings below are OpenAI's and describe OpenAI's network, not ours.

From Work/U7604/Chain/FourierTB/Main.lean:

    Modified copy of lean/OAI/Computability/FourierTransform/UniformBounds.lean of github.com/openai/math
    (commit fd4aeeb, Apache-2.0) …. OpenAI's file itself is
    unmodified in this repository and still imported. Changed for this repository, all mechanically:
      * every declaration of this file (and of the other 10 copied files) has the suffix `TB19`
        on its name, so that it does not collide with OpenAI's original;
      * OpenAI's exponent `alpha = 1 - 2/10^11` and envelope `hills` are replaced by
        `baseEngineExp = 1 - 3880136443749/10^15` and `baseEnvelope` (Work/U7604/Chain/FourierTB/Seam.lean), and the single use of
        OpenAI's `hills_program` by `baseEnvelope_program`;
      * `decimalExponent`, `decimalTime`, `TimeBounds`, `DFTGoal`, `ConvGoal` are replaced by their
        `TB19` versions from Transform/SavingGoal.lean (exponent `1 - statedSavingTB19`);
      * imports point to the copies.
      * (this copy) the suffix `T16A8Z` of #41's chain (Work/FourierT16A8Z) is now `TB19`, the seam
        `1 - 3880136443749/10^15` and the stated exponent `1 - statedSavingTB19` ….
    Comments and docstrings below are OpenAI's and describe OpenAI's network, not ours.

From Work/U7604/Chain/FourierTB/Main.lean:

    Modified copy of lean/OAI/Computability/FourierTransform/Main.lean of github.com/openai/math
    (commit fd4aeeb, Apache-2.0) …. OpenAI's file itself is
    unmodified in this repository and still imported. Changed for this repository, all mechanically:
      * every declaration of this file (and of the other 10 copied files) has the suffix `TB19`
        on its name, so that it does not collide with OpenAI's original;
      * OpenAI's exponent `alpha = 1 - 2/10^11` and envelope `hills` are replaced by
        `baseEngineExp = 1 - 3880136443749/10^15` and `baseEnvelope` (Work/U7604/Chain/FourierTB/Seam.lean), and the single use of
        OpenAI's `hills_program` by `baseEnvelope_program`;
      * `decimalExponent`, `decimalTime`, `TimeBounds`, `DFTGoal`, `ConvGoal` are replaced by their
        `TB19` versions from Transform/SavingGoal.lean (exponent `1 - statedSavingTB19`);
      * imports point to the copies.
      * (this copy) the suffix `T16A8Z` of #41's chain (Work/FourierT16A8Z) is now `TB19`, the seam
        `1 - 3880136443749/10^15` and the stated exponent `1 - statedSavingTB19` ….
      * literal `let d : ℝ := 2/(10:ℝ)^11` -> `let d : ℝ := 3880136443749/(10:ℝ)^15` (alpha_thetaTB19: the local constant d must equal 1 - baseEngineExp)
      * `theorem transform_mainTB19 : DFTGoalSharp :=`: docstring added
      * `theorem convolution_main_sharp : ConvGoalSharp :=`: docstring added
    Comments and docstrings below are OpenAI's and describe OpenAI's network, not ours.

From Cert/Batch/Word.lean:

    Fresh namespace `OAI.PowerSaving.HostPad`.  … adapted from
    Work/Bank401 (Shea's complex588 tree at 0e61af6), prepared with assistance from Claude.  No `sorry`.

From Data/Batch/TplR.lean (part of the line):

    Credits: #7776 / #7700 (SYLforge) A word.

From Data/Batch/TplR.lean (part of the line):

    Credits: Ali Romman (#7756 conjugate root and exact Gaussian proof, #7776 cyclic seam).

From Engine/TensorPower.lean (3 lines) and Engine/Moves.lean (1 line):

    -- changed for the tensor-power extension (30103/10000000); see Submission.lean

### C. Notices of earlier files of this tree (COMB62), whose code is now in the files named

From Algebra/VandermondeFactor.lean, now in Algebra/DFTIdentities.lean:

     Interface follows the OpenAI
    Computability/FourierTransform package (Apache-2.0), whose notices are retained in the
    release tree.

From Cert/Label/Sound.lean, now in Cert/Stage/Window.lean and Cert/Label/Sound.lean:

    DFT Bridge3, 2026-10-11.  
    Credits: Jacob Sussman (engine, chain, Apache-2.0); Dugongue (#401 entrance gauges).  

From Cert/Stage/GaugeRun.lean, now in Cert/StageRoute.lean:

    Credit: p-warpchk (Work/KLowW, Apache-2.0, as used by #41) …; the copied proofs are unchanged.

From Cert/Stage/Window137.lean, now in Cert/Stage/Window.lean:

    Credit: the label geometry and every proof pattern are Jacob Sussman's (`Work.BridgeGeom`, Apache-2.0); the
    compressed layout is jacklightChen's (PR #377).
    Credit: Jacob Sussman's `Work.BridgeGeom.Stage` (Apache-2.0), proof by proof; layout of PR #377 (jacklightChen).

From Cert/Warp/Shear.lean, now in Cert/Warp/Shear.lean and Cert/Stage/Window.lean:

    DFT Bridge3, 2026-10-11.  
      Entrance gauges and residual banks: Dugongue (CrocSwap/integer-mult-bounds PR #401); bank patterns: Lydakis (#275);
      engine: Jacob Sussman.
    Credits: the engine (`coordFrame`, `phasedPerm`, `coreFrame`, `Free`, `GRoute`, `gstep_free`, the invocation package) is Jacob Sussman's
    (wht-power-saving-lean, Apache-2.0); `GInvE`, `entW`, `entN`, `BankSched` are DFT Bridge3's / Nil Mamano's as used in
    Ryan Shea's shea256/fourier-transform-below-nlogn lean/complex588, on Dugongue's entrance gauges (#401); `pk_cperm`,
    `cperm` are from Work/Bank401/Adapt (same authors); the exit frames are the hub's (#593/#599 hyperplane ends, cold
    ends; #799 Kothe lineage).
    …  

From Cert/Warp/StageInvariant.lean, now in Cert/Warp/Shear.lean:

    Credit: p-warpchk (Work/KLowW, Apache-2.0, as used by #41); the copied proofs are unchanged.

-/
