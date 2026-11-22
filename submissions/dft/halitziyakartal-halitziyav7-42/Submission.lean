/-
Big O Speedrun submission: exact DFT of every length, and convolution, with saving
389848144653/100000000000000 (= 0.00389848144653; the certificate holds at 194924072327/(5·10^13) = 0.00389848144654), in OpenAI's
exact computational model.
Entry point: Work/U7604/Chain/FourierTB/Main.lean.

What is new over my previous entry, submissions/dft/halitziyakartal-halitziyav6-pi
(bigospeedrun/verifier PR #156, saving π/1000), whose header follows below unchanged: a new
supplier word and a new controller, #7776's closed 48-call batch caller (Ali Romman, aliromman
4f7c67a, research/p104-dual-supplier-lift), in place of the owned772 word and Ali Romman's 19-leaf
binary query tree, on a rebuilt tree.
* the supplier: the complex native word of #8027 (Ali Romman, aliromman, with Codex; PR head fb9b6a7b,
  research/p104-live-relative-gain/, rebuilt by the PR's journals; word sha256 38d2b3a2...cbfb, layout
  0ce3f9e3...b8ee), after #7830's double paid-chain contraction (Chris R, Clear1nsight, with Codex;
  payload sha256 7660985e...9b48), which continues the #7786 "iterated returns" word at head 89a67c40
  (continuation/WORD.json.gz, payload sha256 c447b6d5...83cb), which extends
  the earlier #7786 word (e40b999d...cec3), which builds on #7781 (Clear1nsight, subdivided helper
  births), which builds on #7776's line (Ali Romman) with #7774's paid replacements and #7756's
  native graph. Lowered event by event and checked by the dense word replay (the path Work/U7604 is
  kept from my previous entry). Same 200 ports and per-port end contracts; now 891 helper
  slots and 733 owned fields. Per call it pays 1:3809 2:792 3:480 4:226 5:314 6:41 7:10 8:2, and its
  helpers end at ranks 1:21 2:9 3:10 4:241 5:33 6:1 7:14 8:33 9:529;
* the unit: the 48-call batch; per gauge copy it pays blocks of rank
  1:183312 2:38016 3:23040 4:10848 5:15072 6:1968 7:480 8:1344 16:1248 24:1248 32:1248 40:1248
  48:1248 56:1248
  and leaves jobs of
  1:1008 2:432 3:480 4:11568 5:1584 6:48 7:672 8:1584 9:25872 17:1248 25:1248 33:1248 41:1248 49:1248
  57:1248 65:1248 129:624
  axes (Data/BaseUnit/Rate.lean, `blockHist` and `targetHist`);
* the tensor power: as before (12^12800 / 11^12800); the rate certificate holds at
  1 - 194924072327/(5·10^13) (Data/BaseUnit/Rate.lean), the seam at 1 - 3898481446539/10^15, and the stated saving
  is the one constant statedSavingTB19 (Work/U7604/Chain/FourierTB/Main.lean);
* the tree is rebuilt against my previous entry (38 Lean files): the word's data, packed and
  decoded inside Lean, and its checks (Data/StageRoute/, Cert/StageRoute.lean, Cert/Scalar/), the
  batch caller and the unit's native price (Data/Batch/, Cert/Batch/, Data/BaseUnit/Rate.lean), the
  checkers and the engine (Cert/, Engine/), and the chain (Work/U7604/Chain/FourierTB/Main.lean);
  OpenAI's files are kept unchanged except their import lines; ideas credited in central/Credits.lean.

Credits: the headers of my previous entries below credit the construction and everything it
builds on.
  Author and supervisor: Halit Ziya KARTAL (https://github.com/HalitZiyaKARTAL,
  https://halitziyakartal.github.io).
  credit:  organized whole thing while models like opus was making lots of retarded mistakes, or dumb limits at claude code, also including claude resetting the container that was just left for something like 15 mins  unused, which erased data like my record was ready so i made and used new tools that recover information with even automating mcp tools etc etc, well it add me experience at least,  i was also using opus deepseek hybrid since anthropic tokenizer and was too suboptimal like i had to use heater(my another tool to keep cache warm) etc,  anyway after meddling with claude code binary more i got more experience and sidestepped older limiters i got and used multiple containers to compile lean branches etc etc  which shown mathlib was very bad at lean and nanoda memory,
  when i removed it i was able to compile something like 4 at once per container ( i was under 10 min for lean but new words i used had problematic events that soak ram and cpu so i optimized some more) also after reaching 500 file and one version was being 100mb i optimized hard so made whole lean tree able to fit something like 500-600k tokens of deepseek, which made it simpler since it meant no read requirement from now on(i was using my other tools like building agents copying rewinding, sending agents between sessions etc etc to handle them,  also weirdly i got lots of classifier false positives during math work where deepseek helped more, also fable had less false positives, but didn't add much since it didn't add much more to opus,  anyways basically i coordinated whole thing and handled bottlenecks,  tried to close weak local minima issues of models etc etc thus resulted in improvements, i also have lean for integer side too but i also waited it for credits which costs time, probably a bit dumb desicion to wait for them,
  but math side have 6 open claims as axioms(i had proven it unconditional(3 classics) for 6e-5 and rest was upgrade package making something like 34/10000), i kinda half solved them too, soo if you have compute to share i can also list under compute sponsors if you want( tokens i meant, and not dumb ones like haiku considering even opus does random rm rf calls etc ) anyways trying to keep shorter now, i could send more to pr maybe but i have other projects to handle too so i am not sure, also i plan to redo whole tree a bit more since its still suboptimal for my taste, soo thats kinda it for now you and comment pr to reach, bye for now
  LLM credits↓
  primarily with heavily modified claude code and  opus 5.5 deepseek fable 5.2 hybrid and some other models-harnesses( if anyone wants to sponsor i can try to do some with their models or harness too, or if economic i can mention as sponsors in credits)

  note: i was planning to share at 33
  365 365.25 366.25 etc (double digit easter eggs i hide at pi, and year easter eggs including astronomical ones too) but i wasted time so i will probably share more regular one this time(but i still put a 42 as file number:)  )
-/

/-
Big O Speedrun submission: exact DFT of every length, and convolution, with saving exactly
π/1000 (Race.bound_pi: O(n (log n)^(1 - Real.pi / 1000))), in OpenAI's exact computational
model. Entry point: Work/BQT/FourierTB/Main.lean.
The board's bound field takes a reduced fraction only, so manifest.json and Race.bound carry
π/1000, cut right after π's first 33 (…26433): 31415926535897932384626433/10^28. Race.bound
follows from Race.bound_pi, since that fraction is below π/1000 (Work/BQT/PiCut.lean).

What is new over my previous entry, submissions/dft/halitziyakartal-halitziyav5-pre-pi
(bigospeedrun/verifier PR #91, saving 312780997/100000000000): a new controller on the same
supplier. The supplier (the owned772 P104 word, read forward only), the engine, the strict
tensor power and the Fourier chain are those of #91, whose header follows below unchanged
(with #41's and Jacob Sussman's headers under it). The controller is now a binary tree of
query suppliers instead of #41's 16-pair path:
* the caller: Ali Romman's binary query tree: a four-field query extension (two child query
  suppliers, one paid thin query and a paired whole idle give a new query supplier and two
  independent Gaussian outputs), a root of three suppliers with no idle, and the 19-leaf tree
  with root children of 4, 7 and 8 leaves; 19 full calls, 16 thin queries and 34 main fields
  per port, on a 19-stage geometry with 153 label coordinates (Work/BQT/G19);
* new Lean: the controller in #41's controller language (Work/BQT/Ctrl.lean, BQ19.ctrl_diag:
  385 events, every main role ends at one monomial of its own input); the tree's other thin
  query orientation Y += Q X, which is one rank-1 block like Y += Q^-1 X
  (Work/BQT/BQ19/Thin.lean, greach_frame_single); its exponent -1 leaves as #91's backward
  reading; the unit's roles, stages, windows, word and certificate (Work/BQT/BQ19); the raw
  certificate on #91's supplier (Work/BQT/RawBQT772.lean). Per gauge copy it pays blocks of rank
  1:43768 2:8683 3:9424 4:1900 5:3097 6:152 7:171 8:19 16:1872 24:208 32:832 56:208 64:208
  and leaves jobs of
  1:266 2:152 3:76 4:2033 5:266 6:38 7:171 8:361 9:7315 17:1872 25:208 33:832 57:208 65:208 153:208
  axes (raw root about 3.1484983e-3);
* the tensor power: the 12800-fold tensor product of the certified unit, completed to 13^12800
  and split at 12^12800 (the 16/17 pair of #41 and #91 does not fit this unit); the rate
  certificate holds at 1 - 67/21280 (67/21280 = 0.0031484962406, Work/BQT/RateBQT772.lean),
  the seam at 1 - 3148496240/10^12, and the stated saving is the one constant
  statedSavingTB19 = π/1000 (Work/BQT/FourierTB/Goal.lean), below the seam since π < 3.1416
  (Mathlib's Real.pi_lt_d4);
* the board's fraction: 3.1415926535897932384626433 < π (Work/BQT/PiCut.lean, by Mathlib's
  pi_lower_bound method, whose own bounds stop at 20 decimals);
* every new file of this entry is in Work/BQT/; every other file is from my previous entry,
  unchanged.
The private theorems marker_* at the end of 42 files of Work/FwdOnly and Work/BQT are the
author's markers, intentional; they do not affect the proof.

Credits: the header of my previous entry below credits the supplier, the construction and
everything they build on.
  adapted from Ali Romman's research/balanced-query-tree (CrocSwap/integer-mult-bounds
    PR #6348): the binary query tree caller (the four-field query extension with its paid idle,
    the three-supplier root, the 19-leaf tree 4, 7, 8), translated here into #41's controller
    language; the thin query and query-thinned path it extends are Cinna Davis' (PR4440,
    PR4470), credited in #41's header.
  Author and supervisor: Halit Ziya KARTAL (https://github.com/HalitZiyaKARTAL,
  https://halitziyakartal.github.io).
  LLM credits↓
  claude code continued working as usual

  note: huh i finally got to π/1000, took a bit longer,  i also planted few more easter eggs there :)   wondering if leaderboard is gonna use letter pi or fraction which also have few easter eggs and also a teaser,  also in #91 i forgot notes in files since i had low usage and send a bit hurried,  hoping this one is more polished,  if anyone wants to cooperate i am open too
-/

/-
Big O Speedrun submission: exact DFT of every length, and convolution, with saving
312780997/100000000000 (about 3.1278e-3), in OpenAI's exact computational model.
Entry point: Work/FwdOnly/FourierT104W/Main.lean.

What is new over my previous entry, submissions/dft/halitziyakartal-halitziyav4-logception
(bigospeedrun/verifier PR #41, saving 30103/10000000): a new supplier in the same construction. The
controller unit, its tensor power and the engine are those of #41, whose header follows below
unchanged (with Jacob Sussman's header under it). The supplier is now the community's P104 word,
read forward only:
* the supplier: the owned772 P104 word of research/p104-owned772-relay-descent (CrocSwap/
  integer-mult-bounds), taken as published (WORD.json.gz, payload sha256
  44e8ef6bfd6fd0aae5252861534b968f241f3f48b7f9266be2e981bf84a219a8) and lowered event by event to
  Sussman's warp certificate format (Work/FwdOnly/Gen/P104W*): 104 ports, 562 helper slots, 29
  owned fields, 1093 frames, 22834 events. Per call it pays 1:2216 2:457 3:496 4:100 5:163 6:8 7:9
  8:1, and its helpers end at ranks 1:14 2:8 3:4 4:107 5:14 6:2 7:9 8:19 9:385;
* forward only: the word clears its owned fields without uncomputing them, so it has no backward
  (dual) reading, which Sussman's certificate asks for. New Lean: the forward half of his warp
  certificate (Work/FwdOnly/KFwd.lean; a clear is his zeroing scale, sound for any content), and
  the backward route of every call obtained from its forward route by a free wrapper of signed
  exchanges and central-square translations, B = R^-1 F R (Work/FwdOnly/BwdWrap.lean, for every
  conjugation window of the unit). The scalar replay of the word is checked by the kernel in seven
  segments, composed in Lean, so that no module needs more than about 4 GB;
* the unit: #41's 16-pair query-thinned controller (PR4440, Cinna Davis), prefix a = 8, on the
  18-stage geometry with 145 label coordinates, now on this supplier. Per gauge copy it pays blocks
  of rank
  1:41448 2:8226 3:8928 4:1800 5:2934 6:144 7:162 8:18 16:416 24:416 32:416 40:416 48:416 56:416
  64:416 72:208
  and leaves jobs of
  1:252 2:144 3:72 4:1926 5:252 6:36 7:162 8:342 9:6930 17:416 25:416 33:416 41:416 49:416 57:416
  65:416 73:208 145:208
  axes (raw root about 3.1278114e-3);
* the tensor power: the 11340-fold tensor product of the certified unit, made strict as in #41
  (PR4412, PR4414, PR4416): every job is completed to 17^11340 axes and every paid block is split at
  16^11340; the rate certificate holds at 1 - 727/232431 (727/232431 = 0.0031278099737,
  Work/FwdOnly/P104WRate.lean), the seam at 1 - 3127809973/10^12, and the stated saving is the one
  constant statedSavingT104W (Work/FwdOnly/FourierT104W/Goal.lean);
* every new file of this entry is in Work/FwdOnly/; every other file is from my previous entry,
  unchanged.

Credits: the header of my previous entry below credits the construction and everything it builds on.
  adapted from research/p104-owned772-relay-descent (CubeJerry; prepared with OpenAI Codex, as its
    PROOF.md says; commit f714f27d6 on CrocSwap/integer-mult-bounds main): the owned772 word itself.
  adapted from DreamingOfClouds' PR6143 (research/p104-root-relay-descent), PR6030
    (research/p104-helper470-twin-rung-removal) and PR5907 (research/p104-helper468-rung-removal):
    the relay descents and rung removals that word is built on.
  adapted from Ali Romman's PR5827 (research/p104-unread-path-resynthesis): the word and checker
    chain of that line; inspired by his research/p104-productive-controller (PROOF.md section 3,
    the inverse of his direct wrapper of PR5398): a forward-only caller whose backward interfaces
    are signed exchanges and central-square translations, which Work/FwdOnly/BwdWrap.lean proves
    in Lean for this model.
  the P104 lineage before them (from PR2305, with PR2219 and PR2152) is credited in their NOTICE
    files.
  Author and supervisor: Halit Ziya KARTAL (https://github.com/HalitZiyaKARTAL,
  https://halitziyakartal.github.io).
  LLM credits↓
  claude code continued working as usual

  note:  umm i kept it as backup so it might not be polished enough, it was a draft i kept before targeting pi/1000 so if anything weird notify me ( at ai i kinda reached my usage limit so i kinda handled it manually some parts, which might be caused weak internal reviews( i usually let ai check deep before publish to be safe))  also if anyone wants to cooperate i am also open to it, since its a bit boring doing it myself solo,  especially at integer side which used lots of compute and budget
-/

/-
Big O Speedrun submission: exact DFT of every length, and convolution, with saving
30103/10000000 (about 3.0103e-3: log10(2)/100 rounded up in its fifth digit, on purpose; see
the note in the credits), in OpenAI's exact computational model.
Entry point: Work/FourierT16A8Z/Main.lean.

What is new over my previous entry, submissions/dft/halitziyakartal-halitziyav3-tensor
(bigospeedrun/verifier PR #40, saving 26159999/10000000000): about 15% more saving, from a larger
unit of the same controller family on a patched native supplier, in the same construction, a
tensor power of a productive-helper unit, run in the engine of Jacob Sussman's entry
submissions/dft/jacobalansussman-lever-2979-full-cut (saving 3577409/2000000000), whose header
follows below unchanged. The supplier, the unit and the tensor power are adapted from the
integer-multiplication line (CrocSwap/integer-mult-bounds):
* the supplier: the #2979 word as patched in PR4470 (Cinna Davis: a joint optimization of helper
  entrances, exits and scalar contact frames), on zxv's exact native supplier, with the retiming of
  PR4441 and the missing span of PR4447 (Cinna Davis). Its native data is generated here from
  PR4470's published files with Sussman's generators and certified in his format
  (Work/GCert/Data/Gen/S2979Z*, Work/PWGen, Work/P4L/LFBaseZ), with no zero buffers and 8 centre
  copies. Per call it pays 1:2237 2:388 3:494 4:147 5:36 8:8, and its helpers end at ranks
  4:28 7:7 8:47 9:326;
* the unit: the 16-pair query-thinned controller of PR4440 (Cinna Davis), prefix a = 8, on that
  supplier and an 18-stage geometry with 145 label coordinates: eighteen full native calls,
  fifteen windows, and fifteen thin queries per port (a copy into fresh scratch, one rank-1 step,
  an add back); every helper slot is a fresh productive helper job (PR4359, zxv) that ends on its
  residual rank. Per gauge copy it pays blocks of rank
  1:41946 2:6984 3:8892 4:2646 5:648 8:144 16:448 24:448 32:448 40:448 48:448 56:448 64:448 72:224
  and leaves jobs of
  4:504 7:126 8:846 9:5868 17:448 25:448 33:448 41:448 49:448 57:448 65:448 73:224 145:224
  axes (raw root about 3.0201660e-3);
* the tensor power: the 7760-fold tensor product of the certified unit, made strict as in the
  strict tensor powers of PR4412, PR4414 and PR4416 (Cinna Davis): every job is completed to
  21^7760 axes and every paid block is split at 20^7760, so every paid block is smaller than every
  job and Sussman's mixed-target recursion applies; the rate certificate holds at
  1 - 4719/1562500, and the stated saving is kept below it at 30103/10000000;
* new Lean: the certified supplier above, the 18-stage geometry (Work/G18), the controller, roles,
  stages, thin queries, windows, word and certificate of the unit (Work/P16A8) on the operator
  semantics, frames and segments of Work/P4L and Work/P3/Ctrl4, fresh productive helpers as live
  roles (Work/Fresh/Helpers), a rule for any list of job sizes (Work/Mixed/MultiTarget,
  Work/Mixed/Bridge/CoreK), the tensor product of certified words with its powers, strict form and
  engine (Work/TensorEng), the rate certificate (Work/TensorProto) and the chain Work/T16A8Z,
  Work/FourierT16A8Z, adapted from Sussman's chain. Every other file is his, unchanged; files of
  his that this proof does not import are left out.

Credits: Jacob Sussman's header below credits his construction and everything it builds on;
the credits of my earlier work are in the header of my previous entry (its Submission.lean).
  Author and supervisor: Halit Ziya KARTAL (https://github.com/HalitZiyaKARTAL,
  https://halitziyakartal.github.io).
  LLM credits↓
  claude code continued working as usual

  note: i intentionally made it O(n(logn)^(1-(log2)/100))  can be nice to keep it at least until someone gets to π(pi)/1000   it looks more funny this way :)
-/

/-
Big O Speedrun submission: exact DFT of every length, and convolution, with saving
3577409/2000000000 (= 17887045/10^10, about 1.7887e-3), in OpenAI's exact
computational model. Submitted by Jacob Sussman (GitHub: jacobalansussman).

What is new in this proof
Every entry on this board before my lever submissions gives each array of its circuit a job of
the same size. This proof uses a new recursion that feeds a circuit with jobs of two sizes in a
fixed ratio (the mixed-target recursion), and a step I call the lever. The circuit is the
community's circuit of CrocSwap/integer-mult-bounds pull request #2979, with one change: a new
table of where helper storage goes, which I solved for this proof with the allocation model and
the placement program of the community's #3815 (made tolerant: 9 roles with no planned slot
left went to free places that obey the same rules). The words, the order of the runs and the
dispatch stay #2979's; #2979's own owner engine accepts the new table, and so do the other
checks of #2979's line except those that ask for a higher figure without the lever. In it,
16,576 blocks of rank 48 in each round are the first operation on their own array, and no other
idle block has rank 48. This proof removes each of them entirely (the full cut), so that its
array takes a job of 25 axes instead of 73; nothing has to be split. The recursion stays
correct as long as every paid block is smaller than every job (23 < 25). Without the lever the
new table is worse than #2979's own; it pays off only with the full cut. The Lean proofs of the
recursion, of the head lemma behind the cut, and of the port of the #2979 circuit (74 copies,
666 runs, helper storage hosted across copies, borrowed helpers with free linear changes of
coordinates) are new. Underneath are my earlier extensions of the engine, first published in
the fifth revision of my repository: exit frames (under Submission/XExit/) and hosting of
helper storage (Submission/Work/XHost*/). The new files were written by the agents (Claude)
working with me. They are machine-checked; a line-by-line human review has not been done yet,
and I would welcome one.

Credits
- Marius-Paul Dumitrean (with Anthropic Claude): the #2979 circuit (joint rank-7 end frames),
  on his #2942 and #2930, Jeremy Kothe's rewrites (#2957, #2948, #2966) and his preload
  supplier and frame accounting (#2894, #2833), Mason Hale's paired extractions and T74
  chronology (#2917), Jeremy Diviney's paired extraction and certificate (#2908), Dugongue's
  composition and packing lineage (#2969, #2863, #2839: the owner engine that checks the new
  table), Yiyang Lu's flow model (#2857, #2848), Ross Richardson's rank-seven obstruction
  (#2918), Tekalign's owner checker, icekylinx's auditor, themilkman216's integrality
  observation and Gareth Davidson's terminal-subspace bounds (#1995, #2013).
- Erwan Secousses / ChaloupeMusic (#3815): the allocation model and the placement program
  with which the new table was made.
- Cinna Davis (1337isnot1337, #2226, with OpenAI Codex): the borrowed helpers and their warps,
  and the exact Clifford machinery that checks them; Jeremy Kothe (#2312): the width exchange;
  icekylinx, DreamingOfClouds and chafreaky: the native and wrapper lineage underneath.
- Rohan Arun, Marius-Paul Dumitrean, Jeremy Kothe, LeverRank, Thomas DiFiore, Jeremy Diviney,
  Chafik Boukhalfa (chafreaky) and Vlado Vojdanovski: the T74 layout the circuit grows from.
- Ryan Shea: the conversion pipeline, the generators and the Lean tree this proof is laid over.
- Nil Mamano: the gauged Lean extension, the Lean files of the nine-stage network and the
  Fourier chain templates of his record submission.
- Dugongue (#401), Zhihao Chen / jacklightChen (#377, #425), lydakis (#275) and DaysSky (#363):
  the entrance gauges and banks, the compressed layout and the argument for mutable sources, the
  bank patterns, the bridged layout and the idea of hosting helpers in idle arrays.
- The authors of CrocSwap/integer-mult-bounds, whose circuits and checks all of this builds on.
- OpenAI: the exact computational model, the statement and the all-length reduction
  (openai/math).
- Jacob Sussman (me): the Lean engine that the earlier entries run on, its extensions for exit
  frames, mutable sources and hosting, the mixed-target recursion, the lever with its full cut,
  the new table and the port.
The complete list, with every pull request, is in the NOTICE of the programs repository below.

Source and packaging
Base: https://github.com/shea256/fourier-transform-below-nlogn, commit
52394849c7ecf3412d39b925d75fc7fdb98994d8, directory lean/complex588. No file of the base
is modified. 286 of the 577 modules of the proof closure are new files.
Entry point: Work/FourierL2979Fc/Main.lean, transform_mainL2979Fc.
The 577-module proof closure is copied under Submission/, changing local import paths
only; this is the packaging of the earlier entry submissions/dft/nmamano-shea-c588, and the
same script reproduces that folder byte for byte. Then, for the verifier's limit of 500
files, 153 small modules (generated data, and chains of modules each importing the one before)
are merged into 23 modules, leaving 447. Each merged module starts with a comment that lists
its members with the sha256 of each original file, and copies each member verbatim after its
import lines, inside its own section; every other file changes only in its import lines.
This adapter selects the existing decimal time bound. The verifier supplies its own trusted
challenge; the source's challenge and wrappers are not used.
Programs, notes and checks: https://github.com/jacobalansussman/wht-power-saving-lean (package/leverAFc)

The upstream NOTICE.complex588 and LICENSE of the base follow, unchanged. The full NOTICE
of the base (lean/complex588/NOTICE) is at the base commit above.


Upstream NOTICE.complex588:
Exact DFT: complex588 instantiation, October 12, 2026

This package retains the Apache-2.0 LICENSE and Jacob Sussman's original NOTICE.
Additional upstream package notices are preserved in third-party/complex588/.
They retain their authors' AI disclosures, including disclosures for work
prepared with Claude. They are provenance notices, not coauthor trailers on
this project's commits.

The source circuit is the atm3 provider reconstructed from Jeremy Kothe's
CrocSwap/integer-mult-bounds PR588, commit
6d0e53b66c29abd17981881a09eaff41ac862d85. Its direct lineage includes
eumemic's complex witnesses; DominikScholz's entrance promotions and structural
gain; jeremykothe2's multi-cut kernels; jon314159's joint-prefix work; and
Chafik Boukhalfa/chafreaky's frame coalescences and portable identity checks.
The inherited notices also credit rohanarun, Dugongue, icekylinx,
DreamingOfClouds, higherbeing, lydakis, and the earlier community contributors.
Douglas Colkitt/CrocSwap maintains the community repository. OpenAI supplies
the original #109/#130 framework. The native conditional integer-multiplication
headline is not claimed as a Fourier theorem.

The general Lean program engine, frame/circuit checker, cost accounting and
Fourier formalization are Jacob Sussman's, with the community extensions
identified in the preserved source headers. The dedicated entrance-gauged
nine-stage layout is Dugongue's #401 on Zhihao Chen/jacklightChen's #377,
building on DaysSky's bridged layout and lydakis's bank patterns. The #401
Lean files name DFT Bridge3 and DFT New Sums; the record instance names DFT Lean.
These files are taken from Nil Mamano's published Big O Speedrun submission,
bigospeedrun/verifier commit 025396033eede56e3af6e02ed2679ba828381bd5.
Their mathematical definitions and proofs are unchanged; only the Submission.
import prefix is removed. OpenAI's exact model and all-length reduction remain
the source of the final Fourier theorem.

New integration in Ryan Shea's project, with OpenAI Codex assistance:
source-copy lowering of the mutable-source provider; rational handling of
target preconditioning and register scales; exact cyclic bank packing;
generated C588 local checks and the C588 Fourier instance; reproducibility,
negative controls, source audit, comparisons and reporting. No authorship of
the imported local circuit, geometry, checker soundness proofs or Fourier
reduction is claimed. This is a new checked instantiation, not verification
of the native idle-data hosting or hyperplane-ended #596 construction.

The general generator headers in generated files are retained as lineage
information. The current reproducible entry points are the scripts under
research/complex-transfer-588-596 and scripts/regenerate.py; SOURCE_MANIFEST.json
classifies all 63 new modules and the unchanged upstream dependency closure.

Same-agent second-pass checks are not independent human mathematical review.


Upstream LICENSE:
                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/
import Submission.Work.U7604.Chain.FourierTB.Main

open OAI.PowerSaving Filter Asymptotics

theorem Race.bound : ∃ order solve W, DFTProgram order solve W ∧
    (fun n : ℕ => (W n : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) * (Real.log (n : ℝ)) ^
        (1 - (389848144653 : ℝ) / 100000000000000)) := by
  obtain ⟨order, solve, W, hprogram, htime⟩ := transform_mainTB19
  refine ⟨order, solve, W, hprogram, ?_⟩
  have hdecimal : decimalTimeTB19 =
      (fun n : ℕ => (n : ℝ) * (Real.log (n : ℝ)) ^
        (1 - (389848144653 : ℝ) / 100000000000000)) := by
    funext n
    have hexponent : decimalExponentTB19 = 1 - (389848144653 : ℝ) / 100000000000000 := by
      norm_num [decimalExponentTB19, statedSavingTB19]
    simp only [decimalTimeTB19, hexponent]
  exact hdecimal ▸ htime.2.1
