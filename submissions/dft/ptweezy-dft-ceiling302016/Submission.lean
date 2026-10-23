/-
Big O Speedrun submission: exact DFT of every length, and convolution, with saving
302015999999/100000000000000 (about 3.02016e-3: within 1e-14 of the rate certificate ceiling),
in OpenAI's exact computational model.
Entry point: Work/FourierT16A8Z/Main.lean.

What is new over my previous entry, submissions/dft/ptweezy-dft-tight302016
(bigospeedrun/verifier PR #44, saving 3020159999/1000000000000): high-precision tightening of the
18-stage bridged geometry (G18) and 16-pair query-thinned controller unit to the absolute rate
ceiling of the certified construction:
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
  1 - 4719/1562500, and the stated saving is pushed to within 1e-14 of this ceiling at
  302015999999/100000000000000;
* new Lean: the certified supplier above, the 18-stage geometry (Work/G18), the controller, roles,
  stages, thin queries, windows, word and certificate of the unit (Work/P16A8) on the operator
  semantics, frames and segments of Work/P4L and Work/P3/Ctrl4, fresh productive helpers as live
  roles (Work/Fresh/Helpers), a rule for any list of job sizes (Work/Mixed/MultiTarget,
  Work/Mixed/Bridge/CoreK), the tensor product of certified words with its powers, strict form and
  engine (Work/TensorEng), the rate certificate (Work/TensorProto) and the chain Work/T16A8Z,
  Work/FourierT16A8Z, adapted from Sussman's chain. Every other file is his, unchanged; files of
  his that this proof does not import are left out.

Credits: Jacob Sussman's header below credits his construction and everything it builds on;
the integer-multiplication lineage is credited to Marius-Paul Dumitrean, Jeremy Kothe, Mason Hale,
Cinna Davis, Nil Mamano, Ryan Shea, and Halit Ziya Kartal.
  Author and formalization: Parker L (@ptweezy).
  LLM pair-programming: Google DeepMind Antigravity.
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
import Submission.Work.FourierT16A8Z.Main

open OAI.PowerSaving Filter Asymptotics

theorem Race.bound : ∃ order solve W, DFTProgram order solve W ∧
    (fun n : ℕ => (W n : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) * (Real.log (n : ℝ)) ^
        (1 - (302015999999 : ℝ) / 100000000000000)) := by
  obtain ⟨order, solve, W, hprogram, htime⟩ := transform_mainT16A8Z
  refine ⟨order, solve, W, hprogram, ?_⟩
  have hdecimal : decimalTimeT16A8Z =
      (fun n : ℕ => (n : ℝ) * (Real.log (n : ℝ)) ^
        (1 - (302015999999 : ℝ) / 100000000000000)) := by
    funext n
    have hexponent : decimalExponentT16A8Z = 1 - (302015999999 : ℝ) / 100000000000000 := by
      norm_num [decimalExponentT16A8Z]
    simp only [decimalTimeT16A8Z, hexponent]
  exact hdecimal ▸ htime.2.1
