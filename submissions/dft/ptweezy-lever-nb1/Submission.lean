/-
Big O Speedrun submission: exact DFT of every length, and convolution, with saving
17887049/10000000000 (= 17887049/10^10, about 1.7887049e-3), in OpenAI's exact
computational model. Submitted by Parker L (GitHub: ptweezy).

What is new in this proof
This is Jacob Sussman's record construction (submissions/dft/jacobalansussman-lever-2979-full-cut:
the community's #2979 circuit, his mixed-target recursion and his lever with the full cut) with
one change: a different table of where helper storage goes (fill NB1s7, FILL.json.gz sha256
1285b9a0ba1119f9b6a21570ad6e185933741b3e1f52b6919989a5e7f0d88644). The words, the order of the
runs and the dispatch stay #2979's. The table was solved as a mixed-integer program (HiGHS) over
the column-generation patterns of the #3815 allocation model with the full cut's objective, as
in Sussman's own fill tools (package/leverAFc/fill/made-by), then placed with #3815's
reverse-time placement made tolerant, as Sussman did; #2979's PR2839 owner engine accepts it
with all seven of its rejection controls. As in Sussman's table, all 16,576 idle rank-48 blocks
per round are literal heads (children 8 and 10) and no other idle block has rank 48, so the
same full cut applies (targets 25, every paid rank at most 23). The paid profile of the cut
prices at 1.78870492727e-3 (Sussman's table: 1.78870456430e-3); the rate certificate proves the
grid numerator 17887049 and refutes 17887050. No new lemma: every Lean file is Sussman's
generator output or his hand-written instance file, regenerated or renamed (L2979Fc to
L2979Nb1) with the new table's numbers. The work was done by AI agents (including Claude)
working with me; it is machine-checked, and a line-by-line human review has not been done.

Credits
- Jacob Sussman: the whole Lean construction this proof re-runs: the engine and its exit-frame,
  mutable-source and hosting extensions, the mixed-target recursion, the lever with its full
  cut, the head lemma, the port of the #2979 circuit, the generators and the fill tools.
- Marius-Paul Dumitrean (with Anthropic Claude): the #2979 circuit (joint rank-7 end frames),
  on his #2942 and #2930, Jeremy Kothe's rewrites (#2957, #2948, #2966) and his preload
  supplier and frame accounting (#2894, #2833), Mason Hale's paired extractions and T74
  chronology (#2917), Jeremy Diviney's paired extraction and certificate (#2908), Dugongue's
  composition and packing lineage (#2969, #2863, #2839: the owner engine that checks the
  table), Yiyang Lu's flow model (#2857, #2848), Ross Richardson's rank-seven obstruction
  (#2918), Tekalign's owner checker, icekylinx's auditor, themilkman216's integrality
  observation and Gareth Davidson's terminal-subspace bounds (#1995, #2013).
- Erwan Secousses / ChaloupeMusic (#3815): the allocation model and the placement program
  with which the table was made.
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
- Parker L (me): the new table (fill NB1s7) and this re-run of Sussman's pipeline on it.

Source and packaging
Base: https://github.com/shea256/fourier-transform-below-nlogn, commit
52394849c7ecf3412d39b925d75fc7fdb98994d8, directory lean/complex588. No file of the base
is modified. Programs: https://github.com/jacobalansussman/wht-power-saving-lean at
86e575e28ed94890872dcff1bb2621d7ff559cbd, package/u8x0hq and package/leverAFc, with the
leverAFc files of the L2979Fc instance replaced by their L2979Nb1 counterparts.
Entry point: Work/FourierL2979Nb1/Main.lean, transform_mainL2979Nb1.
The 577-module proof closure is copied under Submission/, changing local import paths
only (the packaging of submissions/dft/nmamano-shea-c588). Then, for the verifier's limit
of 500 files, the same 153 modules as in Sussman's record submission are merged into the
same 23 modules, leaving 447; the merging was re-done from that submission as a template
(applied to Sussman's own sources, it reproduces all 447 of his files byte for byte). Each
merged module starts with a comment that lists its members with the sha256 of each original
file, and copies each member verbatim after its import lines, inside its own section; every
other file changes only in its import lines.
This adapter selects the existing decimal time bound. The verifier supplies its own trusted
challenge; the source's challenge and wrappers are not used.

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
import Submission.Work.FourierL2979Nb1.Main

open OAI.PowerSaving Filter Asymptotics

theorem Race.bound : ∃ order solve W, DFTProgram order solve W ∧
    (fun n : ℕ => (W n : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) * (Real.log (n : ℝ)) ^
        (1 - (17887049 : ℝ) / 10000000000)) := by
  obtain ⟨order, solve, W, hprogram, htime⟩ := transform_mainL2979Nb1
  refine ⟨order, solve, W, hprogram, ?_⟩
  have hdecimal : decimalTimeL2979Nb1 =
      (fun n : ℕ => (n : ℝ) * (Real.log (n : ℝ)) ^
        (1 - (17887049 : ℝ) / 10000000000)) := by
    funext n
    have hexponent : decimalExponentL2979Nb1 = 1 - (17887049 : ℝ) / 10000000000 := by
      norm_num [decimalExponentL2979Nb1]
    simp only [decimalTimeL2979Nb1, hexponent]
  exact hdecimal ▸ htime.2.1
