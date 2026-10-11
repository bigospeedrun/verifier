/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Programs.Sec2.Theorem5.AllInstances.Program
public import Submission.ThreeSumApsp.Programs.Sec4.Theorem30.Layout
public import Submission.ThreeSumApsp.Programs.Sec4.Theorem30.OfflineLayout
public import Submission.ThreeSumApsp.Programs.Sec4.Theorem30.Routines
public import Submission.ThreeSumApsp.Programs.Sec2.PrunedEnc.SharedStage
public import Submission.ThreeSumApsp.Programs.Sec2.PrunedEnc.Entry

/-!
# Theorem 30 on the word RAM: the program

`program30` is the list of procedures: those of Section 2 (numbers 0 to 28, of which the
preprocessing uses the shared stage), the routines of Section 4 (40 to 53), preCore, queryAt and the
two procedures of the offline form (54 to 57), and the two main procedures of Theorem 30 (80 and
81); the unused numbers hold the empty statement.

The first 58 procedures (`base58`) are also the beginning of the programs for Corollaries 26, 31
and 32.  So the assumptions of the earlier files are discharged for every program `base58 ++ R` that
begins with them: it meets the specifications of the preprocessing and of a query at a given place
of the memory (`preCore_base58`, `queryAt_base58`).  With `theorem_30_of` and `theorem_30_wanted_of`
this gives Theorem 30 and its offline form without hypotheses (`wordRam_theorem_30`,
`wordRam_theorem_30_wanted`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.WordRam

/-- The procedures of the shared stage with pruned encodings, numbers 29 to 31. -/
def prunedProcs : Program :=
  [Sec2.encodePBody Sec2.pEncStep Sec2.pEncodeP, Sec2.encodeBandsPBody, Sec2.sharedPBody]

/-- The procedures number 0 to 57: Section 2's program for the thin matrix product (0 to 28), the
shared stage with pruned encodings (29 to 31), eight unused numbers, the routines of Section 4, the two routines that know the memory map, and the two
routines of the offline form. -/
def base58 : Program :=
  Sec2.programThin ++ prunedProcs ++ List.replicate 8 .skip ++ procs40 ++
    [preCoreBody, queryAtBody, wantedCoreBody, wantedMainBody]

theorem length_base58 : base58.length = 58 := rfl

/-- A procedure of base58 is a procedure, with the same number, of every program that begins with
base58. -/
theorem at_base58 {p : ℕ} {body : Stmt} (h : base58[p]? = some body) (R : Program) :
    (base58 ++ R)[p]? = some body :=
  getElem?_append_of_eq_some h R

/-- The constant of the shared stage. -/
def cShared30 : ℕ := 12 * Sec2.cShared5 + 600

theorem has40_base58 (R : Program) : Has40 (base58 ++ R) := by
  have h := has40_of_append (A := Sec2.programThin ++ prunedProcs ++ List.replicate 8 .skip)
    (B := [preCoreBody, queryAtBody, wantedCoreBody, wantedMainBody] ++ R) rfl
  rwa [← List.append_assoc] at h

/-- The shared stage with pruned encodings, in every program that begins with base58. -/
theorem shared_base58 (R : Program) (lim : Limits) (std : Std lim) :
    Sec2.SharedSpecP lim (base58 ++ R) cShared30 := by
  have e : base58 ++ R = Sec2.program5 ++
      ([Sec2.regimeBody, Sec2.thinBruteBody, Sec2.thinBody] ++ prunedProcs ++ List.replicate 8 .skip
      ++ procs40 ++ [preCoreBody, queryAtBody, wantedCoreBody, wantedMainBody] ++ R) := by
    simp only [base58, Sec2.programThin, List.append_assoc]
  have hP : ∀ {i : ℕ} {body : Stmt}, base58[i]? = some body → (base58 ++ R)[i]? = some body :=
    fun h => at_base58 h R
  have C : Sec2.SharedCalleesP lim (base58 ++ R) Sec2.cShared5 := by
    have C₀ := Sec2.sharedCallees_of_prefix ([Sec2.regimeBody, Sec2.thinBruteBody, Sec2.thinBody]
      ++ prunedProcs ++ List.replicate 8 .skip ++ procs40
      ++ [preCoreBody, queryAtBody, wantedCoreBody, wantedMainBody] ++ R) lim std
    rw [← e] at C₀
    exact
      { pow := C₀.pow, binom := C₀.binom, sqrt := C₀.sqrt, coef := C₀.coef, subsets := C₀.subsets
        counters := C₀.counters, digits := C₀.digits
        bandsL := Sec2.encodeBandsPL_entry std (hP rfl) (Sec2.bandArrayL_entry std (hP rfl))
          (Sec2.encodePL_entry std (hP rfl) (hP rfl)) (by decide)
        bandsR := Sec2.encodeBandsPR_entry std (hP rfl) (Sec2.bandArrayR_entry std (hP rfl))
          (Sec2.encodePR_entry std (hP rfl) (hP rfl)) (by decide) }
  exact Sec2.sharedP_entry std (hP rfl) C le_rfl

/-- **The preprocessing at a given place of the memory**, in every program that begins with base58.
-/
theorem preCore_base58 (R : Program) : ∀ lim, PreCoreSpec lim (base58 ++ R) cShared30 :=
  preCoreSpec_all (has40_base58 R) (at_base58 rfl R) (shared_base58 R)

/-- **A query at a given place of the memory**, in every program that begins with base58. -/
theorem queryAt_base58 (R : Program) : ∀ lim, QueryAtSpec lim (base58 ++ R) :=
  queryAtSpec_all (has40_base58 R) (at_base58 rfl R)

/-- The program of Theorem 30. -/
def program30 : Program := base58 ++ (List.replicate 22 .skip ++ [queryMainBody, preMainBody])

end Light.Sec4
