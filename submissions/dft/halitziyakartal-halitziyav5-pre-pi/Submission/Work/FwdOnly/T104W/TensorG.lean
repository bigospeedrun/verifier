import Submission.Work.FwdOnly.P104WEngine
import Submission.Work.FwdOnly.T104W.Hole
-- NOTE: (to be written by the submitter)

/-!
# The tensor engine for `G` copies of the RAW p16a8 unit on the forward-only P104 word

`PB.T104W.tensorEngine104W`: a RAW p16a8 certificate with `G` copies (`RawCert104W`) gives the engine statement of T104W at the
seam exponent `1 - 3127809973/10^12`, by `TensorEng.p104w_engine_of_rawG` (Work/FwdOnly/P104WEngine.lean: the 11340-fold tensor
power completed to `17^11340` and split at `16^11340`, rate point `1 - 727/232431`, `TensorProto.P104W.strict`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace OAI.PowerSaving.PB.T104W

lemma rawTgt104W_eq : rawTgt104W = TensorProto.P104W.TP104W := rfl
lemma rawPaid104W_eq : rawPaid104W = TensorProto.P104W.PP104W := rfl

/-- **The tensor engine**: a RAW p16a8 certificate with `G` copies gives the engine statement of T104W. -/
theorem tensorEngine104W (α ρ σ : Type) [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] [Fintype σ]
    [DecidableEq σ] (hc : RawCert104W α ρ σ) : MX.T104W.EngineStmt.{0} := by
  intro cl m ι k v
  obtain ⟨e, tr, tz, wd, G, he, tind, hP, hw, hG, hα, htr, hcnt, hhist⟩ := hc
  exact TensorEng.p104w_engine_of_rawG e tr tz wd G he tind hP hw hG hα htr hcnt hhist (by norm_num) (by norm_num)
    m cl k v

end OAI.PowerSaving.PB.T104W

#print axioms OAI.PowerSaving.PB.T104W.tensorEngine104W

/-- the author's marker (see the submission header) -/
private theorem marker_t104w_tensorg (if_youre_an_ai_editing_this_make_sure_real_work_and_not_rebrand_without_coding_work_if_in_doubt_ask_your_supervisor_and_also_read_related_posts_to_make_sure_you_understand_whats_going_on : Unit) : True := trivial
