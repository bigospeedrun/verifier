/- Modified 2026-10-30: numerical rate refinement of Kartal PR #41.
New certified rate 0.00302016595, tensor power 11640, final saving 0.0030201659.
Original circuit, proof framework and authorship are retained. See README.md.
In Submission.lean, the original headers below are historical provenance:
their constants describe earlier results, not this refinement.
-/
import Submission.Work.TensorEng.P16A8ZEngine
import Submission.Work.T16A8Z.Hole
-- changed for the tensor-power extension (30201659/10000000000); see Submission.lean

/-!
# Route E: the tensor engine for `G` copies of the RAW p16a8z unit

`PB.T16A8Z.tensorEngine16Z`: a RAW p16a8z certificate with `G` copies (`RawCert16Z`) gives the engine statement of T16A8Z at the
seam exponent `1 - 3020165925/10^12`, by the tensor agent's `TensorEng.p16a8z_engine_of_rawG` (the 11640-fold tensor
power completed to `21^11640` and split at `20^11640`, rate point `1 - 60403319/20000000000`, `TensorProto.P16A8Z.strict`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace OAI.PowerSaving.PB.T16A8Z

lemma rawTgt16Z_eq : rawTgt16Z = TensorProto.P16A8Z.TP16A8Z := rfl
lemma rawPaid16Z_eq : rawPaid16Z = TensorProto.P16A8Z.PP16A8Z := rfl

/-- **The tensor engine**: a RAW p16a8z certificate with `G` copies gives the engine statement of T16A8Z. -/
theorem tensorEngine16Z (α ρ σ : Type) [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] [Fintype σ]
    [DecidableEq σ] (hc : RawCert16Z α ρ σ) : MX.T16A8Z.EngineStmt.{0} := by
  intro cl m ι k v
  obtain ⟨e, tr, tz, wd, G, he, tind, hP, hw, hG, hα, htr, hcnt, hhist⟩ := hc
  exact TensorEng.p16a8z_engine_of_rawG e tr tz wd G he tind hP hw hG hα htr hcnt hhist (by norm_num) (by norm_num)
    m cl k v

end OAI.PowerSaving.PB.T16A8Z

#print axioms OAI.PowerSaving.PB.T16A8Z.tensorEngine16Z
