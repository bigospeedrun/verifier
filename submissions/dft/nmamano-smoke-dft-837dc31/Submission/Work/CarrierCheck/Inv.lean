import Submission.Work.CarrierCheck.Inst
import Submission.Work.Carrier.PhasedInv

/-!
# (key: carrier-check) The invocation package of a checked carrier certificate

    CCert.Valid.inv      : (V : c.Valid) → c.scalarCheck = true →
                             BR.Inv (Fin c.p.h) (Fin c.v) (Fin c.R) (Fin c.ret.length)   := (V.phased hs).inv
    CCert.Valid.inv_tv   : (V.inv hs).tv = c.tv
    CCert.Valid.inv_cost : (V.inv hs).cost φ = rcost φ c.invRanks

`CR.Phased.inv` is the carrier invocation theorem (`Work/Carrier/PhasedInv.lean`).  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace SSC
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM OAI.PowerSaving.SS
  OAI.PowerSaving.CB OAI.PowerSaving.CR OAI.PowerSaving.BR Finset Matrix

namespace CCert
variable {c : CCert}

/-- **The invocation package of a checked carrier certificate** (for the bridged network). -/
noncomputable def Valid.inv (V : c.Valid) (hs : c.scalarCheck = true) :
    BR.Inv (Fin c.p.h) (Fin c.v) (Fin c.R) (Fin c.ret.length) := (V.phased hs).inv

theorem Valid.inv_tv (V : c.Valid) (hs : c.scalarCheck = true) : (V.inv hs).tv = c.tv := rfl

/-- **the price of one invocation**: the blocks of all roles (x, y, slots) and of the copies -/
theorem Valid.inv_cost (V : c.Valid) (hs : c.scalarCheck = true) (φ : ℕ → ℝ) :
    (V.inv hs).cost φ = rcost φ c.invRanks := V.phased_cost hs φ

end CCert

end SSC

#print axioms SSC.CCert.Valid.inv
#print axioms SSC.CCert.Valid.inv_cost
