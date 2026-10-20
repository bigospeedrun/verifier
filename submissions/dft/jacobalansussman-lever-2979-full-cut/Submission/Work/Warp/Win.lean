import Submission.Work.Warp.Sem
import Submission.Work.GCert.Chain.WinB

/-!
# (key: p-warpsem) The windows of the bridged geometry transport warps

`WLift.gwinB`: the stage-B frame map `(gwinB hB hH d q).X = BXMap.ofConj d q` of every window of the bridged
geometry carries a warp `W` of the label space `H` to the warp `conjW d W` (`y ↦ d ((W ⊕ id) (dᵀ y))`) of the
address space `LB B H = H ⊕ (B × H)`, so `WLift.transport` / `WLift.reach` / `WLift.data` apply to the windows.
No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace WS
open Binary Matrix Finset RAM SS CB RF BR BG GF GX
noncomputable section

section
variable {B H : Type} [Fintype B] [DecidableEq B] [Fintype H] [DecidableEq H]

/-- **every window of the bridged geometry transports warps.** -/
def WLift.gwinB (hB : 1 ≤ Fintype.card B) (hH : 1 ≤ Fintype.card H) (d : Orth (LB B H))
    (q : Finset (B × H)) : WLift (gwinB hB hH d q).X :=
  WLift.ofConj d.1 d.2 (Orth.orth' d) q

@[simp] lemma WLift.gwinB_liftW (hB : 1 ≤ Fintype.card B) (hH : 1 ≤ Fintype.card H) (d : Orth (LB B H))
    (q : Finset (B × H)) (W : APerm H) :
    (WLift.gwinB hB hH d q).liftW W = conjW d.1 d.2 (Orth.orth' d) W := rfl

/-- frame transport in a window: the free `P` with `P * X.Φ U = X.Φ V * warpMat (conjW d W)`. -/
theorem gwinB_transport (hB : 1 ≤ Fintype.card B) (hH : 1 ≤ Fintype.card H) (d : Orth (LB B H))
    (q : Finset (B × H)) (W : APerm H) (U V : SLbl H) (h : ∀ x, V.Mem x ↔ U.Mem ((apInv W).π x)) :
    ∃ P : CMat (LB B H), Free P ∧
      P * (gwinB hB hH d q).X.Φ U = (gwinB hB hH d q).X.Φ V * warpMat (conjW d.1 d.2 (Orth.orth' d) W) :=
  (WLift.gwinB hB hH d q).transport W U V h

end
end
end WS
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.WS.WLift.gwinB
#print axioms OAI.PowerSaving.WS.gwinB_transport
