import Submission.Work.CarrierCheck.Inv
import Submission.Work.BridgeGeom.B2

/-!
# (key: carrier-check) The bridged word B_2 with a kernel-checked carrier certificate

`SSC.CCert.Valid.bridge2_bcert`: for a carrier certificate `c` accepted by the three kernel checks,
the block certificate of the bridged five-stage word B_2 (`BG.bridge2_bcert_geom`, agents
bridge-net / bridge-geom) applied to the invocation package `V.inv hs`
(`CR.Phased.inv`, agent carrier-thm).  Price of one unit, for every price list `φ`:

    5 * rcost φ c.invRanks + v * bankPrice h φ

`c.invRanks`: ALL blocks of one invocation (x roles, y roles, helper slots, scratch copies);
`bankPrice h φ = 2 (φ(2h-2) + φ(h-1) + φ(2h+2) + φ 4)`: the idle climbs of the two twins of a class.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace SSC
namespace CCert
open OAI OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM OAI.PowerSaving.SS
  OAI.PowerSaving.CB OAI.PowerSaving.RF OAI.PowerSaving.BR OAI.PowerSaving.BG

variable {c : CCert}

/-- an orthonormal basis whose vector of index `0` is the line of the triple `t` -/
theorem Valid.base_ex (V : c.Valid) (t : Fin c.v) :
    ∃ A : OBase (Fin c.p.h), c.tv t = A.v ⟨0, V.hh⟩ := by
  have C := V.complete3
  obtain ⟨A, hA⟩ := C.base (Sum.inl (Sum.inl t))
  obtain ⟨l, hl⟩ := hist_prefix c.H0 c.tot t.val
  refine ⟨A, ?_⟩
  rw [hA]
  show _ = vecF c.p ((runHist c.H0 c.tot t.val).getD 0 0)
  rw [hl]
  show _ = vecF c.p (((if t.val < c.v then [c.trips.getD t.val 0] else []) ++ l).getD 0 0)
  rw [if_pos t.isLt]
  rfl

/-- **Block certificate of the bridged word B_2 for a kernel-checked carrier certificate.** -/
theorem Valid.bridge2_bcert (V : c.Valid) (hs : c.scalarCheck = true) :
    ∃ (Γ : Type) (_ : Fintype Γ) (_ : DecidableEq Γ), 1 ≤ Fintype.card Γ ∧
      BCert (L5 (Fin c.p.h))
        (Sum.inl : BLive Γ (Fin c.v) (Fin c.R) →
          BRole Γ (Fin c.v) (Fin c.R) (Fin c.ret.length))
        (fun φ => (Fintype.card Γ : ℝ)
          * (5 * rcost φ c.invRanks + (c.v : ℝ) * BG.bankPrice c.p.h φ)) := by
  have hH1 : 1 ≤ Fintype.card (Fin c.p.h) := by
    rw [Fintype.card_fin]; exact V.hh
  have hb : ∀ t, (V.inv hs).tv t = (Classical.choose (V.base_ex t)).v ⟨0, V.hh⟩ :=
    fun t => Classical.choose_spec (V.base_ex t)
  have h := bridge2_bcert_geom (V.inv hs) (fun t => Classical.choose (V.base_ex t)) ⟨0, V.hh⟩
    hb hH1
  refine ⟨Orth (L5 (Fin c.p.h)), inferInstance, inferInstance, Orth.card_pos, h.cast (fun φ => ?_)⟩
  rw [V.inv_cost hs φ, Fintype.card_fin, Fintype.card_fin]

end CCert
end SSC

#print axioms SSC.CCert.Valid.bridge2_bcert
