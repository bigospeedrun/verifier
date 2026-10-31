import Submission.Work.GCert.Data.Gen.S2979ZWC
import Submission.Work.GCert.Data.S2979ZPrice
import Submission.Work.GCert.Data.Gen.S2979ZSchedR
import Submission.Work.KLowW.Win
import Submission.Work.Warp.KLW
import Submission.Work.PWGen.Roles
import Submission.Work.PWGen.Res
import Submission.Work.Bridge401.GGeom
-- changed for the tensor-power extension (30103/10000000); see Submission.lean
/-!
# the invocation package of the #4470 patched #2979 word `GXD.S2979Z` (Route E)
The leader's glue (`GCert/Data/S2979BGlue401`, p-wgen's template x-words/tools/glue2.lean.tmpl) on the word
`S2979Z`, without the bank schedule (the unit uses only the package, its price and the residuals): p-warpchk's warp
invocation theorem on the word's certificate (`KLW.WValid.invW` on `GXD.S2979Z.wvalid`, roles `PWG.roles`), with the
warps interpreted by p-warpsem's `K_G` at every window whose frame map has a `WLift` (`okW`), reduced to the gauged
package `ginvW := ginvXW.toEW'`; `hent`: the residuals (`Gen.S2979ZRes`, `Gen.S2979ZSchedR`).  No `sorry`.
The word has no zero buffers (full-identity cleanup) and 8 centre copies, so the copies are `Fin 8`.
-/

set_option maxRecDepth 100000
namespace GXD.S2979Z
open GXD OAI.PowerSaving OAI.PowerSaving.CB OAI.PowerSaving.GF OAI.PowerSaving.GX
noncomputable section

/-- the windows with a warp meaning: frame maps with a lift of the warp permutations (p-warpsem) -/
def okW : ∀ {α : Type} [Fintype α] [DecidableEq α], GWin (Fin 9) α → Prop :=
  fun W => Nonempty (OAI.PowerSaving.WS.WLift W.X)

/-- the warp meaning at such a window (the same family serves both orientations, p-warpsem) -/
def wsem {α : Type} [Fintype α] [DecidableEq α] (W : GWin (Fin 9) α) (h : okW W) : KLW.WarpSem 9 wt W.X :=
  OAI.PowerSaving.WS.warpSem (Classical.choice h) wt

theorem roles_ok : KLW.WRoles wc (PWG.embB 112 408 8) (PWG.unB 112 408 8 (by decide)) :=
  PWG.roles wc wvalid (by decide) (by decide)

/-- **the exit-frame invocation package** of the warped word (at the windows `okW`) -/
def ginvXW : KLW.GInvXW (Fin 9) (Fin 112) (Fin 408) (Fin 8) okW :=
  KLW.WValid.invW wvalid roles_ok okW (fun W h => wsem W h) (fun W h => wsem W h)

/-- **the gauged invocation package** (p-warpchk's windowed reduction `GInvXW.toEW'`) -/
def ginvW : KLW.GInvEW (Fin 9) (Fin 112) (Fin 408) (Fin 8) okW := ginvXW.toEW'

theorem h9 : Fintype.card (Fin 9) = 9 := Fintype.card_fin 9

/-- every window of the #401 network (`gwinC`: a conjugation frame map) has a warp meaning -/
theorem okC : ∀ (l : Fin 9) (hH2 : 2 ≤ Fintype.card (Fin 9)) (d : RF.Orth (BC.LC (Fin 8) (Fin 9) l))
    (q : Finset (Fin 8 × BC.Hp (Fin 9) l)), okW (GX.gwinC GX.hB401 hH2 d q) :=
  fun _ _ d q => ⟨OAI.PowerSaving.WS.WLift.ofConj d.1 d.2 (RF.Orth.orth' d) q⟩

/-- its price is the invocation price `invPrice` (kernel counts) -/
theorem ginv_cost (φ : ℕ → ℝ) : ginvW.cost φ = invPrice φ := by
  show rcost φ rAll = invPrice φ
  exact inv_cost φ

theorem hent : ∀ q : Fin 408, Fintype.card (Fin 9) - (ginvW.ent q).dim = schedRes.getD q.val 0 := fun q => by
  show Fintype.card (Fin 9) - (ginvXW.entS q).dim = _
  rw [ginvXW.entS_hd q, schedRes_eq]
  exact (PWG.res wvalid.toS roles_ok q).trans (res_ok q)

end
end GXD.S2979Z
#print axioms GXD.S2979Z.ginvW
#print axioms GXD.S2979Z.ginv_cost
#print axioms GXD.S2979Z.hent
