import Submission.Work.L2979Fc.Stmt
import Submission.Work.Mixed.Bridge.HFTest2979FcW

/-!
# afc-cut: the adapter from the #2979 warp network, FULL cut on A-fc (#2979Fc), to the seam's engine statement
`MX.L2979Fc.EngineStmt`

`MX.L2979Fc.engine_of_geomW`: the geometric warp network of p-a3 (`xnetGeomW`, through x-inst's warp heads-first
certificate and fc-engine's full-cut bridge with the A-fc instance) gives OpenAI's `hills_program` statement at the
seam exponent `1 - 1788704501/10^12` (DFT figure 1.7887045e-3), i.e. `MX.L2979Fc.EngineStmt.{0}` of the generated
`Work/L2979Fc/Stmt.lean` (afc-cut's tools/mk_l2979Fc.py).  The start frames `base` are chosen as in p-a3's
`bridgeHostTW_gcert` (`base_ex`), the label `l` as in p-a3's `engine_of_ginvW_hostT` (any element of `H`).
(aA-data's L2979H/EngineOfGeomW.lean and fc-engine's L3945F/EngineOfGeomW.lean with the A-fc full-cut engine
theorem.)  What is left are the data of the #2979 network with A-fc's fill: the providers (x-words), the schedule `S`
with `hfit`, positive residuals, the head count (16,576) and the unit price (afc-data).
afc-cut (wht45/afc, 20 Oct 2026); prepared with assistance from Claude.  No `sorry`.
-/

namespace OAI
namespace PowerSaving
namespace MX
namespace L2979Fc
open Binary Matrix Finset RAM RAM.Ty SS CB RF BR GF GX BC B401 XHost XHostR XHostD XHostT XHostTW

/-- **The engine statement of L2979Fc from the #2979 warp network and its data.** -/
theorem engine_of_geomW {H Sl C : Type} [Fintype H] [DecidableEq H] [Fintype Sl] [DecidableEq Sl]
    [Fintype C] [DecidableEq C] {Ok : ∀ {β : Type} [Fintype β] [DecidableEq β], GWin H β → Prop}
    (I : GInvW H (Fin 112) Sl C Ok) (Ic : Fin 74 → Fin 9 → GInvW H (Fin 112) Sl C Ok)
    (hIc : ∀ ρ l, (Ic ρ l).tv = I.tv) (hH : Fintype.card H = 9)
    (hOk : ∀ (l : H) (n : ℕ) (d : Orth (BC.LC (Fin 8) H l)), Ok (win401N l hH n d))
    (S : HostSchedT 74 Sl (Fin 112)) (hfit : S.fits (resIcW Ic))
    (hpos : ∀ ρ l' q, 0 < resIcW Ic ρ l' q)
    (hheads : (Finset.univ.filter (fun p : Fin 74 × Bool × Fin 112 => S.hrem p.1 4 p.2 = 48)).card = 16576)
    (hU : ∀ φ, unitPriceTW Ic S φ = listCost φ MX.unit2979Fc) :
    EngineStmt.{0} := by
  intro cl m ι k v
  obtain ⟨l⟩ : Nonempty H := Fintype.card_pos_iff.mp (by omega)
  have hb : ∀ t, ∃ A : OBase H, I.tv t = A.v l := fun t => base_ex (I.tv t) (I.hunit t) (I.hgap t) l
  choose base hbase using hb
  exact PB.HFTest2979FcW.engine2979Fc_geomW_unit I Ic hIc base l hbase hH (hOk l) S hfit hpos hheads hU m cl k v

end L2979Fc
end MX
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.MX.L2979Fc.engine_of_geomW
