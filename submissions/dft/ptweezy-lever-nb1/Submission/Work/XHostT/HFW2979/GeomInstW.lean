import Submission.Work.XHostT.TGeomW
import Submission.Work.XHostT.HFW2979.Heads
import Submission.Work.XHostT.HFW2979.GeomA4W
import Submission.Work.XHostT.HF.GeomInst

/-!
# (key: heads-first, warp) The heads-first certificate of p-a3's GEOMETRIC WARP network `xnetGeomW`

p-hfirst's Work/XHostT/HF/GeomInst.lean for the warp network (providers `GInvW .. Ok`, window facts `hOk`), the
network of the #2979 (and #3945) provider words, which are windowed packages (p-wgen / x-words):
* `xnetGeomW_unit`: its unit price is p-a3's `unitPriceTW Ic S`;
* `xnetGeomW_heads_first`: `GLiveKernel Sum.inl (headWord Sum.inl (headsL hb) (fun _ => 48) zGeom _ ++ body)`, `body`
  proper, `body` price `card Γ * unitPriceTW Ic S - |headsL hb| * φ 48` for every price list;
* `xnetGeomW_heads_first_auto`: the same for the canonical head set `headBins S` (no hypothesis left);
* `xnetGeomW_cut_half`: the whole chain to e-r45m1's half-cut mixed certificate (`MX.cut_heads_half`, a = b = 24).
The head data (`zGeom`, `cutA`, `cutS`, `bph_cut`, `headBins`, `headBins_eq`) are p-hfirst's, imported: they depend
only on the roles and the schedule, not on the providers.
Written by x-inst (wht45/lever2979, 19 Oct 2026) on p-hfirst's file; prepared with assistance from Claude.  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
namespace OAI
namespace PowerSaving
namespace XHostTW
open Binary Matrix Finset RAM SS CB RF BR GF GX BC B401 XHost XHostR XHostD XHostT
noncomputable section

section InstW
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C] {nR : ℕ}
variable {Ok : ∀ {β : Type} [Fintype β] [DecidableEq β], GWin H β → Prop}
variable (I : GInvW H T Sl C Ok) (Ic : Fin nR → Fin 9 → GInvW H T Sl C Ok) (hIc : ∀ ρ l, (Ic ρ l).tv = I.tv)
  (base : T → OBase H) (l : H) (hbase : ∀ t, I.tv t = (base t).v l) (hH : Fintype.card H = 9)
  (hOk : ∀ (n : ℕ) (d : Orth (BC.LC (Fin 8) H l)), Ok (win401N l hH n d))
  (S : HostSchedT nR Sl T) (hfit : S.fits (resIcW Ic))

/-- the unit price of the geometric warp network is p-a3's `unitPriceTW` (the step `e` of `bridgeHostTW_gcert`). -/
lemma xnetGeomW_unit (φ : ℕ → ℝ) :
    (xnetGeomW I Ic hIc base l hbase hH hOk S hfit).unit φ = unitPriceTW Ic S φ := by
  simp only [XNetW.unit, XNetW.callU, Finset.sum_add_distrib, sum_tailUW, Finset.univ_eq_empty, Finset.sum_empty,
    add_zero, unitPriceTW]
  simp only [XNetW.hcost, hcostT, xnetGeomW, bcost_zero, add_zero, mul_zero, Finset.sum_const_zero]

include I hIc hbase hOk hfit in
/-- **THE HEADS-FIRST CERTIFICATE OF THE GEOMETRIC WARP NETWORK.** -/
theorem xnetGeomW_heads_first (hb : Finset (Fin nR × Bool × T))
    (hunh : ∀ ρ l' q ρh j, (ρh, j) ∈ hb → S.host ρ l' q ≠ (ρh, 4, j))
    (h48 : ∀ ρ j, (ρ, j) ∈ hb → S.hrem ρ 4 j = 48) :
    ∃ body : GWord (BC.LC (Fin 8) H l) (BRoleT (Orth (BC.LC (Fin 8) H l)) T 0 C nR),
      body.Proper (Fintype.card (BC.LC (Fin 8) H l)) ∧
      (∀ φ, body.costR φ = (Fintype.card (Orth (BC.LC (Fin 8) H l)) : ℝ) * unitPriceTW Ic S φ
          - ((headsL (Γ := Orth (BC.LC (Fin 8) H l)) (nb := 0) hb).length : ℝ) * φ 48) ∧
      GLiveKernel (Sum.inl : BLiveT (Orth (BC.LC (Fin 8) H l)) T 0 nR → BRoleT (Orth (BC.LC (Fin 8) H l)) T 0 C nR)
        (MX.headWord Sum.inl (headsL hb) (fun _ => 48) (zGeom base l hH) (zGeom_indep base l hH) ++ body) := by
  have hz : ∀ ρ j, (ρ, j) ∈ hb → ∀ g, GReach (blockMat (zGeom base l hH (hroleT ρ g j))
      * (xnetGeomW I Ic hIc base l hbase hH hOk S hfit).x0A4 g j)
      ((xnetGeomW I Ic hIc base l hbase hH hOk S hfit).x1A4 g j) (fun _ => 0) := by
    intro ρ j _ g
    rw [zGeom_head]
    obtain ⟨s, t⟩ := j
    cases s
    · exact a4t_head_geom I.tv base l hbase hH g (false, t)
    · exact a4t_head_geom I.tv base l hbase hH g (true, t)
  obtain ⟨body, hP, hc, hk⟩ := (xnetGeomW I Ic hIc base l hbase hH hOk S hfit).heads_first hb
    (fun ρ l' q ρh j hj h => hunh ρ l' q ρh j hj (Option.some_injective _ h)) h48
    (zGeom base l hH) (zGeom_indep base l hH) hz
  refine ⟨body, hP, fun φ => ?_, hk⟩
  rw [hc φ, xnetGeomW_unit]

include I hIc hbase hOk hfit in
/-- the same for the canonical head set `headBins S` (no hypothesis left). -/
theorem xnetGeomW_heads_first_auto :
    ∃ body : GWord (BC.LC (Fin 8) H l) (BRoleT (Orth (BC.LC (Fin 8) H l)) T 0 C nR),
      body.Proper (Fintype.card (BC.LC (Fin 8) H l)) ∧
      (∀ φ, body.costR φ = (Fintype.card (Orth (BC.LC (Fin 8) H l)) : ℝ) * unitPriceTW Ic S φ
          - ((headsL (Γ := Orth (BC.LC (Fin 8) H l)) (nb := 0) (headBins S)).length : ℝ) * φ 48) ∧
      GLiveKernel (Sum.inl : BLiveT (Orth (BC.LC (Fin 8) H l)) T 0 nR → BRoleT (Orth (BC.LC (Fin 8) H l)) T 0 C nR)
        (MX.headWord Sum.inl (headsL (headBins S)) (fun _ => 48) (zGeom base l hH) (zGeom_indep base l hH) ++ body) :=
  xnetGeomW_heads_first I Ic hIc base l hbase hH hOk S hfit (headBins S) (headBins_unh S) (headBins_48 S)

include I hIc hbase hOk hfit in
/-- **the interface test (warp)**: the heads-first certificate of the geometric warp network fed into e-r45m1's half
cut gives the mixed certificate with targets `blockMat (cutTgt ..)` (rank 49 on the heads, 73 elsewhere). -/
theorem xnetGeomW_cut_half (hb : Finset (Fin nR × Bool × T))
    (hunh : ∀ ρ l' q ρh j, (ρh, j) ∈ hb → S.host ρ l' q ≠ (ρh, 4, j))
    (h48 : ∀ ρ j, (ρ, j) ∈ hb → S.hrem ρ 4 j = 48) :
    ∃ body : GWord (BC.LC (Fin 8) H l) (BRoleT (Orth (BC.LC (Fin 8) H l)) T 0 C nR),
      body.Proper (Fintype.card (BC.LC (Fin 8) H l)) ∧
      (∀ φ, body.costR φ = (Fintype.card (Orth (BC.LC (Fin 8) H l)) : ℝ) * unitPriceTW Ic S φ
          - ((headsL (Γ := Orth (BC.LC (Fin 8) H l)) (nb := 0) hb).length : ℝ) * φ 48) ∧
      MX.GLiveKernelM (Sum.inl : BLiveT (Orth (BC.LC (Fin 8) H l)) T 0 nR → BRoleT (Orth (BC.LC (Fin 8) H l)) T 0 C nR)
        (fun r => blockMat (MX.cutTgt (headsL hb) (cutA base l) (cutS l hH) r).2)
        ((MX.headWord Sum.inl (headsL hb) (fun _ => 24) (MX.partB (a := 24) (zGeom base l hH))
            (MX.partB_indep (zGeom_indep base l hH)) ++ body)
          ++ MX.shiftWord Sum.inl (headsL hb) (MX.cutShift (cutA base l) (cutS l hH))) := by
  obtain ⟨body, hP, hc, hk⟩ := xnetGeomW_heads_first I Ic hIc base l hbase hH hOk S hfit hb hunh h48
  exact ⟨body, hP, hc, MX.cut_heads_half Sum.inl_injective (headsL hb) (headsL_nodup hb) (a := 24) (b := 24)
    (zGeom base l hH) (zGeom_indep base l hH) (cutA base l) (cutS l hH)
    (fun r hr x => bph_cut base l hH hb r hr x) body hk⟩

end InstW
end
end XHostTW
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.XHostTW.xnetGeomW_unit
#print axioms OAI.PowerSaving.XHostTW.xnetGeomW_heads_first
#print axioms OAI.PowerSaving.XHostTW.xnetGeomW_heads_first_auto
#print axioms OAI.PowerSaving.XHostTW.xnetGeomW_cut_half
