import Submission.Work.PWGen.S2979Pair
import Submission.Work.XHostT.HFW2979.Disp2979W
import Submission.Work.XHostT.Inst.S2979Nb1Facts
import Submission.Work.Mixed.Hist2979Nb1

/-!
# nb1-port: the data of the #2979 warp network for NB1 (fill NB1s7, 1285b9a0; full cut, suffix L2979Nb1)

* `I0W`, `I1W`: x-words' two #2979 provider packages (`PWG2979.ginvE` = extra, provider 0; `PWG2979.ginvB` = gauge44,
  provider 1; windowed `KLW.GInvEW .. GXD.S2979B.okW`) as p-a3's warp providers `XHostTW.GInvW` (the same seven
  fields);
* `Ic2979W`: the per-call providers by x-tables' dispatch table `D2979.disp` (x-inst's `D2979W.IcW`), with
  `hIc2979W` (one target-vector family, x-words' `PWG2979.tv_eq`);
* `hOk2979`: every window of the network (Shea's `win401N`, conjugation windows `gwinC`) has a warp meaning
  (x-words' `GXD.S2979B.okC`, by p-warpsem's `WLift.ofConj`);
* `resIcW2979Nb1`: the entrance residual of every slot of every call is the host table's (x-words' `hent` against
  the nb1 data layer's residual table `DH2979Nb1.resT` (= x-tables'), two kernel checks `resE_ok`, `resB_ok`, and the
  data layer's `dp_disp`); hence `hfit2979Nb1W` (the data layer's `sched2979Nb1_fits`) and `hpos2979Nb1W`;
* `hU2979Nb1W`: the unit price of the network is `listCost φ MX.unit2979Nb1` (666 calls of the local profile
  {1: 2445, 2: 706, 3: 232, 4: 108, 5: 18, 8: 8} plus the remaining climbs {1: 2268, 6: 4, 7: 4, 17: 8, 21: 2, 23: 25904, 48: 16576}).
aA-final's `Work/L2979H/Prov.lean` (x-final's `Work/L2979/Prov.lean` for the every-head-kept fill) with the schedule,
host table and unit profile of NB1 (the data layer's `sched2979Nb1`, `K.DH2979Nb1`; `MX.unit2979Nb1`: 16,576 heads and
no other rank-48 block; the providers, dispatch and residuals do not depend on the fill).  nb1-port (2026-10-21;
made by tools/mk_prov2979Nb1.py, afc-cut's generator with the NB1 pins/texts); prepared with assistance from Claude.  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000
namespace OAI
namespace PowerSaving
namespace MX
namespace L2979Nb1
open Finset Binary Matrix RAM SS CB RF BR GF GX BC B401 XHost XHostR XHostD XHostT XHostTW

noncomputable section

/-- provider 0 of #2979's dispatch (the extra word) as a warp provider of p-a3's network. -/
def I0W : GInvW (Fin 9) (Fin 112) (Fin 408) (Fin 99) GXD.S2979B.okW :=
  ⟨PWG2979.ginvE.tv, PWG2979.ginvE.hunit, PWG2979.ginvE.hgap, PWG2979.ginvE.cost, PWG2979.ginvE.ent,
   PWG2979.ginvE.fwd, PWG2979.ginvE.bwd⟩

/-- provider 1 of #2979's dispatch (the gauge44 word) as a warp provider of p-a3's network. -/
def I1W : GInvW (Fin 9) (Fin 112) (Fin 408) (Fin 99) GXD.S2979B.okW :=
  ⟨PWG2979.ginvB.tv, PWG2979.ginvB.hunit, PWG2979.ginvB.hgap, PWG2979.ginvB.cost, PWG2979.ginvB.ent,
   PWG2979.ginvB.fwd, PWG2979.ginvB.bwd⟩

/-- the provider of every call of #2979 (x-tables' table: 416 extra, 250 gauge44). -/
def Ic2979W : Fin 74 → Fin 9 → GInvW (Fin 9) (Fin 112) (Fin 408) (Fin 99) GXD.S2979B.okW :=
  D2979W.IcW D2979.disp I0W I1W

theorem hIc2979W : ∀ ρ l, (Ic2979W ρ l).tv = I0W.tv :=
  D2979W.hIcW D2979.disp I0W I1W PWG2979.tv_eq

/-- **every window of the network has a warp meaning** (Shea's windows are conjugation windows `gwinC`). -/
theorem hOk2979 : ∀ (l : Fin 9) (n : ℕ) (d : Orth (BC.LC (Fin 8) (Fin 9) l)),
    GXD.S2979B.okW (win401N l (Fintype.card_fin 9) n d) := by
  intro l n d
  unfold win401N
  split <;> exact GXD.S2979B.okC _ _ _ _

/-- the residual list `L` agrees with provider `p` of a residual table on the slots `q < m`. -/
def resEqL (resT p : Nat) (L : List Nat) : Nat → Bool
  | 0 => true
  | m + 1 => resEqL resT p L m && Nat.beq (L.getD m 0) (K.resAt resT p m)

theorem resEqL_sound (resT p : Nat) (L : List Nat) :
    ∀ m, resEqL resT p L m = true → ∀ q < m, L.getD q 0 = K.resAt resT p q
  | 0, _, q, hq => absurd hq (Nat.not_lt_zero q)
  | m + 1, h, q, hq => by
    simp only [resEqL, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hq | rfl
    · exact resEqL_sound resT p L m h.1 q hq
    · exact Nat.eq_of_beq_eq_true h.2

/-- the extra word's slot residuals (x-words) are provider 0's of x-tables' table. -/
theorem resE_ok : resEqL K.DH2979Nb1.resT 0 GXD.S2979E.schedRes 408 = true := by decide +kernel
/-- the gauge44 word's slot residuals (x-words) are provider 1's of x-tables' table. -/
theorem resB_ok : resEqL K.DH2979Nb1.resT 1 GXD.S2979B.schedRes 408 = true := by decide +kernel

/-- **the residual of every slot of every call is the host table's.** -/
theorem resIcW2979Nb1 (ρ : Fin 74) (l : Fin 9) (q : Fin 408) :
    resIcW Ic2979W ρ l q = resK K.DH2979Nb1.ct K.DH2979Nb1.resT 74 408 ρ l q := by
  rw [Inst.resK2979Nb1_disp]
  have hp := (D2979.disp (ρ, l)).isLt
  unfold resIcW Ic2979W D2979W.IcW
  by_cases h0 : (D2979.disp (ρ, l)).val = 0
  · rw [if_pos h0, h0]
    show Fintype.card (Fin 9) - (GXD.S2979E.ginvW.ent q).dim = K.resAt K.DH2979Nb1.resT 0 q.val
    rw [GXD.S2979E.hent q]
    exact resEqL_sound _ _ _ 408 resE_ok q.val q.isLt
  · have h1 : (D2979.disp (ρ, l)).val = 1 := by omega
    rw [if_neg h0, h1]
    show Fintype.card (Fin 9) - (GXD.S2979B.ginvW.ent q).dim = K.resAt K.DH2979Nb1.resT 1 q.val
    rw [GXD.S2979B.hent q]
    exact resEqL_sound _ _ _ 408 resB_ok q.val q.isLt

/-- **the schedule fits the providers' residuals** (the nb1 data layer's `sched2979Nb1_fits`). -/
theorem hfit2979Nb1W : Inst.sched2979Nb1.fits (resIcW Ic2979W) := by
  have e : resIcW Ic2979W = resK K.DH2979Nb1.ct K.DH2979Nb1.resT 74 408 := by
    funext ρ l q
    exact resIcW2979Nb1 ρ l q
  rw [e]
  exact Inst.sched2979Nb1_fits

theorem hpos2979Nb1W : ∀ ρ l q, 0 < resIcW Ic2979W ρ l q := fun ρ l q => by
  rw [resIcW2979Nb1]
  exact Inst.resK2979Nb1_pos ρ l q

/-- **the unit price of the #2979 warp network is its profile** `MX.unit2979Nb1`. -/
theorem hU2979Nb1W (φ : ℕ → ℝ) : unitPriceTW Ic2979W Inst.sched2979Nb1 φ = listCost φ MX.unit2979Nb1 := by
  rw [D2979W.unitPriceTW_const Ic2979W Inst.sched2979Nb1 I0W.cost
        (D2979W.IcW_cost D2979.disp I0W I1W (fun φ => (PWG2979.same_price φ).symm)) φ,
      Inst.sched2979Nb1_hcost]
  show ((9 * 74 : ℕ) : ℝ) * GXD.S2979E.ginvW.cost φ + (2268 * φ 1 + 4 * φ 6 + 4 * φ 7 + 8 * φ 17 + 2 * φ 21 + 25904 * φ 23 + 16576 * φ 48)
    = listCost φ MX.unit2979Nb1
  rw [GXD.S2979E.ginv_cost]
  unfold GXD.S2979E.invPrice
  simp only [listCost, MX.unit2979Nb1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

end
end L2979Nb1
end MX
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.MX.L2979Nb1.hIc2979W
#print axioms OAI.PowerSaving.MX.L2979Nb1.hOk2979
#print axioms OAI.PowerSaving.MX.L2979Nb1.resIcW2979Nb1
#print axioms OAI.PowerSaving.MX.L2979Nb1.hfit2979Nb1W
#print axioms OAI.PowerSaving.MX.L2979Nb1.hpos2979Nb1W
#print axioms OAI.PowerSaving.MX.L2979Nb1.hU2979Nb1W
