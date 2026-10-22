import Submission.Work.Mixed.Bridge.Inst2979Nb1
import Submission.Work.XHostT.HF.GeomInst
import Submission.Work.XHostT.HF.Inst2979
import Submission.Work.XHostT.HFW2979.GeomInstW

/-!
# nb1-port: the NB1 FULL-cut (#2979Nb1) engine theorem on the WARP network (the real #2979 provider words)

aA-data's `HFTest2979HW.lean` (x-inst's `HFTest2979W.lean` with design A's numbers) with fc-engine's FULL cut
(`HFTest3945FW.lean`): the heads of the warp network (x-inst's `XHostTW.xnetGeomW_heads_first`; every head is the
block of the 48 A4 lines `a4Lines` of its frame `a4Base`) are removed entirely, so the cut lines of a head are ALL its
48 lines (`cutSF`), and `bph_cutF` is **the 48-line cut fact**, the `hz` of `MX.cut_heads_full` on #2979's words (by
`MX.bph_cast`: the head directions `zGeom` are those lines, cast to `Fin 48`).  The warp network, its heads-first
certificate, `zGeom`, `cutA`, `a4Lines` and `a4Base` are the same modules design A (L2979H) and design B (L3945F)
use; `bph_cutF` is fc-engine's lemma, restated in this namespace for #2979's 74 replicas.
* `engine2979Nb1_geomW`: any head set `hb` (never hosted, remaining climb 48), data facts `hU`, `hcutF`, `hLlen`, `hσ`,
  `hα`;
* `engine2979Nb1_geomW_auto`: 74 replicas, classes `Fin 112`, the canonical head set `headBins S`, the head count in
  Finset form (16,576), positive residuals, any unit profile `U` with `hcutF`;
* `engine2979Nb1_geomW_unit`: the same with `U = MX.unit2979Nb1` (`hcutF2979Nb1`).
Seam exponent `1 - 1788704901/10^12` (DFT figure 1.7887049e-3, e-r45m1's convention).
nb1-port (2026-10-21) on afc-cut's HFTest2979FcW.lean; prepared with assistance from Claude.  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace PB
namespace HFTest2979Nb1W
open Binary Matrix Finset RAM SS CB RF BR GF GX BC B401 XHost XHostR XHostD XHostT XHostTW

noncomputable section

universe U

variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C] {nR : ℕ}
variable {Ok : ∀ {β : Type} [Fintype β] [DecidableEq β], GWin H β → Prop}

/-- the full-cut lines of every live role (only head roles matter): ALL 48 A4 lines of the head of side `s`. -/
def cutSF (l : H) : BLiveT (Orth (BC.LC (Fin 8) H l)) T 0 nR → Finset (BC.LC (Fin 8) H l)
  | Sum.inl (_, d) => a4Lines l (dDecD d).2.1
  | Sum.inr (_, b) => b.elim0

lemma cutSF_card (l : H) (hH : Fintype.card H = 9) (r : BLiveT (Orth (BC.LC (Fin 8) H l)) T 0 nR) :
    (cutSF l r).card = 48 := by
  rcases r with (⟨_, d⟩ | ⟨_, b⟩)
  · exact a4Lines_card hH l _
  · exact b.elim0

/-- **THE 48-LINE CUT FACT on #2979's words** (the `hz` of `MX.cut_heads_full`): each head of the warp network is the
block of all 48 lines `cutSF` of its frame `cutA`. -/
lemma bph_cutF (base : T → OBase H) (l : H) (hH : Fintype.card H = 9) (hb : Finset (Fin nR × Bool × T))
    (r : BLiveT (Orth (BC.LC (Fin 8) H l)) T 0 nR) (hr : r ∈ headsL (nb := 0) hb) (x : Space (BC.LC (Fin 8) H l)) :
    MX.bph (zGeom base l hH r) x = MX.bph ((cutA base l r).fam (cutSF l r)) x := by
  obtain ⟨p, -, g, rfl⟩ := (mem_headsL hb r).1 hr
  obtain ⟨ρ, s, t⟩ := p
  cases s
  · exact MX.bph_cast (a4Lines_card hH l false).symm ((a4Base base l g t).fam (a4Lines l false)) x
  · exact MX.bph_cast (a4Lines_card hH l true).symm ((a4Base base l g t).fam (a4Lines l true)) x

/-- **The NB1 FULL-cut (#2979Nb1) engine theorem from the geometric WARP network.** -/
theorem engine2979Nb1_geomW (I : GInvW H T Sl C Ok) (Ic : Fin nR → Fin 9 → GInvW H T Sl C Ok)
    (hIc : ∀ ρ l, (Ic ρ l).tv = I.tv) (base : T → OBase H) (l : H) (hbase : ∀ t, I.tv t = (base t).v l)
    (hH : Fintype.card H = 9) (hOk : ∀ (n : ℕ) (d : Orth (BC.LC (Fin 8) H l)), Ok (win401N l hH n d))
    (S : HostSchedT nR Sl T) (hfit : S.fits (resIcW Ic))
    (hb : Finset (Fin nR × Bool × T))
    (hunh : ∀ ρ l' q ρh j, (ρh, j) ∈ hb → S.host ρ l' q ≠ (ρh, 4, j))
    (h48 : ∀ ρ j, (ρ, j) ∈ hb → S.hrem ρ 4 j = 48)
    (U : List (ℕ × ℕ)) (hU : ∀ φ, unitPriceTW Ic S φ = listCost φ U)
    (hcutF : ∀ r, BlockAccounting.histFn MX.cut2979Nb1 r
      = (if r = 24 + 24 then 0 else BlockAccounting.histFn U r)
        + (if r = 24 then BlockAccounting.histFn U (24 + 24) - 16576 else 0)
        + (if r = 24 then BlockAccounting.histFn U (24 + 24) - 16576 else 0))
    (hLlen : (headsL (Γ := Orth (BC.LC (Fin 8) H l)) (nb := 0) hb).length
      = Fintype.card (Orth (BC.LC (Fin 8) H l)) * 16576)
    (hσ : Fintype.card (BLiveT (Orth (BC.LC (Fin 8) H l)) T 0 nR)
      = Fintype.card (Orth (BC.LC (Fin 8) H l)) * 66304)
    (hα : Fintype.card (BC.LC (Fin 8) H l) = 73)
    (m : Bool) (cl : Paint) {ι : Type U} (k : ι → ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2 ^ k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2 ^ k i * envelope (1 - (1788704901:ℝ)/(10:ℝ)^12) (k i)) :=
  engine2979Nb1_of_cut Sum.inl Sum.inl_injective (headsL hb) (headsL_nodup hb) (zGeom base l hH)
    (zGeom_indep base l hH) (cutA base l) (cutSF l) (bph_cutF base l hH hb)
    (fun r _ => cutSF_card l hH r)
    (Fintype.card (Orth (BC.LC (Fin 8) H l))) (unitPriceTW Ic S) U hU
    (xnetGeomW_heads_first I Ic hIc base l hbase hH hOk S hfit hb hunh h48) hα hcutF hLlen hσ Orth.card_pos m cl k v

/-- **The NB1 FULL-cut (#2979Nb1) engine theorem from the warp network and the table data**: 74 replicas, classes
`Fin 112`, the canonical head set, the head count in Finset form (afc-data's `sched2979Nb1_heads`), positive
residuals. -/
theorem engine2979Nb1_geomW_auto (I : GInvW H (Fin 112) Sl C Ok) (Ic : Fin 74 → Fin 9 → GInvW H (Fin 112) Sl C Ok)
    (hIc : ∀ ρ l, (Ic ρ l).tv = I.tv) (base : Fin 112 → OBase H) (l : H) (hbase : ∀ t, I.tv t = (base t).v l)
    (hH : Fintype.card H = 9) (hOk : ∀ (n : ℕ) (d : Orth (BC.LC (Fin 8) H l)), Ok (win401N l hH n d))
    (S : HostSchedT 74 Sl (Fin 112)) (hfit : S.fits (resIcW Ic))
    (hpos : ∀ ρ l' q, 0 < resIcW Ic ρ l' q)
    (hheads : (Finset.univ.filter (fun p : Fin 74 × Bool × Fin 112 => S.hrem p.1 4 p.2 = 48)).card = 16576)
    (U : List (ℕ × ℕ)) (hU : ∀ φ, unitPriceTW Ic S φ = listCost φ U)
    (hcutF : ∀ r, BlockAccounting.histFn MX.cut2979Nb1 r
      = (if r = 24 + 24 then 0 else BlockAccounting.histFn U r)
        + (if r = 24 then BlockAccounting.histFn U (24 + 24) - 16576 else 0)
        + (if r = 24 then BlockAccounting.histFn U (24 + 24) - 16576 else 0))
    (m : Bool) (cl : Paint) {ι : Type U} (k : ι → ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2 ^ k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2 ^ k i * envelope (1 - (1788704901:ℝ)/(10:ℝ)^12) (k i)) :=
  engine2979Nb1_geomW I Ic hIc base l hbase hH hOk S hfit (headBins S) (headBins_unh S) (headBins_48 S) U hU hcutF
    (I2979.hLlen_card S (resIcW Ic) hfit hpos hheads) (I2979.card_live2979 _) (card_LC401 l hH) m cl k v

/-- The same with NB1's unit profile `MX.unit2979Nb1` (`hcutF2979Nb1`). -/
theorem engine2979Nb1_geomW_unit (I : GInvW H (Fin 112) Sl C Ok) (Ic : Fin 74 → Fin 9 → GInvW H (Fin 112) Sl C Ok)
    (hIc : ∀ ρ l, (Ic ρ l).tv = I.tv) (base : Fin 112 → OBase H) (l : H) (hbase : ∀ t, I.tv t = (base t).v l)
    (hH : Fintype.card H = 9) (hOk : ∀ (n : ℕ) (d : Orth (BC.LC (Fin 8) H l)), Ok (win401N l hH n d))
    (S : HostSchedT 74 Sl (Fin 112)) (hfit : S.fits (resIcW Ic))
    (hpos : ∀ ρ l' q, 0 < resIcW Ic ρ l' q)
    (hheads : (Finset.univ.filter (fun p : Fin 74 × Bool × Fin 112 => S.hrem p.1 4 p.2 = 48)).card = 16576)
    (hU : ∀ φ, unitPriceTW Ic S φ = listCost φ MX.unit2979Nb1)
    (m : Bool) (cl : Paint) {ι : Type U} (k : ι → ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2 ^ k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2 ^ k i * envelope (1 - (1788704901:ℝ)/(10:ℝ)^12) (k i)) :=
  engine2979Nb1_geomW_auto I Ic hIc base l hbase hH hOk S hfit hpos hheads MX.unit2979Nb1 hU hcutF2979Nb1 m cl k v

end
end HFTest2979Nb1W
end PB
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.PB.HFTest2979Nb1W.bph_cutF
#print axioms OAI.PowerSaving.PB.HFTest2979Nb1W.engine2979Nb1_geomW
#print axioms OAI.PowerSaving.PB.HFTest2979Nb1W.engine2979Nb1_geomW_auto
#print axioms OAI.PowerSaving.PB.HFTest2979Nb1W.engine2979Nb1_geomW_unit
