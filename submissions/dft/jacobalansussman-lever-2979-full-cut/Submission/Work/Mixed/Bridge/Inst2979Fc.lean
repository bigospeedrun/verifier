import Submission.Work.Mixed.Bridge.CoreF
import Submission.Work.Mixed.Hist2979Fc

/-!
# afc-cut: the A-fc FULL-cut instance (#2979Fc) of the bridge (round wht45/afc)

A-fc (hub PR #2979, Marius-Paul Dumitrean's rank7 joint end frames on the T74 clock, with the re-solved fill
u1-2979sep of round wht45/fullcut): the unit profile is `MX.unit2979Fc` (its PROFILE.json), with 16,576 literal
heads of rank 48 per gauge copy and NO other rank-48 block.  The FULL cut: every head is removed entirely (its 48
lines; target `73 - 48 = 25` on the head array).  fc-engine's generic full-cut bridge (`Work.Mixed.Bridge.CoreF`) is
used unchanged with `a = b = 24`: its split `splitWord 24 24` has nothing left to split (the profile identity
`hcutF2979Fc` has `histFn unit2979Fc 48 - 16576 = 0` rank-24 pieces).  Cut profile `cut2979Fc` (R5 file
`Work.Mixed.Rate2979Fc`): {1: 1630639, 2: 470196, 3: 154512, 4: 71928, 5: 11988, 6: 5, 7: 3, 8: 5328, 17: 8, 19: 1,
23: 25905}; every paid rank at most 23 < 25 (separated); `W0 = 66304` arrays per copy, `Hd = 16576` of them cut.

* `hcutF2979Fc`: unit profile -> full-cut profile (checked by `decide`), with negatives `hcutF2979Fc_fewer` (one head
  fewer breaks it: a rank-24 piece would be left) and `unit2979Fc_ne_cutF` (the unit profile is not the cut profile);
  one head MORE is excluded by the head count (`sched2979Fc_heads`, afc-data), not by this identity (the natural
  subtraction `16576 - 16577` is 0);
* `engine2979Fc_of_cut`: the engine theorem from p-hfirst's heads-first conclusion with the full-cut data given
  directly (frames `A`, the 48 head lines `S`, `bph (z l) = bph ((A l).fam (S l))`), at the seam exponent
  `alphaZ = 1 - (100 N + 1)/10^12`, N = 17887045 (e-r45m1's convention), i.e. the statement `hillsZ_program` takes;
* `bundle2979Fc_of_cut`: the hypothesis bundle of `Eng.engine_seam_final` (kmin 25, rate fact at `zRate2979Fc`).
afc-cut (wht45/afc, 20 Oct 2026) on fc-engine's Inst3945F.lean; prepared with assistance from Claude.  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.PB
open Binary Matrix Finset GF MX RAM

noncomputable section

universe U

/-- Unit profile -> full-cut profile for A-fc: the 16,576 heads of rank 48 disappear; there is no other rank-48
block, so the split adds nothing (`histFn MX.unit2979Fc 48 - 16576 = 0`). -/
theorem hcutF2979Fc : ∀ r, BlockAccounting.histFn MX.cut2979Fc r
    = (if r = 24 + 24 then 0 else BlockAccounting.histFn MX.unit2979Fc r)
      + (if r = 24 then BlockAccounting.histFn MX.unit2979Fc (24 + 24) - 16576 else 0)
      + (if r = 24 then BlockAccounting.histFn MX.unit2979Fc (24 + 24) - 16576 else 0) :=
  hcutF_of_check MX.unit2979Fc MX.cut2979Fc 24 24 16576 [1, 2, 3, 4, 5, 6, 7, 8, 17, 19, 23, 24, 48]
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Negative control: the identity fails with one head fewer (16,575): one rank-48 block would be left and split. -/
theorem hcutF2979Fc_fewer : BlockAccounting.histFn MX.cut2979Fc 24
    ≠ (if (24:ℕ) = 24 + 24 then 0 else BlockAccounting.histFn MX.unit2979Fc 24)
      + (if (24:ℕ) = 24 then BlockAccounting.histFn MX.unit2979Fc (24 + 24) - 16575 else 0)
      + (if (24:ℕ) = 24 then BlockAccounting.histFn MX.unit2979Fc (24 + 24) - 16575 else 0) := by decide

/-- Negative control: the unit profile is not the full-cut profile. -/
theorem unit2979Fc_ne_cutF : BlockAccounting.histFn MX.unit2979Fc 48 ≠ BlockAccounting.histFn MX.cut2979Fc 48 := by decide

/-- The unit profile has exactly 16,576 rank-48 blocks (the heads), not 16,577. -/
theorem unit2979Fc_48 : BlockAccounting.histFn MX.unit2979Fc 48 = 16576 := by decide

theorem unit2979Fc_48_sharp : BlockAccounting.histFn MX.unit2979Fc 48 ≠ 16577 := by decide

section Inst
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]

/-- **(f) for A-fc, full cut (#2979Fc)**: the hypothesis bundle of `Eng.engine_seam_final` (kmin 25, rate fact at
R5's `zRate2979Fc`), from p-hfirst's heads-first conclusion and the full-cut data. -/
theorem bundle2979Fc_of_cut (e : σ → ρ) (he : Function.Injective e) (L : List σ) (hL : L.Nodup)
    (z : σ → Fin 48 → Space α) (ind : ∀ l, LinearIndependent F (z l)) (A : σ → OBase α) (S : σ → Finset α)
    (hz : ∀ l ∈ L, ∀ x, bph (z l) x = bph ((A l).fam (S l)) x)
    (hS : ∀ l ∈ L, (S l).card = 48)
    (G : ℕ) (c0 : (ℕ → ℝ) → ℝ) (U : List (ℕ × ℕ)) (hU : ∀ φ, c0 φ = listCost φ U)
    (hnet : ∃ body : GWord α ρ, body.Proper (Fintype.card α) ∧
      (∀ φ, body.costR φ = (G : ℝ) * c0 φ - (L.length : ℝ) * φ 48) ∧
      GLiveKernel e (headWord e L (fun _ => 48) z ind ++ body))
    (hα : Fintype.card α = 73)
    (hcutF : ∀ r, BlockAccounting.histFn MX.cut2979Fc r
      = (if r = 24 + 24 then 0 else BlockAccounting.histFn U r)
        + (if r = 24 then BlockAccounting.histFn U (24 + 24) - 16576 else 0)
        + (if r = 24 then BlockAccounting.histFn U (24 + 24) - 16576 else 0))
    (hLlen : L.length = G * 16576) (hσ : Fintype.card σ = G * 66304) (hG : 1 ≤ G) :
    ∃ (E : Eng α ρ σ) (R : MX.Rule) (typ : ℕ → Fin R.K),
      E.e = e ∧ E.mx = 73 ∧ E.BridgeHyp R typ 25 ∧ R.RateQ zRate2979Fc 1 := by
  obtain ⟨body, hP, hcost, hk⟩ := hnet
  have hcost' : ∀ φ, body.costR φ = (G : ℝ) * listCost φ U - (L.length : ℝ) * φ 48 := fun φ => by
    rw [hcost φ, hU φ]
  have hmom : BlockAccounting.moment (Fintype.card α) zRate2979Fc MX.cut2979Fc
      ≤ ((66304 - 16576 : ℕ) : ℝ) + BlockAccounting.T (Fintype.card α) zRate2979Fc (Fintype.card α - 48) 16576 := by
    rw [hα]
    exact rate2979Fc_moment
  obtain ⟨E, R, typ, -, h2, -, h4, hB, hR⟩ :=
    full_bundle e he L hL (fun _ => 48) z ind A S hz hS body hP hk 24 24 (by norm_num) (by norm_num)
      (by rw [hα]; norm_num) (by rw [hα]; norm_num) MX.cut2979Fc hcost' hcutF hLlen hσ hG (by norm_num) (by norm_num)
      23 (fun q hq => (cut2979Fc_proper q hq).2) (by rw [hα]; norm_num) (by norm_num) (by rw [hα]; norm_num)
      (by rw [hα]; norm_num) hmom
  refine ⟨E, R, typ, h2, by rw [h4, hα], ?_, hR⟩
  have : Fintype.card α - 48 = 25 := by rw [hα]
  rw [this] at hB
  exact hB

/-- **THE ENGINE THEOREM FOR A-fc, FULL CUT (#2979Fc)** from p-hfirst's heads-first conclusion with the full-cut
data given directly: the `hillsZ_program` statement at the seam exponent `1 - 1788704501/10^12` (DFT figure
1.7887045e-3 with e-r45m1's chain convention). -/
theorem engine2979Fc_of_cut (e : σ → ρ) (he : Function.Injective e) (L : List σ) (hL : L.Nodup)
    (z : σ → Fin 48 → Space α) (ind : ∀ l, LinearIndependent F (z l)) (A : σ → OBase α) (S : σ → Finset α)
    (hz : ∀ l ∈ L, ∀ x, bph (z l) x = bph ((A l).fam (S l)) x)
    (hS : ∀ l ∈ L, (S l).card = 48)
    (G : ℕ) (c0 : (ℕ → ℝ) → ℝ) (U : List (ℕ × ℕ)) (hU : ∀ φ, c0 φ = listCost φ U)
    (hnet : ∃ body : GWord α ρ, body.Proper (Fintype.card α) ∧
      (∀ φ, body.costR φ = (G : ℝ) * c0 φ - (L.length : ℝ) * φ 48) ∧
      GLiveKernel e (headWord e L (fun _ => 48) z ind ++ body))
    (hα : Fintype.card α = 73)
    (hcutF : ∀ r, BlockAccounting.histFn MX.cut2979Fc r
      = (if r = 24 + 24 then 0 else BlockAccounting.histFn U r)
        + (if r = 24 then BlockAccounting.histFn U (24 + 24) - 16576 else 0)
        + (if r = 24 then BlockAccounting.histFn U (24 + 24) - 16576 else 0))
    (hLlen : L.length = G * 16576) (hσ : Fintype.card σ = G * 66304) (hG : 1 ≤ G)
    (m : Bool) (cl : Paint) {ι : Type U} (k : ι → ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2 ^ k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2 ^ k i * envelope (1 - (1788704501:ℝ)/(10:ℝ)^12) (k i)) := by
  obtain ⟨E, R, typ, -, -, hB, hR⟩ :=
    bundle2979Fc_of_cut e he L hL z ind A S hz hS G c0 U hU hnet hα hcutF hLlen hσ hG
  exact E.engine_seam_final hB E.mx le_rfl hR (by norm_num [zRate2979Fc]) (by norm_num [zRate2979Fc])
    (by norm_num) m cl k v

end Inst

end
end PowerSaving.PB
end OAI

#print axioms OAI.PowerSaving.PB.hcutF2979Fc
#print axioms OAI.PowerSaving.PB.hcutF2979Fc_fewer
#print axioms OAI.PowerSaving.PB.unit2979Fc_ne_cutF
#print axioms OAI.PowerSaving.PB.unit2979Fc_48
#print axioms OAI.PowerSaving.PB.unit2979Fc_48_sharp
#print axioms OAI.PowerSaving.PB.bundle2979Fc_of_cut
#print axioms OAI.PowerSaving.PB.engine2979Fc_of_cut
