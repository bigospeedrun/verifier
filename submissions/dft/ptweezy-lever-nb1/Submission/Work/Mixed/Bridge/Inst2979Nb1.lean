import Submission.Work.Mixed.Bridge.CoreF
import Submission.Work.Mixed.Hist2979Nb1

/-!
# nb1-port: the NB1 FULL-cut instance (#2979Nb1) of the bridge

NB1 (hub PR #2979, Marius-Paul Dumitrean's rank7 joint end frames on the T74 clock, with the table-MIP fill
NB1s7, SOL-NB1 seed 7): the unit profile is `MX.unit2979Nb1` (its PROFILE.json), with 16,576 literal
heads of rank 48 per gauge copy and NO other rank-48 block.  The FULL cut: every head is removed entirely (its 48
lines; target `73 - 48 = 25` on the head array).  fc-engine's generic full-cut bridge (`Work.Mixed.Bridge.CoreF`) is
used unchanged with `a = b = 24`: its split `splitWord 24 24` has nothing left to split (the profile identity
`hcutF2979Nb1` has `histFn unit2979Nb1 48 - 16576 = 0` rank-24 pieces).  Cut profile `cut2979Nb1` (R5 file
`Work.Mixed.Rate2979Nb1`): {1: 1630638, 2: 470196, 3: 154512, 4: 71928, 5: 11988, 6: 4, 7: 4, 8: 5328, 17: 8, 21: 2,
23: 25904}; every paid rank at most 23 < 25 (separated); `W0 = 66304` arrays per copy, `Hd = 16576` of them cut.

* `hcutF2979Nb1`: unit profile -> full-cut profile (checked by `decide`), with negatives `hcutF2979Nb1_fewer` (one head
  fewer breaks it: a rank-24 piece would be left) and `unit2979Nb1_ne_cutF` (the unit profile is not the cut profile);
  one head MORE is excluded by the head count (`sched2979Nb1_heads`, afc-data), not by this identity (the natural
  subtraction `16576 - 16577` is 0);
* `engine2979Nb1_of_cut`: the engine theorem from p-hfirst's heads-first conclusion with the full-cut data given
  directly (frames `A`, the 48 head lines `S`, `bph (z l) = bph ((A l).fam (S l))`), at the seam exponent
  `alphaZ = 1 - (100 N + 1)/10^12`, N = 17887049 (e-r45m1's convention), i.e. the statement `hillsZ_program` takes;
* `bundle2979Nb1_of_cut`: the hypothesis bundle of `Eng.engine_seam_final` (kmin 25, rate fact at `zRate2979Nb1`).
nb1-port (2026-10-21) on afc-cut's Inst2979Fc.lean (fc-engine's Inst3945F.lean pattern); prepared with assistance from Claude.  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.PB
open Binary Matrix Finset GF MX RAM

noncomputable section

universe U

/-- Unit profile -> full-cut profile for NB1: the 16,576 heads of rank 48 disappear; there is no other rank-48
block, so the split adds nothing (`histFn MX.unit2979Nb1 48 - 16576 = 0`). -/
theorem hcutF2979Nb1 : ∀ r, BlockAccounting.histFn MX.cut2979Nb1 r
    = (if r = 24 + 24 then 0 else BlockAccounting.histFn MX.unit2979Nb1 r)
      + (if r = 24 then BlockAccounting.histFn MX.unit2979Nb1 (24 + 24) - 16576 else 0)
      + (if r = 24 then BlockAccounting.histFn MX.unit2979Nb1 (24 + 24) - 16576 else 0) :=
  hcutF_of_check MX.unit2979Nb1 MX.cut2979Nb1 24 24 16576 [1, 2, 3, 4, 5, 6, 7, 8, 17, 21, 23, 24, 48]
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Negative control: the identity fails with one head fewer (16,575): one rank-48 block would be left and split. -/
theorem hcutF2979Nb1_fewer : BlockAccounting.histFn MX.cut2979Nb1 24
    ≠ (if (24:ℕ) = 24 + 24 then 0 else BlockAccounting.histFn MX.unit2979Nb1 24)
      + (if (24:ℕ) = 24 then BlockAccounting.histFn MX.unit2979Nb1 (24 + 24) - 16575 else 0)
      + (if (24:ℕ) = 24 then BlockAccounting.histFn MX.unit2979Nb1 (24 + 24) - 16575 else 0) := by decide

/-- Negative control: the unit profile is not the full-cut profile. -/
theorem unit2979Nb1_ne_cutF : BlockAccounting.histFn MX.unit2979Nb1 48 ≠ BlockAccounting.histFn MX.cut2979Nb1 48 := by decide

/-- The unit profile has exactly 16,576 rank-48 blocks (the heads), not 16,577. -/
theorem unit2979Nb1_48 : BlockAccounting.histFn MX.unit2979Nb1 48 = 16576 := by decide

theorem unit2979Nb1_48_sharp : BlockAccounting.histFn MX.unit2979Nb1 48 ≠ 16577 := by decide

section Inst
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]

/-- **(f) for NB1, full cut (#2979Nb1)**: the hypothesis bundle of `Eng.engine_seam_final` (kmin 25, rate fact at
R5's `zRate2979Nb1`), from p-hfirst's heads-first conclusion and the full-cut data. -/
theorem bundle2979Nb1_of_cut (e : σ → ρ) (he : Function.Injective e) (L : List σ) (hL : L.Nodup)
    (z : σ → Fin 48 → Space α) (ind : ∀ l, LinearIndependent F (z l)) (A : σ → OBase α) (S : σ → Finset α)
    (hz : ∀ l ∈ L, ∀ x, bph (z l) x = bph ((A l).fam (S l)) x)
    (hS : ∀ l ∈ L, (S l).card = 48)
    (G : ℕ) (c0 : (ℕ → ℝ) → ℝ) (U : List (ℕ × ℕ)) (hU : ∀ φ, c0 φ = listCost φ U)
    (hnet : ∃ body : GWord α ρ, body.Proper (Fintype.card α) ∧
      (∀ φ, body.costR φ = (G : ℝ) * c0 φ - (L.length : ℝ) * φ 48) ∧
      GLiveKernel e (headWord e L (fun _ => 48) z ind ++ body))
    (hα : Fintype.card α = 73)
    (hcutF : ∀ r, BlockAccounting.histFn MX.cut2979Nb1 r
      = (if r = 24 + 24 then 0 else BlockAccounting.histFn U r)
        + (if r = 24 then BlockAccounting.histFn U (24 + 24) - 16576 else 0)
        + (if r = 24 then BlockAccounting.histFn U (24 + 24) - 16576 else 0))
    (hLlen : L.length = G * 16576) (hσ : Fintype.card σ = G * 66304) (hG : 1 ≤ G) :
    ∃ (E : Eng α ρ σ) (R : MX.Rule) (typ : ℕ → Fin R.K),
      E.e = e ∧ E.mx = 73 ∧ E.BridgeHyp R typ 25 ∧ R.RateQ zRate2979Nb1 1 := by
  obtain ⟨body, hP, hcost, hk⟩ := hnet
  have hcost' : ∀ φ, body.costR φ = (G : ℝ) * listCost φ U - (L.length : ℝ) * φ 48 := fun φ => by
    rw [hcost φ, hU φ]
  have hmom : BlockAccounting.moment (Fintype.card α) zRate2979Nb1 MX.cut2979Nb1
      ≤ ((66304 - 16576 : ℕ) : ℝ) + BlockAccounting.T (Fintype.card α) zRate2979Nb1 (Fintype.card α - 48) 16576 := by
    rw [hα]
    exact rate2979Nb1_moment
  obtain ⟨E, R, typ, -, h2, -, h4, hB, hR⟩ :=
    full_bundle e he L hL (fun _ => 48) z ind A S hz hS body hP hk 24 24 (by norm_num) (by norm_num)
      (by rw [hα]; norm_num) (by rw [hα]; norm_num) MX.cut2979Nb1 hcost' hcutF hLlen hσ hG (by norm_num) (by norm_num)
      23 (fun q hq => (cut2979Nb1_proper q hq).2) (by rw [hα]; norm_num) (by norm_num) (by rw [hα]; norm_num)
      (by rw [hα]; norm_num) hmom
  refine ⟨E, R, typ, h2, by rw [h4, hα], ?_, hR⟩
  have : Fintype.card α - 48 = 25 := by rw [hα]
  rw [this] at hB
  exact hB

/-- **THE ENGINE THEOREM FOR NB1, FULL CUT (#2979Nb1)** from p-hfirst's heads-first conclusion with the full-cut
data given directly: the `hillsZ_program` statement at the seam exponent `1 - 1788704901/10^12` (DFT figure
1.7887049e-3 with e-r45m1's chain convention). -/
theorem engine2979Nb1_of_cut (e : σ → ρ) (he : Function.Injective e) (L : List σ) (hL : L.Nodup)
    (z : σ → Fin 48 → Space α) (ind : ∀ l, LinearIndependent F (z l)) (A : σ → OBase α) (S : σ → Finset α)
    (hz : ∀ l ∈ L, ∀ x, bph (z l) x = bph ((A l).fam (S l)) x)
    (hS : ∀ l ∈ L, (S l).card = 48)
    (G : ℕ) (c0 : (ℕ → ℝ) → ℝ) (U : List (ℕ × ℕ)) (hU : ∀ φ, c0 φ = listCost φ U)
    (hnet : ∃ body : GWord α ρ, body.Proper (Fintype.card α) ∧
      (∀ φ, body.costR φ = (G : ℝ) * c0 φ - (L.length : ℝ) * φ 48) ∧
      GLiveKernel e (headWord e L (fun _ => 48) z ind ++ body))
    (hα : Fintype.card α = 73)
    (hcutF : ∀ r, BlockAccounting.histFn MX.cut2979Nb1 r
      = (if r = 24 + 24 then 0 else BlockAccounting.histFn U r)
        + (if r = 24 then BlockAccounting.histFn U (24 + 24) - 16576 else 0)
        + (if r = 24 then BlockAccounting.histFn U (24 + 24) - 16576 else 0))
    (hLlen : L.length = G * 16576) (hσ : Fintype.card σ = G * 66304) (hG : 1 ≤ G)
    (m : Bool) (cl : Paint) {ι : Type U} (k : ι → ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2 ^ k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2 ^ k i * envelope (1 - (1788704901:ℝ)/(10:ℝ)^12) (k i)) := by
  obtain ⟨E, R, typ, -, -, hB, hR⟩ :=
    bundle2979Nb1_of_cut e he L hL z ind A S hz hS G c0 U hU hnet hα hcutF hLlen hσ hG
  exact E.engine_seam_final hB E.mx le_rfl hR (by norm_num [zRate2979Nb1]) (by norm_num [zRate2979Nb1])
    (by norm_num) m cl k v

end Inst

end
end PowerSaving.PB
end OAI

#print axioms OAI.PowerSaving.PB.hcutF2979Nb1
#print axioms OAI.PowerSaving.PB.hcutF2979Nb1_fewer
#print axioms OAI.PowerSaving.PB.unit2979Nb1_ne_cutF
#print axioms OAI.PowerSaving.PB.unit2979Nb1_48
#print axioms OAI.PowerSaving.PB.unit2979Nb1_48_sharp
#print axioms OAI.PowerSaving.PB.bundle2979Nb1_of_cut
#print axioms OAI.PowerSaving.PB.engine2979Nb1_of_cut
