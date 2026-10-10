import Submission.Work.GFrame.Engine.Group
import Submission.Work.CarrierCheck.B2Ke16

/-!
# GFrame, top (key: eng-integrate): the present record THROUGH the re-based engine

Regression and template.  The comparator-checked theorem `WHT.wht_main_B2Ke16x`
(`1 - 5399225/10^10`, `Work/CarrierCheck/B2Ke16.lean`) is re-derived with the GENERALISED
engine (`GWord`, `gwalk`, `GLiveKernel`: `BlockWHT.wht_main_of_ggroup_list`) from the same
kernel-checked certificate, the same block list and the same numeric fact
`BlockAccounting.fold_B2Ke16x`:

* `BridgeRate.B2Ke16.wht_of_gcert_x`   = `wht_of_bcert_x` with `BCert ↦ GCert` (same proof term
                                         with `engine_program_group_list ↦ _ggroup_list`);
* `WHT.wht_main_B2Ke16x_via_g`         the record, the network certificate entering as
                                         `GCert.ofB`.

A new network that delivers a `GCert` (through `gcert_of_sched` / `gcert_of_groute`) with a new
unit price needs exactly this pair of lemmas with its own block list and `fold_*` fact.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace BridgeRate
namespace B2Ke16
open Finset Binary Matrix RAM RAM.Ty CB FoldRate

/-- **Walsh-Hadamard transform at `1 - 5399225/10^10` from a GENERALISED certificate of `G`
units** (same hypotheses as `wht_of_bcert_x`, with `GCert` in the place of `BCert`). -/
theorem wht_of_gcert_x {α ρ σ : Type} [Fintype α] [DecidableEq α] [Fintype ρ]
    [DecidableEq ρ] [Fintype σ] [DecidableEq σ]
    (hα : Fintype.card α = 80) (e : σ → ρ) (he : Function.Injective e)
    (G : ℕ) (hG : 1 ≤ G) (hσ : Fintype.card σ = G * (4 * cert.v + cert.R))
    (c : (ℕ → ℝ) → ℝ) (h : GF.GCert α e c)
    (hc : ∀ φ : ℕ → ℝ, c φ = (G:ℝ) * unitPrice φ) :
    ∃ solve W, WHT.WHTProgram solve W ∧ BlockWHT.WHTTimeBoundsAt (1 - 5399225/(10:ℝ)^10) W :=
  BlockWHT.wht_main_of_ggroup_list 80 hα (by norm_num) e he G 9362 hG (by norm_num)
    (hσ.trans (by rw [unit_live])) c h
    BlockAccounting.blocksB2Ke16x (fun φ => by rw [hc, unit_cost, blocks_x]) 40
    (1 - 5399225/(10:ℝ)^10) (by norm_num) (by norm_num) BlockAccounting.fold_B2Ke16x

end B2Ke16
end BridgeRate

namespace WHT
open BlockWHT

/-- **The present record, through the generalised engine.** -/
theorem wht_main_B2Ke16x_via_g :
    ∃ solve W, WHTProgram solve W ∧ BlockWHT.WHTTimeBoundsAt (1 - 5399225/(10:ℝ)^10) W := by
  obtain ⟨Γ, i1, i2, hG, h⟩ := B2Ke16.certificate_block
  exact BridgeRate.B2Ke16.wht_of_gcert_x B2Ke16.card_label Sum.inl Sum.inl_injective
    (Fintype.card Γ) hG (B2Ke16.card_live Γ) _ (GF.GCert.ofB h) (fun φ => rfl)

end WHT
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.BridgeRate.B2Ke16.wht_of_gcert_x
#print axioms OAI.PowerSaving.WHT.wht_main_B2Ke16x_via_g
