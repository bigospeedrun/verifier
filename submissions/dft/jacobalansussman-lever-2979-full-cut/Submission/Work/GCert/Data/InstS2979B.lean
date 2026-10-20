import Submission.Work.Bridge377.Bank
import Submission.Work.FoldRate.Group
import Submission.Work.GCert.Data.RateS2979Bx
namespace OAI.PowerSaving.BridgeRate.S2979B
open Finset Binary Matrix RAM CB FoldRate
noncomputable section
def invPrice (φ : ℕ → ℝ) : ℝ := 2445 * φ 1 + 706 * φ 2 + 232 * φ 3 + 108 * φ 4 + 18 * φ 5 + 8 * φ 8
def padPrice (φ : ℕ → ℝ) : ℝ := 1 * bcost φ 35 + 1 * bcost φ 36
def unitPrice (φ : ℕ → ℝ) : ℝ := 72 * invPrice φ + ((112:ℕ):ℝ) * GX.bankPrice377 φ + padPrice φ
theorem unit_cost_x (φ : ℕ → ℝ) : unitPrice φ = listCost φ BlockAccounting.blocksS2979Bx := by
  unfold unitPrice invPrice padPrice
  simp only [GX.bankPrice377, listCost, BlockAccounting.blocksS2979Bx, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  norm_num [bcost]
  try ring
theorem unit_tally : unitPrice (fun r => (r:ℝ)) = ((10407:ℕ):ℝ) * 73 - 2560 := by
  rw [unit_cost_x]
  exact BlockAccounting.blocksS2979Bx_tally
end
end OAI.PowerSaving.BridgeRate.S2979B
#print axioms OAI.PowerSaving.BridgeRate.S2979B.unit_cost_x
