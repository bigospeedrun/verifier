import Submission.Work.T16A8Z.Stmt
import Submission.Work.Mixed.HeadM1
import Submission.Work.BlockAccounting.Moment
-- changed for the tensor-power extension (30103/10000000); see Submission.lean

/-!
# Route E (tensor power of the RAW p16a8z unit): the RAW certificate statement

* `RawCert16Z α ρ σ`  the RAW p16a8z certificate with `G ≥ 1` gauge copies, in EXACTLY the shape of the p16a8z builder's
  `OAI.PowerSaving.P16A8.Z.rawCert_exists` (Submission/Work/P16A8/RawZ.lean): a word `wd` on roles `ρ`,
  live roles `σ` (injective `e`), arrays of 145 axes, every live role ending at `blockMat (tz l)` of its OWN input
  (`MX.GLiveKernelM`), target ranks in `[1, 145]` distributed as `G` copies of `rawTgt16Z`, block histogram `G` copies of
  `rawPaid16Z`.
* Such a certificate exists: `PB.T16A8Z.rawCert16Z_ex` (T16A8Z/RawCert.lean, from the p16a8z builder's
  `P16A8.Z.rawCert_exists`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace PB
namespace T16A8Z
open Binary Matrix Finset GF MX RAM

noncomputable section

/-- the RAW p16a8z unit's paid blocks `(rank, count)` (= `TensorProto.P16A8Z.PP16A8Z` = p16a8z's `P16A8.Z.Praw`). -/
def rawPaid16Z : List (ℕ × ℕ) :=
  [(1, 41946), (2, 6984), (3, 8892), (4, 2646), (5, 648), (8, 144), (16, 448), (24, 448), (32, 448), (40, 448), (48, 448), (56, 448), (64, 448), (72, 224)]

/-- the RAW p16a8z unit's live targets `(rank, count)` (= `TensorProto.P16A8Z.TP16A8Z` = p16a8z's `P16A8.Z.Traw`). -/
def rawTgt16Z : List (ℕ × ℕ) :=
  [(4, 504), (7, 126), (8, 846), (9, 5868), (17, 448), (25, 448), (33, 448), (41, 448), (49, 448), (57, 448), (65, 448), (73, 224), (145, 224)]

/-- **The RAW p16a8z certificate with `G` copies** on given types. -/
def RawCert16Z (α ρ σ : Type) [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] [Fintype σ]
    [DecidableEq σ] : Prop :=
  ∃ (e : σ → ρ) (tr : σ → ℕ) (tz : ∀ l, Fin (tr l) → Space α) (wd : GWord α ρ) (G : ℕ),
    Function.Injective e ∧ (∀ l, LinearIndependent F (tz l)) ∧ wd.Proper (Fintype.card α) ∧
    MX.GLiveKernelM e (fun l => blockMat (tz l)) wd ∧
    1 ≤ G ∧ Fintype.card α = 145 ∧
    (∀ l, 1 ≤ tr l ∧ tr l ≤ 145) ∧
    (∀ r, (Finset.univ.filter fun l => tr l = r).card = G * BlockAccounting.histFn rawTgt16Z r) ∧
    (∀ r, wd.hist r = G * BlockAccounting.histFn rawPaid16Z r)

end
end T16A8Z
end PB
end PowerSaving
end OAI
