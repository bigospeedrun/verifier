import Submission.Work.MixedCost.Bridge
import Submission.Work.Mixed.TwoTarget

/-!
# The bridge hypotheses for the two-target rule of a cut word (agent e-r3cost)

`bridge_twoTarget`: if every live role of the engine `E` has target rank `mx` (full) or `kc` (cut), the block
ranks are in `[1, rmax]` with `rmax < kc`, then e-r12's `twoTarget` rule built from `E`'s numbers satisfies
`BridgeHyp` with the type map "cut or not".
-/

set_option linter.unusedSectionVars false

namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset GF MXR
noncomputable section

namespace Eng
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ] (E : Eng α ρ σ)

theorem bridge_twoTarget (kc rmax H : ℕ) (hrk1 : ∀ j : Fin E.nB, 1 ≤ E.rkI j)
    (hrk : ∀ j : Fin E.nB, E.rkI j ≤ rmax) (hsep : rmax < kc) (hkc : kc ≤ E.mx) (h2 : 2 ≤ kc) (hH : 1 ≤ H)
    (htq2 : ∀ x, x < E.W → E.tq x = E.mx ∨ E.tq x = kc) (hne : kc ≠ E.mx)
    (hHdef : ((range E.W).filter (fun x => E.tq x = kc)).card = H) :
    E.BridgeHyp (MX.Rule.twoTarget E.mx kc E.W H E.nB rmax (fun j => E.rkI j) hrk1 hrk hsep hkc h2 hH)
      (fun x => ((if E.tq x = kc then 1 else 0 : Fin 2))) kc := by
  refine ⟨rfl, rfl, fun j => rfl, fun x hx => ?_, fun k => ?_, rfl⟩
  · show E.tq x = (![E.mx, kc] : Fin 2 → ℕ) (if E.tq x = kc then 1 else 0)
    rcases htq2 x hx with h | h
    · have : E.tq x ≠ kc := by rw [h]; exact fun h' => hne h'.symm
      rw [if_neg this, h]; rfl
    · rw [if_pos h, h]; rfl
  · have hsum1 : ∑ x ∈ range E.W, (if E.tq x = kc then 1 else 0) = H := by
      rw [← Finset.card_filter]; exact hHdef
    have hall : ∑ x ∈ range E.W, ((if E.tq x = kc then 1 else 0) + (if ¬ E.tq x = kc then 1 else 0)) = E.W := by
      rw [show ∑ x ∈ range E.W, ((if E.tq x = kc then 1 else 0) + (if ¬ E.tq x = kc then 1 else 0)) =
          ∑ x ∈ range E.W, 1 from Finset.sum_congr rfl (fun x _ => by by_cases hx : E.tq x = kc <;> simp [hx])]
      simp
    rw [Finset.sum_add_distrib, hsum1] at hall
    rw [Finset.card_filter]
    fin_cases k
    · refine Eq.trans (Finset.sum_congr rfl (fun x _ => ?_)) (show ∑ x ∈ range E.W,
          (if ¬ E.tq x = kc then 1 else 0) = _ by
            show _ = E.W - H
            omega)
      split_ifs <;> simp_all [Fin.ext_iff] <;> first | rfl | decide | (intro h; have := congrArg Fin.val h; simp at this)
    · refine Eq.trans (Finset.sum_congr rfl (fun x _ => ?_)) (show ∑ x ∈ range E.W,
          (if E.tq x = kc then 1 else 0) = _ by
            show _ = H
            exact hsum1)
      split_ifs <;> simp_all [Fin.ext_iff] <;> first | rfl | decide | (intro h; have := congrArg Fin.val h; simp at this)

end Eng

end
end PowerSaving.RAM
end OAI

#print axioms OAI.PowerSaving.RAM.Eng.bridge_twoTarget
