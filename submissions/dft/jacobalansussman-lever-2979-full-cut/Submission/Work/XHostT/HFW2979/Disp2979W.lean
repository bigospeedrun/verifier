import Submission.Work.XHostT.TGeomW

/-!
# (key: heads-first, warp) Two warp providers dispatched by a table: the glue the #2979 engine theorem needs

For two windowed providers `I0`, `I1 : GInvW H T Sl C Ok` (x-words' `PWG2979.ginvE` / `ginvB` after the field-for-field
map from `KLW.GInvEW`) and a dispatch table `D : Fin nR × Fin 9 → Fin 2` (x-tables' `D2979.disp`):
* `IcW D I0 I1`: call `(ρ, l)` runs `I0` if `D (ρ, l) = 0`, else `I1`;
* `hIcW`: one target-vector family (`I1.tv = I0.tv`, x-words' `tv_eq`), the `hIc` of the network;
* `IcW_cost`: with equal prices (x-words' `same_price`), every call costs `I0.cost`;
* `unitPriceTW_const`: then the unit price is `9 nR * I0.cost φ` plus the remaining climbs (`hcostT`);
* `resIcW_IcW`: with equal entrance dimensions, every call's residual is `I0`'s (so `hfit` and `hpos` are statements
  about one provider and the table).
Written by x-inst (wht45/lever2979, 19 Oct 2026); prepared with assistance from Claude.  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace OAI
namespace PowerSaving
namespace XHostTW
namespace D2979W
open Binary Matrix Finset RAM SS CB RF BR GF GX BC B401 XHost XHostR XHostD XHostT
noncomputable section

variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C] {nR : ℕ}
variable {Ok : ∀ {β : Type} [Fintype β] [DecidableEq β], GWin H β → Prop}

/-- the per-call providers of a two-provider dispatch table. -/
def IcW (D : Fin nR × Fin 9 → Fin 2) (I0 I1 : GInvW H T Sl C Ok) : Fin nR → Fin 9 → GInvW H T Sl C Ok :=
  fun ρ l => if (D (ρ, l)).val = 0 then I0 else I1

theorem hIcW (D : Fin nR × Fin 9 → Fin 2) (I0 I1 : GInvW H T Sl C Ok) (h : I1.tv = I0.tv) :
    ∀ ρ l, (IcW D I0 I1 ρ l).tv = I0.tv := by
  intro ρ l
  unfold IcW
  split_ifs
  · rfl
  · exact h

theorem IcW_cost (D : Fin nR × Fin 9 → Fin 2) (I0 I1 : GInvW H T Sl C Ok) (hc : ∀ φ, I1.cost φ = I0.cost φ) :
    ∀ ρ l φ, (IcW D I0 I1 ρ l).cost φ = I0.cost φ := by
  intro ρ l φ
  unfold IcW
  split_ifs
  · rfl
  · exact hc φ

/-- **the unit price when every call costs the same**: `9 nR` calls plus the remaining climbs. -/
theorem unitPriceTW_const (Ic : Fin nR → Fin 9 → GInvW H T Sl C Ok) (S : HostSchedT nR Sl T)
    (c : (ℕ → ℝ) → ℝ) (hc : ∀ ρ l φ, (Ic ρ l).cost φ = c φ) (φ : ℕ → ℝ) :
    unitPriceTW Ic S φ = ((9 * nR : ℕ) : ℝ) * c φ + ∑ ρ : Fin nR, ∑ c' : Fin 9, hcostT S ρ c' φ := by
  unfold unitPriceTW
  simp only [hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

theorem resIcW_IcW (D : Fin nR × Fin 9 → Fin 2) (I0 I1 : GInvW H T Sl C Ok)
    (he : ∀ q, (I1.ent q).dim = (I0.ent q).dim) (ρ : Fin nR) (l : Fin 9) (q : Sl) :
    resIcW (IcW D I0 I1) ρ l q = Fintype.card H - (I0.ent q).dim := by
  unfold resIcW IcW
  split_ifs
  · rfl
  · rw [he q]

end
end D2979W
end XHostTW
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.XHostTW.D2979W.hIcW
#print axioms OAI.PowerSaving.XHostTW.D2979W.IcW_cost
#print axioms OAI.PowerSaving.XHostTW.D2979W.unitPriceTW_const
#print axioms OAI.PowerSaving.XHostTW.D2979W.resIcW_IcW
