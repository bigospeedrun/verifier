import Submission.Work.Mixed.Prog.Merged1

/-!
# Mixed engine, top body part 3a: the consumption count, mathematics

(agent e-r3cost, round wht45/lever, 19 Oct 2026.)

* `ownSrc_length`  the number of source slots of a child class, counted on codes `u < W^(h+1)`
                   (`u / W` the child unit, `u` the parent code), without `Nat.nth`;
* `cons_zero`, `cons_succ_idx`  the subtree consumption by recursion on the height, over the block
                   letters by index (`rkI j`, `j < nB`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset GF MXR
noncomputable section

lemma length_filterMap_ite {β : Type*} (P : ℕ → Prop) [DecidablePred P] (f : ℕ → β) (N : ℕ) :
    ((List.range N).filterMap (fun t => if P t then some (f t) else none)).length = Nat.count P N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.filterMap_append, List.length_append, ih, Nat.count_succ]
    by_cases hp : P N <;> simp [hp]

lemma sum_map_getD {β : Type*} (L : List β) (z : β) (g : β → ℕ) :
    (L.map g).sum = ∑ j ∈ Finset.range L.length, g (L.getD j z) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.sum_cons, ih, List.length_cons, Finset.sum_range_succ']
    simp [add_comm]

lemma sum_map_range (N : ℕ) (f : ℕ → ℕ) : ((List.range N).map f).sum = ∑ j ∈ Finset.range N, f j := by
  induction N with
  | zero => simp
  | succ N ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

namespace Eng
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]
variable (E : Eng α ρ σ)

/-- The predicate counted on codes: child unit `u / W` in the child's region, parent code `u` out of the
parent's region. -/
def srcU (n h μ r u : ℕ) : Prop :=
  inRS E.W E.tq E.mx n h (μ * r) (u / E.W) ∧ ¬ inRS E.W E.tq E.mx n (h+1) μ u

instance (n h μ r : ℕ) : DecidablePred (E.srcU n h μ r) := fun u => by unfold srcU; infer_instance

/-- **Source slots of a child, counted on codes.** -/
theorem ownSrc_length (n h μ r : ℕ) :
    (E.ownSrc n h μ r).length = Nat.count (E.srcU n h μ r) (E.W^h * E.W) := by
  unfold ownSrc
  rw [length_filterMap_ite, Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
  have hW := E.W_pos
  refine Finset.card_bij (fun t _ => E.Uc n h (μ * r) (t / E.W) * E.W + t % E.W) ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_range] at ht ⊢
    obtain ⟨hlt, hsrc⟩ := ht
    have hp : t / E.W < E.NUc n h (μ * r) := (Nat.div_lt_iff_lt_mul hW).2 hlt
    have hU := U_spec hp
    have hmod : t % E.W < E.W := Nat.mod_lt _ hW
    have hdiv : (E.Uc n h (μ * r) (t / E.W) * E.W + t % E.W) / E.W = E.Uc n h (μ * r) (t / E.W) := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hW, Nat.div_eq_of_lt hmod, zero_add]
    refine ⟨?_, ?_, ?_⟩
    · calc E.Uc n h (μ * r) (t / E.W) * E.W + t % E.W < E.Uc n h (μ * r) (t / E.W) * E.W + E.W := by omega
        _ = (E.Uc n h (μ * r) (t / E.W) + 1) * E.W := by ring
        _ ≤ E.W^h * E.W := Nat.mul_le_mul_right _ hU.2.1
    · rw [hdiv]; exact hU.1
    · have : E.Uc n h (μ * r) (t / E.W) * E.W + t % E.W = E.parCode n h μ r t := by
        unfold parCode; ring
      rw [this]; exact hsrc.2
  · intro t1 ht1 t2 ht2 heq
    simp only [Finset.mem_filter, Finset.mem_range] at ht1 ht2
    have h1 : t1 / E.W < E.NUc n h (μ * r) := (Nat.div_lt_iff_lt_mul hW).2 ht1.1
    have h2 : t2 / E.W < E.NUc n h (μ * r) := (Nat.div_lt_iff_lt_mul hW).2 ht2.1
    have hm1 : t1 % E.W < E.W := Nat.mod_lt _ hW
    have hm2 : t2 % E.W < E.W := Nat.mod_lt _ hW
    have ediv := congrArg (· / E.W) heq
    have emod := congrArg (· % E.W) heq
    simp only [Nat.add_comm (E.Uc n h (μ * r) _ * E.W), Nat.add_mul_div_right _ _ hW,
      Nat.div_eq_of_lt hm1, Nat.div_eq_of_lt hm2, zero_add, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt hm1, Nat.mod_eq_of_lt hm2] at ediv emod
    have hU : t1 / E.W = t2 / E.W := by
      have e1 := PC_U h1
      have e2 := PC_U h2
      rw [← e1, ← e2]; exact congrArg _ ediv
    calc t1 = E.W * (t1 / E.W) + t1 % E.W := (Nat.div_add_mod t1 E.W).symm
      _ = E.W * (t2 / E.W) + t2 % E.W := by rw [hU, emod]
      _ = t2 := Nat.div_add_mod t2 E.W
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_range] at hu ⊢
    obtain ⟨hlt, hin, hout⟩ := hu
    have hu1 := PC_lt hin
    refine ⟨E.PCc n h (μ * r) (u / E.W) * E.W + u % E.W, ⟨?_, ?_, ?_⟩, ?_⟩
    · have hmod : u % E.W < E.W := Nat.mod_lt _ hW
      calc E.PCc n h (μ * r) (u / E.W) * E.W + u % E.W < E.PCc n h (μ * r) (u / E.W) * E.W + E.W := by omega
        _ = (E.PCc n h (μ * r) (u / E.W) + 1) * E.W := by ring
        _ ≤ E.NUc n h (μ * r) * E.W := Nat.mul_le_mul_right _ hu1
    · have hmod : u % E.W < E.W := Nat.mod_lt _ hW
      calc E.PCc n h (μ * r) (u / E.W) * E.W + u % E.W < E.PCc n h (μ * r) (u / E.W) * E.W + E.W := by omega
        _ = (E.PCc n h (μ * r) (u / E.W) + 1) * E.W := by ring
        _ ≤ E.NUc n h (μ * r) * E.W := Nat.mul_le_mul_right _ hu1
    · have hmod : u % E.W < E.W := Nat.mod_lt _ hW
      have hUP : E.Uc n h (μ * r) (E.PCc n h (μ * r) (u / E.W)) = u / E.W := U_PC hin
      unfold parCode
      rw [Nat.add_comm (E.PCc n h (μ * r) _ * E.W), Nat.add_mul_div_right _ _ hW, Nat.div_eq_of_lt hmod,
        zero_add, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hmod, hUP]
      rw [show u % E.W + E.W * (u / E.W) = u from Nat.mod_add_div u E.W]
      exact hout
    · have hmod : u % E.W < E.W := Nat.mod_lt _ hW
      have hUP : E.Uc n h (μ * r) (E.PCc n h (μ * r) (u / E.W)) = u / E.W := U_PC hin
      rw [Nat.add_comm (E.PCc n h (μ * r) _ * E.W), Nat.add_mul_div_right _ _ hW, Nat.div_eq_of_lt hmod,
        zero_add, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hmod, hUP]
      exact Nat.div_add_mod' u E.W

/-- The number of block letters and their ranks by index. -/
def nB : ℕ := (blockRanks E.wd).length
def rkI (j : ℕ) : ℕ := (blockRanks E.wd).getD j 0

lemma cons_zero (n μ : ℕ) : E.cons n 0 μ = 0 := by simp [cons, srcSizes]

/-- **The consumption of a subtree, by recursion on the height.** -/
theorem cons_succ_idx (n h μ : ℕ) :
    E.cons n (h+1) μ = ∑ j ∈ Finset.range E.nB,
      (Nat.count (E.srcU n h μ (E.rkI j)) (E.W^h * E.W) + E.cons n h (μ * E.rkI j)) := by
  unfold cons
  simp only [srcSizes, List.length_flatMap, List.length_append]
  rw [sum_map_getD (blockRanks E.wd) 0]
  unfold nB rkI
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [ownSrc_length]

end Eng

end
end PowerSaving.RAM
end OAI

#print axioms OAI.PowerSaving.RAM.Eng.ownSrc_length
#print axioms OAI.PowerSaving.RAM.Eng.cons_succ_idx
