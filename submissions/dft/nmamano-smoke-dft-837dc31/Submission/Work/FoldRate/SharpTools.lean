import Submission.Work.FoldRate.RankTools

/-!
# (key: fold-rate) Sharpness for every table, in the notation of the rate modules

* `spare_T_ge_one`   an idle role costs at least one full role, written with `BlockAccounting.T`;
* `table_block_fails`  if `W ≤ moment u z U` then for ALL `K G p : ℕ` the table of `K` copies
                     of `G` units and `p` idle roles has moment at least its number of live
                     roles: the criterion of the block engine fails whatever the table;
* `table_rank_fails`   per-rank companion: if `D ≤ W (u - u^z)` then
                     `K G D ≤ (K G W + p) (u - u^z)`, i.e. `tally / 2^a ≥ u^z` for every table.

Imports only Mathlib (through `Work.FoldRate.RankTools`).  No `sorry`.
-/

namespace OAI
namespace PowerSaving
namespace FoldRate
open BlockAccounting

lemma spare_T_ge_one (u : ℕ) (hu : 2 ≤ u) (z : ℝ) (hz1 : z ≤ 1) :
    1 ≤ T u z (u - 1) 1 + T u z 1 1 := by
  have h := spare_ge_one u hu z hz1
  have h1 : T u z (u - 1) 1 = (((u - 1 : ℕ):ℝ)/(u:ℝ))^z := by
    unfold T
    rw [Nat.cast_one, one_mul]
  have h2 : T u z 1 1 = (((1:ℕ):ℝ)/(u:ℝ))^z := by
    unfold T
    rw [Nat.cast_one, one_mul]
  rw [h1, h2]
  exact h

/-- **whole-block: no table helps.** -/
theorem table_block_fails (u W : ℕ) (hu : 2 ≤ u) (z : ℝ) (hz1 : z ≤ 1) (U : List (ℕ × ℕ))
    (hM : (W:ℝ) ≤ moment u z U) (K G p : ℕ) :
    (K:ℝ) * ((G:ℝ) * (W:ℝ)) + (p:ℝ)
      ≤ (K:ℝ) * ((G:ℝ) * moment u z U) + (p:ℝ) * (T u z (u - 1) 1 + T u z 1 1) :=
  block_fails _ _ _ _ _ _ (Nat.cast_nonneg K) (Nat.cast_nonneg G) (Nat.cast_nonneg p)
    (spare_T_ge_one u hu z hz1) hM

/-- **per-rank: no table helps.** -/
theorem table_rank_fails (u W D : ℕ) (hu : 1 ≤ u) (z : ℝ) (hz1 : z ≤ 1)
    (hD : (D:ℝ) ≤ (W:ℝ) * ((u:ℝ) - (u:ℝ)^z)) (K G p : ℕ) :
    (K:ℝ) * ((G:ℝ) * (D:ℝ)) ≤ ((K:ℝ) * ((G:ℝ) * (W:ℝ)) + (p:ℝ)) * ((u:ℝ) - (u:ℝ)^z) := by
  have hu1 : (1:ℝ) ≤ (u:ℝ) := by exact_mod_cast hu
  have hX : (0:ℝ) ≤ (u:ℝ) - (u:ℝ)^z := by
    have h := Real.rpow_le_rpow_of_exponent_le hu1 hz1
    rw [Real.rpow_one] at h
    linarith
  exact rank_fails _ _ _ _ _ _ (Nat.cast_nonneg K) (Nat.cast_nonneg G) (Nat.cast_nonneg p) hX hD

end FoldRate
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.FoldRate.rank_fact3
#print axioms OAI.PowerSaving.FoldRate.table_block_fails
#print axioms OAI.PowerSaving.FoldRate.table_rank_fails
