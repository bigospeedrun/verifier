import Submission.Work.Mixed.Flow
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Mixed engine, cost part 4: polynomial counts against powers of two

(agent e-r3cost, round wht45/lever, 19 Oct 2026.)  Two facts used by the seam adapter's bill
(`Work.MixedCost.SeamCost`) and available to R2:

* `succ_pow_le_two_pow c`  : `∃ D, ∀ n, (n+1)^c ≤ D * 2^n`;
* `Rule.kmin_pow_G_le_succ` : `kmin^(G n) ≤ n + 1`;
* `Rule.Nsrc_poly_ex`     : `∃ A c, ∀ n, Nsrc n ≤ A * (n+1)^c` (the tree has polynomially many sources).
-/

namespace OAI.PowerSaving.MX

/-- A polynomial is at most a constant times `2^n`. -/
theorem succ_pow_le_two_pow (c : ℕ) : ∃ D : ℕ, ∀ n : ℕ, (n + 1) ^ c ≤ D * 2 ^ n := by
  have h0 := tendsto_pow_const_div_const_pow_of_one_lt c (by norm_num : (1:ℝ) < 2)
  have h1 : Filter.Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ c / 2 ^ (n + 1)) Filter.atTop
      (nhds 0) := h0.comp (Filter.tendsto_add_atTop_nat 1)
  obtain ⟨R, -, hR⟩ := cauchySeq_bdd h1.cauchySeq
  refine ⟨Nat.ceil (1 + 2 * R), fun n => ?_⟩
  have hd := hR n 0
  rw [Real.dist_eq] at hd
  have hu : ((n + 1 : ℕ) : ℝ) ^ c / 2 ^ (n + 1) < 1 / 2 + R := by
    have := (abs_lt.1 hd).2
    simp only [zero_add, Nat.cast_one, one_pow, pow_one] at this
    linarith
  have hp : (0 : ℝ) < 2 ^ (n + 1) := by positivity
  rw [div_lt_iff₀ hp] at hu
  have h2 : ((n + 1 : ℕ) : ℝ) ^ c ≤ (Nat.ceil (1 + 2 * R) : ℝ) * 2 ^ n := by
    have h3 : (1 / 2 + R) * 2 ^ (n + 1) = (1 + 2 * R) * 2 ^ n := by rw [pow_succ]; ring
    have h4 : (1 + 2 * R) * (2:ℝ) ^ n ≤ (Nat.ceil (1 + 2 * R) : ℝ) * 2 ^ n :=
      mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity)
    linarith
  exact_mod_cast h2

namespace Rule

variable (R : Rule)

lemma kmin_pow_G_le_succ (n : ℕ) : R.kmin ^ R.G n ≤ n + 1 := by
  by_cases h0 : R.G n = 0
  · rw [h0]; simp
  · have hP : R.m * R.kmin ^ R.G n ≤ n := Nat.findGreatest_of_ne_zero (P := fun g => R.m * R.kmin ^ g ≤ n) (n := n) (m := R.G n) rfl h0
    have hm := R.two_le_m
    have : R.kmin ^ R.G n ≤ R.m * R.kmin ^ R.G n := Nat.le_mul_of_pos_left _ (by omega)
    omega

/-- The tree has polynomially many sources. -/
theorem Nsrc_poly_ex : ∃ A c : ℕ, ∀ n, R.Nsrc n ≤ A * (n + 1) ^ c := by
  set Q := R.P + R.W + 1
  refine ⟨Q, Q, fun n => ?_⟩
  have h1 := R.Nsrc_le n
  have hQ : Q ≤ R.kmin ^ Q :=
    le_trans (Nat.lt_two_pow_self).le (Nat.pow_le_pow_left R.two_le_kmin _)
  have h2 : Q ^ R.G n ≤ (R.kmin ^ Q) ^ R.G n := Nat.pow_le_pow_left hQ _
  have h3 : (R.kmin ^ Q) ^ R.G n = (R.kmin ^ R.G n) ^ Q := by rw [← pow_mul, ← pow_mul, mul_comm]
  have h4 : (R.kmin ^ R.G n) ^ Q ≤ (n + 1) ^ Q := Nat.pow_le_pow_left (R.kmin_pow_G_le_succ n) _
  calc R.Nsrc n ≤ Q ^ (R.G n + 1) := h1
    _ = Q * Q ^ R.G n := by rw [pow_succ, mul_comm]
    _ ≤ Q * (n + 1) ^ Q := Nat.mul_le_mul_left _ (by rw [h3] at h2; exact le_trans h2 h4)

end Rule

end OAI.PowerSaving.MX

#print axioms OAI.PowerSaving.MX.succ_pow_le_two_pow
#print axioms OAI.PowerSaving.MX.Rule.Nsrc_poly_ex
