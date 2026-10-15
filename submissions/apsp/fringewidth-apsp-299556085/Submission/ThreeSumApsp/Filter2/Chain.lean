/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.AllEdges.Chain
public import Submission.ThreeSumApsp.Statements.Exponents

/-!
# APSP from all-edges Exact Triangle, for an arbitrary time bound

`apsp_of_ae` generalizes `Light.Sec3.apsp_polylog_of_aeUniform`: from a solver of all-edges Exact
Triangle in time `T`, whose growth along `u = c n^{κ+1}` is `O(n^a (log n)^{O(1)})`, APSP takes
`O(n^a (log n)^{O(1)})` time on the word RAM.  `apsp_solvedInTime_299556085` is the final step to the
end statement with exponent `2.99556085`.
-/

@[expose] public section

namespace Light.Filter2

open ThreeSumApsp ThreeSumApsp.WordRam Light.Sec3

/-- `(⌈log₂ n⌉ + 1) = O(log n)`, as an eventual bound. -/
private theorem isPowPolylog_clog' : IsPowPolylog (fun n : ℕ => (Nat.clog 2 n : ℝ) + 1) 0 := by
  obtain ⟨C, hC, h⟩ := dominated_clog_add_one_log 2
  refine (isPowPolylog_log.const_mul C).mono_left_of_nonneg
    (.of_forall fun n => by positivity) ?_
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  exact h n hn

/-- An eventual bound `0 ≤ f n ≤ C n^a` gives `f = Õ(n^a)`. -/
theorem isPowPolylog_of_eventually_le {f : ℕ → ℝ} {a C : ℝ}
    (h : ∀ᶠ n : ℕ in Filter.atTop, 0 ≤ f n ∧ f n ≤ C * (n : ℝ) ^ a) : IsPowPolylog f a :=
  ((isPowPolylog_rpow a).const_mul C).mono_left_of_nonneg (h.mono fun _ h => h.1)
    (h.mono fun _ h => h.2)

/-- **APSP from all-edges Exact Triangle in time `T`**: if `T n u ≥ n²` and `T` grows like
`n^a (log n)^{O(1)}` along `u = c n^{κ+1}` (for all `c ≥ 1`, `κ ≥ 0`), with `a ≥ 2`, then APSP takes
`O(n^a (log n)^{O(1)})` time on the word RAM. -/
theorem apsp_of_ae {T : ℕ → ℝ → ℝ} {a : ℝ} (ha : 2 ≤ a) (hT : SolvedIn aeTask T)
    (hsq : ∀ (n : ℕ) (u : ℝ), 1 ≤ n → (n : ℝ) ^ 2 ≤ T n u)
    (hgrow : ∀ c κ : ℝ, 1 ≤ c → 0 ≤ κ →
      IsPowPolylog (fun n : ℕ => T n (c * (n : ℝ) ^ (κ + 1))) a) :
    SolvedInPolylogTime EndStatement.APSP a := by
  obtain ⟨C, hC, hmp⟩ := mp_solvedIn hT hsq
  obtain ⟨ca, C₀, hca, hap⟩ := claim_apspFromMinPlus
  refine FromClaims.solvedInPolylogTime_of_claim realized_apsp fun κ hκ => ⟨_, hap _ hmp, ?_⟩
  have hκ1 : (0 : ℝ) ≤ κ + 1 := by linarith
  have hmag : ∀ c : ℝ, 1 ≤ c → IsPowPolylog (fun n : ℕ => logU (c * (n : ℝ) ^ (κ + 1))) 0 :=
    fun c hc => isPowPolylog_logU_mul_rpow hc hκ1
  have h36 : (1 : ℝ) ≤ 6 * (6 * ca) := by linarith
  have h6 : (1 : ℝ) ≤ 6 * ca := by linarith
  have hprod : IsPowPolylog (fun n : ℕ => C * (6000 * (T n
      (6 * (6 * ca) * (n : ℝ) ^ (κ + 1)) * logU (6 * ca * (n : ℝ) ^ (κ + 1))) *
        logU (ca * (n : ℝ) ^ (κ + 1)))) a :=
    ((((hgrow _ κ h36 hκ).mul (hmag _ h6)).const_mul 6000).mul (hmag _ hca)).const_mul C |>.mono
      (le_of_eq (by ring))
  have hwrite : IsPowPolylog (fun n : ℕ => C₀ * ((n : ℝ) ^ 2 *
      (1 + logU (ca * (n : ℝ) ^ (κ + 1))))) a :=
    (((isBigOPow_natCast_pow 2).isPowPolylog.mul ((isPowPolylog_const 1).add (hmag _ hca))).const_mul
      C₀).mono (by push_cast; linarith)
  have htotal := (isPowPolylog_clog'.mul (hprod.add hwrite)).mono (b := a) (by linarith)
  refine htotal.upperPowPolylog.mono_left (Filter.eventually_atTop.2 ⟨1, fun n hn => le_of_eq ?_⟩)
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hpow : (n : ℝ) * (n : ℝ) ^ κ = (n : ℝ) ^ (κ + 1) := by
    rw [Real.rpow_add_one hn0.ne', mul_comm]
  simp only [← mul_assoc, hpow]

/-- **The final step**: APSP in `O(n^a (log n)^{O(1)})` with `a < 2.99556085` is APSP in
`O(n^{2.99556085})`. -/
theorem apsp_solvedInTime_299556085 {a : ℝ} (h : SolvedInPolylogTime EndStatement.APSP a)
    (ha : a < 2.99556085) : EndStatement.APSP.SolvedInTime (2.99556085 : ℚ) :=
  (h.solvedInTime (a' := ((2.99556085 : ℚ) : ℝ)) (by push_cast; linarith)).endStatement rfl
    (by norm_num)

/-- The two steps together. -/
theorem apsp_299556085_of_ae {T : ℕ → ℝ → ℝ} {a : ℝ} (ha : 2 ≤ a) (ha' : a < 2.99556085)
    (hT : SolvedIn aeTask T) (hsq : ∀ (n : ℕ) (u : ℝ), 1 ≤ n → (n : ℝ) ^ 2 ≤ T n u)
    (hgrow : ∀ c κ : ℝ, 1 ≤ c → 0 ≤ κ →
      IsPowPolylog (fun n : ℕ => T n (c * (n : ℝ) ^ (κ + 1))) a) :
    EndStatement.APSP.SolvedInTime (2.99556085 : ℚ) :=
  apsp_solvedInTime_299556085 (apsp_of_ae ha hT hsq hgrow) ha'

end Light.Filter2
