/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.AllEdges.Pairs
public import Submission.ThreeSumApsp.AllEdges.Uniform
public import Submission.ThreeSumApsp.RunningTimes.Sec3.Theorem22

/-!
# APSP from all-edges Exact Triangle

All pairs from all-edges Exact Triangle (`isHost_pa`), the (min,+)-product from all pairs
(`isHost_mp`), APSP by repeated squaring (`claim_apspFromMinPlus`).  From a time
`K s^{3−δ} (log s + 1)^e (1 + log u)²` for all-edges Exact Triangle this gives APSP in
`O(n^{3−δ} (log n)^{O(1)})` time on the word RAM (`apsp_polylog_of_aeUniform`): the whole saving
`δ` is kept.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.WordRam

/-- **All pairs from all-edges Exact Triangle**, in time `O(T(n, 6u) log u)`. -/
theorem pairs_solvedIn {T : ℕ → ℝ → ℝ} (hT : SolvedIn aeTask T)
    (hsq : ∀ (n : ℕ) (u : ℝ), 1 ≤ n → (n : ℝ) ^ 2 ≤ T n u) :
    SolvedIn pairsTask fun n u => 6000 * (T n (6 * u) * logU u) := by
  refine isHost_pa.solvedIn hT fun Tn hTn n U u hn hU hu => ?_
  have h6 : (Tn n (6 * U) : ℝ) ≤ T n (6 * u) :=
    hTn n (6 * U) (6 * u) hn (by omega) (by push_cast; linarith)
  have hL := ntLevels_le hU hu
  have hX := hsq n (6 * u) hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog := log_two_le_logU u
  have hl2 : (0.69 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hL0 : (0 : ℝ) ≤ ntLevels U := Nat.cast_nonneg _
  set X := T n (6 * u)
  set lg := logU u
  have hnn : (n : ℝ) * n ≤ X := by nlinarith
  have hX1 : 1 ≤ X := by nlinarith
  simp only [paTime]
  push_cast
  -- `250 n² + 400 ≤ 650 X ≤ 943 X lg` and `L (250 n² + 200 + 2 Tn) ≤ 10 lg · 452 X`
  have h1 : (250 * ((n : ℝ) * n) + 400) ≤ 943 * (X * lg) := by nlinarith
  have h2 : (ntLevels U : ℝ) * (250 * ((n : ℝ) * n) + 200 + 2 * (Tn n (6 * U) : ℝ)) ≤
      (10 * lg) * (452 * X) :=
    mul_le_mul hL (by nlinarith) (by positivity) (by linarith)
  nlinarith

/-- **The (min,+)-product from all-edges Exact Triangle**, in time `O(T(n, 36u) log² u)`. -/
theorem mp_solvedIn {T : ℕ → ℝ → ℝ} (hT : SolvedIn aeTask T)
    (hsq : ∀ (n : ℕ) (u : ℝ), 1 ≤ n → (n : ℝ) ^ 2 ≤ T n u) :
    ∃ C : ℝ, 0 ≤ C ∧ SolvedIn mpTask fun n u =>
      C * (6000 * (T n (6 * (6 * u)) * logU (6 * u)) * logU u) := by
  obtain ⟨C₃, hC₃, hmp⟩ := MinPlusFromNeg.mpTime_dominated
  refine ⟨C₃, hC₃, isHost_mp.solvedIn (pairs_solvedIn hT hsq) fun Tn hTn n U u hn hU hu =>
    hmp ⟨_, Tn, n, U, u⟩ ⟨⟨hTn, hn, hU, hu⟩, fun u' => ?_⟩⟩
  have hX := hsq n (6 * u') hn
  have hlog := log_two_le_logU u'
  have hl2 : (0.69 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  nlinarith [sq_nonneg (n : ℝ)]

/-- `(⌈log₂ n⌉ + 1) = O(log n)`, as an eventual bound. -/
private theorem isPowPolylog_clog : IsPowPolylog (fun n : ℕ => (Nat.clog 2 n : ℝ) + 1) 0 := by
  obtain ⟨C, hC, h⟩ := dominated_clog_add_one_log 2
  refine (isPowPolylog_log.const_mul C).mono_left_of_nonneg
    (.of_forall fun n => by positivity) ?_
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  have := h n hn
  have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  exact this

/-- **APSP from all-edges Exact Triangle**: with exponent `3 − δ` for all-edges Exact Triangle,
APSP takes `O(n^{3−δ} (log n)^{O(1)})` time on the word RAM. -/
theorem apsp_polylog_of_aeUniform {δ : ℝ} {e : ℕ} (hδ : δ ≤ 1)
    (hu : Claim.ExactTriangleUniform aeModel δ e) :
    SolvedInPolylogTime EndStatement.APSP (3 - δ) := by
  obtain ⟨K, hK, hex⟩ := hu
  have hgood := goodTime_uniformTime e hK hδ
  have hsq : ∀ (n : ℕ) (u : ℝ), 1 ≤ n → (n : ℝ) ^ 2 ≤ uniformTime K δ e n u := fun n u hn =>
    (le_mul_of_one_le_right (by positivity) (one_le_one_add_logU u)).trans (hgood.1 n u hn)
  obtain ⟨C, hC, hmp⟩ := mp_solvedIn hex hsq
  obtain ⟨ca, C₀, hca, hap⟩ := claim_apspFromMinPlus
  refine FromClaims.solvedInPolylogTime_of_claim realized_apsp fun κ hκ => ⟨_, hap _ hmp, ?_⟩
  -- every factor is of a known class along `u = n^κ`
  have hκ1 : (0 : ℝ) ≤ κ + 1 := by linarith
  have hmag : ∀ c : ℝ, 1 ≤ c → IsPowPolylog (fun n : ℕ => logU (c * (n : ℝ) ^ (κ + 1))) 0 :=
    fun c hc => isPowPolylog_logU_mul_rpow hc hκ1
  have huT : ∀ c : ℝ, 1 ≤ c →
      IsPowPolylog (fun n : ℕ => uniformTime K δ e n (c * (n : ℝ) ^ (κ + 1))) (3 - δ) :=
    fun c hc => (((isPowPolylog_rpow_mul_log_add_one_pow (3 - δ) e).mul
      (((isPowPolylog_const 1).add (hmag c hc)).pow 2)).const_mul K).mono
        (le_of_eq (by push_cast; ring))
  have h36 : (1 : ℝ) ≤ 6 * (6 * ca) := by linarith
  have h6 : (1 : ℝ) ≤ 6 * ca := by linarith
  have hprod : IsPowPolylog (fun n : ℕ => C * (6000 * (uniformTime K δ e n
      (6 * (6 * ca) * (n : ℝ) ^ (κ + 1)) * logU (6 * ca * (n : ℝ) ^ (κ + 1))) *
        logU (ca * (n : ℝ) ^ (κ + 1)))) (3 - δ) :=
    ((((huT _ h36).mul (hmag _ h6)).const_mul 6000).mul (hmag _ hca)).const_mul C |>.mono
      (le_of_eq (by ring))
  have hwrite : IsPowPolylog (fun n : ℕ => C₀ * ((n : ℝ) ^ 2 *
      (1 + logU (ca * (n : ℝ) ^ (κ + 1))))) (3 - δ) :=
    (((isBigOPow_natCast_pow 2).isPowPolylog.mul ((isPowPolylog_const 1).add (hmag _ hca))).const_mul
      C₀).mono (by push_cast; linarith)
  have htotal := (isPowPolylog_clog.mul (hprod.add hwrite)).mono (b := 3 - δ) (by linarith)
  refine htotal.upperPowPolylog.mono_left (Filter.eventually_atTop.2 ⟨1, fun n hn => le_of_eq ?_⟩)
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hpow : (n : ℝ) * (n : ℝ) ^ κ = (n : ℝ) ^ (κ + 1) := by
    rw [Real.rpow_add_one hn0.ne', mul_comm]
  simp only [← mul_assoc, hpow]

end Light.Sec3
