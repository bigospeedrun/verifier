/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Filter2.HostTime
public import Submission.ThreeSumApsp.Filter2.Asymp
public import Submission.ThreeSumApsp.Filter2.Chain

/-!
# APSP in time `O(n^{2.99556085})` from an abstract counting oracle

The filtering host with block size `s = 2^{⌊σ k⌋}`, `σ = 0.0336175`, over any solver of the
counting oracle task whose time is at most `n^{2.99556082}` along `U ≤ c n^κ`, `p ≤ Pmax`, is a
solver of all-edges Exact Triangle in time `O(n^{2.99556083})` (`filterTime_bound`): the
`n^{o(1)}` oracle calls take `n^{2.99556082}` each, everything else is `O(n^{3 - σ + o(1)})`, and
the final scans vanish under the guard.  `apsp_299556085_of_ae` concludes.
-/

@[expose] public section

open Filter ThreeSumApsp

namespace Light.Filter2

open ThreeSumApsp.Spec Light.Sec3

theorem sq_succ_le {x : ℝ} (hx : 1 ≤ x) : (x + 1) ^ 2 ≤ 4 * x ^ 2 := by nlinarith

set_option maxHeartbeats 2000000 in
/-- **The time of the filtering host over a counting oracle of time `n^{2.99556082}`**: for every `c, κ`, it is
eventually at most `K n^{2.99556083}` along `U ≤ c n^κ`. -/
theorem filterTime_bound {To : List ℕ → ℕ}
    (hT : ∀ c κ : ℝ, ∀ᶠ n : ℕ in atTop, ∀ U : ℕ, (U : ℝ) ≤ c * (n : ℝ) ^ κ →
      ∀ p : ℕ, p ≤ PmaxOf n → (To [n, U, sOf n, p] : ℝ) ≤ (n : ℝ) ^ (2.99556082 : ℝ))
    (c κ : ℝ) : ∃ K : ℝ, ∀ᶠ n : ℕ in atTop, ∀ U : ℕ, (U : ℝ) ≤ c * (n : ℝ) ^ κ →
      (filterTime To n U : ℝ) ≤ K * (n : ℝ) ^ (2.99556083 : ℝ) := by
  set c' := max c 1 with hc'
  set κ' := max κ 0 with hκ'
  have hc'1 : 1 ≤ c' := le_max_right _ _
  have hκ'0 : 0 ≤ κ' := le_max_right _ _
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set K1 := Real.log (3 * c') / Real.log 2 with hK1
  set K2 := κ' / Real.log 2 with hK2
  have hK10 : 0 ≤ K1 := div_nonneg (Real.log_nonneg (by linarith)) hl2.le
  have hK20 : 0 ≤ K2 := div_nonneg hκ'0 hl2.le
  refine ⟨1 + 96000 + 52 + 8000 + 28 * K1 + 28 * K2, ?_⟩
  set η : ℝ := 0.00000001 with hη
  set σ : ℝ := 0.0336175 with hσ
  set a : ℝ := 2.99556083 with ha
  filter_upwards [hT c κ, calls_le_rpow (η := η) (by norm_num [hη]),
    QOf_le_rpow (η := η) (by norm_num [hη]), RR_le_rpow (η := η) (by norm_num [hη]),
    guard_eventually c κ, eventually_ge_atTop 1] with n hor hcalls hQ hRR hG hn U hU
  have hN1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < n := by linarith
  have hle : ∀ e : ℝ, e ≤ a → (n : ℝ) ^ e ≤ (n : ℝ) ^ a :=
    fun e he => Real.rpow_le_rpow_of_exponent_le hN1 he
  have hadd : ∀ e f : ℝ, (n : ℝ) ^ e * (n : ℝ) ^ f = (n : ℝ) ^ (e + f) :=
    fun e f => (Real.rpow_add hN0 e f).symm
  have hsq2 : (n : ℝ) ^ (2 : ℕ) = (n : ℝ) ^ (2 : ℝ) := by
    rw [← Real.rpow_natCast]; norm_num
  have hηpos : (1 : ℝ) ≤ (n : ℝ) ^ η := Real.one_le_rpow hN1 (by norm_num [hη])
  -- one oracle call
  have hsup : (supTo To n U : ℝ) ≤ (n : ℝ) ^ (2.99556082 : ℝ) := by
    obtain ⟨p, hp, heq⟩ := Finset.exists_mem_eq_sup (Finset.range (PmaxOf n + 1))
      ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩ (fun p => To [n, U, sOf n, p])
    have hpP : p ≤ PmaxOf n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hp)
    rw [supTo, heq]
    exact hor U hU p hpP
  -- the number of calls
  have hcalls' : ((roundsOf n * (rOf n * QOf n + 2) : ℕ) : ℝ) ≤ (n : ℝ) ^ η := by
    refine le_trans ?_ hcalls
    exact_mod_cast Nat.mul_le_mul_left _ (by nlinarith)
  have hR2 : ((roundsOf n * (rOf n + 1) + 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) ^ η := by
    have : roundsOf n * (rOf n + 1) ≤ roundsOf n * (rOf n * (QOf n + 1) + 2) :=
      Nat.mul_le_mul_left _ (by nlinarith)
    have h' : ((roundsOf n * (rOf n + 1) : ℕ) : ℝ) ≤ (n : ℝ) ^ η :=
      le_trans (by exact_mod_cast this) hcalls
    push_cast at h' ⊢
    linarith
  -- the number of blocks
  have hm : (mOf n : ℝ) ≤ 4 * (n : ℝ) ^ (1 - σ) := by
    have h1 : ((mOf n * sOf n : ℕ) : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by exact_mod_cast mOf_mul_sOf_le hn
    have h2 := rpow_le_two_mul_sOf n
    push_cast at h1
    have hσp : 0 < (n : ℝ) ^ σ := Real.rpow_pos_of_pos hN0 _
    have e : 4 * (n : ℝ) ^ (1 - σ) * (n : ℝ) ^ σ = 4 * n := by
      rw [mul_assoc, hadd]; norm_num
    have hm0 : (0 : ℝ) ≤ mOf n := Nat.cast_nonneg _
    refine le_of_mul_le_mul_right ?_ hσp
    rw [e]
    have : (mOf n : ℝ) * (n : ℝ) ^ σ ≤ (mOf n : ℝ) * (2 * sOf n) :=
      mul_le_mul_of_nonneg_left h2 hm0
    linarith
  have hQ1 : (QOf n : ℝ) + 1 ≤ 2 * (n : ℝ) ^ η := by linarith
  have hησ : (n : ℝ) ^ η ≤ (n : ℝ) ^ (1 - σ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num [hη, hσ])
  -- one step of a round
  have hstep : (stepWork n : ℝ) ≤ 48000 * (n : ℝ) ^ (3 - σ + η) := by
    unfold stepWork
    push_cast
    have h1 : ((n : ℝ) + 1) ^ 2 ≤ 4 * (n : ℝ) ^ (2 : ℝ) := by rw [← hsq2]; exact sq_succ_le hN1
    have h3 : (mOf n : ℝ) + QOf n + 1 ≤ 6 * (n : ℝ) ^ (1 - σ) := by linarith
    have e : (n : ℝ) ^ (3 - σ + η) = (n : ℝ) ^ (2 : ℝ) * (n : ℝ) ^ η * (n : ℝ) ^ (1 - σ) := by
      rw [hadd, hadd]; ring_nf
    rw [e]
    have hm0 : (0 : ℝ) ≤ mOf n := Nat.cast_nonneg _
    have hq0 : (0 : ℝ) ≤ QOf n := Nat.cast_nonneg _
    calc 1000 * (((n : ℝ) + 1) ^ 2 * ((QOf n : ℝ) + 1) * ((mOf n : ℝ) + QOf n + 1))
        ≤ 1000 * (4 * (n : ℝ) ^ (2 : ℝ) * (2 * (n : ℝ) ^ η) * (6 * (n : ℝ) ^ (1 - σ))) := by
          gcongr
      _ = _ := by ring
  -- the rest of the rounds
  have hrounds : ((roundsOf n * (rOf n + 1) + 1 : ℕ) : ℝ) * (stepWork n : ℝ) ≤
      96000 * (n : ℝ) ^ (3 - σ + 2 * η) := by
    calc _ ≤ 2 * (n : ℝ) ^ η * (48000 * (n : ℝ) ^ (3 - σ + η)) :=
          mul_le_mul hR2 hstep (Nat.cast_nonneg _) (by positivity)
      _ = 96000 * ((n : ℝ) ^ η * (n : ℝ) ^ (3 - σ + η)) := by ring
      _ = _ := by rw [hadd]; ring_nf
  -- the final scans vanish under the guard
  have hfin : cFin n U * tScan (sOf n) = 0 := by rw [cFin_tScan, if_pos (hG U hU)]
  -- the prelude
  have hlog : (Nat.log 2 (3 * U) : ℝ) ≤ K1 + K2 * n := by
    rcases Nat.eq_zero_or_pos (3 * U) with h0 | hpos
    · rw [h0]; simp; positivity
    · have h2 : ((2 ^ Nat.log 2 (3 * U) : ℕ) : ℝ) ≤ ((3 * U : ℕ) : ℝ) := by
        exact_mod_cast Nat.pow_log_le_self 2 hpos.ne'
      push_cast at h2
      have hUc : (U : ℝ) ≤ c' * (n : ℝ) ^ κ' := by
        calc (U : ℝ) ≤ c * (n : ℝ) ^ κ := hU
          _ ≤ c' * (n : ℝ) ^ κ :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hN0.le _)
          _ ≤ c' * (n : ℝ) ^ κ' := mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le hN1 (le_max_left _ _)) (by linarith)
      have hNk : 0 < (n : ℝ) ^ κ' := Real.rpow_pos_of_pos hN0 _
      have hlogn : Real.log n ≤ n := by
        have := Real.log_le_sub_one_of_pos hN0; linarith
      have key : (Nat.log 2 (3 * U) : ℝ) * Real.log 2 ≤ Real.log (3 * c') + κ' * n := by
        calc (Nat.log 2 (3 * U) : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ Nat.log 2 (3 * U)) := by
              rw [Real.log_pow]
          _ ≤ Real.log (3 * (c' * (n : ℝ) ^ κ')) :=
              Real.log_le_log (by positivity) (by linarith)
          _ = Real.log (3 * c') + κ' * Real.log n := by
              rw [← mul_assoc, Real.log_mul (by positivity) hNk.ne', Real.log_rpow hN0]
          _ ≤ _ := by gcongr
      have e : K1 + K2 * n = (Real.log (3 * c') + κ' * n) / Real.log 2 := by
        rw [hK1, hK2]; field_simp
      rw [e, le_div_iff₀ hl2]; exact key
  have hpre : (tPrelude n U : ℝ) ≤ 52 * (n : ℝ) ^ (3 - σ) + 4000 * (n : ℝ) ^ (2 : ℝ) +
      4000 * (n : ℝ) ^ (2 * η) + 28 * (K1 + K2 * n) := by
    have h := (Nat.cast_le (α := ℝ)).2 (tPrelude_le n U)
    push_cast at h
    unfold LL at h
    push_cast at h
    have hLL : (mOf n : ℝ) * ((n : ℝ) * n) ≤ 4 * (n : ℝ) ^ (3 - σ) := by
      have e : (n : ℝ) ^ (3 - σ) = (n : ℝ) ^ (1 - σ) * (n : ℝ) ^ (2 : ℝ) := by
        rw [hadd]; ring_nf
      rw [e, ← hsq2]
      have : (0 : ℝ) ≤ (n : ℝ) * n := by positivity
      nlinarith
    have hn2 : ((n : ℝ) + 1) ^ 2 ≤ 4 * (n : ℝ) ^ (2 : ℝ) := by rw [← hsq2]; exact sq_succ_le hN1
    have hR2' : ((RR n : ℝ) + 1) ^ 2 ≤ 4 * (n : ℝ) ^ (2 * η) := by
      have e : (n : ℝ) ^ (2 * η) = (n : ℝ) ^ η * (n : ℝ) ^ η := by rw [hadd]; ring_nf
      rw [e]
      have : (0 : ℝ) ≤ RR n := Nat.cast_nonneg _
      nlinarith
    linarith
  -- all together
  have htot := (Nat.cast_le (α := ℝ)).2 (filterTime_le To n U)
  rw [hfin] at htot
  push_cast at htot
  have h1 : ((roundsOf n : ℝ) * ((rOf n : ℝ) * QOf n + 2)) * (supTo To n U : ℝ) ≤
      (n : ℝ) ^ a := by
    have hc2 := hcalls'
    push_cast at hc2
    have := mul_le_mul hc2 hsup (Nat.cast_nonneg _) (by positivity)
    refine this.trans ?_
    rw [hadd]; exact hle (η + 2.99556082) (by norm_num [hη, ha])
  have h2 : ((roundsOf n : ℝ) * ((rOf n : ℝ) + 1) + 1) * (stepWork n : ℝ) ≤
      96000 * (n : ℝ) ^ a := by
    have := hrounds; push_cast at this
    refine this.trans ?_
    exact mul_le_mul_of_nonneg_left (hle (3 - σ + 2 * η) (by norm_num [hη, hσ, ha]))
      (by norm_num)
  have hX1 : (1 : ℝ) ≤ (n : ℝ) ^ a := Real.one_le_rpow hN1 (by norm_num [ha])
  have h3 : (n : ℝ) ^ (3 - σ) ≤ (n : ℝ) ^ a := hle _ (by norm_num [hσ, ha])
  have h4 : (n : ℝ) ^ (2 : ℝ) ≤ (n : ℝ) ^ a := hle _ (by norm_num [ha])
  have h5 : (n : ℝ) ^ (2 * η) ≤ (n : ℝ) ^ a := hle _ (by norm_num [hη, ha])
  have h6 : (n : ℝ) ≤ (n : ℝ) ^ a := by
    have := hle 1 (by norm_num [ha]); rwa [Real.rpow_one] at this
  have h7 : K1 + K2 * n ≤ (K1 + K2) * (n : ℝ) ^ a := by nlinarith
  nlinarith

/-- **APSP is solved in time `O(n^{2.99556085})`**, given a counting oracle that runs in time
`n^{2.99556082}` along `U ≤ c n^κ`, `p ≤ Pmax`. -/
theorem apsp_299556085_of_oracle {P : Program} {pO : ℕ} {To : List ℕ → ℕ} {needo : List ℕ → Need}
    (hsol : SolvesN oracleTask P pO To needo) (hpoly : PolyNeedN needo)
    (hT : ∀ c κ : ℝ, ∀ᶠ n : ℕ in atTop, ∀ U : ℕ, (U : ℝ) ≤ c * (n : ℝ) ^ κ →
      ∀ p : ℕ, p ≤ PmaxOf n → (To [n, U, sOf n, p] : ℝ) ≤ (n : ℝ) ^ (2.99556082 : ℝ)) :
    EndStatement.APSP.SolvedInTime (2.99556085 : ℚ) := by
  obtain ⟨R, p', hae⟩ := filter_host.1 _ _ _ _ hsol
  have hS := hae.solvedIn (filter_host.2 _ hpoly)
  have hnn : ∀ n u, 0 ≤ timeUpTo (filterTime To) n u := fun n u => by
    unfold timeUpTo; exact Nat.cast_nonneg _
  refine apsp_299556085_of_ae
    (T := fun n u => timeUpTo (filterTime To) n u + (n : ℝ) ^ 2)
    (a := 2.99556083) (by norm_num) (by norm_num)
    (hS.mono fun n u _ _ => by have := hnn n u; nlinarith)
    (fun n u _ => by have := hnn n u; linarith) (fun c κ hc hκ => ?_)
  obtain ⟨K, hK⟩ := filterTime_bound hT c (κ + 1)
  refine isPowPolylog_of_eventually_le (C := K + 1) ?_
  filter_upwards [hK, eventually_ge_atTop 1] with n hK hn
  have hN1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hu : 0 ≤ c * (n : ℝ) ^ (κ + 1) := by positivity
  have h1 : timeUpTo (filterTime To) n (c * (n : ℝ) ^ (κ + 1)) ≤
      K * (n : ℝ) ^ (2.99556083 : ℝ) :=
    timeUpTo_le fun U hU => hK U (by rwa [max_eq_left hu] at hU)
  have h2 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ (2.99556083 : ℝ) := by
    have := Real.rpow_le_rpow_of_exponent_le hN1 (show (2 : ℝ) ≤ 2.99556083 by norm_num)
    rwa [show (n : ℝ) ^ (2 : ℝ) = (n : ℝ) ^ 2 by rw [← Real.rpow_natCast]; norm_num] at this
  exact ⟨by have := hnn n (c * (n : ℝ) ^ (κ + 1)); positivity, by linarith⟩

end Light.Filter2
