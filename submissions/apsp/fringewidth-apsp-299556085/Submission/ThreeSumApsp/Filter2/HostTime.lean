/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Filter2.HostMain

/-!
# The time of the filtering host

`filterTime_le`: the host calls the oracle `roundsOf n * (rOf n * QOf n + 2)` times, each within
`supTo To n U`; besides, it spends `1000 (n + 1)² (Q + 1) (m + Q + 1)` steps per step of a round and
once for the final pass, `cFin n U * tScan (sOf n)` steps for the final scans (`0` under the guard,
`m n² (24 s + 35)` without it), and `tPrelude n U` steps for the parameters, the sieve, the pool and
the marks.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Filter2

open ThreeSumApsp.Spec Light.Sec3

/-- The time of the parameters, the sieve, the pool and the marks. -/
def tPrelude (n U : ℕ) : ℕ :=
  tParams n U + sieveTime (2 * RR n - 1) + tPoolFilter (2 * RR n) + fillTime (LL n) +
    fillTime (n * n) + 300

/-- The work of one step of a round, apart from the calls of the oracle (a bound). -/
def stepWork (n : ℕ) : ℕ := 1000 * ((n + 1) ^ 2 * (QOf n + 1) * (mOf n + QOf n + 1))

theorem stepWork_parts (n : ℕ) :
    QOf n * (tAggr (n * n) (mOf n) + 40) + tCert (n * n) (QOf n) + tArgmin (n * n) (QOf n) +
        copyTime (n * n) + 124 ≤ stepWork n ∧
      tAggr (n * n) (mOf n) + tFilterAct (LL n) + 240 ≤ stepWork n ∧
      tFinal (n * n) (mOf n) (sOf n) 0 + 30 ≤ stepWork n := by
  have e1 : QOf n * (tAggr (n * n) (mOf n) + 40) + tCert (n * n) (QOf n) +
      tArgmin (n * n) (QOf n) + copyTime (n * n) + 124 =
      30 * (QOf n * (n * n) * mOf n) + 90 * (QOf n * (n * n)) + 80 * QOf n + 46 * (n * n) + 150 := by
    simp only [tAggr, tCert, tArgmin, copyTime]; ring
  have e2 : tAggr (n * n) (mOf n) + tFilterAct (LL n) + 240 =
      50 * (n * n * mOf n) + 30 * (n * n) + 260 := by
    simp only [tAggr, tFilterAct, LL]; ring
  have e3 : tFinal (n * n) (mOf n) (sOf n) 0 + 30 = 60 * (n * n * mOf n) + 60 * (n * n) + 40 := by
    simp only [tFinal]; ring
  rw [e1, e2, e3]
  unfold stepWork
  have hN : n * n ≤ (n + 1) ^ 2 := by
    calc n * n ≤ (n + 1) * (n + 1) := Nat.mul_le_mul (by omega) (by omega)
      _ = (n + 1) ^ 2 := by ring
  have h1 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  generalize QOf n = Q
  generalize mOf n = m
  generalize n * n = N at *
  generalize (n + 1) ^ 2 = N1 at *
  have hA1 : N1 ≤ N1 * (Q + 1) * (m + Q + 1) := by
    calc N1 = N1 * 1 * 1 := by ring
      _ ≤ N1 * (Q + 1) * (m + Q + 1) := Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have hQNm : Q * N * m ≤ N1 * (Q + 1) * (m + Q + 1) := by
    calc Q * N * m = N * Q * m := by ring
      _ ≤ N1 * (Q + 1) * (m + Q + 1) := Nat.mul_le_mul (Nat.mul_le_mul hN (by omega)) (by omega)
  have hQN : Q * N ≤ N1 * (Q + 1) * (m + Q + 1) := by
    calc Q * N = N * Q * 1 := by ring
      _ ≤ N1 * (Q + 1) * (m + Q + 1) := Nat.mul_le_mul (Nat.mul_le_mul hN (by omega)) (by omega)
  have hNm : N * m ≤ N1 * (Q + 1) * (m + Q + 1) := by
    calc N * m = N * 1 * m := by ring
      _ ≤ N1 * (Q + 1) * (m + Q + 1) := Nat.mul_le_mul (Nat.mul_le_mul hN (by omega)) (by omega)
  have hQ : Q ≤ N1 * (Q + 1) * (m + Q + 1) := by
    calc Q = 1 * 1 * Q := by ring
      _ ≤ N1 * (Q + 1) * (m + Q + 1) := Nat.mul_le_mul (Nat.mul_le_mul h1 (by omega)) (by omega)
  have e4 : N * m = N * m := rfl
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- **The time of the host**, split into the calls of the oracle and the rest. -/
theorem filterTime_le (To : List ℕ → ℕ) (n U : ℕ) :
    filterTime To n U ≤ roundsOf n * (rOf n * QOf n + 2) * supTo To n U +
      (roundsOf n * (rOf n + 1) + 1) * stepWork n + cFin n U * tScan (sOf n) + tPrelude n U := by
  obtain ⟨h1, h2, h3⟩ := stepWork_parts n
  have hX : tStep To n U + 58 ≤ QOf n * supTo To n U + stepWork n := by
    have e : tStep To n U + 58 = QOf n * supTo To n U + (QOf n * (tAggr (n * n) (mOf n) + 40) +
        tCert (n * n) (QOf n) + tArgmin (n * n) (QOf n) + copyTime (n * n) + 118) := by
      unfold tStep; ring
    omega
  have hR : tRound To n U + 30 ≤
      2 * supTo To n U + stepWork n + rOf n * (QOf n * supTo To n U + stepWork n) := by
    have h := Nat.mul_le_mul_left (rOf n) hX
    have e : tRound To n U + 30 = 2 * supTo To n U + (tAggr (n * n) (mOf n) + tFilterAct (LL n) +
        230) + rOf n * (tStep To n U + 58) := by
      unfold tRound; ring
    omega
  have hF : tFinal (n * n) (mOf n) (sOf n) (cFin n U) + 30 ≤
      stepWork n + cFin n U * tScan (sOf n) := by
    unfold tFinal at h3 ⊢; omega
  have hC := Nat.mul_le_mul_left (roundsOf n) hR
  have e : roundsOf n * (2 * supTo To n U + stepWork n + rOf n * (QOf n * supTo To n U +
      stepWork n)) = roundsOf n * (rOf n * QOf n + 2) * supTo To n U +
        roundsOf n * (rOf n + 1) * stepWork n := by ring
  have e' : (roundsOf n * (rOf n + 1) + 1) * stepWork n =
      roundsOf n * (rOf n + 1) * stepWork n + stepWork n := by ring
  unfold filterTime tTop tCore tPrelude
  omega

/-- Without the guard, the final scans cost `m n² (24 s + 35)`; with it, nothing. -/
theorem cFin_tScan (n U : ℕ) :
    cFin n U * tScan (sOf n) = if Guard n U then 0 else LL n * (24 * sOf n + 35) := by
  unfold cFin tScan; split_ifs <;> simp


/-- A bound on the time of the parameters, the sieve, the pool and the marks. -/
theorem tPrelude_le (n U : ℕ) :
    tPrelude n U ≤ 13 * LL n + 1000 * ((n + 1) ^ 2 + (RR n + 1) ^ 2) + 28 * Nat.log 2 (3 * U) := by
  have hk : kOf n ≤ n := Nat.size_le.2 Nat.lt_two_pow_self
  have hl : ellOf n < RR n := Nat.lt_two_pow_self
  have hlogn : Nat.log 2 n ≤ n := Nat.log_le_self 2 n
  have hsk : Nat.sqrt (kOf n) ≤ kOf n := Nat.sqrt_le_self _
  have hsl : Nat.sqrt (ellOf n) ≤ ellOf n := Nat.sqrt_le_self _
  have hb : bOf n ≤ RR n * RR n := by
    unfold bOf
    exact Nat.mul_le_mul hl.le (by omega)
  have hs : sOf n ≤ 2 * n + 1 := sOf_le_succ n
  have hlogs : Nat.log 2 (sOf n) ≤ sOf n := Nat.log_le_self 2 _
  have hcK : cKOf n ≤ sOf n := Nat.size_le.2 Nat.lt_two_pow_self
  have he : 336175 * kOf n / 10 ^ 7 ≤ kOf n := by
    rw [Nat.div_le_iff_le_mul_add_pred (by norm_num)]; omega
  have hB : BOf U ≤ Nat.log 2 (3 * U) + 1 := by
    unfold BOf
    rcases Nat.eq_zero_or_pos U with rfl | hU
    · simp
    · rw [size_eq_log (by omega)]
  have d1 := Nat.div_le_self (bOf n) 2
  have d2 := Nat.div_le_self (3 * kOf n) (dOf n)
  have d3 := Nat.div_le_self (n + sOf n - 1) (sOf n)
  have d4 := Nat.div_le_self (cKOf n + bOf n) (ellOf n)
  have d5 := Nat.div_le_self (BOf U - 1) (ellOf n)
  have hm : 2 * RR n - 1 ≤ 2 * RR n := Nat.sub_le _ _
  have hlogm : Nat.log 2 (2 * RR n - 1) ≤ 2 * RR n := (Nat.log_le_self 2 _).trans hm
  have hsv : sieveTime (2 * RR n - 1) ≤ 15 * (2 * RR n) * (2 * RR n + 5) + 35 := by
    unfold sieveTime
    have := Nat.mul_le_mul hm (Nat.add_le_add_right hlogm 5)
    have e : 15 * (2 * RR n - 1) * (Nat.log 2 (2 * RR n - 1) + 5) =
        15 * ((2 * RR n - 1) * (Nat.log 2 (2 * RR n - 1) + 5)) := by ring
    have e' : 15 * (2 * RR n) * (2 * RR n + 5) = 15 * (2 * RR n * (2 * RR n + 5)) := by ring
    omega
  have e1 : 15 * (2 * RR n) * (2 * RR n + 5) = 60 * (RR n * RR n) + 150 * RR n := by ring
  have e2 : (n + 1) ^ 2 = n * n + 2 * n + 1 := by ring
  have e3 : (RR n + 1) ^ 2 = RR n * RR n + 2 * RR n + 1 := by ring
  unfold tPrelude tParams tDiv tPow2 tPoolFilter
  simp only [log2Time, sqrtTime, fillTime]
  omega

end Light.Filter2
