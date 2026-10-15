/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Filter2.HostCore
public import Submission.ThreeSumApsp.Lang.Lib.Logs
public import Submission.ThreeSumApsp.Lang.Lib.Sqrt
public import Submission.ThreeSumApsp.Lang.Lib.Sieve
public import Submission.ThreeSumApsp.Lang.Lib.Copy

/-!
# The filtering host: the parameters

The first part of the host computes the parameters of the filtering from `n` and `U` and lays out
the memory above the free pointer (`params_spec`).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Filter2

open ThreeSumApsp.Spec Light.Sec3

variable {lim : Limits}

theorem size_eq_log {n : ℕ} (hn : 1 ≤ n) : Nat.size n = Nat.log 2 n + 1 := by
  refine le_antisymm (Nat.size_le.2 (Nat.lt_pow_succ_log_self (by norm_num) n)) ?_
  exact Nat.lt_size.2 (Nat.pow_log_le_self 2 (by omega))

/-- The bounds on the numbers that the computation of the parameters forms. -/
theorem param_words {n U : ℕ} (hn : 1 ≤ n) :
    2 * n + 2 ≤ filterWord n U ∧ 3 * kOf n + 4 ≤ filterWord n U ∧
    RR n + ellOf n + 1 ≤ filterWord n U ∧ 3 * ellOf n + 4 ≤ filterWord n U ∧
    bOf n + 2 + 1 ≤ filterWord n U ∧ 3 * kOf n + dOf n + 1 ≤ filterWord n U ∧
    336175 * kOf n + 10 ^ 7 + 1 ≤ filterWord n U ∧
    sOf n + 336175 * kOf n / 10 ^ 7 + 1 ≤ filterWord n U ∧
    n + sOf n - 1 + sOf n + 1 ≤ filterWord n U ∧ 2 * sOf n + 2 ≤ filterWord n U ∧
    cKOf n + bOf n + ellOf n + 1 ≤ filterWord n U ∧ 2 * (3 * U) + 2 ≤ filterWord n U ∧
    BOf U - 1 + ellOf n + 1 ≤ filterWord n U ∧ rOf n + roundsOf n + 1 ≤ filterWord n U := by
  obtain ⟨k1, k2, k3, k4⟩ := KW_ge n U
  have hK1 : 1 ≤ KW n U := by omega
  have hKK : KW n U ≤ KW n U * KW n U := Nat.le_mul_of_pos_left _ (by omega)
  have hn3 : n + 1 ≤ (n + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  have hk : kOf n ≤ n := Nat.size_le.2 Nat.lt_two_pow_self
  have hl : ellOf n < RR n := Nat.lt_two_pow_self
  have hs := sOf_le hn
  have hb : bOf n ≤ RR n * RR n := by
    unfold bOf
    exact Nat.mul_le_mul hl.le (by have := Nat.sqrt_le_self (ellOf n); omega)
  have hbK : bOf n ≤ KW n U * KW n U := hb.trans (Nat.mul_le_mul (by omega) (by omega))
  have hcK : cKOf n ≤ sOf n := Nat.size_le.2 Nat.lt_two_pow_self
  have hB : BOf U ≤ 3 * U := Nat.size_le.2 Nat.lt_two_pow_self
  have hd : dOf n ≤ bOf n := Nat.div_le_self _ _
  have he : 336175 * kOf n / 10 ^ 7 ≤ kOf n := by
    rw [Nat.div_le_iff_le_mul_add_pred (by norm_num)]; omega
  have hr : rOf n ≤ cKOf n + bOf n + 1 := by
    unfold rOf; have := Nat.div_le_self (cKOf n + bOf n) (ellOf n); omega
  have hro : roundsOf n ≤ 3 * kOf n + 1 := by
    unfold roundsOf; have := Nat.div_le_self (3 * kOf n) (dOf n); omega
  rw [filterWord_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega


/-! ## The computation of the parameters -/

/-- The parameters, from `n` (local 0), `U` (local 1) and the free pointer (local 6): 7 `k`, 8 `ℓ`,
9 `R`, 10 `b`, 11 `d`, 12 the number of rounds, 13 `s`, 14 `m`, 15 `c_K`, 16 `r`, 17 `B`, 18 `h`,
19 `N = n²`, and the places 20 `pl`, 21 `act`, 22 `done`, 23 `ua`, 24 `cnt`, 25 `gt`, 26 `top`. -/
def paramsStmt (pLog pSqrt pPow pDiv : ℕ) : Stmt :=
  .call pLog [v 0] 7 ;; .set 7 (v 7 +' k 1) ;;
  .call pSqrt [v 7] 8 ;; .set 8 (v 8 +' k 1) ;;
  .call pPow [v 8] 9 ;;
  .call pSqrt [v 8] 10 ;; .set 10 (v 8 *' (v 10 +' k 1)) ;;
  .call pDiv [v 10, k 2] 11 ;;
  .call pDiv [k 3 *' v 7, v 11] 12 ;; .set 12 (v 12 +' k 1) ;;
  .call pDiv [k 336175 *' v 7, k 10000000] 13 ;; .call pPow [v 13] 13 ;;
  .call pDiv [v 0 +' v 13 -' k 1, v 13] 14 ;;
  .call pLog [v 13] 15 ;; .set 15 (v 15 +' k 1) ;;
  .call pDiv [v 15 +' v 10, v 8] 16 ;; .set 16 (v 16 +' k 1) ;;
  .call pLog [k 3 *' v 1] 17 ;; .set 17 (v 17 +' k 1) ;;
  .call pDiv [v 17 -' k 1, v 8] 18 ;;
  .set 19 (v 0 *' v 0) ;;
  .set 20 (v 6 +' k 2 *' v 9) ;;
  .set 21 (v 6 +' k 4 *' v 9) ;;
  .set 22 (v 21 +' v 14 *' v 19) ;;
  .set 23 (v 22 +' v 19) ;;
  .set 24 (v 23 +' v 19) ;;
  .set 25 (v 24 +' v 14 *' v 19) ;;
  .set 26 (v 25 +' k 2 *' v 9 *' v 19)

/-- The locals after the parameters. -/
def topFrame (x : AEInst) (fr : ℕ) : List ℤ :=
  [x.n, x.U, x.ab, x.bc, x.ac, x.out, fr, kOf x.n, ellOf x.n, RR x.n, bOf x.n, dOf x.n,
    roundsOf x.n, sOf x.n, mOf x.n, cKOf x.n, rOf x.n, BOf x.U, hOf x.n x.U, ((x.n * x.n : ℕ) : ℤ),
    aPL x.n fr, aACT x.n fr, aDONE x.n fr, aUA x.n fr, aCNT x.n fr, aGT x.n fr, aTOP x.n fr]

/-- The time of the parameters. -/
def tParams (n U : ℕ) : ℕ :=
  log2Time n + sqrtTime (kOf n) + tPow2 (ellOf n) + sqrtTime (ellOf n) + tDiv (bOf n) 2 +
    tDiv (3 * kOf n) (dOf n) + tDiv (336175 * kOf n) (10 ^ 7) + tPow2 (336175 * kOf n / 10 ^ 7) +
    tDiv (n + sOf n - 1) (sOf n) + log2Time (sOf n) + tDiv (cKOf n + bOf n) (ellOf n) +
    log2Time (3 * U) + tDiv (BOf U - 1) (ellOf n) + 400

/-- The procedures for the parameters. -/
structure ParamProcs (P : Program) (pLog pSqrt pPow pDiv : ℕ) : Prop where
  log : P[pLog]? = some log2Body
  sqrt : P[pSqrt]? = some sqrtBody
  pow : P[pPow]? = some pow2Body
  div : P[pDiv]? = some divBody

set_option maxHeartbeats 1600000 in
theorem params_spec {P : Program} {d : ℕ} {pLog pSqrt pPow pDiv : ℕ}
    (HP : ParamProcs P pLog pSqrt pPow pDiv) {x : AEInst} {fr : ℕ} {μ : ℕ → ℤ}
    (hn : 1 ≤ x.n) (hU : 1 ≤ x.U) (hw : (lim.space : ℤ) ≤ lim.word)
    (hsp : aTOP x.n fr ≤ lim.space) (hword : (filterWord x.n x.U : ℤ) ≤ lim.word)
    (hdep : d < lim.depth) :
    Ends lim P d (paramsStmt pLog pSqrt pPow pDiv)
      ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, x.out, fr], μ⟩ (tParams x.n x.U)
      fun σ' => σ' = ⟨frame (topFrame x fr), μ⟩ := by
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14⟩ :=
    param_words (U := x.U) hn
  have hk : (kOf x.n : ℤ) = (Nat.log 2 x.n : ℤ) + 1 := by
    unfold kOf; rw [size_eq_log hn]; push_cast; ring
  unfold paramsStmt tParams
  light_call (log2_meets (d := d + 1) HP.log _ (x := x.n) (le_trans (by exact_mod_cast w1) hword))
    with _ _ ⟨rfl, rfl⟩
  light_set (kOf x.n : ℤ) using hk
  -- ℓ
  light_call (sqrt_meets (d := d + 1) HP.sqrt _ (K := kOf x.n)
    (le_trans (by exact_mod_cast w2) hword)) with _ _ ⟨rfl, rfl⟩
  have hl : (ellOf x.n : ℤ) = (Nat.sqrt (kOf x.n) : ℤ) + 1 := by unfold ellOf; push_cast; ring
  light_set (ellOf x.n : ℤ) using hl
  -- R
  light_call (pow2_meets (d := d + 1) HP.pow (e := ellOf x.n)
    (le_trans (by exact_mod_cast w3) hword)) with rR _ ⟨hrR, rfl⟩
  obtain rfl : rR = (RR x.n : ℤ) := by rw [hrR]; rfl
  -- b
  light_call (sqrt_meets (d := d + 1) HP.sqrt _ (K := ellOf x.n)
    (le_trans (by exact_mod_cast w4) hword)) with _ _ ⟨rfl, rfl⟩
  have hb : (bOf x.n : ℤ) = (ellOf x.n : ℤ) * ((Nat.sqrt (ellOf x.n) : ℤ) + 1) := by
    unfold bOf; push_cast; ring
  have hbw : (ellOf x.n : ℤ) * ((Nat.sqrt (ellOf x.n) : ℤ) + 1) ≤ lim.word := by
    rw [← hb]; exact le_trans (by exact_mod_cast (by omega : bOf x.n ≤ filterWord x.n x.U)) hword
  have hsl : (Nat.sqrt (ellOf x.n) : ℤ) + 1 ≤ lim.word := by
    have := Nat.sqrt_le_self (ellOf x.n)
    have : ((Nat.sqrt (ellOf x.n) + 1 : ℕ) : ℤ) ≤ (filterWord x.n x.U : ℤ) := by
      exact_mod_cast (by omega)
    push_cast at this; omega
  have hb0 : 0 ≤ (ellOf x.n : ℤ) * ((Nat.sqrt (ellOf x.n) : ℤ) + 1) := by positivity
  light_set (bOf x.n : ℤ) using hb
  -- d
  light_call (div_meets (d := d + 1) HP.div (a := bOf x.n) (b := 2) (by norm_num)
    (le_trans (by exact_mod_cast w5) hword)) with rd _ ⟨hrd, rfl⟩
  obtain rfl : rd = (dOf x.n : ℤ) := by rw [hrd]; rfl
  -- the number of rounds
  have hd1 := dOf_pos x.n
  light_call (div_meets (d := d + 1) HP.div (a := 3 * kOf x.n) (b := dOf x.n) hd1
    (le_trans (by exact_mod_cast w6) hword)) with rq _ ⟨hrq, rfl⟩
  have hro : (roundsOf x.n : ℤ) = rq + 1 := by
    rw [hrq]; unfold roundsOf; push_cast; ring
  light_set (roundsOf x.n : ℤ) using hro
  -- s
  light_call (div_meets (d := d + 1) HP.div (a := 336175 * kOf x.n) (b := 10000000)
    (by norm_num) (le_trans (by exact_mod_cast w7) hword)) with _ _ ⟨rfl, rfl⟩
  light_call (pow2_meets (d := d + 1) HP.pow (e := 336175 * kOf x.n / 10000000)
    (le_trans (by exact_mod_cast w8) hword)) with rs _ ⟨hrs, rfl⟩
  obtain rfl : rs = (sOf x.n : ℤ) := by rw [hrs]; rfl
  -- m
  have hs1 := sOf_pos x.n
  have hns : ((x.n + sOf x.n - 1 : ℕ) : ℤ) = (x.n : ℤ) + (sOf x.n : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  light_call (div_meets (d := d + 1) HP.div (a := x.n + sOf x.n - 1) (b := sOf x.n) hs1
    (le_trans (by exact_mod_cast w9) hword)) using hns with rm _ ⟨hrm, rfl⟩
  obtain rfl : rm = (mOf x.n : ℤ) := by rw [hrm]; rfl
  -- c_K
  light_call (log2_meets (d := d + 1) HP.log _ (x := sOf x.n)
    (le_trans (by exact_mod_cast w10) hword)) with rc _ ⟨hrc, rfl⟩
  have hcK : (cKOf x.n : ℤ) = rc + 1 := by
    rw [hrc]; unfold cKOf; rw [size_eq_log hs1]; push_cast; ring
  light_set (cKOf x.n : ℤ) using hcK
  -- r
  have hl1 := ellOf_pos x.n
  light_call (div_meets (d := d + 1) HP.div (a := cKOf x.n + bOf x.n) (b := ellOf x.n) hl1
    (le_trans (by exact_mod_cast w11) hword)) with rr _ ⟨hrr, rfl⟩
  have hr : (rOf x.n : ℤ) = rr + 1 := by
    rw [hrr]; unfold rOf; push_cast; ring
  light_set (rOf x.n : ℤ) using hr
  -- B
  have h3U : 1 ≤ 3 * x.U := by omega
  light_call (log2_meets (d := d + 1) HP.log _ (x := 3 * x.U)
    (le_trans (by exact_mod_cast w12) hword)) with rB _ ⟨hrB, rfl⟩
  have hB : (BOf x.U : ℤ) = rB + 1 := by
    rw [hrB]; unfold BOf; rw [size_eq_log h3U]; push_cast; ring
  light_set (BOf x.U : ℤ) using hB
  -- h
  have hB1 : 1 ≤ BOf x.U := by unfold BOf; exact Nat.size_pos.2 (by omega)
  have hBZ : ((BOf x.U - 1 : ℕ) : ℤ) = (BOf x.U : ℤ) - 1 := by
    rw [Nat.cast_sub hB1]; push_cast; ring
  light_call (div_meets (d := d + 1) HP.div (a := BOf x.U - 1) (b := ellOf x.n) hl1
    (le_trans (by exact_mod_cast w13) hword)) using hBZ with rh _ ⟨hrh, rfl⟩
  obtain rfl : rh = (hOf x.n x.U : ℤ) := by rw [hrh]; rfl
  -- the layout
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := layout x.n fr
  have hNZ : ((x.n * x.n : ℕ) : ℤ) = (x.n : ℤ) * (x.n : ℤ) := by push_cast; ring
  have e1 : (aPL x.n fr : ℤ) = (fr : ℤ) + 2 * (RR x.n : ℤ) := by unfold aPL; push_cast; ring
  have e2 : (aACT x.n fr : ℤ) = (fr : ℤ) + 4 * (RR x.n : ℤ) := by unfold aACT; push_cast; ring
  have e3 : (aDONE x.n fr : ℤ) = (aACT x.n fr : ℤ) + (mOf x.n : ℤ) * ((x.n : ℤ) * (x.n : ℤ)) := by
    unfold aDONE LL; push_cast; ring
  have e4 : (aUA x.n fr : ℤ) = (aDONE x.n fr : ℤ) + (x.n : ℤ) * (x.n : ℤ) := by
    unfold aUA; push_cast; ring
  have e5 : (aCNT x.n fr : ℤ) = (aUA x.n fr : ℤ) + (x.n : ℤ) * (x.n : ℤ) := by
    unfold aCNT; push_cast; ring
  have e6 : (aGT x.n fr : ℤ) = (aCNT x.n fr : ℤ) + (mOf x.n : ℤ) * ((x.n : ℤ) * (x.n : ℤ)) := by
    unfold aGT LL; push_cast; ring
  have e7 : (aTOP x.n fr : ℤ) = (aGT x.n fr : ℤ) + 2 * (RR x.n : ℤ) * ((x.n : ℤ) * (x.n : ℤ)) := by
    unfold aTOP; push_cast; ring
  have p1 : 0 ≤ (x.n : ℤ) * (x.n : ℤ) := by positivity
  have p2 : 0 ≤ (mOf x.n : ℤ) * ((x.n : ℤ) * (x.n : ℤ)) := by positivity
  have p3 : 0 ≤ 2 * (RR x.n : ℤ) * ((x.n : ℤ) * (x.n : ℤ)) := by positivity
  have htop : (aTOP x.n fr : ℤ) ≤ lim.word := le_trans (by exact_mod_cast hsp) hw
  light_set ((x.n * x.n : ℕ) : ℤ) using hNZ
  light_set (aPL x.n fr : ℤ) using e1
  light_set (aACT x.n fr : ℤ) using e2
  light_set (aDONE x.n fr : ℤ) using e3
  light_set (aUA x.n fr : ℤ) using e4
  light_set (aCNT x.n fr : ℤ) using e5
  light_set (aGT x.n fr : ℤ) using e6
  light_set (aTOP x.n fr : ℤ) using e7
  rfl

end Light.Filter2
