/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Filter2.HostStep

/-!
# The filtering host: one round

A round: the masses at the modulus `1`, then `r` steps, each of which certifies some groups and
multiplies the modulus by a prime of the pool, and at the end the marks of the candidates whose
count at the final modulus is `0` are cleared (`round_spec`).

The invariants: a group that is done has a witness (`Inv1`), and every candidate of a group that is
not done whose block has a witness is marked (`Inv2`).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Filter2

open ThreeSumApsp.Spec Light.Sec3

variable {lim : Limits}

/-- A group that is done has a witness. -/
def Inv1 (x : AEInst) (D : ℕ → Bool) : Prop :=
  ∀ g < x.n * x.n, D g = true → ∃ c < x.n, triSum x.n x.AB x.BC x.AC g c = 0

/-- A candidate of a group that is not done, whose block has a witness, is marked. -/
def Inv2 (x : AEInst) (act D : ℕ → Bool) : Prop :=
  ∀ i < LL x.n, D (i % (x.n * x.n)) = false → 0 < cntOf x.n (sOf x.n) 0 x.AB x.BC x.AC i →
    act i = true

theorem cntOf_pos_of_cnt0 {n s : ℕ} {AB BC AC : List ℤ} (p : ℕ) {i : ℕ}
    (h : 0 < cntOf n s 0 AB BC AC i) : 0 < cntOf n s p AB BC AC i := by
  unfold cntOf at *
  refine lt_of_lt_of_le h (Finset.card_le_card ?_)
  intro c hc
  simp only [Finset.mem_filter, Finset.mem_range, Nat.cast_zero, zero_dvd_iff] at hc ⊢
  exact ⟨hc.1, hc.2.1, by rw [hc.2.2]; exact dvd_zero _⟩

theorem rOf_le_Pmax (n : ℕ) : rOf n ≤ PmaxOf n := by
  unfold PmaxOf
  have := RR_two_le n
  exact (Nat.lt_pow_self (by omega)).le

/-- round(n, U, ab, bc, ac, s, pl, act, done, ua, cnt, gt, top, N, m, Q, h, r).  Locals: 18 the
modulus `M`, 19 the step, 20 scratch. -/
def roundBody (pO pAggr pStep pFA : ℕ) : Stmt :=
  .call pO [v 0, v 1, v 2, v 3, v 4, v 5, k 1, v 10, v 12] 20 ;;
  .call pAggr [v 10, v 7, v 9, v 13, v 14] 20 ;;
  .set 18 (k 1) ;;
  Stmt.for 19 (v 17) (.call pStep [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11,
    v 12, v 13, v 14, v 15, v 16, v 18] 18) ;;
  .call pO [v 0, v 1, v 2, v 3, v 4, v 5, v 18, v 10, v 12] 20 ;;
  .call pFA [v 7, v 10, v 14 *' v 13] 20

/-- The time of round. -/
def tRound (To : List ℕ → ℕ) (n U : ℕ) : ℕ :=
  2 * supTo To n U + tAggr (n * n) (mOf n) + rOf n * (tStep To n U + 58) + tFilterAct (LL n) + 200

/-- The locals of round. -/
def rFrame (x : AEInst) (fr Mc st : ℕ) (z : ℤ) : List ℤ :=
  stepArgs x fr (rOf x.n) ++ [(Mc : ℤ), (st : ℤ), z]

/-- The procedures that round calls. -/
structure RoundProcs (P : Program) (pO pAggr pStep pFA pCert pArg pCopy : ℕ) : Prop where
  step : P[pStep]? = some (stepBody pO pAggr pCert pArg pCopy)
  sp : StepProcs P pAggr pCert pArg pCopy
  fa : P[pFA]? = some filterActBody

section round

variable {P₀ R : Program} {pO pAggr pStep pFA pCert pArg pCopy : ℕ} {To : List ℕ → ℕ}
  {needo : List ℕ → Need} {d0 : ℕ} {x : AEInst} {fr : ℕ} {μ0 : ℕ → ℤ}

/-- The invariant of the loop over the steps. -/
def StepInv (x : AEInst) (fr : ℕ) (μ0 : ℕ → ℤ) (act D : ℕ → Bool) (st : ℕ) (σ : State) : Prop :=
  ∃ (Mc : ℕ) (z : ℤ) (D' : ℕ → Bool) (μ' : ℕ → ℤ), σ = ⟨frame (rFrame x fr Mc st z), μ'⟩ ∧
    FMem x fr μ0 μ' act D' ∧ UOk x fr μ' act D' Mc ∧ 1 ≤ Mc ∧ Mc ≤ (2 * RR x.n) ^ st ∧
    Inv1 x D' ∧ (∀ g, D g = true → D' g = true) ∧
    QOf x.n ^ st * tot x.n (sOf x.n) x.AB x.BC x.AC (eff (x.n * x.n) act D') Mc ≤
      (2 * hOf x.n x.U) ^ st * tot x.n (sOf x.n) x.AB x.BC x.AC (eff (x.n * x.n) act D) 1

set_option maxHeartbeats 800000 in
/-- **One round.** -/
theorem round_spec (hsol : SolvesN oracleTask P₀ pO To needo) {pRound : ℕ}
    (hRd : (P₀ ++ R)[pRound]? = some (roundBody pO pAggr pStep pFA))
    (HP : RoundProcs (P₀ ++ R) pO pAggr pStep pFA pCert pArg pCopy)
    (E : Env lim d0 x fr μ0 needo) {d : ℕ} (hd : d ≤ d0 + 2) {act D : ℕ → Bool} {μ : ℕ → ℤ}
    (hmem : FMem x fr μ0 μ act D) (hI1 : Inv1 x D) (hI2 : Inv2 x act D) :
    Meets lim (P₀ ++ R) pRound d (stepArgs x fr (rOf x.n)) μ (tRound To x.n x.U) fun _ μ' =>
      ∃ act' D' : ℕ → Bool, FMem x fr μ0 μ' act' D' ∧ Inv1 x D' ∧ Inv2 x act' D' ∧
        QOf x.n ^ rOf x.n * cardA x.n (sOf x.n) (eff (x.n * x.n) act' D') ≤
          (2 * hOf x.n x.U) ^ rOf x.n * (sOf x.n * cardA x.n (sOf x.n) (eff (x.n * x.n) act D)) := by
  have hn := E.n_pos
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := layout x.n fr
  have hsp := E.space
  have hw := E.hw
  obtain ⟨w1, w2, w3, w4, w5, w6, w7⟩ := word_facts (U := x.U) hn
  have hword := E.word
  have hdep := E.depth
  have hQ := QOf_lt x.n
  have hR := RR_two_le x.n
  have hrP := rOf_le_Pmax x.n
  have hP1 : 1 ≤ PmaxOf x.n := by unfold PmaxOf; exact Nat.one_le_pow _ _ (by omega)
  have hLN : LL x.n = mOf x.n * (x.n * x.n) := rfl
  refine Meets.of_body hRd ?_
  unfold roundBody tRound
  simp only [stepArgs]
  -- the masses at the modulus 1
  light_call (oracle_call (R := R) hsol E (d := d + 1) (by omega) hmem.kept (le_refl 1) hP1)
    with _ μ1 ⟨hcnt, hkb⟩
  have hs1 : SameOn (· < aCNT x.n fr) μ μ1 := fun a ha => hkb a ⟨by omega, by omega⟩
  have hmem1 := hmem.keep hs1
  have hc : ∀ i < mOf x.n * (x.n * x.n), cntOf x.n (sOf x.n) 1 x.AB x.BC x.AC i ≤ sOf x.n :=
    fun i _ => cntOf_le_s _ _
  have hcall := aggr_meets (lim := lim) (d := d + 1) HP.sp.aggr (μ := μ1) (cnt := aCNT x.n fr)
    (act := aACT x.n fr) (dst := aUA x.n fr) (N := x.n * x.n) (m := mOf x.n)
    (cmax := sOf x.n) (A := act) (c := fun i => cntOf x.n (sOf x.n) 1 x.AB x.BC x.AC i)
    hmem1.act hcnt hc (by unfold LL at *; omega) (by unfold LL at *; omega) (by omega)
    (by unfold LL at *; omega) (by unfold LL at *; omega) hw
    (le_trans (by exact_mod_cast (by unfold LL at *; omega)) hword)
  light_call hcall with r2 μ2 ⟨hua, hso⟩
  have hmem2 : FMem x fr μ0 μ2 act D := hmem1.keepU fun b hb => hso b (Or.inl hb)
  have hu2 : UOk x fr μ2 act D 1 := fun g hg _ => by
    rw [hua g hg, mass_eq_sum _ _ hg]
    rfl
  light_set (1 : ℕ)
  have hrw : (rOf x.n : ℤ) ≤ lim.word := by
    have : ((rOf x.n : ℕ) : ℤ) ≤ (filterWord x.n x.U : ℤ) := by exact_mod_cast (by omega)
    omega
  refine Ends.next (rOf x.n * (tStep To x.n x.U + 58) + 6)
    (Ends.for (StepInv x fr μ0 act D) (rOf x.n) (tStep To x.n x.U + 50) ?start ?round ?done ?bound
      hrw (by simp only [Expr.cost]; ring_nf; omega))
  case start =>
    refine ⟨1, r2, D, μ2, ?_, hmem2, hu2, le_rfl, by simp, hI1, fun _ h => h, by simp⟩
    simp [rFrame, stepArgs, update_frame_setLocal]
  case bound =>
    rintro st σ hst - ⟨Mc, z, D', μ', rfl, -⟩
    simp only [rFrame, stepArgs, List.cons_append, List.nil_append]
    light_side
  case round =>
    rintro st σ hst - ⟨Mc, z, D', μ', rfl, hm', hu', hM1, hMle, hI1', hDD', hpow⟩
    have hMc : Mc * (2 * RR x.n) ≤ PmaxOf x.n := by
      calc Mc * (2 * RR x.n) ≤ (2 * RR x.n) ^ st * (2 * RR x.n) := Nat.mul_le_mul_right _ hMle
        _ = (2 * RR x.n) ^ (st + 1) := (pow_succ _ _).symm
        _ ≤ PmaxOf x.n := Nat.pow_le_pow_right (by omega) hst
    have hcall := step_spec (R := R) hsol HP.step HP.sp E (d := d + 1) (by omega) hM1 hMc hm' hu'
    simp only [stepArgs] at hcall
    simp only [rFrame, stepArgs, List.cons_append, List.nil_append]
    light_call hcall with _ μ'' ⟨ts, hts, rfl, hm'', hu'', hmin⟩
    obtain ⟨hq1, hq2, -⟩ := pool_bounds (poolAt_mem hts)
    have hD : ∀ g < x.n * x.n, stepD x act D' Mc g = true ↔
        (D' g = true ∨ certOf x.n (sOf x.n) x.U x.AB x.BC x.AC act Mc g) :=
      fun g _ => stepD_iff x act D' Mc g
    have hcon := step_contract E.pre.leAB E.pre.leBC E.pre.leAC hD hts hmin
    refine ⟨by simp, Mc * poolAt x.n ts, z, stepD x act D' Mc, μ'', ?_, hm'', hu'',
      Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), ?_, ?_, ?_,
      pow_step hcon hpow⟩
    · simp [rFrame, stepArgs, update_frame_setLocal]
    · calc Mc * poolAt x.n ts ≤ (2 * RR x.n) ^ st * (2 * RR x.n) := Nat.mul_le_mul hMle hq2.le
        _ = (2 * RR x.n) ^ (st + 1) := (pow_succ _ _).symm
    · intro g hg hDg
      rcases (hD g hg).1 hDg with h | h
      · exact hI1' g hg h
      · exact witness_of_certOf E.pre.leAB E.pre.leBC E.pre.leAC h
    · intro g hg
      simp [stepD, hDD' g hg]
  case done =>
    rintro σ - ⟨Mc, z, D', μ', rfl, hm', hu', hM1, hMle, hI1', hDD', hpow⟩
    simp only [rFrame, stepArgs, List.cons_append, List.nil_append]
    have hMP : Mc ≤ PmaxOf x.n := hMle
    light_call (oracle_call (R := R) hsol E (d := d + 1) (by omega) hm'.kept hM1 hMP)
      with _ μ3 ⟨hcnt3, hkb3⟩
    have hm3 := hm'.keep fun a ha => hkb3 a ⟨by omega, by omega⟩
    have hfa := filterAct_meets (lim := lim) (d := d + 1) HP.fa (μ := μ3) (act := aACT x.n fr)
      (cnt := aCNT x.n fr) (L := LL x.n) (A := act)
      (c := fun i => cntOf x.n (sOf x.n) Mc x.AB x.BC x.AC i) hm3.act hcnt3
      (by omega) (by omega) (by omega) hw (by omega)
    have hLZ : ((mOf x.n : ℤ) * ((x.n : ℤ) * (x.n : ℤ))) = (LL x.n : ℤ) := by
      rw [hLN]; push_cast; ring
    light_call hfa using hLZ with _ μ4 ⟨hact4, hso4⟩
    refine ⟨fun i => act i && decide (0 < cntOf x.n (sOf x.n) Mc x.AB x.BC x.AC i), D', ?_, hI1',
      ?_, ?_⟩
    · exact ⟨fun a ha => (hso4 a (Or.inl (by omega))).trans (hm3.kept a ha),
        hm3.pool.congr fun i hi => hso4 _ (Or.inl (by omega)), hact4,
        hm3.done.congr fun i hi => hso4 _ (Or.inr (by omega))⟩
    · intro i hi hD hc0
      have hDi : D (i % (x.n * x.n)) = false := by
        cases h : D (i % (x.n * x.n)) with
        | false => rfl
        | true => rw [hDD' _ h] at hD; exact absurd hD (by simp)
      simp [hI2 i hi hDi hc0, cntOf_pos_of_cnt0 Mc hc0]
    · have he : eff (x.n * x.n) (fun i => act i && decide (0 < cntOf x.n (sOf x.n) Mc x.AB x.BC x.AC i))
          D' = fun i => eff (x.n * x.n) act D' i &&
            decide (0 < cntOf x.n (sOf x.n) Mc x.AB x.BC x.AC i) := by
        funext i
        simp only [eff]
        cases act i <;> cases D' (i % (x.n * x.n)) <;> simp
      rw [he]
      calc _ ≤ QOf x.n ^ rOf x.n * tot x.n (sOf x.n) x.AB x.BC x.AC (eff (x.n * x.n) act D') Mc :=
            Nat.mul_le_mul_left _ (card_filter_le_tot _ _)
        _ ≤ _ := hpow
        _ ≤ _ := Nat.mul_le_mul_left _ (tot_le_s _ _)

end round

end Light.Filter2
