/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Filter2.HostRound

/-!
# The filtering host: the rounds and the final scans

`core` runs the rounds and then scans the blocks of the candidates that are still marked, in the
groups that are not done (`core_spec`).  The flags it writes are the flags of all-edges Exact
Triangle, whatever the guard; with the guard, no candidate is marked after the rounds, so that the
final scans cost nothing.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Filter2

open ThreeSumApsp.Spec Light.Sec3

variable {lim : Limits}

/-! ## The flags -/

theorem hitB_iff {x : AEInst} {act D : ℕ → Bool} (hI1 : Inv1 x D) (hI2 : Inv2 x act D) {g : ℕ}
    (hg : g < x.n * x.n) :
    hitB x.n (sOf x.n) x.AB x.BC x.AC act D g (mOf x.n) = true ↔
      ∃ c < x.n, triSum x.n x.AB x.BC x.AC g c = 0 := by
  unfold hitB
  simp only [Bool.or_eq_true, List.any_eq_true, List.mem_range, Bool.and_eq_true]
  constructor
  · rintro (h | ⟨j, hj, ha, hb⟩)
    · exact hI1 g hg h
    · have h0 := (blockHit_iff hg (mul_sOf_lt hj)).1 hb
      have := witness_of_cnt0 h0
      rwa [mod_block hg] at this
  · rintro ⟨c, hc, h⟩
    cases hD : D g
    · right
      have hj := div_sOf_lt hc
      have h0 := cnt0_of_witness (sOf_pos x.n) hg hc h
      refine ⟨c / sOf x.n, hj, ?_, (blockHit_iff hg (mul_sOf_lt hj)).2 h0⟩
      refine hI2 _ ?_ (by rw [mod_block hg]; exact hD) h0
      unfold LL
      have := Nat.mul_le_mul_right (x.n * x.n) (show c / sOf x.n + 1 ≤ mOf x.n by omega)
      rw [Nat.add_mul, Nat.one_mul] at this
      omega
    · left; rfl

theorem seg_aeFlags {x : AEInst} {act D : ℕ → Bool} (hI1 : Inv1 x D) (hI2 : Inv2 x act D)
    {μ : ℕ → ℤ}
    (h : Arr μ x.out (x.n * x.n) fun g => bitB (hitB x.n (sOf x.n) x.AB x.BC x.AC act D g (mOf x.n))) :
    Seg μ x.out (aeFlags x.n x.AB x.BC x.AC) := by
  intro i hi
  simp only [aeFlags, List.length_map, List.length_range] at hi
  rw [h i hi]
  simp only [aeFlags, List.getElem_map, List.getElem_range]
  have := hitB_iff hI1 hI2 hi
  unfold triSum at this
  by_cases hw : ∃ c < x.n, x.AB.getD i 0 + x.BC.getD (i % x.n * x.n + c) 0 +
      x.AC.getD (i / x.n * x.n + c) 0 = 0
  · rw [this.2 hw, flag, if_pos hw]; rfl
  · have hf : hitB x.n (sOf x.n) x.AB x.BC x.AC act D i (mOf x.n) = false := by
      cases h' : hitB x.n (sOf x.n) x.AB x.BC x.AC act D i (mOf x.n)
      · rfl
      · exact absurd (this.1 h') hw
    rw [hf, flag, if_neg hw]; rfl

/-- The work of the final scans is the number of marked candidates of the groups that are not
done. -/
theorem sum_cntG_eq (n s : ℕ) (act D : ℕ → Bool) :
    ∑ g ∈ Finset.range (n * n), cntG (n * n) ((n + s - 1) / s) act D g =
      cardA n s (eff (n * n) act D) := by
  unfold cntG cardA
  refine Finset.sum_congr rfl fun g hg => Finset.sum_congr rfl fun j _ => ?_
  simp only [eff, mod_block (Finset.mem_range.1 hg)]

theorem cardA_le_LL (n : ℕ) (A : ℕ → Bool) : cardA n (sOf n) A ≤ LL n := by
  calc cardA n (sOf n) A ≤ cardA n (sOf n) (fun _ => true) := cardA_mono fun _ _ => rfl
    _ = LL n := by rw [cardA_true]; unfold LL mOf; ring

/-! ## The program -/

/-- core(n, U, ab, bc, ac, s, pl, act, done, ua, cnt, gt, top, N, m, Q, h, r, rounds, out).  Locals:
20 the round, 21 scratch. -/
def coreBody (pRound pFinal : ℕ) : Stmt :=
  Stmt.for 20 (v 18) (.call pRound [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11,
    v 12, v 13, v 14, v 15, v 16, v 17] 21) ;;
  .call pFinal [v 0, v 2, v 3, v 4, v 19, v 8, v 7, v 5, v 14, v 13] 21 ;;
  .set 0 (k 0)

/-- The arguments of core. -/
def coreArgs (x : AEInst) (fr : ℕ) : List ℤ :=
  stepArgs x fr (rOf x.n) ++ [(roundsOf x.n : ℤ), (x.out : ℤ)]

/-- The number of candidates that the final scans may meet: none with the guard, all without. -/
def cFin (n U : ℕ) : ℕ := if Guard n U then 0 else LL n

/-- The time of core. -/
def tCore (To : List ℕ → ℕ) (n U : ℕ) : ℕ :=
  roundsOf n * (tRound To n U + 30) + tFinal (n * n) (mOf n) (sOf n) (cFin n U) + 30

/-- The procedures of the final scans. -/
structure FinalProcs (P : Program) (pFinal pGroup pScan : ℕ) : Prop where
  final : P[pFinal]? = some (finalBody pGroup)
  group : P[pGroup]? = some (groupBody pScan)
  scan : P[pScan]? = some scanBody


theorem roundsOf_le_word (n U : ℕ) : roundsOf n ≤ filterWord n U := by
  have h1 : roundsOf n ≤ 3 * n + 1 := by
    have : kOf n ≤ n := Nat.size_le.2 Nat.lt_two_pow_self
    unfold roundsOf
    have := Nat.div_le_self (3 * kOf n) (dOf n)
    omega
  obtain ⟨k1, -, -, -⟩ := KW_ge n U
  have h2 : n + 1 ≤ (n + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  have h3 : KW n U ≤ KW n U * KW n U := Nat.le_mul_of_pos_left _ (by omega)
  rw [filterWord_eq]
  omega

section core

variable {P₀ R : Program} {pO pAggr pStep pFA pCert pArg pCopy : ℕ} {To : List ℕ → ℕ}
  {needo : List ℕ → Need} {d0 : ℕ} {x : AEInst} {fr : ℕ} {μ0 : ℕ → ℤ}

/-- The invariant of the rounds. -/
def CoreInv (x : AEInst) (fr : ℕ) (μ0 : ℕ → ℤ) (ρ : ℕ) (μ : ℕ → ℤ) : Prop :=
  ∃ act D : ℕ → Bool, FMem x fr μ0 μ act D ∧ Inv1 x D ∧ Inv2 x act D ∧
    (Guard x.n x.U → 2 ^ (dOf x.n * ρ) * cardA x.n (sOf x.n) (eff (x.n * x.n) act D) ≤ LL x.n)

theorem weights_of_env {d : ℕ} (E : Env lim d x fr μ0 needo) {μ : ℕ → ℤ} (hk : Kept μ0 μ fr) :
    Weights lim μ x.ab x.bc x.ac x.n x.U x.AB x.BC x.AC := by
  have hpre := E.pre.toPre.keep hk
  have hn := E.n_pos
  obtain ⟨w1, w2, w3, w4, w5, w6, w7⟩ := word_facts (U := x.U) hn
  have hword := E.word
  have hsp := E.space
  obtain ⟨_, _, _, _, _, _, _⟩ := layout x.n fr
  exact { hw := E.hw
          hU := le_trans (by exact_mod_cast w6) hword
          arrAB := ⟨hpre.lenAB, hpre.segAB, hpre.leAB, by have := hpre.belowAB; omega⟩
          arrBC := ⟨hpre.lenBC, hpre.segBC, hpre.leBC, by have := hpre.belowBC; omega⟩
          arrAC := ⟨hpre.lenAC, hpre.segAC, hpre.leAC, by have := hpre.belowAC; omega⟩ }

set_option maxHeartbeats 800000 in
/-- **The rounds and the final scans.** -/
theorem core_spec (hsol : SolvesN oracleTask P₀ pO To needo) {pCore pRound pFinal pGroup pScan : ℕ}
    (hC : (P₀ ++ R)[pCore]? = some (coreBody pRound pFinal))
    (hRd : (P₀ ++ R)[pRound]? = some (roundBody pO pAggr pStep pFA))
    (HP : RoundProcs (P₀ ++ R) pO pAggr pStep pFA pCert pArg pCopy)
    (HF : FinalProcs (P₀ ++ R) pFinal pGroup pScan)
    (E : Env lim d0 x fr μ0 needo) {d : ℕ} (hd : d ≤ d0 + 1) {μ : ℕ → ℤ}
    (hmem : FMem x fr μ0 μ (fun _ => true) (fun _ => false)) :
    Meets lim (P₀ ++ R) pCore d (coreArgs x fr) μ (tCore To x.n x.U) fun _ μ' =>
      Seg μ' x.out (aeFlags x.n x.AB x.BC x.AC) ∧ KeptBut μ0 μ' fr x.out (x.n * x.n) := by
  have hn := E.n_pos
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := layout x.n fr
  have hsp := E.space
  have hw := E.hw
  obtain ⟨w1, w2, w3, w4, w5, w6, w7⟩ := word_facts (U := x.U) hn
  have hword := E.word
  have hdep := E.depth
  have hQ0 := QOf_pos x.n
  have hpre := E.pre
  have hbo := hpre.belowOut
  have hLN : LL x.n = mOf x.n * (x.n * x.n) := rfl
  have hroundsw : (roundsOf x.n : ℤ) ≤ lim.word := by
    have : ((roundsOf x.n : ℕ) : ℤ) ≤ (filterWord x.n x.U : ℤ) := by
      exact_mod_cast roundsOf_le_word x.n x.U
    omega
  refine Meets.of_body hC ?_
  unfold coreBody tCore
  refine Ends.next (roundsOf x.n * (tRound To x.n x.U + 30) + 6)
    (Ends.forScratch [21] (CoreInv x fr μ0) (roundsOf x.n) (tRound To x.n x.U + 22) ?start ?round
      ?done ?bound (by simp) (by simp) hroundsw (by simp only [Expr.cost]; ring_nf; omega))
  case start =>
    refine ⟨fun _ => true, fun _ => false, hmem, fun g _ h => absurd h (by simp),
      fun _ _ _ _ => rfl, fun _ => ?_⟩
    simpa using cardA_le_LL x.n (eff (x.n * x.n) (fun _ => true) fun _ => false)
  case bound =>
    intro j loc' μ' hj _
    simp only [refreshLocals, coreArgs, stepArgs, List.cons_append, List.nil_append]
    light_side
  case round =>
    rintro ρ loc' μ' hρ ⟨act, D, hm, hI1, hI2, hG⟩
    simp only [refreshLocals, coreArgs, stepArgs, List.cons_append, List.nil_append]
    have hcall := round_spec (R := R) hsol hRd HP E (d := d + 1) (by omega) hm hI1 hI2
    simp only [stepArgs] at hcall
    light_call hcall with _ μ'' ⟨act', D', hm', hI1', hI2', hcard⟩
    refine ⟨act', D', hm', hI1', hI2', fun hg => ?_⟩
    have h1 := guard_step hQ0 hg hcard
    calc 2 ^ (dOf x.n * (ρ + 1)) * cardA x.n (sOf x.n) (eff (x.n * x.n) act' D')
        = 2 ^ (dOf x.n * ρ) * (2 ^ dOf x.n * cardA x.n (sOf x.n) (eff (x.n * x.n) act' D')) := by
          rw [Nat.mul_succ, pow_add]; ring
      _ ≤ 2 ^ (dOf x.n * ρ) * cardA x.n (sOf x.n) (eff (x.n * x.n) act D) :=
          Nat.mul_le_mul_left _ h1
      _ ≤ LL x.n := hG hg
  case done =>
    rintro loc' μ1 ⟨act, D, hm, hI1, hI2, hG⟩
    simp only [refreshLocals, coreArgs, stepArgs, List.cons_append, List.nil_append]
    have hW := weights_of_env E hm.kept
    have hsum : ∑ g ∈ Finset.range (x.n * x.n), cntG (x.n * x.n) (mOf x.n) act D g =
        cardA x.n (sOf x.n) (eff (x.n * x.n) act D) := sum_cntG_eq _ _ _ _
    have hcard : cardA x.n (sOf x.n) (eff (x.n * x.n) act D) ≤ cFin x.n x.U := by
      unfold cFin
      split_ifs with hg
      · have h1 := hG hg
        have h2 := card_lt_two_pow x.n
        have h3 : LL x.n = x.n * x.n * mOf x.n := by unfold LL; ring
        have h4 : cardA x.n (sOf x.n) (eff (x.n * x.n) act D) = 0 := by
          by_contra hne
          have : 2 ^ (dOf x.n * roundsOf x.n) ≤
              2 ^ (dOf x.n * roundsOf x.n) * cardA x.n (sOf x.n) (eff (x.n * x.n) act D) :=
            Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hne)
          omega
        omega
      · exact cardA_le_LL _ _
    have hcall : Meets lim (P₀ ++ R) pFinal (d + 1)
        [x.n, x.ab, x.bc, x.ac, x.out, aDONE x.n fr, aACT x.n fr, sOf x.n, mOf x.n, x.n * x.n] μ1
        (tFinal (x.n * x.n) (mOf x.n) (sOf x.n) (cFin x.n x.U)) fun _ μ' =>
          Arr μ' x.out (x.n * x.n)
            (fun g => bitB (hitB x.n (sOf x.n) x.AB x.BC x.AC act D g (mOf x.n))) ∧
          SameOutside μ1 μ' x.out (x.n * x.n) := by
      refine (Meets.of_body HF.final (final_spec HF.group HF.scan hW hm.done hm.act
        (fun j hj => mul_sOf_lt hj) hn (by omega) (by unfold LL at *; omega) (by omega)
        (Or.symm hpre.apartAB) (Or.symm hpre.apartBC) (Or.symm hpre.apartAC) (Or.inl (by omega))
        (Or.inl (by unfold LL at *; omega)) (le_trans (by exact_mod_cast w5) hword)
        (by omega))).mono_time ?_
      rw [hsum]
      unfold tFinal
      have := Nat.mul_le_mul_right (tScan (sOf x.n)) hcard
      omega
    light_call hcall with _ μ2 ⟨harr, hso⟩
    light_set (0 : ℕ)
    exact ⟨seg_aeFlags hI1 hI2 harr, fun b hb => (hso b hb.2).trans (hm.kept b hb.1)⟩

end core

end Light.Filter2
