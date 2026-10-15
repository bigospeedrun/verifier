/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Filter2.HostTop

/-!
# The filtering host: the top procedure

After the parameters, the host sieves the primes below `2R`, keeps those of the pool, marks all
candidates and no group, and runs `core` (`top_spec`).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Filter2

open ThreeSumApsp.Spec Light.Sec3

variable {lim : Limits}

/-- The pool, the marks and the flags, and the core.  Locals 27 `Q`, 28 scratch. -/
def restStmt (pSieve pPF pFill pCore : ℕ) : Stmt :=
  .call pSieve [k 2 *' v 9 -' k 1, v 6, v 26] 27 ;;
  .call pPF [v 6, v 27, v 9, v 20] 27 ;;
  .call pFill [v 21, v 14 *' v 19, k 1] 28 ;;
  .call pFill [v 22, v 19, k 0] 28 ;;
  .call pCore [v 0, v 1, v 2, v 3, v 4, v 13, v 20, v 21, v 22, v 23, v 24, v 25, v 26, v 19,
    v 14, v 27, v 18, v 16, v 12, v 5] 28 ;;
  .set 0 (k 0)

/-- The host. -/
def topBody (pLog pSqrt pPow pDiv pSieve pPF pFill pCore : ℕ) : Stmt :=
  paramsStmt pLog pSqrt pPow pDiv ;; restStmt pSieve pPF pFill pCore

/-- The time of the host. -/
def tTop (To : List ℕ → ℕ) (n U : ℕ) : ℕ :=
  tParams n U + sieveTime (2 * RR n - 1) + tPoolFilter (2 * RR n) + fillTime (LL n) +
    fillTime (n * n) + tCore To n U + 200

/-- The procedures of the host besides core. -/
structure TopProcs (P : Program) (pSieve pPF pFill : ℕ) : Prop where
  sieve : P[pSieve]? = some sieveBody
  pf : P[pPF]? = some poolFilterBody
  fill : P[pFill]? = some fillBody

theorem arr_of_replicate {μ : ℕ → ℤ} {a n : ℕ} {z : ℤ} (h : Seg μ a (List.replicate n z)) :
    Arr μ a n fun _ => z := fun i hi => by
  rw [h i (by simpa using hi)]
  simp

theorem arr_of_poolL {μ : ℕ → ℤ} {a n : ℕ} (h : SegN μ a (poolL n)) :
    Arr μ a (QOf n) fun t => (poolAt n t : ℤ) := fun t ht => by
  have ht' : t < (poolL n).length := by rw [length_poolL]; exact ht
  rw [h t (by simpa using ht')]
  simp only [List.getElem_map]
  unfold poolAt
  rw [List.getD_eq_getElem _ _ ht']

section top

variable {P₀ R : Program} {pO pAggr pStep pFA pCert pArg pCopy : ℕ} {To : List ℕ → ℕ}
  {needo : List ℕ → Need} {d : ℕ} {x : AEInst} {fr : ℕ} {μ0 : ℕ → ℤ}

set_option maxHeartbeats 1600000 in
/-- **The host.** -/
theorem top_spec (hsol : SolvesN oracleTask P₀ pO To needo)
    {pLog pSqrt pPow pDiv pSieve pPF pFill pCore pRound pFinal pGroup pScan : ℕ}
    (HPa : ParamProcs (P₀ ++ R) pLog pSqrt pPow pDiv)
    (HT : TopProcs (P₀ ++ R) pSieve pPF pFill)
    (hC : (P₀ ++ R)[pCore]? = some (coreBody pRound pFinal))
    (hRd : (P₀ ++ R)[pRound]? = some (roundBody pO pAggr pStep pFA))
    (HP : RoundProcs (P₀ ++ R) pO pAggr pStep pFA pCert pArg pCopy)
    (HF : FinalProcs (P₀ ++ R) pFinal pGroup pScan)
    (E : Env lim d x fr μ0 needo) :
    Ends lim (P₀ ++ R) d (topBody pLog pSqrt pPow pDiv pSieve pPF pFill pCore)
      ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, x.out, fr], μ0⟩ (tTop To x.n x.U) fun σ' =>
        Seg σ'.mem x.out (aeFlags x.n x.AB x.BC x.AC) ∧ KeptBut μ0 σ'.mem fr x.out (x.n * x.n) := by
  have hn := E.n_pos
  have hU := E.pre.U_pos
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := layout x.n fr
  have hsp := E.space
  have hw := E.hw
  obtain ⟨w1, w2, w3, w4, w5, w6, w7⟩ := word_facts (U := x.U) hn
  have hword := E.word
  have hdep := E.depth
  have hR := RR_two_le x.n
  have hQ := QOf_lt x.n
  unfold topBody tTop
  light_piece (params_spec HPa hn hU hw (by omega) hword (by omega)) with σ rfl
  unfold restStmt topFrame
  -- the primes below 2R
  have hR1 : ((2 * RR x.n - 1 : ℕ) : ℤ) = 2 * (RR x.n : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hpre : Sieve.Pre lim (2 * RR x.n - 1) fr (aTOP x.n fr) :=
    ⟨hw, le_trans (by exact_mod_cast (by omega : 2 * (2 * RR x.n - 1) + 2 ≤ filterWord x.n x.U))
      hword, by omega, by omega⟩
  light_call (sieve_meets (d := d + 1) (μ := μ0) HT.sieve hpre) using hR1 with _ μ1 ⟨rfl, hseg1, hso1⟩
  have h2R : 2 * RR x.n - 1 + 1 = 2 * RR x.n := by omega
  rw [Sieve.sort_primesLE, h2R] at hseg1
  have hlen : (Sieve.primesBelow (2 * RR x.n)).length = (Nat.primesLE (2 * RR x.n - 1)).card := by
    rw [← Sieve.length_primesBelow, h2R]
  have hc : (Nat.primesLE (2 * RR x.n - 1)).card ≤ 2 * RR x.n := by
    rw [← hlen]
    exact (List.length_filter_le _ _).trans (by simp)
  have hlt : ∀ q ∈ Sieve.primesBelow (2 * RR x.n), q < 2 * RR x.n := fun q hq => by
    simp only [Sieve.primesBelow, List.mem_filter, List.mem_range] at hq
    exact hq.1
  -- the pool
  light_call ((poolFilter_meets (d := d + 1) (R := RR x.n) (dst := aPL x.n fr) HT.pf hseg1 hlen hlt (by omega) (by omega)
    (Or.inl (by omega)) hw (le_trans (by exact_mod_cast (by omega : RR x.n + 2 * RR x.n + 1 ≤
      filterWord x.n x.U)) hword)).mono_time (T' := tPoolFilter (2 * RR x.n))
      (by unfold tPoolFilter; omega)) with rq μ2 ⟨hrq, hseg2, hso2⟩
  obtain rfl : rq = (QOf x.n : ℤ) := by rw [hrq, ← length_poolL]; rfl
  -- all candidates marked, no group done
  have hLZ : (LL x.n : ℤ) = (mOf x.n : ℤ) * ((x.n : ℤ) * (x.n : ℤ)) := by unfold LL; push_cast; ring
  have hLZ' : (LL x.n : ℤ) = (mOf x.n : ℤ) * ((x.n * x.n : ℕ) : ℤ) := by unfold LL; push_cast; ring
  have p2 : 0 ≤ (mOf x.n : ℤ) * ((x.n : ℤ) * (x.n : ℤ)) := by positivity
  light_call (fill_meets (d := d + 1) (μ := μ2) HT.fill (dst := aACT x.n fr) (n := LL x.n)
    (x := 1) hw (by omega)) using hLZ with _ μ3 ⟨hseg3, hso3⟩
  light_call (fill_meets (d := d + 1) (μ := μ3) HT.fill (dst := aDONE x.n fr) (n := x.n * x.n)
    (x := 0) hw (by omega)) with _ μ4 ⟨hseg4, hso4⟩
  have hmem : FMem x fr μ0 μ4 (fun _ => true) (fun _ => false) :=
    ⟨fun a ha => by
      rw [hso4 a (Or.inl (by omega)), hso3 a (Or.inl (by omega)), hso2 a (Or.inl (by omega)),
        hso1 a ⟨Or.inl (by omega), Or.inl (by omega)⟩],
      (arr_of_poolL hseg2).congr fun t ht => by
        rw [hso4 _ (Or.inl (by omega)), hso3 _ (Or.inl (by omega))],
      (arr_of_replicate hseg3).congr fun t ht => hso4 _ (Or.inl (by omega)),
      arr_of_replicate hseg4⟩
  have hcall := core_spec (R := R) hsol hC hRd HP HF E (d := d + 1) le_rfl hmem
  simp only [coreArgs, stepArgs, List.cons_append, List.nil_append] at hcall
  light_call hcall with _ μ5 ⟨hseg5, hkb5⟩
  light_set (0 : ℕ)
  exact ⟨hseg5, hkb5⟩

end top

end Light.Filter2
