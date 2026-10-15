/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Filter2.HostFinal

/-!
# The filtering host: the layout, and one step of a round

* The layout of the memory of the host above the free pointer `fr`: the primes below `2R`, the pool,
  the marks `act` of the `L = m n²` candidates, the flags `done` of the `n²` groups, the masses `ua`
  of the groups, the counts `cnt` of the oracle, the table `gt` of the masses at the moduli `M q`,
  and the free pointer `top` of the oracle.
* `Env`: what the host knows about the limits and the instance; `FMem`: the memory between the
  steps.
* `stepBody`: one step of a round (`step_spec`).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Filter2

open ThreeSumApsp.Spec Light.Sec3

variable {lim : Limits}

/-! ## The layout -/

/-- The number of candidates, `m n²`. -/
def LL (n : ℕ) : ℕ := mOf n * (n * n)

/-- The pool. -/
def aPL (n fr : ℕ) : ℕ := fr + 2 * RR n
/-- The marks of the candidates. -/
def aACT (n fr : ℕ) : ℕ := fr + 4 * RR n
/-- The flags of the groups. -/
def aDONE (n fr : ℕ) : ℕ := aACT n fr + LL n
/-- The masses of the groups at the current modulus. -/
def aUA (n fr : ℕ) : ℕ := aDONE n fr + n * n
/-- The counts written by the oracle. -/
def aCNT (n fr : ℕ) : ℕ := aUA n fr + n * n
/-- The table of the masses at the moduli `M q`. -/
def aGT (n fr : ℕ) : ℕ := aCNT n fr + LL n
/-- The free pointer of the oracle (and the table of the sieve). -/
def aTOP (n fr : ℕ) : ℕ := aGT n fr + 2 * RR n * (n * n)

/-- The largest time of the oracle at the moduli up to `Pmax`. -/
def supTo (To : List ℕ → ℕ) (n U : ℕ) : ℕ :=
  (Finset.range (PmaxOf n + 1)).sup fun p => To [n, U, sOf n, p]

theorem le_supTo (To : List ℕ → ℕ) {n U p : ℕ} (hp : p ≤ PmaxOf n) :
    To [n, U, sOf n, p] ≤ supTo To n U :=
  Finset.le_sup (f := fun p => To [n, U, sOf n, p]) (Finset.mem_range.2 (by omega))

/-- A bound on the numbers that the host forms. -/
def filterWord (n U : ℕ) : ℕ :=
  10 ^ 9 * ((n + 1) ^ 3 * (U + 1) * (RR n + 1) * (PmaxOf n + 1)) ^ 2

/-- What the host knows: the instance (in the first memory `μ0`), the limits, and the need of the
oracle at all moduli up to `Pmax`.  The host runs at depth `d`. -/
structure Env (lim : Limits) (d : ℕ) (x : AEInst) (fr : ℕ) (μ0 : ℕ → ℤ) (needo : List ℕ → Need) :
    Prop where
  pre : x.Pre μ0 fr
  hw : (lim.space : ℤ) ≤ lim.word
  space : aTOP x.n fr + 2 * RR x.n ≤ lim.space
  word : (filterWord x.n x.U : ℤ) ≤ lim.word
  oracle : ∀ p ≤ PmaxOf x.n, (needo [x.n, x.U, sOf x.n, p]).Ok lim (aTOP x.n fr) (d + 4)
  depth : d + 5 ≤ lim.depth

/-- The memory between two steps: nothing below `fr` has changed, and the pool, the marks `act` and
the flags `D` are in place. -/
structure FMem (x : AEInst) (fr : ℕ) (μ0 μ : ℕ → ℤ) (act D : ℕ → Bool) : Prop where
  kept : Kept μ0 μ fr
  pool : Arr μ (aPL x.n fr) (QOf x.n) fun t => (poolAt x.n t : ℤ)
  act : Arr μ (aACT x.n fr) (LL x.n) fun i => bitB (act i)
  done : Arr μ (aDONE x.n fr) (x.n * x.n) fun g => bitB (D g)

/-- The masses of the groups that are not done, at the modulus `M`. -/
def UOk (x : AEInst) (fr : ℕ) (μ : ℕ → ℤ) (act D : ℕ → Bool) (M : ℕ) : Prop :=
  ∀ g < x.n * x.n, D g = false →
    μ (aUA x.n fr + g) = (mass x.n (sOf x.n) x.AB x.BC x.AC act M g : ℤ)

/-- The instance of the oracle at the modulus `p`. -/
def oInst (x : AEInst) (fr p : ℕ) : OracleInst :=
  { toTriInst := x.toTriInst, s := sOf x.n, p := p, cnt := aCNT x.n fr }

theorem Env.n_pos {d : ℕ} {x : AEInst} {fr : ℕ} {μ0 : ℕ → ℤ} {needo : List ℕ → Need}
    (E : Env lim d x fr μ0 needo) : 1 ≤ x.n := E.pre.n_pos

/-- The places, in order. -/
theorem layout (n fr : ℕ) : fr + 2 * RR n = aPL n fr ∧ aPL n fr + 2 * RR n = aACT n fr ∧
    aACT n fr + LL n = aDONE n fr ∧ aDONE n fr + n * n = aUA n fr ∧ aUA n fr + n * n = aCNT n fr ∧
    aCNT n fr + LL n = aGT n fr ∧ aGT n fr + 2 * RR n * (n * n) = aTOP n fr := by
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
  unfold aPL aACT
  omega

theorem seg_cntList_arr {μ : ℕ → ℤ} {a n s p : ℕ} {AB BC AC : List ℤ}
    (h : Seg μ a (cntList n s p AB BC AC)) :
    Arr μ a ((n + s - 1) / s * (n * n)) fun i => (cntOf n s p AB BC AC i : ℤ) := fun i hi => by
  rw [h i (by simp [cntList]; exact hi)]
  simp [cntList]

/-- **The oracle**, called at the modulus `p ≤ Pmax`: it writes the counts to `cnt`. -/
theorem oracle_call {P₀ R : Program} {pO : ℕ} {To : List ℕ → ℕ} {needo : List ℕ → Need}
    (hsol : SolvesN oracleTask P₀ pO To needo) {d0 : ℕ} {x : AEInst} {fr : ℕ} {μ0 : ℕ → ℤ}
    (E : Env lim d0 x fr μ0 needo) {d : ℕ} (hd : d ≤ d0 + 4) {μ : ℕ → ℤ} (hk : Kept μ0 μ fr)
    {p : ℕ} (hp1 : 1 ≤ p) (hp : p ≤ PmaxOf x.n) :
    Meets lim (P₀ ++ R) pO d [x.n, x.U, x.ab, x.bc, x.ac, sOf x.n, p, aCNT x.n fr, aTOP x.n fr] μ
      (supTo To x.n x.U) fun _ μ' =>
        Arr μ' (aCNT x.n fr) (LL x.n) (fun i => (cntOf x.n (sOf x.n) p x.AB x.BC x.AC i : ℤ)) ∧
          KeptBut μ μ' (aTOP x.n fr) (aCNT x.n fr) (LL x.n) := by
  have hpre := E.pre
  have hn := E.n_pos
  obtain ⟨_, _, _, _, _, _, _⟩ := layout x.n fr
  have hbo := hpre.belowOut
  have hAB := hpre.belowAB
  have hBC := hpre.belowBC
  have hAC := hpre.belowAC
  have hopre : (oInst x fr p).Pre μ (aTOP x.n fr) :=
    { toPre := (hpre.toPre.keep hk).mono (by omega)
      s_pos := sOf_pos x.n
      s_le := sOf_le hn
      p_pos := hp1
      belowCnt := by simp only [oInst, OracleInst.len]; unfold LL mOf at *; omega
      apartAB := by simp only [oInst, OracleInst.len, Apart]; omega
      apartBC := by simp only [oInst, OracleInst.len, Apart]; omega
      apartAC := by simp only [oInst, OracleInst.len, Apart]; omega }
  have hok : (needo (oracleTask.pars (oInst x fr p))).Ok lim (aTOP x.n fr) d := by
    show (needo [x.n, x.U, sOf x.n, p]).Ok lim (aTOP x.n fr) d
    exact (E.oracle p hp).mono le_rfl le_rfl (by omega)
  have h := hsol.meets R (oInst x fr p) hopre hok
  refine h.mono (le_supTo To hp) ?_
  rintro r μ' ⟨hseg, hkept⟩
  exact ⟨seg_cntList_arr hseg, hkept⟩

/-! ## Bounds on the numbers -/

/-- The product behind `filterWord`. -/
def KW (n U : ℕ) : ℕ := (n + 1) ^ 3 * (U + 1) * (RR n + 1) * (PmaxOf n + 1)

theorem filterWord_eq (n U : ℕ) : filterWord n U = 10 ^ 9 * (KW n U * KW n U) := by
  unfold filterWord KW; ring

theorem KW_ge (n U : ℕ) : (n + 1) ^ 3 ≤ KW n U ∧ U + 1 ≤ KW n U ∧ RR n + 1 ≤ KW n U ∧
    PmaxOf n + 1 ≤ KW n U := by
  have h1 : 1 ≤ (n + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ U + 1 := by omega
  have h3 : 1 ≤ RR n + 1 := by omega
  have h4 : 1 ≤ PmaxOf n + 1 := by omega
  unfold KW
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc (n + 1) ^ 3 = (n + 1) ^ 3 * 1 * 1 * 1 := by ring
      _ ≤ _ := by gcongr
  · calc U + 1 = 1 * (U + 1) * 1 * 1 := by ring
      _ ≤ _ := by gcongr
  · calc RR n + 1 = 1 * 1 * (RR n + 1) * 1 := by ring
      _ ≤ _ := by gcongr
  · calc PmaxOf n + 1 = 1 * 1 * 1 * (PmaxOf n + 1) := by ring
      _ ≤ _ := by gcongr

theorem le_filterWord {n U a : ℕ} (h : a ≤ 1000 * (KW n U * KW n U)) : a ≤ filterWord n U := by
  rw [filterWord_eq]; omega

theorem hOf_le (n U : ℕ) : hOf n U ≤ 3 * U := by
  unfold hOf BOf
  have : Nat.size (3 * U) ≤ 3 * U := Nat.size_le.2 Nat.lt_two_pow_self
  exact (Nat.div_le_self _ _).trans (by omega)

theorem mass_le {n s : ℕ} {AB BC AC : List ℤ} (A : ℕ → Bool) (M : ℕ) {g : ℕ} (hg : g < n * n) :
    mass n s AB BC AC A M g ≤ (n + s - 1) / s * s := by
  rw [mass_eq_sum _ _ hg]
  calc _ ≤ ∑ j ∈ Finset.range ((n + s - 1) / s), s := Finset.sum_le_sum fun j _ => by
        split_ifs
        · exact cntOf_le_s M _
        · exact Nat.zero_le _
    _ = _ := by simp

/-- The numbers that the host forms. -/
theorem word_facts {n U : ℕ} (hn : 1 ≤ n) :
    mOf n * sOf n + mOf n + 1 ≤ filterWord n U ∧
    (QOf n + hOf n U + 1) * (mOf n * sOf n + 1) ≤ filterWord n U ∧
    n * n * (mOf n * sOf n) + n * n + QOf n + 1 ≤ filterWord n U ∧
    PmaxOf n + 1 ≤ filterWord n U ∧
    LL n + n + sOf n ≤ filterWord n U ∧
    3 * U + 1 ≤ filterWord n U ∧
    4 * RR n + 2 ≤ filterWord n U := by
  obtain ⟨k1, k2, k3, k4⟩ := KW_ge n U
  have hs := sOf_le hn
  have hm := mOf_le n
  have hQ := QOf_lt n
  have hh := hOf_le n U
  set K := KW n U
  have hK : 1 ≤ K := by nlinarith [Nat.one_le_pow 3 (n + 1) (by omega)]
  have hn3 : (n + 1) ^ 3 = (n + 1) * (n + 1) * (n + 1) := by ring
  have hms : mOf n * sOf n ≤ n * n := Nat.mul_le_mul hm hs
  have hnn : n * n ≤ K := by nlinarith
  have hnK : n ≤ K := by nlinarith
  have hL : LL n ≤ K := by
    unfold LL
    calc mOf n * (n * n) ≤ n * (n * n) := Nat.mul_le_mul_right _ hm
      _ ≤ K := by nlinarith
  refine ⟨le_filterWord ?_, le_filterWord ?_, le_filterWord ?_, le_filterWord ?_, le_filterWord ?_,
    le_filterWord ?_, le_filterWord ?_⟩
  · nlinarith
  · have h1 : QOf n + hOf n U + 1 ≤ 6 * K := by omega
    have h2 : mOf n * sOf n + 1 ≤ 2 * K := by omega
    calc (QOf n + hOf n U + 1) * (mOf n * sOf n + 1) ≤ (6 * K) * (2 * K) := Nat.mul_le_mul h1 h2
      _ ≤ 1000 * (K * K) := by nlinarith
  · have h1 : n * n * (mOf n * sOf n) ≤ K * K := Nat.mul_le_mul hnn (hms.trans hnn)
    nlinarith
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith

/-! ## Keeping the memory -/

section keep

variable {x : AEInst} {fr : ℕ} {μ0 μ μ' : ℕ → ℤ} {act D : ℕ → Bool} {M : ℕ}

/-- Writes from `cnt` on keep the memory of the host. -/
theorem FMem.keep (h : FMem x fr μ0 μ act D) (hs : SameOn (· < aCNT x.n fr) μ μ') :
    FMem x fr μ0 μ' act D := by
  obtain ⟨_, _, _, _, _, _, _⟩ := layout x.n fr
  have hQ := QOf_lt x.n
  exact ⟨fun a ha => (hs a (by omega)).trans (h.kept a ha),
    h.pool.congr fun i hi => hs _ (by omega), h.act.congr fun i hi => hs _ (by omega),
    h.done.congr fun i hi => hs _ (by omega)⟩

theorem FMem.keepU (h : FMem x fr μ0 μ act D) (hs : SameOn (· < aUA x.n fr) μ μ') :
    FMem x fr μ0 μ' act D := by
  obtain ⟨_, _, _, _, _, _, _⟩ := layout x.n fr
  have hQ := QOf_lt x.n
  exact ⟨fun a ha => (hs a (by omega)).trans (h.kept a ha),
    h.pool.congr fun i hi => hs _ (by omega), h.act.congr fun i hi => hs _ (by omega),
    h.done.congr fun i hi => hs _ (by omega)⟩

theorem UOk.keep (h : UOk x fr μ act D M) (hs : SameOn (· < aCNT x.n fr) μ μ') :
    UOk x fr μ' act D M := fun g hg hD => by
  obtain ⟨_, _, _, _, _, _, _⟩ := layout x.n fr
  rw [hs _ (by omega)]
  exact h g hg hD

/-- The table of the masses at the moduli `M q`, for the first `t` primes of the pool. -/
def GOk (x : AEInst) (fr : ℕ) (μ : ℕ → ℤ) (act : ℕ → Bool) (M t : ℕ) : Prop :=
  ∀ t' < t, ∀ g < x.n * x.n, μ (aGT x.n fr + (t' * (x.n * x.n) + g)) =
    (mass x.n (sOf x.n) x.AB x.BC x.AC act (M * poolAt x.n t') g : ℤ)

end keep

/-! ## One step -/

/-- step(n, U, ab, bc, ac, s, pl, act, done, ua, cnt, gt, top, N, m, Q, h, M): the oracle at every
`M q`, the certificate, the choice of `q*`; it returns `M q*`.  Locals: 18 t, 19 scratch, 20 the
row `t*`. -/
def stepBody (pO pAggr pCert pArg pCopy : ℕ) : Stmt :=
  Stmt.for 18 (v 15) (
    .call pO [v 0, v 1, v 2, v 3, v 4, v 5, v 17 *' M (v 6 +' v 18), v 10, v 12] 19 ;;
    .call pAggr [v 10, v 7, v 11 +' v 18 *' v 13, v 13, v 14] 19) ;;
  .call pCert [v 9, v 11, v 8, v 13, v 15, v 16] 19 ;;
  .call pArg [v 11, v 8, v 13, v 15] 20 ;;
  .call pCopy [v 11 +' v 20 *' v 13, v 9, v 13] 19 ;;
  .set 0 (v 17 *' M (v 6 +' v 20))

/-- The arguments of step. -/
def stepArgs (x : AEInst) (fr M : ℕ) : List ℤ :=
  [x.n, x.U, x.ab, x.bc, x.ac, sOf x.n, aPL x.n fr, aACT x.n fr, aDONE x.n fr, aUA x.n fr,
    aCNT x.n fr, aGT x.n fr, aTOP x.n fr, ((x.n * x.n : ℕ) : ℤ), mOf x.n, QOf x.n, hOf x.n x.U, M]

/-- The time of step. -/
def tStep (To : List ℕ → ℕ) (n U : ℕ) : ℕ :=
  QOf n * (supTo To n U + tAggr (n * n) (mOf n) + 40) + tCert (n * n) (QOf n) +
    tArgmin (n * n) (QOf n) + copyTime (n * n) + 60

/-- The procedures that step calls. -/
structure StepProcs (P : Program) (pAggr pCert pArg pCopy : ℕ) : Prop where
  aggr : P[pAggr]? = some aggrBody
  cert : P[pCert]? = some certBody
  arg : P[pArg]? = some argminBody
  copy : P[pCopy]? = some copyBody

instance (n s U : ℕ) (AB BC AC : List ℤ) (act : ℕ → Bool) (M g : ℕ) :
    Decidable (certOf n s U AB BC AC act M g) := by
  unfold certOf; infer_instance

section step

variable {P₀ R : Program} {pO pAggr pCert pArg pCopy : ℕ} {To : List ℕ → ℕ}
  {needo : List ℕ → Need} {d0 : ℕ} {x : AEInst} {fr : ℕ} {μ0 : ℕ → ℤ}

set_option maxHeartbeats 400000 in
/-- One round of the loop over the pool: the oracle at `M q`, and the masses at `M q`. -/
theorem stepRound_spec (hsol : SolvesN oracleTask P₀ pO To needo)
    (HP : StepProcs (P₀ ++ R) pAggr pCert pArg pCopy) (E : Env lim d0 x fr μ0 needo) {d : ℕ}
    (hd : d ≤ d0 + 3) {act D : ℕ → Bool} {Mc : ℕ} (hM1 : 1 ≤ Mc)
    (hM : Mc * (2 * RR x.n) ≤ PmaxOf x.n) {t : ℕ} (ht : t < QOf x.n) (z : ℤ) {μ' : ℕ → ℤ}
    (hmem : FMem x fr μ0 μ' act D) (hU : UOk x fr μ' act D Mc) (hG : GOk x fr μ' act Mc t) :
    Ends lim (P₀ ++ R) d
      (.call pO [v 0, v 1, v 2, v 3, v 4, v 5, v 17 *' M (v 6 +' v 18), v 10, v 12] 19 ;;
        .call pAggr [v 10, v 7, v 11 +' v 18 *' v 13, v 13, v 14] 19)
      ⟨frame (setLocal (setLocal (stepArgs x fr Mc) 19 z) 18 t), μ'⟩
      (supTo To x.n x.U + tAggr (x.n * x.n) (mOf x.n) + 27) fun σ' =>
        FMem x fr μ0 σ'.mem act D ∧ UOk x fr σ'.mem act D Mc ∧ GOk x fr σ'.mem act Mc (t + 1) := by
  have hn := E.n_pos
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := layout x.n fr
  have hsp := E.space
  have hw := E.hw
  obtain ⟨w1, w2, w3, w4, w5, w6, w7⟩ := word_facts (U := x.U) hn
  have hword := E.word
  have hdep := E.depth
  have hQ := QOf_lt x.n
  have hpoolt := hmem.pool t ht
  obtain ⟨hq1, hq2, -⟩ := pool_bounds (poolAt_mem ht)
  have hR := RR_two_le x.n
  have hp : Mc * poolAt x.n t ≤ PmaxOf x.n :=
    le_trans (Nat.mul_le_mul_left Mc hq2.le) hM
  have hp1 : 1 ≤ Mc * poolAt x.n t := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hpZ : (Mc : ℤ) * (poolAt x.n t : ℤ) ≤ lim.word := by
    have : ((Mc * poolAt x.n t : ℕ) : ℤ) ≤ (filterWord x.n x.U : ℤ) := by exact_mod_cast (by omega)
    push_cast at this
    omega
  have hpZ0 : (0 : ℤ) ≤ (Mc : ℤ) * (poolAt x.n t : ℤ) := Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  have hLN : LL x.n = mOf x.n * (x.n * x.n) := rfl
  have htN : t * (x.n * x.n) + x.n * x.n ≤ 2 * RR x.n * (x.n * x.n) := by
    have := Nat.mul_le_mul_right (x.n * x.n) (show t + 1 ≤ 2 * RR x.n by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    exact this
  have htNZ : (0 : ℤ) ≤ (t : ℤ) * ((x.n : ℤ) * (x.n : ℤ)) := by positivity
  have htNZ' : (t : ℤ) * ((x.n : ℤ) * (x.n : ℤ)) + (x.n : ℤ) * (x.n : ℤ) ≤
      2 * (RR x.n : ℤ) * ((x.n : ℤ) * (x.n : ℤ)) := by exact_mod_cast htN
  simp only [stepArgs, setLocal]
  -- the oracle at M q
  light_call (oracle_call (R := R) hsol E (d := d + 1) (by omega) hmem.kept hp1 hp) using hpoolt
    with _ μ1 ⟨hcnt, hkb⟩
  -- the masses at M q
  have hs1 : SameOn (· < aCNT x.n fr) μ' μ1 := fun a ha => hkb a ⟨by omega, by omega⟩
  have hmem1 := hmem.keep hs1
  have hc : ∀ i < mOf x.n * (x.n * x.n),
      cntOf x.n (sOf x.n) (Mc * poolAt x.n t) x.AB x.BC x.AC i ≤ sOf x.n :=
    fun i _ => cntOf_le_s _ _
  have hcall := aggr_meets (lim := lim) (d := d + 1) HP.aggr (μ := μ1) (cnt := aCNT x.n fr)
    (act := aACT x.n fr) (dst := aGT x.n fr + t * (x.n * x.n)) (N := x.n * x.n) (m := mOf x.n)
    (cmax := sOf x.n) (A := act)
    (c := fun i => cntOf x.n (sOf x.n) (Mc * poolAt x.n t) x.AB x.BC x.AC i)
    hmem1.act hcnt hc (by unfold LL at *; omega) (by unfold LL at *; omega) (by omega)
    (by unfold LL at *; omega) (by unfold LL at *; omega) hw
    (le_trans (by exact_mod_cast (by unfold LL at *; omega)) hword)
  have htNw : (aGT x.n fr : ℤ) + (t : ℤ) * ((x.n : ℤ) * (x.n : ℤ)) ≤ lim.word := by
    have : ((aGT x.n fr + t * (x.n * x.n) : ℕ) : ℤ) ≤ lim.space := by exact_mod_cast (by omega)
    push_cast at this
    omega
  light_call hcall using htNZ, htNw with _ μ2 ⟨hgt, hso⟩
  have hs2 : SameOn (· < aCNT x.n fr) μ' μ2 := fun a ha =>
    (hso a (Or.inl (by omega))).trans (hs1 a ha)
  refine ⟨hmem.keep hs2, hU.keep hs2, fun t' ht' g hg => ?_⟩
  dsimp only
  rcases Nat.lt_succ_iff_lt_or_eq.1 ht' with ht' | rfl
  · have h1 : t' * (x.n * x.n) + g < t * (x.n * x.n) := by
      have := Nat.mul_le_mul_right (x.n * x.n) (show t' + 1 ≤ t by omega)
      rw [Nat.add_mul, Nat.one_mul] at this
      omega
    rw [hso _ (Or.inl (by omega)), hkb _ ⟨by omega, Or.inr (by omega)⟩]
    exact hG t' ht' g hg
  · have := hgt g hg
    rw [show aGT x.n fr + (t' * (x.n * x.n) + g) = aGT x.n fr + t' * (x.n * x.n) + g by ring, this,
      mass_eq_sum _ _ hg]
    rfl


/-- The flags after the certificate of a step at the modulus `Mc`. -/
def stepD (x : AEInst) (act D : ℕ → Bool) (Mc : ℕ) : ℕ → Bool := fun g =>
  D g || decide (∀ t < QOf x.n, hOf x.n x.U * mass x.n (sOf x.n) x.AB x.BC x.AC act Mc g <
    QOf x.n * mass x.n (sOf x.n) x.AB x.BC x.AC act (Mc * poolAt x.n t) g)

theorem stepD_iff (x : AEInst) (act D : ℕ → Bool) (Mc g : ℕ) :
    stepD x act D Mc g = true ↔
      (D g = true ∨ certOf x.n (sOf x.n) x.U x.AB x.BC x.AC act Mc g) := by
  simp [stepD, certOf]

/-- The remaining mass at the modulus `M`, outside the groups that are done. -/
def remMass (x : AEInst) (act D : ℕ → Bool) (M : ℕ) : ℕ :=
  ∑ g ∈ Finset.range (x.n * x.n), if D g then 0 else mass x.n (sOf x.n) x.AB x.BC x.AC act M g

set_option maxHeartbeats 800000 in
/-- **One step**: the certificate at `Mc`, and the choice of the prime `q*` of the pool that leaves
the least mass; it returns `Mc q*`. -/
theorem step_spec (hsol : SolvesN oracleTask P₀ pO To needo) {pStep : ℕ}
    (hS : (P₀ ++ R)[pStep]? = some (stepBody pO pAggr pCert pArg pCopy))
    (HP : StepProcs (P₀ ++ R) pAggr pCert pArg pCopy) (E : Env lim d0 x fr μ0 needo) {d : ℕ}
    (hd : d ≤ d0 + 3) {act D : ℕ → Bool} {Mc : ℕ} (hM1 : 1 ≤ Mc)
    (hM : Mc * (2 * RR x.n) ≤ PmaxOf x.n) {μ : ℕ → ℤ}
    (hmem : FMem x fr μ0 μ act D) (hU : UOk x fr μ act D Mc) :
    Meets lim (P₀ ++ R) pStep d (stepArgs x fr Mc) μ (tStep To x.n x.U) fun r μ' =>
      ∃ ts < QOf x.n, r = ((Mc * poolAt x.n ts : ℕ) : ℤ) ∧
        FMem x fr μ0 μ' act (stepD x act D Mc) ∧ UOk x fr μ' act (stepD x act D Mc) (Mc * poolAt x.n ts) ∧
        ∀ t < QOf x.n, remMass x act (stepD x act D Mc) (Mc * poolAt x.n ts) ≤
          remMass x act (stepD x act D Mc) (Mc * poolAt x.n t) := by
  have hn := E.n_pos
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := layout x.n fr
  have hsp := E.space
  have hw := E.hw
  obtain ⟨w1, w2, w3, w4, w5, w6, w7⟩ := word_facts (U := x.U) hn
  have hword := E.word
  have hdep := E.depth
  have hQ := QOf_lt x.n
  have hQ0 := QOf_pos x.n
  have hR := RR_two_le x.n
  have hQN : QOf x.n * (x.n * x.n) ≤ 2 * RR x.n * (x.n * x.n) := Nat.mul_le_mul_right _ hQ
  refine Meets.of_body hS ?_
  unfold stepBody tStep
  refine Ends.next (QOf x.n * (supTo To x.n x.U + tAggr (x.n * x.n) (mOf x.n) + 40) + 10)
    (Ends.forScratch [19] (fun t μ' => FMem x fr μ0 μ' act D ∧ UOk x fr μ' act D Mc ∧
      GOk x fr μ' act Mc t) (QOf x.n) (supTo To x.n x.U + tAggr (x.n * x.n) (mOf x.n) + 27)
      ⟨hmem, hU, fun _ h => absurd h (Nat.not_lt_zero _)⟩ ?round ?done ?bound (by simp) (by simp)
      (by omega) (by simp only [Expr.cost]; ring_nf; omega)) (by omega)
  case bound =>
    intro j loc' μ' hj _
    simp only [refreshLocals, stepArgs]
    light_side
  case round =>
    intro t loc' μ' ht ⟨hm, hu, hg⟩
    simp only [refreshLocals]
    exact stepRound_spec hsol HP E (by omega) hM1 hM ht (loc' 19) hm hu hg
  case done =>
    intro loc' μ1 ⟨hm1, hu1, hg1⟩
    simp only [refreshLocals, stepArgs, setLocal]
    have hmb : ∀ (A : ℕ → Bool) (M' g : ℕ), g < x.n * x.n →
        mass x.n (sOf x.n) x.AB x.BC x.AC A M' g ≤ mOf x.n * sOf x.n :=
      fun A M' g hg => mass_le A M' hg
    -- the certificate
    have hcert := cert_meets (lim := lim) (d := d + 1) HP.cert (μ := μ1) (ua := aUA x.n fr)
      (gt := aGT x.n fr) (done := aDONE x.n fr) (N := x.n * x.n) (Q := QOf x.n) (h := hOf x.n x.U)
      (vmax := mOf x.n * sOf x.n) (D := D)
      (Uv := fun g => mass x.n (sOf x.n) x.AB x.BC x.AC act Mc g)
      (Gv := fun t g => mass x.n (sOf x.n) x.AB x.BC x.AC act (Mc * poolAt x.n t) g)
      hm1.done hu1 hg1 (fun g hg => hmb _ _ g hg) (fun t _ g hg => hmb _ _ g hg)
      (by omega) (by omega) (by omega) (by omega) (by omega) hw
      (le_trans (by exact_mod_cast w2) hword)
    light_call hcert with _ μ2 ⟨hdone2, hso2⟩
    have hs2 : SameOn (fun b => b < aDONE x.n fr ∨ aUA x.n fr ≤ b) μ1 μ2 := fun b hb =>
      hso2 b (by rcases hb with hb | hb <;> [exact Or.inl hb; exact Or.inr (by omega)])
    have hm2 : FMem x fr μ0 μ2 act (stepD x act D Mc) :=
      ⟨fun a ha => (hs2 a (Or.inl (by omega))).trans (hm1.kept a ha),
        hm1.pool.congr fun i hi => hs2 _ (Or.inl (by omega)),
        hm1.act.congr fun i hi => hs2 _ (Or.inl (by unfold LL at *; omega)),
        fun g hg => (hdone2 g hg).trans rfl⟩
    have hg2 : GOk x fr μ2 act Mc (QOf x.n) := fun t ht g hg => by
      have : t * (x.n * x.n) + g < QOf x.n * (x.n * x.n) := by
        have := Nat.mul_le_mul_right (x.n * x.n) (show t + 1 ≤ QOf x.n by omega)
        rw [Nat.add_mul, Nat.one_mul] at this
        omega
      rw [hs2 _ (Or.inr (by omega))]
      exact hg1 t ht g hg
    -- the choice of q*
    have harg := argmin_meets (lim := lim) (d := d + 1) HP.arg (μ := μ2) (gt := aGT x.n fr)
      (done := aDONE x.n fr) (N := x.n * x.n) (Q := QOf x.n) (vmax := mOf x.n * sOf x.n)
      (D := stepD x act D Mc)
      (Gv := fun t g => mass x.n (sOf x.n) x.AB x.BC x.AC act (Mc * poolAt x.n t) g)
      hm2.done hg2 (fun t _ g hg => hmb _ _ g hg) (by omega) (by omega) hw
      (le_trans (by exact_mod_cast w3) hword)
    light_call harg with _ μ3 ⟨h32, ts, rfl, hts⟩
    rw [h32]
    obtain ⟨hts, hmin⟩ := hts hQ0
    -- the masses at Mc q*
    have htsN : ts * (x.n * x.n) + x.n * x.n ≤ QOf x.n * (x.n * x.n) := by
      have := Nat.mul_le_mul_right (x.n * x.n) (show ts + 1 ≤ QOf x.n by omega)
      rw [Nat.add_mul, Nat.one_mul] at this
      exact this
    have htsZ : (0 : ℤ) ≤ (ts : ℤ) * ((x.n : ℤ) * (x.n : ℤ)) := by positivity
    have htsw : (aGT x.n fr : ℤ) + (ts : ℤ) * ((x.n : ℤ) * (x.n : ℤ)) ≤ lim.word := by
      have : ((aGT x.n fr + ts * (x.n * x.n) : ℕ) : ℤ) ≤ lim.space := by exact_mod_cast (by omega)
      push_cast at this
      omega
    have hcopy := copy_meets (lim := lim) (d := d + 1) HP.copy (μ := μ2)
      (src := aGT x.n fr + ts * (x.n * x.n)) (dst := aUA x.n fr) (n := x.n * x.n) hw
      (by omega) (by omega) (by omega)
    light_call hcopy using htsZ, htsw with _ μ4 ⟨hcp, hso4⟩
    have hs4 : SameOn (· < aUA x.n fr) μ2 μ4 := fun b hb => hso4 b (Or.inl hb)
    have hpts := hm2.pool ts hts
    obtain ⟨hq1, hq2, -⟩ := pool_bounds (poolAt_mem hts)
    have hp : Mc * poolAt x.n ts ≤ PmaxOf x.n := le_trans (Nat.mul_le_mul_left Mc hq2.le) hM
    have hpZ : (Mc : ℤ) * (poolAt x.n ts : ℤ) ≤ lim.word := by
      have : ((Mc * poolAt x.n ts : ℕ) : ℤ) ≤ (filterWord x.n x.U : ℤ) := by
        exact_mod_cast (by omega)
      push_cast at this
      omega
    have hpZ0 : (0 : ℤ) ≤ (Mc : ℤ) * (poolAt x.n ts : ℤ) :=
      Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    light_set ((Mc * poolAt x.n ts : ℕ) : ℤ) using hs4 _ (show aPL x.n fr + ts < aUA x.n fr by omega),
      hpts
    refine ⟨ts, hts, by simp, ?_, ?_, ?_⟩
    · exact hm2.keepU hs4
    · intro g hg _
      dsimp only
      rw [hcp g hg, show aGT x.n fr + ts * (x.n * x.n) + g = aGT x.n fr + (ts * (x.n * x.n) + g) by
        ring]
      exact hg2 ts hts g hg
    · intro t ht
      exact hmin t ht

end step

end Light.Filter2
