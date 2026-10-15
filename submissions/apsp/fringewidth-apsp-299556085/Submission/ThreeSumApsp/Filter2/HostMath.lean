/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Filter2.Mass
public import Submission.ThreeSumApsp.Lang.Lib.Sieve
public import Mathlib.NumberTheory.Bertrand

/-!
# The filtering host: the pure arithmetic

* `Arr`: an array of the memory, given by a function.
* `poolL`: the pool as a list (the primes of `[R, 2R)` in ascending order); it is never empty
  (Bertrand's postulate).
* The mass of a group as a sum over the blocks (`mass_eq_sum`); the total mass `tot` and the number
  `cardA` of active candidates.
* The step of a round (`step_contract`), the end of a round (`card_filter_le_tot`), and the count
  of the candidates (`card_lt_two_pow`).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Filter2

open ThreeSumApsp.Spec

/-! ## Arrays -/

/-- The `L` cells from `a` hold `f 0, …, f (L - 1)`. -/
def Arr (μ : ℕ → ℤ) (a L : ℕ) (f : ℕ → ℤ) : Prop := ∀ i < L, μ (a + i) = f i

theorem Arr.congr {μ μ' : ℕ → ℤ} {a L : ℕ} {f : ℕ → ℤ} (h : Arr μ a L f)
    (he : ∀ i < L, μ' (a + i) = μ (a + i)) : Arr μ' a L f := fun i hi => (he i hi).trans (h i hi)

theorem Arr.ext {μ : ℕ → ℤ} {a L : ℕ} {f f' : ℕ → ℤ} (h : Arr μ a L f)
    (he : ∀ i < L, f i = f' i) : Arr μ a L f' := fun i hi => (h i hi).trans (he i hi)

/-- A truth value as a number. -/
def bitB (b : Bool) : ℤ := if b then 1 else 0

@[simp] theorem bitB_true : bitB true = 1 := rfl
@[simp] theorem bitB_false : bitB false = 0 := rfl

theorem bitB_nonneg (b : Bool) : 0 ≤ bitB b := by cases b <;> simp
theorem bitB_le_one (b : Bool) : bitB b ≤ 1 := by cases b <;> simp
theorem bitB_eq_zero {b : Bool} : bitB b = 0 ↔ b = false := by cases b <;> simp
theorem bitB_eq_one {b : Bool} : bitB b = 1 ↔ b = true := by cases b <;> simp

/-! ## Parameters -/

theorem ellOf_pos (n : ℕ) : 1 ≤ ellOf n := by unfold ellOf; omega

theorem RR_two_le (n : ℕ) : 2 ≤ RR n := by
  unfold RR
  calc 2 = 2 ^ 1 := rfl
    _ ≤ 2 ^ ellOf n := Nat.pow_le_pow_right (by norm_num) (ellOf_pos n)

theorem dOf_pos (n : ℕ) : 1 ≤ dOf n := by
  unfold dOf bOf
  have h1 := ellOf_pos n
  have h2 : ellOf n * (Nat.sqrt (ellOf n) + 1) ≥ 1 * 2 :=
    Nat.mul_le_mul h1 (by have := Nat.sqrt_pos.2 h1; omega)
  omega

theorem sOf_pos (n : ℕ) : 1 ≤ sOf n := Nat.one_le_two_pow

theorem sOf_le {n : ℕ} (hn : 1 ≤ n) : sOf n ≤ n := by
  have hk : 1 ≤ kOf n := Nat.size_pos.2 hn
  have he : 336175 * kOf n / 10 ^ 7 < kOf n := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num)]
    omega
  unfold sOf
  calc 2 ^ (336175 * kOf n / 10 ^ 7) ≤ 2 ^ (kOf n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ ≤ n := by
      have := Nat.lt_size.1 (show kOf n - 1 < Nat.size n from by unfold kOf at hk ⊢; omega)
      exact this

theorem mOf_le (n : ℕ) : mOf n ≤ n := by
  unfold mOf
  have hs := sOf_pos n
  have : (n + sOf n - 1) / sOf n < n + 1 := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    have : n ≤ n * sOf n := Nat.le_mul_of_pos_right n hs
    rw [Nat.add_mul, Nat.one_mul]
    omega
  omega

theorem mOf_mul_le (n : ℕ) : mOf n * (n * n) ≤ n * (n * n) := Nat.mul_le_mul_right _ (mOf_le n)

/-- A block below `m = ⌈n/s⌉` starts below `n`. -/
theorem mul_sOf_lt {n j : ℕ} (hj : j < mOf n) : j * sOf n < n := by
  have hs := sOf_pos n
  unfold mOf at hj
  have h1 : (j + 1) * sOf n ≤ n + sOf n - 1 := by
    have := (Nat.le_div_iff_mul_le hs).1 (show j + 1 ≤ (n + sOf n - 1) / sOf n by omega)
    exact this
  rw [Nat.add_mul, Nat.one_mul] at h1
  omega

/-- The block of a vertex `c < n` is below `m`. -/
theorem div_sOf_lt {n c : ℕ} (hc : c < n) : c / sOf n < mOf n := by
  have hs := sOf_pos n
  unfold mOf
  rw [← Nat.add_one_le_iff, Nat.le_div_iff_mul_le hs, Nat.add_mul, Nat.one_mul]
  have := Nat.div_mul_le_self c (sOf n)
  omega

/-! ## The pool as a list -/

/-- The pool: the primes of `[R, 2R)` in ascending order. -/
def poolL (n : ℕ) : List ℕ := (Sieve.primesBelow (2 * RR n)).filter fun q => decide (RR n ≤ q)

theorem mem_poolL {n q : ℕ} : q ∈ poolL n ↔ q ∈ pool n := by
  simp only [poolL, Sieve.primesBelow, List.mem_filter, List.mem_range, decide_eq_true_eq, pool,
    Finset.mem_filter, Finset.mem_range]
  tauto

theorem nodup_poolL (n : ℕ) : (poolL n).Nodup :=
  (List.nodup_range.filter _).filter _

theorem length_poolL (n : ℕ) : (poolL n).length = QOf n := by
  rw [QOf, ← List.toFinset_card_of_nodup (nodup_poolL n)]
  congr 1
  ext q
  simp [mem_poolL]

theorem QOf_pos (n : ℕ) : 0 < QOf n := by
  have hR := RR_two_le n
  obtain ⟨p, hp, h1, h2⟩ := Nat.exists_prime_lt_and_le_two_mul (RR n) (by omega)
  have hne : p ≠ 2 * RR n := by
    rintro rfl
    exact Nat.not_prime_mul (by norm_num) (by omega) hp
  exact Finset.card_pos.2 ⟨p, Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), by omega, hp⟩⟩

theorem poolL_get_mem {n t : ℕ} (ht : t < QOf n) :
    (poolL n)[t]'(by rw [length_poolL]; exact ht) ∈ pool n :=
  mem_poolL.1 (List.getElem_mem _)

theorem pool_bounds {n q : ℕ} (hq : q ∈ pool n) : RR n ≤ q ∧ q < 2 * RR n ∧ q.Prime := by
  simp only [pool, Finset.mem_filter, Finset.mem_range] at hq
  exact ⟨hq.2.1, hq.1, hq.2.2⟩

/-- The pool, read with a default. -/
def poolAt (n t : ℕ) : ℕ := (poolL n).getD t 0

theorem poolAt_mem {n t : ℕ} (ht : t < QOf n) : poolAt n t ∈ pool n := by
  unfold poolAt
  rw [List.getD_eq_getElem _ _ (by rw [length_poolL]; exact ht)]
  exact poolL_get_mem ht

theorem exists_poolAt {n q : ℕ} (hq : q ∈ pool n) : ∃ t < QOf n, poolAt n t = q := by
  obtain ⟨t, ht, he⟩ := List.getElem_of_mem (mem_poolL.2 hq)
  refine ⟨t, by rw [← length_poolL]; exact ht, ?_⟩
  unfold poolAt
  rw [List.getD_eq_getElem _ _ ht, he]

theorem QOf_lt (n : ℕ) : QOf n ≤ 2 * RR n := by
  unfold QOf pool
  exact (Finset.card_filter_le _ _).trans (by simp)

/-! ## Masses as sums over the blocks -/

theorem sum_filter_mod_eq (m N g : ℕ) (hg : g < N) (P : ℕ → Bool) (f : ℕ → ℕ) :
    ∑ i ∈ (Finset.range (m * N)).filter (fun i => P i = true ∧ i % N = g), f i =
      ∑ j ∈ Finset.range m, if P (j * N + g) then f (j * N + g) else 0 := by
  rw [Finset.sum_filter]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    rw [Finset.sum_eq_single g]
    · have : (m * N + g) % N = g := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hg]
      by_cases hP : P (m * N + g) <;> simp [this, hP]
    · intro x hx hxg
      have : (m * N + x) % N = x := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (Finset.mem_range.1 hx)]
      simp [this, hxg]
    · intro h
      exact absurd (Finset.mem_range.2 hg) h

variable {n s U : ℕ} {AB BC AC : List ℤ}

/-- The mass of a group, block by block. -/
theorem mass_eq_sum (A : ℕ → Bool) (M : ℕ) {g : ℕ} (hg : g < n * n) :
    mass n s AB BC AC A M g = ∑ j ∈ Finset.range ((n + s - 1) / s),
      if A (j * (n * n) + g) then cntOf n s M AB BC AC (j * (n * n) + g) else 0 :=
  sum_filter_mod_eq _ _ g hg A _

theorem mod_block {N j g : ℕ} (hg : g < N) : (j * N + g) % N = g := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hg]

theorem div_block {N j g : ℕ} (hg : g < N) : (j * N + g) / N = j := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hg, Nat.zero_add]

/-- The total mass of the active candidates. -/
def tot (n s : ℕ) (AB BC AC : List ℤ) (A : ℕ → Bool) (M : ℕ) : ℕ :=
  ∑ g ∈ Finset.range (n * n), mass n s AB BC AC A M g

/-- The number of active candidates. -/
def cardA (n s : ℕ) (A : ℕ → Bool) : ℕ :=
  ∑ g ∈ Finset.range (n * n), ∑ j ∈ Finset.range ((n + s - 1) / s),
    if A (j * (n * n) + g) then 1 else 0

/-- The candidates of the groups that are not done, among those that are marked active. -/
def eff (N : ℕ) (act D : ℕ → Bool) : ℕ → Bool := fun i => act i && !D (i % N)

theorem mass_eff {act D : ℕ → Bool} (M : ℕ) {g : ℕ} (hg : g < n * n) :
    mass n s AB BC AC (eff (n * n) act D) M g =
      if D g then 0 else mass n s AB BC AC act M g := by
  rw [mass_eq_sum _ _ hg, mass_eq_sum _ _ hg]
  by_cases hD : D g
  · simp [eff, mod_block hg, hD]
  · simp [eff, mod_block hg, hD]

theorem tot_le_s (A : ℕ → Bool) (M : ℕ) : tot n s AB BC AC A M ≤ s * cardA n s A := by
  unfold tot cardA
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun g hg => ?_
  rw [mass_eq_sum _ _ (Finset.mem_range.1 hg), Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  split_ifs
  · simpa using cntOf_le_s M _
  · simp

theorem card_filter_le_tot (A : ℕ → Bool) (M : ℕ) :
    cardA n s (fun i => A i && decide (0 < cntOf n s M AB BC AC i)) ≤ tot n s AB BC AC A M := by
  unfold tot cardA
  refine Finset.sum_le_sum fun g hg => ?_
  rw [mass_eq_sum _ _ (Finset.mem_range.1 hg)]
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases hA : A (j * (n * n) + g) <;> by_cases hc : 0 < cntOf n s M AB BC AC (j * (n * n) + g) <;>
    simp [hA, hc] <;> omega

theorem cardA_true : cardA n s (fun _ => true) = n * n * ((n + s - 1) / s) := by
  simp [cardA]

theorem cardA_eq_zero {A : ℕ → Bool} (h : cardA n s A = 0) {g j : ℕ} (hg : g < n * n)
    (hj : j < (n + s - 1) / s) : A (j * (n * n) + g) = false := by
  unfold cardA at h
  have h1 := (Finset.sum_eq_zero_iff.1 h) g (Finset.mem_range.2 hg)
  have h2 := (Finset.sum_eq_zero_iff.1 h1) j (Finset.mem_range.2 hj)
  by_contra hA
  simp [hA] at h2

theorem cardA_mono {A A' : ℕ → Bool} (h : ∀ i, A i = true → A' i = true) :
    cardA n s A ≤ cardA n s A' := by
  unfold cardA
  refine Finset.sum_le_sum fun g _ => Finset.sum_le_sum fun j _ => ?_
  by_cases hA : A (j * (n * n) + g)
  · simp [hA, h _ hA]
  · simp [hA]

/-! ## Witnesses -/

theorem witness_of_cnt0 {i : ℕ} (h : 0 < cntOf n s 0 AB BC AC i) :
    ∃ c < n, triSum n AB BC AC (i % (n * n)) c = 0 := by
  unfold cntOf at h
  obtain ⟨c, hc⟩ := Finset.card_pos.1 h
  simp only [Finset.mem_filter, Finset.mem_range, Nat.cast_zero, zero_dvd_iff] at hc
  exact ⟨c, hc.1, hc.2.2⟩

theorem witness_of_mass0 {A : ℕ → Bool} {g : ℕ} (h : 0 < mass n s AB BC AC A 0 g) :
    ∃ c < n, triSum n AB BC AC g c = 0 := by
  unfold mass at h
  obtain ⟨i, hi, hpos⟩ := Finset.exists_ne_zero_of_sum_ne_zero h.ne'
  simp only [Finset.mem_filter] at hi
  obtain ⟨c, hc, he⟩ := witness_of_cnt0 (Nat.pos_of_ne_zero hpos)
  rw [hi.2.2] at he
  exact ⟨c, hc, he⟩

theorem cnt0_of_witness {g c : ℕ} (hs : 1 ≤ s) (hg : g < n * n) (hc : c < n)
    (h : triSum n AB BC AC g c = 0) :
    0 < cntOf n s 0 AB BC AC ((c / s) * (n * n) + g) := by
  unfold cntOf
  refine Finset.card_pos.2 ⟨c, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_range, Nat.cast_zero, zero_dvd_iff, div_block hg,
    mod_block hg]
  refine ⟨hc, ⟨Nat.div_mul_le_self c s, ?_, hc⟩, h⟩
  rw [Nat.add_mul, Nat.one_mul]
  have := Nat.lt_div_mul_add (a := c) hs
  omega

/-! ## The step of a round -/

/-- The certificate of the group `g`, from the counts `act` at the moduli `M` and `M q`. -/
def certOf (n s U : ℕ) (AB BC AC : List ℤ) (act : ℕ → Bool) (M g : ℕ) : Prop :=
  ∀ t < QOf n, hOf n U * mass n s AB BC AC act M g < QOf n * mass n s AB BC AC act (M * poolAt n t) g

/-- **Soundness of the certificate**: a certified group has an exact witness. -/
theorem witness_of_certOf (hAB : AbsLe AB U) (hBC : AbsLe BC U) (hAC : AbsLe AC U)
    {act : ℕ → Bool} {M g : ℕ} (h : certOf n s U AB BC AC act M g) :
    ∃ c < n, triSum n AB BC AC g c = 0 := by
  refine witness_of_mass0 (s := s) (A := act)
    (exists_witness_of_certified (s := s) (M := M) hAB hBC hAC (QOf_pos n) ?_)
  intro q hq
  obtain ⟨t, ht, rfl⟩ := exists_poolAt hq
  exact h t ht

/-- **The contraction of a step**: after the certification (`D'`) and the choice of the prime
`poolAt n ts`, which minimizes the remaining mass, the total mass shrinks by `2h/Q`. -/
theorem step_contract (hAB : AbsLe AB U) (hBC : AbsLe BC U) (hAC : AbsLe AC U)
    {act D D' : ℕ → Bool} {M ts : ℕ}
    (hD' : ∀ g < n * n, D' g = true ↔ (D g = true ∨ certOf n s U AB BC AC act M g))
    (hts : ts < QOf n)
    (hmin : ∀ t < QOf n,
      (∑ g ∈ Finset.range (n * n), if D' g then 0 else mass n s AB BC AC act (M * poolAt n ts) g) ≤
        ∑ g ∈ Finset.range (n * n), if D' g then 0 else mass n s AB BC AC act (M * poolAt n t) g) :
    QOf n * tot n s AB BC AC (eff (n * n) act D') (M * poolAt n ts) ≤
      2 * hOf n U * tot n s AB BC AC (eff (n * n) act D) M := by
  set Rem := (Finset.range (n * n)).filter fun g => D' g = false with hRem
  have hsum : ∀ (X : ℕ) (f : ℕ → ℕ), (∑ g ∈ Finset.range (n * n), if D' g then 0 else f g) =
      ∑ g ∈ Rem, f g := by
    intro X f
    rw [hRem, Finset.sum_filter]
    refine Finset.sum_congr rfl fun g _ => ?_
    cases D' g <;> simp
  have htot : ∀ (E : ℕ → Bool) (X : ℕ), tot n s AB BC AC (eff (n * n) act E) X =
      ∑ g ∈ Finset.range (n * n), if E g then 0 else mass n s AB BC AC act X g := by
    intro E X
    unfold tot
    exact Finset.sum_congr rfl fun g hg => mass_eff X (Finset.mem_range.1 hg)
  have hcon := contract (A := act) (M := M) (Rem := Rem) (qs := poolAt n ts) hAB hBC hAC
    (fun g hg => by
      simp only [hRem, Finset.mem_filter, Finset.mem_range] at hg
      have hnot : ¬ certOf n s U AB BC AC act M g := fun hc => by
        have := (hD' g hg.1).2 (Or.inr hc)
        rw [hg.2] at this
        exact Bool.false_ne_true this
      unfold certOf at hnot
      push Not at hnot
      obtain ⟨t, ht, hle⟩ := hnot
      exact ⟨poolAt n t, poolAt_mem ht, hle⟩)
    (poolAt_mem hts)
    (fun q hq => by
      obtain ⟨t, ht, rfl⟩ := exists_poolAt hq
      have := hmin t ht
      rwa [hsum 0, hsum 0] at this)
  rw [htot, htot, hsum 0]
  refine hcon.trans (Nat.mul_le_mul_left _ ?_)
  rw [hRem, Finset.sum_filter]
  refine Finset.sum_le_sum fun g hg => ?_
  have hg' := Finset.mem_range.1 hg
  by_cases hD : D g
  · have : D' g = true := (hD' g hg').2 (Or.inl hD)
    simp [hD, this]
  · cases D' g <;> simp [hD]

/-! ## Rounds -/

theorem pow_step {Q h t a b c : ℕ} (h1 : Q * b ≤ 2 * h * a) (h2 : Q ^ t * a ≤ (2 * h) ^ t * c) :
    Q ^ (t + 1) * b ≤ (2 * h) ^ (t + 1) * c :=
  calc Q ^ (t + 1) * b = Q ^ t * (Q * b) := by ring
    _ ≤ Q ^ t * (2 * h * a) := Nat.mul_le_mul_left _ h1
    _ = 2 * h * (Q ^ t * a) := by ring
    _ ≤ 2 * h * ((2 * h) ^ t * c) := Nat.mul_le_mul_left _ h2
    _ = (2 * h) ^ (t + 1) * c := by ring

/-- With the guard, a round shrinks the number of active candidates by `2^d`. -/
theorem guard_step {Q h s r d a0 a1 : ℕ} (hQ : 0 < Q) (hG : s * (2 * h) ^ r * 2 ^ d ≤ Q ^ r)
    (ha : Q ^ r * a1 ≤ (2 * h) ^ r * (s * a0)) : 2 ^ d * a1 ≤ a0 := by
  have hpos : 0 < Q ^ r := Nat.pow_pos hQ
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  calc Q ^ r * (2 ^ d * a1) = 2 ^ d * (Q ^ r * a1) := by ring
    _ ≤ 2 ^ d * ((2 * h) ^ r * (s * a0)) := Nat.mul_le_mul_left _ ha
    _ = s * (2 * h) ^ r * 2 ^ d * a0 := by ring
    _ ≤ Q ^ r * a0 := Nat.mul_le_mul_right _ hG

/-- There are fewer candidates than `2^{d · rounds}`. -/
theorem card_lt_two_pow (n : ℕ) : n * n * mOf n < 2 ^ (dOf n * roundsOf n) := by
  have hd := dOf_pos n
  have hn : n < 2 ^ kOf n := Nat.lt_size_self n
  have h3 : n * n * mOf n ≤ n * n * n := Nat.mul_le_mul_left _ (mOf_le n)
  have hcube : n * n * n < 2 ^ kOf n * 2 ^ kOf n * 2 ^ kOf n := by
    have h1 : n * n < 2 ^ kOf n * 2 ^ kOf n := Nat.mul_lt_mul'' hn hn
    exact Nat.mul_lt_mul'' h1 hn
  have hpow : 2 ^ kOf n * 2 ^ kOf n * 2 ^ kOf n ≤ 2 ^ (dOf n * roundsOf n) := by
    rw [← pow_add, ← pow_add]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    have := Nat.lt_mul_div_succ (3 * kOf n) (show 0 < dOf n by omega)
    unfold roundsOf
    omega
  omega

end Light.Filter2
