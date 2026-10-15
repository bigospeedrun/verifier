/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Filter2.Defs
public import Mathlib.Algebra.BigOperators.Associated

/-!
# The arithmetic of the filtering (Lemma 3.1)

For an active set `A` (a predicate on candidates `i < L`, `L = m n²`) and a modulus `M`, the mass of
the group `g` is `mass A M g = Σ_{i < L, A i, i % n² = g} cnt_M(i)`.  The count at modulus `0` is the
number of exact witnesses (`(0 : ℤ) ∣ v ↔ v = 0`).

* `sum_pool_cntOf_le` (3.2): summed over the pool, the counts at `M q` are at most `Q` times the
  exact witnesses plus `h` times the count at `M`.
* `exists_witness_of_certified` (3.3): a certified group has an exact witness.
* `contract` : with one prime `q*` minimizing the remaining mass, the remaining mass shrinks by
  `2h/Q`.
* `cntOf_pos_of_zero_pos`: an exact witness is counted at every modulus.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Filter2

open ThreeSumApsp.Spec

variable {n s U : ℕ} {AB BC AC : List ℤ}

/-- The mass of the group `g` over the active candidates `A` at the modulus `M`. -/
def mass (n s : ℕ) (AB BC AC : List ℤ) (A : ℕ → Bool) (M g : ℕ) : ℕ :=
  ∑ i ∈ (Finset.range ((n + s - 1) / s * (n * n))).filter (fun i => A i = true ∧ i % (n * n) = g),
    cntOf n s M AB BC AC i

/-- The triangle sums are below `2^B` in absolute value. -/
theorem natAbs_triSum_lt (hAB : AbsLe AB U) (hBC : AbsLe BC U) (hAC : AbsLe AC U) (q c : ℕ) :
    (triSum n AB BC AC q c).natAbs < 2 ^ BOf U := by
  have hg : ∀ {l : List ℤ}, AbsLe l (U : ℤ) → ∀ k, |l.getD k 0| ≤ (U : ℤ) := by
    intro l hl k
    rw [List.getD_eq_getElem?_getD]
    rcases h : l[k]? with _ | x
    · simp
    · exact hl x (List.mem_of_getElem? h)
  have h1 := hg hAB q
  have h2 := hg hBC (q % n * n + c)
  have h3 := hg hAC (q / n * n + c)
  have habs : |triSum n AB BC AC q c| ≤ 3 * (U : ℤ) := by
    unfold triSum
    calc _ ≤ |AB.getD q 0 + BC.getD (q % n * n + c) 0| + |AC.getD (q / n * n + c) 0| :=
          abs_add_le _ _
      _ ≤ |AB.getD q 0| + |BC.getD (q % n * n + c) 0| + |AC.getD (q / n * n + c) 0| := by
          gcongr; exact abs_add_le _ _
      _ ≤ _ := by linarith
  have h3U : (triSum n AB BC AC q c).natAbs ≤ 3 * U := by
    have : ((triSum n AB BC AC q c).natAbs : ℤ) ≤ ((3 * U : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs]; push_cast; exact habs
    exact_mod_cast this
  exact lt_of_le_of_lt h3U (Nat.lt_size_self _)

/-- An exact witness is counted at every modulus. -/
theorem cntOf_pos_of_zero_pos {M i : ℕ} (h : 0 < cntOf n s 0 AB BC AC i) :
    0 < cntOf n s M AB BC AC i := by
  unfold cntOf at h ⊢
  refine lt_of_lt_of_le h (Finset.card_le_card fun c hc => ?_)
  simp only [Finset.mem_filter] at hc ⊢
  refine ⟨hc.1, hc.2.1, ?_⟩
  have := hc.2.2
  rw [Nat.cast_zero, zero_dvd_iff] at this
  rw [this]; exact dvd_zero _

/-- A nonzero integer below `2^B` has at most `h` prime divisors in the pool. -/
theorem card_pool_dvd_le {v : ℤ} (hv : v ≠ 0) (hB : v.natAbs < 2 ^ BOf U) :
    ((pool n).filter fun q : ℕ => (q : ℤ) ∣ v).card ≤ hOf n U := by
  set S := (pool n).filter fun q : ℕ => (q : ℤ) ∣ v
  have hmem : ∀ q ∈ S, q.Prime ∧ RR n ≤ q ∧ q ∣ v.natAbs := by
    intro q hq
    simp only [S, pool, Finset.mem_filter, Finset.mem_range] at hq
    exact ⟨hq.1.2.2, hq.1.2.1, Int.natCast_dvd.1 hq.2⟩
  have hdvd : ∏ q ∈ S, q ∣ v.natAbs :=
    Finset.prod_primes_dvd _ (fun q hq => (hmem q hq).1.prime) fun q hq => (hmem q hq).2.2
  have hpos : 0 < v.natAbs := Int.natAbs_pos.2 hv
  have hle : RR n ^ S.card ≤ ∏ q ∈ S, q := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod' fun q hq => (hmem q hq).2.1
  have hlt : 2 ^ (ellOf n * S.card) < 2 ^ BOf U := by
    rw [pow_mul]
    exact lt_of_le_of_lt (hle.trans (Nat.le_of_dvd hpos hdvd)) hB
  have hexp := (Nat.pow_lt_pow_iff_right (by norm_num)).1 hlt
  have hell : 0 < ellOf n := Nat.succ_pos _
  unfold hOf
  rw [Nat.le_div_iff_mul_le hell]
  rw [mul_comm] at hexp
  omega

/-- A count as a sum of indicators over the block. -/
theorem cntOf_eq_sum (P i : ℕ) :
    cntOf n s P AB BC AC i = ∑ c ∈ (Finset.range n).filter (fun c => InBlock n s (i / (n * n)) c),
      if (P : ℤ) ∣ triSum n AB BC AC (i % (n * n)) c then 1 else 0 := by
  unfold cntOf
  rw [← Finset.card_filter, Finset.filter_filter]

/-- The count at `0` is at most the count at any modulus. -/
theorem cntOf_zero_le (M i : ℕ) : cntOf n s 0 AB BC AC i ≤ cntOf n s M AB BC AC i := by
  rw [cntOf_eq_sum, cntOf_eq_sum]
  refine Finset.sum_le_sum fun c _ => ?_
  split_ifs with h1 h2 <;> try omega
  rw [Nat.cast_zero, zero_dvd_iff] at h1
  exact absurd (h1 ▸ dvd_zero _) h2

/-- The mass at `0` is at most the mass at any modulus. -/
theorem mass_zero_le (A : ℕ → Bool) (M g : ℕ) :
    mass n s AB BC AC A 0 g ≤ mass n s AB BC AC A M g :=
  Finset.sum_le_sum fun i _ => cntOf_zero_le M i

/-- The pool primes `q` with `M q ∣ v`, for a `v` below `2^B`. -/
theorem card_pool_mul_dvd_le {v : ℤ} (hB : v.natAbs < 2 ^ BOf U) (M : ℕ) :
    ((pool n).filter fun q : ℕ => ((M * q : ℕ) : ℤ) ∣ v).card ≤
      QOf n * (if (0 : ℤ) ∣ v then 1 else 0) + hOf n U * (if (M : ℤ) ∣ v then 1 else 0) := by
  by_cases hv : v = 0
  · subst hv
    rw [if_pos (dvd_zero _), if_pos (dvd_zero _)]
    exact le_trans (Finset.card_filter_le _ _) (by unfold QOf; omega)
  have h0 : ¬ (0 : ℤ) ∣ v := by rwa [zero_dvd_iff]
  rw [if_neg h0]
  by_cases hM : (M : ℤ) ∣ v
  · rw [if_pos hM]
    obtain ⟨w, hw⟩ := hM
    have hM0 : M ≠ 0 := by rintro rfl; simp at hw; exact hv hw
    have hw0 : w ≠ 0 := by rintro rfl; simp at hw; exact hv hw
    have hwB : w.natAbs < 2 ^ BOf U := by
      refine lt_of_le_of_lt ?_ hB
      rw [hw, Int.natAbs_mul]
      exact Nat.le_mul_of_pos_left _ (by simp; omega)
    refine le_trans (Finset.card_le_card fun q hq => ?_) (le_trans (card_pool_dvd_le (n := n) hw0 hwB) ?_)
    · simp only [Finset.mem_filter] at hq ⊢
      refine ⟨hq.1, ?_⟩
      rw [hw, Nat.cast_mul] at hq
      exact (Int.dvd_of_mul_dvd_mul_left (by exact_mod_cast hM0) hq.2)
    · omega
  · rw [if_neg hM]
    simp only [mul_zero, add_zero, Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro q _ hq
    exact hM (dvd_trans (by push_cast; exact dvd_mul_right _ _) hq)

/-- **(3.2)**, for one candidate: `Σ_{q ∈ P} cnt_{Mq}(i) ≤ Q · cnt_0(i) + h · cnt_M(i)`. -/
theorem sum_pool_cntOf_le (hAB : AbsLe AB U) (hBC : AbsLe BC U) (hAC : AbsLe AC U) (M i : ℕ) :
    ∑ q ∈ pool n, cntOf n s (M * q) AB BC AC i ≤
      QOf n * cntOf n s 0 AB BC AC i + hOf n U * cntOf n s M AB BC AC i := by
  simp_rw [cntOf_eq_sum]
  rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun c _ => ?_
  rw [Finset.sum_boole]
  exact card_pool_mul_dvd_le (natAbs_triSum_lt hAB hBC hAC _ _) M

/-- **(3.2)**, for a group. -/
theorem sum_pool_mass_le (hAB : AbsLe AB U) (hBC : AbsLe BC U) (hAC : AbsLe AC U)
    (A : ℕ → Bool) (M g : ℕ) :
    ∑ q ∈ pool n, mass n s AB BC AC A (M * q) g ≤
      QOf n * mass n s AB BC AC A 0 g + hOf n U * mass n s AB BC AC A M g := by
  unfold mass
  rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => sum_pool_cntOf_le hAB hBC hAC M i

/-- **Soundness of the certificate (3.3)**: if `h · U_g < Q · G_g(q)` for every `q` in a nonempty
pool, the group has an active candidate with an exact witness. -/
theorem exists_witness_of_certified (hAB : AbsLe AB U) (hBC : AbsLe BC U) (hAC : AbsLe AC U)
    {A : ℕ → Bool} {M g : ℕ} (hQ : 0 < QOf n)
    (hcert : ∀ q ∈ pool n, hOf n U * mass n s AB BC AC A M g < QOf n * mass n s AB BC AC A (M * q) g) :
    0 < mass n s AB BC AC A 0 g := by
  by_contra h0
  have h0 : mass n s AB BC AC A 0 g = 0 := by omega
  have hsum := sum_pool_mass_le (s := s) hAB hBC hAC A M g (n := n)
  rw [h0, mul_zero, zero_add] at hsum
  have hne : (pool n).Nonempty := Finset.card_pos.1 hQ
  have hlt := Finset.sum_lt_sum_of_nonempty hne hcert
  rw [Finset.sum_const, smul_eq_mul, ← Finset.mul_sum] at hlt
  unfold QOf at hlt
  have := Nat.mul_le_mul_left (pool n).card hsum
  omega

/-- **The contraction**: let every group in `Rem` fail the certificate, and let `q* ∈ P` minimize the
mass of `Rem` at `M q`.  Then `Q · Σ_{Rem} mass(M q*) ≤ 2h · Σ_{Rem} mass(M)`. -/
theorem contract (hAB : AbsLe AB U) (hBC : AbsLe BC U) (hAC : AbsLe AC U)
    {A : ℕ → Bool} {M : ℕ} {Rem : Finset ℕ}
    (hfail : ∀ g ∈ Rem, ∃ q ∈ pool n,
      QOf n * mass n s AB BC AC A (M * q) g ≤ hOf n U * mass n s AB BC AC A M g)
    {qs : ℕ} (hqs : qs ∈ pool n)
    (hmin : ∀ q ∈ pool n, ∑ g ∈ Rem, mass n s AB BC AC A (M * qs) g ≤
      ∑ g ∈ Rem, mass n s AB BC AC A (M * q) g) :
    QOf n * ∑ g ∈ Rem, mass n s AB BC AC A (M * qs) g ≤
      2 * hOf n U * ∑ g ∈ Rem, mass n s AB BC AC A M g := by
  have hg : ∀ g ∈ Rem, ∑ q ∈ pool n, mass n s AB BC AC A (M * q) g ≤
      2 * hOf n U * mass n s AB BC AC A M g := by
    intro g hgR
    obtain ⟨q, hq, hle⟩ := hfail g hgR
    have h1 := sum_pool_mass_le (s := s) hAB hBC hAC A M g (n := n)
    have h2 : QOf n * mass n s AB BC AC A 0 g ≤ QOf n * mass n s AB BC AC A (M * q) g :=
      Nat.mul_le_mul_left _ (mass_zero_le A _ g)
    nlinarith
  calc QOf n * ∑ g ∈ Rem, mass n s AB BC AC A (M * qs) g
      = ∑ q ∈ pool n, ∑ g ∈ Rem, mass n s AB BC AC A (M * qs) g := by
        rw [Finset.sum_const, smul_eq_mul]; rfl
    _ ≤ ∑ q ∈ pool n, ∑ g ∈ Rem, mass n s AB BC AC A (M * q) g := Finset.sum_le_sum hmin
    _ = ∑ g ∈ Rem, ∑ q ∈ pool n, mass n s AB BC AC A (M * q) g := Finset.sum_comm
    _ ≤ ∑ g ∈ Rem, 2 * hOf n U * mass n s AB BC AC A M g := Finset.sum_le_sum hg
    _ = _ := by rw [Finset.mul_sum]

/-- A count is at most the block size. -/
theorem cntOf_le_s (M i : ℕ) : cntOf n s M AB BC AC i ≤ s := by
  unfold cntOf
  calc _ ≤ (Finset.Ico (i / (n * n) * s) ((i / (n * n) + 1) * s)).card := by
        refine Finset.card_le_card fun c hc => ?_
        obtain ⟨-, ⟨h1, h2, -⟩, -⟩ := Finset.mem_filter.1 hc
        exact Finset.mem_Ico.2 ⟨h1, h2⟩
    _ = s := by rw [Nat.card_Ico, add_mul, one_mul, Nat.add_sub_cancel_left]

end Light.Filter2
