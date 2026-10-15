/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Filter2.Defs
public import Submission.ThreeSumApsp.Util.PrimesInWindow
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.NumberTheory.Bertrand

/-!
# Asymptotics of the filtering parameters

With `k = Nat.size n`, `ℓ = ⌊√k⌋ + 1`, `m = ⌊√ℓ⌋` (so `b = ℓ (m + 1)`), every parameter is a power
of two whose exponent is a polynomial in `m`, `ℓ`, `k`, and `m → ∞` with `n`.

* `rpow_le_two_mul_sOf`, `sOf_le_two_mul_rpow`: `n^σ / 2 ≤ s ≤ 2 n^σ`, `σ = 0.0336175`.
* `RR_le_rpow`, `QOf_le_rpow`, `calls_le_rpow`, `PmaxOf_le`: `R, Q, rounds · (r (Q + 1) + 2)` are
  `n^{o(1)}`, and `Pmax ≤ s n^{o(1)}`.
* `guard_eventually`: eventually `Guard n U` for all `U ≤ c n^κ`.
-/

@[expose] public section

open Filter

namespace Light.Filter2

/-! ## Basic facts -/

/-- `m = ⌊√ℓ⌋`. -/
def mmOf (n : ℕ) : ℕ := Nat.sqrt (ellOf n)

/-- The exponent of `s`: `s = 2^{jOf n}`. -/
def jOf (n : ℕ) : ℕ := 336175 * kOf n / 10 ^ 7

theorem sOf_eq (n : ℕ) : sOf n = 2 ^ jOf n := rfl

theorem cKOf_eq (n : ℕ) : cKOf n = jOf n + 1 := Nat.size_pow

theorem jOf_mul_le (n : ℕ) : 10 ^ 7 * jOf n ≤ 336175 * kOf n := by
  unfold jOf; rw [mul_comm]; exact Nat.div_mul_le_self _ _

theorem jOf_le (n : ℕ) : jOf n ≤ kOf n := by
  have := jOf_mul_le n; omega

theorem kOf_pos {n : ℕ} (hn : 1 ≤ n) : 1 ≤ kOf n := Nat.size_pos.2 hn

theorem two_pow_kOf_sub_one_le {n : ℕ} (hn : 1 ≤ n) : 2 ^ (kOf n - 1) ≤ n := by
  have := kOf_pos hn
  exact Nat.lt_size.1 (by unfold kOf at this ⊢; omega)

theorem lt_two_pow_kOf (n : ℕ) : n < 2 ^ kOf n := Nat.lt_size_self n

theorem kOf_lt (n : ℕ) : kOf n < ellOf n * ellOf n := Nat.lt_succ_sqrt _

theorem le_kOf (n : ℕ) : (ellOf n - 1) * (ellOf n - 1) ≤ kOf n := by
  unfold ellOf; simpa using Nat.sqrt_le (kOf n)

theorem mmOf_sq_le (n : ℕ) : mmOf n * mmOf n ≤ ellOf n := Nat.sqrt_le _

theorem bOf_eq (n : ℕ) : bOf n = ellOf n * (mmOf n + 1) := rfl

theorem one_le_ellOf (n : ℕ) : 1 ≤ ellOf n := Nat.succ_pos _

theorem one_le_sOf (n : ℕ) : 1 ≤ sOf n := Nat.one_le_two_pow

theorem sOf_le_n {n : ℕ} (hn : 1 ≤ n) : sOf n ≤ n := by
  refine le_trans (Nat.pow_le_pow_right (by norm_num) ?_) (two_pow_kOf_sub_one_le hn)
  have := jOf_mul_le n
  have := kOf_pos hn
  show jOf n ≤ kOf n - 1
  omega

/-- `m → ∞` with `n`. -/
theorem tendsto_mmOf : Tendsto mmOf atTop atTop := by
  refine tendsto_atTop.2 fun M => eventually_atTop.2 ⟨2 ^ (M * M * (M * M)), fun n hn => ?_⟩
  have hk : M * M * (M * M) ≤ kOf n := by
    have := Nat.size_le_size hn
    rw [Nat.size_pow] at this
    unfold kOf; omega
  have h1 : M * M ≤ Nat.sqrt (kOf n) := Nat.le_sqrt.2 hk
  have h2 : M * M ≤ ellOf n := by unfold ellOf; omega
  exact Nat.le_sqrt.2 h2

theorem QOf_le (n : ℕ) : QOf n ≤ 2 ^ (ellOf n + 1) := by
  unfold QOf pool
  refine (Finset.card_filter_le _ _).trans ?_
  rw [Finset.card_range, RR, pow_succ, mul_comm]

theorem QOf_pos (n : ℕ) : 0 < QOf n := by
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (RR n) (by unfold RR; positivity)
  have hR : 2 ≤ RR n := by
    unfold RR; exact le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (one_le_ellOf n))
  have hne : p ≠ 2 * RR n := by
    rintro rfl
    exact (Nat.not_prime_mul (by norm_num) (by omega)) hp
  refine Finset.card_pos.2 ⟨p, ?_⟩
  simp only [pool, Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, hlt.le, hp⟩

/-- For `m ≥ 2`: `r ≤ 2ℓ + 1`. -/
theorem rOf_le {n : ℕ} (hm : 2 ≤ mmOf n) : rOf n ≤ 2 * ellOf n + 1 := by
  have hsq := mmOf_sq_le n
  have hb : bOf n ≤ ellOf n * ellOf n := by
    rw [bOf_eq]; exact Nat.mul_le_mul_left _ (by nlinarith)
  have hk := kOf_lt n
  have hj := jOf_le n
  unfold rOf
  rw [cKOf_eq]
  have : (jOf n + 1 + bOf n) / ellOf n ≤ 2 * ellOf n :=
    Nat.div_le_of_le_mul (by nlinarith)
  omega

/-- `j + 1 + b < ℓ r`. -/
theorem lt_ell_mul_rOf (n : ℕ) : jOf n + 1 + bOf n < ellOf n * rOf n := by
  unfold rOf; rw [cKOf_eq]
  exact Nat.lt_mul_div_succ _ (one_le_ellOf n)

/-- `(ℓ + 1) r ≤ j + b + 3ℓ + 2`, for `m ≥ 2`. -/
theorem ell_succ_mul_rOf_le {n : ℕ} (hm : 2 ≤ mmOf n) :
    (ellOf n + 1) * rOf n ≤ jOf n + bOf n + 3 * ellOf n + 2 := by
  have hr := rOf_le hm
  have h1 : ellOf n * rOf n ≤ jOf n + 1 + bOf n + ellOf n := by
    unfold rOf; rw [cKOf_eq, mul_add, mul_one, mul_comm]
    have := Nat.div_mul_le_self (jOf n + 1 + bOf n) (ellOf n)
    omega
  rw [add_mul, one_mul]
  omega

theorem PmaxOf_le_two_pow {n : ℕ} (hm : 2 ≤ mmOf n) :
    PmaxOf n ≤ sOf n * 2 ^ (bOf n + 3 * ellOf n + 2) := by
  unfold PmaxOf RR
  rw [sOf_eq, ← pow_add, ← pow_succ', ← pow_mul]
  exact Nat.pow_le_pow_right (by norm_num) (by have := ell_succ_mul_rOf_le hm; omega)

/-! ## Polynomial inequalities, eventually -/

/-- For `m` large, `m² ≤ ℓ` and `(ℓ - 1)² ≤ k`: `N (ℓ (m + A) + A) + 1 ≤ k`. -/
theorem poly_le (N A : ℕ) : ∃ M₀ : ℕ, ∀ {m ℓ k : ℕ}, M₀ ≤ m → m * m ≤ ℓ →
    (ℓ - 1) * (ℓ - 1) ≤ k → N * (ℓ * (m + A) + A) + 1 ≤ k := by
  refine ⟨2 * N + 3 * N * A + 4, fun {m ℓ k} hm hml hk => ?_⟩
  have hm4 : 4 ≤ m := by omega
  have hℓ1 : 1 ≤ ℓ := le_trans (by nlinarith) hml
  obtain ⟨L, rfl⟩ : ∃ L, ℓ = L + 1 := ⟨ℓ - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hk
  have h1 : (2 * N + 3 * N * A + 4) * m ≤ m * m := Nat.mul_le_mul_right _ hm
  have hm1 : 1 ≤ m := by omega
  have h2 : 3 * N * A ≤ 3 * N * A * m := Nat.le_mul_of_pos_right _ hm1
  have hL : 2 * N * (m + A) + N * A + 1 ≤ L := by nlinarith
  have hL1 : 1 ≤ L := by nlinarith
  have h3 : N * ((L + 1) * (m + A) + A) + 1 ≤ L * (2 * N * (m + A) + N * A + 1) := by
    have : N * (m + A) ≤ N * (m + A) * L := Nat.le_mul_of_pos_right _ hL1
    have : N * A ≤ N * A * L := Nat.le_mul_of_pos_right _ hL1
    nlinarith
  have h4 : L * (2 * N * (m + A) + N * A + 1) ≤ L * L := Nat.mul_le_mul_left _ hL
  omega

/-- `2^E ≤ n^η` as soon as `N E ≤ k - 1`, `N ≥ 1/η`. -/
theorem exists_two_pow_le_rpow {η : ℝ} (hη : 0 < η) : ∃ N : ℕ, ∀ {n E : ℕ}, 1 ≤ n →
    N * E ≤ kOf n - 1 → (2 : ℝ) ^ E ≤ (n : ℝ) ^ η := by
  obtain ⟨N, hN⟩ := exists_nat_ge (1 / η)
  refine ⟨N, fun {n E} hn hE => ?_⟩
  have hNη : 1 ≤ η * N := by rwa [div_le_iff₀ hη, mul_comm] at hN
  have hE' : (E : ℝ) ≤ η * ((kOf n - 1 : ℕ) : ℝ) := by
    have : ((N * E : ℕ) : ℝ) ≤ ((kOf n - 1 : ℕ) : ℝ) := by exact_mod_cast hE
    push_cast at this
    have hE0 : (0 : ℝ) ≤ E := Nat.cast_nonneg _
    nlinarith
  calc (2 : ℝ) ^ E = (2 : ℝ) ^ (E : ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ (2 : ℝ) ^ (((kOf n - 1 : ℕ) : ℝ) * η) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = (((2 ^ (kOf n - 1) : ℕ) : ℝ)) ^ η := by
        rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]; push_cast; ring_nf
    _ ≤ (n : ℝ) ^ η :=
        Real.rpow_le_rpow (by positivity) (by exact_mod_cast two_pow_kOf_sub_one_le hn) hη.le

/-- The master lemma: eventually `m ≥ 2`, `n ≥ 1`, and `2^E ≤ n^η` for `E ≤ ℓ (m + A) + A`. -/
theorem eventually_two_pow_le {η : ℝ} (hη : 0 < η) (A : ℕ) : ∀ᶠ n : ℕ in atTop,
    2 ≤ mmOf n ∧ 1 ≤ n ∧ ∀ E : ℕ, E ≤ ellOf n * (mmOf n + A) + A →
      (2 : ℝ) ^ E ≤ (n : ℝ) ^ η := by
  obtain ⟨N, hN⟩ := exists_two_pow_le_rpow hη
  obtain ⟨M₀, hM₀⟩ := poly_le N A
  filter_upwards [tendsto_mmOf.eventually_ge_atTop (max M₀ 2), eventually_ge_atTop 1]
    with n hm hn
  refine ⟨le_of_max_le_right hm, hn, fun E hE => hN hn ?_⟩
  have := hM₀ (le_of_max_le_left hm) (mmOf_sq_le n) (le_kOf n)
  have := Nat.mul_le_mul_left N hE
  omega

/-! ## The parameters are `n^{o(1)}` -/

theorem RR_le_rpow {η : ℝ} (hη : 0 < η) : ∀ᶠ n : ℕ in atTop, (RR n : ℝ) ≤ (n : ℝ) ^ η := by
  filter_upwards [eventually_two_pow_le hη 1] with n ⟨_, _, h⟩
  unfold RR; push_cast
  exact h _ (by nlinarith)

theorem QOf_le_rpow {η : ℝ} (hη : 0 < η) : ∀ᶠ n : ℕ in atTop, (QOf n : ℝ) ≤ (n : ℝ) ^ η := by
  filter_upwards [eventually_two_pow_le hη 1] with n ⟨_, _, h⟩
  calc (QOf n : ℝ) ≤ ((2 ^ (ellOf n + 1) : ℕ) : ℝ) := by exact_mod_cast QOf_le n
    _ ≤ _ := by push_cast; exact h _ (by nlinarith)

/-- `rounds · (r (Q + 1) + 2) ≤ 2^{4ℓ + 7}`, for `m ≥ 2`. -/
theorem calls_le_two_pow {n : ℕ} (hm : 2 ≤ mmOf n) :
    roundsOf n * (rOf n * (QOf n + 1) + 2) ≤ 2 ^ (4 * ellOf n + 7) := by
  set P := 2 ^ ellOf n with hP
  have hlP : ellOf n < P := Nat.lt_two_pow_self
  have hk := kOf_lt n
  have hround : roundsOf n ≤ 3 * P * P := by
    unfold roundsOf
    have := Nat.div_le_self (3 * kOf n) (dOf n)
    nlinarith
  have hr : rOf n ≤ 3 * P := by have := rOf_le hm; omega
  have hQ : QOf n + 1 ≤ 3 * P := by
    have := QOf_le n
    rw [pow_succ] at this
    have : 1 ≤ P := Nat.one_le_two_pow
    omega
  have hin : rOf n * (QOf n + 1) + 2 ≤ 11 * P * P := by
    have := Nat.mul_le_mul hr hQ
    have : 1 ≤ P := Nat.one_le_two_pow
    nlinarith
  have heq : 2 ^ (4 * ellOf n + 7) = 128 * (P * P * (P * P)) := by
    rw [hP, pow_add, mul_comm 4, pow_mul]; ring
  rw [heq]
  calc _ ≤ 3 * P * P * (11 * P * P) := Nat.mul_le_mul hround hin
    _ ≤ _ := by nlinarith

theorem calls_le_rpow {η : ℝ} (hη : 0 < η) : ∀ᶠ n : ℕ in atTop,
    ((roundsOf n * (rOf n * (QOf n + 1) + 2) : ℕ) : ℝ) ≤ (n : ℝ) ^ η := by
  filter_upwards [eventually_two_pow_le hη 7] with n ⟨hm, _, h⟩
  calc _ ≤ ((2 ^ (4 * ellOf n + 7) : ℕ) : ℝ) := by exact_mod_cast calls_le_two_pow hm
    _ ≤ _ := by push_cast; exact h _ (by nlinarith)

theorem PmaxOf_le {η : ℝ} (hη : 0 < η) : ∀ᶠ n : ℕ in atTop,
    (PmaxOf n : ℝ) ≤ sOf n * (n : ℝ) ^ η := by
  filter_upwards [eventually_two_pow_le hη 4] with n ⟨hm, _, h⟩
  calc (PmaxOf n : ℝ) ≤ ((sOf n * 2 ^ (bOf n + 3 * ellOf n + 2) : ℕ) : ℝ) := by
        exact_mod_cast PmaxOf_le_two_pow hm
    _ ≤ _ := by
        push_cast
        refine mul_le_mul_of_nonneg_left (h _ ?_) (by positivity)
        rw [bOf_eq]; nlinarith

/-! ## The block size and the number of blocks -/

/-- `s ≤ 2 n^σ`. -/
theorem sOf_le_two_mul_rpow {n : ℕ} (hn : 1 ≤ n) :
    (sOf n : ℝ) ≤ 2 * (n : ℝ) ^ (0.0336175 : ℝ) := by
  set σ : ℝ := 0.0336175
  have hk := kOf_pos hn
  have hj : (jOf n : ℝ) ≤ σ * ((kOf n - 1 : ℕ) : ℝ) + σ := by
    have : ((10 ^ 7 * jOf n : ℕ) : ℝ) ≤ ((336175 * kOf n : ℕ) : ℝ) := by exact_mod_cast jOf_mul_le n
    push_cast [Nat.cast_sub hk] at this ⊢
    simp only [σ]; linarith
  have h1 : (2 : ℝ) ^ (σ * ((kOf n - 1 : ℕ) : ℝ)) ≤ (n : ℝ) ^ σ := by
    rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_natCast]
    exact Real.rpow_le_rpow (by positivity)
      (by exact_mod_cast two_pow_kOf_sub_one_le hn) (by norm_num [σ])
  have h2 : (2 : ℝ) ^ σ ≤ 2 := by
    calc (2 : ℝ) ^ σ ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num [σ])
      _ = 2 := Real.rpow_one 2
  calc (sOf n : ℝ) = (2 : ℝ) ^ (jOf n : ℝ) := by rw [sOf_eq, Real.rpow_natCast]; push_cast; rfl
    _ ≤ (2 : ℝ) ^ (σ * ((kOf n - 1 : ℕ) : ℝ) + σ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hj
    _ = (2 : ℝ) ^ (σ * ((kOf n - 1 : ℕ) : ℝ)) * (2 : ℝ) ^ σ := Real.rpow_add (by norm_num) _ _
    _ ≤ (n : ℝ) ^ σ * 2 := mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = _ := mul_comm _ _

/-- `n^σ ≤ 2 s`. -/
theorem rpow_le_two_mul_sOf (n : ℕ) : (n : ℝ) ^ (0.0336175 : ℝ) ≤ 2 * (sOf n : ℝ) := by
  set σ : ℝ := 0.0336175
  have hj : σ * (kOf n : ℝ) ≤ (jOf n : ℝ) + 1 := by
    have h := Nat.lt_mul_div_succ (336175 * kOf n) (show 0 < 10 ^ 7 by norm_num)
    have : ((336175 * kOf n : ℕ) : ℝ) ≤ ((10 ^ 7 * (jOf n + 1) : ℕ) : ℝ) := by
      exact_mod_cast h.le
    push_cast at this
    simp only [σ]; linarith
  calc (n : ℝ) ^ σ ≤ ((2 : ℝ) ^ kOf n) ^ σ :=
        Real.rpow_le_rpow (by positivity) (by exact_mod_cast (lt_two_pow_kOf n).le) (by norm_num [σ])
    _ = (2 : ℝ) ^ (σ * (kOf n : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm]
    _ ≤ (2 : ℝ) ^ ((jOf n : ℝ) + 1) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hj
    _ = 2 * (sOf n : ℝ) := by
        rw [Real.rpow_add (by norm_num), Real.rpow_natCast, Real.rpow_one, sOf_eq]; push_cast; ring

theorem mOf_le_n {n : ℕ} (hn : 1 ≤ n) : mOf n ≤ n := by
  unfold mOf
  apply Nat.div_le_of_le_mul
  obtain ⟨t, ht⟩ : ∃ t, sOf n = t + 1 := ⟨sOf n - 1, by have := one_le_sOf n; omega⟩
  obtain ⟨u, rfl⟩ : ∃ u, n = u + 1 := ⟨n - 1, by omega⟩
  rw [ht]
  have : u + t + 1 ≤ (t + 1) * (u + 1) := by nlinarith
  omega

theorem mul_mul_mOf_le (n : ℕ) : n * n * mOf n ≤ n ^ 3 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have := mOf_le_n hn
    calc n * n * mOf n ≤ n * n * n := Nat.mul_le_mul_left _ this
      _ = n ^ 3 := by ring

theorem mOf_mul_sOf_le {n : ℕ} (hn : 1 ≤ n) : mOf n * sOf n ≤ 2 * n := by
  have h1 := Nat.div_mul_le_self (n + sOf n - 1) (sOf n)
  have h2 := sOf_le_n hn
  unfold mOf
  omega

theorem mOf_le_div_add_one (n : ℕ) : mOf n ≤ n / sOf n + 1 := by
  unfold mOf
  have hs := one_le_sOf n
  calc (n + sOf n - 1) / sOf n ≤ (n + sOf n) / sOf n := Nat.div_le_div_right (by omega)
    _ = n / sOf n + 1 := Nat.add_div_right _ (by omega)

/-! ## The guard -/

/-- A polynomial is eventually below an exponential. -/
theorem eventually_mul_pow_le_two_pow (D e : ℕ) :
    ∀ᶠ m : ℕ in atTop, D * (m + 1) ^ e ≤ 2 ^ (m + 1) := by
  have h := (tendsto_pow_const_div_const_pow_of_one_lt e (one_lt_two : (1 : ℝ) < 2)).comp
    (tendsto_add_atTop_nat 1)
  have hpos : (0 : ℝ) < 1 / ((D : ℝ) + 1) := by positivity
  filter_upwards [h.eventually (gt_mem_nhds hpos)] with m hm
  simp only [Function.comp, Nat.cast_add, Nat.cast_one] at hm
  have h2 : (0 : ℝ) < 2 ^ (m + 1) := by positivity
  rw [div_lt_div_iff₀ h2 (by positivity), one_mul] at hm
  have : ((D * (m + 1) ^ e : ℕ) : ℝ) ≤ ((2 ^ (m + 1) : ℕ) : ℝ) := by
    push_cast
    have : (0 : ℝ) ≤ ((m : ℝ) + 1) ^ e := by positivity
    nlinarith
  exact_mod_cast this

/-- `2^{ℓ+1} ≤ N₁ (ℓ + 1) Q`, with `N₁ ≥ 1/c₁` from the prime count. -/
theorem two_pow_le_QOf {c₁ : ℝ} (hc₁ : 0 < c₁)
    (hprimes : ∀ x : ℝ, 4 ≤ x → ∀ S : Finset ℕ,
      (∀ p : ℕ, p.Prime → x / 2 ≤ (p : ℝ) → (p : ℝ) < x → p ∈ S) →
      c₁ * (x / Real.log x) ≤ (S.card : ℝ))
    {N₁ : ℕ} (hN₁ : 1 / c₁ ≤ N₁) (n : ℕ) :
    2 ^ (ellOf n + 1) ≤ N₁ * (ellOf n + 1) * QOf n := by
  set x : ℝ := 2 ^ (ellOf n + 1) with hxdef
  have hl := one_le_ellOf n
  have hx : (4 : ℝ) ≤ x := by
    rw [hxdef]
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (ellOf n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hcard := hprimes x hx (pool n) fun p hp hlo hhi => by
    have hR : (RR n : ℝ) = x / 2 := by rw [hxdef, RR, pow_succ]; push_cast; ring
    have h1 : RR n ≤ p := by exact_mod_cast hR ▸ hlo
    have h2 : p < 2 * RR n := by
      have : (p : ℝ) < 2 * (RR n : ℝ) := by rw [hR]; linarith
      exact_mod_cast this
    simp only [pool, Finset.mem_filter, Finset.mem_range]
    exact ⟨h2, h1, hp⟩
  have hlogx : Real.log x ≤ (ellOf n : ℝ) + 1 := by
    rw [hxdef, Real.log_pow]
    have := Real.log_two_lt_d9
    push_cast
    nlinarith
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hQ0 : (0 : ℝ) ≤ QOf n := Nat.cast_nonneg _
  have h1 : c₁ * x ≤ QOf n * Real.log x := by
    have := hcard
    rw [mul_div_assoc', div_le_iff₀ hlogpos] at this
    exact this
  have h2 : c₁ * x ≤ QOf n * ((ellOf n : ℝ) + 1) := h1.trans (by gcongr)
  have hNc : 1 ≤ c₁ * N₁ := by rwa [div_le_iff₀ hc₁, mul_comm] at hN₁
  have h3 : x ≤ (N₁ : ℝ) * ((ellOf n : ℝ) + 1) * QOf n := by
    have hx0 : 0 ≤ x := by linarith
    have hl0 : (0 : ℝ) ≤ (ellOf n : ℝ) + 1 := by positivity
    nlinarith [mul_nonneg hQ0 hl0]
  have : ((2 ^ (ellOf n + 1) : ℕ) : ℝ) ≤ ((N₁ * (ellOf n + 1) * QOf n : ℕ) : ℝ) := by
    push_cast; exact h3
  exact_mod_cast this

/-- **The guard holds eventually** along `U ≤ c n^κ`. -/
theorem guard_eventually (c κ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ U : ℕ, (U : ℝ) ≤ c * (n : ℝ) ^ κ → Guard n U := by
  obtain ⟨c₁, hc₁, hprimes⟩ := Nat.exists_forall_mul_div_log_le_card_primes
  obtain ⟨N₁, hN₁⟩ := exists_nat_ge (1 / c₁)
  obtain ⟨A, hA⟩ := exists_nat_gt (3 * c)
  obtain ⟨K, hK⟩ := exists_nat_ge κ
  set C := 4 * (A + K) * N₁
  filter_upwards [tendsto_mmOf.eventually (eventually_mul_pow_le_two_pow (C ^ 6) 24),
    tendsto_mmOf.eventually_ge_atTop 2, eventually_ge_atTop 1] with n hpoly hm hn U hU
  have hl := one_le_ellOf n
  -- `B ≤ A + K k`
  have hB : BOf U ≤ A + K * kOf n := by
    unfold BOf; rw [Nat.size_le]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have h1 : (n : ℝ) ^ κ ≤ (n : ℝ) ^ K := by
      rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le hn1 hK
    have h3 : (n : ℝ) ^ K ≤ ((2 : ℝ) ^ kOf n) ^ K :=
      pow_le_pow_left₀ (by positivity) (by exact_mod_cast (lt_two_pow_kOf n).le) K
    have h4 : (A : ℝ) ≤ 2 ^ A := by exact_mod_cast (Nat.lt_two_pow_self).le
    have hpos : 0 < (n : ℝ) ^ κ := Real.rpow_pos_of_pos (by linarith) _
    have : ((3 * U : ℕ) : ℝ) < ((2 ^ (A + K * kOf n) : ℕ) : ℝ) := by
      push_cast
      rw [pow_add, mul_comm K, pow_mul]
      calc (3 : ℝ) * U ≤ 3 * c * (n : ℝ) ^ κ := by linarith
        _ < A * (n : ℝ) ^ κ := mul_lt_mul_of_pos_right hA hpos
        _ ≤ 2 ^ A * ((2 : ℝ) ^ kOf n) ^ K :=
            mul_le_mul h4 (h1.trans h3) hpos.le (by positivity)
    exact_mod_cast this
  -- `h ≤ (A + K) ℓ`
  have hh : hOf n U ≤ (A + K) * ellOf n := by
    unfold hOf
    apply Nat.div_le_of_le_mul
    have hk := kOf_lt n
    have h1 : K * kOf n ≤ K * (ellOf n * ellOf n) := Nat.mul_le_mul_left _ hk.le
    have h2 : A ≤ A * (ellOf n * ellOf n) := Nat.le_mul_of_pos_right _ (by positivity)
    have h3 : BOf U - 1 ≤ A + K * kOf n := by omega
    nlinarith
  -- `2^{ℓ+1} ≤ X Q`
  have hQ := two_pow_le_QOf hc₁ hprimes hN₁ n
  set X := N₁ * (ellOf n + 1) with hXdef
  set Y := 2 * hOf n U * X with hYdef
  have hlt : ellOf n < (mmOf n + 1) * (mmOf n + 1) := Nat.lt_succ_sqrt _
  have hY : Y ≤ C * (mmOf n + 1) ^ 4 := by
    calc Y ≤ 2 * ((A + K) * ellOf n) * (N₁ * (2 * ellOf n)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hh) (Nat.mul_le_mul_left _ (by omega))
      _ = C * (ellOf n * ellOf n) := by simp only [C]; ring
      _ ≤ C * ((mmOf n + 1) * (mmOf n + 1) * ((mmOf n + 1) * (mmOf n + 1))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul hlt.le hlt.le)
      _ = C * (mmOf n + 1) ^ 4 := by ring
  have hY6 : Y ^ 6 ≤ 2 ^ (mmOf n + 1) := by
    calc Y ^ 6 ≤ (C * (mmOf n + 1) ^ 4) ^ 6 := Nat.pow_le_pow_left hY 6
      _ = C ^ 6 * (mmOf n + 1) ^ 24 := by ring
      _ ≤ _ := hpoly
  have hr3 : 2 * rOf n ≤ 6 * ellOf n := by have := rOf_le hm; omega
  have hr1 : 1 ≤ rOf n := Nat.succ_pos _
  have hbd : bOf n ≤ 2 * (bOf n - dOf n) := by unfold dOf; omega
  have hYr : Y ^ rOf n ≤ 2 ^ (bOf n - dOf n) := by
    rcases Nat.eq_zero_or_pos Y with h0 | hpos
    · rw [h0, zero_pow (by omega)]; exact Nat.zero_le _
    · rw [← Nat.pow_le_pow_iff_left (two_ne_zero)]
      calc (Y ^ rOf n) ^ 2 = Y ^ (2 * rOf n) := by ring
        _ ≤ Y ^ (6 * ellOf n) := Nat.pow_le_pow_right hpos hr3
        _ = (Y ^ 6) ^ ellOf n := pow_mul _ _ _
        _ ≤ (2 ^ (mmOf n + 1)) ^ ellOf n := Nat.pow_le_pow_left hY6 _
        _ = 2 ^ bOf n := by rw [← pow_mul, bOf_eq, mul_comm]
        _ ≤ 2 ^ (2 * (bOf n - dOf n)) := Nat.pow_le_pow_right (by norm_num) hbd
        _ = (2 ^ (bOf n - dOf n)) ^ 2 := by rw [mul_comm, pow_mul]
  have hd : dOf n ≤ bOf n := Nat.div_le_self _ _
  have hXQ : 2 ^ ellOf n ≤ X * QOf n := by
    have : 2 ^ ellOf n ≤ 2 ^ (ellOf n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hjb := lt_ell_mul_rOf n
  have key : sOf n * (2 * hOf n U) ^ rOf n * 2 ^ dOf n * X ^ rOf n ≤
      QOf n ^ rOf n * X ^ rOf n := by
    calc sOf n * (2 * hOf n U) ^ rOf n * 2 ^ dOf n * X ^ rOf n
        = 2 ^ jOf n * Y ^ rOf n * 2 ^ dOf n := by rw [sOf_eq, hYdef, mul_pow (2 * hOf n U) X]; ring
      _ ≤ 2 ^ jOf n * 2 ^ (bOf n - dOf n) * 2 ^ dOf n := by gcongr
      _ = 2 ^ (jOf n + bOf n) := by rw [← pow_add, ← pow_add]; congr 1; omega
      _ ≤ 2 ^ (ellOf n * rOf n) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = (2 ^ ellOf n) ^ rOf n := pow_mul _ _ _
      _ ≤ (X * QOf n) ^ rOf n := Nat.pow_le_pow_left hXQ _
      _ = _ := by rw [mul_pow, mul_comm]
  have hX0 : 0 < X ^ rOf n := by
    have : 0 < X := by
      rcases Nat.eq_zero_or_pos X with h0 | h0
      · rw [h0, zero_mul] at hQ
        exact absurd hQ (Nat.not_le.2 (by positivity : 0 < 2 ^ (ellOf n + 1)))
      · exact h0
    positivity
  exact Nat.le_of_mul_le_mul_right key hX0

end Light.Filter2
