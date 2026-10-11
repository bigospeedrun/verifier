/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Sec4.Corollary31

/-!
# Helpers for the sharper analysis of Corollary 31

Elementary facts on `φ(y) = y ln y` (tangent-line bounds), the exponent function
`F(u, m, s) = s ln 9 + φ(m) + φ(u-m) - φ(m-s) - φ(u-m+s)` (the logarithm of the proxy for
`β_s / M` with `L = u`), its monotonicity in `s` and in `u`, the binomial ratio bound
`binom(L, k) · k · e^{φ(k) + φ(L-k)}` increasing in `k`, and the upper bound
`binom(n, k) ≤ e^{φ(n) - φ(k) - φ(n-k)}`.
-/

@[expose] public section

open Finset

namespace ThreeSumApsp

namespace PrunedAux

/-- `φ(y) = y ln y`. -/
noncomputable def xlogx (y : ℝ) : ℝ := y * Real.log y

/-- The tangent-line inequality for the convex `φ`: `φ(y) ≥ φ(x) + (y - x)(ln x + 1)`, written as
`y ln y ≥ y ln x + y - x`. -/
theorem tangent {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) :
    y * Real.log x + y - x ≤ xlogx y := by
  unfold xlogx
  rcases hy.eq_or_lt with rfl | hy'
  · simp; linarith
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hy' hx)
  rw [Real.log_div hy'.ne' hx.ne', inv_div] at h
  have h2 : y * (1 - x / y) ≤ y * (Real.log y - Real.log x) := mul_le_mul_of_nonneg_left h hy
  have h3 : y * (1 - x / y) = y - x := by field_simp
  nlinarith

/-- `φ(b) - φ(a) ≤ (b - a)(ln b + 1)` for `0 ≤ a`, `0 < b`. -/
theorem sub_le_right {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    xlogx b - xlogx a ≤ (b - a) * (Real.log b + 1) := by
  have := tangent hb ha
  unfold xlogx at *
  nlinarith

/-- `φ(b) - φ(a) ≥ (b - a)(ln a + 1)` for `0 < a`, `0 ≤ b`. -/
theorem le_sub_left {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    (b - a) * (Real.log a + 1) ≤ xlogx b - xlogx a := by
  have := tangent ha hb
  unfold xlogx at *
  nlinarith

/-- `n^n = e^{φ(n)}` for natural `n` (with `0^0 = 1`). -/
theorem pow_self_eq_exp (n : ℕ) : ((n : ℝ)) ^ n = Real.exp (xlogx n) := by
  unfold xlogx
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [Real.exp_nat_mul, Real.exp_log (by exact_mod_cast hn)]

/-- The exponent `F(u, m, s) = s ln 9 + φ(m) + φ(u-m) - φ(m-s) - φ(u-m+s)`. -/
noncomputable def Fexp (u m s : ℝ) : ℝ :=
  s * Real.log 9 + xlogx m + xlogx (u - m) - xlogx (m - s) - xlogx (u - m + s)

/-- `F(u, m, 0) = 0`. -/
theorem Fexp_zero (u m : ℝ) : Fexp u m 0 = 0 := by
  unfold Fexp
  simp

/-- `F` decreases in `s` as long as `9(m - s) ≤ u - m + s`: an explicit bound on the increment. -/
theorem Fexp_sub_le {u m s₁ s₂ : ℝ} (h12 : s₁ ≤ s₂) (h2 : s₂ ≤ m) (h1 : s₁ < m)
    (hpos : 0 < u - m + s₁) :
    Fexp u m s₂ - Fexp u m s₁
      ≤ (s₂ - s₁) * (Real.log 9 + Real.log (m - s₁) - Real.log (u - m + s₁)) := by
  have hA := sub_le_right (a := m - s₂) (b := m - s₁) (by linarith) (by linarith)
  have hB := le_sub_left (a := u - m + s₁) (b := u - m + s₂) hpos (by linarith)
  unfold Fexp
  have e1 : m - s₁ - (m - s₂) = s₂ - s₁ := by ring
  have e2 : u - m + s₂ - (u - m + s₁) = s₂ - s₁ := by ring
  rw [e1] at hA
  rw [e2] at hB
  nlinarith

/-- `F` decreases in `s` where `9(m - s) ≤ u - m + s`. -/
theorem Fexp_anti_s {u m s₁ s₂ : ℝ} (h12 : s₁ ≤ s₂) (h2 : s₂ ≤ m) (h1 : s₁ < m)
    (hpos : 0 < u - m + s₁) (h9 : 9 * (m - s₁) ≤ u - m + s₁) :
    Fexp u m s₂ ≤ Fexp u m s₁ := by
  have h := Fexp_sub_le h12 h2 h1 hpos
  have hlog : Real.log 9 + Real.log (m - s₁) - Real.log (u - m + s₁) ≤ 0 := by
    rw [← Real.log_mul (by norm_num) (by linarith), sub_nonpos]
    exact Real.log_le_log (by nlinarith) h9
  nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 h12) hlog]

/-- `F` decreases in `u` on `[u₁, u₁ + s]`. -/
theorem Fexp_anti_u {u₁ u₂ m s : ℝ} (h12 : u₁ ≤ u₂) (h2 : u₂ ≤ u₁ + s) (hpos : 0 < u₁ - m) :
    Fexp u₂ m s ≤ Fexp u₁ m s := by
  have hs : 0 ≤ s := by linarith
  have hA := sub_le_right (a := u₁ - m) (b := u₂ - m) (by linarith) (by linarith)
  have hB := le_sub_left (a := u₁ - m + s) (b := u₂ - m + s) (by linarith) (by linarith)
  have hlog : Real.log (u₂ - m) ≤ Real.log (u₁ - m + s) :=
    Real.log_le_log (by linarith) (by linarith)
  have e1 : u₂ - m - (u₁ - m) = u₂ - u₁ := by ring
  have e2 : u₂ - m + s - (u₁ - m + s) = u₂ - u₁ := by ring
  rw [e1] at hA
  rw [e2] at hB
  unfold Fexp
  nlinarith [mul_le_mul_of_nonneg_left hlog (sub_nonneg.2 h12)]

/-- The explicit value: `F(cx, x, θx) = x ((c-1) ln(c-1) - (1-θ) ln(1-θ) - (c-1+θ) ln(c-1+θ) +
θ ln 9)`. -/
theorem Fexp_scale {c θ x : ℝ} (hc : 1 < c) (hθ1 : θ < 1) (hθ0 : 0 ≤ θ) (hx : 0 < x) :
    Fexp (c * x) x (θ * x)
      = x * ((c - 1) * Real.log (c - 1) - (1 - θ) * Real.log (1 - θ)
          - (c - 1 + θ) * Real.log (c - 1 + θ) + θ * Real.log 9) := by
  unfold Fexp xlogx
  have h1 : Real.log (c * x - x) = Real.log (c - 1) + Real.log x := by
    rw [show c * x - x = (c - 1) * x by ring, Real.log_mul (by linarith) hx.ne']
  have h2 : Real.log (x - θ * x) = Real.log (1 - θ) + Real.log x := by
    rw [show x - θ * x = (1 - θ) * x by ring, Real.log_mul (by linarith) hx.ne']
  have h3 : Real.log (c * x - x + θ * x) = Real.log (c - 1 + θ) + Real.log x := by
    rw [show c * x - x + θ * x = (c - 1 + θ) * x by ring, Real.log_mul (by linarith) hx.ne']
  rw [h1, h2, h3]
  ring

/-- `φ(cx) - φ(x) - φ(cx - x) = x (c ln c - (c-1) ln(c-1))`. -/
theorem xlogx_scale {c x : ℝ} (hc : 1 < c) (hx : 0 < x) :
    xlogx (c * x) - xlogx x - xlogx (c * x - x)
      = x * (c * Real.log c - (c - 1) * Real.log (c - 1)) := by
  unfold xlogx
  rw [show c * x - x = (c - 1) * x by ring, Real.log_mul (by linarith) hx.ne',
    Real.log_mul (by linarith) hx.ne']
  ring

/-- `c H(1/c) = c ln c - (c-1) ln(c-1)`. -/
theorem mul_entropy_inv {c : ℝ} (hc : 1 < c) :
    c * entropy (1 / c) = c * Real.log c - (c - 1) * Real.log (c - 1) := by
  have hc0 : c ≠ 0 := by positivity
  unfold entropy
  rw [show (1 : ℝ) - 1 / c = (c - 1) / c by field_simp,
    Real.log_div (show c - 1 ≠ 0 by linarith) hc0, one_div, Real.log_inv]
  field_simp
  ring

/-- `c H(a/c) = c ln c - a ln a - (c-a) ln(c-a)` for `0 < a < c`. -/
theorem mul_entropy_div {c a : ℝ} (ha : 0 < a) (hac : a < c) :
    c * entropy (a / c) = c * Real.log c - a * Real.log a - (c - a) * Real.log (c - a) := by
  have hc0 : c ≠ 0 := by linarith
  unfold entropy
  rw [show (1 : ℝ) - a / c = (c - a) / c by field_simp,
    Real.log_div (show c - a ≠ 0 by linarith) hc0, Real.log_div ha.ne' hc0]
  field_simp
  ring

/-- The binomial coefficient bounded above by the entropy: `binom(n, k) ≤ e^{φ(n) - φ(k) - φ(n-k)}`.
-/
theorem choose_le_exp (n k : ℕ) (hkn : k ≤ n) :
    (n.choose k : ℝ) ≤ Real.exp (xlogx n - xlogx k - xlogx ((n : ℝ) - k)) := by
  have h := Nat.choose_mul_pow_mul_pow_le k (n - k) n k
  rw [Nat.add_sub_cancel' hkn] at h
  have h' : (n.choose k : ℝ) * (k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k) ≤ (n : ℝ) ^ n := by
    exact_mod_cast h
  rw [pow_self_eq_exp, pow_self_eq_exp, pow_self_eq_exp, Nat.cast_sub hkn] at h'
  rw [sub_sub, Real.exp_sub, le_div_iff₀ (Real.exp_pos _), Real.exp_add]
  linarith [h']

/-- The proxy `binom(L, k) · k · e^{φ(k) + φ(L-k)}` increases with `k` by one step. -/
theorem ratio_step (L k : ℕ) (hk : k < L) :
    (L.choose k : ℝ) * k * Real.exp (xlogx k + xlogx ((L : ℝ) - k))
      ≤ (L.choose (k + 1) : ℝ) * ((k + 1 : ℕ) : ℝ)
          * Real.exp (xlogx ((k + 1 : ℕ) : ℝ) + xlogx ((L : ℝ) - ((k + 1 : ℕ) : ℝ))) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp only [Nat.cast_zero, mul_zero, zero_mul]
    positivity
  have hrec : (L.choose (k + 1) : ℝ) * ((k + 1 : ℕ) : ℝ) = (L.choose k : ℝ) * ((L : ℝ) - k) := by
    have := Nat.choose_succ_right_eq L k
    rw [← Nat.cast_sub hk.le]
    exact_mod_cast this
  rw [hrec]
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk0
  have hkL : (k : ℝ) + 1 ≤ L := by exact_mod_cast hk
  push_cast
  -- `φ(k+1) - φ(k) ≥ ln k + 1` and `φ(L-k) - φ(L-k-1) ≤ ln(L-k) + 1`
  have hA := le_sub_left (a := (k : ℝ)) (b := (k : ℝ) + 1) hk' (by linarith)
  have hB := sub_le_right (a := (L : ℝ) - (k + 1)) (b := (L : ℝ) - k) (by linarith) (by linarith)
  have e1 : (k : ℝ) + 1 - k = 1 := by ring
  have e2 : (L : ℝ) - k - ((L : ℝ) - (k + 1)) = 1 := by ring
  rw [e1, one_mul] at hA
  rw [e2, one_mul] at hB
  have hexp : Real.exp (xlogx k + xlogx ((L : ℝ) - k))
      ≤ Real.exp (xlogx ((k : ℝ) + 1) + xlogx ((L : ℝ) - (k + 1)))
          * Real.exp (Real.log ((L : ℝ) - k) - Real.log k) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  rw [Real.exp_sub, Real.exp_log (by linarith), Real.exp_log hk'] at hexp
  have hC : (0 : ℝ) ≤ L.choose k := Nat.cast_nonneg _
  calc (L.choose k : ℝ) * k * Real.exp (xlogx k + xlogx ((L : ℝ) - k))
      ≤ (L.choose k : ℝ) * k * (Real.exp (xlogx ((k : ℝ) + 1) + xlogx ((L : ℝ) - (k + 1)))
          * (((L : ℝ) - k) / k)) := by gcongr
    _ = (L.choose k : ℝ) * ((L : ℝ) - k)
          * Real.exp (xlogx ((k : ℝ) + 1) + xlogx ((L : ℝ) - (k + 1))) := by
        field_simp

/-- The proxy `binom(L, k) · k · e^{φ(k) + φ(L-k)}` is monotone in `k ≤ L`. -/
theorem ratio_mono (L : ℕ) {k₁ k₂ : ℕ} (h12 : k₁ ≤ k₂) (h2 : k₂ ≤ L) :
    (L.choose k₁ : ℝ) * k₁ * Real.exp (xlogx k₁ + xlogx ((L : ℝ) - k₁))
      ≤ (L.choose k₂ : ℝ) * k₂ * Real.exp (xlogx k₂ + xlogx ((L : ℝ) - k₂)) := by
  induction k₂, h12 using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih => exact (ih (by omega)).trans (ratio_step L n (by omega))

end PrunedAux

end ThreeSumApsp
