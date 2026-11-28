-- Pure cost arithmetic of the engine recursion (the cost recurrence and its budget); it is used by the
-- engine seam part of EngineRecursion.lean, whose notices and credits apply (texts/credits.lean).
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
set_option linter.all false

section
namespace OAI.PowerSaving
namespace EngineCost
open Finset
/-- A polynomial in `k + 1` with constant factor `K` ends up below `2^k`: from the limit
`k^c / 2^k → 0` in the reals, shifted by one. -/
lemma pow_eventually_le (c K : ℕ) : ∃ N, ∀ k, N ≤ k → K * (k + 1) ^ c ≤ 2 ^ k := by
  have lim := (tendsto_pow_const_div_const_pow_of_one_lt c (show (1 : ℝ) < 2 by norm_num)).comp
    (Filter.tendsto_add_atTop_nat 1)
  have hε : (0 : ℝ) < 1 / (2 * ((K : ℝ) + 1)) := by positivity
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 ((tendsto_order.1 lim).2 _ hε)
  refine ⟨N, fun k hk => ?_⟩
  have hk' : (((k + 1 : ℕ) : ℝ) ^ c) / 2 ^ (k + 1) < 1 / (2 * ((K : ℝ) + 1)) := hN k hk
  have hp : (0 : ℝ) < 2 ^ (k + 1) := by positivity
  have hq : (0 : ℝ) < 2 * ((K : ℝ) + 1) := by positivity
  rw [div_lt_div_iff₀ hp hq, one_mul, pow_succ] at hk'
  have ha : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) ^ c := by positivity
  have hK : (K : ℝ) * ((k + 1 : ℕ) : ℝ) ^ c ≤ ((K : ℝ) + 1) * ((k + 1 : ℕ) : ℝ) ^ c :=
    mul_le_mul_of_nonneg_right (by linarith) ha
  have hR : ((K * (k + 1) ^ c : ℕ) : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by
    push_cast at hK hk' ha ⊢
    linarith
  exact_mod_cast hR
structure Rule where
  W : ℕ
  m : ℕ
  P : ℕ
  r : ℕ
  W_pos : 1 ≤ W
  r_pos : 1 ≤ r
  r_lt : r < m
/-- The two kinds of work in the cost model: `batch n B` ripples `B` vectors of `n` bits,
`block n μ` is one class pass on `n` bits with block parameter `μ`. -/
inductive JobForm
  | batch (n B : ℕ)
  | block (n μ : ℕ)
/-- A measure that drops from every form to its sub-forms. -/
def JobForm.weight : JobForm → ℕ
  | .batch n _ => 2 * n + 1
  | .block n _ => 2 * n
namespace Rule
variable (R : Rule)
def jobRows (_n : ℕ) : ℕ := R.W
def cutSize (n : ℕ) : ℕ := R.m * (n / R.m)
lemma jobRows_pos (n : ℕ) : 1 ≤ R.jobRows n := R.W_pos
/-- The forms a class pass may take: a positive block parameter whose block fits. -/
def Fits : JobForm → Prop
  | .batch .. => True
  | .block n μ => 1 ≤ μ ∧ R.m * μ ≤ n
/-- The sub-forms of a form at cutoff `n0`: a large batch sends one block per full group of `W`
vectors, a block sends `P` batches of slices. -/
def jobKids (n0 : ℕ) : JobForm → Multiset JobForm
  | .batch n B => if n0 ≤ n ∧ R.W ≤ B then Multiset.replicate (B / R.W) (.block n (n / R.m)) else 0
  | .block n μ => Multiset.replicate R.P (.batch (R.r * μ) (2 ^ (n - R.r * μ)))
/-- The work a form does itself (calls excluded); each of the `B % W` leftover vectors (counted
at every bit count) pays the naive price `(n+1) 2^n`. -/
def jobLocalCost (n0 : ℕ) : JobForm → ℕ
  | .batch n B => (B + 1) * (if n0 ≤ n then 1 else n + 1) * 2 ^ n + (B % R.W) * ((n + 1) * 2 ^ n)
  | .block n _ => 2 ^ n
/-- Total cost of a form under the per-vector budget `J`. A batch pays `J` per vector, the naive
price per leftover vector and an overhead `(n0+1) 2^n + 1`; a block pays one pass plus `P`
batches of slices. -/
def jobTotalCost (n0 : ℕ) (J : ℕ → ℕ) (d : JobForm) : ℕ :=
  let price : ℕ → ℕ → ℕ := fun n B =>
    B * J n + (B % R.W) * ((n + 1) * 2 ^ n) + (n0 + 1) * 2 ^ n + 1
  match d with
  | .batch n B => price n B
  | .block n μ => 2 ^ n + 1 + R.P * price (R.r * μ) (2 ^ (n - R.r * μ))
lemma jobTotalCost_block (n0 : ℕ) (J : ℕ → ℕ) (n μ : ℕ) : R.jobTotalCost n0 J (.block n μ) =
    2 ^ n + 1 + R.P * R.jobTotalCost n0 J (.batch (R.r * μ) (2 ^ (n - R.r * μ))) := rfl
/-- One step of the recursion pays for itself (own work, one tick and the sub-forms fit in the
total), as soon as `J` covers the naive price below the cutoff and one group of `W` vectors
pays for its block at or above it. -/
theorem step_of_cover {n0 : ℕ} {J : ℕ → ℕ} (rippleLow : ∀ n, n < n0 → (n + 1) * 2 ^ n ≤ J n)
    (hgrp : ∀ n, n0 ≤ n → R.jobTotalCost n0 J (.block n (n / R.m)) + R.W * 2 ^ n ≤ R.W * J n)
    (d : JobForm) : R.jobLocalCost n0 d + 1 + ((R.jobKids n0 d).map (R.jobTotalCost n0 J)).sum ≤ R.jobTotalCost n0 J d := by
  have floor : ∀ n, 2 ^ n ≤ J n := fun n => by
    by_cases hn : n < n0
    · exact (Nat.le_mul_of_pos_left _ (Nat.succ_pos n)).trans (rippleLow n hn)
    · have := hgrp n (by omega)
      exact Nat.le_of_mul_le_mul_left (by omega) R.W_pos
  rcases d with ⟨n, B⟩ | ⟨n, μ⟩
  · have hJ := floor n
    show (B + 1) * (if n0 ≤ n then 1 else n + 1) * 2 ^ n + (B % R.W) * ((n + 1) * 2 ^ n) + 1 +
        ((R.jobKids n0 (.batch n B)).map (R.jobTotalCost n0 J)).sum ≤
      B * J n + (B % R.W) * ((n + 1) * 2 ^ n) + (n0 + 1) * 2 ^ n + 1
    generalize (B % R.W) * ((n + 1) * 2 ^ n) = S
    have hover : 2 ^ n ≤ (n0 + 1) * 2 ^ n := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    by_cases hc : n0 ≤ n ∧ R.W ≤ B
    · rw [jobKids, if_pos hc, Multiset.map_replicate, Multiset.sum_replicate, smul_eq_mul, if_pos hc.1, mul_one]
      have hg := Nat.mul_le_mul_left (B / R.W) (hgrp n hc.1)
      have hsplit := Nat.div_add_mod B R.W
      obtain ⟨q, e, hq, he⟩ : ∃ q e, B / R.W = q ∧ B % R.W = e := ⟨_, _, rfl, rfl⟩
      rw [hq] at hg; rw [hq, he] at hsplit
      rw [hq]
      have h1 : B * J n = q * (R.W * J n) + e * J n := by rw [← hsplit]; ring
      have h2 : (B + 1) * 2 ^ n = q * (R.W * 2 ^ n) + e * 2 ^ n + 2 ^ n := by rw [← hsplit]; ring
      have h3 := Nat.mul_le_mul_left e hJ
      have h4 : q * (R.jobTotalCost n0 J (.block n (n / R.m)) + R.W * 2 ^ n) =
          q * R.jobTotalCost n0 J (.block n (n / R.m)) + q * (R.W * 2 ^ n) := Nat.mul_add _ _ _
      omega
    · rw [jobKids, if_neg hc, Multiset.map_zero, Multiset.sum_zero, add_zero]
      by_cases h0 : n0 ≤ n
      · rw [if_pos h0, mul_one]
        have h1 := Nat.mul_le_mul_left B hJ
        have h2 : (B + 1) * 2 ^ n = B * 2 ^ n + 2 ^ n := Nat.succ_mul _ _
        omega
      · rw [if_neg h0]
        have h1 := Nat.mul_le_mul_left B (rippleLow n (by omega))
        have h2 : (n + 1) * 2 ^ n ≤ (n0 + 1) * 2 ^ n := Nat.mul_le_mul_right _ (by omega)
        have h3 : (B + 1) * (n + 1) * 2 ^ n = B * ((n + 1) * 2 ^ n) + (n + 1) * 2 ^ n := by ring
        omega
  · rw [jobTotalCost_block]
    simp only [jobLocalCost, jobKids, Multiset.map_replicate, Multiset.sum_replicate, smul_eq_mul, le_refl]
/-- Above a cutoff of at least `m`, sub-forms keep fitting and lose weight. -/
lemma jobKids_ok {n0 : ℕ} (hm : R.m ≤ n0) {d c : JobForm} (hd : R.Fits d) (hc : c ∈ R.jobKids n0 d) :
    R.Fits c ∧ c.weight < d.weight := by
  have hm0 : 0 < R.m := by have := R.r_pos; have := R.r_lt; omega
  cases d with
  | batch n B =>
    simp only [jobKids] at hc
    split_ifs at hc with h
    · rw [Multiset.eq_of_mem_replicate hc]
      exact ⟨⟨(Nat.one_le_div_iff hm0).2 (hm.trans h.1), Nat.mul_div_le n R.m⟩,
        show 2 * n < 2 * n + 1 by omega⟩
    · exact absurd hc (Multiset.notMem_zero _)
  | block n μ =>
    simp only [jobKids] at hc
    rw [Multiset.eq_of_mem_replicate hc]
    obtain ⟨h1, h2⟩ := hd
    have : R.r * μ < R.m * μ := Nat.mul_lt_mul_of_pos_right R.r_lt h1
    exact ⟨trivial, show 2 * (R.r * μ) + 1 < 2 * n by omega⟩
lemma exists_N2 (Q M : ℕ) (hM : 0 < M) : ∃ N2, ∀ n, N2 ≤ n → (Q + 2) * (n + 1) ^ (Q + 1) ≤ 2 ^ (n / M) := by
  obtain ⟨N, hN⟩ := pow_eventually_le (Q + 1) ((Q + 2) * M ^ (Q + 1))
  refine ⟨N * M, fun n hn => ?_⟩
  have hk : N ≤ n / M := (Nat.le_div_iff_mul_le hM).2 hn
  have hup : n + 1 ≤ M * (n / M + 1) := Nat.lt_mul_div_succ n hM
  calc (Q + 2) * (n + 1) ^ (Q + 1) ≤ (Q + 2) * (M * (n / M + 1)) ^ (Q + 1) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hup _)
    _ = (Q + 2) * M ^ (Q + 1) * (n / M + 1) ^ (Q + 1) := by rw [mul_pow, Nat.mul_assoc]
    _ ≤ 2 ^ (n / M) := hN _ hk
/-- `(x+1)^z ≤ x^z + 1` for `0 < x` and `0 ≤ z ≤ 1`. -/
lemma succ_rpow_le {x z : ℝ} (hx : 0 < x) (hz : z ≤ 1) : (x + 1) ^ z ≤ x ^ z + 1 := by
  have h1 : 0 < x + 1 := by linarith
  have ht0 : 0 < x / (x + 1) := div_pos hx h1
  have hu0 : 0 < 1 / (x + 1) := div_pos one_pos h1
  have a : x / (x + 1) ≤ (x / (x + 1)) ^ z := by
    simpa using Real.rpow_le_rpow_of_exponent_ge ht0 ((div_le_one h1).2 (by linarith)) hz
  have b : 1 / (x + 1) ≤ (1 / (x + 1)) ^ z := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hu0 ((div_le_one h1).2 (by linarith)) hz
  have e1 : (x + 1) ^ z * (x / (x + 1)) ^ z = x ^ z := by
    rw [← Real.mul_rpow h1.le ht0.le, mul_div_cancel₀ _ h1.ne']
  have e2 : (x + 1) ^ z * (1 / (x + 1)) ^ z = 1 := by
    rw [← Real.mul_rpow h1.le hu0.le, mul_one_div_cancel h1.ne', Real.one_rpow]
  have hp : 0 ≤ (x + 1) ^ z := Real.rpow_nonneg h1.le z
  have hs : x / (x + 1) + 1 / (x + 1) = 1 := by rw [← add_div, div_self h1.ne']
  have := add_le_add (mul_le_mul_of_nonneg_left a hp) (mul_le_mul_of_nonneg_left b hp)
  rw [← mul_add, hs, mul_one, e1, e2] at this
  exact this
/-- **A budget exists.** Under the rate `P r^z1 ≤ W m^z1` with `0 ≤ z1 < z ≤ 1`, some cutoff
`N ≥ n0` and some constant `C` make `J n = C 2^n ⌈(n+1)^z⌉` pay for every step of the recursion
at cutoff `N`. -/
theorem budget_exists {z1 z : ℝ} (hrate : (R.P : ℝ) * (R.r : ℝ) ^ z1 ≤ R.W * (R.m : ℝ) ^ z1)
    (hz1 : 0 ≤ z1) (hz : z1 < z) (hz' : z ≤ 1) {n0 : ℕ} (hm : R.m ≤ n0) :
    ∃ N C : ℕ, n0 ≤ N ∧ ∀ d : JobForm,
      R.jobLocalCost N d + 1 + ((R.jobKids N d).map (R.jobTotalCost N fun n => C * 2 ^ n * ⌈((n : ℝ) + 1) ^ z⌉₊)).sum ≤
        R.jobTotalCost N (fun n => C * 2 ^ n * ⌈((n : ℝ) + 1) ^ z⌉₊) d := by
  have hm0 : 0 < R.m := by have := R.r_pos; have := R.r_lt; omega
  have hr0 : (0 : ℝ) < R.r := by exact_mod_cast R.r_pos
  have hrm : (R.r : ℝ) < R.m := by exact_mod_cast R.r_lt
  have hmR : (0 : ℝ) < R.m := hr0.trans hrm
  have hW0 : (0 : ℝ) < R.W := by exact_mod_cast R.W_pos
  have hz0 : 0 < z := hz1.trans_lt hz
  have hq0 : (0 : ℝ) ≤ R.r / R.m := div_nonneg hr0.le hmR.le
  set l : ℝ := ((R.r : ℝ) / R.m) ^ (z - z1) with hl
  have hl1 : l < 1 := Real.rpow_lt_one hq0 ((div_lt_one hmR).2 hrm) (by linarith)
  -- the rate at every scale `k`
  have scale : ∀ k : ℕ, (R.P : ℝ) * ((R.r : ℝ) * k) ^ z ≤ R.W * l * ((R.m : ℝ) * k) ^ z := by
    intro k
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    rw [Real.mul_rpow hr0.le hk, Real.mul_rpow hmR.le hk]
    have e1 : (R.r : ℝ) ^ z = R.r ^ z1 * R.r ^ (z - z1) := by
      rw [← Real.rpow_add hr0]; congr 1; ring
    have e2 : (R.m : ℝ) ^ z = R.m ^ z1 * R.m ^ (z - z1) := by
      rw [← Real.rpow_add hmR]; congr 1; ring
    have e3 : l * (R.m : ℝ) ^ (z - z1) = R.r ^ (z - z1) := by
      rw [hl, Real.div_rpow hr0.le hmR.le, div_mul_cancel₀ _ (Real.rpow_pos_of_pos hmR _).ne']
    have hk' : 0 ≤ (k : ℝ) ^ z := Real.rpow_nonneg hk z
    have hrr : 0 ≤ (R.r : ℝ) ^ (z - z1) := Real.rpow_nonneg hr0.le _
    calc (R.P : ℝ) * ((R.r : ℝ) ^ z * (k : ℝ) ^ z)
        = (R.P * R.r ^ z1) * R.r ^ (z - z1) * k ^ z := by rw [e1]; ring
      _ ≤ (R.W * R.m ^ z1) * R.r ^ (z - z1) * k ^ z :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hrate hrr) hk'
      _ = R.W * l * ((R.m : ℝ) ^ z * k ^ z) := by rw [e2, ← e3]; ring
  -- the thresholds
  have hden : 0 < (R.W : ℝ) * (1 - l) := mul_pos hW0 (by linarith)
  set A : ℝ := (2 + R.W + 2 * R.P) / (R.W * (1 - l)) with hA
  have hA0 : 0 ≤ A := div_nonneg (by positivity) hden.le
  obtain ⟨N2, hN2⟩ := exists_N2 ((R.P + 1) * (R.W + 2)) R.m hm0
  refine ⟨max n0 (max ⌈A ^ z⁻¹⌉₊ N2), max n0 (max ⌈A ^ z⁻¹⌉₊ N2) + 1, le_max_left _ _,
    R.step_of_cover (fun n hn => ?_) (fun n hn => ?_)⟩
  · have hg : 0 < ⌈((n : ℝ) + 1) ^ z⌉₊ := Nat.ceil_pos.2 (Real.rpow_pos_of_pos (by positivity) z)
    exact (Nat.mul_le_mul_right _ (by omega)).trans (Nat.le_mul_of_pos_right _ hg)
  set N := max n0 (max ⌈A ^ z⁻¹⌉₊ N2) with hN
  have hn0 : n0 ≤ n := (le_max_left _ _).trans hn
  have hn1 : ⌈A ^ z⁻¹⌉₊ ≤ n := ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  have hn2 : N2 ≤ n := ((le_max_right _ _).trans (le_max_right _ _)).trans hn
  set k := n / R.m with hk
  have hk1 : 1 ≤ k := (Nat.one_le_div_iff hm0).2 (hm.trans hn0)
  have hmk : R.m * k ≤ n := Nat.mul_div_le n R.m
  have hrk : R.r * k + k ≤ n := by
    have := Nat.mul_le_mul_right k R.r_lt; rw [Nat.succ_mul] at this; omega
  set x := R.r * k with hx
  have hx1 : 1 ≤ x := Nat.mul_le_mul R.r_pos hk1
  have h2n : 2 ^ (n - x) * 2 ^ x = 2 ^ n := by rw [← pow_add, Nat.sub_add_cancel (by omega)]
  -- the overhead of the batches fits in `2^n`
  have hover : R.P * ((2 ^ (n - x) % R.W) * ((x + 1) * 2 ^ x) + (N + 1) * 2 ^ x + 1) + 1 ≤ 2 ^ n := by
    have hQ : (R.P + 1) * (R.W + 2) * (n + 1) ≤ 2 ^ (n - x) :=
      calc (R.P + 1) * (R.W + 2) * (n + 1)
          ≤ ((R.P + 1) * (R.W + 2) + 2) * (n + 1) ^ ((R.P + 1) * (R.W + 2) + 1) :=
            Nat.mul_le_mul (Nat.le_add_right _ _)
              (by simpa using Nat.pow_le_pow_right (Nat.succ_pos n) (Nat.le_add_left 1 _))
        _ ≤ 2 ^ k := hN2 n hn2
        _ ≤ 2 ^ (n - x) := Nat.pow_le_pow_right two_pos (by omega)
    set u := (n + 1) * 2 ^ x
    have hu : 1 ≤ u := Nat.mul_le_mul (Nat.succ_pos n) Nat.one_le_two_pow
    have hs : (2 ^ (n - x) % R.W) * ((x + 1) * 2 ^ x) ≤ R.W * u :=
      Nat.mul_le_mul (Nat.mod_lt _ R.W_pos).le (Nat.mul_le_mul_right _ (by omega))
    have hN1 : (N + 1) * 2 ^ x ≤ u := Nat.mul_le_mul_right _ (by omega)
    have a1 := Nat.mul_le_mul_left R.P (show (2 ^ (n - x) % R.W) * ((x + 1) * 2 ^ x) + (N + 1) * 2 ^ x + 1 ≤
      (R.W + 2) * u by linarith)
    have a2 := Nat.mul_le_mul_right (2 ^ x) hQ
    have a3 : 0 ≤ R.W * u := Nat.zero_le _
    have e : (R.P + 1) * (R.W + 2) * (n + 1) * 2 ^ x = (R.P + 1) * (R.W + 2) * u := by ring
    linarith
  -- the main term, in the reals
  set gx := ⌈((x : ℝ) + 1) ^ z⌉₊ with hgx
  set gn := ⌈((n : ℝ) + 1) ^ z⌉₊ with hgn
  have key : 2 + R.W + R.P * (N + 1) * gx ≤ R.W * (N + 1) * gn := by
    have hxR : (0 : ℝ) < x := by exact_mod_cast hx1
    have t0 : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ z := Real.rpow_nonneg (by positivity) z
    have hgx' : (gx : ℝ) ≤ (x : ℝ) ^ z + 2 := by
      have := Nat.ceil_lt_add_one (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ x + 1) z)
      have := succ_rpow_le hxR hz'
      linarith
    have hgn' : ((n : ℝ) + 1) ^ z ≤ gn := Nat.le_ceil _
    have hAt : A ≤ ((n : ℝ) + 1) ^ z := by
      have h1 : A ^ z⁻¹ ≤ (n : ℝ) + 1 := (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_succ_of_le hn1)
      calc A = (A ^ z⁻¹) ^ z := (Real.rpow_inv_rpow hA0 hz0.ne').symm
        _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hA0 _) h1 hz0.le
    have h3 : 2 + (R.W : ℝ) + 2 * R.P ≤ ((n : ℝ) + 1) ^ z * (R.W * (1 - l)) := (div_le_iff₀ hden).1 hAt
    have h2 : (R.P : ℝ) * (x : ℝ) ^ z ≤ R.W * l * ((n : ℝ) + 1) ^ z := by
      have hs := scale k
      have hmn : (R.m : ℝ) * k ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.le_succ_of_le hmk
      have := Real.rpow_le_rpow (by positivity) hmn hz0.le
      have hxk : ((x : ℕ) : ℝ) = (R.r : ℝ) * k := by rw [hx]; push_cast; ring
      rw [hxk]
      exact hs.trans (mul_le_mul_of_nonneg_left this (by positivity))
    have hP : (0 : ℝ) ≤ R.P := Nat.cast_nonneg _
    have h1 : (R.P : ℝ) * gx ≤ 2 * R.P + R.W * l * ((n : ℝ) + 1) ^ z := by
      have := mul_le_mul_of_nonneg_left hgx' hP
      linarith
    have hc : (1 : ℝ) ≤ (N : ℝ) + 1 := by have : (0 : ℝ) ≤ N := Nat.cast_nonneg _; linarith
    have hc0 : (0 : ℝ) ≤ (N : ℝ) + 1 := by linarith
    have hW : (0 : ℝ) ≤ R.W := hW0.le
    have k1 := mul_le_mul_of_nonneg_left h1 hc0
    have k2 := mul_le_mul_of_nonneg_left h3 hc0
    have k3 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgn' hW) hc0
    have k4 : (2 + (R.W : ℝ)) ≤ ((N : ℝ) + 1) * (2 + R.W) := le_mul_of_one_le_left (by positivity) hc
    have : (2 + R.W + R.P * (N + 1) * gx : ℝ) ≤ R.W * (N + 1) * gn := by linarith
    exact_mod_cast this
  rw [jobTotalCost_block]
  show 2 ^ n + 1 + R.P * R.jobTotalCost N _ (.batch x (2 ^ (n - x))) + R.W * 2 ^ n ≤ R.W * ((N + 1) * 2 ^ n * gn)
  have hb : R.jobTotalCost N (fun n => (N + 1) * 2 ^ n * ⌈((n : ℝ) + 1) ^ z⌉₊) (.batch x (2 ^ (n - x))) =
      (N + 1) * gx * 2 ^ n + ((2 ^ (n - x) % R.W) * ((x + 1) * 2 ^ x) + (N + 1) * 2 ^ x + 1) := by
    show 2 ^ (n - x) * ((N + 1) * 2 ^ x * gx) + _ + _ + 1 = _
    rw [← h2n]; ring
  rw [hb]
  have := Nat.mul_le_mul_right (2 ^ n) key
  have e : R.W * ((N + 1) * 2 ^ n * gn) = R.W * (N + 1) * gn * 2 ^ n := by ring
  rw [e]
  linarith
end Rule
end EngineCost
end OAI.PowerSaving
end
