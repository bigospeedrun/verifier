import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity

/-!
# The Appendix A scalar certificate for the matroid prophet bound C₁₄₁

Formalizes the complete exact scalar certificate of Appendix A (and the parameter
inequalities (3)–(5) of §1) of Chen–Euler, "Matroid Prophet Inequality with a
Constant Factor via ..." (Big O Speedrun record `C₁₄₁ ≈ 5.107 × 10⁻¹⁰` for the
matroid prophet problem, Claimed 2026-10-19; source:
`canghaimeng/openai-math-improvement`, `problems/bound-111/paper.pdf`).

Everything proved here is exact rational/real arithmetic about the paper's
displayed parameter values: the tilt inequalities (3), the parameter conditions
(4) (including `d < -log p`, i.e. `0 < d < λ`), the monotonicity of `s` and `C`
on `[141, ∞)`, `s(141) > 0`, and the final comparison (5)
`C(B) ≥ C(141) = C₁₄₁ > 2⁻²⁹³`, with `B = θ²⁵⁶ > 141`.

Scope: this is the scalar certificate only. The universal matroid argument
(reduction to the slot curves, sampling, and the fixed-vector analysis) remains
written proof, inherited from OpenAI/Shea; see README.md in the package.

The paper's own rational check for `d < -log p` is the 4-term atanh truncation
(eq. (32)); we record that rational inequality as `d_lt_S4` and prove
`d < -log p` over ℝ using Mathlib's certified bounds `Real.exp_one_lt_d9` and
`Real.exp_bound'` instead (same method substitution as the average-sensitivity
package's use of Mathlib's π bound).
-/

namespace MatroidProphet

/-- The record constant `C₁₄₁` of the paper (exact rational). -/
def C141 : ℚ := 165971304277649481670619 / 324956758716416046811841770291200

/-! ### The paper's parameters (Appendix A), as exact rationals -/

/-- `κ = 164` -/
def κ : ℚ := 164
/-- `ρ = 93/256` -/
def ρ : ℚ := 93 / 256
/-- `h = 3/4` -/
def h : ℚ := 3 / 4
/-- `t = 23/262144` -/
def t : ℚ := 23 / 262144
/-- `θ = 261/256` -/
def θ : ℚ := 261 / 256
/-- `L = 256` (used through `256 * (θ - 1) = 5`) -/
def L : ℚ := 256
/-- `μ = 105/8` -/
def μ : ℚ := 105 / 8
/-- `ν = 113/8` -/
def ν : ℚ := 113 / 8
/-- `a = 1/864` -/
def a : ℚ := 1 / 864
/-- `b = 1/4000` -/
def b : ℚ := 1 / 4000
/-- `v = 1/624` -/
def v : ℚ := 1 / 624
/-- `d = 253/250` -/
def d : ℚ := 253 / 250
/-- `K = κ + ν = 1425/8` -/
def K : ℚ := κ + ν
/-- `p = ρ + (1 - ρ) t` -/
def p : ℚ := ρ + (1 - ρ) * t
/-- `bY = ((2/3) a (1/ρ - 1) + b) / (1 + a) + 2v` -/
def bY : ℚ := ((2 / 3) * a * (1 / ρ - 1) + b) / (1 + a) + 2 * v
/-- `γ = ρ/4 - bY / d` -/
def γ : ℚ := ρ / 4 - bY / d
/-- `ε = μρ/κ + a/d` -/
def ε : ℚ := μ * ρ / κ + a / d
/-- `a₀ = 1/d` -/
def a0 : ℚ := 1 / d
/-- `R = Kt + Kρ/κ` (the constant in the loss curve) -/
def Rc : ℚ := K * t + K * ρ / κ
/-- The loss curve `loss(x) = ε + Kt + R / (x - 1)`. -/
def loss (x : ℚ) : ℚ := ε + K * t + Rc / (x - 1)
/-- The slot curve `s(x) = (1 - h) (γ - loss(x) / h)`. -/
def sCurve (x : ℚ) : ℚ := (1 - h) * (γ - loss x / h)
/-- The constant curve `C(x) = (1 - t) ((x-1)/x)² t s(x) / (5K)`. -/
def CCurve (x : ℚ) : ℚ := (1 - t) * ((x - 1) / x) ^ 2 * t * sCurve x / (5 * K)
/-- `B = θ^L = θ^256` -/
def B : ℚ := θ ^ 256
/-- `β = (B - 1) / B` -/
def β : ℚ := (B - 1) / B
/-- The tilt constant `A = ρ (3 + 4v/3)` of eq. (31). -/
def A : ℚ := ρ * (3 + 4 * v / 3)

/-! ### Exact values of the derived parameters -/

theorem p_value : p = 24383141 / 67108864 := by norm_num [p, ρ, t]

theorem gamma_value : γ = 69959099203 / 812800834560 := by
  norm_num [γ, bY, ρ, a, b, v, d]

theorem epsilon_value : ε = 69328715 / 2294341632 := by norm_num [ε, μ, ρ, κ, a, d]

theorem a0_value : a0 = 250 / 253 := by norm_num [a0, d]

theorem A_value : A = 130665 / 119808 := by norm_num [A, ρ, v]

/-! ### The conditions (4) over ℚ -/

theorem gamma_pos : 0 < γ := by
  rw [gamma_value]; norm_num

theorem gamma_le : γ ≤ ρ / 4 := by
  norm_num [γ, bY, ρ, a, b, v, d]

theorem quarter_bound : (1 - t) * (γ * κ + a0) / K ≤ 1 / 4 := by
  norm_num [t, γ, bY, ρ, a, b, v, d, κ, a0, K, ν]

theorem Rc_pos : 0 < Rc := by norm_num [Rc, K, κ, ν, t, ρ]

theorem K_pos : 0 < K := by norm_num [K, κ, ν]

theorem t_pos : 0 < t := by norm_num [t]

/-! ### Values at `x = 141` and `x = 140`; the gain over the predecessor -/

theorem sCurve141_value : sCurve 141 = 3932831273804099 / 747774506088529920 := by
  norm_num [sCurve, loss, ε, μ, ρ, κ, a, d, γ, bY, b, v, h, Rc, K, ν, t]

theorem sCurve141_pos : 0 < sCurve 141 := by
  rw [sCurve141_value]; norm_num

theorem CCurve141_value : CCurve 141 = C141 := by
  norm_num [CCurve, sCurve, loss, ε, μ, ρ, κ, a, d, γ, bY, b, v, h, Rc, K, ν, t, C141]

theorem CCurve140_value :
    CCurve 140 = 4084754449786906742230661 / 8009094702029267287249256448000000 := by
  norm_num [CCurve, sCurve, loss, ε, μ, ρ, κ, a, d, γ, bY, b, v, h, Rc, K, ν, t]

theorem CCurve_gain :
    CCurve 141 - CCurve 140
      = 116935879834753076315538659 / 159228811771043862937802467442688000000 := by
  rw [CCurve141_value, CCurve140_value]; norm_num [C141]

set_option exponentiation.threshold 512 in
theorem CCurve141_gt : (1 / 2 : ℚ) ^ 293 < CCurve 141 := by
  have h : (1 : ℚ) * 324956758716416046811841770291200
      < 165971304277649481670619 * 2 ^ 293 := by norm_num
  rw [CCurve141_value]
  unfold C141
  rw [div_pow, one_pow, div_lt_div_iff₀ (by positivity) (by norm_num)]
  exact h

/-! ### Monotonicity of `s` and `C` on `[141, ∞)` -/

/-- The difference of the slot curve is a single positive term:
`s(y) - s(x) = (1 - h) (R/h) (y - x) / ((x - 1)(y - 1))`. -/
theorem sCurve_diff (x y : ℚ) (hx : x ≠ 1) (hy : y ≠ 1) :
    sCurve y - sCurve x = (1 - h) * (Rc / h) * (y - x) / (x - 1) / (y - 1) := by
  have hx1 : x - 1 ≠ 0 := sub_ne_zero.mpr hx
  have hy1 : y - 1 ≠ 0 := sub_ne_zero.mpr hy
  have key : Rc / (x - 1) - Rc / (y - 1) = Rc * (y - x) / (x - 1) / (y - 1) := by
    rw [div_sub_div _ _ hx1 hy1, div_div]
    congr 1
    ring
  have expand : sCurve y - sCurve x
      = (1 - h) * ((Rc / (x - 1) - Rc / (y - 1)) / h) := by
    simp only [sCurve, loss]
    ring
  rw [expand, key]
  ring

theorem sCurve_strictMono {x y : ℚ} (hx : 141 ≤ x) (hxy : x < y) :
    sCurve x < sCurve y := by
  have h1 : (0:ℚ) < x - 1 := by linarith
  have h2 : (0:ℚ) < y - 1 := by linarith
  have hcore : (0:ℚ) < (1 - h) * (Rc / h) * (y - x) :=
    mul_pos (mul_pos (by norm_num [h]) (div_pos Rc_pos (by norm_num [h]))) (by linarith)
  have hdiff : (0:ℚ) < (1 - h) * (Rc / h) * (y - x) / (x - 1) / (y - 1) :=
    div_pos (div_pos hcore h1) h2
  have hsd := sCurve_diff x y (by linarith) (by linarith)
  linarith

theorem sCurve_pos_of_ge {x : ℚ} (hx : 141 ≤ x) : 0 < sCurve x := by
  rcases eq_or_lt_of_le hx with hxx | hxx
  · rw [← hxx]; exact sCurve141_pos
  · exact lt_trans sCurve141_pos (sCurve_strictMono le_rfl hxx)

/-- `C(x)` in factored form. -/
theorem CCurve_eq (x : ℚ) :
    CCurve x = ((1 - t) * t / (5 * K)) * ((x - 1) / x) ^ 2 * sCurve x := by
  simp only [CCurve]
  ring

theorem CCurve_strictMono {x y : ℚ} (hx : 141 ≤ x) (hxy : x < y) :
    CCurve x < CCurve y := by
  have hy : 141 ≤ y := le_trans hx hxy.le
  have hx0 : (0:ℚ) < x := by linarith
  have hy0 : (0:ℚ) < y := by linarith
  have hs_diff : 0 < sCurve y - sCurve x := sub_pos.mpr (sCurve_strictMono hx hxy)
  have hsx : 0 < sCurve x := sCurve_pos_of_ge hx
  have hg : (x - 1) / x < (y - 1) / y := by
    rw [div_lt_div_iff₀ hx0 hy0]
    nlinarith [hxy]
  have hA : (0:ℚ) ≤ (x - 1) / x := by
    apply div_nonneg (by linarith) hx0.le
  have hB : (0:ℚ) < (y - 1) / y := by
    apply div_pos (by linarith) hy0
  have hg2 : ((x - 1) / x) ^ 2 < ((y - 1) / y) ^ 2 := by
    nlinarith [hg, hA, hB, mul_pos (sub_pos.mpr hg) (add_pos_of_pos_of_nonneg hB hA)]
  have hc1 : (0:ℚ) < (1 - t) * t / (5 * K) := by
    apply div_pos
    · apply mul_pos _ t_pos
      norm_num [t]
    · exact mul_pos (by norm_num) K_pos
  have e : CCurve y - CCurve x
      = ((1 - t) * t / (5 * K))
        * (((y - 1) / y) ^ 2 * (sCurve y - sCurve x) + sCurve x * (((y - 1) / y) ^ 2 - ((x - 1) / x) ^ 2)) := by
    rw [CCurve_eq, CCurve_eq]
    ring
  have hpos : (0:ℚ) < ((1 - t) * t / (5 * K))
      * (((y - 1) / y) ^ 2 * (sCurve y - sCurve x) + sCurve x * (((y - 1) / y) ^ 2 - ((x - 1) / x) ^ 2)) := by
    apply mul_pos hc1
    apply add_pos
    · exact mul_pos (pow_pos hB 2) hs_diff
    · exact mul_pos hsx (sub_pos.mpr hg2)
  linarith

/-! ### `B = θ^256 > 141` and the final comparison (5) -/

theorem B_gt_141 : (141:ℚ) < B := by norm_num [B, θ]

theorem sCurve_B_pos : 0 < sCurve B := sCurve_pos_of_ge B_gt_141.le

theorem CCurve_B_gt : CCurve 141 < CCurve B :=
  CCurve_strictMono le_rfl B_gt_141

/-- The identity behind (5): the paper's `(1-t) β² t s(B) / (L (θ-1) K)` is `C(B)`,
since `L (θ - 1) = 256 · (5/256) = 5` and `β = (B-1)/B`. -/
theorem eq5_form :
    (1 - t) * β ^ 2 * t * sCurve B / (L * (θ - 1) * K) = CCurve B := by
  have hθ : L * (θ - 1) = 5 := by norm_num [L, θ]
  rw [hθ]
  simp only [β, CCurve]

/-- The paper's (5): the certified lower bound exceeds `C₁₄₁`. -/
theorem constant_bound :
    C141 < (1 - t) * β ^ 2 * t * sCurve B / (L * (θ - 1) * K) := by
  rw [eq5_form, ← CCurve141_value]
  exact CCurve_B_gt

/-! ### The paper's rational atanh check (32), left inequality: `d < S₄` -/

/-- `S₄ = 2 (ζ + ζ³/3 + ζ⁵/5 + ζ⁷/7)` with `ζ = (1-p)/(1+p)`, compared to `d`. -/
theorem d_lt_S4 :
    d < 2 * ((1 - p) / (1 + p) + ((1 - p) / (1 + p)) ^ 3 / 3
      + ((1 - p) / (1 + p)) ^ 5 / 5 + ((1 - p) / (1 + p)) ^ 7 / 7) := by
  norm_num [d, p, ρ, t]

/-! ### The tilt inequalities (3) and `d < λ = -log p`, over ℝ -/

/-- The exact rational heart of tilt 1: `A⁸ p¹⁰⁵ < (av)⁸` in ℚ. -/
theorem tilt1_rat : A ^ 8 * p ^ 105 < (a * v) ^ 8 := by
  norm_num [A, ρ, v, p, t, a]

/-- The exact rational heart of tilt 2: `(1-p)⁸ p¹¹³ < (bv)⁸` in ℚ. -/
theorem tilt2_rat : (1 - p) ^ 8 * p ^ 113 < (b * v) ^ 8 := by
  norm_num [p, ρ, t, b, v]

theorem p_pos_rat : 0 < p := by norm_num [p, ρ, t]

private theorem cast_pos {q : ℚ} (hq : 0 < q) : (0:ℝ) < (q : ℝ) := by exact_mod_cast hq

/-- Tilt 1 of (3): `ρ p^μ (p^(-1/4) + 3/v) ≤ a` over ℝ, via the 8th root `z = p^(1/8)`. -/
theorem tilt_one : (ρ : ℝ) * (p : ℝ) ^ (μ : ℝ) * ((p : ℝ) ^ ((-1 / 4 : ℝ)) + 3 / (v : ℝ)) ≤ (a : ℝ) := by
  have hp0 : (0:ℝ) < (p : ℝ) := cast_pos p_pos_rat
  have hρ0 : (0:ℝ) < (ρ : ℝ) := by exact_mod_cast (by norm_num [ρ] : (0:ℚ) < ρ)
  have hv0 : (0:ℝ) < (v : ℝ) := by exact_mod_cast (by norm_num [v] : (0:ℚ) < v)
  have ha0 : (0:ℝ) < (a : ℝ) := by exact_mod_cast (by norm_num [a] : (0:ℚ) < a)
  have hA0 : (0:ℝ) < (A : ℝ) := by
    exact_mod_cast (by norm_num [A, ρ, v] : (0:ℚ) < A)
  -- the 8th root and its powers
  set z : ℝ := (p : ℝ) ^ (((8 : ℕ) : ℝ)⁻¹) with hz_def
  have hz0 : 0 < z := Real.rpow_pos_of_pos hp0 _
  have hz8 : z ^ 8 = (p : ℝ) := Real.rpow_inv_natCast_pow hp0.le (by norm_num)
  have hμ : (p : ℝ) ^ (μ : ℝ) = z ^ 105 := by
    have h1 : (μ : ℝ) = ((8 : ℕ) : ℝ)⁻¹ * ((105 : ℕ) : ℝ) := by
      simp only [μ]; push_cast; norm_num
    rw [h1, Real.rpow_mul hp0.le, Real.rpow_natCast]
  have h4 : (p : ℝ) ^ ((1 / 4 : ℝ)) = z ^ 2 := by
    have h1 : (1 / 4 : ℝ) = ((8 : ℕ) : ℝ)⁻¹ * ((2 : ℕ) : ℝ) := by
      push_cast; norm_num
    rw [h1, Real.rpow_mul hp0.le, Real.rpow_natCast]
  have hneg4 : (p : ℝ) ^ ((-1 / 4 : ℝ)) = (z ^ 2)⁻¹ := by
    have h1 : (-1 / 4 : ℝ) = -((1 / 4 : ℝ)) := by norm_num
    rw [h1, Real.rpow_neg hp0.le, h4]
  -- `p > (3/4)^4`, hence `z^2 = p^(1/4) > 3/4`
  have hp4 : ((3 / 4 : ℚ)) ^ 4 < p := by norm_num [p, ρ, t]
  have hz2 : (3 / 4 : ℝ) < z ^ 2 := by
    have hcast : ((3 / 4 : ℝ)) ^ 4 < (p : ℝ) := by
      have h' : ((3 / 4 : ℚ) ^ 4 : ℝ) < (p : ℝ) := by exact_mod_cast hp4
      push_cast at h'
      exact h'
    have h24 : (z ^ 2) ^ 4 = (p : ℝ) := by rw [← pow_mul]; exact hz8
    by_contra hcon
    have hle : z ^ 2 ≤ 3 / 4 := le_of_not_gt hcon
    have := pow_le_pow_left₀ (pow_nonneg hz0.le 2) hle 4
    rw [h24] at this
    linarith
  have hzinv : (z ^ 2)⁻¹ < 4 / 3 := by
    have h2 : (1 : ℝ) / (z ^ 2) < 1 / (3 / 4 : ℝ) :=
      one_div_lt_one_div_of_lt (by norm_num) hz2
    norm_num at h2
    exact h2
  -- the 8th-power comparison in ℝ
  have key8 : (A : ℝ) * z ^ 105 < (a : ℝ) * (v : ℝ) := by
    by_contra hcon
    have hle : (a : ℝ) * (v : ℝ) ≤ (A : ℝ) * z ^ 105 := le_of_not_gt hcon
    have h1 : ((a : ℝ) * (v : ℝ)) ^ 8 ≤ ((A : ℝ) * z ^ 105) ^ 8 :=
      pow_le_pow_left₀ (mul_nonneg ha0.le hv0.le) hle 8
    have h2 : ((A : ℝ) * z ^ 105) ^ 8 = (A : ℝ) ^ 8 * (p : ℝ) ^ 105 := by
      rw [mul_pow, ← pow_mul, show 105 * 8 = 8 * 105 from rfl, pow_mul, hz8]
    have h3 : ((A : ℝ)) ^ 8 * (p : ℝ) ^ 105 < ((a : ℝ) * (v : ℝ)) ^ 8 := by
      exact_mod_cast tilt1_rat
    linarith [h1, h2, h3]
  -- assembly
  have hAeq : (A : ℝ) = (ρ : ℝ) * (3 + 4 * (v : ℝ) / 3) := by
    simp only [A]
    push_cast
    ring
  have hz105 : 0 < z ^ 105 := pow_pos hz0 105
  have hlt : (ρ : ℝ) * (p : ℝ) ^ (μ : ℝ) * ((p : ℝ) ^ ((-1 / 4 : ℝ)) + 3 / (v : ℝ)) < (a : ℝ) := by
    calc (ρ : ℝ) * (p : ℝ) ^ (μ : ℝ) * ((p : ℝ) ^ ((-1 / 4 : ℝ)) + 3 / (v : ℝ))
        = (ρ : ℝ) * z ^ 105 * ((z ^ 2)⁻¹ + 3 / (v : ℝ)) := by rw [hμ, hneg4]
      _ < (ρ : ℝ) * z ^ 105 * (4 / 3 + 3 / (v : ℝ)) := by
          apply mul_lt_mul_of_pos_left _ (mul_pos hρ0 hz105)
          gcongr
      _ = (A : ℝ) * z ^ 105 / (v : ℝ) := by
          rw [hAeq]
          field_simp [hv0.ne']
          ring
      _ < (a : ℝ) * (v : ℝ) / (v : ℝ) := by
          exact (div_lt_div_iff_of_pos_right hv0).mpr key8
      _ = (a : ℝ) := mul_div_cancel_right₀ _ hv0.ne'
  exact hlt.le

/-- Tilt 2 of (3): `(1 - p) p^ν / v ≤ b` over ℝ. -/
theorem tilt_two : (1 - (p : ℝ)) * (p : ℝ) ^ (ν : ℝ) / (v : ℝ) ≤ (b : ℝ) := by
  have hp0 : (0:ℝ) < (p : ℝ) := cast_pos p_pos_rat
  have hp1 : (0:ℝ) < 1 - (p : ℝ) := by
    have h1 : (p : ℝ) < 1 := by exact_mod_cast (by norm_num [p, ρ, t] : p < 1)
    linarith
  have hv0 : (0:ℝ) < (v : ℝ) := by exact_mod_cast (by norm_num [v] : (0:ℚ) < v)
  have hb0 : (0:ℝ) < (b : ℝ) := by exact_mod_cast (by norm_num [b] : (0:ℚ) < b)
  set z : ℝ := (p : ℝ) ^ (((8 : ℕ) : ℝ)⁻¹) with hz_def
  have hz0 : 0 < z := Real.rpow_pos_of_pos hp0 _
  have hz8 : z ^ 8 = (p : ℝ) := Real.rpow_inv_natCast_pow hp0.le (by norm_num)
  have hν : (p : ℝ) ^ (ν : ℝ) = z ^ 113 := by
    have h1 : (ν : ℝ) = ((8 : ℕ) : ℝ)⁻¹ * ((113 : ℕ) : ℝ) := by
      simp only [ν]; push_cast; norm_num
    rw [h1, Real.rpow_mul hp0.le, Real.rpow_natCast]
  have key8 : (1 - (p : ℝ)) * z ^ 113 < (b : ℝ) * (v : ℝ) := by
    by_contra hcon
    have hle : (b : ℝ) * (v : ℝ) ≤ (1 - (p : ℝ)) * z ^ 113 := le_of_not_gt hcon
    have h1 : ((b : ℝ) * (v : ℝ)) ^ 8 ≤ ((1 - (p : ℝ)) * z ^ 113) ^ 8 :=
      pow_le_pow_left₀ (mul_nonneg hb0.le hv0.le) hle 8
    have h2 : ((1 - (p : ℝ)) * z ^ 113) ^ 8 = (1 - (p : ℝ)) ^ 8 * (p : ℝ) ^ 113 := by
      rw [mul_pow, ← pow_mul, show 113 * 8 = 8 * 113 from rfl, pow_mul, hz8]
    have h3 : (1 - (p : ℝ)) ^ 8 * (p : ℝ) ^ 113 < ((b : ℝ) * (v : ℝ)) ^ 8 := by
      exact_mod_cast tilt2_rat
    linarith [h1, h2, h3]
  have hlt : (1 - (p : ℝ)) * (p : ℝ) ^ (ν : ℝ) / (v : ℝ) < (b : ℝ) := by
    calc (1 - (p : ℝ)) * (p : ℝ) ^ (ν : ℝ) / (v : ℝ)
        = (1 - (p : ℝ)) * z ^ 113 / (v : ℝ) := by rw [hν]
      _ < (b : ℝ) * (v : ℝ) / (v : ℝ) := by
          exact (div_lt_div_iff_of_pos_right hv0).mpr key8
      _ = (b : ℝ) := mul_div_cancel_right₀ _ hv0.ne'
  exact hlt.le

/-- `0 < d < λ`, i.e. `d < -log p`, over ℝ. Proved via
`p * exp d < 1` with `exp d = exp 1 * exp (3/250)` bounded by
`Real.exp_one_lt_d9` and `Real.exp_bound'` (n = 3). -/
theorem d_lt_neg_log_p : (d : ℝ) < -Real.log (p : ℝ) := by
  have hp0 : (0:ℝ) < (p : ℝ) := cast_pos p_pos_rat
  have hdeq : (d : ℝ) = 1 + 3 / 250 := by norm_num [d]
  have h_exp3 : Real.exp (3 / 250 : ℝ) ≤ 15813631 / 15625000 := by
    have h := Real.exp_bound' (x := (3 / 250 : ℝ)) (by norm_num) (by norm_num)
      (n := 3) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    exact h
  have he1 : Real.exp 1 < (27182818286 : ℝ) / 10000000000 := by
    have h := Real.exp_one_lt_d9
    norm_num at h
    linarith [h]
  have h_expd : Real.exp (d : ℝ)
      ≤ ((27182818286 : ℝ) / 10000000000) * (15813631 / 15625000) := by
    rw [hdeq, Real.exp_add]
    exact mul_le_mul he1.le h_exp3 (Real.exp_nonneg _) (by norm_num)
  have hprod : (p : ℝ) * Real.exp (d : ℝ) < 1 := by
    have h1 : (p : ℝ) * Real.exp (d : ℝ)
        ≤ (p : ℝ) * (((27182818286 : ℝ) / 10000000000) * (15813631 / 15625000)) :=
      mul_le_mul_of_nonneg_left h_expd hp0.le
    have h2 : (p : ℝ) * (((27182818286 : ℝ) / 10000000000) * (15813631 / 15625000)) < 1 := by
      have hpeq : (p : ℝ) = ((24383141 / 67108864 : ℚ) : ℝ) := by rw [p_value]
      rw [hpeq]
      norm_num
    linarith
  have hlt : (p : ℝ) < Real.exp (-(d : ℝ)) := by
    have h2 : Real.exp (-(d : ℝ)) = (Real.exp (d : ℝ))⁻¹ := Real.exp_neg _
    rw [h2, ← one_div, lt_div_iff₀ (Real.exp_pos _)]
    simpa using hprod
  have := (Real.log_lt_iff_lt_exp hp0).mpr hlt
  linarith

/-! ### The certificate as a single statement -/

/-- **Appendix A scalar certificate** (paper §1 (3)–(5) + Appendix A):
with the paper's exact rational parameters, the tilt inequalities hold over ℝ,
`0 < d < -log p`, the parameter conditions (4) hold over ℚ, and the final
constant satisfies `C₁₄₁ < (1-t) β² t s(B) / (L (θ-1) K)`, `B = θ²⁵⁶`. -/
theorem appendixA_certificate :
    (ρ : ℝ) * (p : ℝ) ^ (μ : ℝ) * ((p : ℝ) ^ ((-1 / 4 : ℝ)) + 3 / (v : ℝ)) ≤ (a : ℝ)
    ∧ (1 - (p : ℝ)) * (p : ℝ) ^ (ν : ℝ) / (v : ℝ) ≤ (b : ℝ)
    ∧ (d : ℝ) < -Real.log (p : ℝ)
    ∧ (0 < γ ∧ γ ≤ ρ / 4)
    ∧ (1 - t) * (γ * κ + a0) / K ≤ 1 / 4
    ∧ C141 < (1 - t) * β ^ 2 * t * sCurve B / (L * (θ - 1) * K) :=
  ⟨tilt_one, tilt_two, d_lt_neg_log_p, ⟨gamma_pos, gamma_le⟩, quarter_bound,
   constant_bound⟩

end MatroidProphet

#print axioms MatroidProphet.appendixA_certificate
#print axioms MatroidProphet.constant_bound
#print axioms MatroidProphet.CCurve141_value
#print axioms MatroidProphet.CCurve141_gt
#print axioms MatroidProphet.d_lt_S4
