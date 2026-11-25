import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic

/-! The padding and power-envelope induction are adapted from OpenAI's
FiniteFourier/PrimeKernel.lean, Apache-2.0. Here the integer recurrence
counts RAM work, takes two bits per template column, and charges the full
per-level data movement before summing recursive calls. -/
namespace DFTSpeedrun.HalfCost
open Filter
open scoped Topology
theorem exists_padding {ℓ A W σ : ℕ} {θ : ℝ} (hℓ : 1 < ℓ)
    (hs : (σ : ℝ) / W < (A : ℝ) ^ θ) :
    ∃ r : ℕ, A ≤ r ∧ (σ : ℝ) / W * (1 + (W : ℝ) / (ℓ : ℝ) ^ r) < (A : ℝ) ^ θ := by
  have ht := tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast hℓ : (1 : ℝ) < ℓ)
  have hl : Tendsto (fun r : ℕ => (σ : ℝ) / W * (1 + (W : ℝ) / (ℓ : ℝ) ^ r))
      atTop (𝓝 ((σ : ℝ) / W)) := by
    simpa using ((ht.const_div_atTop (W : ℝ)).const_add 1).const_mul ((σ : ℝ) / W)
  exact ((eventually_ge_atTop A).and (hl.eventually_lt_const hs)).exists

/-- Solve the single-array recurrence after reserving enough inactive digits
that `A * (1 + f) ≤ 1 + k` in every recursive call. -/
private theorem power_bound_of_recursion {T : ℕ → ℝ} {A k₀ : ℕ} {b C θ small : ℝ}
    (hA : 0 < A) (hb : 0 ≤ b) (hθ : 0 ≤ θ) (hs : b < (A : ℝ) ^ θ)
    (hsmall : 0 ≤ small) (hbase : ∀ k < k₀, T k ≤ small)
    (hstep : ∀ k, k₀ ≤ k → ∃ f < k, A * (1 + f) ≤ 1 + k ∧ T k ≤ C + b * T f) :
    ∀ k : ℕ, T k ≤ max (1 + small) (C / ((A : ℝ) ^ θ - b)) * (1 + (k : ℝ)) ^ θ := by
  let D := max (1 + small) (C / ((A : ℝ) ^ θ - b))
  have hD : 0 < D := lt_of_lt_of_le (by linarith : 0 < 1 + small) (le_max_left _ _)
  have hC : C ≤ D * ((A : ℝ) ^ θ - b) := (div_le_iff₀ (sub_pos.mpr hs)).mp (le_max_right _ _)
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    have hone (u : ℕ) : 1 ≤ (1 + (u : ℝ)) ^ θ :=
      Real.one_le_rpow (by linarith [Nat.cast_nonneg (α := ℝ) u]) hθ
    by_cases hk : k < k₀
    · calc
        T k ≤ small := hbase k hk
        _ ≤ D := (by linarith : small ≤ 1 + small).trans (le_max_left _ _)
        _ ≤ D * (1 + (k : ℝ)) ^ θ := le_mul_of_one_le_right hD.le (hone k)
    · obtain ⟨f, hfk, hsize, hrec⟩ := hstep k (by omega)
      have hsize' : (A : ℝ) * (1 + (f : ℝ)) ≤ 1 + (k : ℝ) := by exact_mod_cast hsize
      have hpow := Real.rpow_le_rpow (by positivity) hsize' hθ
      rw [Real.mul_rpow (Nat.cast_nonneg _) (by positivity)] at hpow
      have hcost := le_mul_of_one_le_right (mul_nonneg hD.le (sub_nonneg.mpr hs.le)) (hone f)
      calc
        T k ≤ C + b * T f := hrec
        _ ≤ C + b * (D * (1 + (f : ℝ)) ^ θ) := by gcongr; exact ih f hfk
        _ ≤ D * ((A : ℝ) ^ θ * (1 + (f : ℝ)) ^ θ) := by linarith [hC.trans hcost]
        _ ≤ D * (1 + (k : ℝ)) ^ θ := mul_le_mul_of_nonneg_left hpow hD.le

/-- Real-valued upper bound on the integer number of batches, accounting
for the last, possibly padded, batch. -/
private theorem ceil_div_real_le (H W : ℕ) (hW : 0 < W) :
    ((H ⌈/⌉ W : ℕ) : ℝ) ≤ (H : ℝ) / W + 1 := by
  rw [Nat.ceilDiv_eq_add_pred_div, show H + W - 1 = H + (W - 1) by omega]
  have hn := Nat.div_mul_le_self (H + (W - 1)) W
  have h : (H + (W-1)) / W * W ≤ H + W := by omega
  have h' : (((H + (W-1)) / W : ℕ) : ℝ) * W ≤ (H : ℝ) + W := by exact_mod_cast h
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  calc
    _ ≤ ((H : ℝ) + W) / W := (le_div_iff₀ hW').mpr h'
    _ = (H : ℝ) / W + 1 := by field_simp



def next (A r k : ℕ) := (k-r)/A
def spare (A r k : ℕ) := r+(k-r)%A

def children (A W σ r k : ℕ) :=
  (4^(spare A r k) ⌈/⌉ W) * σ * 4^((A-1)*next A r k)

/-- At a leaf the dense work per array entry is bounded by a template-dependent
constant. At an internal node this constant covers grouping, residual transforms,
and the linear passes of one invocation of the fixed template. -/
def budget (A W σ r C : ℕ) (hr : 0 < r) (k : ℕ) : ℕ :=
  C * 4^k + if r+A ≤ k then children A W σ r k * budget A W σ r C hr (next A r k) else 0
termination_by k
decreasing_by
  unfold next
  have := Nat.div_le_self (k-r) A
  omega

theorem budget_bound {A W σ r C : ℕ} {θ : ℝ}
    (hA : 0 < A) (hW : 0 < W) (hr : A ≤ r) (hθ : 0 ≤ θ)
    (hsave : (σ:ℝ)/W * (1+(W:ℝ)/(4:ℝ)^r) < (A:ℝ)^θ) :
    ∃ K : ℝ, ∀ k, (budget A W σ r C (lt_of_lt_of_le hA hr) k : ℝ) ≤
        K * (4:ℝ)^k * (1+(k:ℝ))^θ := by
  let T (k : ℕ) : ℝ := budget A W σ r C (lt_of_lt_of_le hA hr) k / (4:ℝ)^k
  let b := (σ:ℝ)/W*(1+(W:ℝ)/(4:ℝ)^r)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have base (k : ℕ) (hk : k < r+A) : T k ≤ C := by
    unfold T
    rw [budget, if_neg (by omega : ¬r+A ≤ k)]
    simp
  have step (k : ℕ) (hk : r+A ≤ k) :
      ∃ f < k, A*(1+f) ≤ 1+k ∧ T k ≤ C + b*T f := by
    let f := next A r k
    let h := spare A r k
    have rem : A*f+h=k := by
      dsimp [f,h,next,spare]
      have := Nat.mod_add_div (k-r) A
      omega
    have rh : r ≤ h := Nat.le_add_right _ _
    have posf : 0 < f := Nat.div_pos (by omega) hA
    have lt : f < k := by have := Nat.le_mul_of_pos_left f hA; omega
    refine ⟨f,lt,by rw [Nat.mul_add,Nat.mul_one]; omega,?_⟩
    have split : (4:ℝ)^k = 4^h * 4^((A-1)*f) * 4^f := by
      rw [←pow_add,←pow_add]; congr 1
      have e : (A-1)*f+f=A*f := by rw [←Nat.succ_mul]; congr 1; omega
      omega
    have ratio := ceil_div_real_le (4^h) W hW
    push_cast at ratio
    have hpow : (4:ℝ)^r ≤ 4^h := pow_le_pow_right₀ (by norm_num) rh
    have rpos : (0:ℝ)<4^r := by positivity
    have hp : (0:ℝ)<4^h := by positivity
    have wpos : (0:ℝ)<W := Nat.cast_pos.mpr hW
    have weight : ((4^h ⌈/⌉ W : ℕ):ℝ)*(σ:ℝ)/(4:ℝ)^h ≤ b := calc
      _ ≤ ((4:ℝ)^h/W+1)*σ/4^h := by gcongr
      _ = (σ:ℝ)/W*(1+W/4^h) := by field_simp
                                    <;> ring
      _ ≤ b := by unfold b; gcongr
    have tk : 0 ≤ T f := by dsimp [T]; positivity
    have ev : T k = C + (((4^h ⌈/⌉ W : ℕ):ℝ)*σ/4^h)*T f := by
      unfold T
      rw [budget,if_pos hk]
      simp only [children, show spare A r k=h from rfl, show next A r k=f from rfl]
      push_cast
      rw [split]
      field_simp
      all_goals ring
    rw [ev]; exact add_le_add le_rfl (mul_le_mul_of_nonneg_right weight tk)
  have ans := power_bound_of_recursion hA hb hθ hsave (Nat.cast_nonneg C) base step
  refine ⟨max (1+(C:ℝ)) ((C:ℝ)/((A:ℝ)^θ-b)),fun k => ?_⟩
  have h := (div_le_iff₀ (by positivity : (0:ℝ)<4^k)).mp (ans k)
  rw [mul_right_comm] at h
  exact h
end DFTSpeedrun.HalfCost
