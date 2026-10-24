module

public import Statement
public import Mathlib.Tactic

public section

open Filter BigOSpeedrun.Catalan

namespace CatalanStatementValidation

/-- Elaboration checks the pinned source's 740 statement literally, without
importing Challenge.lean, which is a statement template with proof holes. -/
theorem source_740_shape : Endpoint constant 740 ↔
    (∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(740 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b|) := by
  rfl

/-- Conditional bridge only: this does not prove the source's endpoint. -/
theorem endpoint_implies_upperBoundFor {x r : ℝ} (h : Endpoint x r) :
    UpperBoundFor x r := by
  intro s hrs
  filter_upwards [h, eventually_ge_atTop 1] with b hb hb1
  intro a _
  have hbR : 1 ≤ (b : ℝ) := by exact_mod_cast hb1
  exact (Real.rpow_le_rpow_of_exponent_le hbR (neg_le_neg hrs.le)).trans_lt (hb a)

theorem source_740_implies_bound (h : Endpoint constant 740) : Bound 740 := by
  refine ⟨by norm_num, ?_⟩
  exact endpoint_implies_upperBoundFor h

/-- Raising an upper bound weakens the proposition. -/
theorem upperBoundFor_mono {x r t : ℝ} (hrt : r ≤ t)
    (h : UpperBoundFor x r) : UpperBoundFor x t := by
  intro s hts
  exact h s (hrt.trans_lt hts)

theorem bound_mono {r t : ℚ} (hrt : r ≤ t) (h : Bound r) : Bound t := by
  refine ⟨h.1.trans hrt, ?_⟩
  exact upperBoundFor_mono (by exact_mod_cast hrt) h.2

/-- Positive control: the rational number zero has upper exponent at most one.
The exclusion of exact approximations is necessary for this control. -/
theorem zero_has_upperBound_one : UpperBoundFor 0 1 := by
  intro s hs
  filter_upwards [eventually_ge_atTop 2] with b hb
  intro a hne
  have hbR2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hbR : 1 < (b : ℝ) := by linarith
  have hbpos : 0 < (b : ℝ) := lt_trans zero_lt_one hbR
  have ha : a ≠ 0 := by
    intro ha
    apply hne
    simp [ha]
  have haR : (1 : ℝ) ≤ |(a : ℝ)| := by
    exact_mod_cast (Int.one_le_abs ha)
  have hs' : (b : ℝ) ^ (-s) < (b : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt hbR (by linarith)
  have hdiv : (b : ℝ)⁻¹ ≤ |0 - (a : ℝ) / (b : ℝ)| := by
    rw [zero_sub, abs_neg, abs_div, abs_of_pos hbpos, ← one_div]
    exact (div_le_div_iff_of_pos_right hbpos).mpr haR
  exact hs'.trans_le (by simpa only [Real.rpow_neg_one] using hdiv)

/-- Wrong-bound control for every real x, including Catalan's constant.
The numerator floor(b*x)+1 always gives nonzero error at most 1/b. -/
theorem no_upperBound_zero (x : ℝ) : ¬ UpperBoundFor x 0 := by
  intro h
  obtain ⟨B, hB⟩ := eventually_atTop.mp (h 1 (by norm_num))
  let b : ℕ := max B 1
  have hbB : B ≤ b := le_max_left _ _
  have hb1 : 1 ≤ b := le_max_right _ _
  have hbposN : 0 < b := lt_of_lt_of_le Nat.zero_lt_one hb1
  have hbpos : (0 : ℝ) < b := by exact_mod_cast hbposN
  let a : ℤ := ⌊(b : ℝ) * x⌋ + 1
  have hlo : (b : ℝ) * x < (a : ℝ) := by
    simpa only [a, Int.cast_add, Int.cast_one] using Int.lt_floor_add_one ((b : ℝ) * x)
  have hhi : (a : ℝ) ≤ (b : ℝ) * x + 1 := by
    dsimp [a]
    push_cast
    linarith [Int.floor_le ((b : ℝ) * x)]
  have hxa : x < (a : ℝ) / (b : ℝ) :=
    (lt_div_iff₀ hbpos).mpr (by nlinarith [hlo])
  have herr : |x - (a : ℝ) / (b : ℝ)| ≤ (b : ℝ)⁻¹ := by
    rw [abs_of_neg (sub_neg.mpr hxa), neg_sub, ← one_div]
    apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ hbpos).mpr
    calc
      (a : ℝ) ≤ (b : ℝ) * x + 1 := hhi
      _ = (1 / (b : ℝ) + x) * (b : ℝ) := by
        field_simp
        ring
  have hbad := hB b hbB a (ne_of_lt hxa)
  simp only [Real.rpow_neg_one] at hbad
  exact (not_lt_of_ge herr) hbad

theorem no_bound_zero : ¬ Bound 0 := by
  intro h
  exact no_upperBound_zero constant (by simpa only [Rat.cast_zero] using h.2)

#print axioms source_740_shape
#print axioms source_740_implies_bound
#print axioms bound_mono
#print axioms zero_has_upperBound_one
#print axioms no_bound_zero

end CatalanStatementValidation
