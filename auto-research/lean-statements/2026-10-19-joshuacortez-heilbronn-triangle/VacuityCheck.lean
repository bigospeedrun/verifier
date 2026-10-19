import Statement

/-!
Released under Apache 2.0.
Prepared with assistance from Claude (Anthropic).

Vacuity checks for `BigOSpeedrun.HeilbronnTriangle.Bound`.

* `bound_mono`: a larger saving implies every smaller one.
* `bound_zero`: the classical saving `η = 0` holds (Erdős's parabola modulo a
  prime, with Bertrand's postulate for every `n`).
* `not_bound_of_two_lt`: every saving `η > 2` fails, because no triangle in the
  unit square has area above `1`.

So the target is neither trivially true nor trivially false. These lemmas are
review evidence only; they are not part of the trusted statement.
-/

namespace BigOSpeedrun.HeilbronnTriangle

open OAI.Problem355

/-- A larger saving implies every smaller one. -/
theorem bound_mono {η η' : ℚ} (h : Bound η) (hle : η' ≤ η) : Bound η' := by
  obtain ⟨c, hc, N, hN⟩ := h
  refine ⟨c, hc, max N 1, fun n hn => ?_⟩
  obtain ⟨P, hcard, hsq, hareas⟩ := hN n (le_of_max_le_left hn)
  refine ⟨P, hcard, hsq, ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
  have hpow : Real.rpow (n : ℝ) (-2 + (η' : ℝ)) ≤ Real.rpow (n : ℝ) (-2 + (η : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by
      have : (η' : ℝ) ≤ η := by exact_mod_cast hle
      linarith)
  unfold triangleAreasAtLeast at hareas ⊢
  intro p hp q hq r hr hpq hpr hqr
  exact le_trans (mul_le_mul_of_nonneg_left hpow hc.le) (hareas p hp q hq r hr hpq hpr hqr)

/-- No triangle with vertices in the closed unit square has area above `1`. -/
theorem triangleArea_le_one {p q r : Point} (hp : pointInUnitSquare p)
    (hq : pointInUnitSquare q) (hr : pointInUnitSquare r) : triangleArea p q r ≤ 1 := by
  obtain ⟨hp1, hp1', hp2, hp2'⟩ := hp
  obtain ⟨hq1, hq1', hq2, hq2'⟩ := hq
  obtain ⟨hr1, hr1', hr2, hr2'⟩ := hr
  have ha : |q.1 - p.1| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hb : |r.2 - p.2| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hc : |q.2 - p.2| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hd : |r.1 - p.1| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have h1 : |(q.1 - p.1) * (r.2 - p.2)| ≤ 1 := by
    rw [abs_mul]; nlinarith [abs_nonneg (q.1 - p.1), abs_nonneg (r.2 - p.2)]
  have h2 : |(q.2 - p.2) * (r.1 - p.1)| ≤ 1 := by
    rw [abs_mul]; nlinarith [abs_nonneg (q.2 - p.2), abs_nonneg (r.1 - p.1)]
  unfold triangleArea
  have := abs_sub ((q.1 - p.1) * (r.2 - p.2)) ((q.2 - p.2) * (r.1 - p.1))
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- Every saving above `2` fails. -/
theorem not_bound_of_two_lt {η : ℚ} (hη : 2 < η) : ¬ Bound η := by
  rintro ⟨c, hc, N, hN⟩
  have hexp : 0 < -2 + (η : ℝ) := by
    have : (2 : ℝ) < η := by exact_mod_cast hη
    linarith
  -- `n ^ (-2 + η)` tends to infinity, so eventually `c * n ^ (-2 + η) > 1`.
  have htend : Filter.Tendsto (fun n : ℕ => Real.rpow (n : ℝ) (-2 + (η : ℝ)))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hexp).comp tendsto_natCast_atTop_atTop
  have hev := (htend.eventually_gt_atTop (1 / c)).and
    (Filter.eventually_ge_atTop (max N 3))
  obtain ⟨n, hbig, hn⟩ := hev.exists
  obtain ⟨P, hcard, hsq, hareas⟩ := hN n (le_of_max_le_left hn)
  have h3 : 2 < P.card := by rw [hcard]; exact lt_of_lt_of_le (by norm_num) (le_of_max_le_right hn)
  obtain ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr⟩ := Finset.two_lt_card.mp h3
  unfold triangleAreasAtLeast at hareas
  unfold pointsInUnitSquare at hsq
  have hlow := hareas p hp q hq r hr hpq hpr hqr
  have hup := triangleArea_le_one (hsq p hp) (hsq q hq) (hsq r hr)
  have : 1 < c * Real.rpow (n : ℝ) (-2 + (η : ℝ)) := by
    rw [div_lt_iff₀ hc] at hbig; linarith
  linarith

section Erdos

/-- Erdős's point `x ↦ (x/p, (x² mod p)/p)`. -/
noncomputable def erdosPoint (p x : ℕ) : Point :=
  ((x : ℝ) / p, ((x ^ 2 % p : ℕ) : ℝ) / p)

/-- The doubled signed area of three Erdős points, times `p²`, as an integer. -/
def erdosDet (p x y z : ℕ) : ℤ :=
  ((y : ℤ) - x) * (((z ^ 2 % p : ℕ) : ℤ) - ((x ^ 2 % p : ℕ) : ℤ)) -
    (((y ^ 2 % p : ℕ) : ℤ) - ((x ^ 2 % p : ℕ) : ℤ)) * ((z : ℤ) - x)

theorem erdosArea_eq {p : ℕ} (hp : 0 < p) (x y z : ℕ) :
    triangleArea (erdosPoint p x) (erdosPoint p y) (erdosPoint p z) =
      |(erdosDet p x y z : ℝ)| / (2 * (p : ℝ) ^ 2) := by
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  unfold triangleArea erdosPoint erdosDet
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast]
  have key : ((y : ℝ) / p - x / p) * (((z ^ 2 % p : ℕ) : ℝ) / p - ((x ^ 2 % p : ℕ) : ℝ) / p) -
      (((y ^ 2 % p : ℕ) : ℝ) / p - ((x ^ 2 % p : ℕ) : ℝ) / p) * ((z : ℝ) / p - x / p) =
      (((y : ℝ) - x) * (((z ^ 2 % p : ℕ) : ℝ) - ((x ^ 2 % p : ℕ) : ℝ)) -
        (((y ^ 2 % p : ℕ) : ℝ) - ((x ^ 2 % p : ℕ) : ℝ)) * ((z : ℝ) - x)) / (p : ℝ) ^ 2 := by
    field_simp
  rw [key, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (p : ℝ) ^ 2)]
  ring

theorem erdosDet_ne_zero {p : ℕ} (hp : p.Prime) {x y z : ℕ} (hx : x < p) (hy : y < p)
    (hz : z < p) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : erdosDet p x y z ≠ 0 := by
  have := Fact.mk hp
  intro h0
  have hcast : ((erdosDet p x y z : ℤ) : ZMod p) =
      ((y : ZMod p) - x) * ((z : ZMod p) - x) * ((z : ZMod p) - y) := by
    unfold erdosDet
    push_cast
    try simp only [ZMod.natCast_mod]
    ring
  have hne : ∀ {a b : ℕ}, a < p → b < p → a ≠ b → ((a : ZMod p) - b) ≠ 0 := by
    intro a b ha hb hab h
    apply hab
    have : (a : ZMod p) = b := sub_eq_zero.mp h
    rw [ZMod.natCast_eq_natCast_iff'] at this
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  have : ((erdosDet p x y z : ℤ) : ZMod p) ≠ 0 := by
    rw [hcast]
    exact mul_ne_zero (mul_ne_zero (hne hy hx (Ne.symm hxy)) (hne hz hx (Ne.symm hxz)))
      (hne hz hy (Ne.symm hyz))
  rw [h0] at this
  simp at this

/-- The classical saving `η = 0`: `Δ(n) ≥ n⁻² / 8` for every `n ≥ 1`. -/
theorem bound_zero : Bound 0 := by
  refine ⟨1 / 8, by norm_num, 1, fun n hn => ?_⟩
  obtain ⟨p, hp, hnp, hp2n⟩ := Nat.exists_prime_lt_and_le_two_mul n (by omega)
  have hp0 : 0 < p := hp.pos
  have hinj : Set.InjOn (erdosPoint p) (Finset.range n : Set ℕ) := by
    intro a _ b _ hab
    have h1 := congrArg Prod.fst hab
    simp only [erdosPoint] at h1
    have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp0.ne'
    rw [div_left_inj' hp'] at h1
    exact_mod_cast h1
  refine ⟨(Finset.range n).image (erdosPoint p), ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  · unfold pointsInUnitSquare
    intro q hq
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
    have hx' : x < p := lt_trans (Finset.mem_range.mp hx) hnp
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
    have hmod : x ^ 2 % p < p := Nat.mod_lt _ hp0
    simp only [erdosPoint]
    refine ⟨by positivity, ?_, by positivity, ?_⟩
    · rw [div_le_one hpR]; exact_mod_cast hx'.le
    · rw [div_le_one hpR]; exact_mod_cast hmod.le
  · unfold triangleAreasAtLeast
    intro a ha b hb c hc hab hac hbc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hc
    have hx' : x < p := lt_trans (Finset.mem_range.mp hx) hnp
    have hy' : y < p := lt_trans (Finset.mem_range.mp hy) hnp
    have hz' : z < p := lt_trans (Finset.mem_range.mp hz) hnp
    have hxy : x ≠ y := fun h => hab (h ▸ rfl)
    have hxz : x ≠ z := fun h => hac (h ▸ rfl)
    have hyz : y ≠ z := fun h => hbc (h ▸ rfl)
    rw [erdosArea_eq hp0]
    have hdet := erdosDet_ne_zero hp hx' hy' hz' hxy hxz hyz
    have hone : (1 : ℝ) ≤ |(erdosDet p x y z : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hdet
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < n := by linarith
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
    have hp2 : (p : ℝ) ≤ 2 * n := by exact_mod_cast hp2n
    have hrpow : Real.rpow (n : ℝ) (-2 + ((0 : ℚ) : ℝ)) = 1 / (n : ℝ) ^ 2 := by
      show (n : ℝ) ^ (-2 + ((0 : ℚ) : ℝ)) = 1 / (n : ℝ) ^ 2
      rw [Rat.cast_zero, add_zero, show (-2 : ℝ) = ((-2 : ℤ) : ℝ) by norm_num,
        Real.rpow_intCast]
      simp [zpow_neg, one_div]
    rw [hrpow]
    have hsq : (p : ℝ) ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by nlinarith
    rw [show (1 / 8 : ℝ) * (1 / (n : ℝ) ^ 2) = 1 / (8 * (n : ℝ) ^ 2) by field_simp]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith

end Erdos

/-- The target is not vacuous: the baseline holds and an impossible saving fails. -/
theorem nonvacuous : Bound 0 ∧ ¬ Bound 3 :=
  ⟨bound_zero, not_bound_of_two_lt (by norm_num)⟩

end BigOSpeedrun.HeilbronnTriangle
