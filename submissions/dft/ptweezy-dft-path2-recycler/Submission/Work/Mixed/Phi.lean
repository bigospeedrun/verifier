import Submission.Work.Mixed.Flow
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# R1 (real part): Phi conservation (Lemma D) and the unit count (Lemma E)

rb-r12, 14 Oct 2026.  `Phi g s = ∑_{x ∈ s} g x` on multisets of job sizes.  The rate hypothesis at an exponent
`z` is `∑_j rk_j^z ≤ q * ∑_k Wk_k kr_k^z` (q = 1 is the plain rate fact; q < 1 holds strictly above the
critical exponent, `rate_mono`).

* `phi_out_le`   : one class: Phi of all its outputs ≤ q * Phi of its inputs.
* `phi_exT_le`   : **Lemma D**: Phi(exits) ≤ Phi(sources) for the whole tree.
* `units_le`     : **Lemma E**: number of fluid units ≤ α * Phi(sources) when `1 ≤ α (1 - q)`.
* `rate_mono`    : the rate fact at `z1` gives the factor `q = (rmax/kmin)^(z - z1)` at every `z ≥ z1`.
-/

namespace OAI.PowerSaving.MX

open Finset

/-- Phi of a multiset of sizes, as an additive monoid map -/
def Phi (g : ℕ → ℝ) : Multiset ℕ →+ ℝ where
  toFun s := (s.map g).sum
  map_zero' := by simp
  map_add' := by intro a b; simp

@[simp] lemma Phi_apply (g : ℕ → ℝ) (s : Multiset ℕ) : Phi g s = (s.map g).sum := rfl

lemma Phi_single (g : ℕ → ℝ) (x : ℕ) : Phi g {x} = g x := by simp

lemma Phi_nsmul_single (g : ℕ → ℝ) (c x : ℕ) : Phi g (c • ({x} : Multiset ℕ)) = (c : ℝ) * g x := by
  rw [map_nsmul, Phi_single, nsmul_eq_mul]

lemma Phi_mono {g g' : ℕ → ℝ} {s : Multiset ℕ} (h : ∀ x ∈ s, g x ≤ g' x) : Phi g s ≤ Phi g' s := by
  simp only [Phi_apply]; exact Multiset.sum_map_le_sum_map _ _ h

lemma Phi_nonneg {g : ℕ → ℝ} {s : Multiset ℕ} (h : ∀ x ∈ s, 0 ≤ g x) : 0 ≤ Phi g s := by
  simp only [Phi_apply]
  exact Multiset.sum_nonneg (fun y hy => by
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 hy; exact h x hx)

/-- the power weight `x ↦ x^z` -/
noncomputable def pw (z : ℝ) : ℕ → ℝ := fun x => (x : ℝ) ^ z

lemma pw_nonneg (z : ℝ) (x : ℕ) : 0 ≤ pw z x := Real.rpow_nonneg (Nat.cast_nonneg x) z

lemma pw_mul (z : ℝ) (a b : ℕ) : pw z (a * b) = pw z a * pw z b := by
  unfold pw; push_cast; exact Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)

lemma one_le_pw {z : ℝ} (hz : 0 ≤ z) {x : ℕ} (hx : 1 ≤ x) : 1 ≤ pw z x :=
  Real.one_le_rpow (by exact_mod_cast hx) hz

namespace Rule

variable (R : Rule)

/-- the rate hypothesis with factor `q` at exponent `z` -/
def RateQ (z q : ℝ) : Prop := ∑ j, (R.rk j : ℝ) ^ z ≤ q * ∑ k, (R.Wk k : ℝ) * (R.kr k : ℝ) ^ z

/-- One class: the outputs of all its rounds carry at most `q` times the Phi of its inputs. -/
theorem phi_out_le {z q : ℝ} (hq : 0 ≤ q) (hrate : R.RateQ z q) (n h ρ : ℕ) :
    Phi (pw z) (∑ j, R.outMS n h ρ j) ≤ q * Phi (pw z) (R.inMS n h ρ) := by
  simp only [outMS, inMS, map_sum, Phi_nsmul_single]
  have hL : ∑ j, ∑ b ∈ R.pts n h ρ, (R.uh h b : ℝ) * pw z (ρ * R.rk j * R.col b) =
      ∑ b ∈ R.pts n h ρ, ((R.uh h b : ℝ) * pw z (ρ * R.col b)) * ∑ j, (R.rk j : ℝ) ^ z := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [show ρ * R.rk j * R.col b = R.rk j * (ρ * R.col b) by ring, pw_mul]
    unfold pw; ring
  have hR : q * ∑ b ∈ R.pts n h ρ, ∑ k, ((R.uh h b * R.Wk k : ℕ) : ℝ) * pw z (ρ * R.kr k * R.col b) =
      ∑ b ∈ R.pts n h ρ, ((R.uh h b : ℝ) * pw z (ρ * R.col b)) *
        (q * ∑ k, (R.Wk k : ℝ) * (R.kr k : ℝ) ^ z) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [show ρ * R.kr k * R.col b = R.kr k * (ρ * R.col b) by ring, pw_mul]
    unfold pw; push_cast; ring
  rw [hL, hR]
  refine Finset.sum_le_sum (fun b _ => ?_)
  exact mul_le_mul_of_nonneg_left hrate (mul_nonneg (Nat.cast_nonneg _) (pw_nonneg _ _))

/-- Lemma D for a subtree: the Phi of its exits is at most the Phi of its root's inputs plus the Phi of the
sources of its descendants. -/
theorem phi_exitsSub_le {z : ℝ} (hrate : R.RateQ z 1) (n : ℕ) :
    ∀ h ρ, Phi (pw z) (R.exitsSub n h ρ) ≤ Phi (pw z) (R.inMS n h ρ) + Phi (pw z) (R.srcBelow n h ρ) := by
  intro h
  induction h with
  | zero =>
    intro ρ
    simp only [exitsSub, srcBelow, map_zero, add_zero]
    have := R.phi_out_le zero_le_one hrate n 0 ρ
    rwa [one_mul] at this
  | succ h ih =>
    intro ρ
    simp only [exitsSub, srcBelow, map_sum, map_add]
    have hout := R.phi_out_le zero_le_one hrate n (h + 1) ρ
    rw [one_mul, map_sum] at hout
    calc ∑ j, Phi (pw z) (R.exitsSub n h (ρ * R.rk j))
        ≤ ∑ j, (Phi (pw z) (R.inMS n h (ρ * R.rk j)) + Phi (pw z) (R.srcBelow n h (ρ * R.rk j))) :=
          Finset.sum_le_sum (fun j _ => ih _)
      _ = ∑ j, Phi (pw z) (R.outMS n (h + 1) ρ j) +
            ∑ j, (Phi (pw z) (R.srcMS n h (ρ * R.rk j) ρ) + Phi (pw z) (R.srcBelow n h (ρ * R.rk j))) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [R.balance n h ρ j, map_add]; ring
      _ ≤ Phi (pw z) (R.inMS n (h + 1) ρ) +
            ∑ j, (Phi (pw z) (R.srcMS n h (ρ * R.rk j) ρ) + Phi (pw z) (R.srcBelow n h (ρ * R.rk j))) := by
          linarith

/-- **Lemma D** (Phi conserved, at most): the exits of the tree carry at most the Phi of its sources. -/
theorem phi_exT_le {z : ℝ} (hrate : R.RateQ z 1) (n : ℕ) : Phi (pw z) (R.exT n) ≤ Phi (pw z) (R.srcT n) := by
  unfold exT srcT; rw [map_add]; exact R.phi_exitsSub_le hrate n _ _

lemma W_pos : 1 ≤ R.W := by
  obtain ⟨k, _, hk⟩ := R.kmin_att
  exact le_trans hk (Finset.single_le_sum (f := R.Wk) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k))

/-- the units of one class are at most the Phi of its inputs (every input has size at least 1) -/
lemma unitsC_le {z : ℝ} (hz : 0 ≤ z) (n h ρ : ℕ) (hρ : 1 ≤ ρ) :
    (R.unitsC n h ρ : ℝ) ≤ Phi (pw z) (R.inMS n h ρ) := by
  simp only [unitsC, inMS, map_sum, Phi_nsmul_single]
  push_cast
  refine Finset.sum_le_sum (fun b _ => ?_)
  have hW : (1 : ℝ) ≤ ∑ k, (R.Wk k : ℝ) := by exact_mod_cast R.W_pos
  calc (R.uh h b : ℝ) = (R.uh h b : ℝ) * 1 := by ring
    _ ≤ (R.uh h b : ℝ) * ∑ k, (R.Wk k : ℝ) := mul_le_mul_of_nonneg_left hW (Nat.cast_nonneg _)
    _ = ∑ k, (R.uh h b : ℝ) * (R.Wk k : ℝ) * 1 := by rw [Finset.mul_sum]; simp
    _ ≤ ∑ k, (R.uh h b : ℝ) * (R.Wk k : ℝ) * pw z (ρ * R.kr k * R.col b) := by
        refine Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (one_le_pw hz ?_) (by positivity))
        have := R.kr_pos k; have := R.col_pos b
        exact Nat.one_le_iff_ne_zero.2 (by positivity)

/-- Lemma E for a subtree. -/
theorem unitsSub_le {z q α : ℝ} (hz : 0 ≤ z) (hq : 0 ≤ q) (hrate : R.RateQ z q) (hα0 : 0 ≤ α)
    (hα : 1 ≤ α * (1 - q)) (n : ℕ) :
    ∀ h ρ, 1 ≤ ρ → (R.unitsSub n h ρ : ℝ) ≤ α * (Phi (pw z) (R.inMS n h ρ) + Phi (pw z) (R.srcBelow n h ρ)) := by
  have hα1 : 1 ≤ α := by nlinarith
  intro h
  induction h with
  | zero =>
    intro ρ hρ
    simp only [unitsSub, srcBelow, map_zero, add_zero]
    have h1 := R.unitsC_le hz n 0 ρ hρ
    have h2 : 0 ≤ Phi (pw z) (R.inMS n 0 ρ) := Phi_nonneg (fun x _ => pw_nonneg z x)
    nlinarith
  | succ h ih =>
    intro ρ hρ
    simp only [unitsSub, srcBelow, map_sum, map_add]
    push_cast
    have hout := R.phi_out_le hq hrate n (h + 1) ρ
    rw [map_sum] at hout
    have h1 := R.unitsC_le hz n (h + 1) ρ hρ
    have hin0 : 0 ≤ Phi (pw z) (R.inMS n (h + 1) ρ) := Phi_nonneg (fun x _ => pw_nonneg z x)
    have hsub : ∑ j, (R.unitsSub n h (ρ * R.rk j) : ℝ) ≤
        α * (∑ j, Phi (pw z) (R.outMS n (h + 1) ρ j) +
          ∑ j, (Phi (pw z) (R.srcMS n h (ρ * R.rk j) ρ) + Phi (pw z) (R.srcBelow n h (ρ * R.rk j)))) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_le_sum (fun j _ => ?_)
      have := ih (ρ * R.rk j) (le_trans hρ (Nat.le_mul_of_pos_right _ (R.rk_pos j)))
      rw [R.balance n h ρ j, map_add] at this
      linarith
    have : α * ∑ j, Phi (pw z) (R.outMS n (h + 1) ρ j) ≤ α * (q * Phi (pw z) (R.inMS n (h + 1) ρ)) :=
      mul_le_mul_of_nonneg_left hout hα0
    nlinarith

/-- **Lemma E**: the fluid units of the tree are at most `α` times the Phi of its sources. -/
theorem units_le {z q α : ℝ} (hz : 0 ≤ z) (hq : 0 ≤ q) (hrate : R.RateQ z q) (hα0 : 0 ≤ α)
    (hα : 1 ≤ α * (1 - q)) (n : ℕ) : (R.unitsT n : ℝ) ≤ α * Phi (pw z) (R.srcT n) := by
  unfold unitsT srcT; rw [map_add]; exact R.unitsSub_le hz hq hrate hα0 hα n _ _ le_rfl

/-- Above the exponent of a rate fact the rate is strict, by the factor `(rmax/kmin)^(z - z1)` (separation). -/
theorem rate_mono {z1 z : ℝ} (h1 : R.RateQ z1 1) (hz : z1 ≤ z) :
    R.RateQ z (((R.rmax : ℝ) / R.kmin) ^ (z - z1)) := by
  unfold RateQ at *
  rw [one_mul] at h1
  set δ := z - z1 with hδ
  have hδ0 : 0 ≤ δ := by linarith
  have hk0 : (0 : ℝ) < R.kmin := by exact_mod_cast R.kmin_pos
  have hzs : z = z1 + δ := by ring
  have hL : ∑ j, (R.rk j : ℝ) ^ z ≤ (R.rmax : ℝ) ^ δ * ∑ j, (R.rk j : ℝ) ^ z1 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun j _ => ?_)
    have hr : (0 : ℝ) < R.rk j := by exact_mod_cast R.rk_pos j
    rw [hzs, Real.rpow_add hr, mul_comm]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hr.le (by exact_mod_cast R.rk_le j) hδ0)
      (Real.rpow_nonneg hr.le _)
  have hR : (R.kmin : ℝ) ^ δ * ∑ k, (R.Wk k : ℝ) * (R.kr k : ℝ) ^ z1 ≤ ∑ k, (R.Wk k : ℝ) * (R.kr k : ℝ) ^ z := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun k _ => ?_)
    have hkr : (0 : ℝ) < R.kr k := by exact_mod_cast R.kr_pos k
    rw [hzs, Real.rpow_add hkr]
    have : (R.kmin : ℝ) ^ δ ≤ (R.kr k : ℝ) ^ δ := Real.rpow_le_rpow hk0.le (by exact_mod_cast R.kmin_le k) hδ0
    have h2 : 0 ≤ (R.Wk k : ℝ) * (R.kr k : ℝ) ^ z1 := by positivity
    nlinarith
  have hkd : 0 < (R.kmin : ℝ) ^ δ := Real.rpow_pos_of_pos hk0 _
  rw [Real.div_rpow (Nat.cast_nonneg _) hk0.le]
  have hS : 0 ≤ ∑ j, (R.rk j : ℝ) ^ z1 := Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hrm : 0 ≤ (R.rmax : ℝ) ^ δ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc ∑ j, (R.rk j : ℝ) ^ z ≤ (R.rmax : ℝ) ^ δ * ∑ j, (R.rk j : ℝ) ^ z1 := hL
    _ ≤ (R.rmax : ℝ) ^ δ * ∑ k, (R.Wk k : ℝ) * (R.kr k : ℝ) ^ z1 := mul_le_mul_of_nonneg_left h1 hrm
    _ = (R.rmax : ℝ) ^ δ / (R.kmin : ℝ) ^ δ * ((R.kmin : ℝ) ^ δ * ∑ k, (R.Wk k : ℝ) * (R.kr k : ℝ) ^ z1) := by
        field_simp
    _ ≤ (R.rmax : ℝ) ^ δ / (R.kmin : ℝ) ^ δ * ∑ k, (R.Wk k : ℝ) * (R.kr k : ℝ) ^ z :=
        mul_le_mul_of_nonneg_left hR (div_nonneg hrm hkd.le)

lemma rate_factor_lt_one {δ : ℝ} (hδ : 0 < δ) : ((R.rmax : ℝ) / R.kmin) ^ δ < 1 := by
  have hk0 : (0 : ℝ) < R.kmin := by exact_mod_cast R.kmin_pos
  refine Real.rpow_lt_one (div_nonneg (Nat.cast_nonneg _) hk0.le) ?_ hδ
  rw [div_lt_one hk0]; exact_mod_cast R.sep

end Rule

end OAI.PowerSaving.MX
