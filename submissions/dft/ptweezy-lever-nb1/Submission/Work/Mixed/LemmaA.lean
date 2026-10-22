import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Multiset

/-!
# R2 (abstract part): Lemma A, the top-split induction with leftovers (rl-prove section 2)

rb-r12, 14 Oct 2026.  No log factor is used (lg-g2 DESIGN 3.3): the induction runs at an exponent `z`,
and the leftovers (exits) are asked to carry at most `η/2` of the sources' Phi at `z`, which the tree gives
for all large `n` once the rate fact holds at some `z1 < z` (`Work.Mixed.Bound`).

* `eta_step` : for a source `s ∈ (n/m, n]` and `0 < z ≤ 1`, `(n - s + 1)^z ≤ (n+1)^z - (z/m) s^z`.
* `lemmaA`   : any per-entry cost `t` obeying the flow recurrence for `n ≥ n0` satisfies `t n ≤ C (n+1)^z`.
-/

namespace OAI.PowerSaving.MX

/-- The top-split step: removing a source of size `s ∈ (n/m, n]` from `n + 1` lowers `(·)^z` by at least
`(z/m) s^z` (`0 < z ≤ 1`). -/
theorem eta_step {m n s : ℕ} {z : ℝ} (hm : 1 ≤ m) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hlt : n < m * s) (hle : s ≤ n) :
    (((n - s : ℕ) : ℝ) + 1) ^ z ≤ ((n : ℝ) + 1) ^ z - z / m * (s : ℝ) ^ z := by
  set N1 : ℝ := (n : ℝ) + 1 with hN1def
  have hN1 : 0 < N1 := by positivity
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set x : ℝ := (s : ℝ) / N1 with hxdef
  have hsR : (s : ℝ) ≤ n := by exact_mod_cast hle
  have hx0 : 0 ≤ x := div_nonneg (Nat.cast_nonneg _) hN1.le
  have hx1 : x ≤ 1 := by rw [div_le_one hN1]; linarith
  have hmx : 1 ≤ (m : ℝ) * x := by
    have h1 : ((n : ℝ) + 1) ≤ (m : ℝ) * s := by exact_mod_cast hlt
    rw [hxdef, ← mul_div_assoc, le_div_iff₀ hN1]; linarith
  have hcast : (((n - s : ℕ) : ℝ) + 1) = N1 * (1 - x) := by
    rw [Nat.cast_sub hle, hxdef, hN1def]; field_simp; ring
  have hs : (s : ℝ) = x * N1 := by rw [hxdef]; field_simp
  rw [hcast, Real.mul_rpow hN1.le (by linarith)]
  have hb : (1 - x) ^ z ≤ 1 - z * x := by
    have := rpow_one_add_le_one_add_mul_self (s := -x) (by linarith) hz0 hz1
    simpa [sub_eq_add_neg, mul_neg] using this
  have hxz : x ^ z ≤ 1 := Real.rpow_le_one hx0 hx1 hz0
  have hsz : (s : ℝ) ^ z = x ^ z * N1 ^ z := by rw [hs, Real.mul_rpow hx0 hN1.le]
  have hNz : 0 ≤ N1 ^ z := Real.rpow_nonneg hN1.le _
  rw [hsz]
  have key : z / m * (x ^ z * N1 ^ z) ≤ z * x * N1 ^ z := by
    have h1 : z / m * x ^ z ≤ z * x := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hmR]
      nlinarith [mul_nonneg hz0 hx0]
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hb hNz]

/-- **Lemma A** (rl-prove section 2, the case `psi = 1` with leftovers measured against the sources'
Phi). `t n` is a per-entry cost; for `n ≥ n0` a flow with sources `src n` (each in `(n/m, n]`, giving the
step `eta`) and exits `ex n` (each `< n`) bounds `card (src n) * t n` by the internal cost `I n`, the exits'
costs and the rests' costs. If the exits carry at most `η/2` of the sources' Phi and the internal cost is at
most `A` times it, then `t n ≤ C (n+1)^z` for all `n`. -/
theorem lemmaA (t : ℕ → ℝ) (src ex : ℕ → Multiset ℕ) (I : ℕ → ℝ) (n0 : ℕ) {z A η : ℝ}
    (hz : 0 ≤ z) (hA : 0 ≤ A) (hη : 0 < η)
    (hN : ∀ n, n0 ≤ n → src n ≠ 0)
    (hrec : ∀ n, n0 ≤ n → (Multiset.card (src n) : ℝ) * t n ≤
        I n + ((ex n).map t).sum + ((src n).map (fun s => t (n - s))).sum)
    (hsrc : ∀ n, n0 ≤ n → ∀ s ∈ src n, 1 ≤ s ∧ s ≤ n ∧
        (((n - s : ℕ) : ℝ) + 1) ^ z ≤ ((n : ℝ) + 1) ^ z - η * (s : ℝ) ^ z)
    (hex : ∀ n, n0 ≤ n → ∀ e ∈ ex n, e < n)
    (hexPhi : ∀ n, n0 ≤ n →
        ((ex n).map (fun e : ℕ => ((e : ℝ) + 1) ^ z)).sum ≤ η / 2 * ((src n).map (fun s : ℕ => (s : ℝ) ^ z)).sum)
    (hI : ∀ n, n0 ≤ n → I n ≤ A * ((src n).map (fun s : ℕ => (s : ℝ) ^ z)).sum) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, t n ≤ C * ((n : ℝ) + 1) ^ z := by
  set S : ℝ := ∑ k ∈ Finset.range n0, |t k| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun k _ => abs_nonneg _)
  refine ⟨max (2 * A / η) S, le_trans hS0 (le_max_right _ _), ?_⟩
  set C := max (2 * A / η) S with hC
  have hC0 : 0 ≤ C := le_trans hS0 (le_max_right _ _)
  have hCη : 2 * A ≤ C * η := by
    have := le_max_left (2 * A / η) S
    rw [div_le_iff₀ hη] at this; linarith
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  have hpow1 : 1 ≤ ((n : ℝ) + 1) ^ z := Real.one_le_rpow (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]) hz
  by_cases hn : n < n0
  · have h1 : t n ≤ |t n| := le_abs_self _
    have h2 : |t n| ≤ S := Finset.single_le_sum (f := fun k => |t k|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.2 hn)
    have h3 : S ≤ C := le_max_right _ _
    nlinarith
  · push Not at hn
    set Φ : ℝ := ((src n).map (fun s : ℕ => (s : ℝ) ^ z)).sum with hΦ
    have hΦ0 : 0 ≤ Φ := Multiset.sum_nonneg (fun y hy => by
      obtain ⟨x, _, rfl⟩ := Multiset.mem_map.1 hy; exact Real.rpow_nonneg (Nat.cast_nonneg _) _)
    set N : ℝ := (Multiset.card (src n) : ℝ) with hNdef
    have hNpos : 0 < N := by
      rw [hNdef]; exact_mod_cast Multiset.card_pos.2 (hN n hn)
    -- exits
    have hE : ((ex n).map t).sum ≤ C * (η / 2 * Φ) := by
      calc ((ex n).map t).sum ≤ ((ex n).map (fun e : ℕ => C * (((e : ℝ) + 1) ^ z))).sum :=
            Multiset.sum_map_le_sum_map _ _ (fun e he => ih e (hex n hn e he))
        _ = C * ((ex n).map (fun e : ℕ => ((e : ℝ) + 1) ^ z)).sum := Multiset.sum_map_mul_left
        _ ≤ C * (η / 2 * Φ) := mul_le_mul_of_nonneg_left (hexPhi n hn) hC0
    -- rests
    have hRst : ((src n).map (fun s => t (n - s))).sum ≤ C * (N * ((n : ℝ) + 1) ^ z - η * Φ) := by
      calc ((src n).map (fun s => t (n - s))).sum
          ≤ ((src n).map (fun s : ℕ => C * (((n : ℝ) + 1) ^ z - η * (s : ℝ) ^ z))).sum := by
            refine Multiset.sum_map_le_sum_map _ _ (fun s hs => ?_)
            obtain ⟨h1, h2, h3⟩ := hsrc n hn s hs
            have := ih (n - s) (by omega)
            calc t (n - s) ≤ C * (((n - s : ℕ) : ℝ) + 1) ^ z := this
              _ ≤ C * (((n : ℝ) + 1) ^ z - η * (s : ℝ) ^ z) := mul_le_mul_of_nonneg_left h3 hC0
        _ = C * (N * ((n : ℝ) + 1) ^ z - η * Φ) := by
            rw [Multiset.sum_map_mul_left, Multiset.sum_map_sub, Multiset.sum_map_mul_left,
              Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul]
    have hrec' := hrec n hn
    have hI' := hI n hn
    have key : N * t n ≤ N * (C * ((n : ℝ) + 1) ^ z) := by nlinarith
    exact le_of_mul_le_mul_left key hNpos

end OAI.PowerSaving.MX
