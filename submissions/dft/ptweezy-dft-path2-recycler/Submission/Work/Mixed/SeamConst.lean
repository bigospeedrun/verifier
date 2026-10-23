import Submission.Work.Scratch.Engine

/-!
# R4: the seam with a constant (e-r45m1, round wht45/lever, 19 Oct 2026)

OpenAI's seam `hills_program` (and our copies `hillsZ_program`, `hillsU8X0HQ_program`) is a `Can` statement with
work `2^k * ⌈(k+1)^z⌉`.  `Can` already carries an implicit constant (`Able`: work `C*(W i+1) + Z i` for SOME `C`,
OAI/Computability/FourierTransform/ProgramBounds.lean), so an engine whose cost obeys a real bound
`c ≤ A 2^k (k+1)^z` with ANY constant `A` (the mixed engine: R2's `allotM_bound`) gives the seam unchanged.
This file proves exactly that, plus the monotonicity in the exponent.  The Fourier chain (`hillsZ_pos`,
`hillsZ_mono`, `hillsZ_real`, the goal) is untouched: only the proof of the seam theorem changes, and only through
`can_envelope_of_real`.

* `dom_envelope_of_real`       a real bound with a constant ⇒ the `Dom` bound against `2^k * envelope z k`;
* `can_envelope_of_real`       the same for a `Can` statement (`Can.weaken`);
* `envelope_nat_real_le`       `2^k * envelope z k ≤ 2 * 2^k * (k+1)^z'` for `0 ≤ z ≤ z'` (as reals);
* `can_envelope_mono`          `Can` at envelope `z` ⇒ `Can` at envelope `z'` for `z ≤ z'`.

No `sorry`, no axioms.
-/

namespace OAI.PowerSaving.MX
open PowerSaving.RAM Ty

universe U

/-- **The seam with a constant.**  If `c i ≤ A * 2^(k i) * (k i + 1)^z` (reals, any constant `A`), then `c` is
dominated, in the sense of `Can.weaken`, by the seam's natural work `2^(k i) * ⌈(k i + 1)^z⌉`. -/
theorem dom_envelope_of_real {ι : Type*} (k : ι → ℕ) (c : ι → ℕ) {A z : ℝ}
    (hc : ∀ i, (c i : ℝ) ≤ A * 2 ^ k i * ((k i : ℝ) + 1) ^ z) :
    Dom (fun i => 2 ^ k i * envelope z (k i)) c := by
  refine ⟨Nat.ceil A + 1, fun i => ?_⟩
  dsimp only
  set n := k i
  set W := 2 ^ n * envelope z n
  have h1 : ((n : ℝ) + 1) ^ z ≤ (envelope z n : ℝ) := Nat.le_ceil _
  have key : (c i : ℝ) ≤ (Nat.ceil A : ℝ) * (W : ℝ) := by
    have hW : (W : ℝ) = (2:ℝ) ^ n * (envelope z n : ℝ) := by simp [W]
    rw [hW]
    rcases le_or_gt 0 A with hA | hA
    · calc (c i : ℝ) ≤ A * 2 ^ n * ((n : ℝ) + 1) ^ z := hc i
        _ ≤ (Nat.ceil A : ℝ) * 2 ^ n * (envelope z n : ℝ) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (Nat.le_ceil A) (by positivity)) h1
            (by positivity) (by positivity)
        _ = (Nat.ceil A : ℝ) * (2 ^ n * (envelope z n : ℝ)) := by ring
    · have hp : 0 < (2:ℝ) ^ n * ((n : ℝ) + 1) ^ z := by positivity
      have hneg : A * 2 ^ n * ((n : ℝ) + 1) ^ z < 0 := by
        rw [mul_assoc]; exact mul_neg_of_neg_of_pos hA hp
      have h0 : (0 : ℝ) ≤ c i := Nat.cast_nonneg _
      have := hc i
      linarith
  have key' : c i ≤ Nat.ceil A * W := by exact_mod_cast key
  have e : (Nat.ceil A + 1) * (W + 1) = Nat.ceil A * W + Nat.ceil A + W + 1 := by ring
  rw [e]
  first | omega | linarith

/-- **The seam with a constant**, for a `Can` statement: any real bound `A 2^k (k+1)^z` on the work gives the work
`2^k * envelope z k` of the seam's shape. -/
theorem can_envelope_of_real {ι : Type U} {m : Bool} {B : ι → ℕ} {s t : Ty} {x : ι → T s} {y : ι → T t}
    (k : ι → ℕ) (c : ι → ℕ) {A z : ℝ} (hc : ∀ i, (c i : ℝ) ≤ A * 2 ^ k i * ((k i : ℝ) + 1) ^ z)
    (h : Can m B s t x y c) : Can m B s t x y (fun i => 2 ^ k i * envelope z (k i)) :=
  h.weaken (dom_envelope_of_real k c hc)

/-- The natural envelope work as a real bound with constant 2, at any larger exponent. -/
lemma envelope_nat_real_le {z z' : ℝ} (hz : 0 ≤ z) (hzz : z ≤ z') (n : ℕ) :
    ((2 ^ n * envelope z n : ℕ) : ℝ) ≤ 2 * 2 ^ n * ((n : ℝ) + 1) ^ z' := by
  have h1 : (envelope z n : ℝ) ≤ 2 * ((n : ℝ) + 1) ^ z := by
    have h := Real.one_le_rpow (show 1 ≤ (n : ℝ) + 1 by simp) hz
    have hh : (envelope z n : ℝ) < ((n : ℝ) + 1) ^ z + 1 := Nat.ceil_lt_add_one (by positivity)
    linarith
  have h2 : ((n : ℝ) + 1) ^ z ≤ ((n : ℝ) + 1) ^ z' :=
    Real.rpow_le_rpow_of_exponent_le (by simp) hzz
  push_cast
  calc (2:ℝ) ^ n * (envelope z n : ℝ) ≤ 2 ^ n * (2 * ((n : ℝ) + 1) ^ z) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ 2 ^ n * (2 * ((n : ℝ) + 1) ^ z') := by gcongr
    _ = 2 * 2 ^ n * ((n : ℝ) + 1) ^ z' := by ring

/-- `Can` at envelope `z` gives `Can` at every envelope `z' ≥ z`. -/
theorem can_envelope_mono {ι : Type U} {m : Bool} {B : ι → ℕ} {s t : Ty} {x : ι → T s} {y : ι → T t}
    (k : ι → ℕ) {z z' : ℝ} (hzz : z ≤ z')
    (h : Can m B s t x y (fun i => 2 ^ k i * envelope z (k i))) :
    Can m B s t x y (fun i => 2 ^ k i * envelope z' (k i)) :=
  h.mono fun i => Nat.mul_le_mul_left _ (Nat.ceil_le_ceil
    (Real.rpow_le_rpow_of_exponent_le (by simp) hzz))

end OAI.PowerSaving.MX

#print axioms OAI.PowerSaving.MX.dom_envelope_of_real
#print axioms OAI.PowerSaving.MX.can_envelope_of_real
#print axioms OAI.PowerSaving.MX.envelope_nat_real_le
#print axioms OAI.PowerSaving.MX.can_envelope_mono
