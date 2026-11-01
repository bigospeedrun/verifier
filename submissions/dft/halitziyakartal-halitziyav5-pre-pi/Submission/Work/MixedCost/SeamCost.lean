import Submission.Work.MixedCost.Bill
import Submission.Work.MixedCost.Poly
import Submission.Work.Scratch.Engine

/-!
# Mixed engine, cost part 5: the bill of the seam adapter

(agent e-r3cost, round wht45/lever, 19 Oct 2026.)

The seam (`hillsZ_program`, Work/Fourier/Seam.lean) asks for the kernel on ONE vector of `k` bits
with work `O(2^k * envelope z k)`.  The mixed engine's top job `Do(n, B)` is efficient only with
at least `Nsrc n` vectors, so the adapter splits the bits (`a = k/2`, `b = k - k/2`):

  `top a (2^b)` (the kernel on the low `a` bits of each of the `2^b` slices), a relabel, then
  `top b (2^a)` (the kernel on the high `b` bits), a relabel back:
  `H_k = (H_b ⊗ I)(I ⊗ H_a)` (commuting Hadamards on disjoint bits, `Work.Mixed.Prog.Sem`).

`adapterCost k` is the cost of these two calls plus `2^k` for the relabels, and `seam_dom` is the
`Dom` bound that `Can.weaken` / `Able.weaken` needs: if the per-vector cost obeys
`J n ≤ C * 2^n * (n+1)^z` (R2's `allotM_bound`), then `adapterCost k = O(2^k * envelope z k)`.
-/

set_option linter.unusedSectionVars false

namespace OAI.PowerSaving.MX

open PowerSaving.RAM

namespace Rule

variable (R : Rule)

/-- The cost of the seam adapter on one vector of `k` bits: two top calls and the relabels. -/
def adapterCost (n0 : ℕ) (J : ℕ → ℕ) (k : ℕ) : ℕ :=
  R.topCost n0 J (k / 2) (2 ^ (k - k / 2)) + R.topCost n0 J (k - k / 2) (2 ^ (k / 2)) + 2 ^ k

/-- The `J`-part of a top call on `2^(k-n)` vectors of `2^n` entries. -/
lemma J_part_le {J : ℕ → ℕ} {z C : ℝ} (hz : 0 ≤ z)
    (hJ : ∀ n, (J n : ℝ) ≤ C * 2 ^ n * ((n : ℝ) + 1) ^ z) {k n : ℕ} (hn : n ≤ k) :
    2 ^ (k - n) * J n ≤ Nat.ceil C * (2 ^ k * envelope z k) := by
  have hk : (2:ℝ) ^ (k - n) * 2 ^ n = 2 ^ k := by rw [← pow_add, Nat.sub_add_cancel hn]
  have h1 : ((n : ℝ) + 1) ^ z ≤ ((k : ℝ) + 1) ^ z :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1) hz
  have h2 : ((k : ℝ) + 1) ^ z ≤ (envelope z k : ℝ) := Nat.le_ceil _
  have hJn := hJ n
  have hC0 : 0 ≤ C := by
    by_contra hneg
    push_neg at hneg
    have : C * 2 ^ n * ((n : ℝ) + 1) ^ z < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hneg (by positivity)) (by positivity)
    have : (0 : ℝ) ≤ J n := Nat.cast_nonneg _
    linarith
  have key : ((2 ^ (k - n) * J n : ℕ) : ℝ) ≤ ((Nat.ceil C * (2 ^ k * envelope z k) : ℕ) : ℝ) := by
    push_cast
    calc (2:ℝ) ^ (k - n) * J n ≤ 2 ^ (k - n) * (C * 2 ^ n * ((n : ℝ) + 1) ^ z) :=
          mul_le_mul_of_nonneg_left hJn (by positivity)
      _ = C * (2 ^ (k - n) * 2 ^ n) * ((n : ℝ) + 1) ^ z := by ring
      _ = C * 2 ^ k * ((n : ℝ) + 1) ^ z := by rw [hk]
      _ ≤ C * 2 ^ k * (envelope z k : ℝ) :=
          mul_le_mul_of_nonneg_left (le_trans h1 h2) (by positivity)
      _ ≤ (Nat.ceil C : ℝ) * (2 ^ k * (envelope z k : ℝ)) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_right (Nat.le_ceil C) (by positivity)
  exact_mod_cast key

/-- Everything but the `J`-parts is `O(2^k)`. -/
lemma adapter_rest_le {n0 : ℕ} (hn0 : R.m ≤ n0) :
    ∃ E : ℕ, ∀ k, R.LftS n0 (k / 2) (2 ^ (k - k / 2)) + ((k / 2 + 1) * 2 ^ (k / 2) + 1)
      + (R.LftS n0 (k - k / 2) (2 ^ (k / 2)) + ((k - k / 2 + 1) * 2 ^ (k - k / 2) + 1)) + 2 ^ k
      ≤ E * 2 ^ k := by
  obtain ⟨A, c, hA⟩ := R.Nsrc_poly_ex
  obtain ⟨D, hD⟩ := succ_pow_le_two_pow (c + 1)
  obtain ⟨D1, hD1⟩ := succ_pow_le_two_pow 1
  refine ⟨3 * A * D + 3 * D1 + 4, fun k => ?_⟩
  set a := k / 2
  set b := k - k / 2
  have hab : a + b = k := by omega
  have hab1 : a ≤ b := by omega
  have hba : b ≤ a + 1 := by omega
  have hk : 2 ^ k = 2 ^ a * 2 ^ b := by rw [← pow_add, hab]
  have haa : 2 ^ a * 2 ^ a ≤ 2 ^ k := by rw [hk]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hab1)
  have hbb : 2 ^ b * 2 ^ b ≤ 2 * 2 ^ k := by
    rw [hk]
    have : 2 ^ b ≤ 2 * 2 ^ a := by
      calc 2 ^ b ≤ 2 ^ (a + 1) := Nat.pow_le_pow_right (by norm_num) hba
        _ = 2 * 2 ^ a := by ring
    calc 2 ^ b * 2 ^ b ≤ (2 * 2 ^ a) * 2 ^ b := Nat.mul_le_mul_right _ this
      _ = 2 * (2 ^ a * 2 ^ b) := by ring
  -- the leftovers: `Nsrc x * (x+1) * 2^x ≤ A * D * 2^x * 2^x`
  have hL : ∀ x B, R.LftS n0 x B ≤ A * D * (2 ^ x * 2 ^ x) := by
    intro x B
    have h1 := R.LftS_le hn0 x B
    have h2 : R.Nsrc x * (x + 1) ≤ A * (x + 1) ^ (c + 1) := by
      calc R.Nsrc x * (x + 1) ≤ A * (x + 1) ^ c * (x + 1) := Nat.mul_le_mul_right _ (hA x)
        _ = A * (x + 1) ^ (c + 1) := by ring
    have h3 : A * (x + 1) ^ (c + 1) ≤ A * (D * 2 ^ x) := Nat.mul_le_mul_left _ (hD x)
    calc R.LftS n0 x B ≤ R.Nsrc x * (x + 1) * 2 ^ x := h1
      _ ≤ A * (D * 2 ^ x) * 2 ^ x := Nat.mul_le_mul_right _ (le_trans h2 h3)
      _ = A * D * (2 ^ x * 2 ^ x) := by ring
  have hN : ∀ x, (x + 1) * 2 ^ x + 1 ≤ (D1 + 1) * (2 ^ x * 2 ^ x) := by
    intro x
    have h1 : x + 1 ≤ D1 * 2 ^ x := by simpa using hD1 x
    have h2 : 1 ≤ 2 ^ x * 2 ^ x := Nat.one_le_iff_ne_zero.2 (by positivity)
    calc (x + 1) * 2 ^ x + 1 ≤ D1 * 2 ^ x * 2 ^ x + 2 ^ x * 2 ^ x := Nat.add_le_add (Nat.mul_le_mul_right _ h1) h2
      _ = (D1 + 1) * (2 ^ x * 2 ^ x) := by ring
  have e1 := hL a (2 ^ b)
  have e2 := hL b (2 ^ a)
  have e3 := hN a
  have e4 := hN b
  have f1 : A * D * (2 ^ a * 2 ^ a) ≤ A * D * 2 ^ k := Nat.mul_le_mul_left _ haa
  have f2 : A * D * (2 ^ b * 2 ^ b) ≤ A * D * (2 * 2 ^ k) := Nat.mul_le_mul_left _ hbb
  have f3 : (D1 + 1) * (2 ^ a * 2 ^ a) ≤ (D1 + 1) * 2 ^ k := Nat.mul_le_mul_left _ haa
  have f4 : (D1 + 1) * (2 ^ b * 2 ^ b) ≤ (D1 + 1) * (2 * 2 ^ k) := Nat.mul_le_mul_left _ hbb
  have : A * D * 2 ^ k + A * D * (2 * 2 ^ k) + (D1 + 1) * 2 ^ k + (D1 + 1) * (2 * 2 ^ k) + 2 ^ k
      = (3 * A * D + 3 * D1 + 4) * 2 ^ k := by ring
  linarith

/-- **The seam adapter's bill**: with R2's bound `J n ≤ C 2^n (n+1)^z`, the adapter's cost is
`O(2^k * envelope z k)`, in the form `Can.weaken` takes. -/
theorem seam_dom {n0 : ℕ} (hn0 : R.m ≤ n0) {J : ℕ → ℕ} {z C : ℝ} (hz : 0 ≤ z)
    (hJ : ∀ n, (J n : ℝ) ≤ C * 2 ^ n * ((n : ℝ) + 1) ^ z) {ι : Type*} (k : ι → ℕ) :
    Dom (fun i => 2 ^ k i * envelope z (k i)) (fun i => R.adapterCost n0 J (k i)) := by
  obtain ⟨E, hE⟩ := R.adapter_rest_le hn0
  refine ⟨2 * Nat.ceil C + E + 1, fun i => ?_⟩
  dsimp only
  set x := k i
  set W := 2 ^ x * envelope z x
  have hW : 2 ^ x ≤ W := Nat.le_mul_of_pos_right _ (envelope_pos z x)
  have j1 : 2 ^ (x - x / 2) * J (x / 2) ≤ Nat.ceil C * W := J_part_le hz hJ (Nat.div_le_self x 2)
  have j2 : 2 ^ (x - (x - x / 2)) * J (x - x / 2) ≤ Nat.ceil C * W := J_part_le hz hJ (Nat.sub_le x _)
  have hxx : x - (x - x / 2) = x / 2 := by omega
  rw [hxx] at j2
  have hr := hE x
  have hEW : E * 2 ^ x ≤ E * W := Nat.mul_le_mul_left _ hW
  unfold adapterCost topCost
  have hW1 : (2 * Nat.ceil C + E + 1) * (W + 1) = 2 * Nat.ceil C * W + E * W + W
      + (2 * Nat.ceil C + E + 1) := by ring
  linarith

end Rule

end OAI.PowerSaving.MX

#print axioms OAI.PowerSaving.MX.Rule.seam_dom
