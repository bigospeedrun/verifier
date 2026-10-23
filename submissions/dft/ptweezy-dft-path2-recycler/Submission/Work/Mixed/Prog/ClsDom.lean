import Submission.Work.Mixed.Prog.CostC
import Submission.Work.MixedCost.Poly

/-!
# Mixed engine, R3 program part 21: a valid class has a unit, and its work is `O(2^n (NU + cons))`

* `Eng.NU_pos`      the code `a0 a0 ... a0` (all letters the smallest target type) is in the region;
* `Eng.clsLoc_dom`  `clsLoc + 1 ≤ C * (2^n * (NU + cons) + 1)` on valid classes (the polynomial bookkeeping
                    is absorbed: `W^(h+1) ≤ W * n^W` because `kmin^h ≤ n`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset GF MXR
noncomputable section

namespace Eng
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]
variable (E : Eng α ρ σ)

/-- The code of the sequence `a0 a0 ... a0` of length `h`. -/
def repCode (a0 : ℕ) : ℕ → ℕ
  | 0 => 0
  | h + 1 => a0 + E.W * repCode a0 h

lemma repCode_spec (a0 : ℕ) (ha : a0 < E.W) :
    ∀ h, E.repCode a0 h < E.W^h ∧ colS E.W E.tq h (E.repCode a0 h) = E.tq a0 ^ h := by
  intro h
  induction h with
  | zero => simp [repCode]
  | succ h ih =>
    refine ⟨lt_of_cons E.W h a0 _ ha ih.1, ?_⟩
    simp only [repCode]
    rw [colS_cons E.W E.tq h a0 _ ha, ih.2, pow_succ, Nat.mul_comm]

/-- **A valid class has at least one unit.** -/
lemma NU_pos {kmin : ℕ} (hk : E.KMin kmin) {n h μ o BS : ℕ} {J sup : ℕ → Bits n → ℂ}
    (hd : E.Valid kmin (MDesc.cls n h μ o BS J sup)) : 1 ≤ E.NUc n h μ := by
  obtain ⟨hμ, hreg, _⟩ := hd
  obtain ⟨l, hl⟩ := hk.att
  let a0 := E.Q.loc l
  have ha : a0 < E.W := E.Q.bd l
  have htq : E.tq a0 = kmin := by
    unfold tq; rw [dif_pos ha]
    have : E.Q.atFin ⟨a0, ha⟩ = l := by
      apply E.Q.inj; rw [Layout.loc_atFin]
    rw [this, hl]
  obtain ⟨hlt, hcol⟩ := E.repCode_spec a0 ha h
  have hin : inRS E.W E.tq E.mx n h μ (E.repCode a0 h) := by
    refine ⟨hlt, ?_⟩
    rw [hcol, htq, ← Nat.mul_assoc]; exact hreg
  have := count_lt_of_mem hin hlt
  exact Nat.one_le_iff_ne_zero.2 (by unfold NUc MXR.NU MXR.PC at *; omega)

/-- The bookkeeping is polynomial in `n`. -/
lemma poly_valid {kmin : ℕ} (hk : E.KMin kmin) {n h μ o BS : ℕ} {J sup : ℕ → Bits n → ℂ}
    (hd : E.Valid kmin (MDesc.cls n h μ o BS J sup)) :
    (E.W^(h+1) + 1) * (E.W^(h+1) + 1) * (h + 3) + n + 1 ≤ 12 * (E.W + 1) * (E.W + 1) * (n + 1)^(2 * E.W + 1) := by
  obtain ⟨hμ, hreg, _⟩ := hd
  have hm : 1 ≤ E.mx := le_trans (by norm_num) E.three
  have hkh : kmin ^ h ≤ n := le_trans (Nat.le_mul_of_pos_left _ (Nat.mul_pos hm hμ)) hreg
  have hWk : E.W ≤ kmin ^ E.W := le_trans (Nat.lt_two_pow_self).le (Nat.pow_le_pow_left hk.two _)
  have hhn : h ≤ n := by
    have : h < 2^h := Nat.lt_two_pow_self
    have : 2^h ≤ kmin^h := Nat.pow_le_pow_left hk.two _
    omega
  have hWh : E.W^h ≤ (n + 1)^E.W := by
    calc E.W^h ≤ (kmin ^ E.W)^h := Nat.pow_le_pow_left hWk _
      _ = (kmin ^ h)^E.W := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ ≤ (n + 1)^E.W := Nat.pow_le_pow_left (by omega) _
  have hW1 : E.W^(h+1) + 1 ≤ (E.W + 1) * (n + 1)^E.W := by
    rw [pow_succ]
    have h1 : 1 ≤ (n + 1)^E.W := Nat.one_le_pow _ _ (by omega)
    nlinarith
  set X := (n + 1)^E.W with hX
  have hX1 : 1 ≤ X := Nat.one_le_pow _ _ (by omega)
  have e : (n + 1)^(2 * E.W + 1) = X * X * (n + 1) := by rw [hX, pow_succ, two_mul, pow_add]
  rw [e]
  have h2 : (E.W^(h+1) + 1) * (E.W^(h+1) + 1) ≤ ((E.W + 1) * X) * ((E.W + 1) * X) := Nat.mul_le_mul hW1 hW1
  have h3 : h + 3 ≤ 3 * (n + 1) := by omega
  have h4 := Nat.mul_le_mul h2 h3
  have h5 : n + 1 ≤ (E.W + 1) * (E.W + 1) * (X * X * (n + 1)) := by
    have : 1 ≤ (E.W + 1) * (E.W + 1) * (X * X) := by
      have : 0 < (E.W + 1) * (E.W + 1) * (X * X) := by positivity
      omega
    nlinarith
  nlinarith

/-- **The local work of a valid class is `O(2^n * (NU + cons))`.** -/
theorem clsLoc_dom {kmin : ℕ} (hk : E.KMin kmin) : ∃ C : ℕ, ∀ (n h μ o BS : ℕ) (J sup : ℕ → Bits n → ℂ),
    E.Valid kmin (MDesc.cls n h μ o BS J sup) →
    E.clsLoc n h μ + 1 ≤ C * (2^n * (E.NUc n h μ + E.cons n h μ) + 1) := by
  obtain ⟨C1, hC1⟩ := E.clsLoc_le hk
  obtain ⟨D, hD⟩ := MX.succ_pow_le_two_pow (2 * E.W + 1)
  refine ⟨C1 * (1 + 12 * (E.W + 1) * (E.W + 1) * D) + 1, fun n h μ o BS J sup hd => ?_⟩
  have h1 := hC1 n h μ o BS J sup hd
  have h2 := E.poly_valid hk hd
  have h3 := hD n
  have hNU := E.NU_pos hk hd
  set Y := 2^n * (E.NUc n h μ + E.cons n h μ)
  have hY : 2^n ≤ Y := by
    calc 2^n = 2^n * 1 := by ring
      _ ≤ Y := Nat.mul_le_mul_left _ (by omega)
  have h4 : (E.W^(h+1) + 1) * (E.W^(h+1) + 1) * (h + 3) + n + 1 ≤ 12 * (E.W + 1) * (E.W + 1) * D * Y := by
    calc _ ≤ 12 * (E.W + 1) * (E.W + 1) * (n + 1)^(2 * E.W + 1) := h2
      _ ≤ 12 * (E.W + 1) * (E.W + 1) * (D * 2^n) := Nat.mul_le_mul_left _ h3
      _ ≤ 12 * (E.W + 1) * (E.W + 1) * (D * Y) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hY)
      _ = _ := by ring
  have h5 : E.clsLoc n h μ ≤ C1 * (Y + 12 * (E.W + 1) * (E.W + 1) * D * Y) := by
    calc E.clsLoc n h μ ≤ C1 * (Y + (E.W^(h+1) + 1) * (E.W^(h+1) + 1) * (h + 3) + n + 1) := h1
      _ ≤ C1 * (Y + 12 * (E.W + 1) * (E.W + 1) * D * Y) := by
        apply Nat.mul_le_mul_left; omega
  have h6 : C1 * (Y + 12 * (E.W + 1) * (E.W + 1) * D * Y) = C1 * (1 + 12 * (E.W + 1) * (E.W + 1) * D) * Y := by ring
  rw [h6] at h5
  set K := C1 * (1 + 12 * (E.W + 1) * (E.W + 1) * D)
  have h7 : (K + 1) * (Y + 1) = K * Y + K + Y + 1 := by ring
  rw [h7]
  omega

end Eng

end
end PowerSaving.RAM
end OAI
