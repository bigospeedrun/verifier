import Submission.Work.MixedCost.Bridge
import Submission.Work.MixedCost.Poly

/-!
# Mixed engine, top body part 7: the top job's local work is `O(locS)`

(agent e-r3cost, round wht45/lever, 19 Oct 2026.)

* `Ptop_le`   the bookkeeping is polynomial, hence `≤ D * 2^n`;
* `locTop_dom` **`locTop = O(locS (top n B))`** for the rule `R` of the engine (`hloc` of `mixed_close`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset GF MXR
noncomputable section

namespace Eng
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ] (E : Eng α ρ σ)

lemma kmin_pow_topG (kmin n : ℕ) (hk : 2 ≤ kmin) : kmin ^ E.topG kmin n ≤ n + 1 := by
  by_cases h0 : E.topG kmin n = 0
  · rw [h0]; simp
  · have hP : E.mx * kmin ^ E.topG kmin n ≤ n :=
      Nat.findGreatest_of_ne_zero (P := fun g => E.mx * kmin ^ g ≤ n) (n := n) (m := E.topG kmin n) rfl h0
    have h3 : 1 ≤ E.mx := le_trans (by norm_num) E.three
    have : kmin ^ E.topG kmin n ≤ E.mx * kmin ^ E.topG kmin n := Nat.le_mul_of_pos_left _ h3
    omega

lemma pow_topG_le (kmin n b : ℕ) (hk : 2 ≤ kmin) : b ^ E.topG kmin n ≤ (n + 1) ^ b := by
  have hb : b ≤ kmin ^ b := le_trans (Nat.lt_two_pow_self).le (Nat.pow_le_pow_left hk _)
  calc b ^ E.topG kmin n ≤ (kmin ^ b) ^ E.topG kmin n := Nat.pow_le_pow_left hb _
    _ = (kmin ^ E.topG kmin n) ^ b := by rw [← pow_mul, ← pow_mul, mul_comm]
    _ ≤ (n + 1) ^ b := Nat.pow_le_pow_left (E.kmin_pow_topG kmin n hk) _

lemma Ptop_poly (kmin n M Q : ℕ) (hM1 : E.W ≤ M) (hM2 : E.nB + 1 ≤ M) (hM3 : 2 ≤ M)
    (hQ : Q = M ^ E.topG kmin n) :
    E.Ptop kmin n ≤ (64 * (E.W + 1) * (E.nB + 1) + 64) * ((Q * Q) * ((n + 1) * (n + 1))) := by
  have hGn : E.topG kmin n ≤ n := E.topG_le kmin n
  have hQ1 : 1 ≤ Q := by rw [hQ]; exact Nat.one_le_pow _ _ (by omega)
  have hWQ : E.W ^ E.topG kmin n ≤ Q := by rw [hQ]; exact Nat.pow_le_pow_left hM1 _
  have hBQ : (E.nB + 1) ^ E.topG kmin n ≤ Q := by rw [hQ]; exact Nat.pow_le_pow_left hM2 _
  have hNU : E.NUc n (E.topG kmin n) 1 ≤ Q := le_trans (MXR.NU_le _ _ _) hWQ
  generalize hX : (Q * Q) * ((n + 1) * (n + 1)) = X
  have hn1 : 1 ≤ n + 1 := by omega
  have hQQ : Q ≤ Q * Q := Nat.le_mul_of_pos_left _ hQ1
  have hnn : n + 1 ≤ (n + 1) * (n + 1) := Nat.le_mul_of_pos_left _ hn1
  have a1 : Q * Q * (n + 1) ≤ X := by rw [← hX]; exact Nat.mul_le_mul_left _ hnn
  have a2 : Q * (n + 1) ≤ X := by rw [← hX]; exact Nat.mul_le_mul hQQ hnn
  have a3 : Q ≤ X := le_trans (Nat.le_mul_of_pos_right _ hn1) a2
  have a4 : (n + 1) * (n + 1) ≤ X := by rw [← hX]; exact Nat.le_mul_of_pos_left _ (Nat.mul_pos hQ1 hQ1)
  -- the five terms
  have t12 : (n + 1) + (n * (n + 3) + 1) ≤ 4 * X := by nlinarith
  have t3 : E.idxCost n (E.topG kmin n) 1 ≤ 8 * X := by
    unfold idxCost
    have h1 : E.W ^ E.topG kmin n + 1 ≤ 2 * Q := by omega
    have h2 : E.topG kmin n + 2 ≤ 2 * (n + 1) := by omega
    calc (E.W ^ E.topG kmin n + 1) * (E.W ^ E.topG kmin n + 1) * (E.topG kmin n + 2)
        ≤ (2 * Q) * (2 * Q) * (2 * (n + 1)) := Nat.mul_le_mul (Nat.mul_le_mul h1 h1) h2
      _ = 8 * (Q * Q * (n + 1)) := by ring
      _ ≤ 8 * X := Nat.mul_le_mul_left _ a1
  have t4 : E.NUc n (E.topG kmin n) 1 * (4 * n + 4 * E.topG kmin n + 8) ≤ 8 * X := by
    calc E.NUc n (E.topG kmin n) 1 * (4 * n + 4 * E.topG kmin n + 8) ≤ Q * (8 * (n + 1)) :=
          Nat.mul_le_mul hNU (by omega)
      _ = 8 * (Q * (n + 1)) := by ring
      _ ≤ 8 * X := Nat.mul_le_mul_left _ a2
  have t5 : E.cstC (E.topG kmin n) ≤ (16 * (E.W + 1) * (E.nB + 1) + 2) * X := by
    refine le_trans (E.cstC_le _) ?_
    have hb : (E.nB + 1) ^ E.topG kmin n ≤ Q := hBQ
    unfold locH
    have h1 : E.W ^ E.topG kmin n * E.W * (2 * E.topG kmin n + 3 + 1) ≤ Q * E.W * (8 * (n + 1)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ hWQ) (by omega)
    have h2 : E.nB * (E.W ^ E.topG kmin n * E.W * (2 * E.topG kmin n + 3 + 1) + 1 + (E.topG kmin n + 1) + 4) + 2 ≤
        E.nB * (Q * E.W * (8 * (n + 1)) + 8 * (n + 1)) + 2 := by
      have := Nat.mul_le_mul_left E.nB (show E.W ^ E.topG kmin n * E.W * (2 * E.topG kmin n + 3 + 1) + 1 +
        (E.topG kmin n + 1) + 4 ≤ Q * E.W * (8 * (n + 1)) + 8 * (n + 1) by omega)
      omega
    calc (E.nB + 1) ^ E.topG kmin n * (E.nB * (E.W ^ E.topG kmin n * E.W * (2 * E.topG kmin n + 3 + 1) + 1 +
          (E.topG kmin n + 1) + 4) + 2)
        ≤ Q * (E.nB * (Q * E.W * (8 * (n + 1)) + 8 * (n + 1)) + 2) := Nat.mul_le_mul hb h2
      _ = 8 * (E.nB * E.W) * (Q * Q * (n + 1)) + 8 * E.nB * (Q * (n + 1)) + 2 * Q := by ring
      _ ≤ 8 * (E.nB * E.W) * X + 8 * E.nB * X + 2 * X :=
          Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ a1) (Nat.mul_le_mul_left _ a2))
            (Nat.mul_le_mul_left _ a3)
      _ = (8 * (E.nB * E.W) + 8 * E.nB + 2) * X := by ring
      _ ≤ (16 * (E.W + 1) * (E.nB + 1) + 2) * X := by
          apply Nat.mul_le_mul_right
          have : 16 * (E.W + 1) * (E.nB + 1) = 16 * (E.nB * E.W) + 16 * E.W + 16 * E.nB + 16 := by ring
          omega
  unfold Ptop
  have hfin : (4 + 8 + 8 + (16 * (E.W + 1) * (E.nB + 1) + 2)) * X ≤ (64 * (E.W + 1) * (E.nB + 1) + 64) * X := by
    apply Nat.mul_le_mul_right
    have : 1 ≤ (E.W + 1) * (E.nB + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
    have e : 64 * (E.W + 1) * (E.nB + 1) = 64 * ((E.W + 1) * (E.nB + 1)) := by ring
    have e' : 16 * (E.W + 1) * (E.nB + 1) = 16 * ((E.W + 1) * (E.nB + 1)) := by ring
    omega
  have e6 : (4 + 8 + 8 + (16 * (E.W + 1) * (E.nB + 1) + 2)) * X =
      4 * X + 8 * X + 8 * X + (16 * (E.W + 1) * (E.nB + 1) + 2) * X := by ring
  omega

/-- **The bookkeeping is polynomial**, hence at most `D * 2^n`. -/
theorem Ptop_le (kmin : ℕ) (hk : 2 ≤ kmin) : ∃ D : ℕ, ∀ n, E.Ptop kmin n ≤ D * 2 ^ n := by
  obtain ⟨M, hM⟩ : ∃ M, M = (E.W + 1) * (E.nB + 1) * 2 := ⟨_, rfl⟩
  have hM1 : E.W ≤ M := by rw [hM]; nlinarith
  have hM2 : E.nB + 1 ≤ M := by rw [hM]; nlinarith
  have hM3 : 2 ≤ M := by rw [hM]; nlinarith
  obtain ⟨D0, hD0⟩ := MX.succ_pow_le_two_pow (2 * M + 2)
  refine ⟨(64 * (E.W + 1) * (E.nB + 1) + 64) * D0, fun n => ?_⟩
  have h1 := E.Ptop_poly kmin n M (M ^ E.topG kmin n) hM1 hM2 hM3 rfl
  have hQn : M ^ E.topG kmin n ≤ (n + 1) ^ M := E.pow_topG_le kmin n M hk
  have hpoly : (M ^ E.topG kmin n * M ^ E.topG kmin n) * ((n + 1) * (n + 1)) ≤ (n + 1) ^ (2 * M + 2) := by
    have : (M ^ E.topG kmin n * M ^ E.topG kmin n) * ((n + 1) * (n + 1)) ≤
        ((n + 1) ^ M * (n + 1) ^ M) * ((n + 1) * (n + 1)) := Nat.mul_le_mul_right _ (Nat.mul_le_mul hQn hQn)
    refine le_trans this (le_of_eq ?_)
    ring
  calc E.Ptop kmin n ≤ (64 * (E.W + 1) * (E.nB + 1) + 64) * ((M ^ E.topG kmin n * M ^ E.topG kmin n) * ((n + 1) * (n + 1))) := h1
    _ ≤ (64 * (E.W + 1) * (E.nB + 1) + 64) * (D0 * 2 ^ n) := Nat.mul_le_mul_left _ (le_trans hpoly (hD0 n))
    _ = (64 * (E.W + 1) * (E.nB + 1) + 64) * D0 * 2 ^ n := by ring


variable {E} {R : MX.Rule} {typ : ℕ → Fin R.K} {kmin : ℕ}

/-- **The top job's local work is `O(locS)`** (the `hloc` of `mixed_close` on top shapes). -/
theorem BridgeHyp.locTop_dom (H : E.BridgeHyp R typ kmin) (hk : 2 ≤ kmin) (n0 : ℕ) :
    ∃ C : ℕ, ∀ n B, E.locTop kmin n0 n B + 1 ≤ C * (R.locS n0 (MX.Shape.top n B) + 1) := by
  obtain ⟨D, hD⟩ := E.Ptop_le kmin hk
  refine ⟨D + 2, fun n B => ?_⟩
  unfold locTop
  simp only [MX.Rule.locS]
  by_cases hn : n0 ≤ n
  · rw [if_pos hn, if_pos hn, H.topN_eq n]
    have h1 := hD n
    have hX : 2 ^ n ≤ (B + 1) * 2 ^ n := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    have h2 : D * 2 ^ n ≤ D * ((B + 1) * 2 ^ n) := Nat.mul_le_mul_left _ hX
    generalize (B + 1) * 2 ^ n = X at *
    generalize B % R.Nsrc n * (n + 1) * 2 ^ n = Y at *
    nlinarith
  · rw [if_neg hn, if_neg hn]
    generalize (B + 1) * (n + 1) * 2 ^ n = Z
    nlinarith

end Eng

end
end PowerSaving.RAM
end OAI

#print axioms OAI.PowerSaving.RAM.Eng.Ptop_le
#print axioms OAI.PowerSaving.RAM.Eng.BridgeHyp.locTop_dom
