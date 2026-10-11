/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.AllEdges.Passes
public import Submission.ThreeSumApsp.Spec.Sec3.Theorem21b.NegativeTriangle

/-!
# All pairs by prefixes, pair by pair

`X[i,k] + Y[k,j] < V[i,j]` exactly if `−V[i,j] + Yᵀ[j,k] + X[i,k] < 0`, a negative triangle on the
edge `(i, j)`.  As for Negative Triangle, this holds exactly if, at one of the levels `ℓ < L` and
for `e = 2` or `e = 3`, the instance of the prefixes has a zero triangle on the edge `(i, j)`
(`pair_iff_exists_level`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-- For three weights: a negative sum, by prefixes. -/
theorem neg_iff_exists_level {U L : ℕ} {w₁ w₂ w₃ : ℤ} (h₁ : |w₁| ≤ U) (h₂ : |w₂| ≤ U)
    (h₃ : |w₃| ≤ U) (hL : 3 * U < 2 ^ L) :
    w₁ + w₂ + w₃ < 0 ↔ ∃ ℓ < L, ∃ e : ℤ, (e = 2 ∨ e = 3) ∧
      ((triOf 1 [w₁] [w₂] [w₃]).mapWeights (Theorem21.negToExact U ℓ e)).S 0 0 0 = 0 := by
  have hT : (triOf 1 [w₁] [w₂] [w₃]).WeightsBoundedBy (U : ℤ) :=
    triOf_bounded (by simpa [AbsLe] using h₁) (by simpa [AbsLe] using h₂)
      (by simpa [AbsLe] using h₃)
  have h := Theorem21.hasNegativeTriangle_iff _ hT hL
  have hS : ∀ (T : TriangleInstance ℤ 1) (P : Fin 1 → Fin 1 → Fin 1 → Prop),
      (∃ a b c, P a b c) ↔ P 0 0 0 := fun _ P =>
    ⟨fun ⟨a, b, c, h⟩ => by rwa [Subsingleton.elim a 0, Subsingleton.elim b 0,
      Subsingleton.elim c 0] at h, fun h => ⟨0, 0, 0, h⟩⟩
  simp only [TriangleInstance.HasNegativeTriangle, TriangleInstance.HasZeroTriangle,
    TriangleInstance.IsZeroTriangle] at h
  rw [hS (triOf 1 [w₁] [w₂] [w₃]) fun a b c => _] at h
  simp only [hS (triOf 1 [w₁] [w₂] [w₃]) fun a b c => _] at h
  simpa [TriangleInstance.S, triOf] using h

/-- The weights `−V`. -/
def negL (V : List ℤ) : List ℤ := affL (-1) 0 V

/-- The prefixes of the first matrix at the level `ℓ`. -/
def pairsQAB (U ℓ : ℕ) (V : List ℤ) : List ℤ := (affL 2 (2 * U) (negL V)).map (prefQ ℓ)

/-- The prefixes of the second matrix at the level `ℓ`. -/
def pairsQBC (n U ℓ : ℕ) (Y : List ℤ) : List ℤ :=
  (affL 2 (2 * U) (Light.Sec3.transL n Y)).map (prefQ ℓ)

theorem absLe_negL {V : List ℤ} {U : ℤ} (h : AbsLe V U) : AbsLe (negL V) U := by
  intro x hx
  simp only [negL, affL, List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  simpa using h y hy

theorem absLe_transL {n : ℕ} {Y : List ℤ} {U : ℕ} (h : AbsLe Y U) :
    AbsLe (Light.Sec3.transL n Y) U := by
  intro x hx
  simp only [Light.Sec3.transL, List.mem_map] at hx
  obtain ⟨q, -, rfl⟩ := hx
  exact AbsLe.abs_getD_le (Int.natCast_nonneg U) h _

theorem getD_transL {n : ℕ} {Y : List ℤ} {b c : ℕ} (hb : b < n) (hc : c < n) :
    (Light.Sec3.transL n Y).getD (b * n + c) 0 = Y.getD (c * n + b) 0 := by
  have hlt : b * n + c < n * n := by nlinarith
  rw [Light.Sec3.transL, List.getD_eq_getElem _ _ (by simpa using hlt)]
  simp only [List.getElem_map, List.getElem_range]
  rw [show (b * n + c) % n = c by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc],
    show (b * n + c) / n = b by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hc, Nat.zero_add]]

/-- **All pairs by prefixes**, for the pair `q = i n + j`. -/
theorem pair_iff_exists_level {n U L : ℕ} {X Y V : List ℤ} (lX : X.length = n * n)
    (lY : Y.length = n * n) (lV : V.length = n * n) (hX : AbsLe X U) (hY : AbsLe Y U)
    (hV : AbsLe V U) (hL : 3 * U < 2 ^ L) {q : ℕ} (hq : q < n * n) :
    (∃ k < n, X.getD (q / n * n + k) 0 + Y.getD (k * n + q % n) 0 < V.getD q 0) ↔
      ∃ ℓ < L, ∃ e : ℤ, (e = 2 ∨ e = 3) ∧ ∃ c < n, (pairsQAB U ℓ V).getD q 0 +
        (pairsQBC n U ℓ Y).getD (q % n * n + c) 0 + (negThird U ℓ e X).getD (q / n * n + c) 0
          = 0 := by
  have hn : 0 < n := by rcases Nat.eq_zero_or_pos n with h | h <;> simp_all
  have ha : q / n < n := Nat.div_lt_of_lt_mul hq
  have hb : q % n < n := Nat.mod_lt _ hn
  have hU : (0 : ℤ) ≤ U := Int.natCast_nonneg U
  have lN : (negL V).length = n * n := by simp [negL, lV]
  have lT : (Light.Sec3.transL n Y).length = n * n := by simp [Light.Sec3.transL]
  have hlev := fun ℓ e => triOf_level lN lT lX (absLe_negL hV) (absLe_transL hY) hX ℓ e
  -- the sum of the prefix instance on (q / n, q % n, c), by the level lemma
  have hsum : ∀ ℓ (e : ℤ) (c : ℕ) (hc : c < n), (pairsQAB U ℓ V).getD q 0 +
      (pairsQBC n U ℓ Y).getD (q % n * n + c) 0 + (negThird U ℓ e X).getD (q / n * n + c) 0 =
      ((triOf 1 [-V.getD q 0] [Y.getD (c * n + q % n) 0] [X.getD (q / n * n + c) 0]).mapWeights
        (Theorem21.negToExact U ℓ e)).S 0 0 0 := by
    intro ℓ e c hc
    have h := congrArg (fun T => TriangleInstance.S T ⟨q / n, ha⟩ ⟨q % n, hb⟩ ⟨c, hc⟩) (hlev ℓ e)
    have hq' : q / n * n + q % n = q := Nat.div_add_mod' q n
    have hnegq : (negL V).getD q 0 = -V.getD q 0 := by
      rw [negL, affL, List.getD_map_of_lt _ (by omega) 0 0]
      ring
    simp only [TriangleInstance.S, triOf, TriangleInstance.mapWeights, hq', pairsQAB,
      pairsQBC] at h ⊢
    rw [h, hnegq, getD_transL hb hc]
    simp [triOf, Theorem21.negToExact]
  constructor
  · rintro ⟨k, hk, hlt⟩
    have h₁ : |-V.getD q 0| ≤ U := by rw [abs_neg]; exact AbsLe.abs_getD_le hU hV q
    obtain ⟨ℓ, hℓ, e, he, h0⟩ := (neg_iff_exists_level h₁ (AbsLe.abs_getD_le hU hY _)
      (AbsLe.abs_getD_le hU hX _) hL).1 (by linarith)
    exact ⟨ℓ, hℓ, e, he, k, hk, by rw [hsum ℓ e k hk]; exact h0⟩
  · rintro ⟨ℓ, hℓ, e, he, c, hc, h0⟩
    have h₁ : |-V.getD q 0| ≤ U := by rw [abs_neg]; exact AbsLe.abs_getD_le hU hV q
    have := (neg_iff_exists_level h₁ (AbsLe.abs_getD_le hU hY (c * n + q % n))
      (AbsLe.abs_getD_le hU hX (q / n * n + c)) hL).2 ⟨ℓ, hℓ, e, he, by rw [← hsum ℓ e c hc]; exact h0⟩
    exact ⟨c, hc, by linarith⟩

end ThreeSumApsp.Spec
