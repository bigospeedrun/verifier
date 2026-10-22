import Submission.Work.XHostT.KHist
import Submission.Work.XHostT.KHeadC

/-!
# (key: bridge-host-cross) What the per-kind counters mean, and all host indices by replica, kind, side and class

* `sum_range_mul`, `sum_range_224`, **`sum_bins`**: a sum over all host indices `i < 224 (9 n)` of a table is the sum
  over replicas `ρ < n`, kinds `c < 9`, classes `t < 112` of its two sides `2016 ρ + 224 c + t` (x) and
  `2016 ρ + 224 c + 112 + t` (y): the index layout of p-a3's `decH` / `encH'`;
* **`cntK_card`**: `cntK rt v c n` is the number of hosts `(ρ, (s, t))` of kind `c` whose remainder
  `remAt rt (2016 ρ + 224 c + (if s then 112 else 0) + t)` is `v` (the form of `schedOfTabOK_hrem`);
* `resGE_sound`, `resEqP_sound`.
x-tables (wht45/lever2979, 19 Oct 2026); prepared with assistance from Claude.  No `sorry`.
-/

namespace OAI.PowerSaving.XHostT.K
open Finset

lemma sum_range_mul {M : Type*} [AddCommMonoid M] (g : ℕ → M) (k : ℕ) : ∀ m : ℕ,
    ∑ i ∈ range (m * k), g i = ∑ x ∈ range m, ∑ y ∈ range k, g (k * x + y)
  | 0 => by simp
  | m + 1 => by
    rw [show (m + 1) * k = m * k + k by ring, sum_range_add, sum_range_mul g k m, sum_range_succ, Nat.mul_comm m k]

lemma sum_range_224 {M : Type*} [AddCommMonoid M] (g : ℕ → M) :
    ∑ b ∈ range 224, g b = ∑ t : Fin 112, (g t.val + g (112 + t.val)) := by
  rw [show range 224 = range (112 + 112) from rfl, sum_range_add, sum_range, sum_range, ← sum_add_distrib]

/-- **all host indices of a table of `n` replicas, by replica, kind, side and class.** -/
theorem sum_bins {M : Type*} [AddCommMonoid M] (g : ℕ → M) (n : ℕ) :
    ∑ i ∈ range (224 * (9 * n)), g i =
      ∑ ρ : Fin n, ∑ c : Fin 9, ∑ t : Fin 112,
        (g (2016 * ρ.val + 224 * c.val + t.val) + g (2016 * ρ.val + 224 * c.val + 112 + t.val)) := by
  rw [show 224 * (9 * n) = n * 2016 by ring, sum_range_mul g 2016 n, sum_range]
  refine Fintype.sum_congr _ _ (fun ρ => ?_)
  rw [show range 2016 = range (9 * 224) from rfl, sum_range_mul (fun y => g (2016 * ρ.val + y)) 224 9, sum_range]
  refine Fintype.sum_congr _ _ (fun c => ?_)
  rw [sum_range_224 (fun z => g (2016 * ρ.val + (224 * c.val + z)))]
  refine Fintype.sum_congr _ _ (fun t => ?_)
  simp only [Nat.add_assoc]

lemma cntK_sum (rt : CT) (v c : ℕ) : ∀ n, cntK rt v c n = ∑ ρ ∈ range n, cntB (rt.get (9 * ρ + c)).1 v 224
  | 0 => by simp [cntK]
  | n + 1 => by rw [cntK, cntK_sum rt v c n, sum_range_succ]

/-- **what `cntK` counts.** -/
theorem cntK_card (rt : CT) (v : ℕ) (c : Fin 9) (n : ℕ) :
    cntK rt v c.val n = #{p ∈ (univ : Finset (Fin n × Bool × Fin 112)) |
      remAt rt (2016 * p.1.val + 224 * c.val + (if p.2.1 then 112 else 0) + p.2.2.val) = v} := by
  rw [card_filter, Fintype.sum_prod_type, cntK_sum, sum_range]
  refine Fintype.sum_congr _ _ (fun ρ => ?_)
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  rw [cntB_sum, sum_range_224, ← sum_add_distrib]
  refine Fintype.sum_congr _ _ (fun t => ?_)
  have h0 : remAt rt (2016 * ρ.val + 224 * c.val + t.val) = fld6 (rt.get (9 * ρ.val + c.val)).1 t.val := by
    rw [show 2016 * ρ.val + 224 * c.val + t.val = 224 * (9 * ρ.val + c.val) + t.val by ring]
    exact remAt_kind rt _ _ (by omega)
  have h1 : remAt rt (2016 * ρ.val + 224 * c.val + 112 + t.val)
      = fld6 (rt.get (9 * ρ.val + c.val)).1 (112 + t.val) := by
    rw [show 2016 * ρ.val + 224 * c.val + 112 + t.val = 224 * (9 * ρ.val + c.val) + (112 + t.val) by ring]
    exact remAt_kind rt _ _ (by omega)
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, h0, h1]
  exact Nat.add_comm _ _

theorem resGE_sound (resT p v : ℕ) : ∀ m, resGE resT p v m = true → ∀ q < m, v ≤ resAt resT p q
  | 0, _, q, hq => absurd hq (Nat.not_lt_zero q)
  | m + 1, h, q, hq => by
    simp only [resGE, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hq | rfl
    · exact resGE_sound resT p v m h.1 q hq
    · exact Nat.le_of_ble_eq_true h.2

theorem resEqP_sound (resT : ℕ) : ∀ m, resEqP resT m = true → ∀ q < m, resAt resT 0 q = resAt resT 1 q
  | 0, _, q, hq => absurd hq (Nat.not_lt_zero q)
  | m + 1, h, q, hq => by
    simp only [resEqP, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hq | rfl
    · exact resEqP_sound resT m h.1 q hq
    · exact Nat.eq_of_beq_eq_true h.2

end OAI.PowerSaving.XHostT.K

#print axioms OAI.PowerSaving.XHostT.K.sum_bins
#print axioms OAI.PowerSaving.XHostT.K.cntK_card
#print axioms OAI.PowerSaving.XHostT.K.resGE_sound
