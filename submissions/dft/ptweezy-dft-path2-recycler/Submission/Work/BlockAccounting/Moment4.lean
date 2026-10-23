import Submission.Work.BlockAccounting.Moment

/-!
# Fourth-order term bound for the moment certificates (agent key: block-accounting, x-pack)

Importable module `Work.BlockAccounting.Moment4`.  Imports only `Work.BlockAccounting.Moment` (Mathlib only).
No `sorry`.

`term_le4` is a drop-in replacement for `term_le` (same arguments, same conclusion `T m (1-ε) r n ≤ q`) whose
hypothesis `hq` uses the fourth-order bound `exp x ≤ 1 + x + x²/2 + x³/6 + (5/96) x⁴` on `[0,1]`
(`Real.exp_bound'` with `n = 4`) instead of the third-order `1 + x + x²/2 + (2/9) x³`.  At the exponents of the
nine-stage certificates (`x = ε log 73 ≈ 0.0053`) the third-order remainder costs about a dozen units of `10^-10`
in the certified saving; the fourth-order one costs none at that grid.
-/

namespace OAI.PowerSaving.BlockAccounting
open Finset

/-- Fourth-order upper bound of `exp` on `[0,1]`. -/
lemma exp_le_quartic (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Real.exp x ≤ 1 + x + x^2/2 + x^3/6 + x^4*(5/96) := by
  have h := Real.exp_bound' h0 h1 (n := 4) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

/-- `(r/m)^(1-ε) ≤ (r/m) (1 + x + x²/2 + x³/6 + (5/96) x⁴)` with `x = ε L`, when `log (m/r) ≤ L`. -/
lemma rpow_ratio_le4 (r m L ε : ℝ) (hr : 0 < r) (hm : 0 < m) (hε : 0 ≤ ε) (hL0 : 0 ≤ L)
    (hL : Real.log (m/r) ≤ L) (hx : ε * L ≤ 1) :
    (r/m)^(1-ε) ≤ r/m * (1 + ε*L + (ε*L)^2/2 + (ε*L)^3/6 + (ε*L)^4*(5/96)) := by
  have hx0 : (0:ℝ) < r/m := div_pos hr hm
  have hlog : Real.log (r/m) = - Real.log (m/r) := by
    rw [← Real.log_inv, inv_div]
  have h1 : (r/m)^(1-ε) = r/m * Real.exp (ε * Real.log (m/r)) := by
    rw [Real.rpow_def_of_pos hx0, hlog,
      show -Real.log (m/r) * (1-ε) = -Real.log (m/r) + ε * Real.log (m/r) by ring,
      Real.exp_add, ← hlog, Real.exp_log hx0]
  rw [h1]
  apply mul_le_mul_of_nonneg_left _ hx0.le
  have h2 : Real.exp (ε * Real.log (m/r)) ≤ Real.exp (ε * L) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hL hε)
  exact h2.trans (exp_le_quartic (ε*L) (mul_nonneg hε hL0) hx)

/-- Upper bound for one term of the moment at `z = 1 - ε` (fourth order; drop-in for `term_le`). -/
lemma term_le4 (m r n : ℕ) (ε L q : ℝ) (hr : 0 < r) (hm : 0 < m) (hε : 0 ≤ ε) (hL0 : 0 ≤ L)
    (hL : Real.log ((m:ℝ)/(r:ℝ)) ≤ L) (hx : ε * L ≤ 1)
    (hq : (n:ℝ) * ((r:ℝ)/(m:ℝ) * (1 + ε*L + (ε*L)^2/2 + (ε*L)^3/6 + (ε*L)^4*(5/96))) ≤ q) :
    T m (1-ε) r n ≤ q := by
  have hr' : (0:ℝ) < (r:ℝ) := by exact_mod_cast hr
  have hm' : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have h := rpow_ratio_le4 (r:ℝ) (m:ℝ) L ε hr' hm' hε hL0 hL hx
  have h' : T m (1-ε) r n
      ≤ (n:ℝ) * ((r:ℝ)/(m:ℝ) * (1 + ε*L + (ε*L)^2/2 + (ε*L)^3/6 + (ε*L)^4*(5/96))) :=
    mul_le_mul_of_nonneg_left h (by positivity)
  exact h'.trans hq

end OAI.PowerSaving.BlockAccounting

#print axioms OAI.PowerSaving.BlockAccounting.term_le4
