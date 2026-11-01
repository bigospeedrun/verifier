import Submission.Work.Mixed.Bound

/-!
# The two-target rule of a cut word (K = 2), and its rate fact in normalised form

e-r12, 19 Oct 2026.  For the bridge (p-bridge) and the rate fact (R5): a `Rule` built from plain numbers,
and the rate fact in the `BlockAccounting.moment` shape `∑_j (r_j/m)^z ≤ (W - H) + H (kc/m)^z`.

Half cut on #3945 (BRIEF.md): `m = 73`, `kc = 49` (heads cut by 24 of their 48 axes), `rmax = 48`, `H` = the
number of literal rank-48 heads, `W` = arrays of the unit, `rk` = the paid ranks of the body in word order.
-/

namespace OAI.PowerSaving.MX

namespace Rule

/-- The mixed rule of a cut word with two targets: `W` arrays of `m` axes, `H` of them (the cut heads) with
target rank `kc` and the other `W - H` with the full target `m`; `P` paid rounds with ranks `rk j ∈ [1, rmax]`,
separated (`rmax < kc`). -/
def twoTarget (m kc W H P rmax : ℕ) (rk : Fin P → ℕ) (hrk1 : ∀ j, 1 ≤ rk j) (hrk : ∀ j, rk j ≤ rmax)
    (hsep : rmax < kc) (hkc : kc ≤ m) (h2 : 2 ≤ kc) (hH : 1 ≤ H) : Rule where
  K := 2
  kr := ![m, kc]
  Wk := ![W - H, H]
  m := m
  P := P
  rk := rk
  kmin := kc
  rmax := rmax
  kmin_le := by intro k; fin_cases k <;> simp [hkc]
  kr_le := by intro k; fin_cases k <;> simp [hkc]
  rk_pos := hrk1
  rk_le := hrk
  sep := hsep
  two_le_kmin := h2
  kmin_att := ⟨1, by simp, by simpa using hH⟩

/-- The rate fact of the two-target rule from its normalised (moment) form. -/
theorem twoTarget_rateQ {m kc W H P rmax : ℕ} {rk : Fin P → ℕ} (hrk1 : ∀ j, 1 ≤ rk j) (hrk : ∀ j, rk j ≤ rmax)
    (hsep : rmax < kc) (hkc : kc ≤ m) (h2 : 2 ≤ kc) (hH : 1 ≤ H) {z : ℝ}
    (h : ∑ j, ((rk j : ℝ) / m) ^ z ≤ ((W - H : ℕ) : ℝ) + (H : ℝ) * ((kc : ℝ) / m) ^ z) :
    (twoTarget m kc W H P rmax rk hrk1 hrk hsep hkc h2 hH).RateQ z 1 := by
  have hm : (m : ℝ) ≠ 0 := by
    have : 0 < m := by omega
    exact_mod_cast this.ne'
  have key : ∑ j : Fin P, ((rk j : ℝ) / m) ^ z ≤
      ∑ k : Fin 2, ((![W - H, H] k : ℕ) : ℝ) * (((![m, kc] k : ℕ) : ℝ) / m) ^ z := by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [div_self hm, Real.one_rpow, mul_one]
    exact h
  exact rateQ_of_normalized _ key

/-- the same with the left side by histogram of the paid ranks (`cnt r` = number of paid rounds of rank `r`) -/
theorem twoTarget_rateQ_hist {m kc W H P rmax : ℕ} {rk : Fin P → ℕ} (hrk1 : ∀ j, 1 ≤ rk j)
    (hrk : ∀ j, rk j ≤ rmax) (hsep : rmax < kc) (hkc : kc ≤ m) (h2 : 2 ≤ kc) (hH : 1 ≤ H) {z : ℝ}
    (h : ∑ r ∈ Finset.range (rmax + 1), ((Finset.univ.filter fun j => rk j = r).card : ℝ) * ((r : ℝ) / m) ^ z
      ≤ ((W - H : ℕ) : ℝ) + (H : ℝ) * ((kc : ℝ) / m) ^ z) :
    (twoTarget m kc W H P rmax rk hrk1 hrk hsep hkc h2 hH).RateQ z 1 := by
  refine twoTarget_rateQ hrk1 hrk hsep hkc h2 hH ?_
  have e : ∑ j : Fin P, ((rk j : ℝ) / m) ^ z = ∑ r ∈ Finset.range (rmax + 1),
      ((Finset.univ.filter fun j : Fin P => rk j = r).card : ℝ) * ((r : ℝ) / m) ^ z :=
    (twoTarget m kc W H P rmax rk hrk1 hrk hsep hkc h2 hH).sum_rk_hist (fun r => ((r : ℝ) / m) ^ z)
  rw [e]
  exact h

/-- **R2 for the two-target rule**, in one statement: the rate fact in moment form at `z1 > 0` gives, for every
`z ∈ (z1, 1]` and every threshold `n0 ≥ m`, `allotM n0 n ≤ C 2^n (n+1)^z`. -/
theorem twoTarget_allotM_bound {m kc W H P rmax : ℕ} {rk : Fin P → ℕ} (hrk1 : ∀ j, 1 ≤ rk j)
    (hrk : ∀ j, rk j ≤ rmax) (hsep : rmax < kc) (hkc : kc ≤ m) (h2 : 2 ≤ kc) (hH : 1 ≤ H) {z1 z : ℝ}
    (h : ∑ j, ((rk j : ℝ) / m) ^ z1 ≤ ((W - H : ℕ) : ℝ) + (H : ℝ) * ((kc : ℝ) / m) ^ z1)
    (hz1 : 0 < z1) (h12 : z1 < z) (hz : z ≤ 1) {n0 : ℕ} (hn0 : m ≤ n0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ((twoTarget m kc W H P rmax rk hrk1 hrk hsep hkc h2 hH).allotM n0 n : ℝ)
      ≤ C * 2 ^ n * ((n : ℝ) + 1) ^ z :=
  (twoTarget m kc W H P rmax rk hrk1 hrk hsep hkc h2 hH).allotM_bound
    (twoTarget_rateQ hrk1 hrk hsep hkc h2 hH h) hz1 h12 hz hn0

end Rule

end OAI.PowerSaving.MX
