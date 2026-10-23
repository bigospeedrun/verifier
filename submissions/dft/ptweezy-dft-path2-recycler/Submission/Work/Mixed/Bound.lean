import Submission.Work.Mixed.Phi
import Submission.Work.Mixed.LemmaA
import Submission.Work.MixedCost.Bill

/-!
# R2: the cost bound of the mixed recursion (Theorem 1G, rl-prove; lg-g2 DESIGN 3.3)

rb-r12 (14 Oct) / e-r12 (19 Oct 2026).  This file assembles the job-model flow (`Work.Mixed.Flow`,
`Work.Mixed.Phi`) and the abstract induction (`Work.Mixed.LemmaA`) into the bound that the R3 bill
(rb-r3cost INTERFACE.txt, item 3) needs.

* `treeCost`, `Rnd`, `JobRec`, `allotM`, `allotM_upper` : e-r3cost's, in `Work.MixedCost.Bill` (not redefined here).
* `allotM_bound`  : for a rate fact at `z1 > 0` and any `z1 < z ≤ 1`, `allotM n0 n ≤ C 2^n (n+1)^z` (every `n0 ≥ m`).
* `Nsrc_poly`, `poly_le_two_pow`, `poly_le_const_two_pow` : polynomial counts against `2^n`.
* `rateQ_of_normalized`, `sum_rk_hist` : bridges from the `moment` / histogram form of the rate fact.

No log factor is needed (no Lemma A3): the exits' Phi at `z` is at most `2 (rmax (rmax/kmin)^G)^δ` times
the sources' Phi (`exits_small`, from Lemma D at `z1` and `δ = z - z1 > 0`), which tends to 0.
-/

namespace OAI.PowerSaving.MX

open Finset

/-! ### polynomial against exponential, in ℕ -/

/-- `D * (t+1)^d ≤ 2^t` for all large `t`. -/
theorem poly_le_two_pow (D d : ℕ) : ∃ T, ∀ t, T ≤ t → D * (t + 1) ^ d ≤ 2 ^ t := by
  obtain ⟨c, hc⟩ : ∃ c, c = 2 * d + 2 := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X, X = D * c ^ d := ⟨_, rfl⟩
  refine ⟨2 * X + 2, fun t ht => ?_⟩
  have hc0 : 0 < c := by omega
  obtain ⟨u, hu⟩ : ∃ u, u = t / c := ⟨_, rfl⟩
  have h1 : t + 1 ≤ c * (u + 1) := by rw [hu]; exact Nat.lt_mul_div_succ t hc0
  have h2 : u * c ≤ t := by rw [hu]; exact Nat.div_mul_le_self t c
  have h3 : (u + 1) ^ d ≤ 2 ^ (u * d) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left Nat.lt_two_pow_self d
  have h4 : u * c = 2 * (u * d) + 2 * u := by rw [hc]; ring
  have h5 : (t + 1) ^ d ≤ c ^ d * 2 ^ (t / 2) := by
    calc (t + 1) ^ d ≤ (c * (u + 1)) ^ d := Nat.pow_le_pow_left h1 d
      _ = c ^ d * (u + 1) ^ d := by rw [mul_pow]
      _ ≤ c ^ d * 2 ^ (u * d) := Nat.mul_le_mul_left _ h3
      _ ≤ c ^ d * 2 ^ (t / 2) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h6 : X ≤ 2 ^ (t / 2) := by
    have h7 : X < 2 ^ X := Nat.lt_two_pow_self
    have h8 : 2 ^ X ≤ 2 ^ (t / 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  calc D * (t + 1) ^ d ≤ D * (c ^ d * 2 ^ (t / 2)) := Nat.mul_le_mul_left _ h5
    _ = X * 2 ^ (t / 2) := by rw [hX]; ring
    _ ≤ 2 ^ (t / 2) * 2 ^ (t / 2) := Nat.mul_le_mul_right _ h6
    _ = 2 ^ (t / 2 + t / 2) := by rw [pow_add]
    _ ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- `D * (t+1)^d ≤ c * 2^t` for all `t`. -/
theorem poly_le_const_two_pow (D d : ℕ) : ∃ c, ∀ t, D * (t + 1) ^ d ≤ c * 2 ^ t := by
  obtain ⟨T, hT⟩ := poly_le_two_pow D d
  refine ⟨D * (T + 1) ^ d + 1, fun t => ?_⟩
  have h1 : 1 ≤ 2 ^ t := Nat.one_le_two_pow
  by_cases ht : T ≤ t
  · calc D * (t + 1) ^ d ≤ 2 ^ t := hT t ht
      _ ≤ (D * (T + 1) ^ d + 1) * 2 ^ t := Nat.le_mul_of_pos_left _ (by omega)
  · have h2 : D * (t + 1) ^ d ≤ D * (T + 1) ^ d :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    exact le_trans h2 (le_trans (Nat.le_succ _) (Nat.le_mul_of_pos_right _ h1))

lemma cast_sum_map (s : Multiset ℕ) (f : ℕ → ℕ) :
    ((((s.map f).sum : ℕ)) : ℝ) = (s.map fun x => (f x : ℝ)).sum := by
  rw [Nat.cast_multiset_sum, Multiset.map_map]; rfl

namespace Rule

variable (R : Rule)

lemma exT_lt {n e : ℕ} (he : e ∈ R.exT n) : e < n := (R.exit_size he).2.2

lemma srcT_sub_lt {n s : ℕ} (hs : s ∈ R.srcT n) : n - s < n := by
  have h1 := R.src_pos hs; have h2 := (R.src_size hs).2; omega

/-! ### polynomial counts -/

lemma G_zero_or (x : ℕ) : R.G x = 0 ∨ R.m * R.kmin ^ R.G x ≤ x := by
  by_cases h : R.G x = 0
  · exact Or.inl h
  · exact Or.inr (Nat.findGreatest_of_ne_zero (P := fun g => R.m * R.kmin ^ g ≤ x) (n := x) rfl h)

lemma kmin_pow_G_le (x : ℕ) : R.kmin ^ R.G x ≤ x + 1 := by
  rcases R.G_zero_or x with h | h
  · rw [h]; simp
  · have h3 : R.kmin ^ R.G x ≤ R.m * R.kmin ^ R.G x :=
      Nat.le_mul_of_pos_left _ (by have := R.two_le_m; omega)
    omega

lemma kmin_pow_G_le_src {n s : ℕ} (hs : s ∈ R.srcT n) : R.kmin ^ R.G n ≤ s := by
  rcases R.G_zero_or n with h | h
  · rw [h, pow_zero]; exact R.src_pos hs
  · have h1 := (R.src_size hs).1
    have h2 : R.m * R.kmin ^ R.G n < R.m * s := lt_of_le_of_lt h h1
    exact (Nat.lt_of_mul_lt_mul_left h2).le

/-- `Q = P + W + 1`, the base of the source count -/
def Q : ℕ := R.P + R.W + 1

lemma Q_pow_G_le (x : ℕ) : R.Q ^ R.G x ≤ (x + 1) ^ R.Q := by
  have h1 : R.Q ≤ R.kmin ^ R.Q :=
    le_trans Nat.lt_two_pow_self.le (Nat.pow_le_pow_left R.two_le_kmin _)
  calc R.Q ^ R.G x ≤ (R.kmin ^ R.Q) ^ R.G x := Nat.pow_le_pow_left h1 _
    _ = (R.kmin ^ R.G x) ^ R.Q := by rw [← pow_mul, ← pow_mul, mul_comm]
    _ ≤ (x + 1) ^ R.Q := Nat.pow_le_pow_left (R.kmin_pow_G_le x) _

lemma Nsrc_poly (x : ℕ) : R.Nsrc x ≤ R.Q * (x + 1) ^ R.Q := by
  have h := R.Nsrc_le x
  calc R.Nsrc x ≤ R.Q ^ (R.G x + 1) := h
    _ = R.Q ^ R.G x * R.Q := pow_succ _ _
    _ ≤ (x + 1) ^ R.Q * R.Q := Nat.mul_le_mul_right _ (R.Q_pow_G_le x)
    _ = R.Q * (x + 1) ^ R.Q := mul_comm _ _

lemma exists_N2 : ∃ N2, ∀ n, N2 ≤ n → (R.Q + 2) * (n + 1) ^ (R.Q + 1) ≤ 2 ^ (n / R.m) := by
  obtain ⟨T, hT⟩ := poly_le_two_pow ((R.Q + 2) * R.m ^ (R.Q + 1)) (R.Q + 1)
  have hm : 0 < R.m := by have := R.two_le_m; omega
  refine ⟨R.m * T, fun n hn => ?_⟩
  have ht : T ≤ n / R.m := (Nat.le_div_iff_mul_le hm).2 (by rw [mul_comm]; exact hn)
  have h1 : n + 1 ≤ R.m * (n / R.m + 1) := Nat.lt_mul_div_succ n hm
  calc (R.Q + 2) * (n + 1) ^ (R.Q + 1) ≤ (R.Q + 2) * (R.m * (n / R.m + 1)) ^ (R.Q + 1) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 _)
    _ = (R.Q + 2) * R.m ^ (R.Q + 1) * (n / R.m + 1) ^ (R.Q + 1) := by rw [mul_pow]; ring
    _ ≤ 2 ^ (n / R.m) := hT _ ht

lemma bracket_le {N2 : ℕ} (hN2 : ∀ n, N2 ≤ n → (R.Q + 2) * (n + 1) ^ (R.Q + 1) ≤ 2 ^ (n / R.m))
    {n x y : ℕ} (hn : N2 ≤ n) (hxy : x + y = n) (hy : n ≤ R.m * y) :
    (R.Nsrc x + 1) * (x + 1) * 2 ^ x + 1 ≤ 2 ^ n := by
  have hx : x + 1 ≤ n + 1 := by omega
  have h0 : 1 ≤ (n + 1) ^ R.Q := Nat.one_le_pow _ _ (by omega)
  have h2 : R.Nsrc x + 1 ≤ (R.Q + 1) * (n + 1) ^ R.Q := by
    have := le_trans (R.Nsrc_poly x) (Nat.mul_le_mul_left R.Q (Nat.pow_le_pow_left hx R.Q))
    have e : (R.Q + 1) * (n + 1) ^ R.Q = R.Q * (n + 1) ^ R.Q + (n + 1) ^ R.Q := by ring
    omega
  have h3 : 1 ≤ (n + 1) ^ (R.Q + 1) := Nat.one_le_pow _ _ (by omega)
  have h1 : (R.Nsrc x + 1) * (x + 1) + 1 ≤ (R.Q + 2) * (n + 1) ^ (R.Q + 1) := by
    have h4 := Nat.mul_le_mul h2 hx
    have h5 : (R.Q + 1) * (n + 1) ^ R.Q * (n + 1) = (R.Q + 1) * (n + 1) ^ (R.Q + 1) := by rw [pow_succ]; ring
    have h6 : (R.Q + 2) * (n + 1) ^ (R.Q + 1) = (R.Q + 1) * (n + 1) ^ (R.Q + 1) + (n + 1) ^ (R.Q + 1) := by ring
    omega
  have h4 : 2 ^ (n / R.m) ≤ 2 ^ y := Nat.pow_le_pow_right (by norm_num) (Nat.div_le_of_le_mul hy)
  have h5 : ((R.Nsrc x + 1) * (x + 1) + 1) * 2 ^ x ≤ 2 ^ y * 2 ^ x :=
    Nat.mul_le_mul_right _ (le_trans h1 (le_trans (hN2 n hn) h4))
  have h6 : 2 ^ y * 2 ^ x = 2 ^ n := by rw [← pow_add]; congr 1; omega
  have h7 : 1 ≤ 2 ^ x := Nat.one_le_two_pow
  have h8 : ((R.Nsrc x + 1) * (x + 1) + 1) * 2 ^ x = (R.Nsrc x + 1) * (x + 1) * 2 ^ x + 2 ^ x := by ring
  omega

/-- an exit leaves at least `n/m` bits for its batch: `n ≤ m (n - e)` -/
lemma exit_room {n e : ℕ} (he : e ∈ R.exT n) : n ≤ R.m * (n - e) := by
  have hlt := R.exT_lt he
  obtain ⟨ρ', j, hej, h2, -, -⟩ := R.mem_exitsSub he
  have h5 : R.rk j < R.m := lt_of_lt_of_le (R.rk_lt_kr j (R.kmin_att.choose)) (R.kr_le _)
  have h6 : R.m * e ≤ n * (R.m - 1) := by
    rw [hej]
    calc R.m * (ρ' * R.rk j) = (R.m * ρ') * R.rk j := by ring
      _ ≤ n * R.rk j := Nat.mul_le_mul_right _ h2
      _ ≤ n * (R.m - 1) := Nat.mul_le_mul_left _ (by omega)
  have h9 : R.m * (n - e) + R.m * e = R.m * n := by rw [← mul_add, Nat.sub_add_cancel hlt.le]
  have h10 : n * (R.m - 1) + n = n * R.m := by
    rw [← mul_add_one]; congr 1; have := R.two_le_m; omega
  have h11 : R.m * n = n * R.m := mul_comm _ _
  omega

/-- the leftover term (Bill's `Rnd`): for large `n`, every bracket is at most `2^n` -/
lemma Rnd_le {N2 : ℕ} (hN2 : ∀ n, N2 ≤ n → (R.Q + 2) * (n + 1) ^ (R.Q + 1) ≤ 2 ^ (n / R.m))
    {n : ℕ} (hn : N2 ≤ n) : R.Rnd n ≤ (Multiset.card (R.exT n) + R.Nsrc n) * 2 ^ n := by
  unfold Rnd
  rw [add_mul]
  refine Nat.add_le_add ?_ ?_
  · have h := Multiset.sum_le_card_nsmul ((R.exT n).map fun e => (R.Nsrc e + 1) * (e + 1) * 2 ^ e + 1) (2 ^ n)
      (by
        intro y hy
        obtain ⟨e, he, rfl⟩ := Multiset.mem_map.1 hy
        exact R.bracket_le hN2 hn (x := e) (y := n - e) (by have := R.exT_lt he; omega) (R.exit_room he))
    rw [Multiset.card_map, smul_eq_mul] at h
    exact h
  · have h := Multiset.sum_le_card_nsmul
      ((R.srcT n).map fun s => (R.Nsrc (n - s) + 1) * (n - s + 1) * 2 ^ (n - s) + 1) (2 ^ n)
      (by
        intro y hy
        obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.1 hy
        have h1 := R.src_size hs
        exact R.bracket_le hN2 hn (x := n - s) (y := s) (by omega) h1.1.le)
    rw [Multiset.card_map, smul_eq_mul] at h
    exact h

/-! ### real estimates -/

lemma G_ge {n g : ℕ} (hn : R.m * R.kmin ^ g ≤ n) : g ≤ R.G n := by
  show g ≤ Nat.findGreatest (fun g => R.m * R.kmin ^ g ≤ n) n
  have h1 : g < 2 ^ g := Nat.lt_two_pow_self
  have h2 : 2 ^ g ≤ R.kmin ^ g := Nat.pow_le_pow_left R.two_le_kmin g
  have h3 : R.kmin ^ g ≤ R.m * R.kmin ^ g := Nat.le_mul_of_pos_left _ (by have := R.two_le_m; omega)
  exact Nat.le_findGreatest (by omega) hn

/-- **Exit decay** (lg-g2 DESIGN 3.3): above the rate exponent `z1`, the exits of the tree carry an
arbitrarily small share of the sources' Phi at `z`, for all large `n`.  This replaces the log factor. -/
theorem exits_small {z1 z η : ℝ} (h12 : z1 < z) (hz : z ≤ 1) (hz0 : 0 ≤ z) (hη : 0 < η)
    (hrate : R.RateQ z1 1) :
    ∃ N, ∀ n, N ≤ n → ((R.exT n).map (fun e : ℕ => ((e : ℝ) + 1) ^ z)).sum ≤
      η / 2 * ((R.srcT n).map (fun s : ℕ => (s : ℝ) ^ z)).sum := by
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = z - z1 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (R.rmax : ℝ) / R.kmin := ⟨_, rfl⟩
  have hk0 : (0 : ℝ) < R.kmin := by exact_mod_cast R.kmin_pos
  have hr0 : 0 ≤ r := by rw [hr]; exact div_nonneg (Nat.cast_nonneg _) hk0.le
  have hr1 : r < 1 := by rw [hr, div_lt_one hk0]; exact_mod_cast R.sep
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = (η / 4) ^ δ⁻¹ := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; exact Real.rpow_pos_of_pos (by linarith) _
  have hR1 : (0 : ℝ) < R.rmax + 1 := by positivity
  obtain ⟨g, hg⟩ := exists_pow_lt_of_lt_one (div_pos hε0 hR1) hr1
  refine ⟨R.m * R.kmin ^ g, fun n hn => ?_⟩
  have hmpos : 0 < R.m := by have := R.two_le_m; omega
  have hmn : R.m ≤ n := le_trans (Nat.le_mul_of_pos_right _ (pow_pos R.kmin_pos g)) hn
  have hG : g ≤ R.G n := R.G_ge hn
  have hm0 : (0 : ℝ) < R.m := by exact_mod_cast hmpos
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (R.rmax : ℝ) ^ (R.G n + 1) := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = (n : ℝ) / R.m := ⟨_, rfl⟩
  have hY0 : 0 < Y := by
    rw [hY]; exact div_pos (by exact_mod_cast (show 0 < n by omega)) hm0
  have hkG : (R.kmin : ℝ) ^ R.G n ≤ Y := by
    rw [hY, le_div_iff₀ hm0]
    have h := R.m_kmin_pow_G_le hmn
    have h' : R.kmin ^ R.G n * R.m ≤ n := by rw [mul_comm]; exact h
    exact_mod_cast h'
  have hkG0 : (R.kmin : ℝ) ^ R.G n ≠ 0 := by positivity
  have hEY : E ≤ ((R.rmax : ℝ) * r ^ R.G n) * Y := by
    have h : E = ((R.rmax : ℝ) * r ^ R.G n) * (R.kmin : ℝ) ^ R.G n := by
      calc E = (R.rmax : ℝ) * (R.rmax : ℝ) ^ R.G n := by rw [hE, pow_succ, mul_comm]
        _ = (R.rmax : ℝ) * (r ^ R.G n * (R.kmin : ℝ) ^ R.G n) := by
            rw [hr, div_pow, div_mul_cancel₀ _ hkG0]
        _ = ((R.rmax : ℝ) * r ^ R.G n) * (R.kmin : ℝ) ^ R.G n := by ring
    rw [h]
    exact mul_le_mul_of_nonneg_left hkG (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hr0 _))
  have hrG : (R.rmax : ℝ) * r ^ R.G n ≤ ε := by
    have h1 : r ^ R.G n ≤ r ^ g := pow_le_pow_of_le_one hr0 hr1.le hG
    have h2 : (R.rmax : ℝ) ≤ R.rmax + 1 := by linarith
    have h3 : r ^ g * ((R.rmax : ℝ) + 1) < ε := by rwa [lt_div_iff₀ hR1] at hg
    calc (R.rmax : ℝ) * r ^ R.G n ≤ ((R.rmax : ℝ) + 1) * r ^ g :=
          mul_le_mul h2 h1 (pow_nonneg hr0 _) hR1.le
      _ ≤ ε := by linarith [mul_comm (r ^ g) ((R.rmax : ℝ) + 1)]
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  have hEδ : E ^ δ ≤ η / 4 * Y ^ δ := by
    have hb0 : 0 ≤ (R.rmax : ℝ) * r ^ R.G n := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hr0 _)
    calc E ^ δ ≤ (((R.rmax : ℝ) * r ^ R.G n) * Y) ^ δ := Real.rpow_le_rpow hE0 hEY hδ0.le
      _ = ((R.rmax : ℝ) * r ^ R.G n) ^ δ * Y ^ δ := Real.mul_rpow hb0 hY0.le
      _ ≤ ε ^ δ * Y ^ δ :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hb0 hrG hδ0.le) (Real.rpow_nonneg hY0.le _)
      _ = η / 4 * Y ^ δ := by rw [hε, Real.rpow_inv_rpow (by linarith) hδ0.ne']
  -- each exit
  have hexit : ∀ e ∈ R.exT n, ((e : ℝ) + 1) ^ z ≤ 2 * E ^ δ * (e : ℝ) ^ z1 := by
    intro e he
    obtain ⟨h1, h2, -⟩ := R.exit_size he
    have he0 : (1 : ℝ) ≤ e := by exact_mod_cast h1
    have heE : (e : ℝ) ≤ E := by rw [hE]; exact_mod_cast h2
    have h2z : (2 : ℝ) ^ z ≤ 2 := by
      calc (2 : ℝ) ^ z ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hz
        _ = 2 := Real.rpow_one 2
    calc ((e : ℝ) + 1) ^ z ≤ (2 * (e : ℝ)) ^ z := Real.rpow_le_rpow (by positivity) (by linarith) hz0
      _ = 2 ^ z * (e : ℝ) ^ z := Real.mul_rpow (by norm_num) (by positivity)
      _ ≤ 2 * (e : ℝ) ^ z := mul_le_mul_of_nonneg_right h2z (by positivity)
      _ = 2 * ((e : ℝ) ^ z1 * (e : ℝ) ^ δ) := by
          rw [← Real.rpow_add (by linarith)]; congr 2; rw [hδ]; ring
      _ ≤ 2 * ((e : ℝ) ^ z1 * E ^ δ) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (by positivity) heE hδ0.le) (by positivity)) (by norm_num)
      _ = 2 * E ^ δ * (e : ℝ) ^ z1 := by ring
  -- each source
  have hsrc : ∀ s ∈ R.srcT n, Y ^ δ * (s : ℝ) ^ z1 ≤ (s : ℝ) ^ z := by
    intro s hs
    have h1 := (R.src_size hs).1
    have hsY : Y ≤ s := by
      rw [hY, div_le_iff₀ hm0]
      have h' : n ≤ s * R.m := by rw [mul_comm]; exact h1.le
      exact_mod_cast h'
    have hs0 : (0 : ℝ) < s := lt_of_lt_of_le hY0 hsY
    calc Y ^ δ * (s : ℝ) ^ z1 ≤ (s : ℝ) ^ δ * (s : ℝ) ^ z1 :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hY0.le hsY hδ0.le) (Real.rpow_nonneg hs0.le _)
      _ = (s : ℝ) ^ z := by rw [← Real.rpow_add hs0]; congr 1; rw [hδ]; ring
  -- assemble with Lemma D at z1
  have hD := R.phi_exT_le hrate n
  simp only [Phi_apply, pw] at hD
  have hA : ((R.exT n).map (fun e : ℕ => ((e : ℝ) + 1) ^ z)).sum ≤
      2 * E ^ δ * ((R.exT n).map (fun e : ℕ => (e : ℝ) ^ z1)).sum := by
    rw [← Multiset.sum_map_mul_left]
    exact Multiset.sum_map_le_sum_map _ _ hexit
  have hB : Y ^ δ * ((R.srcT n).map (fun s : ℕ => (s : ℝ) ^ z1)).sum ≤
      ((R.srcT n).map (fun s : ℕ => (s : ℝ) ^ z)).sum := by
    rw [← Multiset.sum_map_mul_left]
    exact Multiset.sum_map_le_sum_map _ _ hsrc
  have hS1 : 0 ≤ ((R.srcT n).map (fun s : ℕ => (s : ℝ) ^ z1)).sum :=
    Multiset.sum_nonneg (fun y hy => by
      obtain ⟨x, _, rfl⟩ := Multiset.mem_map.1 hy; exact Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hEd0 : 0 ≤ E ^ δ := Real.rpow_nonneg hE0 _
  calc ((R.exT n).map (fun e : ℕ => ((e : ℝ) + 1) ^ z)).sum
      ≤ 2 * E ^ δ * ((R.exT n).map (fun e : ℕ => (e : ℝ) ^ z1)).sum := hA
    _ ≤ 2 * E ^ δ * ((R.srcT n).map (fun s : ℕ => (s : ℝ) ^ z1)).sum :=
        mul_le_mul_of_nonneg_left hD (by linarith)
    _ ≤ 2 * (η / 4 * Y ^ δ) * ((R.srcT n).map (fun s : ℕ => (s : ℝ) ^ z1)).sum :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hEδ (by norm_num)) hS1
    _ = η / 2 * (Y ^ δ * ((R.srcT n).map (fun s : ℕ => (s : ℝ) ^ z1)).sum) := by ring
    _ ≤ η / 2 * ((R.srcT n).map (fun s : ℕ => (s : ℝ) ^ z)).sum :=
        mul_le_mul_of_nonneg_left hB (by linarith)

/-- the source copies: `G n + 1 ≤ c s^z` for every source `s` of the tree for `n` -/
lemma G_succ_le {z : ℝ} (hz : 0 < z) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ n s, s ∈ R.srcT n → ((R.G n : ℝ) + 1) ≤ c * (s : ℝ) ^ z := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpos : 0 < z * Real.log 2 := mul_pos hz hl
  refine ⟨1 / (z * Real.log 2) + 1, by positivity, fun n s hs => ?_⟩
  have hG2 : (R.G n : ℝ) * (z * Real.log 2) + 1 ≤ (2 : ℝ) ^ ((R.G n : ℝ) * z) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    have := Real.add_one_le_exp (Real.log 2 * ((R.G n : ℝ) * z))
    have e : Real.log 2 * ((R.G n : ℝ) * z) = (R.G n : ℝ) * (z * Real.log 2) := by ring
    linarith
  have h2s : (2 : ℝ) ^ ((R.G n : ℝ) * z) ≤ (s : ℝ) ^ z := by
    rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
    apply Real.rpow_le_rpow (by positivity) _ hz.le
    have : 2 ^ R.G n ≤ s := le_trans (Nat.pow_le_pow_left R.two_le_kmin _) (R.kmin_pow_G_le_src hs)
    exact_mod_cast this
  have h1le : 1 ≤ (2 : ℝ) ^ ((R.G n : ℝ) * z) := Real.one_le_rpow (by norm_num) (by positivity)
  have hGle : (R.G n : ℝ) ≤ (2 : ℝ) ^ ((R.G n : ℝ) * z) / (z * Real.log 2) := by
    rw [le_div_iff₀ hpos]; linarith
  calc (R.G n : ℝ) + 1 ≤ (2 : ℝ) ^ ((R.G n : ℝ) * z) / (z * Real.log 2) + (2 : ℝ) ^ ((R.G n : ℝ) * z) := by
        linarith
    _ = (1 / (z * Real.log 2) + 1) * (2 : ℝ) ^ ((R.G n : ℝ) * z) := by ring
    _ ≤ (1 / (z * Real.log 2) + 1) * (s : ℝ) ^ z := mul_le_mul_of_nonneg_left h2s (by positivity)

/-- `treeCost` per entry, as a real number -/
lemma treeCost_real (J : ℕ → ℕ) (n : ℕ) :
    ((R.treeCost J n : ℕ) : ℝ) = (((2 * R.unitsT n + R.Nsrc n * (R.G n + 1) : ℕ) : ℝ)
      + ((R.exT n).map (fun e => (J e : ℝ) / 2 ^ e)).sum
      + ((R.srcT n).map (fun s => (J (n - s) : ℝ) / 2 ^ (n - s))).sum) * 2 ^ n := by
  have hex : ((((R.exT n).map fun e => 2 ^ (n - e) * J e).sum : ℕ) : ℝ) =
      ((R.exT n).map (fun e => (J e : ℝ) / 2 ^ e)).sum * 2 ^ n := by
    rw [cast_sum_map, ← Multiset.sum_map_mul_right]
    congr 1
    refine Multiset.map_congr rfl (fun e he => ?_)
    have hle : e ≤ n := (R.exT_lt he).le
    have h2 : (2 : ℝ) ^ n = 2 ^ (n - e) * 2 ^ e := by rw [← pow_add, Nat.sub_add_cancel hle]
    have h3 : (2 : ℝ) ^ e ≠ 0 := by positivity
    rw [h2]; push_cast; field_simp
  have hsr : ((((R.srcT n).map fun s => 2 ^ s * J (n - s)).sum : ℕ) : ℝ) =
      ((R.srcT n).map (fun s => (J (n - s) : ℝ) / 2 ^ (n - s))).sum * 2 ^ n := by
    rw [cast_sum_map, ← Multiset.sum_map_mul_right]
    congr 1
    refine Multiset.map_congr rfl (fun s hs => ?_)
    have hle : s ≤ n := (R.src_size hs).2
    have h2 : (2 : ℝ) ^ n = 2 ^ s * 2 ^ (n - s) := by rw [← pow_add, Nat.add_sub_cancel' hle]
    have h3 : (2 : ℝ) ^ (n - s) ≠ 0 := by positivity
    rw [h2]; push_cast; field_simp
  unfold treeCost
  rw [Nat.cast_add, Nat.cast_add, hex, hsr, Nat.cast_mul (2 * R.unitsT n + R.Nsrc n * (R.G n + 1)) (2 ^ n),
    Nat.cast_pow, Nat.cast_ofNat]
  ring

/-- **R2, the cost bound.** If the rate fact holds at `z1 > 0`, then for every `z ∈ (z1, 1]` and every
threshold `n0` the per-vector cost of the mixed recursion is `O(2^n (n+1)^z)`. -/
theorem allotM_bound {z1 z : ℝ} (hrate : R.RateQ z1 1) (hz1 : 0 < z1) (h12 : z1 < z) (hz : z ≤ 1)
    {n0 : ℕ} (hn0 : R.m ≤ n0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, (R.allotM n0 n : ℝ) ≤ C * 2 ^ n * ((n : ℝ) + 1) ^ z := by
  have hz0 : 0 < z := by linarith
  have hm1 : 1 ≤ R.m := by have := R.two_le_m; omega
  have hmR : (0 : ℝ) < R.m := by exact_mod_cast hm1
  have hmR1 : (1 : ℝ) ≤ R.m := by exact_mod_cast hm1
  have hη : 0 < z / (R.m : ℝ) := div_pos hz0 hmR
  have hη1 : z / (R.m : ℝ) ≤ 1 := by rw [div_le_one hmR]; linarith
  obtain ⟨N1, hN1⟩ := R.exits_small h12 hz hz0.le hη hrate
  obtain ⟨N2, hN2⟩ := R.exists_N2
  obtain ⟨cG, hcG0, hcG⟩ := R.G_succ_le hz0
  -- the unit count (Lemma E) at z, with the strict rate factor q
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = ((R.rmax : ℝ) / R.kmin) ^ (z - z1) := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by
    rw [hq]; exact Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _
  have hq1 : q < 1 := by rw [hq]; exact R.rate_factor_lt_one (by linarith)
  have hrq : R.RateQ z q := by rw [hq]; exact R.rate_mono hrate h12.le
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = 1 / (1 - q) := ⟨_, rfl⟩
  have h1q : 0 < 1 - q := by linarith
  have hα0 : 0 ≤ α := by rw [hα]; positivity
  have hα1 : 1 ≤ α * (1 - q) := by rw [hα, one_div, inv_mul_cancel₀ h1q.ne']
  have hunits := R.units_le hz0.le hq0 hrq hα0 hα1
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 2 * α + cG + 3 := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; linarith
  obtain ⟨n1, hn1⟩ : ∃ n1, n1 = max (max n0 R.m) (max N1 N2) := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : ℕ → ℝ, t = fun n => (R.allotM n0 n : ℝ) / 2 ^ n := ⟨_, rfl⟩
  obtain ⟨I, hI⟩ : ∃ I : ℕ → ℝ, I = fun n => ((2 * R.unitsT n + R.Nsrc n * (R.G n + 1) : ℕ) : ℝ)
      + ((R.Rnd n + R.Nsrc n : ℕ) : ℝ) / 2 ^ n := ⟨_, rfl⟩
  have hNn : ∀ n, n1 ≤ n → R.srcT n ≠ 0 := by
    intro n hn
    have h := R.Nsrc_pos (n := n) (by rw [hn1] at hn; omega)
    exact Multiset.card_pos.1 (by unfold Nsrc at h; omega)
  have hrec : ∀ n, n1 ≤ n → (Multiset.card (R.srcT n) : ℝ) * t n ≤
      I n + ((R.exT n).map t).sum + ((R.srcT n).map (fun s => t (n - s))).sum := by
    intro n hn
    have hnn0 : n0 ≤ n := by rw [hn1] at hn; omega
    have hle := (R.allotM_upper hn0).2 n hnn0
    have hleR : ((R.Nsrc n * R.allotM n0 n : ℕ) : ℝ) ≤
        ((R.treeCost (R.allotM n0) n + R.Rnd n + R.Nsrc n : ℕ) : ℝ) := by exact_mod_cast hle
    rw [Nat.cast_add, Nat.cast_add, R.treeCost_real, Nat.cast_mul] at hleR
    have h2 : (0 : ℝ) < 2 ^ n := by positivity
    simp only [ht, hI]
    rw [show (Multiset.card (R.srcT n) : ℝ) = (R.Nsrc n : ℝ) from rfl, mul_div_assoc', div_le_iff₀ h2]
    have hx : (((2 * R.unitsT n + R.Nsrc n * (R.G n + 1) : ℕ) : ℝ) + ((R.Rnd n + R.Nsrc n : ℕ) : ℝ) / 2 ^ n
        + ((R.exT n).map (fun e => (R.allotM n0 e : ℝ) / 2 ^ e)).sum
        + ((R.srcT n).map (fun s => (R.allotM n0 (n - s) : ℝ) / 2 ^ (n - s))).sum) * 2 ^ n =
        (((2 * R.unitsT n + R.Nsrc n * (R.G n + 1) : ℕ) : ℝ)
        + ((R.exT n).map (fun e => (R.allotM n0 e : ℝ) / 2 ^ e)).sum
        + ((R.srcT n).map (fun s => (R.allotM n0 (n - s) : ℝ) / 2 ^ (n - s))).sum) * 2 ^ n
        + ((R.Rnd n : ℝ) + (R.Nsrc n : ℝ)) := by
      push_cast; field_simp; ring
    rw [hx]
    linarith
  have hsrc : ∀ n, n1 ≤ n → ∀ s ∈ R.srcT n, 1 ≤ s ∧ s ≤ n ∧
      (((n - s : ℕ) : ℝ) + 1) ^ z ≤ ((n : ℝ) + 1) ^ z - z / (R.m : ℝ) * (s : ℝ) ^ z := by
    intro n _ s hs
    have h1 := R.src_size hs
    exact ⟨R.src_pos hs, h1.2, eta_step hm1 hz0.le hz h1.1 h1.2⟩
  have hex : ∀ n, n1 ≤ n → ∀ e ∈ R.exT n, e < n := fun n _ e he => R.exT_lt he
  have hexPhi : ∀ n, n1 ≤ n → ((R.exT n).map (fun e : ℕ => ((e : ℝ) + 1) ^ z)).sum ≤
      z / (R.m : ℝ) / 2 * ((R.srcT n).map (fun s : ℕ => (s : ℝ) ^ z)).sum := by
    intro n hn
    exact hN1 n (by rw [hn1] at hn; omega)
  have hIb : ∀ n, n1 ≤ n → I n ≤ A * ((R.srcT n).map (fun s : ℕ => (s : ℝ) ^ z)).sum := by
    intro n hn
    have hnN1 : N1 ≤ n := by rw [hn1] at hn; omega
    have hnN2 : N2 ≤ n := by rw [hn1] at hn; omega
    obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℝ, Φ = ((R.srcT n).map (fun s : ℕ => (s : ℝ) ^ z)).sum := ⟨_, rfl⟩
    rw [← hΦ]
    -- units
    have hU : (R.unitsT n : ℝ) ≤ α * Φ := by
      have h := hunits n
      rw [hΦ]; exact h
    -- card of sources
    have hNs : (R.Nsrc n : ℝ) ≤ Φ := by
      rw [hΦ]
      have h : ((R.srcT n).map (fun _ : ℕ => (1 : ℝ))).sum ≤ ((R.srcT n).map (fun s : ℕ => (s : ℝ) ^ z)).sum :=
        Multiset.sum_map_le_sum_map _ _ (fun s hs => Real.one_le_rpow (by exact_mod_cast R.src_pos hs) hz0.le)
      rw [Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul, mul_one] at h
      exact h
    -- source copies
    have hGs : (R.Nsrc n : ℝ) * ((R.G n : ℝ) + 1) ≤ cG * Φ := by
      rw [hΦ]
      have h : ((R.srcT n).map (fun _ : ℕ => (R.G n : ℝ) + 1)).sum ≤
          ((R.srcT n).map (fun s : ℕ => cG * (s : ℝ) ^ z)).sum :=
        Multiset.sum_map_le_sum_map _ _ (fun s hs => hcG n s hs)
      rw [Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul, Multiset.sum_map_mul_left] at h
      exact h
    -- exits count
    have hEx : (Multiset.card (R.exT n) : ℝ) ≤ Φ := by
      have h1 : ((R.exT n).map (fun _ : ℕ => (1 : ℝ))).sum ≤ ((R.exT n).map (fun e : ℕ => ((e : ℝ) + 1) ^ z)).sum :=
        Multiset.sum_map_le_sum_map _ _ (fun e _ => Real.one_le_rpow (by linarith [(Nat.cast_nonneg e : (0:ℝ) ≤ e)]) hz0.le)
      rw [Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul, mul_one] at h1
      have h2 := hN1 n hnN1
      rw [← hΦ] at h2
      have hΦ0 : 0 ≤ Φ := le_trans (Nat.cast_nonneg _) hNs
      nlinarith
    -- leftovers
    have hR : ((R.Rnd n + R.Nsrc n : ℕ) : ℝ) / 2 ^ n ≤ (Multiset.card (R.exT n) : ℝ) + 2 * (R.Nsrc n : ℝ) := by
      have h := R.Rnd_le hN2 hnN2
      have h2 : (0 : ℝ) < 2 ^ n := by positivity
      have h1 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      rw [div_le_iff₀ h2]
      have hR' : (R.Rnd n : ℝ) ≤ ((Multiset.card (R.exT n) : ℝ) + (R.Nsrc n : ℝ)) * 2 ^ n := by
        exact_mod_cast h
      push_cast
      nlinarith [(Nat.cast_nonneg (R.Nsrc n) : (0:ℝ) ≤ R.Nsrc n)]
    simp only [hI]
    push_cast at hR ⊢
    rw [hA]
    linarith
  have hL := lemmaA t R.srcT R.exT I n1 hz0.le hA0 hη hNn hrec hsrc hex hexPhi hIb
  obtain ⟨C, hC0, hC⟩ := hL
  refine ⟨C, hC0, fun n => ?_⟩
  have h := hC n
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [ht] at h
  simp only at h
  rw [div_le_iff₀ h2] at h
  linarith

/-- the same bound in the form the task names: for every `z' > z1` (in particular every rational
`z' > tau_c` when the rate fact holds at some `z1 ∈ (tau_c, z')`), with `z' ≤ 1`. -/
theorem allotM_envelope {z1 : ℝ} (hrate : R.RateQ z1 1) (hz1 : 0 < z1) {n0 : ℕ} (hn0 : R.m ≤ n0) :
    ∀ z' : ℝ, z1 < z' → z' ≤ 1 → ∃ A : ℝ, 0 ≤ A ∧ ∀ k, (R.allotM n0 k : ℝ) ≤ A * 2 ^ k * ((k : ℝ) + 1) ^ z' :=
  fun _ h12 hz => R.allotM_bound hrate hz1 h12 hz hn0

/-! ### bridges for the rate fact (R5 / integration) -/

/-- the rate fact with ranks normalised by `m` (the `BlockAccounting.moment` shape) gives `RateQ z 1` -/
theorem rateQ_of_normalized {z : ℝ}
    (h : ∑ j, ((R.rk j : ℝ) / R.m) ^ z ≤ ∑ k, (R.Wk k : ℝ) * ((R.kr k : ℝ) / R.m) ^ z) : R.RateQ z 1 := by
  unfold RateQ
  have hm0 : (0 : ℝ) < R.m := by exact_mod_cast (show 0 < R.m by have := R.two_le_m; omega)
  have hmz : 0 < (R.m : ℝ) ^ z := Real.rpow_pos_of_pos hm0 z
  have e1 : ∑ j, ((R.rk j : ℝ) / R.m) ^ z = (∑ j, (R.rk j : ℝ) ^ z) * ((R.m : ℝ) ^ z)⁻¹ := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun j _ => by rw [Real.div_rpow (Nat.cast_nonneg _) hm0.le, div_eq_mul_inv])
  have e2 : ∑ k, (R.Wk k : ℝ) * ((R.kr k : ℝ) / R.m) ^ z =
      (∑ k, (R.Wk k : ℝ) * (R.kr k : ℝ) ^ z) * ((R.m : ℝ) ^ z)⁻¹ := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Real.div_rpow (Nat.cast_nonneg _) hm0.le, div_eq_mul_inv, mul_assoc]
  rw [e1, e2] at h
  have h' := le_of_mul_le_mul_right h (inv_pos.2 hmz)
  linarith

/-- the left side of the rate fact by histogram of the paid ranks -/
theorem sum_rk_hist (f : ℕ → ℝ) :
    ∑ j, f (R.rk j) = ∑ r ∈ Finset.range (R.rmax + 1),
      ((Finset.univ.filter fun j => R.rk j = r).card : ℝ) * f r := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.range (R.rmax + 1)) (g := R.rk)
    (fun j _ => Finset.mem_range.2 (Nat.lt_succ_of_le (R.rk_le j)))]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Finset.sum_congr rfl (fun j hj => by rw [(Finset.mem_filter.1 hj).2]), Finset.sum_const, nsmul_eq_mul]

end Rule

end OAI.PowerSaving.MX
