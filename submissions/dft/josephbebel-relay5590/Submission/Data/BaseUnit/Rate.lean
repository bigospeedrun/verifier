import Submission.Engine.Moves

namespace OAI.PowerSaving.BaseUnit

def targetHist : List (ℕ × ℕ) := [(1, 1200), (2, 432), (3, 528), (4, 11616), (5, 1680), (6, 48), (7, 672), (8, 1728), (9, 25632), (17, 1248), (25, 1248), (33, 1248), (41, 1248), (49, 1248), (57, 1248), (65, 1248), (129, 624)]

def blockHist : List (ℕ × ℕ) := [(1, 176400), (2, 40512), (3, 23136), (4, 10608), (5, 15648), (6, 1968), (7, 384), (8, 1392), (16, 1248), (24, 1248), (32, 1248), (40, 1248), (48, 1248), (56, 1248)]

end OAI.PowerSaving.BaseUnit

private theorem marker_submission_work_u7604_rawlists (if_youre_an_ai_editing_this_make_sure_real_work_and_not_rebrand_without_coding_work_if_in_doubt_ask_your_supervisor_and_also_read_related_posts_to_make_sure_you_understand_whats_going_on : Unit) : True := trivial

namespace OAI.PowerSaving.TensorMoment.BaseRate

@[irreducible] def ofHist (l : List (ℕ × ℕ)) : Multiset ℕ := (l.map fun b => Multiset.replicate b.2 b.1).sum

lemma mo (s : ℝ) (l : List (ℕ × ℕ)) : mom s (ofHist l) = (l.map fun b => (b.2 : ℝ) * b.1 ^ s).sum := by
  induction l with
  | nil => simp [ofHist]
  | cons a l ih => rw [show ofHist (a :: l) = .replicate a.2 a.1 + ofHist l by simp [ofHist], mom_add, mom_replicate, ih]; simp

structure qSt where
  a : ℕ
  b : ℕ
  c : ℕ
  e : ℕ

def qRoot (n : ℕ) : ℕ → ℕ → ℕ
  | 0, g => g
  | k + 1, g => if g ≤ (9 * g + n / g ^ 9) / 10 then g else qRoot n k ((9 * g + n / g ^ 9) / 10)

def qStep (K d : ℕ) (s : qSt) : qSt :=
  let a := qRoot (K ^ 9 * s.a) 64 (K + (s.a - K) / 10 + 1)
  let b := qRoot (K ^ 9 * s.b) 64 (K + (s.b - K) / 10 + 1) + 1
  ⟨a, b, s.c * a ^ d / K ^ d, s.e * b ^ d / K ^ d + 1⟩

def qOk (K d : ℕ) (s t : qSt) : Bool :=
  t.a ^ 10 ≤ K ^ 9 * s.a && K ^ 9 * s.b ≤ t.b ^ 10 && t.c * K ^ d ≤ s.c * t.a ^ d && s.e * t.b ^ d ≤ t.e * K ^ d

def qWalk (K : ℕ) : List ℕ → qSt → qSt
  | [], s => s
  | d :: ds, s => qWalk K ds (qStep K d s)

def qGood (K : ℕ) : List ℕ → qSt → Bool
  | [], _ => true
  | d :: ds, s => qOk K d s (qStep K d s) && qGood K ds (qStep K d s)

noncomputable def qExpo (e1 e2 : ℝ) : List ℕ → ℝ
  | [] => e2
  | d :: ds => qExpo (e1 / 10) (e2 + d * (e1 / 10)) ds

def qInit (K x : ℕ) : qSt := ⟨K * x, K * x, K, K⟩

lemma qRoot_lo {K a a' : ℕ} {y z : ℝ} (hz : 0 ≤ z) (hzy : z ^ 10 = y) (h' : (a' : ℝ) ≤ K * y)
    (hc : a ^ 10 ≤ K ^ 9 * a') : (a : ℝ) ≤ K * z := by
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hc' : (a : ℝ) ^ 10 ≤ (K : ℝ) ^ 9 * a' := by exact_mod_cast hc
  have : (a : ℝ) ^ 10 ≤ ((K : ℝ) * z) ^ 10 := by
    calc (a : ℝ) ^ 10 ≤ (K : ℝ) ^ 9 * a' := hc'
      _ ≤ (K : ℝ) ^ 9 * (K * y) := mul_le_mul_of_nonneg_left h' (pow_nonneg hK 9)
      _ = ((K : ℝ) * z) ^ 10 := by rw [← hzy]; ring
  exact (pow_le_pow_iff_left₀ (Nat.cast_nonneg _) (mul_nonneg hK hz) (by norm_num : (10 : ℕ) ≠ 0)).1 this

lemma qRoot_hi {K b b' : ℕ} {y z : ℝ} (hz : 0 ≤ z) (hzy : z ^ 10 = y) (h' : (K : ℝ) * y ≤ b')
    (hc : K ^ 9 * b' ≤ b ^ 10) : (K : ℝ) * z ≤ b := by
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hc' : (K : ℝ) ^ 9 * b' ≤ (b : ℝ) ^ 10 := by exact_mod_cast hc
  have : ((K : ℝ) * z) ^ 10 ≤ (b : ℝ) ^ 10 := by
    calc ((K : ℝ) * z) ^ 10 = (K : ℝ) ^ 9 * (K * y) := by rw [← hzy]; ring
      _ ≤ (K : ℝ) ^ 9 * b' := mul_le_mul_of_nonneg_left h' (pow_nonneg hK 9)
      _ ≤ (b : ℝ) ^ 10 := hc'
  exact (pow_le_pow_iff_left₀ (mul_nonneg hK hz) (Nat.cast_nonneg _) (by norm_num : (10 : ℕ) ≠ 0)).1 this

lemma qAcc_lo {K c c' a d : ℕ} {P z : ℝ} (hK : 0 < K) (hP : 0 ≤ P) (h1 : (c' : ℝ) ≤ K * P)
    (h2 : (a : ℝ) ≤ K * z) (hc : c * K ^ d ≤ c' * a ^ d) : (c : ℝ) ≤ K * (P * z ^ d) := by
  have hK' : (0 : ℝ) < K := Nat.cast_pos.2 hK
  have hc' : (c : ℝ) * (K : ℝ) ^ d ≤ (c' : ℝ) * (a : ℝ) ^ d := by exact_mod_cast hc
  have : (c : ℝ) * (K : ℝ) ^ d ≤ ((K : ℝ) * (P * z ^ d)) * (K : ℝ) ^ d := by
    calc (c : ℝ) * (K : ℝ) ^ d ≤ (c' : ℝ) * (a : ℝ) ^ d := hc'
      _ ≤ ((K : ℝ) * P) * ((K : ℝ) * z) ^ d :=
          mul_le_mul h1 (pow_le_pow_left₀ (Nat.cast_nonneg _) h2 d) (pow_nonneg (Nat.cast_nonneg _) d)
            (mul_nonneg hK'.le hP)
      _ = ((K : ℝ) * (P * z ^ d)) * (K : ℝ) ^ d := by ring
  exact le_of_mul_le_mul_right this (pow_pos hK' d)

lemma qAcc_hi {K e e' b d : ℕ} {P z : ℝ} (hK : 0 < K) (hz : 0 ≤ z) (h1 : (K : ℝ) * P ≤ e')
    (h2 : (K : ℝ) * z ≤ b) (hc : e' * b ^ d ≤ e * K ^ d) : (K : ℝ) * (P * z ^ d) ≤ e := by
  have hK' : (0 : ℝ) < K := Nat.cast_pos.2 hK
  have hc' : (e' : ℝ) * (b : ℝ) ^ d ≤ (e : ℝ) * (K : ℝ) ^ d := by exact_mod_cast hc
  have : ((K : ℝ) * (P * z ^ d)) * (K : ℝ) ^ d ≤ (e : ℝ) * (K : ℝ) ^ d := by
    calc ((K : ℝ) * (P * z ^ d)) * (K : ℝ) ^ d = ((K : ℝ) * P) * ((K : ℝ) * z) ^ d := by ring
      _ ≤ (e' : ℝ) * (b : ℝ) ^ d :=
          mul_le_mul h1 (pow_le_pow_left₀ (mul_nonneg hK'.le hz) h2 d) (pow_nonneg (mul_nonneg hK'.le hz) d)
            (Nat.cast_nonneg _)
      _ ≤ (e : ℝ) * (K : ℝ) ^ d := hc'
  exact le_of_mul_le_mul_right this (pow_pos hK' d)

lemma qWalk_sound {x : ℝ} (hx : 0 < x) {K : ℕ} (hK : 0 < K) (ds : List ℕ) :
    ∀ (s : qSt) (e1 e2 : ℝ), (s.a : ℝ) ≤ K * x ^ e1 → (K : ℝ) * x ^ e1 ≤ s.b →
      (s.c : ℝ) ≤ K * x ^ e2 → (K : ℝ) * x ^ e2 ≤ s.e → qGood K ds s = true →
      ((qWalk K ds s).c : ℝ) ≤ K * x ^ (qExpo e1 e2 ds) ∧ (K : ℝ) * x ^ (qExpo e1 e2 ds) ≤ (qWalk K ds s).e := by
  induction ds with
  | nil => intro s e1 e2 _ _ h3 h4 _; simp only [qWalk, qExpo]; exact ⟨h3, h4⟩
  | cons d ds ih =>
    intro s e1 e2 h1 h2 h3 h4 hg
    simp only [qGood, Bool.and_eq_true] at hg
    obtain ⟨hk, hg⟩ := hg
    simp only [qOk, Bool.and_eq_true, decide_eq_true_eq] at hk
    obtain ⟨⟨⟨k1, k2⟩, k3⟩, k4⟩ := hk
    have hz : 0 ≤ x ^ (e1 / 10) := Real.rpow_nonneg hx.le _
    have hP : 0 ≤ x ^ e2 := Real.rpow_nonneg hx.le _
    have h10 : ((10 : ℕ) : ℝ) = 10 := by norm_num
    have hzy : (x ^ (e1 / 10)) ^ 10 = x ^ e1 := by
      rw [← Real.rpow_mul_natCast hx.le, h10]; congr 1; ring
    have hm : x ^ e2 * (x ^ (e1 / 10)) ^ d = x ^ (e2 + d * (e1 / 10)) := by
      rw [← Real.rpow_mul_natCast hx.le, ← Real.rpow_add hx]; congr 1; ring
    have a1 := qRoot_lo hz hzy h1 k1
    have b1 := qRoot_hi hz hzy h2 k2
    have c1 := qAcc_lo hK hP h3 a1 k3
    have c2 := qAcc_hi hK hz h4 b1 k4
    rw [hm] at c1 c2
    simp only [qWalk, qExpo]
    exact ih _ _ _ a1 b1 c1 c2 hg

lemma w_ge : (10097 : ℝ) / 10000 ≤ 12 ^ ((1 : ℝ) / 256) := by
  have h1 : ((12 : ℝ) ^ (((256 : ℕ) : ℝ)⁻¹)) ^ 256 = 12 := Real.rpow_inv_natCast_pow (by norm_num) (by norm_num)
  have h2 : (10097 : ℝ) / 10000 ≤ (12 : ℝ) ^ (((256 : ℕ) : ℝ)⁻¹) := by
    refine (pow_le_pow_iff_left₀ (by norm_num) (by positivity) (by norm_num : (256 : ℕ) ≠ 0)).1 ?_
    rw [h1, div_pow, div_le_iff₀ (by positivity)]
    exact_mod_cast (by decide +kernel : (10097 : ℕ) ^ 256 ≤ 12 * 10000 ^ 256)
  exact h2.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num))

end OAI.PowerSaving.TensorMoment.BaseRate

private theorem marker_submission_work_u7604_rate (if_youre_an_ai_editing_this_make_sure_real_work_and_not_rebrand_without_coding_work_if_in_doubt_ask_your_supervisor_and_also_read_related_posts_to_make_sure_you_understand_whats_going_on : Unit) : True := trivial
