import Submission.Engine.Moves

namespace OAI.PowerSaving.BaseUnit

def targetHist : List (ℕ × ℕ) := [(1, 1008), (2, 432), (3, 480), (4, 11568), (5, 1584), (6, 48), (7, 672), (8, 1584), (9, 25872), (17, 1248), (25, 1248), (33, 1248), (41, 1248), (49, 1248), (57, 1248), (65, 1248), (129, 624)]

def blockHist : List (ℕ × ℕ) := [(1, 177168), (2, 40704), (3, 23232), (4, 10656), (5, 15264), (6, 1968), (7, 480), (8, 1344), (16, 1248), (24, 1248), (32, 1248), (40, 1248), (48, 1248), (56, 1248)]

end OAI.PowerSaving.BaseUnit

private theorem marker_submission_work_u7604_rawlists (if_youre_an_ai_editing_this_make_sure_real_work_and_not_rebrand_without_coding_work_if_in_doubt_ask_your_supervisor_and_also_read_related_posts_to_make_sure_you_understand_whats_going_on : Unit) : True := trivial

namespace OAI.PowerSaving.TensorMoment.BaseRate

@[irreducible] def ofHist (l : List (ℕ × ℕ)) : Multiset ℕ := (l.map fun b => Multiset.replicate b.2 b.1).sum

def Kc : ℕ := 10 ^ 26
def Kf : ℕ := 10 ^ 18

def f (r : ℕ) : ℕ := ([(1, 999999999999999999), (2, 1994577041222669791), (3, 2987117449089133709), (4, 3978337573372579789), (5, 4968577099621255733), (6, 5958035883388813279), (7, 6946845873052483999), (8, 7935100786082456185), (9, 8922870654652773318), (16, 15827169847708026679), (17, 16812374957022750076), (24, 23703078018387806193), (25, 24686758394880769824), (32, 31568509605770129099), (33, 32551101674818442596), (40, 39426160048915916591), (41, 40407905418993310650), (48, 47277615221786053512), (49, 48258667583946328634), (56, 55123922148052432414), (57, 56104387941220772818), (65, 63945781804474856587), (129, 126567502923382823695)].lookup r).getD 0

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

def qDig : List ℕ := [0, 0, 3, 9, 1, 7, 1, 5, 0, 9, 0, 7, 6, 8, 0, 4, 3, 5]

def qInit (K x : ℕ) : qSt := ⟨K * x, K * x, K, K⟩

def qCert (r : ℕ) : Bool :=
  1 ≤ r && qGood Kc qDig (qInit Kc r) && f r * (qWalk Kc qDig (qInit Kc r)).e ≤ Kf * Kc * r &&
    Kf * Kc * r ≤ (f r + 1) * (qWalk Kc qDig (qInit Kc r)).c

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

lemma qExpo_eq : qExpo 1 0 qDig = (3917150907680435 : ℝ) / 1000000000000000000 := by norm_num [qExpo, qDig]

lemma rank_bnd (r : ℕ) (h : qCert r = true) :
    ((f r : ℕ) : ℝ) ≤ (Kf : ℝ) * (r : ℝ) ^ (1 - (3917150907680435 : ℝ) / 1000000000000000000) ∧
    (Kf : ℝ) * (r : ℝ) ^ (1 - (3917150907680435 : ℝ) / 1000000000000000000) ≤ ((f r + 1 : ℕ) : ℝ) := by
  simp only [qCert, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, hg⟩, hlo⟩, hhi⟩ := h
  have hx : (0 : ℝ) < r := Nat.cast_pos.2 h1
  have hK : 0 < Kc := by unfold Kc; positivity
  have hKc : (0 : ℝ) < Kc := Nat.cast_pos.2 hK
  obtain ⟨w1, w2⟩ := qWalk_sound hx hK qDig (qInit Kc r) 1 0 (by simp [qInit]) (by simp [qInit])
    (by simp [qInit]) (by simp [qInit]) hg
  rw [qExpo_eq] at w1 w2
  set W := qWalk Kc qDig (qInit Kc r) with hW
  have hy : 0 < (r : ℝ) ^ ((3917150907680435 : ℝ) / 1000000000000000000) := Real.rpow_pos_of_pos hx _
  have q2 : ((f r : ℕ) : ℝ) * W.e ≤ (Kf : ℝ) * Kc * r := by exact_mod_cast hlo
  have q3 : (Kf : ℝ) * Kc * r ≤ ((f r + 1 : ℕ) : ℝ) * W.c := by exact_mod_cast hhi
  rw [Real.rpow_sub hx, Real.rpow_one]
  constructor
  · rw [mul_div_assoc', le_div_iff₀ hy]
    have q1 : ((f r : ℕ) : ℝ) * (Kc * (r : ℝ) ^ ((3917150907680435 : ℝ) / 1000000000000000000)) ≤ ((f r : ℕ) : ℝ) * W.e :=
      mul_le_mul_of_nonneg_left w2 (Nat.cast_nonneg _)
    have : (Kc : ℝ) * (((f r : ℕ) : ℝ) * (r : ℝ) ^ ((3917150907680435 : ℝ) / 1000000000000000000)) ≤ (Kc : ℝ) * ((Kf : ℝ) * r) :=
      calc (Kc : ℝ) * (((f r : ℕ) : ℝ) * (r : ℝ) ^ ((3917150907680435 : ℝ) / 1000000000000000000))
          = ((f r : ℕ) : ℝ) * (Kc * (r : ℝ) ^ ((3917150907680435 : ℝ) / 1000000000000000000)) := by ring
        _ ≤ ((f r : ℕ) : ℝ) * W.e := q1
        _ ≤ (Kf : ℝ) * Kc * r := q2
        _ = (Kc : ℝ) * ((Kf : ℝ) * r) := by ring
    exact le_of_mul_le_mul_left this hKc
  · rw [mul_div_assoc', div_le_iff₀ hy]
    have q1 : ((f r + 1 : ℕ) : ℝ) * W.c ≤ ((f r + 1 : ℕ) : ℝ) * (Kc * (r : ℝ) ^ ((3917150907680435 : ℝ) / 1000000000000000000)) :=
      mul_le_mul_of_nonneg_left w1 (Nat.cast_nonneg _)
    have : (Kc : ℝ) * ((Kf : ℝ) * r) ≤ (Kc : ℝ) * (((f r + 1 : ℕ) : ℝ) * (r : ℝ) ^ ((3917150907680435 : ℝ) / 1000000000000000000)) :=
      calc (Kc : ℝ) * ((Kf : ℝ) * r) = (Kf : ℝ) * Kc * r := by ring
        _ ≤ ((f r + 1 : ℕ) : ℝ) * W.c := q3
        _ ≤ ((f r + 1 : ℕ) : ℝ) * (Kc * (r : ℝ) ^ ((3917150907680435 : ℝ) / 1000000000000000000)) := q1
        _ = (Kc : ℝ) * (((f r + 1 : ℕ) : ℝ) * (r : ℝ) ^ ((3917150907680435 : ℝ) / 1000000000000000000)) := by ring
    exact le_of_mul_le_mul_left this hKc

lemma bnd (l : List (ℕ × ℕ)) (h : ∀ b ∈ l, qCert b.1 = true) :
    (((l.map fun b => b.2 * f b.1).sum : ℕ) : ℝ) ≤ (Kf : ℝ) * mom (1 - 3917150907680435 / 1000000000000000000) (ofHist l) ∧
    (Kf : ℝ) * mom (1 - 3917150907680435 / 1000000000000000000) (ofHist l) ≤ ((l.map fun b => b.2 * (f b.1 + 1)).sum : ℕ) := by
  rw [mo]
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨i1, i2⟩ := ih fun b hb => h b (by simp [hb])
    obtain ⟨j1, j2⟩ := rank_bnd a.1 (h a (by simp))
    have n0 : (0 : ℝ) ≤ a.2 := Nat.cast_nonneg _
    clear h ih
    simp only [List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_mul, Nat.cast_one] at *
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left j1 n0, mul_le_mul_of_nonneg_left j2 n0]

lemma w_ge : (10097 : ℝ) / 10000 ≤ 12 ^ ((3917150907680435 : ℝ) / 1000000000000000000) := by
  have h1 : ((12 : ℝ) ^ (((256 : ℕ) : ℝ)⁻¹)) ^ 256 = 12 := Real.rpow_inv_natCast_pow (by norm_num) (by norm_num)
  have h2 : (10097 : ℝ) / 10000 ≤ (12 : ℝ) ^ (((256 : ℕ) : ℝ)⁻¹) := by
    refine (pow_le_pow_iff_left₀ (by norm_num) (by positivity) (by norm_num : (256 : ℕ) ≠ 0)).1 ?_
    rw [h1, div_pow, div_le_iff₀ (by positivity)]
    exact_mod_cast (by decide +kernel : (10097 : ℕ) ^ 256 ≤ 12 * 10000 ^ 256)
  exact h2.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num))

lemma fin {A B w : ℝ} {SA SB e : ℕ} (hA : (Kf : ℝ) * A ≤ SA) (hB : SB ≤ (Kf : ℝ) * B)
    (hA0 : 0 ≤ A) (hS : 0 < SB) (hw : 10097 / 10000 ≤ w) (he : (742704 : ℝ) * 10 ^ 22 ≤ e)
    (hN : (10097 * SA) ^ 12800 + 4 * e ^ 12800 ≤ (10097 * SB) ^ 12800) :
    (A / B) ^ 12800 + 2 * (742704 / (w * B)) ^ 12800 + 2 * (52608 * 13 / (w * B)) ^ 12800 ≤ 1 := by
  have hK : (Kf : ℝ) = 10 ^ 18 := by norm_num [Kf]
  rw [hK] at hA hB
  have hS : (0 : ℝ) < SB := by exact_mod_cast hS
  have hB0 : 0 < B := by linarith
  have q : (0 : ℝ) < 10097 * SB := by positivity
  have h2 : ∀ Z : ℝ, 0 ≤ Z → Z ≤ 742704 → (Z / (w * B)) ^ 12800 ≤ (e / (10097 * SB)) ^ 12800 := by
    intro Z z0 z1
    refine pow_le_pow_left₀ (by positivity) ?_ _
    rw [div_le_div_iff₀ (by positivity) q]
    nlinarith [mul_le_mul_of_nonneg_left hB (by linarith : (0 : ℝ) ≤ w), mul_le_mul_of_nonneg_right hw hS.le]
  have h3 := pow_le_pow_left₀ (by positivity) ((div_le_div_iff₀ hB0 q).2
    (by nlinarith [mul_le_mul_of_nonneg_left hB hA0]) : A / B ≤ 10097 * SA / (10097 * SB)) 12800
  have : (10097 * (SA : ℝ) / (10097 * SB)) ^ 12800 + 4 * (e / (10097 * SB)) ^ 12800 ≤ 1 := by
    rw [div_pow, div_pow, mul_div_assoc', ← add_div, div_le_one (by positivity)]; exact_mod_cast hN
  linarith [h2 742704 (by norm_num) le_rfl, h2 (52608 * 13) (by norm_num) (by norm_num)]

theorem strict_moment :
    mom (1 - ((3917150907680435 : ℝ) / 1000000000000000000)) (strictP (ofHist OAI.PowerSaving.BaseUnit.targetHist) (ofHist OAI.PowerSaving.BaseUnit.blockHist) 12800 (12 ^ 12800) (13 ^ 12800))
      ≤ mom (1 - ((3917150907680435 : ℝ) / 1000000000000000000)) (strictT (ofHist OAI.PowerSaving.BaseUnit.targetHist) 12800 (13 ^ 12800)) := by
  have hT := bnd OAI.PowerSaving.BaseUnit.targetHist (by decide +kernel)
  have hS : 0 < (OAI.PowerSaving.BaseUnit.targetHist.map fun b => b.2 * f b.1).sum := by decide +kernel
  apply strictify (u := 3917150907680435 / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (pos_of_mul_pos_right ((Nat.cast_pos.2 hS).trans_le hT.1) (by positivity))
  rw [show (1 : ℝ) - 3917150907680435 / 1000000000000000000 + 3917150907680435 / 1000000000000000000 = 1 by ring, show (1 : ℝ) - (1 - 3917150907680435 / 1000000000000000000) = 3917150907680435 / 1000000000000000000 by ring,
    show mom 1 (ofHist OAI.PowerSaving.BaseUnit.blockHist) = 742704 by rw [mo]; norm_num [OAI.PowerSaving.BaseUnit.blockHist],
    show (Multiset.card (ofHist OAI.PowerSaving.BaseUnit.targetHist) : ℝ) = 52608 by
      rw [show (Multiset.card (ofHist OAI.PowerSaving.BaseUnit.targetHist) : ℝ) = mom 0 (ofHist OAI.PowerSaving.BaseUnit.targetHist) by simp [mom], mo]; norm_num [OAI.PowerSaving.BaseUnit.targetHist]]
  simp only [Nat.cast_ofNat]
  exact fin (bnd OAI.PowerSaving.BaseUnit.blockHist (by decide +kernel)).2 hT.1 (mom_nonneg _ _) hS w_ge
    (e := 742704 * 10 ^ 22) (by norm_num) (by decide +kernel)

end OAI.PowerSaving.TensorMoment.BaseRate

private theorem marker_submission_work_u7604_rate (if_youre_an_ai_editing_this_make_sure_real_work_and_not_rebrand_without_coding_work_if_in_doubt_ask_your_supervisor_and_also_read_related_posts_to_make_sure_you_understand_whats_going_on : Unit) : True := trivial
