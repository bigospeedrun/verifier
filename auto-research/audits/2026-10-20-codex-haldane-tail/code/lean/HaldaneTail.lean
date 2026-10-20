import Mathlib

/-!
The new scalar tail argument for the conditional Haldane certificate.
This file does not formalize the spatial transfer construction or the finite
thermal certificates. It proves the added scalar inequalities over the reals.
Written with Codex GPT-6 on 20 October 2026. See the research package for credits.
-/

namespace HaldaneTail

set_option maxHeartbeats 2000000

noncomputable def f (z : ℝ) : ℝ := z ^ 2 / (2 * (1 - z) ^ 2)

def mix (p q : ℝ) : ℝ := 1 - (1 - p) ^ 2 * (1 - q)

lemma f_nonneg (z : ℝ) : 0 ≤ f z := by
  unfold f
  positivity

lemma mix_bounds {p q : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    0 ≤ mix p q ∧ mix p q ≤ 2 * p + q := by
  have hs : (1 - p) ^ 2 ≤ 1 := by nlinarith
  have hprod : (1 - p) ^ 2 * (1 - q) ≤ 1 := by
    calc
      (1 - p) ^ 2 * (1 - q) ≤ 1 * (1 - q) :=
        mul_le_mul_of_nonneg_right hs (by linarith)
      _ ≤ 1 := by linarith
  have hqp : q * (1 - p) ^ 2 ≤ q := by
    calc
      q * (1 - p) ^ 2 ≤ q * 1 := mul_le_mul_of_nonneg_left hs hq
      _ = q := by ring
  unfold mix
  constructor
  · linarith
  · nlinarith [sq_nonneg p]

lemma f_upper {z u v : ℝ} (hz : 0 ≤ z) (hzu : z ≤ u)
    (hv : 0 < v) (hvz : v ≤ 1 - z) :
    f z ≤ u ^ 2 / (2 * v ^ 2) := by
  have hnum : z ^ 2 ≤ u ^ 2 := by nlinarith
  have hden : 2 * v ^ 2 ≤ 2 * (1 - z) ^ 2 := by nlinarith
  have hz1 : 0 < 1 - z := lt_of_lt_of_le hv hvz
  unfold f
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  calc
    z ^ 2 * (2 * v ^ 2) ≤ u ^ 2 * (2 * v ^ 2) :=
      mul_le_mul_of_nonneg_right hnum (by positivity)
    _ ≤ u ^ 2 * (2 * (1 - z) ^ 2) :=
      mul_le_mul_of_nonneg_left hden (sq_nonneg u)

/-- A root-free form of the stronger invariant step. Here w = x^3.
The successors P and Q are valid bounds supplied by the predecessor's update.
-/
theorem strengthened_step {x p q : ℝ}
    (hx : 0 ≤ x) (hxmax : x ≤ 1 / 100)
    (hp : 0 ≤ p) (hpp : p ≤ x ^ 2 / 100)
    (hq : 0 ≤ q) (hqq : q ≤ x ^ 3) :
    let P := f (mix p q)
    let Q := f (mix q P)
    0 ≤ P ∧ P ≤ x ^ 4 / 100 ∧
    0 ≤ Q ∧ Q ≤ (201 / 100 : ℝ) * x ^ 6 ∧
    P ^ 3 ≤ (1 / 100 : ℝ) ^ 3 * ((201 / 100 : ℝ) * x ^ 6) ^ 2 := by
  have hx2 : x ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := by gcongr
  have hx3 : x ^ 3 ≤ (1 / 100 : ℝ) ^ 3 := by gcongr
  have hx4 : x ^ 4 ≤ (1 / 100 : ℝ) ^ 4 := by gcongr
  have hx3p : 0 ≤ x ^ 3 := by positivity
  have hx4p : 0 ≤ x ^ 4 := by positivity
  have hp1 : p ≤ 1 := by nlinarith
  have hq1 : q ≤ 1 := by norm_num at hx3 ⊢ <;> linarith
  have hmix := mix_bounds hp hp1 hq hq1
  have hx32 : x ^ 3 ≤ x ^ 2 / 100 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 / 100 - x) (sq_nonneg x)]
  have ha : mix p q ≤ (3 / 100 : ℝ) * x ^ 2 := by nlinarith [hmix.2]
  have hal : (1 / 2 : ℝ) ≤ 1 - mix p q := by nlinarith
  have hP0 : 0 ≤ f (mix p q) := f_nonneg _
  have hP : f (mix p q) ≤ x ^ 4 / 100 := by
    calc
      f (mix p q) ≤ ((3 / 100 : ℝ) * x ^ 2) ^ 2 / (2 * (1 / 2 : ℝ) ^ 2) :=
        f_upper hmix.1 ha (by norm_num) hal
      _ ≤ x ^ 4 / 100 := by
        ring_nf
        nlinarith [pow_nonneg hx 4]
  have hP1 : f (mix p q) ≤ 1 := by nlinarith
  have hnext := mix_bounds hq hq1 hP0 hP1
  have hx43 : x ^ 4 ≤ x ^ 3 / 100 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 / 100 - x) hx3p]
  have hn : mix q (f (mix p q)) ≤ (20001 / 10000 : ℝ) * x ^ 3 := by
    nlinarith [hnext.2]
  have hnl : (99999 / 100000 : ℝ) ≤ 1 - mix q (f (mix p q)) := by
    norm_num at hx3
    nlinarith
  have hQ : f (mix q (f (mix p q))) ≤ (201 / 100 : ℝ) * x ^ 6 := by
    calc
      f (mix q (f (mix p q))) ≤
          ((20001 / 10000 : ℝ) * x ^ 3) ^ 2 /
            (2 * (99999 / 100000 : ℝ) ^ 2) :=
        f_upper hnext.1 hn (by norm_num) hnl
      _ ≤ (201 / 100 : ℝ) * x ^ 6 := by
        ring_nf
        nlinarith [pow_nonneg hx 6]
  have hcube : f (mix p q) ^ 3 ≤ (x ^ 4 / 100) ^ 3 := by gcongr
  have hpreserve : f (mix p q) ^ 3 ≤
      (1 / 100 : ℝ) ^ 3 * ((201 / 100 : ℝ) * x ^ 6) ^ 2 := by
    nlinarith [pow_nonneg hx 12]
  exact ⟨hP0, hP, f_nonneg _, hQ, hpreserve⟩

/-- The product lower bound in the written proof loses less than 2.01w. -/
theorem purity_floor {w : ℝ} (hw : 0 ≤ w) :
    1 - (201 / 100 : ℝ) * w ≤
      ((1 - (10001 / 5000 : ℝ) * w) * (1 - (3 / 500 : ℝ) * w)) /
        (1 + w / 1000) ^ 2 := by
  have hd : 0 < (1 + w / 1000) ^ 2 := by positivity
  apply (le_div_iff₀ hd).2
  nlinarith [sq_nonneg w, pow_nonneg hw 3]

/-- Exact constants used to pass from residual moments to purity. -/
theorem interpolation_constants :
    (1 / 1000 : ℝ) ^ 2 = (1 / 100 : ℝ) ^ 3 ∧
    (3 / 100 : ℝ) ^ 3 < (3 / 500 : ℝ) ^ 2 ∧
    2 * (1 + (1 / 100 : ℝ) / 100) + 3 / 500 + 2 / 1000 < 201 / 100 := by
  norm_num

lemma power_le_self {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    ∀ n : ℕ, r ^ (n + 1) ≤ r := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      r ^ (n + 1 + 1) = r ^ (n + 1) * r := by rw [pow_succ]
      _ ≤ r * r := mul_le_mul_of_nonneg_right ih hr
      _ ≤ r := by nlinarith

/-- With B=C, the two exponential tail conditions reduce to this geometric
inequality. The exponent n+1 can in particular be any positive dyadic power.
-/
theorem tail_geometric {alpha E : ℝ} (ha : 0 ≤ alpha) (hE : 0 ≤ E)
    (hsmall : E * alpha + alpha < 1) (n : ℕ) :
    E ^ (n + 1) * alpha ^ (n + 1) / (1 - alpha ^ (n + 1)) < 1 := by
  have hprod : 0 ≤ E * alpha := mul_nonneg hE ha
  have ha1 : alpha ≤ 1 := by linarith
  have hprod1 : E * alpha ≤ 1 := by linarith
  have hpa := power_le_self ha ha1 n
  have hpp := power_le_self hprod hprod1 n
  have hd : 0 < 1 - alpha ^ (n + 1) := by linarith
  apply (div_lt_iff₀ hd).2
  rw [← mul_pow]
  nlinarith

theorem gap_from_exponential {beta delta gap : ℝ} (hb : 0 < beta)
    (hsmall : Real.exp (beta * delta) * Real.exp (-beta * gap) < 1) :
    delta < gap := by
  have he : Real.exp (beta * (delta - gap)) < Real.exp 0 := by
    calc
      Real.exp (beta * (delta - gap)) =
          Real.exp (beta * delta) * Real.exp (-beta * gap) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ < 1 := hsmall
      _ = Real.exp 0 := by simp
  have hm := Real.exp_lt_exp.mp he
  nlinarith

/-- A conditional implication from a supplied physical exponential bound.
The physical bound remains an explicit hypothesis, not an added axiom.
-/
theorem conditional_gap {alpha E beta delta gap : ℝ}
    (ha : 0 ≤ alpha) (hE : 0 ≤ E) (hsmall : E * alpha + alpha < 1)
    (hb : 0 < beta) (n : ℕ)
    (hphysical : Real.exp (beta * delta) * Real.exp (-beta * gap) ≤
      E ^ (n + 1) * alpha ^ (n + 1) / (1 - alpha ^ (n + 1))) :
    delta < gap := by
  exact gap_from_exponential hb (lt_of_le_of_lt hphysical (tail_geometric ha hE hsmall n))

/-- The small-w domain is preserved by the new scalar update. -/
theorem invariant_domain {w : ℝ} (hw : 0 ≤ w) (hmax : w ≤ 1 / 1000000) :
    0 ≤ (201 / 100 : ℝ) * w ^ 2 ∧
    (201 / 100 : ℝ) * w ^ 2 ≤ 1 / 1000000 := by
  have hs : w ^ 2 ≤ (1 / 1000000 : ℝ) ^ 2 := by gcongr
  constructor
  · positivity
  · norm_num at hs
    nlinarith

/-- Exact certificate values for an independently Lean-checked exponential
enclosure. The prior Python Taylor routine is not used by this proof. -/
def finalW : ℚ := 170982022810726 / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def finalE : ℚ := 26944642906237948270024277222985942937260000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 / 1

theorem final_tail_comparison :
    finalE * (201 / 100) * finalW + (201 / 100) * finalW < 1 := by
  norm_num [finalW, finalE]

theorem final_tail_comparison_real :
    (finalE : ℝ) * (201 / 100) * (finalW : ℝ) +
      (201 / 100) * (finalW : ℝ) < 1 := by
  norm_num [finalW, finalE]

lemma exp_small_upper {t : ℝ} (ht : t < 1) :
    Real.exp t ≤ 1 / (1 - t) := by
  have hp : 0 < 1 - t := by linarith
  have hl := Real.log_le_sub_one_of_pos hp
  calc
    Real.exp t ≤ Real.exp (-Real.log (1 - t)) := Real.exp_le_exp.mpr (by linarith)
    _ = 1 / (1 - t) := by rw [Real.exp_neg, Real.exp_log hp, one_div]

lemma exp_step {t a b : ℝ} (ha : Real.exp t ≤ a) (hab : a ^ 2 ≤ b) :
    Real.exp (t + t) ≤ b := by
  rw [Real.exp_add]
  have hn : 0 ≤ Real.exp t := (Real.exp_pos t).le
  have han : 0 ≤ a := le_trans hn ha
  calc
    Real.exp t * Real.exp t ≤ a * a := mul_le_mul ha ha hn han
    _ ≤ b := by nlinarith

/-- An independent exponential enclosure using log(1-u) <= -u followed
by thirty squarings. Every rational rounding inequality is checked here. -/
theorem final_exp_upper :
    Real.exp (12544 * (1517 / 10000 : ℝ)) ≤ (finalE : ℝ) := by
  let r0 : ℝ := 41943040000 / 41942965667
  let r1 : ℝ := 250000886120767640908911734261411984833 / 250000000000000000000000000000000000000
  let r2 : ℝ := 1000007088978704487508806093008047275117 / 1000000000000000000000000000000000000000
  let r3 : ℝ := 1000014178007662594090289584721143814051 / 1000000000000000000000000000000000000000
  let r4 : ℝ := 40001134248653643578446236361677780869 / 40000000000000000000000000000000000000
  let r5 : ℝ := 1000056713236757184104980806147042494543 / 1000000000000000000000000000000000000000
  let r6 : ℝ := 500056714844952795843189934036161399807 / 500000000000000000000000000000000000000
  let r7 : ℝ := 1000226872246105735451448250348890648771 / 1000000000000000000000000000000000000000
  let r8 : ℝ := 500226897981613761982145607827392918359 / 500000000000000000000000000000000000000
  let r9 : ℝ := 62556737366076955595304027831022938041 / 62500000000000000000000000000000000000
  let r10 : ℝ := 500908209905706086385223990535444700367 / 500000000000000000000000000000000000000
  let r11 : ℝ := 501818069501877818087094362482247866619 / 500000000000000000000000000000000000000
  let r12 : ℝ := 1007285499514365905378717111564471694501 / 1000000000000000000000000000000000000000
  let r13 : ℝ := 202924815506381127320109596804036489547 / 200000000000000000000000000000000000000
  let r14 : ℝ := 257365504676867615114195109552202735487 / 250000000000000000000000000000000000000
  let r15 : ℝ := 1059792047961260260294967235821662569043 / 1000000000000000000000000000000000000000
  let r16 : ℝ := 1123159184921922167839533589321091165661 / 1000000000000000000000000000000000000000
  let r17 : ℝ := 252297310934895311266852732359776175361 / 200000000000000000000000000000000000000
  let r18 : ℝ := 1591348327624481130062712902744710499599 / 1000000000000000000000000000000000000000
  let r19 : ℝ := 126619474991661646626335592376631023601 / 50000000000000000000000000000000000000
  let r20 : ℝ := 6412996578865611658797518359228058224947 / 1000000000000000000000000000000000000000
  let r21 : ℝ := 4112652512054203929624006120908961557941 / 100000000000000000000000000000000000000
  let r22 : ℝ := 6765564273962301599463927217322366863 / 4000000000000000000000000000000000
  let r23 : ℝ := 357600468321211290408545533093030129309 / 125000000000000000000000000000000
  let r24 : ℝ := 8184198076387176938056721968171334345089 / 1000000000000000000000000000
  let r25 : ℝ := 3349054907676978363959034810145625714539 / 50000000000000
  let r26 : ℝ := 4486467509854101629183189864429077507724000000000000 / 1
  let r27 : ℝ := 20128390716976463499158184664451721310780000000000000000000000000000000000000000000000000000000000000000 / 1
  let r28 : ℝ := 405152112855264270318890436995915451027200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 / 1
  let r29 : ℝ := 164148234551084795607151720175100254430500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 / 1
  let r30 : ℝ := 26944642906237948270024277222985942937260000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 / 1
  have h0 : Real.exp (74333 / 41943040000 : ℝ) ≤ r0 := by
    calc
      _ ≤ 1 / (1 - (74333 / 41943040000 : ℝ)) :=
        exp_small_upper (by norm_num)
      _ = r0 := by norm_num [r0]
  have h1 : Real.exp (74333 / 20971520000 : ℝ) ≤ r1 := by
    rw [show (74333 / 20971520000 : ℝ) =
      (74333 / 41943040000 : ℝ) + (74333 / 41943040000 : ℝ) by norm_num]
    exact exp_step h0 (by norm_num [r0, r1])
  have h2 : Real.exp (74333 / 10485760000 : ℝ) ≤ r2 := by
    rw [show (74333 / 10485760000 : ℝ) =
      (74333 / 20971520000 : ℝ) + (74333 / 20971520000 : ℝ) by norm_num]
    exact exp_step h1 (by norm_num [r1, r2])
  have h3 : Real.exp (74333 / 5242880000 : ℝ) ≤ r3 := by
    rw [show (74333 / 5242880000 : ℝ) =
      (74333 / 10485760000 : ℝ) + (74333 / 10485760000 : ℝ) by norm_num]
    exact exp_step h2 (by norm_num [r2, r3])
  have h4 : Real.exp (74333 / 2621440000 : ℝ) ≤ r4 := by
    rw [show (74333 / 2621440000 : ℝ) =
      (74333 / 5242880000 : ℝ) + (74333 / 5242880000 : ℝ) by norm_num]
    exact exp_step h3 (by norm_num [r3, r4])
  have h5 : Real.exp (74333 / 1310720000 : ℝ) ≤ r5 := by
    rw [show (74333 / 1310720000 : ℝ) =
      (74333 / 2621440000 : ℝ) + (74333 / 2621440000 : ℝ) by norm_num]
    exact exp_step h4 (by norm_num [r4, r5])
  have h6 : Real.exp (74333 / 655360000 : ℝ) ≤ r6 := by
    rw [show (74333 / 655360000 : ℝ) =
      (74333 / 1310720000 : ℝ) + (74333 / 1310720000 : ℝ) by norm_num]
    exact exp_step h5 (by norm_num [r5, r6])
  have h7 : Real.exp (74333 / 327680000 : ℝ) ≤ r7 := by
    rw [show (74333 / 327680000 : ℝ) =
      (74333 / 655360000 : ℝ) + (74333 / 655360000 : ℝ) by norm_num]
    exact exp_step h6 (by norm_num [r6, r7])
  have h8 : Real.exp (74333 / 163840000 : ℝ) ≤ r8 := by
    rw [show (74333 / 163840000 : ℝ) =
      (74333 / 327680000 : ℝ) + (74333 / 327680000 : ℝ) by norm_num]
    exact exp_step h7 (by norm_num [r7, r8])
  have h9 : Real.exp (74333 / 81920000 : ℝ) ≤ r9 := by
    rw [show (74333 / 81920000 : ℝ) =
      (74333 / 163840000 : ℝ) + (74333 / 163840000 : ℝ) by norm_num]
    exact exp_step h8 (by norm_num [r8, r9])
  have h10 : Real.exp (74333 / 40960000 : ℝ) ≤ r10 := by
    rw [show (74333 / 40960000 : ℝ) =
      (74333 / 81920000 : ℝ) + (74333 / 81920000 : ℝ) by norm_num]
    exact exp_step h9 (by norm_num [r9, r10])
  have h11 : Real.exp (74333 / 20480000 : ℝ) ≤ r11 := by
    rw [show (74333 / 20480000 : ℝ) =
      (74333 / 40960000 : ℝ) + (74333 / 40960000 : ℝ) by norm_num]
    exact exp_step h10 (by norm_num [r10, r11])
  have h12 : Real.exp (74333 / 10240000 : ℝ) ≤ r12 := by
    rw [show (74333 / 10240000 : ℝ) =
      (74333 / 20480000 : ℝ) + (74333 / 20480000 : ℝ) by norm_num]
    exact exp_step h11 (by norm_num [r11, r12])
  have h13 : Real.exp (74333 / 5120000 : ℝ) ≤ r13 := by
    rw [show (74333 / 5120000 : ℝ) =
      (74333 / 10240000 : ℝ) + (74333 / 10240000 : ℝ) by norm_num]
    exact exp_step h12 (by norm_num [r12, r13])
  have h14 : Real.exp (74333 / 2560000 : ℝ) ≤ r14 := by
    rw [show (74333 / 2560000 : ℝ) =
      (74333 / 5120000 : ℝ) + (74333 / 5120000 : ℝ) by norm_num]
    exact exp_step h13 (by norm_num [r13, r14])
  have h15 : Real.exp (74333 / 1280000 : ℝ) ≤ r15 := by
    rw [show (74333 / 1280000 : ℝ) =
      (74333 / 2560000 : ℝ) + (74333 / 2560000 : ℝ) by norm_num]
    exact exp_step h14 (by norm_num [r14, r15])
  have h16 : Real.exp (74333 / 640000 : ℝ) ≤ r16 := by
    rw [show (74333 / 640000 : ℝ) =
      (74333 / 1280000 : ℝ) + (74333 / 1280000 : ℝ) by norm_num]
    exact exp_step h15 (by norm_num [r15, r16])
  have h17 : Real.exp (74333 / 320000 : ℝ) ≤ r17 := by
    rw [show (74333 / 320000 : ℝ) =
      (74333 / 640000 : ℝ) + (74333 / 640000 : ℝ) by norm_num]
    exact exp_step h16 (by norm_num [r16, r17])
  have h18 : Real.exp (74333 / 160000 : ℝ) ≤ r18 := by
    rw [show (74333 / 160000 : ℝ) =
      (74333 / 320000 : ℝ) + (74333 / 320000 : ℝ) by norm_num]
    exact exp_step h17 (by norm_num [r17, r18])
  have h19 : Real.exp (74333 / 80000 : ℝ) ≤ r19 := by
    rw [show (74333 / 80000 : ℝ) =
      (74333 / 160000 : ℝ) + (74333 / 160000 : ℝ) by norm_num]
    exact exp_step h18 (by norm_num [r18, r19])
  have h20 : Real.exp (74333 / 40000 : ℝ) ≤ r20 := by
    rw [show (74333 / 40000 : ℝ) =
      (74333 / 80000 : ℝ) + (74333 / 80000 : ℝ) by norm_num]
    exact exp_step h19 (by norm_num [r19, r20])
  have h21 : Real.exp (74333 / 20000 : ℝ) ≤ r21 := by
    rw [show (74333 / 20000 : ℝ) =
      (74333 / 40000 : ℝ) + (74333 / 40000 : ℝ) by norm_num]
    exact exp_step h20 (by norm_num [r20, r21])
  have h22 : Real.exp (74333 / 10000 : ℝ) ≤ r22 := by
    rw [show (74333 / 10000 : ℝ) =
      (74333 / 20000 : ℝ) + (74333 / 20000 : ℝ) by norm_num]
    exact exp_step h21 (by norm_num [r21, r22])
  have h23 : Real.exp (74333 / 5000 : ℝ) ≤ r23 := by
    rw [show (74333 / 5000 : ℝ) =
      (74333 / 10000 : ℝ) + (74333 / 10000 : ℝ) by norm_num]
    exact exp_step h22 (by norm_num [r22, r23])
  have h24 : Real.exp (74333 / 2500 : ℝ) ≤ r24 := by
    rw [show (74333 / 2500 : ℝ) =
      (74333 / 5000 : ℝ) + (74333 / 5000 : ℝ) by norm_num]
    exact exp_step h23 (by norm_num [r23, r24])
  have h25 : Real.exp (74333 / 1250 : ℝ) ≤ r25 := by
    rw [show (74333 / 1250 : ℝ) =
      (74333 / 2500 : ℝ) + (74333 / 2500 : ℝ) by norm_num]
    exact exp_step h24 (by norm_num [r24, r25])
  have h26 : Real.exp (74333 / 625 : ℝ) ≤ r26 := by
    rw [show (74333 / 625 : ℝ) =
      (74333 / 1250 : ℝ) + (74333 / 1250 : ℝ) by norm_num]
    exact exp_step h25 (by norm_num [r25, r26])
  have h27 : Real.exp (148666 / 625 : ℝ) ≤ r27 := by
    rw [show (148666 / 625 : ℝ) =
      (74333 / 625 : ℝ) + (74333 / 625 : ℝ) by norm_num]
    exact exp_step h26 (by norm_num [r26, r27])
  have h28 : Real.exp (297332 / 625 : ℝ) ≤ r28 := by
    rw [show (297332 / 625 : ℝ) =
      (148666 / 625 : ℝ) + (148666 / 625 : ℝ) by norm_num]
    exact exp_step h27 (by norm_num [r27, r28])
  have h29 : Real.exp (594664 / 625 : ℝ) ≤ r29 := by
    rw [show (594664 / 625 : ℝ) =
      (297332 / 625 : ℝ) + (297332 / 625 : ℝ) by norm_num]
    exact exp_step h28 (by norm_num [r28, r29])
  have h30 : Real.exp (1189328 / 625 : ℝ) ≤ r30 := by
    rw [show (1189328 / 625 : ℝ) =
      (594664 / 625 : ℝ) + (594664 / 625 : ℝ) by norm_num]
    exact exp_step h29 (by norm_num [r29, r30])
  calc
    Real.exp (12544 * (1517 / 10000 : ℝ)) =
        Real.exp (1189328 / 625 : ℝ) := by congr 1 <;> norm_num
    _ ≤ r30 := h30
    _ = (finalE : ℝ) := by norm_num [r30, finalE]

/-- The actual exponential tail comparison for delta = 1517/10000. -/
theorem final_exponential_comparison :
    Real.exp (12544 * (1517 / 10000 : ℝ)) * (201 / 100) * (finalW : ℝ) +
      (201 / 100) * (finalW : ℝ) < 1 := by
  have hw : 0 ≤ (finalW : ℝ) := by norm_num [finalW]
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right final_exp_upper (by norm_num : (0 : ℝ) ≤ 201 / 100)) hw
  linarith [final_tail_comparison_real]

#print axioms strengthened_step
#print axioms purity_floor
#print axioms interpolation_constants
#print axioms tail_geometric
#print axioms conditional_gap
#print axioms invariant_domain
#print axioms final_tail_comparison
#print axioms final_tail_comparison_real
#print axioms final_exp_upper
#print axioms final_exponential_comparison

end HaldaneTail
