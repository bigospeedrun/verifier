import Submission.Data.BaseUnit.Rate

open OAI.PowerSaving OAI.PowerSaving.TensorMoment
open OAI.PowerSaving.TensorMoment.BaseRate

namespace FourierSearch.Moment

abbrev Hist := List (ℕ × ℕ)

theorem card_ofHist (h : Hist) : (ofHist h).card = (h.map Prod.snd).sum := by
  induction h with
  | nil => simp [ofHist]
  | cons e h ih => simp [ofHist] at ih ⊢; omega

/-- The multiplier for moment endpoints and the precision of intermediate
decimal roots are independent. Near a crossing, coarse endpoints can hide
a genuine strict inequality even if the underlying circuit is unchanged. -/
structure Precision where
  scale : ℕ
  rootScale : ℕ
  positive : 0 < rootScale

namespace Precision

variable (prec : Precision)

set_option maxHeartbeats 1000000

/-- Round the negative power down on the paid side or up on the target side
using the upstream base-ten root certificate. Separate endpoints also cover
rank one, where the exact power is an integer. -/
def bounds (digits : List ℕ) (r : ℕ) : ℕ × ℕ :=
  let s := qWalk prec.rootScale digits (qInit prec.rootScale r)
  (prec.scale * prec.rootScale * r / s.e, (prec.scale * prec.rootScale * r + s.c - 1) / s.c)

def certified (digits : List ℕ) (r : ℕ) : Bool :=
  let s := qWalk prec.rootScale digits (qInit prec.rootScale r)
  let (a, b) := bounds prec digits r
  1 ≤ r && qGood prec.rootScale digits (qInit prec.rootScale r) &&
    a * s.e ≤ prec.scale * prec.rootScale * r && prec.scale * prec.rootScale * r ≤ b * s.c

theorem enclose (digits : List ℕ) (r : ℕ) (hc : certified prec digits r = true) :
    ((bounds prec digits r).1 : ℝ) ≤ prec.scale * (r : ℝ) ^ (1 - qExpo 1 0 digits) ∧
    prec.scale * (r : ℝ) ^ (1 - qExpo 1 0 digits) ≤ ((bounds prec digits r).2 : ℝ) := by
  simp only [certified, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨hr, hwalk⟩, ha⟩, hb⟩ := hc
  have hr' : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hk' : (0 : ℝ) < prec.rootScale := Nat.cast_pos.mpr prec.positive
  obtain ⟨lo, hi⟩ := qWalk_sound hr' prec.positive digits (qInit prec.rootScale r) 1 0
    (by simp [qInit]) (by simp [qInit]) (by simp [qInit]) (by simp [qInit]) hwalk
  set s := qWalk prec.rootScale digits (qInit prec.rootScale r)
  let a := (bounds prec digits r).1
  let b := (bounds prec digits r).2
  have ha' : (a : ℝ) * s.e ≤ (prec.scale : ℝ) * prec.rootScale * r := by exact_mod_cast ha
  have hb' : (prec.scale : ℝ) * prec.rootScale * r ≤ (b : ℝ) * s.c := by exact_mod_cast hb
  have positive := Real.rpow_pos_of_pos hr' (qExpo 1 0 digits)
  rw [Real.rpow_sub hr', Real.rpow_one, mul_div_assoc']
  constructor
  · apply (le_div_iff₀ positive).mpr
    apply le_of_mul_le_mul_left (a := (prec.rootScale : ℝ)) _ hk'
    calc
      (prec.rootScale : ℝ) * ((a : ℝ) * (r : ℝ) ^ qExpo 1 0 digits) =
          a * ((prec.rootScale : ℝ) * (r : ℝ) ^ qExpo 1 0 digits) := by ring
      _ ≤ a * (s.e : ℝ) := mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg _)
      _ ≤ _ := by linarith only [ha']
  · apply (div_le_iff₀ positive).mpr
    apply le_of_mul_le_mul_left (a := (prec.rootScale : ℝ)) _ hk'
    calc
      (prec.rootScale : ℝ) * ((prec.scale : ℝ) * r) ≤ (b : ℝ) * s.c := by linarith only [hb']
      _ ≤ b * ((prec.rootScale : ℝ) * (r : ℝ) ^ qExpo 1 0 digits) :=
          mul_le_mul_of_nonneg_left lo (Nat.cast_nonneg _)
      _ = _ := by ring

end Precision

def total (weight : ℕ → ℕ) (h : Hist) : ℕ :=
  (h.map fun entry => entry.2 * weight entry.1).sum

namespace Precision

variable (prec : Precision)

theorem enclose_hist (digits : List ℕ) (h : Hist)
    (ok : ∀ e ∈ h, certified prec digits e.1 = true) :
    ((total (fun r => (bounds prec digits r).1) h : ℕ) : ℝ) ≤
      prec.scale * mom (1 - qExpo 1 0 digits) (ofHist h) ∧
    prec.scale * mom (1 - qExpo 1 0 digits) (ofHist h) ≤
      ((total (fun r => (bounds prec digits r).2) h : ℕ) : ℝ) := by
  rw [mo]
  induction h with
  | nil => simp [total]
  | cons e tail ih =>
    obtain ⟨l, u⟩ := ih fun b hb => ok b (List.mem_cons_of_mem _ hb)
    obtain ⟨a, b⟩ := enclose prec digits e.1 (ok e (by simp))
    simp only [total, List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_mul] at *
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left a (Nat.cast_nonneg e.2),
      mul_le_mul_of_nonneg_left b (Nat.cast_nonneg e.2)]

end Precision
end FourierSearch.Moment
