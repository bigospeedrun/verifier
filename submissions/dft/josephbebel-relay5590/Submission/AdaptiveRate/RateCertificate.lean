import Submission.AdaptiveRate.AdaptiveTensor

open OAI.PowerSaving OAI.PowerSaving.TensorMoment
open OAI.PowerSaving.TensorMoment.BaseRate Asymptotics Filter
open FourierSearch.Moment

namespace FourierSearch.RateCertificate

/-- Leave guard digits in both the final moment sum and the repeated
tenth roots. Every rounding inequality is
checked against the exact rank and the actual supplier histogram. -/
def prec : Precision := ⟨10^43, 10^54, by norm_num⟩

def lower (ds : List ℕ) (h : Hist) := total (fun r => (prec.bounds ds r).1) h
def upper (ds : List ℕ) (h : Hist) := total (fun r => (prec.bounds ds r).2) h

/-- All supplier-specific integer tests for a proposed witness. The Boolean
form lets the kernel evaluate the same checklist for every published word. -/
def passes (ds : List ℕ) : Bool :=
  BaseUnit.blockHist.all (fun e => prec.certified ds e.1) &&
  BaseUnit.targetHist.all (fun e => prec.certified ds e.1) &&
  decide (upper ds BaseUnit.blockHist < lower ds BaseUnit.targetHist) &&
  decide (737420 * prec.scale ≤ lower ds BaseUnit.targetHist) &&
  decide (total id BaseUnit.blockHist ≤ 742704) &&
  decide ((BaseUnit.targetHist.map Prod.snd).sum ≤ 52896) &&
  decide (0 < Histogram.histFn BaseUnit.targetHist 4)

theorem moment_lt {ds : List ℕ} {u : ℝ} {a b : Hist} (hd : qExpo 1 0 ds = u)
    (ha : ∀ e ∈ a, prec.certified ds e.1 = true)
    (hb : ∀ e ∈ b, prec.certified ds e.1 = true) (hlt : upper ds a < lower ds b) :
    mom (1-u) (ofHist a) < mom (1-u) (ofHist b) := by
  have A := (prec.enclose_hist ds a ha).2
  have B := (prec.enclose_hist ds b hb).1
  rw [hd] at A B
  exact lt_of_mul_lt_mul_left (A.trans_lt ((Nat.cast_lt.mpr hlt).trans_le B)) (Nat.cast_nonneg _)

theorem score {ds : List ℕ} {s u : ℝ} (hs : 0 ≤ s) (hsu : s < u) (hu : u < 1)
    (hd : qExpo 1 0 ds = u) (hw : (10097:ℝ)/10000 ≤ 12^u)
    (hc : passes ds = true) :
    ∃ order solve W, DFTProgram order solve W ∧
      (fun n : ℕ => (W n : ℝ)) =O[atTop]
        (fun n : ℕ => (n : ℝ) * (Real.log (n : ℝ)) ^ (1-s)) := by
  simp only [passes, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨hp, ht⟩, hlt⟩, hfloor⟩, hsum⟩, hsize⟩, hsmall⟩ := hc
  have hmass : mom 1 (ofHist BaseUnit.blockHist) ≤ 742704 := by
    rw [mo]
    simpa [total, Function.comp_def] using
      (show (total id BaseUnit.blockHist : ℝ) ≤ 742704 by exact_mod_cast hsum)
  rw [← Moment.card_ofHist] at hsize
  have B := (prec.enclose_hist ds BaseUnit.targetHist ht).1
  rw [hd] at B
  have hval : (737420:ℝ) * prec.scale ≤ (lower ds BaseUnit.targetHist : ℝ) := by
    exact_mod_cast hfloor
  have hB : (737420:ℝ) ≤ mom (1-u) (ofHist BaseUnit.targetHist) := by
    apply le_of_mul_le_mul_left (a := (prec.scale:ℝ)) _ (by norm_num [prec])
    rw [mul_comm (prec.scale : ℝ) 737420]
    exact hval.trans B
  have hden := mul_le_mul hw hB (by norm_num) (by positivity)
  apply AdaptiveTensor.bound_of_raw hs hsu hu hsmall (moment_lt hd hp ht hlt)
  · linarith
  · have hcard : ((ofHist BaseUnit.targetHist).card : ℝ) ≤ 52896 := by exact_mod_cast hsize
    linarith

end FourierSearch.RateCertificate
