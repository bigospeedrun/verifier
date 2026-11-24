import Submission.AdaptiveRate.HistogramMoment
import Submission.AdaptiveRate.RateToDFT

open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.TensorMoment
open OAI.PowerSaving.TensorPower OAI.PowerSaving.TensorMoment.BaseRate
open Asymptotics Filter
open scoped Topology

namespace FourierSearch.AdaptiveTensor

/-- A single positive tensor order suffices for all three overhead terms.
Taking the limit avoids losing score by fixing the order in advance. -/
private theorem exists_order {a b c : ℝ} (a0 : 0 ≤ a) (a1 : a < 1)
    (b0 : 0 ≤ b) (b1 : b < 1) (c0 : 0 ≤ c) (c1 : c < 1) :
    ∃ n : ℕ, a ^ (n+1) + 2 * b ^ (n+1) + 2 * c ^ (n+1) ≤ 1 := by
  have ha := tendsto_pow_atTop_nhds_zero_of_lt_one a0 a1
  have hb := tendsto_pow_atTop_nhds_zero_of_lt_one b0 b1
  have hc := tendsto_pow_atTop_nhds_zero_of_lt_one c0 c1
  have h : Tendsto (fun v : ℕ => a^v + 2*b^v + 2*c^v) atTop (𝓝 0) := by
    simpa using (ha.add (hb.const_mul 2)).add (hc.const_mul 2)
  obtain ⟨n, hn⟩ := eventually_atTop.1 (h.eventually_lt_const (by norm_num : (0:ℝ) < 1))
  exact ⟨n, (hn (n+1) (by omega)).le⟩

private theorem strict_at_some_order {P T : Multiset ℕ} {u : ℝ}
    (hu : 0 ≤ u) (hu1 : u < 1) (hraw : mom (1-u) P < mom (1-u) T)
    (hpaid : mom 1 P < (12:ℝ)^u * mom (1-u) T)
    (hpad : (T.card : ℝ) * 13 < (12:ℝ)^u * mom (1-u) T) :
    ∃ n : ℕ, mom (1-u) (strictP T P (n+1) (12^(n+1)) (13^(n+1))) ≤
      mom (1-u) (strictT T (n+1) (13^(n+1))) := by
  have ht := (mom_nonneg _ _).trans_lt hraw
  have hden : 0 < (12:ℝ)^u * mom (1-u) T := mul_pos (by positivity) ht
  obtain ⟨n, hn⟩ := exists_order (div_nonneg (mom_nonneg _ _) ht.le)
    ((div_lt_one ht).2 hraw) (div_nonneg (mom_nonneg _ _) hden.le)
    ((div_lt_one hden).2 hpaid) (div_nonneg (by positivity) hden.le)
    ((div_lt_one hden).2 hpad)
  refine ⟨n, strictify (t := 1-u) (u := u) (by norm_num) (by norm_num)
    (by linarith) hu (by linarith) ht ?_⟩
  norm_num only [sub_add_cancel, sub_sub_cancel, Nat.cast_ofNat] at *
  exact hn

/-- The public batch supplies its exact linear map, output frames and paid moves.
The engine proof is adapted from the supplier's Apache-2.0 TensorPower.lean.
Only the choice of tensor order and the rate inequalities are replaced. -/
theorem bound_of_raw {s u : ℝ} (hs : 0 ≤ s) (hsu : s < u) (hu1 : u < 1)
    (hsmall : 0 < Histogram.histFn BaseUnit.targetHist 4)
    (hraw : mom (1-u) (ofHist BaseUnit.blockHist) < mom (1-u) (ofHist BaseUnit.targetHist))
    (hpaid : mom 1 (ofHist BaseUnit.blockHist) <
      (12:ℝ)^u * mom (1-u) (ofHist BaseUnit.targetHist))
    (hpad : ((ofHist BaseUnit.targetHist).card : ℝ) * 13 <
      (12:ℝ)^u * mom (1-u) (ofHist BaseUnit.targetHist)) :
    ∃ order solve W, DFTProgram order solve W ∧
      (fun n : ℕ => (W n : ℝ)) =O[atTop]
        (fun n : ℕ => (n : ℝ) * (Real.log (n : ℝ)) ^ (1-s)) := by
  obtain ⟨n, hm⟩ := strict_at_some_order (hs.trans hsu.le) hu1 hraw hpaid hpad
  obtain ⟨α, ρ, σ, _, _, _, _, _, _, e, tr, tz, wd, G,
    he, hind, hP, hw, hG, hα, htr, hcnt, hhist⟩ := Batch48.rawCert_exists_B48
  let A : BundledUnit := ⟨α, ρ, σ, ⟨e, he, tr, tz, hind, wd, hw⟩⟩
  have hPr := RawCert.ranks_eq_of_histG A _ G hhist
  have hTg := RawCert.tgts_eq_of_cardG A _ G hcnt
  have hR : A.BlockRanksOk := fun _ hr => RawCert.rk_bounds_of_proper hP hr
  have hT : A.TargetsOk := by
    intro l
    refine ⟨(htr l).1, ?_⟩
    change tr l ≤ Fintype.card α
    rw [hα]
    exact (htr l).2
  have hσ : 0 < Fintype.card σ := by
    have h := Finset.card_le_univ (Finset.univ.filter fun l : σ => tr l = 4)
    rw [hcnt 4] at h
    exact (Nat.mul_pos hG hsmall).trans_le h
  have hm' : mom (1-u) (strictP A.targets A.blockRanks (n+1) (12^(n+1)) (13^(n+1))) ≤
      mom (1-u) (strictT A.targets (n+1) (13^(n+1))) := by
    rw [hPr, hTg, RawCert.strictP_nsmul, RawCert.strictT_nsmul, RawCert.mom_nsmul, RawCert.mom_nsmul]
    exact mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg _)
  have hsize : Fintype.card (A.pow n).α = 137 ^ (n+1) := by rw [BundledUnit.card_pow, hα]
  have hmem : 13^(n+1) ∈ strictT A.targets (n+1) (13^(n+1)) := by
    rw [hTg, RawCert.strictT_nsmul, Multiset.mem_nsmul_of_ne_zero (pow_ne_zero _ (by omega))]
    have h4 : 4 ∈ ofHist BaseUnit.targetHist :=
      Multiset.count_pos.1 (by rwa [RawCert.count_ofHist])
    exact mem_padT (pow_mem_tpow h4 (n+1)) (Nat.pow_le_pow_left (by norm_num) _)
  let z := 1 - (s+u)/2
  have hz : z ≤ 1 := by dsimp [z]; linarith
  have engine : RippleEngine.{0} z := by
    refine ⟨by dsimp [z]; linarith, fun cl m _ k v => A.ripple_program n _ _ ?_ (by positivity)
      (Nat.pow_lt_pow_left (by norm_num) (Nat.succ_ne_zero n)) hR hT ?_ ?_ hmem hm'
      (by linarith) (by dsimp [z]; linarith) hz m cl k v⟩
    · rw [hsize]; exact Nat.pow_le_pow_left (by norm_num) _
    · rw [RawCert.card_σ_pow]; exact pow_pos hσ _
    · rw [hsize]; exact le_trans (by norm_num) (Nat.le_self_pow (Nat.succ_ne_zero n) 137)
  exact bound_of_engine engine hz (by dsimp [z]; linarith)

end FourierSearch.AdaptiveTensor
