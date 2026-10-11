/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Pruned.Costs
public import Submission.ThreeSumApsp.Programs.Sec4.Theorem30.TimeOfBlock

/-!
# The preprocessing of Theorem 30 with pruned encodings, against the sharper cost `cost8p`

The shared stage of Section 4 writes the encodings only at the leaves with at most `m` nines.  Its
time is a constant times `retW L m`, `N (L + 1)` and the work for the bands
(`sharedShapeP_le_ret`); with the tiles this makes the preprocessing `O(cost8p)`, where
`cost8p L m t N = L (m+1) (∑_{d ≥ t} β_d / M) N² + L N ∑_{d ≤ m} β_d / √M`
(`exists_tPreCore_le_p`).

* `retW L m` is the number of strings of `L` digits with at most `m` nines, which is
  `∑_{d ≤ m} β_d = retained L m` (`retW_eq_retained`).
* `Within8p f`: `f` is at most a constant times `cost8p`, under the hypotheses of Theorem 30.
  Everything is compared with the second term `L N R/√M`, `R = retained L m`, via
  `√M = √K N₀ ≤ 7^L ≤ 9^L ≤ R` and `√M ≤ N`; the boxes are compared with the first term by
  Lemma 29 and the count of the tiles.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec Finset

/-! ## The retained leaves -/

private theorem nine_mul_choose_succ (L j : ℕ) :
    9 * (L.choose (j + 1) * 9 ^ (L - (j + 1))) = L.choose (j + 1) * 9 ^ (L - j) := by
  rcases Nat.lt_or_ge j L with hj | hj
  · obtain ⟨k, rfl⟩ : ∃ k, L = j + 1 + k := ⟨L - (j + 1), by omega⟩
    rw [show j + 1 + k - (j + 1) = k by omega, show j + 1 + k - j = k + 1 by omega, pow_succ]
    ring
  · rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

/-- `retW L r` counts the strings of `L` digits with at most `r` nines. -/
theorem retW_eq_sum (L r : ℕ) :
    Sec2.retW L r = ∑ j ∈ range (r + 1), L.choose j * 9 ^ (L - j) := by
  induction L generalizing r with
  | zero =>
    rw [Finset.sum_range_succ']
    simp [Sec2.retW]
  | succ L ih =>
    cases r with
    | zero =>
      simp [Sec2.retW, ih, pow_succ]
      ring
    | succ r =>
      rw [Sec2.retW, ih, ih, Finset.sum_range_succ' _ (r + 1),
        Finset.sum_range_succ' (fun j => (L + 1).choose j * 9 ^ (L + 1 - j)) (r + 1)]
      simp only [Nat.choose_succ_succ, Nat.choose_zero_right, add_mul, Finset.sum_add_distrib,
        Nat.add_sub_add_right, Nat.sub_zero]
      rw [Nat.mul_add, Finset.mul_sum, Finset.sum_congr rfl fun j _ => nine_mul_choose_succ L j]
      simp only [Nat.succ_eq_add_one]
      ring

/-- `retW L m = ∑_{d ≤ m} β_d`. -/
theorem retW_eq_retained {L m : ℕ} (hmL : m ≤ L) : Sec2.retW L m = retained L m := by
  rw [retW_eq_sum, retained, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun d hd => ?_
  have := Finset.mem_range.1 hd
  simp only [beta]
  rw [show m + 1 - 1 - d = m - d by omega, show L - (m - d) = L - m + d by omega]

/-! ## The facts about the sizes -/

section facts

variable {p : Sec2.Par} {t : ℕ}

theorem Hyp30.sqrtKN0_pos (h : Hyp30 p t) : 0 < sqrtKN0 p.L p.m := ThreeSumApsp.sqrtKN0_pos h.m_le

/-- `√M = √K N₀`. -/
theorem sqrt_M_eq (L m : ℕ) (hmL : m ≤ L) :
    Real.sqrt (ThreeSumApsp.M L m : ℝ) = sqrtKN0 L m := by
  rw [← sqrtKN0_sq, Real.sqrt_sq (ThreeSumApsp.sqrtKN0_pos hmL).le]

/-- `9^L ≤ ∑_{d ≤ m} β_d`. -/
theorem nine_pow_le_retained {L m : ℕ} (hmL : m ≤ L) : 9 ^ L ≤ retained L m :=
  retW_eq_retained hmL ▸ Sec2.nine_pow_le_retW L m

/-- `K N₀ 4^m ≤ ∑_{d ≤ m} β_d`. -/
theorem KND_le_retained {L m : ℕ} (hmL : m ≤ L) :
    K L m * N0 L m * 4 ^ m ≤ retained L m :=
  (Theorem30.K_mul_N0_mul_D_le L m).trans
    ((Nat.pow_le_pow_left (by norm_num) L).trans (nine_pow_le_retained hmL))

/-- `√K N₀ 4^m ≤ ∑_{d ≤ m} β_d`. -/
theorem sqrtKN0_mul_pow_le_retained {L m : ℕ} (hmL : m ≤ L) :
    sqrtKN0 L m * (4 : ℝ) ^ m ≤ (retained L m : ℝ) := by
  calc sqrtKN0 L m * (4 : ℝ) ^ m ≤ (K L m : ℝ) * (N0 L m : ℝ) * (4 : ℝ) ^ m := by
        gcongr
        exact sqrtKN0_le hmL
    _ = ((K L m * N0 L m * 4 ^ m : ℕ) : ℝ) := by push_cast; ring
    _ ≤ (retained L m : ℝ) := by exact_mod_cast KND_le_retained hmL

/-- `√K N₀ ≤ ∑_{d ≤ m} β_d`. -/
theorem sqrtKN0_le_retained {L m : ℕ} (hmL : m ≤ L) : sqrtKN0 L m ≤ (retained L m : ℝ) := by
  have h := sqrtKN0_mul_pow_le_retained hmL
  have h4 : (1 : ℝ) ≤ (4 : ℝ) ^ m := one_le_pow₀ (by norm_num)
  nlinarith [(ThreeSumApsp.sqrtKN0_pos hmL).le]

/-- The first term of `cost8p` is not negative. -/
theorem cost8p_first_nonneg (L m t N : ℕ) :
    0 ≤ (L : ℝ) * ((m : ℝ) + 1) * (tailBeta L m t / (ThreeSumApsp.M L m : ℝ)) * (N : ℝ) ^ 2 := by
  have : 0 ≤ tailBeta L m t := sum_nonneg fun _ _ => Nat.cast_nonneg _
  positivity

/-- `cost8p` with `√M` under its name `√K N₀`. -/
theorem cost8p_eq {L m : ℕ} (t N : ℕ) (hmL : m ≤ L) :
    cost8p L m t N = (L : ℝ) * ((m : ℝ) + 1) * (tailBeta L m t / (ThreeSumApsp.M L m : ℝ))
        * (N : ℝ) ^ 2 + (L : ℝ) * (N : ℝ) * (retained L m : ℝ) / sqrtKN0 L m := by
  rw [cost8p, sqrt_M_eq L m hmL]

/-- A quantity whose product with `√K N₀` is at most `k L N R` is at most `k cost8p`. -/
theorem le_cost8p_of_mul (h : Hyp30 p t) {x k : ℝ} (hk : 0 ≤ k)
    (hx : x * sqrtKN0 p.L p.m ≤ k * ((p.L : ℝ) * (p.N : ℝ) * (retained p.L p.m : ℝ))) :
    x ≤ k * cost8p p.L p.m t p.N := by
  have hs := h.sqrtKN0_pos
  have hfirst := cost8p_first_nonneg p.L p.m t p.N
  rw [cost8p_eq t p.N h.m_le]
  have hx' : x ≤ k * ((p.L : ℝ) * (p.N : ℝ) * (retained p.L p.m : ℝ) / sqrtKN0 p.L p.m) := by
    rw [mul_div_assoc', le_div_iff₀ hs]
    exact hx
  nlinarith

theorem Hyp30.one_le_L_real (h : Hyp30 p t) : (1 : ℝ) ≤ (p.L : ℝ) := by
  exact_mod_cast h.L_pos

theorem Hyp30.one_le_retained (h : Hyp30 p t) : (1 : ℝ) ≤ (retained p.L p.m : ℝ) := by
  have := nine_pow_le_retained h.m_le
  have : 1 ≤ retained p.L p.m := le_trans (Nat.one_le_pow _ _ (by norm_num)) this
  exact_mod_cast this

theorem Hyp30.one_le_N (h : Hyp30 p t) : 1 ≤ p.N := by
  have hs := h.sqrtKN0_pos
  have := h.N_ge
  have : (0 : ℝ) < p.N := lt_of_lt_of_le hs this
  exact_mod_cast this

end facts

/-! ## Within `cost8p` -/

/-- `f = O(cost8p)` under the hypotheses of Theorem 30. -/
def Within8p (f : Sec2.Par → ℕ → ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ p t, Hyp30 p t → (f p t : ℝ) ≤ C * cost8p p.L p.m t p.N

namespace Within8p

variable {f g : Sec2.Par → ℕ → ℕ}

theorem of_le (hg : Within8p g) (h : ∀ p t, Hyp30 p t → f p t ≤ g p t) : Within8p f :=
  let ⟨C, hC, hg⟩ := hg
  ⟨C, hC, fun p t hp => le_trans (by exact_mod_cast h p t hp) (hg p t hp)⟩

theorem add (hf : Within8p f) (hg : Within8p g) : Within8p fun p t => f p t + g p t := by
  obtain ⟨A, hA, hf⟩ := hf
  obtain ⟨B, hB, hg⟩ := hg
  refine ⟨A + B, add_nonneg hA hB, fun p t hp => ?_⟩
  rw [Nat.cast_add, add_mul]
  exact add_le_add (hf p t hp) (hg p t hp)

theorem const_mul (c : ℕ) (hf : Within8p f) : Within8p fun p t => c * f p t := by
  obtain ⟨A, hA, hf⟩ := hf
  refine ⟨c * A, by positivity, fun p t hp => ?_⟩
  rw [Nat.cast_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hf p t hp) (Nat.cast_nonneg c)

end Within8p

/-- `1 ≤ cost8p`. -/
theorem one_le_cost8p {p : Sec2.Par} {t : ℕ} (h : Hyp30 p t) : 1 ≤ cost8p p.L p.m t p.N := by
  have hL := h.one_le_L_real
  have hR := h.one_le_retained
  have hN := h.N_ge
  have hs := h.sqrtKN0_pos
  refine (le_cost8p_of_mul h zero_le_one ?_).trans_eq (one_mul _)
  have hN0 : (0 : ℝ) ≤ p.N := Nat.cast_nonneg _
  have : (p.N : ℝ) ≤ (p.L : ℝ) * (p.N : ℝ) * (retained p.L p.m : ℝ) := by
    have h1 : (p.N : ℝ) ≤ (p.L : ℝ) * (p.N : ℝ) := le_mul_of_one_le_left hN0 hL
    have h2 : (p.L : ℝ) * (p.N : ℝ) ≤ (p.L : ℝ) * (p.N : ℝ) * (retained p.L p.m : ℝ) :=
      le_mul_of_one_le_right (by positivity) hR
    linarith
  linarith

theorem within8p_one : Within8p fun _ _ => 1 :=
  ⟨1, zero_le_one, fun p t h => by simpa using one_le_cost8p h⟩

/-- `N 4^m ≤ cost8p`. -/
theorem N_mul_pow_le_cost8p {p : Sec2.Par} {t : ℕ} (h : Hyp30 p t) :
    (p.N : ℝ) * (4 : ℝ) ^ p.m ≤ cost8p p.L p.m t p.N := by
  have hL := h.one_le_L_real
  have hkey := sqrtKN0_mul_pow_le_retained h.m_le
  refine (le_cost8p_of_mul h zero_le_one ?_).trans_eq (one_mul _)
  have hN0 : (0 : ℝ) ≤ p.N := Nat.cast_nonneg _
  calc (p.N : ℝ) * (4 : ℝ) ^ p.m * sqrtKN0 p.L p.m
      = (p.N : ℝ) * (sqrtKN0 p.L p.m * (4 : ℝ) ^ p.m) := by ring
    _ ≤ (p.N : ℝ) * (retained p.L p.m : ℝ) := mul_le_mul_of_nonneg_left hkey hN0
    _ ≤ 1 * ((p.L : ℝ) * (p.N : ℝ) * (retained p.L p.m : ℝ)) := by
        have hNR : (0 : ℝ) ≤ (p.N : ℝ) * (retained p.L p.m : ℝ) := by positivity
        nlinarith

/-- `N (L + 1) ≤ 2 cost8p`. -/
theorem N_mul_le_cost8p {p : Sec2.Par} {t : ℕ} (h : Hyp30 p t) :
    (p.N : ℝ) * ((p.L : ℝ) + 1) ≤ 2 * cost8p p.L p.m t p.N := by
  have hL := h.one_le_L_real
  have hsR := sqrtKN0_le_retained h.m_le
  have hs := h.sqrtKN0_pos
  refine le_cost8p_of_mul h zero_le_two ?_
  have hN0 : (0 : ℝ) ≤ p.N := Nat.cast_nonneg _
  calc (p.N : ℝ) * ((p.L : ℝ) + 1) * sqrtKN0 p.L p.m
      ≤ (p.N : ℝ) * (2 * (p.L : ℝ)) * (retained p.L p.m : ℝ) := by
        gcongr
        linarith
    _ = 2 * ((p.L : ℝ) * (p.N : ℝ) * (retained p.L p.m : ℝ)) := by ring

theorem within8p_N_mul : Within8p fun p _ => p.N * (p.L + 1) :=
  ⟨2, by norm_num, fun p t h => by
    push_cast
    exact N_mul_le_cost8p h⟩

/-- The retained leaves: `retW L m ≤ cost8p`. -/
theorem within8p_ret : Within8p fun p _ => Sec2.retW p.L p.m := by
  refine ⟨1, zero_le_one, fun p t h => ?_⟩
  dsimp only
  rw [retW_eq_retained h.m_le]
  have hL := h.one_le_L_real
  have hN := h.N_ge
  refine le_cost8p_of_mul h zero_le_one ?_
  have hR0 : (0 : ℝ) ≤ (retained p.L p.m : ℝ) := Nat.cast_nonneg _
  calc (retained p.L p.m : ℝ) * sqrtKN0 p.L p.m ≤ (retained p.L p.m : ℝ) * (p.N : ℝ) :=
        mul_le_mul_of_nonneg_left hN hR0
    _ ≤ 1 * ((p.L : ℝ) * (p.N : ℝ) * (retained p.L p.m : ℝ)) := by
        have hNR : (0 : ℝ) ≤ (p.N : ℝ) * (retained p.L p.m : ℝ) := by positivity
        nlinarith

/-- The work for the bands: `retW L m + L 7^L` for each band. -/
theorem within8p_bands :
    Within8p fun p _ => p.nB * (Sec2.retW p.L p.m + p.L * 7 ^ p.L) := by
  refine ⟨4, by norm_num, fun p t h => ?_⟩
  have hL := h.one_le_L_real
  have hband := Theorem30.numBands_mul_le h.m_pos h.L_ge h.N_ge
  have h7 : (7 : ℝ) ^ p.L ≤ (retained p.L p.m : ℝ) := by
    exact_mod_cast (Nat.pow_le_pow_left (by norm_num) p.L).trans (nine_pow_le_retained h.m_le)
  dsimp only
  rw [retW_eq_retained h.m_le]
  refine le_cost8p_of_mul h (by norm_num) ?_
  push_cast
  change (numBands p.L p.m p.N : ℝ) * _ * _ ≤ _
  have hR0 : (0 : ℝ) ≤ (retained p.L p.m : ℝ) := Nat.cast_nonneg _
  have hsum : (retained p.L p.m : ℝ) + (p.L : ℝ) * (7 : ℝ) ^ p.L
      ≤ 2 * (p.L : ℝ) * (retained p.L p.m : ℝ) := by
    have : (p.L : ℝ) * (7 : ℝ) ^ p.L ≤ (p.L : ℝ) * (retained p.L p.m : ℝ) :=
      mul_le_mul_of_nonneg_left h7 (by positivity)
    nlinarith
  calc (numBands p.L p.m p.N : ℝ) * ((retained p.L p.m : ℝ) + (p.L : ℝ) * (7 : ℝ) ^ p.L)
        * sqrtKN0 p.L p.m
      = ((numBands p.L p.m p.N : ℝ) * sqrtKN0 p.L p.m)
          * ((retained p.L p.m : ℝ) + (p.L : ℝ) * (7 : ℝ) ^ p.L) := by ring
    _ ≤ (2 * (p.N : ℝ)) * (2 * (p.L : ℝ) * (retained p.L p.m : ℝ)) :=
        mul_le_mul hband hsum (by positivity) (by positivity)
    _ = 4 * ((p.L : ℝ) * (p.N : ℝ) * (retained p.L p.m : ℝ)) := by ring

/-- The work for the boxes: `L` for each box of each tile, against the first term of `cost8p`. -/
theorem within8p_boxes : Within8p fun p t => p.L * (p.nB ^ 2 * (boxes p.L p.m t).card) := by
  refine ⟨4, by norm_num, fun p t h => ?_⟩
  have hs := h.sqrtKN0_pos
  have hM : (0 : ℝ) < (ThreeSumApsp.M p.L p.m : ℝ) := by
    rw [← sqrtKN0_sq]; positivity
  have htiles := Theorem30.tiles h.m_pos h.L_ge h.N_ge
  have hcount : ((boxes p.L p.m t).card : ℝ) ≤ ((p.m : ℝ) + 1) * tailBeta p.L p.m t := by
    unfold tailBeta
    exact_mod_cast lemma_29_count p.L p.m t h.L_ge h.t_le
  have hsecond : 0 ≤ (p.L : ℝ) * (p.N : ℝ) * (retained p.L p.m : ℝ) / sqrtKN0 p.L p.m := by
    positivity
  rw [cost8p_eq t p.N h.m_le]
  push_cast
  change (p.L : ℝ) * ((numBands p.L p.m p.N : ℝ) ^ 2 * _) ≤ _
  have hL0 : (0 : ℝ) ≤ p.L := Nat.cast_nonneg _
  have hkey : (p.L : ℝ) * ((numBands p.L p.m p.N : ℝ) ^ 2 * ((boxes p.L p.m t).card : ℝ))
      ≤ 4 * ((p.L : ℝ) * ((p.m : ℝ) + 1) * (tailBeta p.L p.m t / (ThreeSumApsp.M p.L p.m : ℝ))
        * (p.N : ℝ) ^ 2) := by
    calc (p.L : ℝ) * ((numBands p.L p.m p.N : ℝ) ^ 2 * ((boxes p.L p.m t).card : ℝ))
        ≤ (p.L : ℝ) * ((4 * (p.N : ℝ) ^ 2 / (ThreeSumApsp.M p.L p.m : ℝ))
            * (((p.m : ℝ) + 1) * tailBeta p.L p.m t)) := by
          gcongr
      _ = 4 * ((p.L : ℝ) * ((p.m : ℝ) + 1)
            * (tailBeta p.L p.m t / (ThreeSumApsp.M p.L p.m : ℝ)) * (p.N : ℝ) ^ 2) := by
          field_simp
  linarith

/-! ## The shared stage and the tiles -/

/-- **The pruned shared stage** runs within `cost8p`. -/
theorem within8p_sharedShapeP : Within8p fun p _ => Sec2.sharedShapeP p := by
  refine (((within8p_ret.const_mul 7).add (within8p_N_mul.const_mul 14)).add
    (within8p_bands.const_mul 7)).of_le fun p t h => ?_
  have hshape := sharedShapeP_le_ret p h.m_le
  have hN := h.one_le_N
  have hNL : (p.N + 1) * (p.L + 1) ≤ 2 * (p.N * (p.L + 1)) := by
    rw [Nat.add_one_mul p.N]
    have : p.L + 1 ≤ p.N * (p.L + 1) := Nat.le_mul_of_pos_left _ hN
    omega
  generalize Sec2.retW p.L p.m = R at *
  generalize p.nB * (R + p.L * 7 ^ p.L) = B at *
  generalize p.N * (p.L + 1) = X at *
  omega

/-- The time for a tile is `O(L)` for each box (as in `Time.lean`). -/
private theorem exists_tTile_le' : ∃ c : ℕ, ∀ L m t : ℕ, 1 ≤ L → m ≤ L →
    tTile L m t + 120 ≤ c * (L * (boxes L m t).card) := by
  refine ⟨2000, fun L m t hL1 hmL => ?_⟩
  have hcard := succ_le_card_boxes (t := t) hmL
  have hstarts : (m - t + 1) * (tNineFirst L + 120) ≤ (boxes L m t).card * (tNineFirst L + 120) :=
    Nat.mul_le_mul_right _ hcard
  rw [tTile_eq]
  simp only [tFillStep, tFillRound, tStarFirst, tHorner, tSumTen, tLookup, tInsert, tNineNext,
    tNewRoot, tNineFirst] at hstarts ⊢
  generalize (boxes L m t).card = b at *
  have hb : b ≤ L * b := Nat.le_mul_of_pos_left _ hL1
  rw [show b * (30 * L + 30 + 120) = 30 * (L * b) + 150 * b by ring] at hstarts
  rw [show b * (50 * L + 30 + (20 * L + 10) + (10 * (20 * L + 12 + 40) + 30) + (220 * L + 20)
    + (90 * L + 60) + 120) = 580 * (L * b) + 790 * b by ring]
  omega

/-- **The tries of all tiles** are built within `cost8p`. -/
theorem within8p_tAllTiles : Within8p fun p t => tAllTiles p.L p.m t p.nB := by
  obtain ⟨c, hc⟩ := exists_tTile_le'
  refine ((within8p_boxes.const_mul c).add (within8p_one.const_mul 30)).of_le fun p t h => ?_
  have htile := hc p.L p.m t h.L_pos h.m_le
  have hn : p.nB ≤ p.nB ^ 2 := Nat.le_self_pow (by norm_num) _
  calc tAllTiles p.L p.m t p.nB
      = p.nB ^ 2 * (tTile p.L p.m t + 80) + p.nB * 40 + 30 := by simp only [tAllTiles]; ring
    _ ≤ p.nB ^ 2 * (tTile p.L p.m t + 80) + p.nB ^ 2 * 40 + 30 := by gcongr
    _ = p.nB ^ 2 * (tTile p.L p.m t + 120) + 30 := by ring
    _ ≤ p.nB ^ 2 * (c * (p.L * (boxes p.L p.m t).card)) + 30 := by gcongr
    _ = c * (p.L * (p.nB ^ 2 * (boxes p.L p.m t).card)) + 30 * 1 := by ring

/-- **The preprocessing with pruned encodings** takes `O(cost8p)` steps.  `c` is the constant of the
shared stage. -/
theorem exists_tPreCore_le_p (c : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : Sec2.Par) (t : ℕ), Hyp30 p t →
    (tPreCore c p t : ℝ) ≤ C * cost8p p.L p.m t p.N :=
  (((within8p_sharedShapeP.const_mul c).add within8p_tAllTiles).add
    (within8p_one.const_mul 300)).of_le fun _ _ _ => le_of_eq (by simp [tPreCore])

end Light.Sec4
