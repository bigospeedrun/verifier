/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Batch.OSetup
public import Submission.ThreeSumApsp.Batch.OBound
public import Submission.ThreeSumApsp.Programs.Sec4.Theorem30.TimeOfBlock
public import Submission.ThreeSumApsp.Programs.Sec4.Theorem30.WordSize

/-!
# The batched counting oracle: the need stays polynomial

Every part of `oNeed [n, U, s, p]` is at most `Y^20` with `Y = 16^40 Q^40`,
`Q = (n + 1)(U + 1)(s + 1)(p + 1)`: every basic size (`n`, `U`, `s`, `p`, `k`, `L`, `b^L` for
`b ≤ 16`, `binom(L, m)`, …) is at most `Y`, because `4^m ≤ 16 Q` and `L = 20 m`, and everything
else is a short sum of short products of them (`oNeed_poly`).
-/

@[expose] public section

namespace Light.Batch

open ThreeSumApsp Light.Sec4

private theorem pw_mul {a b Y i j : ℕ} (ha : a ≤ Y ^ i) (hb : b ≤ Y ^ j) :
    a * b ≤ Y ^ (i + j) := by
  rw [pow_add]; exact Nat.mul_le_mul ha hb

private theorem pw_mono {a Y i j : ℕ} (hY : 1 ≤ Y) (ha : a ≤ Y ^ i) (hij : i ≤ j) : a ≤ Y ^ j :=
  ha.trans (Nat.pow_le_pow_right hY hij)

private theorem pw_add {a b Y i : ℕ} (hY : 2 ≤ Y) (ha : a ≤ Y ^ i) (hb : b ≤ Y ^ i) :
    a + b ≤ Y ^ (i + 1) := by
  rw [pow_succ]
  have := Nat.mul_le_mul_left (Y ^ i) hY
  omega

private theorem pw_one {a Y : ℕ} (h : a ≤ Y) : a ≤ Y ^ 1 := by rwa [pow_one]

private theorem four_pow_oM_le (s p : ℕ) : 4 ^ oM s p ≤ 16 * ((s + 1) * (p + 1)) := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp [oM]; omega
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp [oM]; omega
  have h := oD_le (s := s) (p := p) hs hp
  unfold oD at h
  have : 16 * s * p ≤ 16 * ((s + 1) * (p + 1)) := by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
  omega

/-- The three parts of the need are at most `Y^20`, for every `Y ≥ (16 Q)^40`. -/
private theorem oNeedAt_le (n U s p Y : ℕ)
    (hYQ : (16 * ((n + 1) * (U + 1) * (s + 1) * (p + 1))) ^ 40 ≤ Y) (hYbig : 2 ^ 30 ≤ Y) :
    (oNeedAt n U s p).word ≤ Y ^ 20 ∧ (oNeedAt n U s p).cells ≤ Y ^ 20 ∧
    (oNeedAt n U s p).depth ≤ Y ^ 20 := by
  generalize hQdef : (n + 1) * (U + 1) * (s + 1) * (p + 1) = Q at hYQ
  have hQ1 : 1 ≤ Q := Nat.one_le_iff_ne_zero.2 (by rw [← hQdef]; positivity)
  have hnQ : n + 1 ≤ Q := by
    rw [← hQdef]
    calc n + 1 = (n + 1) * 1 * 1 * 1 := by ring
      _ ≤ _ := by gcongr <;> omega
  have hUQ : U + 1 ≤ Q := by
    rw [← hQdef]
    calc U + 1 = 1 * (U + 1) * 1 * 1 := by ring
      _ ≤ _ := by gcongr <;> omega
  have hsQ : s + 1 ≤ Q := by
    rw [← hQdef]
    calc s + 1 = 1 * 1 * (s + 1) * 1 := by ring
      _ ≤ _ := by gcongr <;> omega
  have hpQ : p + 1 ≤ Q := by
    rw [← hQdef]
    calc p + 1 = 1 * 1 * 1 * (p + 1) := by ring
      _ ≤ _ := by gcongr <;> omega
  have hspQ : (s + 1) * (p + 1) ≤ Q := by
    rw [← hQdef]
    calc (s + 1) * (p + 1) = 1 * 1 * (s + 1) * (p + 1) := by ring
      _ ≤ _ := by gcongr <;> omega
  have hQY : Q ≤ Y :=
    ((Nat.le_mul_of_pos_left Q (by norm_num : 0 < 16)).trans
      (Nat.le_self_pow (by norm_num) _)).trans hYQ
  have hY1 : 1 ≤ Y := le_trans (by norm_num) hYbig
  have hY2 : 2 ≤ Y := le_trans (by norm_num) hYbig
  -- the key size
  set m := oM s p with hm
  set L := oL s p with hL
  have hLm : L = 20 * m := rfl
  have hX : 4 ^ m ≤ 16 * Q := (four_pow_oM_le s p).trans (Nat.mul_le_mul_left _ hspQ)
  have hX40 : (4 ^ m) ^ 40 ≤ Y :=
    (Nat.pow_le_pow_left hX 40).trans hYQ
  have hb : ∀ b, b ≤ 16 → b ^ L ≤ Y := fun b hb16 =>
    calc b ^ L ≤ 16 ^ L := Nat.pow_le_pow_left hb16 _
      _ = (4 ^ m) ^ 40 := by
          rw [hLm, show (16 : ℕ) = 4 ^ 2 by norm_num, ← pow_mul, ← pow_mul]; ring_nf
      _ ≤ Y := hX40
  -- the basic sizes
  have h2L := hb 2 (by norm_num)
  have h3L := hb 3 (by norm_num)
  have h7L := hb 7 (by norm_num)
  have h10L := hb 10 (by norm_num)
  have h11L := hb 11 (by norm_num)
  have hLY : L ≤ Y := (Nat.lt_two_pow_self).le.trans h2L
  have hmL : m ≤ L := by omega
  have hmY : m ≤ Y := hmL.trans hLY
  have h10m : 10 ^ m ≤ Y := (Nat.pow_le_pow_right (by norm_num) hmL).trans h10L
  have hch : L.choose m ≤ Y := (Nat.choose_le_two_pow _ _).trans h2L
  have hK0 : oK0 s p ≤ Y := (Nat.sqrt_le_self _).trans hch
  have hKK : oKK s p ≤ Y := (oKK_le s p).trans hch
  have hN0 : oN0 s p ≤ Y := (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le L m)).trans h3L
  have hN01 := one_le_oN0 s p
  have hD : oD s p ≤ Y := (Nat.le_self_pow (by norm_num) _).trans hX40
  have hk : oDig p ≤ Y := by
    have : oDig p ≤ p + 1 := by
      unfold oDig; have := Nat.sqrt_le_self (p - 1); omega
    omega
  have hTY : oT s p ≤ Y := (oT_le s p).trans hmY
  have hnY : n ≤ Y := by omega
  have hUY : U ≤ Y := by omega
  have hsY : s ≤ Y := by omega
  have hpY : p ≤ Y := by omega
  -- the derived sizes
  have hnk : n * oDig p ≤ Y ^ 2 := pw_mul (pw_one hnY) (pw_one hk)
  have hnb : oNb n s p ≤ Y ^ 3 := by
    have h1 : oNb n s p ≤ n * oDig p + oN0 s p := by
      unfold oNb
      rw [Nat.ceilDiv_eq_add_pred_div]
      have := Nat.div_le_self (n * oDig p + oN0 s p - 1) (oN0 s p)
      omega
    exact h1.trans (pw_add hY2 hnk (pw_mono hY1 (pw_one hN0) (by norm_num)))
  have hNP : oNP n s p ≤ Y ^ 4 := pw_mul hnb (pw_one hN0)
  have hNv : oNv n s p ≤ Y ^ 5 := by
    have := pw_mul (pw_one hK0) hNP
    unfold oNv; simpa [Nat.add_comm] using this
  have hprod : oProd n s ≤ Y ^ 2 := by
    have h1 : oProd n s ≤ n + s := by
      unfold oProd; rw [Nat.ceilDiv_eq_add_pred_div]
      have := Nat.div_le_self (n + s - 1) s
      omega
    exact h1.trans (pw_add hY2 (pw_one hnY) (pw_one hsY))
  have hbat : oBat n s p ≤ Y ^ 3 := by
    have h1 : oBat n s p ≤ oProd n s + oKK s p := by
      unfold oBat; rw [Nat.ceilDiv_eq_add_pred_div]
      have := Nat.div_le_self (oProd n s + oKK s p - 1) (oKK s p)
      omega
    exact h1.trans (pw_add hY2 hprod (pw_mono hY1 (pw_one hKK) (by norm_num)))
  have hSz : oSz n s p ≤ Y ^ 6 := pw_mul (pw_mul (pw_one hKK) hNP) (pw_one hD)
  have hZ : 2 ^ 20 * Y ^ 19 ≤ Y ^ 20 := by
    rw [pow_succ, Nat.mul_comm]; exact Nat.mul_le_mul_left _ (le_trans (by norm_num) hYbig)
  have hZbig : 2 ^ 30 ≤ Y ^ 19 := hYbig.trans (pw_mono hY1 (pw_one le_rfl) (by norm_num))
  have up : ∀ {a i}, a ≤ Y ^ i → i ≤ 19 → a ≤ Y ^ 19 := fun h hi => pw_mono hY1 h hi
  have up1 : ∀ {a}, a ≤ Y → a ≤ Y ^ 19 := fun h => up (pw_one h) (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · -- the word
    have t1 : 10 ^ m * (7 ^ L * 7 ^ L) ≤ Y ^ 19 :=
      up (pw_mul (pw_one h10m) (pw_mul (pw_one h7L) (pw_one h7L))) (by norm_num)
    have t2 : 7 ^ (L + 1) ≤ Y ^ 19 := by
      rw [pow_succ]; exact up (pw_mul (pw_one h7L) (pw_one (by omega : 7 ≤ Y))) (by norm_num)
    have t3 : 10 ^ (L + 1) ≤ Y ^ 19 := by
      rw [pow_succ]; exact up (pw_mul (pw_one h10L) (pw_one (by omega : 10 ≤ Y))) (by norm_num)
    have t4 : 4 * s * p ≤ Y ^ 19 :=
      up (pw_mul (pw_mul (pw_one (by omega : 4 ≤ Y)) (pw_one hsY)) (pw_one hpY)) (by norm_num)
    have t5 : 3 ^ (L - m) ≤ Y ^ 19 := up1 hN0
    have t6 : (oNb n s p + 1) * (oKK s p * oN0 s p + oN0 s p + 1) ≤ Y ^ 19 := by
      have a1 : oNb n s p + 1 ≤ Y ^ 4 := pw_add hY2 hnb (pw_mono hY1 (pw_one hY1) (by norm_num))
      have a2 : oKK s p * oN0 s p ≤ Y ^ 2 := pw_mul (pw_one hKK) (pw_one hN0)
      have a3 : oKK s p * oN0 s p + oN0 s p ≤ Y ^ 3 :=
        pw_add hY2 a2 (pw_mono hY1 (pw_one hN0) (by norm_num))
      have a4 : oKK s p * oN0 s p + oN0 s p + 1 ≤ Y ^ 4 :=
        pw_add hY2 a3 (pw_mono hY1 (pw_one hY1) (by norm_num))
      exact up (pw_mul a1 a4) (by norm_num)
    have t7 : (oProd n s + oKK s p + 1) * (s + 1) ≤ Y ^ 19 := by
      have a1 : oProd n s + oKK s p ≤ Y ^ 3 :=
        pw_add hY2 hprod (pw_mono hY1 (pw_one hKK) (by norm_num))
      have a2 : oProd n s + oKK s p + 1 ≤ Y ^ 4 :=
        pw_add hY2 a1 (pw_mono hY1 (pw_one hY1) (by norm_num))
      have a3 : s + 1 ≤ Y ^ 2 := pw_add hY2 (pw_one hsY) (pw_one hY1)
      exact up (pw_mul a2 a3) (by norm_num)
    have t8 : n * n ≤ Y ^ 19 := up (pw_mul (pw_one hnY) (pw_one hnY)) (by norm_num)
    have t9 : oK0 s p * oN0 s p ≤ Y ^ 19 := up (pw_mul (pw_one hK0) (pw_one hN0)) (by norm_num)
    have := up hnk (by norm_num); have := up hnb (by norm_num); have := up hNP (by norm_num)
    have := up hNv (by norm_num); have := up hprod (by norm_num); have := up hbat (by norm_num)
    have := up hSz (by norm_num); have := up1 h2L; have := up1 hch; have := up1 hD
    have := up1 hmY; have := up1 hLY; have := up1 hUY; have := up1 hpY; have := up1 hnY
    have := up1 hsY; have := up1 hKK; have := up1 hN0
    show oWordSum n U s p ≤ Y ^ 20
    unfold oWordSum
    rw [← hL, ← hm]
    omega
  · -- the cells
    set P := oPar n s p with hP
    have hPL : P.L = L := rfl
    have hPm : P.m = m := rfl
    have hPN : P.N = oNv n s p := rfl
    have hPKK : P.KK = oKK s p := rfl
    have hPD : P.D = oD s p := rfl
    have hPT : P.T = 10 ^ L := rfl
    have hPS7 : P.S7 = 7 ^ L := rfl
    have hPLo : P.Lo ≤ L := Nat.sub_le _ _
    have hband : bandSize P.L P.m ≤ Y ^ 2 := pw_mul (pw_one hK0) (pw_one hN0)
    have hnB : P.nB ≤ Y ^ 6 := by
      have h1 : P.nB ≤ P.N + bandSize P.L P.m := by
        show numBands P.L P.m P.N ≤ _
        unfold numBands
        have := Nat.div_le_self (P.N + bandSize P.L P.m - 1) (bandSize P.L P.m)
        omega
      rw [hPN] at h1
      exact h1.trans (pw_add hY2 hNv (pw_mono hY1 hband (by norm_num)))
    have hcard : (boxes P.L P.m (oT s p)).card ≤ Y := (card_boxes_le _ _ _).trans h11L
    have htop := top_sub_eq P (oT s p) 0
    simp only [Nat.sub_zero] at htop
    have hsh : P.sharedEnd 0 = 32 + (P.L + 1) + (P.L + 1) + (P.L + 1) + (P.L + 1) + (P.L + 2)
        + 70 + 70 + P.KK * P.L + P.N + P.N + P.N * P.Lo + P.D * P.m + P.nB * P.T + P.nB * P.T
        + P.S7 + P.S7 := by
      simp only [Sec2.Par.sharedEnd, Sec2.Par.aZS, Sec2.Par.aARR, Sec2.Par.aENCB, Sec2.Par.aENCA,
        Sec2.Par.aDIG4, Sec2.Par.aDIG3, Sec2.Par.aBLOCK, Sec2.Par.aBAND, Sec2.Par.aMASK,
        Sec2.Par.aPSI, Sec2.Par.aPHI, Sec2.Par.aPAS, Sec2.Par.aP10, Sec2.Par.aP7, Sec2.Par.aP4,
        Sec2.Par.aP3]
    rw [hsh, hPL, hPm, hPN, hPKK, hPD, hPT, hPS7] at htop
    have c1 : oKK s p * L ≤ Y ^ 19 := up (pw_mul (pw_one hKK) (pw_one hLY)) (by norm_num)
    have c2 : oNv n s p * P.Lo ≤ Y ^ 19 :=
      up (pw_mul hNv (pw_one (hPLo.trans hLY))) (by norm_num)
    have c3 : oD s p * m ≤ Y ^ 19 := up (pw_mul (pw_one hD) (pw_one hmY)) (by norm_num)
    have c4 : P.nB * 10 ^ L ≤ Y ^ 19 := up (pw_mul hnB (pw_one h10L)) (by norm_num)
    have c5 : P.nB * P.nB * (11 * (1 + L * (boxes L m (oT s p)).card)) ≤ Y ^ 19 := by
      have a1 : L * (boxes L m (oT s p)).card ≤ Y ^ 2 := pw_mul (pw_one hLY) (pw_one hcard)
      have a2 : 1 + L * (boxes L m (oT s p)).card ≤ Y ^ 3 :=
        pw_add hY2 (pw_mono hY1 (pw_one hY1) (by norm_num)) a1
      have a3 : 11 * (1 + L * (boxes L m (oT s p)).card) ≤ Y ^ 4 := by
        have := pw_mul (pw_one (by omega : 11 ≤ Y)) a2
        simpa [Nat.add_comm] using this
      exact up (pw_mul (pw_mul hnB hnB) a3) (by norm_num)
    have c6 : P.nB * P.nB ≤ Y ^ 19 := up (pw_mul hnB hnB) (by norm_num)
    have c7 : Nat.log 2 (U + 3 * p + 1) ≤ U + 3 * p + 1 := Nat.log_le_self _ _
    have c8 : oDig p * oDig p ≤ Y ^ 19 := up (pw_mul (pw_one hk) (pw_one hk)) (by norm_num)
    have t8 : n * n ≤ Y ^ 19 := up (pw_mul (pw_one hnY) (pw_one hnY)) (by norm_num)
    have := up hNP (by norm_num); have := up hNv (by norm_num); have := up hSz (by norm_num)
    have := up1 h7L; have := up1 h10L; have := up1 hLY; have := up1 hmY; have := up1 hk
    have := up1 hUY; have := up1 hpY
    show oCells n U s p ≤ Y ^ 20
    unfold oCells
    rw [htop]
    simp only [oB0, oaY, oaX, oaZL, oaZH, oaDK, oaRV, oaRS, oaHK, oaNL, oaRNAB, oaRNBC]
    rw [← hL]
    omega
  · -- the depth
    show oL s p + 8 ≤ Y ^ 20
    have := up1 hLY
    omega

/-- The product of the first four parameters is at most the product of all. -/
private theorem q4_le_prod (ps : List ℕ) :
    (ps.getD 0 0 + 1) * (ps.getD 1 0 + 1) * (ps.getD 2 0 + 1) * (ps.getD 3 0 + 1) ≤
      (ps.map (· + 1)).prod := by
  rcases ps with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨e, rest⟩⟩⟩⟩
  · simp
  · simp
  · simp
  · simp only [List.getD_cons_zero, List.getD_cons_succ, List.getD_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, Nat.zero_add, Nat.mul_one]
    rw [Nat.mul_assoc]
  · have h1 : 1 ≤ (rest.map (· + 1)).prod := List.prod_pos fun x hx => by
      obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
      exact Nat.succ_pos y
    simp only [List.getD_cons_zero, List.getD_cons_succ, List.map_cons, List.prod_cons]
    calc (a + 1) * (b + 1) * (c + 1) * (e + 1)
          = (a + 1) * ((b + 1) * ((c + 1) * ((e + 1) * 1))) := by ring
      _ ≤ (a + 1) * ((b + 1) * ((c + 1) * ((e + 1) * (rest.map (· + 1)).prod))) := by gcongr

/-- **The need of the batched oracle is polynomially bounded** in its parameters `[n, U, s, p]`. -/
theorem oNeed_poly : PolyNeedN oNeed := by
  refine ⟨3200, 800, fun ps => ?_⟩
  have hQ := q4_le_prod ps
  have hQ1 : 1 ≤ (ps.getD 0 0 + 1) * (ps.getD 1 0 + 1) * (ps.getD 2 0 + 1) * (ps.getD 3 0 + 1) :=
    Nat.one_le_iff_ne_zero.2 (by positivity)
  have hbig : 2 ^ 30 ≤ (16 * ((ps.getD 0 0 + 1) * (ps.getD 1 0 + 1) * (ps.getD 2 0 + 1) *
      (ps.getD 3 0 + 1))) ^ 40 := by
    calc 2 ^ 30 ≤ 2 ^ (4 * 40) := Nat.pow_le_pow_right (by norm_num) (by norm_num)
      _ = 16 ^ 40 := by rw [pow_mul]; norm_num
      _ ≤ _ := Nat.pow_le_pow_left (Nat.le_mul_of_pos_right 16 hQ1) _
  obtain ⟨h1, h2, h3⟩ := oNeedAt_le (ps.getD 0 0) (ps.getD 1 0) (ps.getD 2 0) (ps.getD 3 0) _
    le_rfl hbig
  generalize (ps.getD 0 0 + 1) * (ps.getD 1 0 + 1) * (ps.getD 2 0 + 1) * (ps.getD 3 0 + 1) = Q
    at hQ h1 h2 h3
  have hY : ((16 * Q) ^ 40) ^ 20 ≤ polyBound 3200 800 ps := by
    unfold polyBound
    rw [← pow_mul, mul_pow, show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul,
      show 4 * (40 * 20) = 3200 by norm_num, show 40 * 20 = 800 by norm_num]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hQ _)
  exact ⟨h1.trans hY, h2.trans hY, h3.trans hY⟩

end Light.Batch
