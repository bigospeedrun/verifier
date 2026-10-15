/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Batch.OSpecs

/-!
# The batched counting oracle: the tables

Proofs of the specifications (`OSpecs`) of the small procedures 76 to 81: powNat, residTab,
smallTab, rowTab, divTab and zTab.
-/

@[expose] public section

namespace Light.Batch

open ThreeSumApsp ThreeSumApsp.Batch Light.Sec4

variable {lim : Limits} {P : Program}

/-! ## powNat -/

theorem powNat_ok (hP : P[pPowNat]? = some powNatBody) : PowNatSpec lim P := by
  intro b e μ d hb hword
  refine .of_body hP ?_
  unfold tPowNat
  push_cast at hword
  have hpe : ∀ j ≤ e, b ^ j ≤ b ^ e := fun j hj => Nat.pow_le_pow_right hb hj
  have h0 : (0 : ℤ) ≤ (b : ℤ) ^ e := by positivity
  light_set (1 : ℕ)
  refine Ends.next _ (Ends.for (fun j σ => σ = ⟨frame [b, e, j, (b ^ j : ℕ)], μ⟩) e 4
    ?start ?round ?done ?bound (hT := le_rfl))
  case start => simp [update_frame_setLocal]
  case bound =>
    rintro j _ - - rfl
    simp
  case round =>
    rintro j _ hj - rfl
    have h1 : b ^ (j + 1) ≤ b ^ e := hpe _ hj
    have h1Z : ((b ^ (j + 1) : ℕ) : ℤ) ≤ ((b ^ e : ℕ) : ℤ) := by exact_mod_cast h1
    rw [pow_succ] at h1Z
    push_cast at h1Z
    have h2 : (0 : ℤ) ≤ (b : ℤ) ^ j * b := by positivity
    refine Ends.setTo ((b : ℤ) ^ j * b) ?_
    simp [update_frame_setLocal, pow_succ]
  case done =>
    rintro _ - rfl
    exact Ends.setTo (b ^ e : ℕ) (by simp)

/-! ## A pass that writes a row at an address given by an expression -/

/-- The loop "for c < n: mem[a + c] := e", where a gives the address dst + m and round j writes
f (m + j): the cells from dst + m are written as `wrote μ dst f` goes on from m to m + n. -/
theorem Ends.passAt {d c x n m dst T : ℕ} {a e : Expr} {loc μ ν : ℕ → ℤ} {Q : State → Prop}
    (f : ℕ → ℤ) (hν : ν = wrote μ dst f m)
    (round : ∀ j < n,
      a.Gives lim ⟨Function.update loc c j, wrote μ dst f (m + j)⟩ ((dst + m : ℕ) : ℤ) ∧
      e.Gives lim ⟨Function.update loc c j, wrote μ dst f (m + j)⟩ (f (m + j)))
    (done : Q ⟨Function.update loc c n, wrote μ dst f (m + n)⟩)
    (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + m + n ≤ lim.space) (hlen : loc x = n)
    (hx : x ≠ c := by decide)
    (hT : n * (a.cost + e.cost + 11) + 6 ≤ T := by light_time) :
    Ends lim P d (Stmt.for c (v x) (.store (a +' v c) e)) ⟨loc, ν⟩ T Q := by
  subst hν
  refine Ends.forMem (fun j μ' => μ' = wrote μ dst f (m + j)) n ((a +' v c).cost + e.cost + 1)
    (by simp)
    (fun j μ' hj hμ' => ?_) (fun μ' h => by rw [h]; exact done)
    (fun j μ' _ _ => ⟨trivial, by simp [Function.update_of_ne hx, hlen]⟩) (by omega)
    (le_trans (le_of_eq (by simp only [Expr.cost]; ring)) hT)
  subst hμ'
  obtain ⟨⟨has, hav⟩, hes, hev⟩ := round j hj
  have hval : (a +' v c).val ⟨Function.update loc c j, wrote μ dst f (m + j)⟩ =
      ((dst + (m + j) : ℕ) : ℤ) := by
    simp only [Expr.val, Op.eval, hav, Function.update_self]
    push_cast
    ring
  refine Ends.store ⟨has, trivial, ?_⟩ hes ?_ le_rfl ⟨rfl, ?_⟩
  · change |(a +' v c).val _| ≤ lim.word
    rw [hval, abs_of_nonneg (by positivity)]
    omega
  · rw [hval]
    exact ⟨by positivity, by omega⟩
  · simp only
    rw [hval, Int.toNat_natCast, hev, wrote_succ, Nat.add_assoc]

/-! ## divTab -/

theorem divTab_ok (hP : P[pDivTab]? = some divTabBody) : DivTabSpec lim P := by
  intro dst kk μ d hstd hspace
  have hw := hstd.space_le
  refine .of_body hP ?_
  unfold tDivTab
  have hkk : kk ≤ kk * kk := Nat.le_mul_self kk
  refine Ends.for (fun h σ => σ.loc 0 = dst ∧ σ.loc 1 = kk ∧
      σ.mem = wrote μ dst (fun z => ((z / kk : ℕ) : ℤ)) (h * kk)) kk (kk * 17 + 6)
    ?start ?round ?done ?bound
  case start => simp [wrote_zero]
  case bound =>
    rintro j _ - - ⟨-, h1, -⟩
    simp [h1]
  case done =>
    rintro ⟨loc, μ'⟩ - ⟨-, -, rfl⟩
    dsimp only
    refine ⟨seg_wrote (by simp) fun i hi => ?_, sameOutside_wrote le_rfl⟩
    simp
  case round =>
    rintro h ⟨loc, μ'⟩ hh hc ⟨h0, h1, rfl⟩
    simp only at h0 h1 hc
    have hle : h * kk + kk ≤ kk * kk := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hh
    have hleZ : ((h * kk : ℕ) : ℤ) + kk ≤ ((kk * kk : ℕ) : ℤ) := by exact_mod_cast hle
    push_cast at hleZ
    have hdiv : ∀ o < kk, (h * kk + o) / kk = h := fun o ho => by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt ho, Nat.zero_add]
    refine Ends.passAt (m := h * kk) (n := kk) (x := 1) _ rfl (fun o ho => ?_) ?_ hw
      (by nlinarith) h1
    · refine ⟨?_, ?_⟩
      · light_side [h0, h1, hc]
      · simp [hc, hdiv o ho]
    · refine ⟨by simp [hc], by simp [h0], by simp [h1], ?_⟩
      simp only
      congr 1
      ring

/-! ## rowTab -/

theorem rowTab_ok (hP : P[pRowTab]? = some rowTabBody) : RowTabSpec lim P := by
  intro dst nb N0 Mul μ d hstd hN0 hspace hword
  have hw := hstd.space_le
  refine .of_body hP ?_
  unfold tRowTab
  have hnb : nb + 1 ≤ (nb + 1) * (Mul + N0 + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hN0w : N0 ≤ (nb + 1) * (Mul + N0 + 1) := by nlinarith
  refine Ends.for (fun i σ => σ.loc 0 = dst ∧ σ.loc 2 = N0 ∧ σ.loc 3 = Mul ∧ σ.loc 1 = nb ∧
      σ.mem = wrote μ dst (fun R => ((R / N0 * Mul + R % N0 : ℕ) : ℤ)) (i * N0)) nb (N0 * 21 + 6)
    ?start ?round ?done ?bound
  case start => simp [wrote_zero]
  case bound =>
    rintro j _ - - ⟨-, -, -, h1, -⟩
    simp [h1]
  case done =>
    rintro ⟨loc, μ'⟩ - ⟨-, -, -, -, rfl⟩
    dsimp only
    refine ⟨seg_wrote (by simp) fun i hi => ?_, sameOutside_wrote le_rfl⟩
    simp
  case round =>
    rintro i ⟨loc, μ'⟩ hi hc ⟨h0, h2, h3, h1, rfl⟩
    simp only at h0 h1 h2 h3 hc
    have hle : i * N0 + N0 ≤ nb * N0 := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hi
    have hleZ : ((i * N0 : ℕ) : ℤ) + N0 ≤ ((nb * N0 : ℕ) : ℤ) := by exact_mod_cast hle
    have hiM : i * Mul ≤ nb * Mul := Nat.mul_le_mul_right _ hi.le
    have hval : i * Mul + N0 ≤ (nb + 1) * (Mul + N0 + 1) := by nlinarith
    have hvalZ : ((i * Mul : ℕ) : ℤ) + N0 ≤ (((nb + 1) * (Mul + N0 + 1) : ℕ) : ℤ) := by
      exact_mod_cast hval
    push_cast at hleZ hvalZ hword
    have hdiv : ∀ o < N0, (i * N0 + o) / N0 = i := fun o ho => by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt ho, Nat.zero_add]
    have hmod : ∀ o < N0, (i * N0 + o) % N0 = o := fun o ho => by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ho]
    refine Ends.passAt (m := i * N0) (n := N0) (x := 2) _ rfl (fun o ho => ?_) ?_ hw
      (by omega) h2
    · refine ⟨?_, ?_⟩
      · light_side [h0, h2, hc]
      · refine ⟨?_, ?_⟩
        · light_side [h3, hc]
        · simp [hc, h3, hdiv o ho, hmod o ho]
    · refine ⟨by simp [hc], by simp [h0], by simp [h2], by simp [h3], by simp [h1], ?_⟩
      simp only
      congr 1
      ring

/-! ## zTab -/

theorem zTab_ok (hP : P[pZTab]? = some zTabBody) : ZTabSpec lim P := by
  intro zh zl rn dk kk RN μ d hstd hk hrn hdk hlt a1 a2 a3 a4 s1 s2 s3 s4
  have hw := hstd.space_le
  refine .of_body hP ?_
  unfold tZTab
  set len := RN.length with hlen
  have hx : ∀ j < len, RN.getD j 0 < kk * kk := fun j hj =>
    hlt _ (by rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj)
  have hrd : ∀ j < len, μ (rn + j) = ((RN.getD j 0 : ℕ) : ℤ) := fun j hj => hrn.read hj
  have hdd : ∀ z < kk * kk, μ (dk + z) = ((z / kk : ℕ) : ℤ) := fun z hz => by
    rw [hdk.getElem (by simpa using hz)]
    simp
  have hmd : ∀ x : ℕ, (x : ℤ) - (kk : ℤ) * ((x / kk : ℕ) : ℤ) = ((x % kk : ℕ) : ℤ) := fun x => by
    have := Nat.mod_add_div x kk
    have hc : (((x % kk : ℕ) : ℤ) + ((kk * (x / kk) : ℕ) : ℤ)) = (x : ℤ) := by exact_mod_cast this
    push_cast at hc ⊢
    linarith
  obtain ⟨f1, hf1⟩ : ∃ f : ℕ → ℤ, ∀ q, f q = ((RN.getD q 0 / kk : ℕ) : ℤ) := ⟨_, fun _ => rfl⟩
  obtain ⟨f2, hf2⟩ : ∃ f : ℕ → ℤ, ∀ q, f q = ((RN.getD q 0 % kk : ℕ) : ℤ) := ⟨_, fun _ => rfl⟩
  refine Ends.next _ (Ends.pass (x := 4) (y := 0) (n := len) (dst := zh) f1 (fun j hj => ?_) ?_ hw
    (by omega) (by simp [hlen]) (by simp) (hT := le_rfl))
  · -- zh[q] := dk[rn[q]]
    have hxj := hx j hj
    have e1 : wrote μ zh f1 j (rn + j) = ((RN.getD j 0 : ℕ) : ℤ) := by
      rw [wrote_rest (by omega), hrd j hj]
    have e2 : wrote μ zh f1 j (dk + RN.getD j 0) = ((RN.getD j 0 / kk : ℕ) : ℤ) := by
      rw [wrote_rest (by omega), hdd _ hxj]
    have hf := hf1 j
    generalize RN.getD j 0 / kk = q at e2 hf
    generalize RN.getD j 0 = x at e1 e2 hxj
    light_side [e1, e2, hf]
  -- zl[q] := rn[q] - k zh[q]
  refine Ends.pass (x := 4) (y := 1) (n := len) (dst := zl) f2 (fun j hj => ?_) ?_ hw
    (by omega) (by simp [hlen]) (by simp)
  · have hxj := hx j hj
    have e3 : wrote (wrote μ zh f1 len) zl f2 j (rn + j) = ((RN.getD j 0 : ℕ) : ℤ) := by
      rw [wrote_rest (by omega), wrote_rest (by omega), hrd j hj]
    have e4 : wrote (wrote μ zh f1 len) zl f2 j (zh + j) = ((RN.getD j 0 / kk : ℕ) : ℤ) := by
      rw [wrote_rest (by omega), wrote_done hj, hf1]
    have hm := hmd (RN.getD j 0)
    have hq : kk * (RN.getD j 0 / kk) ≤ RN.getD j 0 := Nat.mul_div_le _ _
    have hf := hf2 j
    generalize RN.getD j 0 / kk = q at e4 hm hq
    generalize RN.getD j 0 % kk = r at hm hf
    generalize RN.getD j 0 = x at e3 hm hq hxj
    have hqZ : ((kk * q : ℕ) : ℤ) ≤ (x : ℤ) := by exact_mod_cast hq
    push_cast at hqZ
    light_side [e3, e4, hf, hm]
  · refine ⟨?_, ?_, fun b hb => ?_⟩
    · have g1 : SegN (wrote μ zh f1 len) zh (RN.map (· / kk)) := by
        refine seg_wrote (by simp [hlen]) fun i hi => ?_
        rw [hf1, List.getD_eq_getElem _ _ (by simpa using hi : i < RN.length)]
        simp
      exact g1.of_sameOutside (sameOutside_wrote le_rfl) (by simp only [List.length_map]; omega)
    · refine seg_wrote (by simp [hlen]) fun i hi => ?_
      rw [hf2, List.getD_eq_getElem _ _ (by simpa using hi : i < RN.length)]
      simp
    · simp only
      rw [wrote_rest hb.2, wrote_rest hb.1]

/-! ## residTab and smallTab -/

theorem emodTime_mono {a b M : ℕ} (h : a ≤ b) : emodTime a M ≤ emodTime b M := by
  have := Nat.size_le_size (Nat.div_le_div_right (c := M) h)
  simp only [emodTime, emodRounds]
  omega

theorem natAbs_le_of_abs_le {x : ℤ} {V : ℕ} (h : |x| ≤ (V : ℤ)) : x.natAbs ≤ V := by
  have := Int.natCast_natAbs x
  omega

/-- The residue of an integer, as an integer. -/
theorem emod_eq_resid {p : ℕ} (hp : 1 ≤ p) (x : ℤ) : x % (p : ℤ) = ((resid p x : ℕ) : ℤ) := by
  rw [resid, Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))]

theorem residTab_ok (hP : P[pResidTab]? = some residTabBody) (hE : P[pEmod]? = some emodBody) :
    ResidTabSpec lim P := by
  intro dst src W sgn p V fr μ d hsgn hW hV F hdst hsrc hap hdepth
  light_facts F
  refine .of_body hP ?_
  unfold tResidTab
  set len := W.length with hlen
  have hrd : ∀ j < len, μ (src + j) = W.getD j 0 := fun j hj => hW.getD hj 0
  have hwV : ∀ j < len, |W.getD j 0| ≤ V := fun j hj =>
    hV _ (by rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj)
  have hsw : ∀ w : ℤ, |sgn * w| = |w| := by rcases hsgn with rfl | rfl <;> simp
  refine Ends.forShape (fun j s μ' => ⟨frame [dst, src, len, sgn, p, fr, j, s], μ'⟩)
    (fun j μ' => (∀ i < j, μ' (dst + i) = ((resid p (sgn * W.getD i 0) : ℕ) : ℤ)) ∧
      SameOn (fun b => b < fr ∧ Outside dst len b) μ μ')
    len (emodTime V p + 15) (0 : ℤ) ⟨fun i hi => absurd hi (by omega), SameOn.refl⟩ ?round ?done
    (first := by
      rw [update_frame_setLocal]
      exact congrArg (State.mk · μ) (frame_append_zeros _ 1).symm)
  case round =>
    rintro j s μ' hj ⟨hdone, hsame⟩
    have hread : μ' (src + j) = W.getD j 0 := by rw [hsame _ ⟨by omega, by omega⟩, hrd j hj]
    have hx := hwV j hj
    rw [← hsw (W.getD j 0)] at hx
    have htime : emodTime (sgn * W.getD j 0).natAbs p ≤ emodTime V p :=
      emodTime_mono (natAbs_le_of_abs_le hx)
    have hxa := abs_le.1 hx
    generalize hwd : W.getD j 0 = w at *
    light_call (emod_meets hE F hx) using hread with r μ₁ ⟨rfl, hkept⟩
    light_store (dst + j) ((sgn * w) % (p : ℤ))
    refine ⟨_, _, rfl, fun i hi => ?_, fun b hb => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
      · rw [Function.update_of_ne (by omega), hkept _ (by omega), hdone i h]
      · rw [Function.update_self, emod_eq_resid F.mod_pos, hwd]
    · rw [Function.update_of_ne (by omega), hkept _ hb.1, hsame _ hb]
  case done =>
    rintro s μ' ⟨hdone, hsame⟩
    refine ⟨fun i hi => ?_, hsame⟩
    have hi' : i < W.length := by simpa using hi
    dsimp only
    rw [List.getElem_map, List.getElem_map, hdone i hi', List.getD_eq_getElem _ _ hi']

theorem smallTab_ok (hP : P[pSmallTab]? = some smallTabBody) (hE : P[pEmod]? = some emodBody) :
    SmallTabSpec lim P := by
  intro dst len mul add p V fr μ d hval hmul hadd hlenV F hdst hdepth
  light_facts F
  refine .of_body hP ?_
  unfold tSmallTab
  refine Ends.forShape (fun j s μ' => ⟨frame [dst, len, mul, add, p, fr, j, s], μ'⟩)
    (fun j μ' => (∀ i < j, μ' (dst + i) = ((resid p ((i : ℤ) * mul + add) : ℕ) : ℤ)) ∧
      SameOn (fun b => b < fr ∧ Outside dst len b) μ μ')
    len (emodTime V p + 15) (0 : ℤ) ⟨fun i hi => absurd hi (by omega), SameOn.refl⟩ ?round ?done
    (first := by
      rw [update_frame_setLocal]
      exact congrArg (State.mk · μ) (frame_append_zeros _ 1).symm)
  case round =>
    rintro j s μ' hj ⟨hdone, hsame⟩
    have hx := hval j hj
    have htime : emodTime ((j : ℤ) * mul + add).natAbs p ≤ emodTime V p :=
      emodTime_mono (natAbs_le_of_abs_le hx)
    have hxa := abs_le.1 hx
    have hab := abs_le.1 hadd
    light_call (emod_meets hE F hx) with r μ₁ ⟨rfl, hkept⟩
    light_store (dst + j) (((j : ℤ) * mul + add) % (p : ℤ))
    refine ⟨_, _, rfl, fun i hi => ?_, fun b hb => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
      · rw [Function.update_of_ne (by omega), hkept _ (by omega), hdone i h]
      · rw [Function.update_self, emod_eq_resid F.mod_pos]
    · rw [Function.update_of_ne (by omega), hkept _ hb.1, hsame _ hb]
  case done =>
    rintro s μ' ⟨hdone, hsame⟩
    have hL : ∀ l : List ℕ, (do let a ← l; pure (a : ℤ) : List ℤ) = l.map (fun a : ℕ => (a : ℤ)) := by
      intro l
      induction l with
      | nil => rfl
      | cons x l ih => simp [List.map_eq_flatMap]
    dsimp only
    rw [hL, List.map_map]
    refine ⟨fun i hi => ?_, hsame⟩
    have hi' : i < len := by simpa using hi
    rw [List.getElem_map, List.getElem_map, List.getElem_range, hdone i hi']
    rfl

end Light.Batch
