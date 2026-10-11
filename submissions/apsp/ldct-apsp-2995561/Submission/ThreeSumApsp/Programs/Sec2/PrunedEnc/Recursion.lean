/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Programs.Sec2.PrunedEnc.Contracts
public import Submission.ThreeSumApsp.Programs.Sec2.Theorem5.Encode.Recursion

/-!
# The pruned encoding, by the recursion of Section 2.4.1

The pruned encoder is `encode` with one more argument, the budget r of digits 9.  At level `L + 1`
the terms 0, …, 8 are treated as in `encode`, with the same budget for the recursive call; the term
number 9 (the term P₀ of Schönhage's identity) is treated only if `0 < r`, with the budget `r - 1`.
So the leaves whose code has more than r digits 9 are not written.  Before the term 9 the budget is
cut down to the level: a budget of more than `L` nines prunes nothing at level `L`, and so the
budget `r - 1` that is passed on is at most `L` and fits in a word.

* `encPTime L r` is the number of steps, and `encPTime_le` bounds it by `O(retW L r)`.
* `encodePTerm_spec` treats the two calls for one term, `encodeP_leaf` the level 0, `encodeP_node`
  the levels `L + 1`, and `encodeP_spec` is the induction.
-/

@[expose] public section

namespace Light.Sec2

open Finset ThreeSumApsp

namespace EncodeP

/-- The local variables of encodeP: the arguments L, src, out, scr, tab, p7, p10, r; the lengths
7^{L-1} and 10^{L-1}; the number of the term; the result of a call, which is not used. -/
abbrev Level : ℕ := 0
@[inherit_doc Level] abbrev Src : ℕ := 1
@[inherit_doc Level] abbrev Out : ℕ := 2
@[inherit_doc Level] abbrev Scr : ℕ := 3
@[inherit_doc Level] abbrev Table : ℕ := 4
@[inherit_doc Level] abbrev Pow7 : ℕ := 5
@[inherit_doc Level] abbrev Pow10 : ℕ := 6
@[inherit_doc Level] abbrev Budget : ℕ := 7
@[inherit_doc Level] abbrev Len7 : ℕ := 8
@[inherit_doc Level] abbrev Len10 : ℕ := 9
@[inherit_doc Level] abbrev TermNo : ℕ := 10
@[inherit_doc Level] abbrev Res : ℕ := 11

end EncodeP

open EncodeP

/-- The two calls for the term number TermNo, the recursive one with the budget b. -/
def encodePTerm (pS pE : ℕ) (b : Expr) : Stmt :=
  .call pS [v Src, v Scr, v Len7, v TermNo, v Table] Res ;;
  .call pE [v Level -' k 1, v Scr, v Out +' v TermNo *' v Len10, v Scr +' v Len7, v Table, v Pow7,
    v Pow10, b] Res

/-- encodeP(L, src, out, scr, tab, p7, p10, r).  The loop over the terms 0, …, 8 leaves 9 in
TermNo; the term 9 is treated only if `0 < r`, with the budget `min(r, L) - 1`.  pS and pE are the
numbers that the procedures encStep and encodeP have in the program. -/
def encodePBody (pS pE : ℕ) : Stmt :=
  .ite (v Level =' k 0)
    (.store (v Out) (M (v Src)))
    (.set Len7 (M (v Pow7 +' v Level -' k 1)) ;;
     .set Len10 (M (v Pow10 +' v Level -' k 1)) ;;
     .for TermNo (k 9) (encodePTerm pS pE (v Budget)) ;;
     .ite (k 0 <' v Budget)
       (.ite (v Level <' v Budget) (.set Budget (v Level)) .skip ;;
        encodePTerm pS pE (v Budget -' k 1))
       .skip)

/-! ## The number of steps -/

/-- The number of steps of `encodeP`: at level `L + 1`, nine times the two calls for a term with the
same budget, and if `0 < r` once more the two calls with the budget `min (r - 1) L`. -/
def encPTime : ℕ → ℕ → ℕ
  | 0, _ => 8
  | L + 1, 0 => 100 + 9 * (27 + tEncStep (7 ^ L) + encPTime L 0)
  | L + 1, r + 1 => 106 + 9 * (27 + tEncStep (7 ^ L) + encPTime L (r + 1)) +
      (27 + tEncStep (7 ^ L) + encPTime L (min r L))

/-- The time of the two calls for one term, with the budget `r` for the recursive call. -/
def tTermP (L r : ℕ) : ℕ := 27 + tEncStep (7 ^ L) + encPTime L r

/-- The number of steps at level `L + 1` with no nine allowed. -/
theorem encPTime_succ_zero (L : ℕ) : encPTime (L + 1) 0 = 100 + 9 * tTermP L 0 := rfl

/-- The number of steps at level `L + 1` with `r + 1` nines allowed. -/
theorem encPTime_succ_succ (L r : ℕ) :
    encPTime (L + 1) (r + 1) = 106 + 9 * tTermP L (r + 1) + tTermP L (min r L) := rfl

/-- The constant of the running time of `encodeP`. -/
def cEncodeP : ℕ := 1035

/-- `retW L r` grows with `r`. -/
theorem retW_le_succ (L r : ℕ) : retW L r ≤ retW L (r + 1) := by
  induction L generalizing r with
  | zero => simp [retW]
  | succ L ih =>
    cases r with
    | zero => simp only [retW]; have := ih 0; omega
    | succ r => simp only [retW]; have := ih (r + 1); have := ih r; omega

/-- `retW L r` grows with `r`. -/
theorem retW_mono (L : ℕ) {r s : ℕ} (h : r ≤ s) : retW L r ≤ retW L s :=
  monotone_nat_of_le_succ (retW_le_succ L) h

/-- The number of steps is `O(retW L r)`.  The two further terms on the left make the induction go
through: `7^L` is small against the `9^L ≤ retW L r` leaves. -/
theorem encPTime_le (L r : ℕ) : encPTime L r + 977 * 7 ^ L + 50 ≤ cEncodeP * retW L r := by
  unfold cEncodeP
  induction L generalizing r with
  | zero => simp [encPTime, retW]
  | succ L ih =>
    cases r with
    | zero =>
      have := ih 0
      simp only [encPTime, tEncStep, retW, pow_succ]
      omega
    | succ r =>
      have := ih (r + 1)
      have := ih (min r L)
      have := retW_mono L (min_le_left r L)
      simp only [encPTime, tEncStep, retW, pow_succ]
      omega

/-! ## Facts about the positions -/

/-- The part of the encoding below the term number lam is the encoding of A_lam. -/
private theorem encIdx_succ' (c a : ℕ → ℤ) (L lam : ℕ) {i : ℕ} (hi : i < 10 ^ L) :
    encIdx c (L + 1) a (lam * 10 ^ L + i) = encIdx c L (encSlice c a L lam) i := by
  rw [encIdx, Nat.mul_add_div_of_lt hi, Nat.mul_add_mod_of_lt hi]

/-- The nines of a position below the term number lam: one more if `lam = 9`. -/
theorem ninesIdx_part (L lam : ℕ) {i : ℕ} (hi : i < 10 ^ L) :
    ninesIdx (L + 1) (lam * 10 ^ L + i) = (if lam = 9 then 1 else 0) + ninesIdx L i := by
  rw [ninesIdx, Nat.mul_add_div_of_lt hi, Nat.mul_add_mod_of_lt hi]

variable {lim : Limits} {P : Program} {d : ℕ} {μ μ' μ₁ μ₂ : ℕ → ℤ}
  {src out scr tab p7 p10 L lam r : ℕ} {V : ℤ} {a c : ℕ → ℤ}

/-- What has not changed at level `L + 1`, with the sizes in terms of `10^L`, `7^L` and
`scrSize L`. -/
private theorem sameOutside2_succ'
    (h : SameOutside2 μ μ' out (10 ^ (L + 1)) scr (scrSize (L + 1))) :
    SameOutside2 μ μ' out (10 * 10 ^ L) scr (7 ^ L + scrSize L) := by
  simpa only [pow_succ', scrSize] using h

/-- The layout of the recursive call for the term number `lam`. -/
private theorem EncodeLayout.toRecP (lay : EncodeLayout lim src out scr tab p7 p10 (L + 1))
    (hlam : lam < 10) :
    EncodeLayout lim scr (out + lam * 10 ^ L) (scr + 7 ^ L) tab p7 p10 L := by
  have hplaces := lay.places_succ
  have hpart : lam * 10 ^ L + 10 ^ L ≤ 10 * 10 ^ L := Nat.mul_add_le_mul hlam le_rfl
  exact ⟨lay.std, by omega, by omega, by omega, by omega, by omega, by omega⟩

namespace EncodePre

/-- The bound `V` is not negative. -/
private theorem V_nonneg' (pre : EncodePre lim μ src out scr tab p7 p10 V L a c) : 0 ≤ V := by
  have := pre.src_bound 0 (by positivity)
  omega

/-- In the course of `encodeP` at level `L + 1`, the hypotheses of `encStep` hold for every
term. -/
private theorem toStepP (pre : EncodePre lim μ src out scr tab p7 p10 V (L + 1) a c)
    (hlam : lam < 10) (same : SameOutside2 μ μ' out (10 ^ (L + 1)) scr (scrSize (L + 1))) :
    EncStepPre lim μ' src scr (7 ^ L) lam tab V := by
  have hplaces := pre.lay.places_succ
  have hkept := sameOutside2_succ' same
  have hV := pre.V_nonneg'
  have hword := pre.word_bound
  have hone : (1 : ℤ) ≤ 7 ^ L := one_le_pow₀ (by norm_num)
  rw [pow_succ'] at hword
  push_cast at hword
  exact
    { std := pre.lay.std, tab_le := by omega, src_le := by omega, dst_le := by omega
      coef := fun i hi => by
        rw [Nat.add_assoc, hkept _ (by omega), pre.tabV _ (by omega)]
        exact pre.coef_bound _ (by omega)
      vals := fun i hi => by
        rw [hkept _ (by omega), pre.srcV i (by rw [pow_succ']; omega)]
        exact pre.src_bound i (by rw [pow_succ']; omega)
      word_bound := (mul_le_mul_of_nonneg_right (by omega) hV).trans hword }

/-- After `encStep` has written `A_lam` to the scratch area, the hypotheses of `encodeP` hold at
level `L` for the recursive call. -/
private theorem toRecP (pre : EncodePre lim μ src out scr tab p7 p10 V (L + 1) a c)
    (hlam : lam < 10) (same : SameOutside2 μ μ' out (10 ^ (L + 1)) scr (scrSize (L + 1)))
    (hstep : ∀ j < 7 ^ L, μ₁ (scr + j) = encStepVal μ' src lam tab (7 ^ L) j 7)
    (same₁ : SameOutside μ' μ₁ scr (7 ^ L)) :
    EncodePre lim μ₁ scr (out + lam * 10 ^ L) (scr + 7 ^ L) tab p7 p10 (7 * V) L
      (encSlice c a L lam) c := by
  have hplaces := pre.lay.places_succ
  have hkept := sameOutside2_succ' same
  have hword := pre.word_bound
  have hsrc : ∀ j < 7 * 7 ^ L, μ' (src + j) = a j := fun j hj => by
    rw [hkept _ (by omega)]
    exact pre.srcV j (by rw [pow_succ']; omega)
  have htab : ∀ i < 70, μ' (tab + i) = c i := fun i hi => by
    rw [hkept _ (by omega)]
    exact pre.tabV i hi
  exact
    { lay := pre.lay.toRecP hlam
      srcV := fun j hj => by
        rw [hstep j hj]
        refine Finset.sum_congr rfl fun s hs => ?_
        have hs7 : s < 7 := Finset.mem_range.mp hs
        rw [Nat.add_assoc tab, htab (7 * lam + s) (by omega), Nat.add_assoc src,
          hsrc _ (Nat.mul_add_lt_mul hs7 hj)]
      src_bound := fun j hj => by
        simpa [encSlice] using enc_sum_bound 7 fun s hs =>
          enc_coef_mul_bound (pre.coef_bound (7 * lam + s) (by omega))
            (pre.src_bound (s * 7 ^ L + j) (by rw [pow_succ']; exact Nat.mul_add_lt_mul hs hj))
      tabV := fun i hi => by rw [same₁ _ (by omega), htab i hi]
      coef_bound := pre.coef_bound
      p7V := fun i hi => by rw [same₁ _ (by omega), hkept _ (by omega), pre.p7V i (by omega)]
      p10V := fun i hi => by rw [same₁ _ (by omega), hkept _ (by omega), pre.p10V i (by omega)]
      word_bound := by
        rw [pow_succ'] at hword
        push_cast at hword ⊢
        rwa [show (7 : ℤ) ^ L * (7 * V) = 7 * 7 ^ L * V by ring] }

end EncodePre

/-! ## What encodeP guarantees -/

/-- What `encodeP` guarantees: the output holds the encoding at the positions with at most `r`
nines, and only the `10^L` cells of `out` and the `scrSize L` cells of the scratch area have
changed. -/
def EncodePPost (μ : ℕ → ℤ) (out scr L r : ℕ) (a c : ℕ → ℤ) (μ' : ℕ → ℤ) : Prop :=
  (∀ i < 10 ^ L, ninesIdx L i ≤ r → μ' (out + i) = encIdx c L a i) ∧
    SameOutside2 μ μ' out (10 ^ L) scr (scrSize L)

/-- The memory before the round of the term number `lam`: the parts of the output below the earlier
terms are filled at the positions with at most `r` nines, and only the output and the scratch area
have changed. -/
def TermsDoneP (μ : ℕ → ℤ) (out scr L r : ℕ) (a c : ℕ → ℤ) (lam : ℕ) (μ' : ℕ → ℤ) : Prop :=
  (∀ i < lam * 10 ^ L, ninesIdx (L + 1) i ≤ r → μ' (out + i) = encIdx c (L + 1) a i) ∧
    SameOutside2 μ μ' out (10 ^ (L + 1)) scr (scrSize (L + 1))

/-- The two calls for the term number `lam`, the recursive one with a budget `r₀` that is large
enough, fill the part of the output below it. -/
theorem TermsDoneP.step {r₀ : ℕ} (lay : EncodeLayout lim src out scr tab p7 p10 (L + 1))
    (hlam : lam < 10) (hr : ∀ x ≤ L, (if lam = 9 then 1 else 0) + x ≤ r → x ≤ r₀)
    (h : TermsDoneP μ out scr L r a c lam μ') (same₁ : SameOutside μ' μ₁ scr (7 ^ L))
    (hpost : EncodePPost μ₁ (out + lam * 10 ^ L) (scr + 7 ^ L) L r₀ (encSlice c a L lam) c μ₂) :
    TermsDoneP μ out scr L r a c (lam + 1) μ₂ := by
  have hplaces := lay.places_succ
  have hpart : lam * 10 ^ L + 10 ^ L ≤ 10 * 10 ^ L := Nat.mul_add_le_mul hlam le_rfl
  obtain ⟨hdone, same⟩ := h
  obtain ⟨hnew, same₂⟩ := hpost
  have hkept := sameOutside2_succ' same
  refine ⟨fun i hi hn => ?_, ?_⟩
  · rw [Nat.succ_mul] at hi
    by_cases hold : i < lam * 10 ^ L
    · -- The parts below the earlier terms are not touched.
      rw [same₂ _ (by omega), same₁ _ (by omega), hdone i hold hn]
    · -- The part below this term.
      obtain ⟨i, rfl⟩ : ∃ i', i = lam * 10 ^ L + i' := ⟨i - lam * 10 ^ L, by omega⟩
      rw [ninesIdx_part L lam (by omega)] at hn
      rw [← Nat.add_assoc, hnew i (by omega) (hr _ (ninesIdx_le L i) hn),
        encIdx_succ' c a L lam (by omega)]
  · simp only [pow_succ', scrSize]
    clear same
    light_keep

/-- The list of the local variables at level L + 1, with the value `rb` of the budget. -/
abbrev EncodeP.locals (L src out scr tab p7 p10 rb lam : ℕ) (res : ℤ) : List ℤ :=
  [(L + 1 : ℕ), src, out, scr, tab, p7, p10, rb, (7 ^ L : ℕ), (10 ^ L : ℕ), lam, res]

/-- The specification of encodeP at level L, for a caller at depth d, with every budget. -/
def EncodePMeets (lim : Limits) (P : Program) (pE d tab p7 p10 L : ℕ) (c : ℕ → ℤ) : Prop :=
  ∀ (μ : ℕ → ℤ) (src out scr : ℕ) (V : ℤ) (a : ℕ → ℤ) (r : ℕ),
    EncodePre lim μ src out scr tab p7 p10 V L a c →
    Meets lim P pE (d + 1) [L, src, out, scr, tab, p7, p10, r] μ (encPTime L r) fun _ μ' =>
      EncodePPost μ out scr L r a c μ'

variable {pS pE : ℕ}

/-- **One term**: step (2) and step (3) fill the part of the output below the term number `lam`,
at the positions with at most `r` nines, if the budget `r₀` that the expression `b` gives is large
enough. -/
theorem encodePTerm_spec (hS : P[pS]? = some encStepBody)
    (hrec : EncodePMeets lim P pE d tab p7 p10 L c)
    (pre : EncodePre lim μ src out scr tab p7 p10 V (L + 1) a c) (hd : d < lim.depth)
    (hlam : lam < 10) {b : Expr} {rb r₀ : ℕ}
    (hb : ∀ σ : State, σ.loc Budget = rb → b.Gives lim σ r₀) (hbc : b.cost ≤ 3)
    (hr : ∀ x ≤ L, (if lam = 9 then 1 else 0) + x ≤ r → x ≤ r₀)
    (h : TermsDoneP μ out scr L r a c lam μ') (res : ℤ) :
    Ends lim P d (encodePTerm pS pE b) ⟨frame (EncodeP.locals L src out scr tab p7 p10 rb lam res),
      μ'⟩ (tTermP L r₀)
      fun σ' => ∃ (res' : ℤ) (μ'' : ℕ → ℤ),
        σ' = ⟨frame (EncodeP.locals L src out scr tab p7 p10 rb lam res'), μ''⟩ ∧
          TermsDoneP μ out scr L r a c (lam + 1) μ'' := by
  have hplaces := pre.lay.places_succ
  -- The arguments of the two calls fit in a word, by the layout and the next three facts.
  have hpart : lam * 10 ^ L + 10 ^ L ≤ 10 * 10 ^ L := Nat.mul_add_le_mul hlam le_rfl
  have hprod : ((lam * 10 ^ L : ℕ) : ℤ) = lam * 10 ^ L := by push_cast; rfl
  have hpow : ((7 ^ L : ℕ) : ℤ) = 7 ^ L := by push_cast; rfl
  unfold encodePTerm tTermP
  -- Res := encStep(src, scr, 7^L, lam, tab)
  light_call (encStep_meets hS (pre.toStepP hlam h.2)) with r₁ μ₁ ⟨hstep, same₁⟩
  -- Res := encodeP(L, scr, out + lam 10^L, scr + 7^L, tab, p7, p10, b)
  obtain ⟨hbs, hbv⟩ := hb ⟨frame (EncodeP.locals L src out scr tab p7 p10 rb lam r₁), μ₁⟩ rfl
  refine Ends.callTo (hrec _ _ _ _ _ _ r₀ (pre.toRecP hlam h.2 hstep same₁)) ?_ ?_ hd ?_
  · exact fun r₂ μ₂ hpost => ⟨r₂, μ₂, rfl, h.step pre.lay hlam hr same₁ hpost⟩
  · change (∀ e ∈ _, Expr.Safe lim ⟨frame (EncodeP.locals L src out scr tab p7 p10 rb lam r₁), μ₁⟩
      e) ∧ List.map (Expr.val ⟨frame (EncodeP.locals L src out scr tab p7 p10 rb lam r₁), μ₁⟩) _ = _
    light_side [hbs, hbv]
  · light_time

/-! ## The recursion -/

/-- **A leaf**: the number is copied. -/
theorem encodeP_leaf (pre : EncodePre lim μ src out scr tab p7 p10 V 0 a c) :
    Ends lim P d (encodePBody pS pE) ⟨frame [(0 : ℕ), src, out, scr, tab, p7, p10, r], μ⟩
      (encPTime 0 r) fun σ' => EncodePPost μ out scr 0 r a c σ'.mem := by
  light_facts pre.lay pre.lay.std
  have hread : μ src = a 0 := pre.srcV 0 (by norm_num)
  -- if Level = 0 then mem[Out] := mem[Src]
  refine Ends.iteLast (fun _ => ?_) (fun h => absurd (by simp) h) (hT := by simp [encPTime])
  refine Ends.storeTo out (a 0) ⟨fun i hi _ => ?_, by light_keep⟩
    (by light_side [hread]) (by simp [encPTime])
  obtain rfl : i = 0 := by simpa using hi
  exact Function.update_self ..

/-- After the ten terms the output is filled at the positions with at most `r` nines. -/
private theorem TermsDoneP.post (h : TermsDoneP μ out scr L r a c 10 μ') :
    EncodePPost μ out scr (L + 1) r a c μ' :=
  ⟨fun i hi hn => h.1 i (by rwa [pow_succ'] at hi) hn, h.2⟩

/-- With no nine allowed, the output is filled after nine terms. -/
private theorem TermsDoneP.post_zero (h : TermsDoneP μ out scr L 0 a c 9 μ') :
    EncodePPost μ out scr (L + 1) 0 a c μ' := by
  refine ⟨fun i hi hn => ?_, h.2⟩
  by_cases hlow : i < 9 * 10 ^ L
  · exact h.1 i hlow hn
  · obtain ⟨i, rfl⟩ : ∃ i', i = 9 * 10 ^ L + i' := ⟨i - 9 * 10 ^ L, by omega⟩
    rw [pow_succ'] at hi
    rw [ninesIdx_part L 9 (by omega)] at hn
    simp at hn

/-- **An inner vertex**: the two lengths are read from the tables, the loop runs through the terms
0, …, 8, and the term 9 follows if a nine is allowed. -/
theorem encodeP_node (hS : P[pS]? = some encStepBody)
    (hrec : EncodePMeets lim P pE d tab p7 p10 L c)
    (pre : EncodePre lim μ src out scr tab p7 p10 V (L + 1) a c) (hd : d < lim.depth) :
    Ends lim P d (encodePBody pS pE) ⟨frame [(L + 1 : ℕ), src, out, scr, tab, p7, p10, r], μ⟩
      (encPTime (L + 1) r) fun σ' => EncodePPost μ out scr (L + 1) r a c σ'.mem := by
  have hplaces := pre.lay.places_succ
  have haddr7 : ((p7 : ℤ) + ((L : ℤ) + 1) - 1).toNat = p7 + L := by omega
  have haddr10 : ((p10 : ℤ) + ((L : ℤ) + 1) - 1).toNat = p10 + L := by omega
  have hread7 := pre.p7V L (by omega)
  have hread10 := pre.p10V L (by omega)
  have htime : 100 + 9 * tTermP L r ≤ encPTime (L + 1) r := by
    cases r <;> simp only [encPTime, tTermP] <;> omega
  -- if Level = 0
  refine Ends.iteLast (fun h => absurd h (by simp; omega)) (fun _ => ?_)
  -- Len7 := mem[Pow7 + Level - 1]; Len10 := mem[Pow10 + Level - 1]
  light_set (7 ^ L : ℕ) using haddr7, hread7
  light_set (10 ^ L : ℕ) using haddr10, hread10
  -- for TermNo < 9: the parts of the output below the earlier terms are filled
  refine Ends.next (9 * (1 + tTermP L r + 7) + 1 + 5)
    (Ends.forShape
      (fun lam res μ' => ⟨frame (EncodeP.locals L src out scr tab p7 p10 r lam res), μ'⟩)
      (TermsDoneP μ out scr L r a c) 9 (tTermP L r) 0 ⟨fun i hi => absurd hi (by omega), .refl⟩
      (fun lam res μ' hlam h => encodePTerm_spec (b := v Budget) hS hrec pre hd (by omega)
        (fun σ hσ => ⟨trivial, hσ⟩) (by simp)
        (fun x _ hx => by simp [show lam ≠ 9 by omega] at hx; omega) h res)
      ?_ (by rw [update_frame_setLocal, ← frame_append_zeros _ 1]; rfl) (hT := le_rfl)) ?_
  case refine_2 => light_time
  intro res μ' h
  -- if 0 < r: the term 9
  light_if hpos hzero : 0 < r
  · obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    -- if Level < r then r := Level
    light_if hbig hsmall : L + 1 < r + 1 using encPTime_succ_succ
    · have hmin : min r L = L := by omega
      light_set ((L + 1 : ℕ) : ℤ) using encPTime_succ_succ
      light_piece (encodePTerm_spec (b := v Budget -' k 1) (rb := L + 1) (r₀ := L) hS hrec pre hd
        (by omega) (fun σ hσ => by light_side [hσ]) (by simp) (fun x hx _ => hx) h res)
        using encPTime_succ_succ, hmin with σ' ⟨res', μ'', rfl, hdone⟩
      light_skip
      exact hdone.post
    · have hmin : min r L = r := by omega
      light_piece (encodePTerm_spec (b := v Budget -' k 1) (rb := r + 1) (r₀ := r) hS hrec pre hd
        (by omega) (fun σ hσ => by light_side [hσ]) (by simp)
        (fun x _ hx => by simp at hx; omega) h res)
        using encPTime_succ_succ, hmin with σ' ⟨res', μ'', rfl, hdone⟩
      light_skip
      exact hdone.post
  · obtain rfl : r = 0 := by omega
    light_skip
    exact h.post_zero

/-- **encodeP** is correct and takes at most `encPTime L r` steps, in every program whose procedures
number pS and pE are encStep and encodeP.  It nests calls at most L deep. -/
theorem encodeP_spec (hS : P[pS]? = some encStepBody) (hE : P[pE]? = some (encodePBody pS pE))
    (hd : d + L ≤ lim.depth) (pre : EncodePre lim μ src out scr tab p7 p10 V L a c) :
    Ends lim P d (encodePBody pS pE) ⟨frame [L, src, out, scr, tab, p7, p10, r], μ⟩
      (encPTime L r) fun σ' => EncodePPost μ out scr L r a c σ'.mem := by
  induction L generalizing d μ src out scr V a r with
  | zero => exact encodeP_leaf pre
  | succ L ih =>
    exact encodeP_node hS (fun _ _ _ _ _ _ _ pre' => Meets.of_body hE (ih (by omega) pre')) pre
      (by omega)

end Light.Sec2
