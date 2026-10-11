/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Batch.OSpecs

/-!
# The batched counting oracle: the queries of a batch

`queries(b0, ZL, ZH, RV, n, k, N0, K0, KKb, cnt, j0)` asks, for each product `u < KKb` of the batch
(slot `g = u / K₀`, `h = u % K₀`) and each pair `(a, b)`, the query at the virtual positions
`I = virt g (a k + ZL[a n + b])`, `J = virt h (b k + ZH[a n + b])`, and stores the answer at
`cnt + (j0 + u) n² + a n + b` (`queries_ok`).  The invariant `QInv E`: the data structure is ready,
the first `E` cells from `cnt + j0 n²` hold their answers, and no other cell below b0 has changed.
-/

@[expose] public section

namespace Light.Batch

open ThreeSumApsp ThreeSumApsp.Spec ThreeSumApsp.Batch Light.Sec4 QS

variable {lim : Limits} {P : Program} {d : ℕ}

/-- The answer of the query of the pair `(a, b)` in the slot `(g, h)`. -/
def qVal (pv : Sec2.Par) (t : ℕ) (hmL : pv.m ≤ pv.L) (AL : ArrL pv) (AR : ArrR pv) (n k : ℕ)
    (ZL ZH : List ℕ) (g h a b : ℕ) : ℤ :=
  queryValue pv.m t
    (encRowA AL (virt pv.K0 pv.N0 g (a * k + ZL.getD (a * n + b) 0) / (pv.K0 * pv.N0)))
    (encColA AR (virt pv.K0 pv.N0 h (b * k + ZH.getD (a * n + b) 0) / (pv.K0 * pv.N0)))
    (outStrOfPos (stdLayout hmL) (virt pv.K0 pv.N0 g (a * k + ZL.getD (a * n + b) 0))
      (virt pv.K0 pv.N0 h (b * k + ZH.getD (a * n + b) 0)))

/-- The answer of the cell `e` from `cnt + j0 n²`. -/
def qAns (pv : Sec2.Par) (t : ℕ) (hmL : pv.m ≤ pv.L) (AL : ArrL pv) (AR : ArrR pv) (n k : ℕ)
    (ZL ZH : List ℕ) (e : ℕ) : ℤ :=
  qVal pv t hmL AL AR n k ZL ZH (e / (n * n) / pv.K0) (e / (n * n) % pv.K0) (e % (n * n) / n)
    (e % (n * n) % n)

/-- What the queries of a batch assume, in the memory μ₀ at the start. -/
structure QSet (lim : Limits) (P : Program) (pv : Sec2.Par) (t : ℕ) (aX aY b0 : ℕ) (AL : ArrL pv)
    (AR : ArrR pv) (U : ℤ) (μ₀ : ℕ → ℤ) (zl zh rv n k NP KKb cnt j0 : ℕ) (ZL ZH : List ℕ) :
    Prop where
  hq : QueryAtASpec lim P
  ht : t ≤ pv.m
  hlim : Lim30 lim pv t b0 U
  hb : BoundA AL AR U
  segZL : SegN μ₀ zl ZL
  segZH : SegN μ₀ zh ZH
  lenZL : ZL.length = n * n
  lenZH : ZH.length = n * n
  ltZL : ∀ x ∈ ZL, x < k
  ltZH : ∀ x ∈ ZH, x < k
  segRV : SegN μ₀ rv ((List.range NP).map fun R => R / pv.N0 * (pv.K0 * pv.N0) + R % pv.N0)
  hN : pv.N = pv.K0 * NP
  n_pos : 1 ≤ n
  NP_mul : pv.N0 ∣ NP
  nk_le : n * k ≤ NP
  KKb_le : KKb ≤ pv.K0 * pv.K0
  belowZL : zl + n * n ≤ b0
  belowZH : zh + n * n ≤ b0
  belowRV : rv + NP ≤ b0
  belowCnt : cnt + (j0 + KKb) * (n * n) ≤ b0
  apZL : Apart (cnt + j0 * (n * n)) (KKb * (n * n)) zl (n * n)
  apZH : Apart (cnt + j0 * (n * n)) (KKb * (n * n)) zh (n * n)
  apRV : Apart (cnt + j0 * (n * n)) (KKb * (n * n)) rv NP

/-- The invariant: the data structure is ready, the first `E` cells from `cnt + j0 n²` hold their
answers, and no other cell below b0 has changed. -/
def QInv (pv : Sec2.Par) (t : ℕ) (hmL : pv.m ≤ pv.L) (aX aY b0 : ℕ) (AL : ArrL pv) (AR : ArrR pv)
    (μ₀ : ℕ → ℤ) (n k : ℕ) (ZL ZH : List ℕ) (base E : ℕ) (μ : ℕ → ℤ) : Prop :=
  DSReadyA pv t aX aY b0 AL AR μ ∧ (∀ e < E, μ (base + e) = qAns pv t hmL AL AR n k ZL ZH e) ∧
    ∀ x < b0, (x < base ∨ base + E ≤ x) → μ x = μ₀ x

/-- The time of the queries of a batch. -/
def tQueries (KKb n tq : ℕ) : ℕ := KKb * (n * (n * (tq + 80) + 20) + 80) + 30


section cell

variable {pv : Sec2.Par} {t : ℕ} {aX aY b0 : ℕ} {AL : ArrL pv} {AR : ArrR pv} {U : ℤ}
  {μ₀ : ℕ → ℤ} {zl zh rv n k NP KKb cnt j0 : ℕ} {ZL ZH : List ℕ}

/-- The locals of queries. -/
abbrev qFr (b0 zl zh rv n k N0 K0 KKb cnt j0 g h a b : ℕ) (I J r : ℤ) (dst u : ℕ) : List ℤ :=
  [b0, zl, zh, rv, n, k, N0, K0, KKb, cnt, j0, g, h, a, b, I, J, r, dst, u]

/-- A cell of a table below b0, away from the counts, still holds its entry. -/
theorem QSet.read (S : QSet lim P pv t aX aY b0 AL AR U μ₀ zl zh rv n k NP KKb cnt j0 ZL ZH)
    (hmL : pv.m ≤ pv.L) {E : ℕ} {μ : ℕ → ℤ}
    (hinv : QInv pv t hmL aX aY b0 AL AR μ₀ n k ZL ZH (cnt + j0 * (n * n)) E μ)
    (hE : E ≤ KKb * (n * n)) {x : ℕ} (hx : x < b0)
    (hout : x < cnt + j0 * (n * n) ∨ cnt + j0 * (n * n) + KKb * (n * n) ≤ x) : μ x = μ₀ x :=
  hinv.2.2 x hx (by omega)

/-- **One query.** -/
theorem queryCell_ends (S : QSet lim P pv t aX aY b0 AL AR U μ₀ zl zh rv n k NP KKb cnt j0 ZL ZH)
    (hmL : pv.m ≤ pv.L) (hd : d + 3 ≤ lim.depth) {u a b : ℕ} (hu : u < KKb) (ha : a < n)
    (hb : b < n) (I J r : ℤ) {μ : ℕ → ℤ}
    (hinv : QInv pv t hmL aX aY b0 AL AR μ₀ n k ZL ZH (cnt + j0 * (n * n))
      (u * (n * n) + (a * n + b)) μ) :
    Ends lim P d queryCell ⟨frame (qFr b0 zl zh rv n k pv.N0 pv.K0 KKb cnt j0 (u / pv.K0)
        (u % pv.K0) a b I J r (cnt + (j0 + u) * (n * n)) u), μ⟩ (tQueryAt pv.L pv.m t + 70)
      fun σ' => ∃ (I' J' r' : ℤ) (μ' : ℕ → ℤ), σ' = ⟨frame (qFr b0 zl zh rv n k pv.N0 pv.K0 KKb cnt
        j0 (u / pv.K0) (u % pv.K0) a b I' J' r' (cnt + (j0 + u) * (n * n)) u), μ'⟩ ∧
        QInv pv t hmL aX aY b0 AL AR μ₀ n k ZL ZH (cnt + j0 * (n * n))
          (u * (n * n) + (a * n + b) + 1) μ' := by
  have hlim := S.hlim
  have std := hlim.std
  have hspace := hlim.space
  have htop := base_le_top pv t b0
  have hscr := scratch_in_block pv t b0
  have hK0 : 0 < pv.K0 := ThreeSumApsp.K0_pos hmL
  have hN0 : 0 < pv.N0 := ThreeSumApsp.N0_pos _ _
  have hq : a * n + b < n * n := Nat.mul_add_lt_mul ha hb
  have hE : u * (n * n) + (a * n + b) < KKb * (n * n) := by
    have := Nat.mul_add_lt_mul hu hq
    omega
  have hbz := S.belowZL
  have hbh := S.belowZH
  have hbr := S.belowRV
  have hbc := S.belowCnt
  have hapl := S.apZL
  have haph := S.apZH
  have hapr := S.apRV
  have hjn : (j0 + KKb) * (n * n) = j0 * (n * n) + KKb * (n * n) := by ring
  -- the entries of the tables
  have hzlv : ZL.getD (a * n + b) 0 < k := by
    rw [List.getD_eq_getElem _ _ (by rw [S.lenZL]; exact hq)]
    exact S.ltZL _ (List.getElem_mem _)
  have hzhv : ZH.getD (a * n + b) 0 < k := by
    rw [List.getD_eq_getElem _ _ (by rw [S.lenZH]; exact hq)]
    exact S.ltZH _ (List.getElem_mem _)
  have rzl : μ (zl + (a * n + b)) = (ZL.getD (a * n + b) 0 : ℕ) := by
    rw [S.read hmL hinv hE.le (by omega) (by omega)]
    exact S.segZL.read (by rw [S.lenZL]; exact hq)
  have rzh : μ (zh + (a * n + b)) = (ZH.getD (a * n + b) 0 : ℕ) := by
    rw [S.read hmL hinv hE.le (by omega) (by omega)]
    exact S.segZH.read (by rw [S.lenZH]; exact hq)
  set zL := ZL.getD (a * n + b) 0 with hzL
  set zH := ZH.getD (a * n + b) 0 with hzH
  have hR : a * k + zL < NP := by
    have := Nat.mul_add_lt_mul ha hzlv
    have := S.nk_le
    omega
  have hC : b * k + zH < NP := by
    have := Nat.mul_add_lt_mul hb hzhv
    have := S.nk_le
    omega
  have rrv : ∀ R < NP, μ (rv + R) = ((R / pv.N0 * (pv.K0 * pv.N0) + R % pv.N0 : ℕ) : ℤ) := by
    intro R hRl
    rw [S.read hmL hinv hE.le (by omega) (by omega)]
    have := S.segRV.read (i := R) (by simpa using hRl)
    rw [this, List.getD_eq_getElem _ _ (by simpa using hRl), List.getElem_map, List.getElem_range]
  have rzl' : μ (((zl : ℤ) + a * n + b).toNat) = (zL : ℤ) := by
    rw [show ((zl : ℤ) + a * n + b) = ((zl + (a * n + b) : ℕ) : ℤ) by push_cast; ring,
      Int.toNat_natCast, rzl]
  have rzh' : μ (((zh : ℤ) + a * n + b).toNat) = (zH : ℤ) := by
    rw [show ((zh : ℤ) + a * n + b) = ((zh + (a * n + b) : ℕ) : ℤ) by push_cast; ring,
      Int.toNat_natCast, rzh]
  set R := a * k + zL with hRdef
  set C := b * k + zH with hCdef
  have rrl : μ (((rv : ℤ) + a * k + zL).toNat)
      = ((R / pv.N0 * (pv.K0 * pv.N0) + R % pv.N0 : ℕ) : ℤ) := by
    rw [show ((rv : ℤ) + a * k + zL) = ((rv + R : ℕ) : ℤ) by push_cast [hRdef]; ring, Int.toNat_natCast,
      rrv R hR]
  have rrh : μ (((rv : ℤ) + b * k + zH).toNat)
      = ((C / pv.N0 * (pv.K0 * pv.N0) + C % pv.N0 : ℕ) : ℤ) := by
    rw [show ((rv : ℤ) + b * k + zH) = ((rv + C : ℕ) : ℤ) by push_cast [hCdef]; ring, Int.toNat_natCast,
      rrv C hC]
  set Iv := virt pv.K0 pv.N0 (u / pv.K0) R with hIv
  set Jv := virt pv.K0 pv.N0 (u % pv.K0) C with hJv
  have hvI : ((R / pv.N0 * (pv.K0 * pv.N0) + R % pv.N0 : ℕ) : ℤ) + ((u / pv.K0 : ℕ) : ℤ) * pv.N0
      = (Iv : ℤ) := by rw [hIv, virt]; push_cast; ring
  have hvJ : ((C / pv.N0 * (pv.K0 * pv.N0) + C % pv.N0 : ℕ) : ℤ) + ((u % pv.K0 : ℕ) : ℤ) * pv.N0
      = (Jv : ℤ) := by rw [hJv, virt]; push_cast; ring
  -- bounds for the arithmetic of the addresses
  have hNb : b0 + pv.N ≤ aWD pv b0 := by
    simp only [aWD, Sec2.Par.sharedEnd, Sec2.Par.aZS, Sec2.Par.aARR, Sec2.Par.aENCB,
      Sec2.Par.aENCA, Sec2.Par.aDIG4, Sec2.Par.aDIG3, Sec2.Par.aBLOCK, Sec2.Par.aBAND,
      Sec2.Par.aMASK, Sec2.Par.aPSI, Sec2.Par.aPHI, Sec2.Par.aPAS, Sec2.Par.aP10, Sec2.Par.aP7,
      Sec2.Par.aP4, Sec2.Par.aP3]
    omega
  have hvirt : ∀ {g R' : ℕ}, g < pv.K0 → R' < NP → virt pv.K0 pv.N0 g R' < pv.N := by
    intro g R' hg hR'
    rw [S.hN]
    have h1 : R' / pv.N0 * (pv.K0 * pv.N0) + (g * pv.N0 + R' % pv.N0)
        < (R' / pv.N0 + 1) * (pv.K0 * pv.N0) := by
      have := Nat.mul_add_lt_mul hg (Nat.mod_lt R' hN0)
      have e : (R' / pv.N0 + 1) * (pv.K0 * pv.N0) = R' / pv.N0 * (pv.K0 * pv.N0) + pv.K0 * pv.N0 :=
        by ring
      omega
    have h2 : (R' / pv.N0 + 1) * (pv.K0 * pv.N0) ≤ pv.K0 * NP := by
      obtain ⟨c, hc⟩ := S.NP_mul
      have : R' / pv.N0 < c := Nat.div_lt_of_lt_mul (by rw [← hc]; exact hR')
      calc (R' / pv.N0 + 1) * (pv.K0 * pv.N0) ≤ c * (pv.K0 * pv.N0) :=
            Nat.mul_le_mul_right _ this
        _ = pv.K0 * NP := by rw [hc]; ring
    unfold virt
    omega
  have hIN : Iv < pv.N := hvirt (Nat.div_lt_of_lt_mul (by have := S.KKb_le; omega)) hR
  have hJN : Jv < pv.N := hvirt (Nat.mod_lt _ hK0) hC
  have z1 : (0 : ℤ) ≤ (a : ℤ) * n := by positivity
  have z2 : (a : ℤ) * n + b < n * n := by exact_mod_cast hq
  have z3 : (0 : ℤ) ≤ (a : ℤ) * k := by positivity
  have z4 : (0 : ℤ) ≤ (b : ℤ) * k := by positivity
  have z5 : (a : ℤ) * k + zL < NP := by exact_mod_cast hR
  have z6 : (b : ℤ) * k + zH < NP := by exact_mod_cast hC
  have z7 : (0 : ℤ) ≤ ((u / pv.K0 : ℕ) : ℤ) * pv.N0 := by positivity
  have z8 : (0 : ℤ) ≤ ((u % pv.K0 : ℕ) : ℤ) * pv.N0 := by positivity
  have z9 : (0 : ℤ) ≤ (n : ℤ) * n := by positivity
  have hspN : b0 + pv.N ≤ lim.space := by omega
  unfold queryCell
  have zR : (0 : ℤ) ≤ ((R / pv.N0 * (pv.K0 * pv.N0) + R % pv.N0 : ℕ) : ℤ) := by positivity
  have zC : (0 : ℤ) ≤ ((C / pv.N0 * (pv.K0 * pv.N0) + C % pv.N0 : ℕ) : ℤ) := by positivity
  push_cast at z7 z8 hvI hvJ zR zC
  light_set (Iv : ℕ) using rzl', rrl
  light_set (Jv : ℕ) using rzh', rrh
  light_call (S.hq pv t hmL aX aY b0 AL AR U μ ⟨Iv, hIN⟩ ⟨Jv, hJN⟩ S.ht hlim S.hb hinv.1)
    with r₁ μ₁ ⟨hr₁, hds₁, hso₁⟩
  have hlt : cnt + j0 * (n * n) + (u * (n * n) + (a * n + b)) < b0 := by omega
  have hlt' : (cnt : ℤ) + j0 * (n * n) + (u * (n * n) + (a * n + b)) < b0 := by exact_mod_cast hlt
  have hdst : (cnt : ℤ) + (j0 + u) * (n * n) = cnt + j0 * (n * n) + u * (n * n) := by ring
  have z10 : (0 : ℤ) ≤ (j0 : ℤ) * (n * n) := by positivity
  have z11 : (0 : ℤ) ≤ (u : ℤ) * (n * n) := by positivity
  light_store (cnt + j0 * (n * n) + (u * (n * n) + (a * n + b))) r₁ using hdst
  refine ⟨(Iv : ℕ), (Jv : ℕ), r₁, _, rfl, ?_, ?_, ?_⟩
  · refine dsReadyA_congr hds₁ fun x hx => Function.update_of_ne (by omega) _ _
  · intro e he
    rcases Nat.lt_succ_iff_lt_or_eq.1 he with he | he
    · rw [Function.update_of_ne (by omega), hso₁ _ (Or.inl (by omega))]
      exact hinv.2.1 e he
    · subst he
      have hnn : 0 < n * n := by omega
      have h1 : (u * (n * n) + (a * n + b)) / (n * n) = u := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hnn, Nat.div_eq_of_lt hq, zero_add]
      have h2 : (u * (n * n) + (a * n + b)) % (n * n) = a * n + b := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hq]
      rw [Function.update_self, hr₁]
      unfold qAns qVal
      rw [h1, h2, Nat.mul_add_div_of_lt hb, Nat.mul_add_mod_of_lt hb]
  · intro x hx hout
    rw [Function.update_of_ne (by omega), hso₁ _ (Or.inl (by omega))]
    exact hinv.2.2 x hx (by omega)

/-- The time of the queries of a row `a`. -/
def tQRow (n tq : ℕ) : ℕ := n * (tq + 80) + 6

/-- **The queries of a row `a`.** -/
theorem queryRow_ends (S : QSet lim P pv t aX aY b0 AL AR U μ₀ zl zh rv n k NP KKb cnt j0 ZL ZH)
    (hmL : pv.m ≤ pv.L) (hd : d + 3 ≤ lim.depth) {u a : ℕ} (hu : u < KKb) (ha : a < n)
    (b : ℕ) (I J r : ℤ) {μ : ℕ → ℤ}
    (hinv : QInv pv t hmL aX aY b0 AL AR μ₀ n k ZL ZH (cnt + j0 * (n * n)) (u * (n * n) + a * n) μ) :
    Ends lim P d (.for QS.B (v QS.N) queryCell) ⟨frame (qFr b0 zl zh rv n k pv.N0 pv.K0 KKb cnt j0
        (u / pv.K0) (u % pv.K0) a b I J r (cnt + (j0 + u) * (n * n)) u), μ⟩
      (tQRow n (tQueryAt pv.L pv.m t))
      fun σ' => ∃ (b' : ℕ) (I' J' r' : ℤ) (μ' : ℕ → ℤ), σ' = ⟨frame (qFr b0 zl zh rv n k pv.N0
        pv.K0 KKb cnt j0 (u / pv.K0) (u % pv.K0) a b' I' J' r' (cnt + (j0 + u) * (n * n)) u), μ'⟩ ∧
        QInv pv t hmL aX aY b0 AL AR μ₀ n k ZL ZH (cnt + j0 * (n * n)) (u * (n * n) + a * n + n)
          μ' := by
  have std := S.hlim.std
  have hspace := S.hlim.space
  have htop := base_le_top pv t b0
  have hbc := S.belowCnt
  have hnn : n ≤ n * n := Nat.le_mul_self n
  have hnw : (n : ℤ) ≤ lim.word := by
    have := std.space_le
    have : n ≤ b0 := by
      have : n * n ≤ (j0 + KKb) * (n * n) := Nat.le_mul_of_pos_left _ (by omega)
      omega
    omega
  unfold tQRow
  refine Ends.forShape (β := ℤ × ℤ × ℤ)
    (fun j s μ' => ⟨frame (qFr b0 zl zh rv n k pv.N0 pv.K0 KKb cnt j0 (u / pv.K0) (u % pv.K0) a j
      s.1 s.2.1 s.2.2 (cnt + (j0 + u) * (n * n)) u), μ'⟩)
    (fun j μ' => QInv pv t hmL aX aY b0 AL AR μ₀ n k ZL ZH (cnt + j0 * (n * n))
      (u * (n * n) + (a * n + j)) μ') n (tQueryAt pv.L pv.m t + 70) (I, J, r) hinv ?_ ?_
  · rintro j ⟨I₁, J₁, r₁⟩ μ' hj hI
    refine (queryCell_ends S hmL hd hu ha hj I₁ J₁ r₁ hI).mono le_rfl ?_
    rintro _ ⟨I', J', r', μ'', rfl, h⟩
    exact ⟨(I', J', r'), μ'', rfl, h⟩
  · rintro ⟨I₁, J₁, r₁⟩ μ' hI
    exact ⟨n, I₁, J₁, r₁, μ', rfl, by rwa [Nat.add_assoc]⟩

/-- The time of the queries of a product. -/
def tQRows (n tq : ℕ) : ℕ := n * (tQRow n tq + 10) + 6

/-- **The queries of a product `u`.** -/
theorem queryRows_ends (S : QSet lim P pv t aX aY b0 AL AR U μ₀ zl zh rv n k NP KKb cnt j0 ZL ZH)
    (hmL : pv.m ≤ pv.L) (hd : d + 3 ≤ lim.depth) {u : ℕ} (hu : u < KKb) (a b : ℕ) (I J r : ℤ)
    {μ : ℕ → ℤ}
    (hinv : QInv pv t hmL aX aY b0 AL AR μ₀ n k ZL ZH (cnt + j0 * (n * n)) (u * (n * n)) μ) :
    Ends lim P d (.for QS.A (v QS.N) (.for QS.B (v QS.N) queryCell)) ⟨frame (qFr b0 zl zh rv n k
        pv.N0 pv.K0 KKb cnt j0 (u / pv.K0) (u % pv.K0) a b I J r (cnt + (j0 + u) * (n * n)) u), μ⟩
      (tQRows n (tQueryAt pv.L pv.m t))
      fun σ' => ∃ (a' b' : ℕ) (I' J' r' : ℤ) (μ' : ℕ → ℤ), σ' = ⟨frame (qFr b0 zl zh rv n k pv.N0
        pv.K0 KKb cnt j0 (u / pv.K0) (u % pv.K0) a' b' I' J' r' (cnt + (j0 + u) * (n * n)) u), μ'⟩ ∧
        QInv pv t hmL aX aY b0 AL AR μ₀ n k ZL ZH (cnt + j0 * (n * n)) ((u + 1) * (n * n)) μ' := by
  have std := S.hlim.std
  have hspace := S.hlim.space
  have htop := base_le_top pv t b0
  have hbc := S.belowCnt
  have hnn : n ≤ n * n := Nat.le_mul_self n
  have hnw : (n : ℤ) ≤ lim.word := by
    have := std.space_le
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · simp [h0]; omega
    have : n ≤ b0 := by
      have : n * n ≤ (j0 + KKb) * (n * n) := Nat.le_mul_of_pos_left _ (by omega)
      omega
    omega
  unfold tQRows
  refine Ends.forShape (β := ℕ × ℤ × ℤ × ℤ)
    (fun j s μ' => ⟨frame (qFr b0 zl zh rv n k pv.N0 pv.K0 KKb cnt j0 (u / pv.K0) (u % pv.K0) j
      s.1 s.2.1 s.2.2.1 s.2.2.2 (cnt + (j0 + u) * (n * n)) u), μ'⟩)
    (fun j μ' => QInv pv t hmL aX aY b0 AL AR μ₀ n k ZL ZH (cnt + j0 * (n * n))
      (u * (n * n) + j * n) μ') n (tQRow n (tQueryAt pv.L pv.m t) + 2) (b, I, J, r)
      (by simpa using hinv) ?_ ?_
  · rintro j ⟨b₁, I₁, J₁, r₁⟩ μ' hj hI
    refine (queryRow_ends S hmL hd hu hj b₁ I₁ J₁ r₁ hI).mono (by omega) ?_
    rintro _ ⟨b', I', J', r', μ'', rfl, h⟩
    exact ⟨(b', I', J', r'), μ'', rfl, by rwa [Nat.succ_mul, ← Nat.add_assoc]⟩
  · rintro ⟨b₁, I₁, J₁, r₁⟩ μ' hI
    exact ⟨n, b₁, I₁, J₁, r₁, μ', rfl, by rwa [Nat.succ_mul]⟩

/-- The time of a product. -/
def tQProd (n tq : ℕ) : ℕ := tQRows n tq + 60

/-- **A product `u` of the batch**: its queries, then the next slot. -/
theorem queryProd_ends (S : QSet lim P pv t aX aY b0 AL AR U μ₀ zl zh rv n k NP KKb cnt j0 ZL ZH)
    (hmL : pv.m ≤ pv.L) (hd : d + 3 ≤ lim.depth) {u : ℕ} (hu : u < KKb) (a b : ℕ) (I J r : ℤ)
    (dst : ℕ) {μ : ℕ → ℤ}
    (hinv : QInv pv t hmL aX aY b0 AL AR μ₀ n k ZL ZH (cnt + j0 * (n * n)) (u * (n * n)) μ) :
    Ends lim P d queryProd ⟨frame (qFr b0 zl zh rv n k pv.N0 pv.K0 KKb cnt j0 (u / pv.K0)
        (u % pv.K0) a b I J r dst u), μ⟩
      (tQProd n (tQueryAt pv.L pv.m t))
      fun σ' => ∃ (a' b' : ℕ) (I' J' r' : ℤ) (μ' : ℕ → ℤ), σ' = ⟨frame (qFr b0 zl zh rv n k pv.N0
        pv.K0 KKb cnt j0 ((u + 1) / pv.K0) ((u + 1) % pv.K0) a' b' I' J' r'
        (cnt + (j0 + u) * (n * n)) u), μ'⟩ ∧
        QInv pv t hmL aX aY b0 AL AR μ₀ n k ZL ZH (cnt + j0 * (n * n)) ((u + 1) * (n * n)) μ' := by
  have std := S.hlim.std
  have hspace := S.hlim.space
  have htop := base_le_top pv t b0
  have hbc := S.belowCnt
  have hK0 : 0 < pv.K0 := ThreeSumApsp.K0_pos hmL
  have hsw := std.space_le
  have hK0w : (pv.K0 : ℤ) ≤ lim.word := by
    have h1 : pv.K0 ≤ 10 ^ (pv.L + 1) := pv.K0_le_K.trans (pv.K_le_T.trans
      (Nat.pow_le_pow_right (by norm_num) (by omega)))
    exact le_trans (by exact_mod_cast h1) S.hlim.pow
  have hdl : cnt + (j0 + u) * (n * n) ≤ b0 := by
    have : (j0 + u) * (n * n) ≤ (j0 + KKb) * (n * n) := Nat.mul_le_mul_right _ (by omega)
    omega
  have hnb : n * n ≤ b0 := by
    have : n * n ≤ (j0 + KKb) * (n * n) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hdlZ : (cnt : ℤ) + (j0 + u) * (n * n) ≤ b0 := by exact_mod_cast hdl
  have hju : j0 + u ≤ b0 := by
    have : j0 + u ≤ (j0 + u) * (n * n) :=
      Nat.le_mul_of_pos_right _ (Nat.mul_pos S.n_pos S.n_pos)
    omega
  have hnbZ : (n : ℤ) * n ≤ b0 := by exact_mod_cast hnb
  have z1 : (0 : ℤ) ≤ (n : ℤ) * n := by positivity
  have z2 : (0 : ℤ) ≤ ((j0 : ℤ) + u) * (n * n) := by positivity
  have hm : u % pv.K0 < pv.K0 := Nat.mod_lt _ hK0
  unfold queryProd tQProd
  light_set (cnt + (j0 + u) * (n * n) : ℕ)
  light_piece (queryRows_ends S hmL hd hu a b I J r hinv) with _ ⟨a', b', I', J', r', μ', rfl, h⟩
  light_set ((u % pv.K0 + 1 : ℕ) : ℤ)
  have hdiv : ((u / pv.K0 : ℕ) : ℤ) ≤ u := by exact_mod_cast Nat.div_le_self _ _
  have hdiv0 : (0 : ℤ) ≤ ((u / pv.K0 : ℕ) : ℤ) := by positivity
  push_cast at hdiv hdiv0
  have hlt := base_lt_top pv t b0
  have e := Nat.div_add_mod u pv.K0
  light_if hc hc' : u % pv.K0 + 1 = pv.K0
  · light_set (0 : ℕ)
    light_set (u / pv.K0 + 1 : ℕ)
    have hu1 : u + 1 = pv.K0 * (u / pv.K0 + 1) := by rw [Nat.mul_succ]; omega
    have h1 : (u + 1) / pv.K0 = u / pv.K0 + 1 := by rw [hu1, Nat.mul_div_cancel_left _ hK0]
    have h2 : (u + 1) % pv.K0 = 0 := by rw [hu1, Nat.mul_mod_right]
    exact ⟨a', b', I', J', r', μ', by rw [h1, h2]; rfl, h⟩
  · light_skip
    have hm' : u % pv.K0 + 1 < pv.K0 := by omega
    have hu1 : u + 1 = (u % pv.K0 + 1) + pv.K0 * (u / pv.K0) := by omega
    have h1 : (u + 1) / pv.K0 = u / pv.K0 := by
      rw [hu1, Nat.add_mul_div_left _ _ hK0, Nat.div_eq_of_lt hm', zero_add]
    have h2 : (u + 1) % pv.K0 = u % pv.K0 + 1 := by
      rw [hu1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hm']
    exact ⟨a', b', I', J', r', μ', by rw [h1, h2]; rfl, h⟩

/-- **The queries of a batch.** -/
theorem queries_ok (hP : P[pQueries]? = some queriesBody)
    (S : QSet lim P pv t aX aY b0 AL AR U μ₀ zl zh rv n k NP KKb cnt j0 ZL ZH)
    (hmL : pv.m ≤ pv.L) (hd : d + 3 ≤ lim.depth) (hds : DSReadyA pv t aX aY b0 AL AR μ₀) :
    Meets lim P pQueries d [b0, zl, zh, rv, n, k, pv.N0, pv.K0, KKb, cnt, j0] μ₀
      (tQueries KKb n (tQueryAt pv.L pv.m t)) fun _ μ' =>
        QInv pv t hmL aX aY b0 AL AR μ₀ n k ZL ZH (cnt + j0 * (n * n)) (KKb * (n * n)) μ' := by
  have std := S.hlim.std
  have hsw := std.space_le
  have hspace := S.hlim.space
  have htop := base_le_top pv t b0
  have hbc := S.belowCnt
  have hKb : KKb ≤ b0 := by
    have : KKb ≤ (j0 + KKb) * (n * n) :=
      (Nat.le_add_left _ _).trans (Nat.le_mul_of_pos_right _ (Nat.mul_pos S.n_pos S.n_pos))
    omega
  refine .of_body hP ?_
  unfold queriesBody tQueries
  light_set (0 : ℕ)
  light_set (0 : ℕ)
  refine Ends.for (fun j σ => ∃ (a b : ℕ) (I J r : ℤ) (dst : ℕ) (μ' : ℕ → ℤ),
      σ = ⟨frame (qFr b0 zl zh rv n k pv.N0 pv.K0 KKb cnt j0 (j / pv.K0) (j % pv.K0) a b I J r dst
        j), μ'⟩ ∧ QInv pv t hmL aX aY b0 AL AR μ₀ n k ZL ZH (cnt + j0 * (n * n)) (j * (n * n)) μ')
    KKb (tQProd n (tQueryAt pv.L pv.m t)) ?start ?round ?done ?bound (hT := ?hT)
  case hT =>
    have e1 : (v QS.KKb).cost = 1 := rfl
    have e2 : (Light.k 0).cost = 1 := rfl
    rw [e1, e2]
    unfold tQProd tQRows tQRow
    generalize tQueryAt pv.L pv.m t = q
    have h1 : 1 + (n * (n * (q + 80) + 6 + 10) + 6 + 60) + 7 ≤ n * (n * (q + 80) + 20) + 80 := by
      have := Nat.mul_le_mul_left n (show n * (q + 80) + 6 + 10 ≤ n * (q + 80) + 20 by omega)
      omega
    have h2 := Nat.mul_le_mul_left KKb h1
    generalize KKb * (1 + (n * (n * (q + 80) + 6 + 10) + 6 + 60) + 7) = A at h2 ⊢
    generalize KKb * (n * (n * (q + 80) + 20) + 80) = B at h2 ⊢
    omega
  case start =>
    refine ⟨0, 0, 0, 0, 0, 0, μ₀, ?_, hds, fun e he => by omega, fun x _ _ => rfl⟩
    simp [update_frame_setLocal, qFr]
  case round =>
    rintro j σ hj - ⟨a, b, I, J, r, dst, μ', rfl, hI⟩
    refine (queryProd_ends S hmL hd hj a b I J r dst hI).mono le_rfl ?_
    rintro _ ⟨a', b', I', J', r', μ'', rfl, h⟩
    refine ⟨by simp, a', b', I', J', r', cnt + (j0 + j) * (n * n), μ'', ?_, h⟩
    simp [update_frame_setLocal, qFr]
  case done =>
    rintro σ - ⟨a, b, I, J, r, dst, μ', rfl, h⟩
    exact h
  case bound =>
    rintro j σ hj - ⟨a, b, I, J, r, dst, μ', rfl, h⟩
    simp

end cell

end Light.Batch
