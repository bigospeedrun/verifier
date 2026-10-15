/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Batch.OMath
public import Submission.ThreeSumApsp.Batch.OQuery

/-!
# The batched counting oracle: the sources written from the tables

writeSrc reads its residues from two tables; where a cell is valid, the residue is that of
`srcMat` with the tables `t1X`, `t2X` (left source) or `t1Y`, `t2Y` (right source).  So the cells
that writeSrc leaves hold the two sources (`matAt_srcX`, `matAt_srcY`).
-/

@[expose] public section

open ThreeSumApsp ThreeSumApsp.Batch

namespace Light.Batch

theorem srcVal_congr {s p KK N0 : ℕ} {ok : ℕ → ℕ → ℕ → Bool} {f f' : ℕ → ℕ → ℕ → ℕ}
    (h : ∀ u R cl, ok u R cl = true → f u R cl = f' u R cl) (ρ κ : ℕ) :
    srcVal s p KK N0 ok f ρ κ = srcVal s p KK N0 ok f' ρ κ := by
  unfold srcVal
  by_cases hc : ok (rowU KK N0 ρ) (rowR KK N0 ρ) (κ / p) = true
  · rw [h _ _ _ hc]
  · simp [hc]

theorem resid_natCast (p x : ℕ) : resid p (x : ℤ) = x % p := by
  unfold resid
  rw [← Int.natCast_mod, Int.toNat_natCast]

/-- The table of the left source: `resid p (1 · w)` of the entries. -/
theorem getD_tabX {AC : List ℤ} {p q : ℕ} (hq : q < AC.length) :
    (AC.map fun w => resid p (1 * w)).getD q 0 = t1X p AC q := by
  rw [List.getD_eq_getElem _ _ (by simpa using hq), List.getElem_map, t1X,
    List.getD_eq_getElem _ _ hq, one_mul]

theorem getD_tabY {BC : List ℤ} {p q : ℕ} (hq : q < BC.length) :
    (BC.map fun w => resid p (-1 * w)).getD q 0 = t1Y p BC q := by
  rw [List.getD_eq_getElem _ _ (by simpa using hq), List.getElem_map, t1Y,
    List.getD_eq_getElem _ _ hq, neg_one_mul]

theorem getD_tabNL {p k l : ℕ} (hl : l < k) (hkp : k ≤ p) :
    ((List.range k).map fun h : ℕ => resid p ((p : ℤ) - h)).getD l 0 = t2X p l := by
  rw [List.getD_eq_getElem _ _ (by simpa using hl), List.getElem_map, List.getElem_range, t2X,
    show ((p : ℤ) - l) = ((p - l : ℕ) : ℤ) by push_cast [Nat.cast_sub (by omega : l ≤ p)]; ring,
    resid_natCast]

theorem getD_tabHK {p k h : ℕ} (hh : h < k) :
    ((List.range k).map fun h : ℕ => resid p ((h * k : ℕ) : ℤ)).getD h 0 = t2Y p k h := by
  rw [List.getD_eq_getElem _ _ (by simpa using hh), List.getElem_map, List.getElem_range, t2Y,
    resid_natCast]

variable {n s p k T KK bt N0 : ℕ}

/-- Where the left source is valid, the residues of writeSrc are those of `srcMat`. -/
theorem fGen_tabX {AC : List ℤ} (hAC : AC.length = n * n) (hk : 0 < k) (hkp : k ≤ p) {u R cl : ℕ}
    (hok : okX n s k T KK bt u R cl = true) :
    fGen n s p k KK bt (fun q => (AC.map fun w => resid p (1 * w)).getD q 0)
        (fun l => ((List.range k).map fun h : ℕ => resid p ((p : ℤ) - h)).getD l 0) u R cl
      = fGen n s p k KK bt (t1X p AC) (t2X p) u R cl := by
  simp only [okX, decide_eq_true_eq] at hok
  obtain ⟨-, hR, hc⟩ := hok
  have hq : R / k * n + (jOf KK bt u * s + cl) < AC.length := by
    rw [hAC]; exact Nat.mul_add_lt_mul hR hc
  unfold fGen
  beta_reduce
  rw [getD_tabX hq, getD_tabNL (Nat.mod_lt _ hk) hkp]

/-- Where the right source is valid, the residues of writeSrc are those of `srcMat`. -/
theorem fGen_tabY {BC : List ℤ} (hBC : BC.length = n * n) (hk : 0 < k) {u C cl : ℕ}
    (hok : okX n s k T KK bt u C cl = true) :
    fGen n s p k KK bt (fun q => (BC.map fun w => resid p (-1 * w)).getD q 0)
        (fun l => ((List.range k).map fun h : ℕ => resid p ((h * k : ℕ) : ℤ)).getD l 0) u C cl
      = fGen n s p k KK bt (t1Y p BC) (t2Y p k) u C cl := by
  simp only [okX, decide_eq_true_eq] at hok
  obtain ⟨-, hR, hc⟩ := hok
  have hq : C / k * n + (jOf KK bt u * s + cl) < BC.length := by
    rw [hBC]; exact Nat.mul_add_lt_mul hR hc
  unfold fGen
  beta_reduce
  rw [getD_tabY hq, getD_tabHK (Nat.mod_lt _ hk)]

/-- The cells of a source written by writeSrc hold `srcMat`. -/
theorem matAt_src {μ : ℕ → ℤ} {base rows D' : ℕ} {T1 T2 T1' T2' : ℕ → ℕ}
    (hcell : ∀ ρ < rows, ∀ κ < D', μ (base + ρ * D' + κ) =
      srcVal s p KK N0 (okX n s k T KK bt) (fGen n s p k KK bt T1 T2) ρ κ)
    (hagree : ∀ u R cl, okX n s k T KK bt u R cl = true →
      fGen n s p k KK bt T1 T2 u R cl = fGen n s p k KK bt T1' T2' u R cl) :
    MatAt μ base (srcMat rows D' n s p k T KK N0 bt T1' T2') := by
  intro i j
  rw [hcell i i.2 j j.2, srcVal_congr hagree]
  rfl

/-- **The answers of the queries of a batch are the counts** of the candidates of its products. -/
theorem qAns_eq_cntOf {pv : Sec2.Par} (hmL : pv.m ≤ pv.L) {t : ℕ} (ht : t ≤ pv.m)
    {n s p k KK bt NP nb KKb : ℕ} {AB BC AC : List ℤ} (hp : 0 < p) (hk : p ≤ k * k) (hkp : k ≤ p)
    (hsD : s * p ≤ ThreeSumApsp.D pv.m) (hKK : KK = pv.K0 * pv.K0) (hNP : NP = nb * pv.N0)
    (hN : pv.N = pv.K0 * NP) (hnk : n * k ≤ NP) (hKKb : KKb ≤ KK) (hAB : AB.length = n * n)
    {e : ℕ} (he : e < KKb * (n * n)) :
    qAns pv t hmL
        (batchL pv hmL (srcMat (pv.K0 * pv.N) (ThreeSumApsp.D pv.m) n s p k (bt * KK + KKb) KK
          pv.N0 bt (t1X p AC) (t2X p)))
        (batchR pv hmL (srcMat (pv.K0 * pv.N) (ThreeSumApsp.D pv.m) n s p k (bt * KK + KKb) KK
          pv.N0 bt (t1Y p BC) (t2Y p k)).transpose)
        n k ((AB.map fun w => resid p (-1 * w)).map (· % k))
        ((AB.map fun w => resid p (-1 * w)).map (· / k)) e
      = (Light.Filter2.cntOf n s p AB BC AC (bt * KK * (n * n) + e) : ℤ) := by
  have hK0 : 0 < pv.K0 := ThreeSumApsp.K0_pos hmL
  have hnn : 0 < n * n := by
    rcases Nat.eq_zero_or_pos (n * n) with h0 | h0
    · rw [h0] at he; omega
    · exact h0
  have hn : 0 < n := Nat.pos_of_mul_pos_left hnn
  set u := e / (n * n) with hu
  set q := e % (n * n) with hq
  have huK : u < KKb := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at he)
  have hqn : q < n * n := Nat.mod_lt _ hnn
  have ha : q / n < n := Nat.div_lt_of_lt_mul hqn
  have hb : q % n < n := Nat.mod_lt _ hn
  have hqab : q / n * n + q % n = q := by rw [Nat.mul_comm]; exact Nat.div_add_mod q n
  have hg : u / pv.K0 < pv.K0 := Nat.div_lt_of_lt_mul (by rw [← hKK]; omega)
  have hh : u % pv.K0 < pv.K0 := Nat.mod_lt _ hK0
  have hgh : u / pv.K0 * pv.K0 + u % pv.K0 = u := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod u pv.K0
  have hj : jOf KK bt (u / pv.K0 * pv.K0 + u % pv.K0) < bt * KK + KKb := by
    rw [hgh]; unfold jOf; omega
  have key := query_eq_cntOf (n := n) (s := s) (T := bt * KK + KKb) (KK := KK) (bt := bt) (NP := NP)
    (nb := nb) (AB := AB) (BC := BC) (AC := AC) hmL ht hp hk hkp hsD hKK hNP hN hnk ha hb hg hh hj
  simp only at key
  have hlen : q / n * n + q % n < AB.length := by rw [hAB, hqab]; exact hqn
  have hZ : ∀ (f : ℕ → ℕ), ((AB.map fun w => resid p (-1 * w)).map f).getD (q / n * n + q % n) 0
      = f (resid p (-AB.getD (q / n * n + q % n) 0)) := by
    intro f
    rw [List.getD_eq_getElem _ _ (by simpa using hlen), List.getElem_map, List.getElem_map,
      List.getD_eq_getElem _ _ hlen, neg_one_mul]
  unfold qAns qVal
  rw [← hu, ← hq]
  rw [hZ, hZ, key, hgh, hqab]
  unfold jOf
  congr 2
  rw [hu, hq, Nat.add_mul, Nat.add_assoc, Nat.div_add_mod']

end Light.Batch
