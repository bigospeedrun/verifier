/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Batch.Lift
public import Submission.ThreeSumApsp.Batch.SharedB
public import Submission.ThreeSumApsp.Filter2.Defs

/-!
# The batched counting oracle: the sources and the answer of a query

The two sources of a batch have the same shape (`srcMat`): the entry `(ρ, κ)` is 1 iff the product
`u` and the row `R` of the row `ρ`, and the vertex `cl = κ / p` of the middle block, are valid, and
`κ % p` is the residue `fGen T1 T2 u R cl = (T1[a n + c] + T2[l]) mod p` (`R = a k + l`,
`c = j s + cl`).  The left source has `T1 = w(a, c) mod p`, `T2[l] = -l mod p`; the right source,
transposed, has `T1 = -w(b, c) mod p`, `T2[h] = h k mod p`.

`query_eq_cntOf`: the query of the batched data structure at the virtual positions of the pair
`(a, b)` in the slot `(g, h)` returns the count of the candidate `j n² + a n + b`, `j` the middle
block of the product `u = g K₀ + h`.
-/

@[expose] public section

open Finset ThreeSumApsp ThreeSumApsp.Batch ThreeSumApsp.Spec

namespace Light.Batch

/-- The residue of the cell of the row `R` and the vertex `cl`. -/
def fGen (n s p k KK bt : ℕ) (T1 T2 : ℕ → ℕ) (u R cl : ℕ) : ℕ :=
  (T1 (R / k * n + (jOf KK bt u * s + cl)) + T2 (R % k)) % p

/-- A source of a batch, `rows × D`. -/
def srcMat (rows D' n s p k T KK N0 bt : ℕ) (T1 T2 : ℕ → ℕ) : Matrix (Fin rows) (Fin D') ℤ :=
  fun ρ κ => srcVal s p KK N0 (okX n s k T KK bt) (fGen n s p k KK bt T1 T2) ρ κ

/-- The tables of the left source. -/
def t1X (p : ℕ) (AC : List ℤ) (q : ℕ) : ℕ := resid p (AC.getD q 0)
def t2X (p : ℕ) (l : ℕ) : ℕ := (p - l) % p
/-- The tables of the right source. -/
def t1Y (p : ℕ) (BC : List ℤ) (q : ℕ) : ℕ := resid p (-BC.getD q 0)
def t2Y (p k : ℕ) (h : ℕ) : ℕ := h * k % p

theorem fGen_X (n s p k KK bt : ℕ) (AC : List ℤ) :
    fGen n s p k KK bt (t1X p AC) (t2X p) = fX n s p k KK bt AC := rfl

theorem fGen_Y (n s p k KK bt : ℕ) (BC : List ℤ) :
    fGen n s p k KK bt (t1Y p BC) (t2Y p k) = fY n s p k KK bt BC := by
  funext u C cl
  simp only [fGen, fY, t1Y, t2Y, Nat.add_comm]

/-- **The answer of a query.** -/
theorem query_eq_cntOf {pv : Sec2.Par} (hmL : pv.m ≤ pv.L) {t : ℕ} (ht : t ≤ pv.m)
    {n s p k T KK bt NP nb : ℕ} {AB BC AC : List ℤ} (hp : 0 < p) (hk : p ≤ k * k) (hkp : k ≤ p)
    (hsD : s * p ≤ D pv.m) (hKK : KK = pv.K0 * pv.K0) (hNP : NP = nb * pv.N0)
    (hN : pv.N = pv.K0 * NP) (hnk : n * k ≤ NP) {a b g h : ℕ} (ha : a < n) (hb : b < n)
    (hg : g < pv.K0) (hh : h < pv.K0) (hj : jOf KK bt (g * pv.K0 + h) < T) :
    let z := resid p (-AB.getD (a * n + b) 0)
    let I := virt pv.K0 pv.N0 g (a * k + z % k)
    let J := virt pv.K0 pv.N0 h (b * k + z / k)
    let X := srcMat (pv.K0 * pv.N) (D pv.m) n s p k T KK pv.N0 bt (t1X p AC) (t2X p)
    let Y := (srcMat (pv.K0 * pv.N) (D pv.m) n s p k T KK pv.N0 bt (t1Y p BC) (t2Y p k)).transpose
    queryValue pv.m t (encRowA (batchL pv hmL X) (I / (pv.K0 * pv.N0)))
        (encColA (batchR pv hmL Y) (J / (pv.K0 * pv.N0))) (outStrOfPos (stdLayout hmL) I J)
      = (Light.Filter2.cntOf n s p AB BC AC (jOf KK bt (g * pv.K0 + h) * (n * n) + (a * n + b))
          : ℤ) := by
  intro z I J X Y
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · simp [h0] at hk; omega
    · exact h0
  have hz : z < p := resid_lt hp _
  have hzk : z / k < k := Nat.div_lt_of_lt_mul (by nlinarith)
  have hN0 : 0 < pv.N0 := ThreeSumApsp.N0_pos _ _
  set u := g * pv.K0 + h with hu
  have huK : u < KK := by
    rw [hKK, hu]
    nlinarith
  set R := a * k + z % k with hR
  set C := b * k + z / k with hC
  have hbk : ∀ {x y : ℕ}, x < n → y < k → x * k + y < n * k := fun hx hy =>
    Nat.mul_add_lt_mul hx hy
  have hRn : R < n * k := hbk ha (Nat.mod_lt z hk0)
  have hCn : C < n * k := hbk hb hzk
  -- the query is the inner product of two source rows
  have hq := queryValue_bArray t ht (stdLayout hmL) X Y I J
  have hband : ∀ x, bandOf pv.L pv.m x = x / (pv.K0 * pv.N0) := fun x => rfl
  rw [hband, hband] at hq
  change queryValue pv.m t (encodingL (bArrayL (stdLayout hmL) X (I / (pv.K0 * pv.N0))))
    (encodingR (bArrayR (stdLayout hmL) Y (J / (pv.K0 * pv.N0)))) _ = _
  rw [hq]
  obtain ⟨hsr, hsc⟩ := srcRow_virt (stdLayout hmL) (R := R) (C := C) hg hh
  change ∑ κ : Fin (D pv.m), padRows X (srcRow (stdLayout hmL) I J) κ
    * padCols Y κ (srcCol (stdLayout hmL) I J) = _
  have hKK' : ThreeSumApsp.K0 pv.L pv.m * ThreeSumApsp.K0 pv.L pv.m = KK := hKK.symm
  rw [show srcRow (stdLayout hmL) I J = _ from hsr, show srcCol (stdLayout hmL) I J = _ from hsc,
    hKK']
  -- the two source rows lie in the sources
  have hrows : pv.K0 * pv.N = KK * (nb * pv.N0) := by rw [hN, hNP, hKK]; ring
  have hR' : R < nb * pv.N0 := by omega
  have hC' : C < nb * pv.N0 := by omega
  have hρ₁ := srcOf_lt (KK := KK) (N0 := pv.N0) huK hR'
  have hρ₂ := srcOf_lt (KK := KK) (N0 := pv.N0) huK hC'
  rw [← hrows] at hρ₁ hρ₂
  have hpad : ∀ κ : Fin (D pv.m),
      padRows X (srcOf KK pv.N0 u R) κ * padCols Y κ (srcOf KK pv.N0 u C)
        = srcVal s p KK pv.N0 (okX n s k T KK bt) (fX n s p k KK bt AC) (srcOf KK pv.N0 u R) κ
          * srcVal s p KK pv.N0 (okY n s k T KK bt) (fY n s p k KK bt BC)
              (srcOf KK pv.N0 u C) κ := by
    intro κ
    unfold padRows padCols
    rw [dif_pos hρ₁, dif_pos hρ₂]
    simp only [X, Y, srcMat, Matrix.transpose_apply, fGen_X, fGen_Y]
    rfl
  refine (sum_congr rfl fun κ _ => hpad κ).trans ?_
  rw [Fin.sum_univ_eq_sum_range (fun κ => srcVal s p KK pv.N0 (okX n s k T KK bt)
      (fX n s p k KK bt AC) (srcOf KK pv.N0 u R) κ * srcVal s p KK pv.N0 (okY n s k T KK bt)
        (fY n s p k KK bt BC) (srcOf KK pv.N0 u C) κ),
    sum_srcVal (fX := fX n s p k KK bt AC) (fY := fY n s p k KK bt BC) hp hsD (fun _ _ _ => Nat.mod_lt _ hp) (fun _ _ _ => Nat.mod_lt _ hp) _ _
      (by rw [rowU_srcOf huK hN0, rowU_srcOf huK hN0]),
    rowU_srcOf huK hN0, rowR_srcOf huK hN0, rowR_srcOf huK hN0]
  have hcard := card_lift (n := n) (s := s) (T := T) (bt := bt) (AB := AB) (BC := BC) (AC := AC)
    (KK := KK) hp hk hkp (u := u) ha hb hj
  simp only at hcard
  rw [hcard]
  -- the count of the candidate
  have hq2 : a * n + b < n * n := Nat.mul_add_lt_mul ha hb
  unfold Light.Filter2.cntOf
  rw [Nat.mul_add_div_of_lt hq2, Nat.mul_add_mod_of_lt hq2]
  congr 2
  ext c
  simp only [Light.Filter2.InBlock, Light.Filter2.triSum, Nat.mul_add_div_of_lt hb,
    Nat.mul_add_mod_of_lt hb]
