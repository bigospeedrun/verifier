/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Batch.OProg
public import Submission.ThreeSumApsp.Batch.OMath

/-!
# The batched counting oracle: what its small procedures do

The specifications of the procedures 76 to 82 (`OProg`), as propositions about a program `P`, with
their times.  They are proved in `OTables` (the tables) and `OWrite` (writeSrc).
-/

@[expose] public section

namespace Light.Batch

open ThreeSumApsp ThreeSumApsp.Batch Light.Sec4

/-! ## Times -/

def tPowNat (e : ℕ) : ℕ := 12 * e + 12
def tResidTab (len V p : ℕ) : ℕ := len * (emodTime V p + 30) + 10
def tSmallTab (len V p : ℕ) : ℕ := len * (emodTime V p + 30) + 10
def tRowTab (nb N0 : ℕ) : ℕ := nb * (N0 * 30 + 30) + 10
def tDivTab (k : ℕ) : ℕ := k * (k * 30 + 30) + 10
def tZTab (len : ℕ) : ℕ := len * 60 + 20
/-- writeSrc: the clearing of `sz` cells, then the products, rows and cells. -/
def tWriteSrc (sz KKb n k s : ℕ) : ℕ :=
  tFill sz + KKb * (n * (k * (s * 60 + 60) + 30) + 60) + 30

/-! ## Specifications -/

variable (lim : Limits) (P : Program)

/-- powNat(b, e) returns `b^e`, for `b ≥ 1`, and changes no cell. -/
def PowNatSpec : Prop :=
  ∀ (b e : ℕ) (μ : ℕ → ℤ) (d : ℕ), 1 ≤ b → ((b ^ e + e + 1 : ℕ) : ℤ) ≤ lim.word →
    Meets lim P pPowNat d [b, e] μ (tPowNat e) fun r μ' => r = (b ^ e : ℕ) ∧ μ' = μ

/-- residTab(dst, src, len, sgn, p, fr), `sgn = ±1`: `dst[q] := resid p (sgn · src[q])`.  It changes
the `len` cells from dst and cells from fr on (the table of emod). -/
def ResidTabSpec : Prop :=
  ∀ (dst src : ℕ) (W : List ℤ) (sgn : ℤ) (p V fr : ℕ) (μ : ℕ → ℤ) (d : ℕ),
    (sgn = 1 ∨ sgn = -1) → Seg μ src W → (∀ w ∈ W, |w| ≤ V) → Emod.Pre lim p V fr →
    dst + W.length ≤ fr → src + W.length ≤ fr → Apart dst W.length src W.length →
    d + 1 ≤ lim.depth →
    Meets lim P pResidTab d [dst, src, W.length, sgn, p, fr] μ (tResidTab W.length V p)
      fun _ μ' => SegN μ' dst (W.map fun w => resid p (sgn * w)) ∧
        SameOn (fun b => b < fr ∧ Outside dst W.length b) μ μ'

/-- smallTab(dst, len, mul, add, p, fr): `dst[h] := resid p (h · mul + add)`. -/
def SmallTabSpec : Prop :=
  ∀ (dst len : ℕ) (mul add : ℤ) (p V fr : ℕ) (μ : ℕ → ℤ) (d : ℕ),
    (∀ h < len, |(h : ℤ) * mul + add| ≤ V) → |mul| ≤ V → |add| ≤ V → (len : ℤ) ≤ V →
    Emod.Pre lim p V fr → dst + len ≤ fr → d + 1 ≤ lim.depth →
    Meets lim P pSmallTab d [dst, len, mul, add, p, fr] μ (tSmallTab len V p)
      fun _ μ' => SegN μ' dst ((List.range len).map fun h => resid p ((h : ℤ) * mul + add)) ∧
        SameOn (fun b => b < fr ∧ Outside dst len b) μ μ'

/-- rowTab(dst, nb, N0, Mul): `dst[R] := R / N0 · Mul + R % N0` for `R < nb N0`. -/
def RowTabSpec : Prop :=
  ∀ (dst nb N0 Mul : ℕ) (μ : ℕ → ℤ) (d : ℕ), Std lim → 1 ≤ N0 → dst + nb * N0 < lim.space →
    (((nb + 1) * (Mul + N0 + 1) : ℕ) : ℤ) ≤ lim.word →
    Meets lim P pRowTab d [dst, nb, N0, Mul] μ (tRowTab nb N0)
      fun _ μ' => SegN μ' dst ((List.range (nb * N0)).map fun R => R / N0 * Mul + R % N0) ∧
        SameOutside μ μ' dst (nb * N0)

/-- divTab(dst, k): `dst[z] := z / k` for `z < k²`. -/
def DivTabSpec : Prop :=
  ∀ (dst k : ℕ) (μ : ℕ → ℤ) (d : ℕ), Std lim → dst + k * k < lim.space →
    Meets lim P pDivTab d [dst, k] μ (tDivTab k)
      fun _ μ' => SegN μ' dst ((List.range (k * k)).map fun z => z / k) ∧
        SameOutside μ μ' dst (k * k)

/-- zTab(zh, zl, rn, dk, len, k): `zh[q] := rn[q] / k`, `zl[q] := rn[q] % k`, from the table
`dk` of divTab. -/
def ZTabSpec : Prop :=
  ∀ (zh zl rn dk k : ℕ) (RN : List ℕ) (μ : ℕ → ℤ) (d : ℕ), Std lim → 1 ≤ k → SegN μ rn RN →
    SegN μ dk ((List.range (k * k)).map fun z => z / k) → (∀ z ∈ RN, z < k * k) →
    Apart zh RN.length zl RN.length → Apart zh RN.length rn RN.length →
    Apart zl RN.length rn RN.length → Apart zh RN.length dk (k * k) →
    zh + RN.length < lim.space → zl + RN.length < lim.space → rn + RN.length < lim.space →
    dk + k * k < lim.space →
    Meets lim P pZTab d [zh, zl, rn, dk, RN.length, k] μ (tZTab RN.length)
      fun _ μ' => SegN μ' zh (RN.map (· / k)) ∧ SegN μ' zl (RN.map (· % k)) ∧
        SameOn (fun b => Outside zh RN.length b ∧ Outside zl RN.length b) μ μ'

/-- What writeSrc assumes.  The source has `KK NP` rows of `D` cells from base; the tables T1
(`n²` residues) and T2 (`k` residues) and the table RS of the first rows `R / N0 · KK N0 + R % N0`
lie apart from it; the products `j0 + u`, `u < KKb`, have middle blocks that begin below `n`. -/
structure WriteSrcPre (μ : ℕ → ℤ) (base t1 t2 rs n k p D N0 j0 KKb s KK NP : ℕ) (T1 T2 : List ℕ) :
    Prop where
  std : Std lim
  p_pos : 1 ≤ p
  N0_pos : 1 ≤ N0
  k_pos : 1 ≤ k
  D_pos : 1 ≤ D
  seg1 : SegN μ t1 T1
  len1 : T1.length = n * n
  lt1 : ∀ x ∈ T1, x < p
  seg2 : SegN μ t2 T2
  len2 : T2.length = k
  lt2 : ∀ x ∈ T2, x < p
  segRS : SegN μ rs ((List.range NP).map fun R => R / N0 * (KK * N0) + R % N0)
  NP_mul : N0 ∣ NP
  nk_le : n * k ≤ NP
  KKb_le : KKb ≤ KK
  blocks : ∀ u < KKb, (j0 + u) * s < n
  sp_le : s * p ≤ D
  space : base + KK * NP * D < lim.space
  apart1 : Apart base (KK * NP * D) t1 (n * n)
  apart2 : Apart base (KK * NP * D) t2 k
  apartRS : Apart base (KK * NP * D) rs NP
  below1 : t1 + n * n < lim.space
  below2 : t2 + k < lim.space
  belowRS : rs + NP < lim.space
  word : (((j0 + KKb + 1) * (s + 1) + n * n + n * k + 2 * p + 4 : ℕ) : ℤ) ≤ lim.word

/-- writeSrc(base, t1, t2, rs, n, k, p, D, N0, j0, KKb, s, KK NP D): afterwards the `KK NP × D`
source at base holds `srcMat` for the batch `bt` (`j0 = bt KK`, the valid products `u < KKb`), and
no other cell has changed. -/
def WriteSrcSpec : Prop :=
  ∀ (base t1 t2 rs n k p D N0 bt KKb s KK NP : ℕ) (T1 T2 : List ℕ) (μ : ℕ → ℤ) (d : ℕ),
    WriteSrcPre lim μ base t1 t2 rs n k p D N0 (bt * KK) KKb s KK NP T1 T2 →
    d + 1 ≤ lim.depth →
    Meets lim P pWriteSrc d [base, t1, t2, rs, n, k, p, D, N0, bt * KK, KKb, s, KK * NP * D] μ
      (tWriteSrc (KK * NP * D) KKb n k s) fun _ μ' =>
      (∀ ρ < KK * NP, ∀ κ < D, μ' (base + ρ * D + κ) =
        srcVal s p KK N0 (okX n s k (bt * KK + KKb) KK bt)
          (fGen n s p k KK bt (fun q => T1.getD q 0) (fun l => T2.getD l 0)) ρ κ) ∧
      SameOutside μ μ' base (KK * NP * D)

end Light.Batch
