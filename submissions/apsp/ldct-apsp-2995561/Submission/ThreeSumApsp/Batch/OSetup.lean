/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Batch.OQuery
public import Submission.ThreeSumApsp.Batch.OTables
public import Submission.ThreeSumApsp.Batch.OWrite
public import Submission.ThreeSumApsp.Filter2.Defs

/-!
# The batched counting oracle: the layout, the locals and the need

From the free pointer `fr` on, the oracle lays out the tables `RAC` (`n²`), `RNBC` (`n²`), `RNAB`
(`n²`), `NL` (`k`), `HK` (`k`), `RS` (`NP`), `RV` (`NP`), `DK` (`k²`), `ZH` (`n²`), `ZL` (`n²`), the
two sources X and Y (`KK NP D` each), and the data structure of Theorem 30 at `B0`.

`oLocP` are the locals after the parameters, `oLocA` after the addresses.  The need `oNeedAt`:
the word bound `oWordSum`, the cells up to the top of the data structure, the depth `L + 8`.
-/

@[expose] public section

namespace Light.Batch

open ThreeSumApsp Light.Sec4 Light.Filter2

/-! ## The addresses, relative to the free pointer -/

def oaRNBC (n fr : ℕ) : ℕ := fr + n * n
def oaRNAB (n fr : ℕ) : ℕ := oaRNBC n fr + n * n
def oaNL (n fr : ℕ) : ℕ := oaRNAB n fr + n * n
def oaHK (n p fr : ℕ) : ℕ := oaNL n fr + oDig p
def oaRS (n p fr : ℕ) : ℕ := oaHK n p fr + oDig p
def oaRV (n s p fr : ℕ) : ℕ := oaRS n p fr + oNP n s p
def oaDK (n s p fr : ℕ) : ℕ := oaRV n s p fr + oNP n s p
def oaZH (n s p fr : ℕ) : ℕ := oaDK n s p fr + oDig p * oDig p
def oaZL (n s p fr : ℕ) : ℕ := oaZH n s p fr + n * n
/-- The cells of a source. -/
def oSz (n s p : ℕ) : ℕ := oKK s p * oNP n s p * oD s p
def oaX (n s p fr : ℕ) : ℕ := oaZL n s p fr + n * n
def oaY (n s p fr : ℕ) : ℕ := oaX n s p fr + oSz n s p
/-- The base of the data structure. -/
def oB0 (n s p fr : ℕ) : ℕ := oaY n s p fr + oSz n s p

theorem oB0_eq (n s p fr : ℕ) : oB0 n s p fr = fr + oB0 n s p 0 := by
  simp only [oB0, oaY, oaX, oaZL, oaZH, oaDK, oaRV, oaRS, oaHK, oaNL, oaRNAB, oaRNBC]
  omega

/-! ## The locals -/

/-- The locals after the parameters (`oParams`): the arguments, then `m, D, L, t, N0, K0, KK, k, nb,
NP, Nv, T, B` at 9 to 21, zeros, and `binom(L, m)` at 41. -/
def oLocP (x : OracleInst) (fr : ℕ) : List ℤ :=
  ([x.n, x.U, x.ab, x.bc, x.ac, x.s, x.p, x.cnt, fr] : List ℕ).map (fun z : ℕ => (z : ℤ)) ++
  ([oM x.s x.p, oD x.s x.p, oL x.s x.p, oT x.s x.p, oN0 x.s x.p, oK0 x.s x.p, oKK x.s x.p,
    oDig x.p, oNb x.n x.s x.p, oNP x.n x.s x.p, oNv x.n x.s x.p, oProd x.n x.s,
    oBat x.n x.s x.p] : List ℕ).map (fun z : ℕ => (z : ℤ)) ++
  List.replicate 19 (0 : ℤ) ++ [(((oL x.s x.p).choose (oM x.s x.p) : ℕ) : ℤ)]

/-- The locals after the addresses (`oAddrs`), with the temporary, the batch, its first product and
its number of products. -/
def oLocA (x : OracleInst) (fr : ℕ) (tmp bn j0 kkb : ℤ) : List ℤ :=
  ([x.n, x.U, x.ab, x.bc, x.ac, x.s, x.p, x.cnt, fr] : List ℕ).map (fun z : ℕ => (z : ℤ)) ++
  ([oM x.s x.p, oD x.s x.p, oL x.s x.p, oT x.s x.p, oN0 x.s x.p, oK0 x.s x.p, oKK x.s x.p,
    oDig x.p, oNb x.n x.s x.p, oNP x.n x.s x.p, oNv x.n x.s x.p, oProd x.n x.s,
    oBat x.n x.s x.p] : List ℕ).map (fun z : ℕ => (z : ℤ)) ++
  ([fr, oaRNBC x.n fr, oaRNAB x.n fr, oaNL x.n fr, oaHK x.n x.p fr, oaRS x.n x.p fr,
    oaRV x.n x.s x.p fr, oaDK x.n x.s x.p fr, oaZH x.n x.s x.p fr, oaZL x.n x.s x.p fr,
    oaX x.n x.s x.p fr, oaY x.n x.s x.p fr, oB0 x.n x.s x.p fr] : List ℕ).map
      (fun z : ℕ => (z : ℤ)) ++
  [tmp, bn, j0, kkb] ++
  ([oKK x.s x.p * oNP x.n x.s x.p, oSz x.n x.s x.p, (oL x.s x.p).choose (oM x.s x.p)] :
    List ℕ).map (fun z : ℕ => (z : ℤ))

/-! ## The need -/

/-- Everything that the oracle forms or passes on is at most this. -/
def oWordSum (n U s p : ℕ) : ℕ :=
  100 + 10 ^ oM s p * (7 ^ oL s p * 7 ^ oL s p) + 7 ^ (oL s p + 1) + 10 ^ (oL s p + 1)
    + 2 ^ oL s p + 4 * (oL s p).choose (oM s p) + 4 + 4 * s * p + oD s p + 56569 * oM s p + 500000
    + 3 ^ (oL s p - oM s p) + oL s p + 1 + 4 * U + 16 * p + 16 + n * oDig p + oN0 s p
    + oNb n s p + oNP n s p + oNv n s p + n + s + oProd n s + oKK s p + oBat n s p
    + (oNb n s p + 1) * (oKK s p * oN0 s p + oN0 s p + 1) + (oProd n s + oKK s p + 1) * (s + 1)
    + n * n + 2 * p + 4 + oSz n s p + oK0 s p * oN0 s p

/-- The cells from the free pointer on: the tables, the sources, the data structure, and room for
the table of binomials and the table of emod. -/
def oCells (n U s p : ℕ) : ℕ :=
  oB0 n s p 0 + top (oPar n s p) (oT s p) 0 + oL s p + Nat.log 2 (U + 3 * p + 1) + 10

/-- The need of the oracle, for `n`, `U`, `s`, `p`. -/
def oNeedAt (n U s p : ℕ) : Need := ⟨oWordSum n U s p, oCells n U s p, oL s p + 8⟩

/-- **The need of the oracle** as a function of the parameters `[n, U, s, p]`. -/
def oNeed (ps : List ℕ) : Need := oNeedAt (ps.getD 0 0) (ps.getD 1 0) (ps.getD 2 0) (ps.getD 3 0)

/-- A number below one of the summands is below `oWordSum`. -/
theorem le_oWordSum_of (n U s p : ℕ) {z : ℕ} (h : z ≤ 100 ∨ z ≤ 10 ^ oM s p * (7 ^ oL s p * 7 ^ oL s p)
    ∨ z ≤ 7 ^ (oL s p + 1) ∨ z ≤ 10 ^ (oL s p + 1) ∨ z ≤ 2 ^ oL s p
    ∨ z ≤ 4 * (oL s p).choose (oM s p) + 4 ∨ z ≤ 4 * s * p ∨ z ≤ oD s p
    ∨ z ≤ 56569 * oM s p + 500000 ∨ z ≤ 3 ^ (oL s p - oM s p) + oL s p + 1
    ∨ z ≤ 4 * U + 16 * p + 16 ∨ z ≤ n * oDig p + oN0 s p + oNb n s p + oNP n s p + oNv n s p
    ∨ z ≤ n + s + oProd n s + oKK s p + oBat n s p
    ∨ z ≤ (oNb n s p + 1) * (oKK s p * oN0 s p + oN0 s p + 1)
    ∨ z ≤ (oProd n s + oKK s p + 1) * (s + 1) + n * n + n * oDig p + 2 * p + 4
    ∨ z ≤ oSz n s p + oK0 s p * oN0 s p) : z ≤ oWordSum n U s p := by
  unfold oWordSum
  generalize 10 ^ oM s p * (7 ^ oL s p * 7 ^ oL s p) = A at h
  generalize 7 ^ (oL s p + 1) = B at h
  generalize 10 ^ (oL s p + 1) = C at h
  generalize 2 ^ oL s p = E at h
  generalize 3 ^ (oL s p - oM s p) = F at h
  omega

/-- A number that is at most `oWordSum` fits in a word. -/
theorem oWordSum_fits {lim : Limits} {n U s p fr d : ℕ} (hok : (oNeedAt n U s p).Ok lim fr d)
    {z : ℕ} (hz : z ≤ oWordSum n U s p := by apply le_oWordSum_of; omega) : ((z : ℕ) : ℤ) ≤ lim.word :=
  le_trans (by exact_mod_cast hz) hok.word

end Light.Batch
