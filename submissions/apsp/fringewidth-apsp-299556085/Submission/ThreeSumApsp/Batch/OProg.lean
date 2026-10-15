/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Batch.Program
public import Submission.ThreeSumApsp.Batch.OParams
public import Submission.ThreeSumApsp.Lang.Lib.Emod
public import Submission.ThreeSumApsp.Programs.Sec4.ChoosingParameters.Program

/-!
# The batched counting oracle: the program text

The program `oProg` is `base58B` (Theorem 30 with the batched band arrays, numbers 0 to 57), the
procedures 58 to 73 of Section 4.4 for the rational parameters `c = 20`, `θ = 56569/500000`
(`procs31 G20`: copy, fill, log4, …, and `⌈θ m⌉` at 73), and the procedures of the oracle from 74 on:

* 74 emod, 75 ceilDiv, 76 powNat(b, e) = b^e;
* 77 residTab(dst, src, len, sgn, p, fr): `dst[q] := (sgn · src[q]) mod p` for `q < len`;
* 78 smallTab(dst, len, mul, add, p, fr): `dst[h] := (h · mul + add) mod p` for `h < len`;
* 79 rowTab(dst, nb, N0, Mul): `dst[i N0 + o] := i · Mul + o` for `i < nb`, `o < N0`;
* 80 divTab(dst, k): `dst[h k + l] := h` for `h, l < k`;
* 81 zTab(zh, zl, rn, dk, len, k): `zh[q] := dk[rn[q]]`, then `zl[q] := rn[q] - k · zh[q]`;
* 82 writeSrc: one source of a batch;
* 83 queries: the queries of a batch;
* 84 oracle: the top procedure.
-/

@[expose] public section

namespace Light.Batch

open ThreeSumApsp Light.Sec4

/-! ## The procedure numbers -/

abbrev pEmod : ℕ := 74
abbrev pCeilDiv : ℕ := 75
abbrev pPowNat : ℕ := 76
abbrev pResidTab : ℕ := 77
abbrev pSmallTab : ℕ := 78
abbrev pRowTab : ℕ := 79
abbrev pDivTab : ℕ := 80
abbrev pZTab : ℕ := 81
abbrev pWriteSrc : ℕ := 82
abbrev pQueries : ℕ := 83
abbrev pOracle : ℕ := 84

/-! ## Small procedures -/

/-- powNat(b, e): locals 2 (counter) and 3 (the power). -/
def powNatBody : Stmt :=
  .set 3 (k 1) ;;
  .for 2 (v 1) (.set 3 (v 3 *' v 0)) ;;
  .set 0 (v 3)

/-- residTab(dst, src, len, sgn, p, fr): local 6 is the counter, 7 the residue. -/
def residTabBody : Stmt :=
  .for 6 (v 2) (
    .call pEmod [v 3 *' M (v 1 +' v 6), v 4, v 5] 7 ;;
    .store (v 0 +' v 6) (v 7))

/-- smallTab(dst, len, mul, add, p, fr): local 6 is the counter, 7 the residue. -/
def smallTabBody : Stmt :=
  .for 6 (v 1) (
    .call pEmod [v 6 *' v 2 +' v 3, v 4, v 5] 7 ;;
    .store (v 0 +' v 6) (v 7))

/-- rowTab(dst, nb, N0, Mul): locals 4 and 5 are the counters i and o. -/
def rowTabBody : Stmt :=
  .for 4 (v 1) (.for 5 (v 2) (.store (v 0 +' v 4 *' v 2 +' v 5) (v 4 *' v 3 +' v 5)))

/-- divTab(dst, k): locals 2 and 3 are the counters h and l. -/
def divTabBody : Stmt :=
  .for 2 (v 1) (.for 3 (v 1) (.store (v 0 +' v 2 *' v 1 +' v 3) (v 2)))

/-- zTab(zh, zl, rn, dk, len, k): local 6 is the counter. -/
def zTabBody : Stmt :=
  .for 6 (v 4) (.store (v 0 +' v 6) (M (v 3 +' M (v 2 +' v 6)))) ;;
  .for 6 (v 4) (.store (v 1 +' v 6) (M (v 2 +' v 6) -' v 5 *' M (v 0 +' v 6)))

/-! ## One source of a batch -/

namespace WS

/-- The locals of writeSrc: the arguments base, T1, T2, RS, n, k, p, D, N0, j0, KKb, s, sz; then
the counters u, a, l, cl, the first vertex c0 = (j0 + u) s of the middle block, its length len, a
temporary, and the address of the row. -/
abbrev Base : ℕ := 0
@[inherit_doc Base] abbrev T1 : ℕ := 1
@[inherit_doc Base] abbrev T2 : ℕ := 2
@[inherit_doc Base] abbrev RS : ℕ := 3
@[inherit_doc Base] abbrev N : ℕ := 4
@[inherit_doc Base] abbrev Kd : ℕ := 5
@[inherit_doc Base] abbrev Pr : ℕ := 6
@[inherit_doc Base] abbrev Dd : ℕ := 7
@[inherit_doc Base] abbrev N0 : ℕ := 8
@[inherit_doc Base] abbrev J0 : ℕ := 9
@[inherit_doc Base] abbrev KKb : ℕ := 10
@[inherit_doc Base] abbrev S : ℕ := 11
@[inherit_doc Base] abbrev Sz : ℕ := 12
@[inherit_doc Base] abbrev U : ℕ := 13
@[inherit_doc Base] abbrev A : ℕ := 14
@[inherit_doc Base] abbrev Lc : ℕ := 15
@[inherit_doc Base] abbrev Cl : ℕ := 16
@[inherit_doc Base] abbrev C0 : ℕ := 17
@[inherit_doc Base] abbrev Len : ℕ := 18
@[inherit_doc Base] abbrev Tmp : ℕ := 19
@[inherit_doc Base] abbrev Row : ℕ := 20

end WS

open WS in
/-- One cell: `tmp := T1[a n + c0 + cl] + T2[l]`, reduced mod p; `row[cl p + tmp] := 1`. -/
def writeSrcCell : Stmt :=
  .set Tmp (M (v T1 +' v A *' v N +' v C0 +' v Cl) +' M (v T2 +' v Lc)) ;;
  .ite (v Tmp <' v Pr) .skip (.set Tmp (v Tmp -' v Pr)) ;;
  .store (v Row +' v Cl *' v Pr +' v Tmp) (k 1)

open WS in
/-- The row `R = a k + l` of the product `u`: its address `base + (RS[R] + u N0) D`, then its cells. -/
def writeSrcRow : Stmt :=
  .set Row (v Base +' (M (v RS +' v A *' v Kd +' v Lc) +' v U *' v N0) *' v Dd) ;;
  .for Cl (v Len) writeSrcCell

open WS in
/-- The product `u` of the batch: its middle block, then its rows. -/
def writeSrcProd : Stmt :=
  .set C0 ((v J0 +' v U) *' v S) ;;
  .ite (v C0 +' v S ≤' v N) (.set Len (v S)) (.set Len (v N -' v C0)) ;;
  .for A (v N) (.for Lc (v Kd) writeSrcRow)

open WS in
/-- writeSrc(base, T1, T2, RS, n, k, p, D, N0, j0, KKb, s, sz): clear the `sz` cells, then mark the
cells of the products `u < KKb`. -/
def writeSrcBody : Stmt :=
  .call Proc.fill [v Base, v Sz, k 0] Tmp ;;
  .for U (v KKb) writeSrcProd

/-! ## The queries of a batch -/

namespace QS

/-- The locals of queries: the arguments b0, ZL, ZH, RV, n, k, N0, K0, KKb, cnt, j0; then the
slot g, h, the counters a, b, the two positions I, J, the answer, the place of the counts of the
product, and the counter u of the products. -/
abbrev B0 : ℕ := 0
@[inherit_doc B0] abbrev ZL : ℕ := 1
@[inherit_doc B0] abbrev ZH : ℕ := 2
@[inherit_doc B0] abbrev RV : ℕ := 3
@[inherit_doc B0] abbrev N : ℕ := 4
@[inherit_doc B0] abbrev Kd : ℕ := 5
@[inherit_doc B0] abbrev N0 : ℕ := 6
@[inherit_doc B0] abbrev K0 : ℕ := 7
@[inherit_doc B0] abbrev KKb : ℕ := 8
@[inherit_doc B0] abbrev Cnt : ℕ := 9
@[inherit_doc B0] abbrev J0 : ℕ := 10
@[inherit_doc B0] abbrev G : ℕ := 11
@[inherit_doc B0] abbrev H : ℕ := 12
@[inherit_doc B0] abbrev A : ℕ := 13
@[inherit_doc B0] abbrev B : ℕ := 14
@[inherit_doc B0] abbrev I : ℕ := 15
@[inherit_doc B0] abbrev J : ℕ := 16
@[inherit_doc B0] abbrev Res : ℕ := 17
@[inherit_doc B0] abbrev Dst : ℕ := 18
@[inherit_doc B0] abbrev Uq : ℕ := 19

end QS

open QS in
/-- The query of the pair `(a, b)` in the slot `(g, h)`. -/
def queryCell : Stmt :=
  .set I (M (v RV +' v A *' v Kd +' M (v ZL +' v A *' v N +' v B)) +' v G *' v N0) ;;
  .set J (M (v RV +' v B *' v Kd +' M (v ZH +' v A *' v N +' v B)) +' v H *' v N0) ;;
  .call Proc.queryAt [v I, v J, v B0] Res ;;
  .store (v Dst +' v A *' v N +' v B) (v Res)

open QS in
/-- The product `u = g K₀ + h` of the batch: the queries of all pairs, then the next slot. -/
def queryProd : Stmt :=
  .set Dst (v Cnt +' (v J0 +' v Uq) *' (v N *' v N)) ;;
  .for A (v N) (.for B (v N) queryCell) ;;
  .set H (v H +' k 1) ;;
  .ite (v H =' v K0) (.set H (k 0) ;; .set G (v G +' k 1)) .skip

open QS in
/-- queries(b0, ZL, ZH, RV, n, k, N0, K0, KKb, cnt, j0): the products `u < KKb` of the batch, in the
slots `(g, h)`, `u = g K₀ + h`. -/
def queriesBody : Stmt :=
  .set G (k 0) ;; .set H (k 0) ;;
  .for Uq (v KKb) queryProd

/-! ## The top procedure -/

namespace OS

/-- The locals of the oracle: the arguments n, U, ab, bc, ac, s, p, cnt, fr; the parameters m, D,
L, t, N0, K0, KK, k, nb, NP, Nv, T, B; the addresses of the tables RAC, RNBC, RNAB, NL, HK, RS,
RV, DK, ZH, ZL, of the two sources and of the data structure; a temporary; the batch, its first
product j0 and its number KKb of products; the rows and the cells of a source; binom(L, m). -/
abbrev Nn : ℕ := 0
@[inherit_doc Nn] abbrev Ub : ℕ := 1
@[inherit_doc Nn] abbrev Ab : ℕ := 2
@[inherit_doc Nn] abbrev Bc : ℕ := 3
@[inherit_doc Nn] abbrev Ac : ℕ := 4
@[inherit_doc Nn] abbrev S : ℕ := 5
@[inherit_doc Nn] abbrev Pr : ℕ := 6
@[inherit_doc Nn] abbrev Cnt : ℕ := 7
@[inherit_doc Nn] abbrev Fr : ℕ := 8
@[inherit_doc Nn] abbrev Mm : ℕ := 9
@[inherit_doc Nn] abbrev Dd : ℕ := 10
@[inherit_doc Nn] abbrev Ll : ℕ := 11
@[inherit_doc Nn] abbrev Tt : ℕ := 12
@[inherit_doc Nn] abbrev N0 : ℕ := 13
@[inherit_doc Nn] abbrev K0 : ℕ := 14
@[inherit_doc Nn] abbrev KK : ℕ := 15
@[inherit_doc Nn] abbrev Kd : ℕ := 16
@[inherit_doc Nn] abbrev Nb : ℕ := 17
@[inherit_doc Nn] abbrev NP : ℕ := 18
@[inherit_doc Nn] abbrev Nv : ℕ := 19
@[inherit_doc Nn] abbrev Tp : ℕ := 20
@[inherit_doc Nn] abbrev Bt : ℕ := 21
@[inherit_doc Nn] abbrev aRAC : ℕ := 22
@[inherit_doc Nn] abbrev aRNBC : ℕ := 23
@[inherit_doc Nn] abbrev aRNAB : ℕ := 24
@[inherit_doc Nn] abbrev aNL : ℕ := 25
@[inherit_doc Nn] abbrev aHK : ℕ := 26
@[inherit_doc Nn] abbrev aRS : ℕ := 27
@[inherit_doc Nn] abbrev aRV : ℕ := 28
@[inherit_doc Nn] abbrev aDK : ℕ := 29
@[inherit_doc Nn] abbrev aZH : ℕ := 30
@[inherit_doc Nn] abbrev aZL : ℕ := 31
@[inherit_doc Nn] abbrev aX : ℕ := 32
@[inherit_doc Nn] abbrev aY : ℕ := 33
@[inherit_doc Nn] abbrev B0 : ℕ := 34
@[inherit_doc Nn] abbrev Tmp : ℕ := 35
@[inherit_doc Nn] abbrev Bn : ℕ := 36
@[inherit_doc Nn] abbrev J0 : ℕ := 37
@[inherit_doc Nn] abbrev KKb : ℕ := 38
@[inherit_doc Nn] abbrev Rows : ℕ := 39
@[inherit_doc Nn] abbrev Sz : ℕ := 40
@[inherit_doc Nn] abbrev Kb : ℕ := 41

end OS

open OS in
/-- The parameters. -/
def oParams : Stmt :=
  .call Proc.log4 [(k 4 *' v S) *' v Pr, v Fr] Mm ;;
  .set Dd (M (v Fr)) ;;
  .set Ll (k 20 *' v Mm) ;;
  .call Proc.switch31 [v Mm] Tt ;;
  .call pPowNat [k 3, v Ll -' v Mm] N0 ;;
  .call Sec2.pBinom [v Ll, v Mm, v Fr +' k 1] Kb ;;
  .call Sec2.pSqrt [v Kb] K0 ;;
  .set KK (v K0 *' v K0) ;;
  .call Sec2.pSqrt [v Pr -' k 1] Kd ;;
  .set Kd (v Kd +' k 1) ;;
  .call pCeilDiv [v Nn *' v Kd, v N0] Nb ;;
  .set Nb (v Nb +' k 1) ;;
  .set NP (v Nb *' v N0) ;;
  .set Nv (v K0 *' v NP) ;;
  .call pCeilDiv [v Nn, v S] Tp ;;
  .call pCeilDiv [v Tp, v KK] Bt

open OS in
/-- The addresses: the tables, the two sources, the data structure. -/
def oAddrs : Stmt :=
  .set aRAC (v Fr) ;;
  .set aRNBC (v aRAC +' v Nn *' v Nn) ;;
  .set aRNAB (v aRNBC +' v Nn *' v Nn) ;;
  .set aNL (v aRNAB +' v Nn *' v Nn) ;;
  .set aHK (v aNL +' v Kd) ;;
  .set aRS (v aHK +' v Kd) ;;
  .set aRV (v aRS +' v NP) ;;
  .set aDK (v aRV +' v NP) ;;
  .set aZH (v aDK +' v Kd *' v Kd) ;;
  .set aZL (v aZH +' v Nn *' v Nn) ;;
  .set Rows (v KK *' v NP) ;;
  .set Sz (v Rows *' v Dd) ;;
  .set aX (v aZL +' v Nn *' v Nn) ;;
  .set aY (v aX +' v Sz) ;;
  .set B0 (v aY +' v Sz)

open OS in
/-- The tables. -/
def oTables : Stmt :=
  .call pResidTab [v aRAC, v Ac, v Nn *' v Nn, k 1, v Pr, v B0] Tmp ;;
  .call pResidTab [v aRNBC, v Bc, v Nn *' v Nn, k 0 -' k 1, v Pr, v B0] Tmp ;;
  .call pResidTab [v aRNAB, v Ab, v Nn *' v Nn, k 0 -' k 1, v Pr, v B0] Tmp ;;
  .call pSmallTab [v aNL, v Kd, k 0 -' k 1, v Pr, v Pr, v B0] Tmp ;;
  .call pSmallTab [v aHK, v Kd, v Kd, k 0, v Pr, v B0] Tmp ;;
  .call pRowTab [v aRS, v Nb, v N0, v KK *' v N0] Tmp ;;
  .call pRowTab [v aRV, v Nb, v N0, v K0 *' v N0] Tmp ;;
  .call pDivTab [v aDK, v Kd] Tmp ;;
  .call pZTab [v aZH, v aZL, v aRNAB, v aDK, v Nn *' v Nn, v Kd] Tmp

open OS in
/-- One batch: its products, the two sources, the preprocessing, the queries. -/
def oBatch : Stmt :=
  .set J0 (v Bn *' v KK) ;;
  .ite (v J0 +' v KK ≤' v Tp) (.set KKb (v KK)) (.set KKb (v Tp -' v J0)) ;;
  .call pWriteSrc [v aX, v aRAC, v aNL, v aRS, v Nn, v Kd, v Pr, v Dd, v N0, v J0, v KKb, v S,
    v Sz] Tmp ;;
  .call pWriteSrc [v aY, v aRNBC, v aHK, v aRS, v Nn, v Kd, v Pr, v Dd, v N0, v J0, v KKb, v S,
    v Sz] Tmp ;;
  .call Proc.preCore [v Ll, v Mm, v Tt, v Nv, v Dd, v aX, v aY, v B0] Tmp ;;
  .call pQueries [v B0, v aZL, v aZH, v aRV, v Nn, v Kd, v N0, v K0, v KKb, v Cnt, v J0] Tmp

open OS in
/-- oracle(n, U, ab, bc, ac, s, p, cnt, fr). -/
def oracleBody : Stmt :=
  oParams ;; oAddrs ;; oTables ;; .for Bn (v Bt) oBatch

/-! ## The program -/

/-- The rational parameters `c = 20`, `θ = 56569/500000`. -/
def G20 : RatParams where
  a := 20
  b := 1
  p := 56569
  q := 500000
  m₀ := 1
  hb := by norm_num
  hq := by norm_num
  hc := by norm_num
  hp := by norm_num
  hθ := by norm_num
  hm₀ := by norm_num

/-- The procedures of the oracle, numbers 74 to 84. -/
def oProcs : Program :=
  [emodBody, Sec3.ceilDivBody, powNatBody, residTabBody, smallTabBody, rowTabBody, divTabBody,
    zTabBody, writeSrcBody, queriesBody, oracleBody]

/-- **The program of the batched counting oracle.** -/
def oProg : Program := base58B ++ procs31 G20 ++ oProcs

theorem length_base58B_procs31 : (base58B ++ procs31 G20).length = 74 := by
  simp [length_base58B, procs31]

/-- The procedures of the oracle stand at their numbers. -/
theorem oProg_at (n : ℕ) {body : Stmt} (hn : 74 ≤ n := by norm_num)
    (h : oProcs[n - 74]? = some body := by rfl) (R : Program) : (oProg ++ R)[n]? = some body := by
  rw [oProg, List.append_assoc, List.getElem?_append_right (by rw [length_base58B_procs31]; exact hn),
    length_base58B_procs31]
  exact getElem?_append_of_eq_some h R

/-- The procedures 58 to 73 stand at their numbers. -/
theorem oProg_at31 (n : ℕ) {body : Stmt} (hn : 58 ≤ n := by norm_num) (hn' : n < 74 := by norm_num)
    (h : (procs31 G20)[n - 58]? = some body := by rfl) (R : Program) :
    (oProg ++ R)[n]? = some body := by
  rw [oProg, List.append_assoc, List.append_assoc,
    List.getElem?_append_right (by rw [length_base58B]; exact hn), length_base58B]
  exact getElem?_append_of_eq_some h _

end Light.Batch
