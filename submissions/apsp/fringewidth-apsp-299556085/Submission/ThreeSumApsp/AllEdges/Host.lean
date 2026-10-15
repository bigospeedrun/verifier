/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.AllEdges.Loop
public import Submission.ThreeSumApsp.Programs.Sec3.Theorem17.Host.Program

/-!
# All-edges host: the top procedures

The host of all-edges Exact Triangle has two procedures above the loop.

* aeTop(n, U, ab, bc, ac, out, fr) fills the `n²` flags with 0, puts the address `out` into the cell
  `fr`, and calls aeCore with the free pointer `fr + 1`.
* aeCore(n, U, ab, bc, ac, fr) is et17 with the loop of the all-edges form; the address of the flags
  is read from the cell `fr - 1`.  The first two parts of et17 (the parameters; the prime, the sizes
  and the addresses) are used unchanged, with their specifications.  In the small case aeCore calls
  the all-edges brute force.

The procedures of the host of Theorem 17 stay in the program, so that its context `Et17Ctx` holds and
the specifications of the parts can be used.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

open Et17 in
/-- The third part of aeCore: the residues, the classes, the chunks, and the loop over the
instances, which gets the address of the flags from the cell below the free pointer. -/
def aeTables (ν : Et17Nums) (pAELoop : ℕ) : Stmt :=
  .call ν.pDbl [v Free, v ThePrime, v Bits] Small ;;
  .call ν.pResidues [v AdrAB, v ResAB, v SizeSq, v Free, v Bits] Small ;;
  .call ν.pResidues [v AdrBC, v ResBC, v SizeSq, v Free, v Bits] Small ;;
  .call ν.pResidues [v AdrAC, v ResAC, v SizeSq, v Free, v Bits] Small ;;
  .call ν.pClasses [v ResAB, v Size, v ThePrime, v Cls, v Cur, v Rows, v Cols] Small ;;
  .call ν.pChunks [v Cls, v ThePrime, v Cap, v TabR, v TabL, v TabW] NumChunks ;;
  .set NumInst (v NumPieces *' v NumChunks) ;;
  .call pAELoop [v Size, v ParD, v ThePrime, v PieceLen, v NumChunks, v NumInst, v AdrAB, v AdrBC,
    v AdrAC, v ResAC, v ResBC, v Rows, v Cols, v TabR, v TabL, v TabW, v MatX, v MatY, v AdrOut,
    v SolverFree, M (v Free -' k 1)] 0

open Et17 in
/-- aeCore(n, U, ab, bc, ac, fr), with the address of the flags in the cell fr - 1. -/
def aeCoreBody (ν : Et17Nums) (pAEBrute pAELoop : ℕ) : Stmt :=
  et17Params ν ;;
  .ite (v Small =' k 1)
    (.call pAEBrute [v Size, v Bound, v AdrAB, v AdrBC, v AdrAC, M (v Free -' k 1), v Free] 0)
    (et17Sizes ν ;; aeTables ν pAELoop)

/-- aeTop(n, U, ab, bc, ac, out, fr). -/
def aeTopBody (pFill pCore : ℕ) : Stmt :=
  .call pFill [v 5, v 0 *' v 0, k 0] 7 ;;
  .store (v 6) (v 5) ;;
  .call pCore [v 0, v 1, v 2, v 3, v 4, v 6 +' k 1] 7 ;;
  .set 0 (k 0)

/-! ## Time -/

/-- A bound on the time of the loop over the instances: at most 4ng instances, with pieces of at
most q vertices and at most cap query pairs, and at most falsePositiveBound + n² scans. -/
noncomputable def aeLoopBound (Tn : List ℕ → ℕ) (n U D g : ℕ) : ℕ :=
  4 * n * g *
      (tWrites n D (pieceSizeNat D g) + supTime Tn n D (queryCapNat n D)
        + tAEAnswers (queryCapNat n D))
    + (tScanCall (pieceSizeNat D g) + 20) * (falsePositiveBound n U D + n * n) + 14

/-- The time of aeCore after the tests, if n is not small. -/
noncomputable def aeHostMain (Tn : List ℕ → ℕ) (n U D g : ℕ) : ℕ :=
  chooseTime n U D + tQueryCapNat n D + tCeilDiv (Nat.sqrt D) g + tCeilDiv n (pieceSizeNat D g)
    + tBitLen U + tDblTable (bitLen U) + 3 * tResidues (n * n) (bitLen U) + tClasses n (Nat.sqrt D)
    + tChunks (Nat.sqrt D) (4 * n * g) + aeLoopBound Tn n U D g + 300

/-- A bound on the time of aeCore in the worst case. -/
noncomputable def aeCoreTime (Dfun Gfun tD tG : ℕ → ℕ) (Tn : List ℕ → ℕ) (n U : ℕ) : ℕ :=
  hostSetup tD tG n (Dfun n) +
    if SmallCase n (Dfun n) (Gfun (Dfun n)) then tAEBrute n + 20
    else aeHostMain Tn n U (Dfun n) (Gfun (Dfun n))

/-- **A bound on the time of the all-edges host.** -/
noncomputable def aeHostTime (Dfun Gfun tD tG : ℕ → ℕ) (Tn : List ℕ → ℕ) (n U : ℕ) : ℕ :=
  fillTime (n * n) + aeCoreTime Dfun Gfun tD tG Tn n U + 40

/-- The time of the third part of aeCore in a run. -/
def aeRunTime (Tn : List ℕ → ℕ) (X : HostData) (U : ℕ) : ℕ :=
  tDblTable (bitLen U) + 3 * tResidues (X.n * X.n) (bitLen U) + tClasses X.n X.p
    + tChunks X.p X.chunkCount + tAELoop Tn X + 80

/-- **The need of the all-edges host**: that of the host of Theorem 17, one more cell and one more
level of calls, and the product `n²`. -/
def aeHostNeed (Dfun Gfun wD wG : ℕ → ℕ) (need : List ℕ → Need) (n U : ℕ) : Need :=
  ⟨(hostNeed Dfun Gfun wD wG need n U).word + n * n,
    (hostNeed Dfun Gfun wD wG need n U).cells + 1,
    (hostNeed Dfun Gfun wD wG need n U).depth + 1⟩

/-! ## The context -/

/-- The context of aeTop: the context of et17, and the procedures of the all-edges host. -/
structure AECtx (P₀ R : Program) (ν : Et17Nums) (pAEBrute pAELoop pScanPairsAE pCore pFill : ℕ)
    (Tn : List ℕ → ℕ) (need : List ℕ → Need) (Dfun Gfun tD tG wD wG : ℕ → ℕ) : Prop where
  et : Et17Ctx P₀ R ν Tn need Dfun Gfun tD tG wD wG
  hScanPairsAE : (P₀ ++ R)[pScanPairsAE]? = some (scanPairsAEBody ν.pScan)
  hAELoop : (P₀ ++ R)[pAELoop]? = some (aeLoopBody ν.pS ν.pWriteX ν.pWriteY pScanPairsAE)
  hAEBrute : (P₀ ++ R)[pAEBrute]? = some (aeBruteBody ν.pScan)
  hCore : (P₀ ++ R)[pCore]? = some (aeCoreBody ν pAEBrute pAELoop)
  hFill : (P₀ ++ R)[pFill]? = some fillBody

variable {P₀ R : Program} {ν : Et17Nums} {pAEBrute pAELoop pScanPairsAE pCore pFill : ℕ}
  {Tn : List ℕ → ℕ} {need : List ℕ → Need} {Dfun Gfun tD tG wD wG : ℕ → ℕ}

/-- The context of the loop. -/
theorem AECtx.loop (C : AECtx P₀ R ν pAEBrute pAELoop pScanPairsAE pCore pFill Tn need Dfun Gfun tD
    tG wD wG) : AEHostCtx P₀ R ν.pS ν.pWriteX ν.pWriteY pScanPairsAE ν.pScan Tn need :=
  ⟨C.et.loop.sol, C.et.loop.writeX, C.et.loop.writeY, C.hScanPairsAE, C.et.loop.scan⟩

/-! ## The third part -/

open Et17 in
/-- **The third part of aeCore**: below the free pointer, the memory with the marks after all
instances.  The flags lie below the cell `fr` that holds their address, and they are 0. -/
theorem aeTables_spec (C : AECtx P₀ R ν pAEBrute pAELoop pScanPairsAE pCore pFill Tn need Dfun Gfun
    tD tG wD wG) {lim : Limits} {d : ℕ} (x : AEInst) (μ : ℕ → ℤ) (fr D g a b : ℕ)
    (hpre : x.Pre μ fr) (hcell : μ fr = x.out) (hzero : ∀ q < x.n * x.n, μ (x.out + q) = 0)
    (hbig : BigCase x.n D g) (hok : (hostNeedAt a b need x.n x.U D g).Ok lim (fr + 1) d) :
    Ends lim (P₀ ++ R) d (aeTables ν pAELoop) ⟨frame (et17LocB x.toTriInst (fr + 1) D g), μ⟩
      (aeRunTime Tn (hostData x.toTriInst D g) x.U)
      fun σ' => Kept (withMarks μ x.out (x.n * x.n)
        ((hostData x.toTriInst D g).marks (hostData x.toTriInst D g).m)) σ'.mem (fr + 1) := by
  have hpre' : x.toTriInst.Pre μ (fr + 1) := hpre.toPre.mono (by omega)
  have hr := ready_of hpre' hbig hok
  have hlim := hostLim_of_ok hbig hok
  have hv := hostData_valid hpre' hbig
  have hbo := hpre.belowOut
  have hAB := hpre.apartAB
  have hBC := hpre.apartBC
  have hAC := hpre.apartAC
  unfold et17LocB
  generalize hX : hostData x.toTriInst D g = X at hr hlim hv ⊢
  have hn : X.n = x.n := by rw [← hX]; rfl
  have hdepth := hr.depth
  have hplaces := host_places X x.U (fr + 1)
  have hfr : fr + 1 ≤ aX X x.U (fr + 1) := by omega
  unfold aeTables aeRunTime
  refine resid_then C.et.hDbl C.et.hResid C.et.hResidues hr (fun r₁ μ₁ hresid => ?_) (by omega)
  refine classes_then C.et.hClasses C.et.hChunks hr hv.cap_pos hresid.rab
    (fun r₂ μ₂ hclass => ?_) (by omega)
  -- below the free pointer nothing has changed
  have hsame : ∀ c < fr + 1, μ₂ c = μ c := fun c hc =>
    (hclass.same c (Or.inl (by omega))).trans (hresid.same c (Or.inl hc))
  -- NumInst := NumPieces * NumChunks
  have hcount := hlim.count
  have hm : (X.m : ℤ) = (X.h : ℤ) * X.chunkCount := by
    rw [HostData.m]
    push_cast
    rfl
  have hpos : (0 : ℤ) ≤ (X.h : ℤ) * X.chunkCount := by positivity
  light_set (X.m : ℕ) using hm
  -- the loop
  have hcell₂ : μ₂ fr = x.out := (hsame fr (by omega)).trans hcell
  have hzero₂ : ∀ q < X.n * X.n, μ₂ (x.out + q) = 0 := fun q hq => by
    rw [hn] at hq
    rw [hsame _ (by omega)]
    exact hzero q hq
  have hL : AEMarksLay X (hostAddr x.toTriInst X (fr + 1)) x.out := by
    have hnn : X.n * X.n = x.n * x.n := by rw [hn]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp only [hostAddr, Apart, hnn]
    all_goals try omega
  have hloop := aeLoop_spec C.loop ⟨hv, hr.leAB, hr.leBC, hr.leAC⟩ (hostMem_of hr hresid hclass)
    (hostLay_of hr (hr.chunkCount_le hv.cap_pos)) hlim hL hzero₂
  refine Ends.callTo (Meets.of_body (Q := fun _ μ' => Kept (aeBase X x.out μ₂ X.m) μ'
      (hostAddr x.toTriInst X (fr + 1)).x) C.hAELoop hloop) ?_ ?_ (by omega) (by simp; omega)
  · intro r μ₃ hkept c hc
    change μ₃ c = _
    rw [hkept c (by simp only [hostAddr]; omega)]
    simp only [aeBase, hn]
    unfold withMarks
    split_ifs
    · rfl
    · exact hsame c hc
  · constructor
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp [Expr.Safe]
      have htop := hr.top
      have hsp := hr.space
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      simp only [Limits.Addr]
      omega
    · simp [aeLoopArgs, hostAddr, setLocal, hcell₂]

/-! ## The time of a run -/

namespace AETime

private theorem tWrites_mono (n D : ℕ) {a b : ℕ} (h : a ≤ b) : tWrites n D a ≤ tWrites n D b := by
  unfold tWrites tWriteX tWriteY
  gcongr

private theorem le_supTime (Tn : List ℕ → ℕ) (n D : ℕ) {w cap : ℕ} (h : w ≤ cap) :
    Tn [n, D, w] ≤ supTime Tn n D cap :=
  Finset.le_sup (f := fun w => Tn [n, D, w]) (Finset.mem_range.2 (by omega))

/-- The time of one instance is at most the worst case plus the time of its scans. -/
private theorem instance_le (Tn : List ℕ → ℕ) (n D execs : ℕ) {len q w cap : ℕ} (hlen : len ≤ q)
    (hw : w ≤ cap) :
    tWrites n D len + Tn [n, D, w] + tScanPairsAE w len execs
      ≤ tWrites n D q + supTime Tn n D cap + tAEAnswers cap + (tScanCall q + 20) * execs := by
  have hwrites := tWrites_mono n D hlen
  have hsolver := le_supTime Tn n D hw
  have hanswers : tAEAnswers w ≤ tAEAnswers cap := by
    unfold tAEAnswers
    gcongr
  have hscans : (tScanCall len + 20) * execs ≤ (tScanCall q + 20) * execs := by
    unfold tScanCall tScan
    gcongr
  unfold tScanPairsAE
  omega

private theorem sum_le_mul_add {m M A B E : ℕ} {f e : ℕ → ℕ} (hf : ∀ t < m, f t ≤ A + B * e t)
    (hm : m ≤ M) (he : ∑ t ∈ Finset.range m, e t ≤ E) :
    ∑ t ∈ Finset.range m, f t ≤ M * A + B * E :=
  calc ∑ t ∈ Finset.range m, f t ≤ ∑ t ∈ Finset.range m, (A + B * e t) :=
        Finset.sum_le_sum fun t ht => hf t (Finset.mem_range.1 ht)
    _ = m * A + B * ∑ t ∈ Finset.range m, e t := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
          Finset.mul_sum]
    _ ≤ M * A + B * E := Nat.add_le_add (Nat.mul_le_mul_right _ hm) (Nat.mul_le_mul_left _ he)

private theorem chunkCount_le_m {X : HostData} (hv : X.Valid) : X.chunkCount ≤ X.m := by
  have hn := hv.n_pos
  have hq := hv.q_pos
  have hpieces : 1 ≤ X.h := by
    rw [HostData.h, Nat.ceilDiv_eq_add_pred_div, Nat.le_div_iff_mul_le (by omega)]
    omega
  rw [HostData.m]
  exact Nat.le_mul_of_pos_left _ hpieces

variable {x : TriInst} {μ : ℕ → ℤ} {fr D g : ℕ}

private theorem sum_aeExecs_le_bound (hpre : x.Pre μ fr) (hbig : BigCase x.n D g) :
    ∑ t ∈ Finset.range (hostData x D g).m, (hostData x D g).aeExecs t
      ≤ falsePositiveBound x.n x.U D + x.n * x.n :=
  (HostData.sum_aeExecs_le (hostData_valid hpre hbig)).trans
    (Nat.add_le_add_right (F_le_falsePositiveBound hpre hbig) _)

private theorem tAELoop_le (hpre : x.Pre μ fr) (hbig : BigCase x.n D g) (Tn : List ℕ → ℕ) :
    tAELoop Tn (hostData x D g) ≤ aeLoopBound Tn x.n x.U D g :=
  Nat.add_le_add_right (sum_le_mul_add
    (fun _ ht => instance_le Tn x.n D _ (Nat.min_le_left _ _) ((hostData x D g).w_le_cap ht))
    (hostData_m_le hbig) (sum_aeExecs_le_bound hpre hbig)) 14

/-- **The time of a run after the choice of the prime is within the worst case.** -/
theorem aeRunTime_le (hpre : x.Pre μ fr) (hbig : BigCase x.n D g) (Tn : List ℕ → ℕ) :
    aeRunTime Tn (hostData x D g) x.U
      ≤ tDblTable (bitLen x.U) + 3 * tResidues (x.n * x.n) (bitLen x.U)
        + tClasses x.n (Nat.sqrt D) + tChunks (Nat.sqrt D) (4 * x.n * g)
        + aeLoopBound Tn x.n x.U D g + 80 := by
  have hprime : (hostData x D g).p ≤ Nat.sqrt D := hostData_p_le x g hbig.sixteen_le
  have hchunks : (hostData x D g).chunkCount ≤ 4 * x.n * g :=
    (chunkCount_le_m (hostData_valid hpre hbig)).trans (hostData_m_le hbig)
  have hloop := tAELoop_le hpre hbig Tn
  have hn : (hostData x D g).n = x.n := rfl
  unfold aeRunTime
  rw [hn]
  unfold tClasses tChunks
  omega

end AETime

/-! ## The procedures -/

/-- An instance stays where it is if no cell below the free pointer changes. -/
theorem AEInst.Pre.keep {x : AEInst} {μ μ' : ℕ → ℤ} {fr : ℕ} (h : x.Pre μ fr)
    (hs : Kept μ μ' fr) : x.Pre μ' fr :=
  { h with toPre := h.toPre.keep hs }

/-- The free pointer may grow. -/
theorem AEInst.Pre.mono {x : AEInst} {μ : ℕ → ℤ} {fr fr' : ℕ} (h : x.Pre μ fr) (hfr : fr ≤ fr') :
    x.Pre μ fr' :=
  { h with toPre := h.toPre.mono hfr, belowOut := h.belowOut.trans hfr }

open Et17 in
/-- **aeCore writes the flags.** -/
theorem aeCore_spec (C : AECtx P₀ R ν pAEBrute pAELoop pScanPairsAE pCore pFill Tn need Dfun Gfun
    tD tG wD wG) {lim : Limits} {d : ℕ} (x : AEInst) (μ : ℕ → ℤ) (fr : ℕ) (hpre : x.Pre μ fr)
    (hcell : μ fr = x.out) (hzero : ∀ q < x.n * x.n, μ (x.out + q) = 0)
    (hok : (hostNeed Dfun Gfun wD wG need x.n x.U).Ok lim (fr + 1) d) :
    Ends lim (P₀ ++ R) d (aeCoreBody ν pAEBrute pAELoop)
      ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, (fr + 1 : ℕ)], μ⟩
      (aeCoreTime Dfun Gfun tD tG Tn x.n x.U) fun σ' =>
        Seg σ'.mem x.out (aeFlags x.n x.AB x.BC x.AC) ∧ KeptBut μ σ'.mem fr x.out (x.n * x.n) := by
  have hpre' : x.toTriInst.Pre μ (fr + 1) := hpre.toPre.mono (by omega)
  have hparams := et17Params_spec C.et x.toTriInst μ (fr + 1) hpre' hok
  have hone : (1 : ℤ) ≤ lim.word := by
    have hword := hok.word
    simp only [hostNeed, hostNeedAt, hostWord] at hword
    omega
  have hbo := hpre.belowOut
  rw [← frame_append_zeros [(x.n : ℤ), x.U, x.ab, x.bc, x.ac, ((fr + 1 : ℕ) : ℤ)] 29]
  unfold hostNeed at hok
  unfold aeCoreBody aeCoreTime hostSetup
  generalize Dfun x.n = D at *
  generalize Gfun D = g at *
  refine Ends.next _ (hparams.mono le_rfl ?_) (by omega)
  rintro _ rfl
  by_cases hs : SmallCase x.n D g
  · -- the small case: the brute force
    rw [if_pos hs]
    have hbrute : (aeBruteNeed x.n x.U).Ok lim (fr + 1) (d + 1) :=
      hok.mono (by simp only [aeBruteNeed, hostNeedAt, hostWord]; omega)
        (by simp only [aeBruteNeed]; omega) (by simp only [aeBruteNeed, hostNeedAt]; omega)
    have hdepth := hok.depth
    simp only [hostNeedAt] at hdepth
    have hcells := hok.cells
    refine Ends.iteLast (fun _ => ?_) (fun h => absurd (by simp [et17LocA, hs]) h) (by simp; omega)
    refine Ends.callTo (aeBrute_meets C.hAEBrute C.et.loop.scan x μ (fr + 1)
      (hpre.mono (by omega)) hbrute) ?_ ?_ (by omega) (by simp; omega)
    · rintro _ μ' ⟨hseg, hkept⟩
      exact ⟨hseg, fun c hc => hkept c ⟨by omega, hc.2⟩⟩
    · constructor
      · intro e he
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        have hsp := hok.space
        rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals simp [Expr.Safe, et17LocA]
        refine ⟨⟨by omega, by omega⟩, ?_⟩
        simp only [Limits.Addr]
        omega
      · simp [et17LocA, hcell]
  rw [if_neg hs]
  refine Ends.iteLast (fun h => absurd h (by simp [et17LocA, hs])) (fun _ => ?_) (by simp; omega)
  -- otherwise: the sizes, then the tables and the loop over the instances
  have hbig := not_smallCase_iff.1 hs
  have htime := AETime.aeRunTime_le hpre' hbig Tn
  refine Ends.next _ ((et17Sizes_spec C.et x.toTriInst μ (fr + 1) D g _ _ hpre' hbig hok).mono
    le_rfl ?_) (by unfold aeHostMain; simp; omega)
  rintro _ ⟨μ', rfl, hk⟩
  have hpre₁ : x.Pre μ' fr := hpre.keep fun c hc => hk c (by omega)
  refine (aeTables_spec C x μ' fr D g _ _ hpre₁ ((hk fr (by omega)).trans hcell)
    (fun q hq => (hk _ (by omega)).trans (hzero q hq)) hbig hok).mono
    (by unfold aeHostMain; simp; omega) ?_
  rintro σ'' hk'
  have hv := hostData_valid hpre' hbig
  refine ⟨fun q hq => ?_, fun c hc => ?_⟩
  · rw [length_aeFlags] at hq
    rw [hk' _ (by omega), withMarks_in _ hq, getElem_aeFlags]
    exact HostData.bit_marks_m hv hq
  · rw [hk' c (by omega), withMarks_out _ hc.2]
    exact hk c (by omega)

/-- **aeTop solves all-edges Exact Triangle.** -/
theorem aeTop_spec (C : AECtx P₀ R ν pAEBrute pAELoop pScanPairsAE pCore pFill Tn need Dfun Gfun
    tD tG wD wG) {lim : Limits} {d : ℕ} (x : AEInst) (μ : ℕ → ℤ) (fr : ℕ) (hpre : x.Pre μ fr)
    (hok : (aeHostNeed Dfun Gfun wD wG need x.n x.U).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (aeTopBody pFill pCore)
      ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, x.out, fr], μ⟩
      (aeHostTime Dfun Gfun tD tG Tn x.n x.U) fun σ' => aeTask.Post x μ fr (σ'.loc 0) σ'.mem := by
  have hw := hok.space
  have hcells := hok.cells
  have hdepth := hok.depth
  have hword := hok.word
  simp only [aeHostNeed] at hcells hdepth hword
  have hbo := hpre.belowOut
  have hAB := hpre.apartAB
  have hBC := hpre.apartBC
  have hAC := hpre.apartAC
  have lAB := hpre.lenAB
  have lBC := hpre.lenBC
  have lAC := hpre.lenAC
  have hbAB := hpre.belowAB
  have hbBC := hpre.belowBC
  have hbAC := hpre.belowAC
  have hnn : ((x.n * x.n : ℕ) : ℤ) ≤ lim.word := by
    have : (0 : ℤ) ≤ ((hostNeed Dfun Gfun wD wG need x.n x.U).word : ℤ) := by positivity
    push_cast at hword ⊢
    omega
  have hcore : (hostNeed Dfun Gfun wD wG need x.n x.U).Ok lim (fr + 1) (d + 1) :=
    ⟨by push_cast at hword; omega, by omega, hw, by omega⟩
  unfold aeTopBody aeHostTime
  -- fill(out, n², 0)
  light_call (fill_meets (d := d + 1) (dst := x.out) (n := x.n * x.n) (x := 0) C.hFill hw
    (by omega)) with r₁ μ₁ ⟨hfill, same₁⟩
  -- mem[fr] := out
  refine Ends.storeToThen fr (x.out : ℤ) ?_ (by light_side) (by light_time)
  -- aeCore(n, U, ab, bc, ac, fr + 1)
  set μ₂ := Function.update μ₁ fr (x.out : ℤ) with hμ₂
  have hpre₂ : x.Pre μ₂ fr :=
    { hpre with
      segAB := fun i hi => by
        rw [hμ₂, Function.update_of_ne (by omega), same₁ _ (by omega)]
        exact hpre.segAB i hi
      segBC := fun i hi => by
        rw [hμ₂, Function.update_of_ne (by omega), same₁ _ (by omega)]
        exact hpre.segBC i hi
      segAC := fun i hi => by
        rw [hμ₂, Function.update_of_ne (by omega), same₁ _ (by omega)]
        exact hpre.segAC i hi }
  have hcell : μ₂ fr = x.out := by simp [hμ₂]
  have hzero : ∀ q < x.n * x.n, μ₂ (x.out + q) = 0 := fun q hq => by
    rw [hμ₂, Function.update_of_ne (by omega)]
    have := hfill q (by simpa using hq)
    simpa using this
  have hcall : Meets lim (P₀ ++ R) pCore (d + 1) [x.n, x.U, x.ab, x.bc, x.ac, (fr + 1 : ℕ)] μ₂
      (aeCoreTime Dfun Gfun tD tG Tn x.n x.U) fun _ μ' =>
        Seg μ' x.out (aeFlags x.n x.AB x.BC x.AC) ∧ KeptBut μ₂ μ' fr x.out (x.n * x.n) :=
    Meets.of_body C.hCore (aeCore_spec C x μ₂ fr hpre₂ hcell hzero hcore)
  light_call hcall with r₃ μ₃ ⟨hseg, hkept⟩
  -- return 0
  refine Ends.setTo 0 ⟨hseg, fun c hc => ?_⟩ (by simp; omega) (by simp; omega)
  change μ₃ c = μ c
  rw [hkept c hc, hμ₂, Function.update_of_ne (by omega)]
  exact same₁ c hc.2

/-! ## The program, assembled -/

/-- The procedures of the all-edges host behind those of the host of Theorem 17, which start at
the number `o`: scanPairsAE, aeLoop, aeBrute, aeCore, and the top procedure aeTop, which gets the
number `o + 33`. -/
def aeExtra (pS pD pG o : ℕ) : Program :=
  let ν := et17NumsAt pS pD pG o
  [scanPairsAEBody ν.pScan,                                 -- 29
    aeLoopBody pS ν.pWriteX ν.pWriteY (o + 29),             -- 30
    aeBruteBody ν.pScan,                                    -- 31
    aeCoreBody ν (o + 31) (o + 30),                         -- 32
    aeTopBody (o + 14) (o + 32)]                            -- 33

/-- The procedures of the all-edges host. -/
def aeProcs (pS pD pG o : ℕ) : Program := et17Procs pS pD pG o ++ aeExtra pS pD pG o

theorem length_et17Procs (pS pD pG o : ℕ) : (et17Procs pS pD pG o).length = 29 := rfl

/-- **The context of the top procedure**, in the assembled program with anything appended to it. -/
theorem aeCtx_assembled {P₀ : Program} {pS pD pG : ℕ} {Tn : List ℕ → ℕ} {need : List ℕ → Need}
    {Dfun Gfun tD tG wD wG : ℕ → ℕ} (hsol : SolvesN lopDetectTask P₀ pS Tn need)
    (hD : ∀ R, ParamProc (P₀ ++ R) pD Dfun tD wD) (hG : ∀ R, ParamProc (P₀ ++ R) pG Gfun tG wG)
    (hpos : ∀ n, 1 ≤ n → 1 ≤ Dfun n) (R : Program) :
    AECtx P₀ (aeProcs pS pD pG P₀.length ++ R) (et17NumsAt pS pD pG P₀.length)
      (P₀.length + 31) (P₀.length + 30) (P₀.length + 29) (P₀.length + 32) (P₀.length + 14)
      Tn need Dfun Gfun tD tG wD wG := by
  have hR : aeProcs pS pD pG P₀.length ++ R =
      et17Procs pS pD pG P₀.length ++ (aeExtra pS pD pG P₀.length ++ R) := by
    rw [aeProcs, List.append_assoc]
  have L : ∀ {i : ℕ} {body : Stmt}, (aeExtra pS pD pG P₀.length)[i]? = some body →
      (P₀ ++ (aeProcs pS pD pG P₀.length ++ R))[P₀.length + (29 + i)]? = some body := by
    intro i body h
    rw [aeProcs, List.append_assoc]
    exact getElem?_append_append (B := et17Procs pS pD pG P₀.length ++ aeExtra pS pD pG P₀.length)
      R (by rw [List.getElem?_append_right (by simp [length_et17Procs]), length_et17Procs,
        Nat.add_sub_cancel_left]; exact h)
  have hfill : (P₀ ++ (aeProcs pS pD pG P₀.length ++ R))[P₀.length + 14]? = some fillBody := by
    rw [aeProcs, List.append_assoc]
    exact getElem?_append_append (B := et17Procs pS pD pG P₀.length ++ aeExtra pS pD pG P₀.length)
      R (by rw [List.getElem?_append_left (by simp [length_et17Procs])]; rfl)
  refine ⟨?_, L (i := 0) rfl, L (i := 1) rfl, L (i := 2) rfl, L (i := 3) rfl, hfill⟩
  rw [hR]
  exact et17Ctx_assembled hsol hD hG hpos _

/-- **The all-edges host as a solver of all-edges Exact Triangle**: from a solver of
Lop-AE-SparseTri and two procedures that compute the parameters, in one program `P₀`. -/
theorem ae_solves {P₀ : Program} {pS pD pG : ℕ} {Tn : List ℕ → ℕ} {need : List ℕ → Need}
    {Dfun Gfun tD tG wD wG : ℕ → ℕ} (hsol : SolvesN lopDetectTask P₀ pS Tn need)
    (hD : ∀ R, ParamProc (P₀ ++ R) pD Dfun tD wD) (hG : ∀ R, ParamProc (P₀ ++ R) pG Gfun tG wG)
    (hpos : ∀ n, 1 ≤ n → 1 ≤ Dfun n) :
    Solves aeTask (P₀ ++ aeProcs pS pD pG P₀.length) (P₀.length + 33)
      (aeHostTime Dfun Gfun tD tG Tn) (aeHostNeed Dfun Gfun wD wG need) := by
  refine ⟨aeTopBody (P₀.length + 14) (P₀.length + 32), ?_, fun R lim d x μ fr hpre hok => ?_⟩
  · have := (aeCtx_assembled hsol hD hG hpos []).hCore
    have htop : (P₀ ++ (aeProcs pS pD pG P₀.length ++ []))[P₀.length + 33]? =
        some (aeTopBody (P₀.length + 14) (P₀.length + 32)) := by
      rw [aeProcs, List.append_assoc]
      exact getElem?_append_append
        (B := et17Procs pS pD pG P₀.length ++ aeExtra pS pD pG P₀.length) []
        (by rw [List.getElem?_append_right (by simp [length_et17Procs])]; rfl)
    simpa using htop
  · rw [List.append_assoc]
    exact aeTop_spec (aeCtx_assembled hsol hD hG hpos R) x μ fr hpre hok

end Light.Sec3
