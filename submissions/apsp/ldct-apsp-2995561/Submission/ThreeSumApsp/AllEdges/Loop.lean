/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.AllEdges.Data
public import Submission.ThreeSumApsp.Programs.Sec3.Theorem17.Host.Loop

/-!
# All-edges host: the loop over the instances

The loop of the host of Theorem 17, with `scanPairsAE` in the place of `scanPairs`: the marks of the
`n²` pairs lie in `n²` cells from `fl`, below the matrices of the instances.  The loop writes, for
every pair, whether a zero triangle through it has been found (`aeLoop_spec`).

The memory before instance `t` agrees below `x` with the first memory, with the marks `marks t` in
the cells from `fl`; so the facts `HostSetting` of the loop of Theorem 17 hold with that memory as
the first one, and the lemmas about the calls of writeX, writeY and the solver are used unchanged.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {d : ℕ}

/-! ## The procedure -/

namespace AELocal

/-- The address of the marks; the arguments before it are those of hostLoop. -/
abbrev Fl : ℕ := 20
/-- The number t of the instance. -/
abbrev Inst : ℕ := 21
/-- The number ch of its chunk. -/
abbrev ChunkNo : ℕ := 22
/-- The first vertex c0 of its piece. -/
abbrev PieceStart : ℕ := 23

end AELocal

open HostLocal AELocal

/-- The four calls for one instance: the two matrices, the solver, the scans. -/
def aeCalls (pS pWriteX pWriteY pScanPairs : ℕ) : Stmt :=
  .call pWriteX [v MatX, v ResAC, v Size, v ParD, v ThePrime, v AELocal.PieceStart, v Len,
    v Residue] Unused ;;
  .call pWriteY [v MatY, v ResBC, v Size, v ParD, v ThePrime, v AELocal.PieceStart, v Len] Unused ;;
  .call pS [v Size, v ParD, v NumPairs, k 1, v MatX, v MatY, v Rows +' v Start, v Cols +' v Start,
    v AdrOut, v SolverFree] Unused ;;
  .call pScanPairs [v AdrOut, v Rows +' v Start, v Cols +' v Start, v NumPairs, v Fl, v AdrAB,
    v AdrBC, v AdrAC, v Size, v AELocal.PieceStart, v Len] Unused

/-- The numbers of the next instance, of its chunk, and the first vertex of its piece. -/
def aeNext : Stmt :=
  .set AELocal.ChunkNo (v AELocal.ChunkNo +' k 1) ;;
  .ite (v AELocal.ChunkNo =' v NumChunks)
    (.set AELocal.ChunkNo (k 0) ;; .set AELocal.PieceStart (v AELocal.PieceStart +' v PieceLen))
    .skip ;;
  .set AELocal.Inst (v AELocal.Inst +' k 1)

/-- The parameters of the instance. -/
def aeParams : Stmt :=
  .set Len (v PieceLen) ;;
  .ite (v Size -' v AELocal.PieceStart <' v PieceLen) (.set Len (v Size -' v AELocal.PieceStart))
    .skip ;;
  .set Residue (M (v TabR +' v AELocal.ChunkNo)) ;;
  .set Start (M (v TabL +' v AELocal.ChunkNo)) ;;
  .set NumPairs (M (v TabW +' v AELocal.ChunkNo))

/-- One round of aeLoop. -/
def aeRound (pS pWriteX pWriteY pScanPairs : ℕ) : Stmt :=
  aeParams ;;
  aeCalls pS pWriteX pWriteY pScanPairs ;;
  aeNext

/-- aeLoop(n, D, p, q, chunkCount, m, ab, bc, ac, rac, rbc, qi, qj, cr, cl, cw, x, y, out, fr, fl).
-/
def aeLoopBody (pS pWriteX pWriteY pScanPairs : ℕ) : Stmt :=
  .set AELocal.Inst (k 0) ;; .set AELocal.ChunkNo (k 0) ;; .set AELocal.PieceStart (k 0) ;;
  .while (v AELocal.Inst <' v NumInst) (aeRound pS pWriteX pWriteY pScanPairs) ;;
  .set 0 (k 0)

/-- The number of steps of aeLoop, if the solver takes Tn. -/
def tAELoop (Tn : List ℕ → ℕ) (X : HostData) : ℕ :=
  (∑ t ∈ Finset.range X.m, (tWrites X.n X.D (X.len t) + Tn [X.n, X.D, X.w t] +
    tScanPairsAE (X.w t) (X.len t) (X.aeExecs t))) + 14

/-! ## What the loop relies on -/

/-- The marks lie below x, apart from everything that the loop reads. -/
structure AEMarksLay (X : HostData) (A : HostAddr) (fl : ℕ) : Prop where
  below : fl + X.n * X.n ≤ A.x
  ab : Apart A.ab (X.n * X.n) fl (X.n * X.n)
  bc : Apart A.bc (X.n * X.n) fl (X.n * X.n)
  ac : Apart A.ac (X.n * X.n) fl (X.n * X.n)
  rac : Apart A.rac (X.n * X.n) fl (X.n * X.n)
  rbc : Apart A.rbc (X.n * X.n) fl (X.n * X.n)
  qi : Apart A.qi (X.n * X.n) fl (X.n * X.n)
  qj : Apart A.qj (X.n * X.n) fl (X.n * X.n)
  cr : Apart A.cr X.chunkCount fl (X.n * X.n)
  cl : Apart A.cl X.chunkCount fl (X.n * X.n)
  cw : Apart A.cw X.chunkCount fl (X.n * X.n)

/-- The context of aeLoop: a solver of Lop-AE-SparseTri, and the procedures writeX, writeY,
scanPairsAE, scan in the program. -/
structure AEHostCtx (P₀ R : Program) (pS pWriteX pWriteY pScanPairs pScan : ℕ) (Tn : List ℕ → ℕ)
    (need : List ℕ → Need) : Prop where
  sol : SolvesN lopDetectTask P₀ pS Tn need
  writeX : (P₀ ++ R)[pWriteX]? = some writeXBody
  writeY : (P₀ ++ R)[pWriteY]? = some writeYBody
  scanPairs : (P₀ ++ R)[pScanPairs]? = some (scanPairsAEBody pScan)
  scan : (P₀ ++ R)[pScan]? = some scanBody

/-- The context of hostLoop, for the lemmas on the first three calls. -/
def AEHostCtx.toHost {P₀ R : Program} {pS pWriteX pWriteY pScanPairs pScan : ℕ} {Tn : List ℕ → ℕ}
    {need : List ℕ → Need} (C : AEHostCtx P₀ R pS pWriteX pWriteY pScanPairs pScan Tn need)
    (p : ℕ) (hp : (P₀ ++ R)[p]? = some (scanPairsBody pScan)) :
    HostCtx P₀ R pS pWriteX pWriteY p pScan Tn need :=
  ⟨C.sol, C.writeX, C.writeY, hp, C.scan⟩

/-- The arguments of aeLoop. -/
def aeLoopArgs (X : HostData) (A : HostAddr) (fl : ℕ) : List ℤ :=
  [X.n, X.D, X.p, X.q, X.chunkCount, X.m, A.ab, A.bc, A.ac, A.rac, A.rbc, A.qi, A.qj, A.cr, A.cl,
    A.cw, A.x, A.y, A.out, A.fr, fl]

/-! ## Marks in the memory -/

/-- A memory that holds the marks already. -/
theorem withMarks_self {μ : ℕ → ℤ} {fl N : ℕ} {g : ℕ → Bool}
    (h : ∀ q < N, μ (fl + q) = bit (g q)) : withMarks μ fl N g = μ := by
  funext a
  unfold withMarks
  split_ifs with ha
  · have := h (a - fl) (by omega)
    rw [Nat.add_sub_cancel' ha.1] at this
    exact this.symm
  · rfl

/-- What the loop reads stands in a memory with other marks as it stood before. -/
theorem HostMem.withMarks {X : HostData} {A : HostAddr} {fl : ℕ} {μ : ℕ → ℤ}
    (h : HostMem X A μ) (L : AEMarksLay X A fl) (hv : X.Valid) (g' : ℕ → Bool) :
    HostMem X A (Light.Sec3.withMarks μ fl (X.n * X.n) g') := by
  have lenAB := hv.lenAB
  have lenBC := hv.lenBC
  have lenAC := hv.lenAC
  have lenRAC : X.RAC.length = X.n * X.n := by simp [HostData.RAC, residList, hv.lenAC]
  have lenRBC : X.RBC.length = X.n * X.n := by simp [HostData.RBC, residList, hv.lenBC]
  have lenQI := hv.length_QI
  have lenQJ := hv.length_QJ
  have lenCT : X.CT.length = X.chunkCount := rfl
  have hout : SameOn (Outside fl (X.n * X.n)) μ (Light.Sec3.withMarks μ fl (X.n * X.n) g') :=
    fun a ha => withMarks_out _ ha
  have lenCR : (X.CT.map fun c => c.residue).length = X.chunkCount := by simp [lenCT]
  have lenCL : (X.CT.map fun c => c.start).length = X.chunkCount := by simp [lenCT]
  have lenCW : (X.CT.map fun c => c.len).length = X.chunkCount := by simp [lenCT]
  exact
    { segAB := h.segAB.keep (SameOn.mono hout fun a ha => by have := L.ab; simp only [Inside] at ha; omega)
      segBC := h.segBC.keep (SameOn.mono hout fun a ha => by have := L.bc; simp only [Inside] at ha; omega)
      segAC := h.segAC.keep (SameOn.mono hout fun a ha => by have := L.ac; simp only [Inside] at ha; omega)
      segRAC := h.segRAC.keep (SameOn.mono hout fun a ha => by have := L.rac; simp only [Inside] at ha; omega)
      segRBC := h.segRBC.keep (SameOn.mono hout fun a ha => by have := L.rbc; simp only [Inside] at ha; omega)
      segQI := h.segQI.keep (SameOn.mono hout fun a ha => by have := L.qi; simp only [Inside] at ha; omega)
      segQJ := h.segQJ.keep (SameOn.mono hout fun a ha => by have := L.qj; simp only [Inside] at ha; omega)
      segCR := h.segCR.keep (SameOn.mono hout fun a ha => by
        have := L.cr
        simp only [Inside, lenCR] at ha; omega)
      segCL := h.segCL.keep (SameOn.mono hout fun a ha => by
        have := L.cl
        simp only [Inside, lenCL] at ha; omega)
      segCW := h.segCW.keep (SameOn.mono hout fun a ha => by
        have := L.cw
        simp only [Inside, lenCW] at ha; omega) }

/-! ## The parts of a round -/

variable {P₀ R : Program} {pS pWriteX pWriteY pScanPairs pScan : ℕ} {Tn : List ℕ → ℕ}
  {need : List ℕ → Need} {X : HostData} {U : ℕ} {A : HostAddr} {fl : ℕ} {μ μ' : ℕ → ℤ} {t : ℕ}

/-- The state of aeLoop: the arguments, the numbers t, ch and c0 of the instance, and what the
locals Len, Residue, Start, NumPairs and Unused hold. -/
abbrev aeState (X : HostData) (A : HostAddr) (fl t ch c0 : ℕ) (len rho lo w res : ℤ)
    (μ' : ℕ → ℤ) : State :=
  ⟨frame [X.n, X.D, X.p, X.q, X.chunkCount, X.m, A.ab, A.bc, A.ac, A.rac, A.rbc, A.qi, A.qj, A.cr,
    A.cl, A.cw, A.x, A.y, A.out, A.fr, fl, t, ch, c0, len, rho, lo, w, res], μ'⟩

/-- The memory before instance `t`, below `x`: the first memory with the marks of `t`. -/
abbrev aeBase (X : HostData) (fl : ℕ) (μ : ℕ → ℤ) (t : ℕ) : ℕ → ℤ :=
  withMarks μ fl (X.n * X.n) (X.marks t)

/-- **The parameters of instance t.** -/
theorem aeParams_spec {P : Program} {B : ℕ → ℤ} (S : HostSetting lim d X U A need B μ')
    (ht : t < X.m) (len rho lo w res : ℤ) :
    Ends lim P d aeParams (aeState X A fl t (t % X.chunkCount) (X.c0 t) len rho lo w res μ') 27
      (· = aeState X A fl t (t % X.chunkCount) (X.c0 t) (X.len t) (X.rho t) (X.lo t) (X.w t) res
        μ') := by
  have hplaces := S.places ht
  obtain ⟨hrho, hlo, hw⟩ := S.read_chunk ht
  have hlen : X.len t = min X.q (X.n - X.c0 t) := rfl
  generalize t % X.chunkCount = ch at *
  have htail : ∀ len' : ℤ, len' = X.len t → Ends lim P d
      (.set Residue (M (v TabR +' v AELocal.ChunkNo)) ;; .set Start (M (v TabL +' v AELocal.ChunkNo)) ;;
        .set NumPairs (M (v TabW +' v AELocal.ChunkNo)))
      (aeState X A fl t ch (X.c0 t) len' rho lo w res μ') 15
      (· = aeState X A fl t ch (X.c0 t) (X.len t) (X.rho t) (X.lo t) (X.w t) res μ') := by
    rintro _ rfl
    refine Ends.setToThen (X.rho t : ℤ) ?_ (by light_side [hrho])
    refine Ends.setToThen (X.lo t : ℤ) ?_ (by light_side [hlo])
    exact Ends.setTo (X.w t : ℤ) rfl (by light_side [hw])
  unfold aeParams
  -- len := q
  light_set X.q
  -- if n - c0 < q then len := n - c0
  refine Ends.iteThen (fun hc => ?_) (fun hc => ?_)
  · replace hc : (X.n : ℤ) - X.c0 t < X.q := by simpa using hc
    exact Ends.setToThen (X.len t : ℤ) ((htail _ rfl).mono (by light_time) fun _ h => h)
  · replace hc : ¬ (X.n : ℤ) - X.c0 t < X.q := by simpa using hc
    refine Ends.next 0 (Ends.skip ?_)
    exact (htail _ (by omega)).mono (by light_time) fun _ h => h

/-- The time of the four calls. -/
def tAECalls (Tn : List ℕ → ℕ) (X : HostData) (t : ℕ) : ℕ :=
  tWriteX X.n X.D (X.len t) + tWriteY X.n X.D (X.len t) + Tn [X.n, X.D, X.w t] +
    tScanPairsAE (X.w t) (X.len t) (X.aeExecs t) + 52

/-- The marks lie apart from what scanPairsAE reads for instance t. -/
theorem AEMarksLay.marksApart {B : ℕ → ℤ} (L : AEMarksLay X A fl) (S : HostSetting lim d X U A need B μ')
    (ht : t < X.m) :
    MarksApart lim fl A.out (A.qi + X.lo t) (A.qj + X.lo t) (X.w t) A.ab A.bc A.ac X.n := by
  have hplaces := S.places ht
  have hb := L.below
  exact
    { out := by omega
      qa := by have := L.qi; omega
      qb := by have := L.qj; omega
      ab := L.ab
      bc := L.bc
      ac := L.ac
      space := by omega }

/-- **The four calls for instance t.** -/
theorem aeCalls_spec (C : AEHostCtx P₀ R pS pWriteX pWriteY pScanPairs pScan Tn need)
    (hmem : HostMem X A μ) (L : AEMarksLay X A fl)
    (S : HostSetting lim d X U A need (aeBase X fl μ t) μ') (ht : t < X.m) (ch : ℕ) (res : ℤ) :
    Ends lim (P₀ ++ R) d (aeCalls pS pWriteX pWriteY pScanPairs)
      (aeState X A fl t ch (X.c0 t) (X.len t) (X.rho t) (X.lo t) (X.w t) res μ')
      (tAECalls Tn X t) fun σ => ∃ (res' : ℤ) (μ'' : ℕ → ℤ),
        σ = aeState X A fl t ch (X.c0 t) (X.len t) (X.rho t) (X.lo t) (X.w t) res' μ'' ∧
          HostSetting lim d X U A need (aeBase X fl μ (t + 1)) μ'' := by
  have hplaces := S.places ht
  have hb := L.below
  unfold aeCalls tAECalls
  -- res := writeX(x, rac, n, D, p, c0, len, rho)
  have hWX : Meets lim (P₀ ++ R) pWriteX (d + 1)
      [(A.x : ℤ), A.rac, X.n, X.D, X.p, X.c0 t, X.len t, X.rho t] μ' (tWriteX X.n X.D (X.len t))
      fun _ μ₁ => Seg μ₁ A.x (X.matX t) ∧ SameOutside μ' μ₁ A.x (X.n * X.D) :=
    Meets.of_body C.writeX (writeX_spec (S.writeX ht) (S.ok.valid.rho_lt ht))
  light_call hWX with r₁ μ₁ ⟨hX, hrest₁⟩
  have S₁ := S.next fun a ha => hrest₁ a (Or.inl ha)
  -- res := writeY(y, rbc, n, D, p, c0, len)
  have hWY : Meets lim (P₀ ++ R) pWriteY (d + 1) [(A.y : ℤ), A.rbc, X.n, X.D, X.p, X.c0 t, X.len t]
      μ₁ (tWriteY X.n X.D (X.len t))
      fun _ μ₂ => Seg μ₂ A.y (X.matY t) ∧ SameOutside μ₁ μ₂ A.y (X.D * X.n) :=
    Meets.of_body C.writeY (writeY_spec (S₁.writeY ht))
  light_call hWY with r₂ μ₂ ⟨hY, hrest₂⟩
  have S₂ := S₁.next fun a ha => hrest₂ a (Or.inl (by omega))
  replace hX : Seg μ₂ A.x (X.matX t) :=
    hX.keep (by light_keep [X.length_matX t])
  -- res := solver(n, D, w, 1, x, y, qi + lo, qj + lo, out, fr)
  have hSol : Meets lim (P₀ ++ R) pS (d + 1)
      [(X.n : ℤ), X.D, X.w t, (1 : ℕ), A.x, A.y, (A.qi + X.lo t : ℕ), (A.qj + X.lo t : ℕ), A.out,
        A.fr] μ₂ (Tn [X.n, X.D, X.w t])
      fun _ μ₃ => Seg μ₃ A.out (X.ans t) ∧ KeptBut μ₂ μ₃ A.fr A.out (X.w t) :=
    C.sol.meets R (HostSetting.inst X A t) (S₂.solver ht hX hY) (S₂.fits.solver t ht)
  light_call hSol with r₃ μ₃ ⟨hans, hkept₃⟩
  have S₃ := S₂.next fun a ha => hkept₃ a (by omega)
  -- res := scanPairsAE(out, qi + lo, qj + lo, w, fl, ab, bc, ac, n, c0, len)
  have hself : withMarks μ₃ fl (X.n * X.n) (X.marks t) = μ₃ := withMarks_self fun q hq => by
    rw [S₃.kept (fl + q) (by omega)]
    exact withMarks_in _ hq
  have hcall := scanPairsAE_spec (d := d + 1) (g := X.marks t) C.scan (S₃.weights ht) (S₃.answers ht hans)
    (L.marksApart S₃ ht) (by omega) (S₃.ok.valid.piece_le ht)
  rw [hself] at hcall
  have hSP : Meets lim (P₀ ++ R) pScanPairs (d + 1)
      [(A.out : ℤ), (A.qi + X.lo t : ℕ), (A.qj + X.lo t : ℕ), X.w t, fl, A.ab, A.bc, A.ac, X.n,
        X.c0 t, X.len t] μ₃ (tScanPairsAE (X.w t) (X.len t) (X.aeExecs t))
      fun _ μ₄ => μ₄ = withMarks μ₃ fl (X.n * X.n) (X.marks (t + 1)) :=
    Meets.of_body C.scanPairs hcall
  light_call hSP with _ μ₄ hμ₄
  refine ⟨_, μ₄, rfl, ?_⟩
  refine { S₃ with mem := HostMem.withMarks hmem L S.ok.valid _, kept := fun a ha => ?_ }
  rw [hμ₄]
  change withMarks μ₃ fl (X.n * X.n) (X.marks (t + 1)) a = withMarks μ fl (X.n * X.n) (X.marks (t + 1)) a
  unfold withMarks
  split_ifs with hin
  · rfl
  · rw [S₃.kept a ha]
    exact withMarks_out _ (by omega)

/-- **The counters**: from instance t to instance t + 1. -/
theorem aeNext_spec {P : Program} {B : ℕ → ℤ} (S : HostSetting lim d X U A need B μ')
    (ht : t < X.m) (len rho lo w res : ℤ) :
    Ends lim P d aeNext (aeState X A fl t (t % X.chunkCount) (X.c0 t) len rho lo w res μ') 18
      (· = aeState X A fl (t + 1) ((t + 1) % X.chunkCount) (X.c0 (t + 1)) len rho lo w res
        μ') := by
  have hplaces := S.places ht
  have hlast := Nat.succ_div_mod_of_eq (n := X.chunkCount) (i := t)
  have hinner := Nat.succ_div_mod_of_ne (n := X.chunkCount) (i := t) (by omega)
  have hc0 : X.c0 t = t / X.chunkCount * X.q := rfl
  have hc0' : X.c0 (t + 1) = (t + 1) / X.chunkCount * X.q := rfl
  generalize t % X.chunkCount = ch at *
  generalize (t + 1) % X.chunkCount = ch' at *
  -- t := t + 1
  have htail : Ends lim P d (.set AELocal.Inst (v AELocal.Inst +' k 1))
      (aeState X A fl t ch' (X.c0 (t + 1)) len rho lo w res μ') 4
      (· = aeState X A fl (t + 1) ch' (X.c0 (t + 1)) len rho lo w res μ') :=
    Ends.setTo (t + 1 : ℕ) rfl
  unfold aeNext
  -- ch := ch + 1
  light_set (ch + 1 : ℕ)
  -- if ch = chunkCount
  refine Ends.iteThen (fun hc => ?_) (fun hc => ?_)
  · replace hc : ch + 1 = X.chunkCount := by
      have : ((ch + 1 : ℕ) : ℤ) = X.chunkCount := by simpa using hc
      exact_mod_cast this
    obtain ⟨hdiv, rfl⟩ := hlast hc
    have hstep : X.c0 (t + 1) = X.c0 t + X.q := by rw [hc0', hc0, hdiv, Nat.succ_mul]
    -- ch := 0; c0 := c0 + q
    have hwrap : Ends lim P d
        (.set AELocal.ChunkNo (k 0) ;; .set AELocal.PieceStart (v AELocal.PieceStart +' v PieceLen))
        (aeState X A fl t (ch + 1) (X.c0 t) len rho lo w res μ') 6
        (· = aeState X A fl t 0 (X.c0 (t + 1)) len rho lo w res μ') :=
      Ends.setToThen ((0 : ℕ) : ℤ)
        (Ends.setTo (X.c0 (t + 1) : ℕ) rfl (by light_side [hstep]))
    refine Ends.next _ (hwrap.mono le_rfl ?_)
    rintro _ rfl
    exact htail.mono (by light_time) fun _ h => h
  · replace hc : ch + 1 ≠ X.chunkCount := fun h => hc (by simp; exact_mod_cast h)
    obtain ⟨hdiv, rfl⟩ := hinner hc
    have hstep : X.c0 (t + 1) = X.c0 t := by rw [hc0', hc0, hdiv]
    -- skip
    refine Ends.next 0 (Ends.skip ?_)
    rw [← hstep]
    exact htail.mono (by light_time) fun _ h => h

/-! ## The loop -/

/-- The invariant of the loop, before instance t. -/
def AEInv (lim : Limits) (d : ℕ) (X : HostData) (U : ℕ) (A : HostAddr) (fl : ℕ)
    (need : List ℕ → Need) (μ : ℕ → ℤ) (t : ℕ) (σ : State) : Prop :=
  ∃ (len rho lo w res : ℤ) (μ' : ℕ → ℤ),
    σ = aeState X A fl t (t % X.chunkCount) (X.c0 t) len rho lo w res μ' ∧
    HostSetting lim d X U A need (aeBase X fl μ t) μ'

/-- **One round of the loop.** -/
theorem aeRound_spec (C : AEHostCtx P₀ R pS pWriteX pWriteY pScanPairs pScan Tn need)
    (hmem : HostMem X A μ) (L : AEMarksLay X A fl)
    (ht : t < X.m) {σ : State} (hσ : AEInv lim d X U A fl need μ t σ) :
    Ends lim (P₀ ++ R) d (aeRound pS pWriteX pWriteY pScanPairs) σ (tAECalls Tn X t + 45)
      (AEInv lim d X U A fl need μ (t + 1)) := by
  obtain ⟨len, rho, lo, w, res, μ', rfl, S⟩ := hσ
  unfold aeRound
  -- the parameters of the instance
  light_piece (aeParams_spec S ht len rho lo w res) with _ rfl
  -- the four calls
  light_piece (aeCalls_spec C hmem L S ht _ res) with _ ⟨res', μ'', rfl, S'⟩
  -- the counters
  light_piece (aeNext_spec S' ht _ _ _ _ res') with _ rfl
  exact ⟨_, _, _, _, _, μ'', rfl, S'⟩

/-- **aeLoop** writes the marks of all pairs: below x the final memory is the first one with the
marks after all instances.  The marks start at 0. -/
theorem aeLoop_spec (C : AEHostCtx P₀ R pS pWriteX pWriteY pScanPairs pScan Tn need)
    (hok : HostOk X U) (hmem : HostMem X A μ) (hlay : HostLay X A)
    (hlim : HostLim lim d X U A need) (L : AEMarksLay X A fl)
    (hzero : ∀ q < X.n * X.n, μ (fl + q) = 0) :
    Ends lim (P₀ ++ R) d (aeLoopBody pS pWriteX pWriteY pScanPairs)
      ⟨frame (aeLoopArgs X A fl), μ⟩ (tAELoop Tn X) fun σ' =>
      Kept (aeBase X fl μ X.m) σ'.mem A.x := by
  have hw := hlim.space
  have hT : ∑ t ∈ Finset.range X.m, (4 + (tAECalls Tn X t + 45))
      ≤ ∑ t ∈ Finset.range X.m, (tWrites X.n X.D (X.len t) + Tn [X.n, X.D, X.w t] +
        tScanPairsAE (X.w t) (X.len t) (X.aeExecs t)) :=
    Finset.sum_le_sum fun t _ => by simp [tAECalls, tWrites]; omega
  have hbase : aeBase X fl μ 0 = μ := withMarks_self fun q hq => by
    rw [hzero q hq]
    rfl
  unfold aeLoopBody tAELoop aeLoopArgs
  -- t := 0; ch := 0; c0 := 0
  light_set (0 : ℕ)
  light_set (0 : ℕ)
  light_set (0 : ℕ)
  -- while t < m
  refine Ends.next _ (Ends.while (AEInv lim d X U A fl need μ) X.m (fun t => tAECalls Tn X t + 45)
    ?start ?round ?done) (by simp only [Cond.cost, Expr.cost, Nat.reduceAdd]; omega)
  case start =>
    refine ⟨0, 0, 0, 0, 0, μ, ?_, ⟨hok, by rw [hbase]; exact hmem, hlay, hlim, fun a _ => by rw [hbase]⟩⟩
    rw [aeState, ← frame_append_zeros _ 5]
    simp [HostData.c0]
  case round =>
    intro t σ ht hσ
    obtain ⟨len, rho, lo, w, res, μ', rfl, -⟩ := id hσ
    exact ⟨⟨trivial, trivial⟩, by simpa using ht, aeRound_spec C hmem L ht hσ⟩
  case done =>
    rintro _ ⟨len, rho, lo, w, res, μ', rfl, S⟩
    exact ⟨⟨trivial, trivial⟩, by simp, Ends.setTo 0 S.kept
      (by simp; omega) (hT := by simp only [Cond.cost, Expr.cost, Nat.reduceAdd]; omega)⟩

end Light.Sec3
