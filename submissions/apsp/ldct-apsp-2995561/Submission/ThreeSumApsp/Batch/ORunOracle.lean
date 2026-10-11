/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Batch.ORunBatch
public import Submission.ThreeSumApsp.Batch.ORunTables
public import Submission.ThreeSumApsp.Batch.ORunParams

/-!
# The batched counting oracle: the run

A batch `j` (`oBatch_ends`), the loop over the batches (`oLoop_ends`), and the whole oracle.
-/

@[expose] public section

namespace Light.Batch

open ThreeSumApsp ThreeSumApsp.Batch Light.Sec4 Light.Filter2 OS

/-- The number of products of the batch `j`. -/
def oKb (n s p j : ℕ) : ℕ := min (oKK s p) (oProd n s - j * oKK s p)

/-- The time of a batch. -/
def tOBatch (n s p : ℕ) : ℕ := tOBTail n s p + 30

theorem setLocal_oLocA_J0 (x : OracleInst) (fr : ℕ) (tmp bn j0 kkb r : ℤ) :
    setLocal (oLocA x fr tmp bn j0 kkb) J0 r = oLocA x fr tmp bn r kkb := rfl

theorem setLocal_oLocA_KKb (x : OracleInst) (fr : ℕ) (tmp bn j0 kkb r : ℤ) :
    setLocal (oLocA x fr tmp bn j0 kkb) KKb r = oLocA x fr tmp bn j0 r := rfl

theorem setLocal_oLocA_Bn (x : OracleInst) (fr : ℕ) (tmp bn j0 kkb r : ℤ) :
    setLocal (oLocA x fr tmp bn j0 kkb) Bn r = oLocA x fr tmp r j0 kkb := rfl

/-- **One batch**: afterwards the counts of its products stand in their cells. -/
theorem oBatch_ends (R : Program) {lim : Limits} {d : ℕ} {x : OracleInst} {μ₀ μ : ℕ → ℤ}
    {fr : ℕ} (hpre : x.Pre μ₀ fr) (hok : (oNeedAt x.n x.U x.s x.p).Ok lim fr d) {j : ℕ}
    (hj : j < oBat x.n x.s x.p) (tmp j0 kkb : ℤ) (hT : BTabs x fr μ) :
    Ends lim (oProg ++ R) d oBatch ⟨frame (oLocA x fr tmp j j0 kkb), μ⟩ (tOBatch x.n x.s x.p)
      fun σ' => ∃ tmp' : ℤ, σ'.loc = frame (oLocA x fr tmp' j (j * oKK x.s x.p : ℕ)
          (oKb x.n x.s x.p j)) ∧
        BTabs x fr σ'.mem ∧
        (∀ e < oKb x.n x.s x.p j * (x.n * x.n), σ'.mem (x.cnt + j * oKK x.s x.p * (x.n * x.n) + e)
          = (cntOf x.n x.s x.p x.AB x.BC x.AC (j * oKK x.s x.p * (x.n * x.n) + e) : ℤ)) ∧
        (∀ b < fr, (b < x.cnt + j * oKK x.s x.p * (x.n * x.n) ∨
          x.cnt + j * oKK x.s x.p * (x.n * x.n) + oKb x.n x.s x.p j * (x.n * x.n) ≤ b) →
            σ'.mem b = μ b) := by
  have h100 : ((100 : ℕ) : ℤ) ≤ lim.word := oWordSum_fits hok
  have hwT : ((oProd x.n x.s + oKK x.s x.p : ℕ) : ℤ) ≤ lim.word := oWordSum_fits hok
  obtain ⟨-, -, -, -, -, hKK1, -⟩ := oParams_facts (n := x.n) hpre.s_pos hpre.p_pos
  have hjT : j * oKK x.s x.p < oProd x.n x.s := (Nat.lt_ceilDiv_iff hKK1).1 hj
  unfold tOBatch
  rw [oBatch_eq]
  light_set ((j * oKK x.s x.p : ℕ) : ℤ) using oLocA, tOBatch
  rw [setLocal_oLocA_J0]
  light_if h1 h2 : j * oKK x.s x.p + oKK x.s x.p ≤ oProd x.n x.s using oLocA, tOBatch
  · light_set ((oKK x.s x.p : ℕ) : ℤ) using oLocA, tOBatch
    rw [setLocal_oLocA_KKb]
    have hkb : oKb x.n x.s x.p j = oKK x.s x.p := by unfold oKb; omega
    rw [hkb]
    refine Ends.pieceLast (oBatchTail_ends R hpre hok (bt := j) hKK1 le_rfl h1 tmp hT)
      (fun _ h => h) ?_
    light_time
  · light_set ((oProd x.n x.s - j * oKK x.s x.p : ℕ) : ℤ) using oLocA, tOBatch
    rw [setLocal_oLocA_KKb]
    have hkb : oKb x.n x.s x.p j = oProd x.n x.s - j * oKK x.s x.p := by unfold oKb; omega
    rw [hkb]
    refine Ends.pieceLast (oBatchTail_ends R hpre hok (bt := j) (kb := oProd x.n x.s - j * oKK x.s x.p)
      (by omega) (by omega) (by omega) tmp hT) (fun _ h => h) ?_
    light_time

/-- What holds after `j` batches: the tables, the counts of the first `min (j KK) T` products, and
the cells below the free pointer outside the counts. -/
def LoopInv (x : OracleInst) (fr : ℕ) (μ₀ : ℕ → ℤ) (j : ℕ) (μ : ℕ → ℤ) : Prop :=
  BTabs x fr μ ∧
    (∀ i < min (j * oKK x.s x.p) (oProd x.n x.s) * (x.n * x.n),
      μ (x.cnt + i) = (cntOf x.n x.s x.p x.AB x.BC x.AC i : ℤ)) ∧
    ∀ b < fr, (b < x.cnt ∨ x.cnt + x.len ≤ b) → μ b = μ₀ b

/-- **The loop over the batches.** -/
theorem oLoop_ends (R : Program) {lim : Limits} {d : ℕ} {x : OracleInst} {μ₀ μ : ℕ → ℤ}
    {fr : ℕ} (hpre : x.Pre μ₀ fr) (hok : (oNeedAt x.n x.U x.s x.p).Ok lim fr d)
    (tmp bn j0 kkb : ℤ) (hT : BTabs x fr μ) (hkeep : Kept μ₀ μ fr) :
    Ends lim (oProg ++ R) d (.for Bn (v Bt) oBatch) ⟨frame (oLocA x fr tmp bn j0 kkb), μ⟩
      (oBat x.n x.s x.p * (tOBatch x.n x.s x.p + 8) + 6) fun σ' =>
        Seg σ'.mem x.cnt (cntList x.n x.s x.p x.AB x.BC x.AC) ∧
          KeptBut μ₀ σ'.mem fr x.cnt x.len := by
  have hwB : ((oBat x.n x.s x.p : ℕ) : ℤ) ≤ lim.word := oWordSum_fits hok
  obtain ⟨-, -, -, -, -, hKK1, -⟩ := oParams_facts (n := x.n) hpre.s_pos hpre.p_pos
  have hlen : x.len = oProd x.n x.s * (x.n * x.n) := rfl
  have hcntB := hpre.belowCnt
  refine Ends.forShape (β := ℤ × ℤ × ℤ)
    (fun j s μ' => ⟨frame (oLocA x fr s.1 j s.2.1 s.2.2), μ'⟩) (LoopInv x fr μ₀)
    (oBat x.n x.s x.p) (tOBatch x.n x.s x.p) (tmp, j0, kkb) ⟨hT, fun i hi => by simp at hi, fun b hb _ => hkeep b hb⟩
    ?round ?done (bound := fun j s μ' _ _ => by light_side [oLocA]) (counter := fun j s μ' => rfl)
  case round =>
    rintro j ⟨tmp, j0, kkb⟩ μ' hj ⟨hT', hcnt, hkp⟩
    refine (oBatch_ends R hpre hok hj tmp j0 kkb hT').mono le_rfl ?_
    rintro ⟨loc', m'⟩ ⟨tmp', hloc, hT'', hc', hk'⟩
    simp only at hloc hT'' hc' hk'
    subst hloc
    have hjT : j * oKK x.s x.p < oProd x.n x.s := (Nat.lt_ceilDiv_iff hKK1).1 hj
    have hkbT : j * oKK x.s x.p + oKb x.n x.s x.p j ≤ oProd x.n x.s := by unfold oKb; omega
    have e1 : min ((j + 1) * oKK x.s x.p) (oProd x.n x.s) = j * oKK x.s x.p + oKb x.n x.s x.p j := by
      rw [Nat.add_mul, Nat.one_mul]; unfold oKb; omega
    have e2 : min (j * oKK x.s x.p) (oProd x.n x.s) = j * oKK x.s x.p := by omega
    have e3 : (j * oKK x.s x.p + oKb x.n x.s x.p j) * (x.n * x.n)
        = j * oKK x.s x.p * (x.n * x.n) + oKb x.n x.s x.p j * (x.n * x.n) := by ring
    have e4 : (j * oKK x.s x.p + oKb x.n x.s x.p j) * (x.n * x.n) ≤ oProd x.n x.s * (x.n * x.n) :=
      Nat.mul_le_mul_right _ hkbT
    rw [e2] at hcnt
    refine ⟨(tmp', _, _), m', rfl, hT'', fun i hi => ?_, fun b hb hor => ?_⟩
    · rw [e1, e3] at hi
      by_cases hil : i < j * oKK x.s x.p * (x.n * x.n)
      · rw [hk' (x.cnt + i) (by omega) (Or.inl (by omega))]
        exact hcnt i hil
      · have := hc' (i - j * oKK x.s x.p * (x.n * x.n)) (by omega)
        rwa [show x.cnt + j * oKK x.s x.p * (x.n * x.n) + (i - j * oKK x.s x.p * (x.n * x.n))
          = x.cnt + i by omega, show j * oKK x.s x.p * (x.n * x.n) + (i - j * oKK x.s x.p *
            (x.n * x.n)) = i by omega] at this
    · rw [hk' b hb (by omega)]
      exact hkp b hb hor
  case done =>
    rintro ⟨tmp, j0, kkb⟩ μ' ⟨-, hcnt, hkp⟩
    have hTB : oProd x.n x.s ≤ oBat x.n x.s x.p * oKK x.s x.p := le_ceilDiv_mul _ _ hKK1
    have e : min (oBat x.n x.s x.p * oKK x.s x.p) (oProd x.n x.s) = oProd x.n x.s := by omega
    rw [e] at hcnt
    refine ⟨fun i hi => ?_, fun b ⟨hb, hout⟩ => hkp b hb hout⟩
    simp only [cntList, List.length_map, List.length_range] at hi
    simp only [cntList, List.getElem_map, List.getElem_range]
    exact hcnt i hi

/-- **The addresses.** -/
theorem oAddrs_ends (R : Program) {lim : Limits} {d : ℕ} {x : OracleInst} {μ₀ μ : ℕ → ℤ}
    {fr : ℕ} (hpre : x.Pre μ₀ fr) (hok : (oNeedAt x.n x.U x.s x.p).Ok lim fr d) :
    Ends lim (oProg ++ R) d oAddrs ⟨frame (oLocP x fr), μ⟩ 200 fun σ' =>
      σ'.loc = frame (oLocA x fr 0 0 0 0) ∧ σ'.mem = μ := by
  have h100 : ((100 : ℕ) : ℤ) ≤ lim.word := oWordSum_fits hok
  have std : Std lim := ⟨hok.space, by exact_mod_cast h100⟩
  have hsw := std.space_le
  have hcells := hok.cells
  simp only [oNeedAt, oCells] at hcells
  have hB0 := oB0_eq x.n x.s x.p fr
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12⟩ := oAddrs_eq x.n x.s x.p fr
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hSz⟩ :=
    oParams_facts (n := x.n) hpre.s_pos hpre.p_pos
  have hkk : oDig x.p * oDig x.p ≤ 3 * x.p := oDig_sq_le hpre.p_pos
  have hwn : ((x.n * x.n : ℕ) : ℤ) ≤ lim.word := oWordSum_fits hok
  have hwk : ((oDig x.p * oDig x.p : ℕ) : ℤ) ≤ lim.word := oWordSum_fits hok
  have hwS : ((oSz x.n x.s x.p : ℕ) : ℤ) ≤ lim.word := oWordSum_fits hok
  have hRS : oKK x.s x.p * oNP x.n x.s x.p ≤ oSz x.n x.s x.p := by
    rw [hSz]; exact Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (by norm_num))
  have hwR : ((oKK x.s x.p * oNP x.n x.s x.p : ℕ) : ℤ) ≤ lim.word := by
    have : ((oKK x.s x.p * oNP x.n x.s x.p : ℕ) : ℤ) ≤ ((oSz x.n x.s x.p : ℕ) : ℤ) := by
      exact_mod_cast hRS
    omega
  have hTop := base_le_top (oPar x.n x.s x.p) (oT x.s x.p) 0
  unfold oAddrs
  light_set (fr : ℤ) using oLocP
  light_set ((oaRNBC x.n fr : ℕ) : ℤ) using oLocP, e1
  light_set ((oaRNAB x.n fr : ℕ) : ℤ) using oLocP, e1, e2
  light_set ((oaNL x.n fr : ℕ) : ℤ) using oLocP, e1, e2, e3
  light_set ((oaHK x.n x.p fr : ℕ) : ℤ) using oLocP, e1, e2, e3, e4
  light_set ((oaRS x.n x.p fr : ℕ) : ℤ) using oLocP, e1, e2, e3, e4, e5
  light_set ((oaRV x.n x.s x.p fr : ℕ) : ℤ) using oLocP, e1, e2, e3, e4, e5, e6
  light_set ((oaDK x.n x.s x.p fr : ℕ) : ℤ) using oLocP, e1, e2, e3, e4, e5, e6, e7
  light_set ((oaZH x.n x.s x.p fr : ℕ) : ℤ) using oLocP, e1, e2, e3, e4, e5, e6, e7, e8
  light_set ((oaZL x.n x.s x.p fr : ℕ) : ℤ) using oLocP, e1, e2, e3, e4, e5, e6, e7, e8, e9
  light_set ((oKK x.s x.p * oNP x.n x.s x.p : ℕ) : ℤ) using oLocP
  have hSzI : ((oKK x.s x.p : ℕ) : ℤ) * (oNP x.n x.s x.p : ℕ) * (oD x.s x.p : ℕ)
      = ((oSz x.n x.s x.p : ℕ) : ℤ) := by rw [hSz]; push_cast; ring
  light_set ((oSz x.n x.s x.p : ℕ) : ℤ) using oLocP
  light_set ((oaX x.n x.s x.p fr : ℕ) : ℤ) using oLocP, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10
  light_set ((oaY x.n x.s x.p fr : ℕ) : ℤ) using oLocP, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10,
    e11
  light_set ((oB0 x.n x.s x.p fr : ℕ) : ℤ) using oLocP, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10,
    e11, e12
  exact ⟨rfl, rfl⟩

/-- The tables that oTables writes are those that a batch reads. -/
theorem BTabs.of_OTabs {x : OracleInst} {fr : ℕ} {μ : ℕ → ℤ} (h : OTabs x fr μ) : BTabs x fr μ := by
  have enl : (fun h : ℕ => resid x.p ((h : ℤ) * (-1) + (x.p : ℤ)))
      = fun h : ℕ => resid x.p ((x.p : ℤ) - h) := by
    funext h; congr 1; ring
  have ehk : (fun h : ℕ => resid x.p ((h : ℤ) * (oDig x.p : ℤ) + 0))
      = fun h : ℕ => resid x.p ((h * oDig x.p : ℕ) : ℤ) := by
    funext h; congr 1
  have hnl := h.nl
  have hhk := h.hk
  rw [enl] at hnl
  rw [ehk] at hhk
  exact ⟨h.rac, h.rnbc, hnl, hhk, h.rs, h.rv, h.zh, h.zl⟩

/-- The time of the oracle. -/
def tOracle (n U s p : ℕ) : ℕ :=
  tOParams n s p + tOTables n U s p + oBat n s p * (tOBatch n s p + 8) + 300

/-- **The run of the oracle.** -/
theorem oracle_ends (R : Program) {lim : Limits} {d : ℕ} {x : OracleInst} {μ : ℕ → ℤ} {fr : ℕ}
    (hpre : x.Pre μ fr) (hok : (oNeedAt x.n x.U x.s x.p).Ok lim fr d) :
    Ends lim (oProg ++ R) d oracleBody ⟨frame (oracleTask.args x ++ [(fr : ℤ)]), μ⟩
      (tOracle x.n x.U x.s x.p) fun σ' => oracleTask.Post x μ fr (σ'.loc 0) σ'.mem := by
  unfold oracleBody tOracle
  light_piece (oParams_ends' R hpre hok) with ⟨loc₁, μ₁⟩ ⟨hloc₁, hso₁⟩
  simp only at hloc₁ hso₁
  subst hloc₁
  have hk₁ : Kept μ μ₁ fr := fun b hb => hso₁ b (Or.inl hb)
  have hpre₁ : x.Pre μ₁ fr := { hpre with toPre := hpre.toPre.keep hk₁ }
  light_piece (oAddrs_ends R hpre hok (μ := μ₁)) with ⟨loc₂, μ₂⟩ ⟨hloc₂, hm₂⟩
  simp only at hloc₂ hm₂
  subst hloc₂ hm₂
  light_piece (oTables_ends R hpre₁ hok 0 0 0 0) with ⟨loc₃, μ₃⟩ ⟨tmp, hloc₃, hOT, hk₃⟩
  simp only at hloc₃ hOT hk₃
  subst hloc₃
  refine Ends.pieceLast (oLoop_ends R hpre hok tmp 0 0 0 (BTabs.of_OTabs hOT)
    (fun b hb => (hk₃ b hb).trans (hk₁ b hb))) (fun σ' h => h) ?_
  light_time

end Light.Batch
