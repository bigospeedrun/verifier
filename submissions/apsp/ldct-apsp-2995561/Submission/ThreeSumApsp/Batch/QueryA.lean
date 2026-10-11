/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Batch.Ready
public import Submission.ThreeSumApsp.Programs.Sec4.Theorem30.Query

/-!
# A query of Theorem 30, for arbitrary input arrays

`queryAt` for the invariant `DSReadyA`: the proof of `Sec4.queryAt_spec` goes through as it is,
up to its last step. The value returned is the value of the query of Lemma 28 for the encodings of
the band of I and of the band of J (`queryValue`); Theorem 30 is not used.
-/

@[expose] public section

namespace Light.Batch

open ThreeSumApsp ThreeSumApsp.Spec Light.Sec4 Light.Sec4.QueryAt

/-- queryAt(I, J, b0), for the data structure of the arrays `AL`, `AR`: it returns the value of the
query of the position (I, J) on the encodings of the band of I and the band of J. -/
def QueryAtASpec (lim : Limits) (P : Program) : Prop :=
  ∀ (p : Sec2.Par) (t : ℕ) (hmL : p.m ≤ p.L) (aX aY b0 : ℕ) (AL : ArrL p) (AR : ArrR p) (U : ℤ)
    (μ : ℕ → ℤ) (I J : Fin p.N),
    t ≤ p.m → Lim30 lim p t b0 U → BoundA AL AR U → DSReadyA p t aX aY b0 AL AR μ →
    ∀ d, d + 2 ≤ lim.depth →
    Meets lim P Proc.queryAt d [(I : ℕ), (J : ℕ), b0] μ (tQueryAt p.L p.m t) fun r μ' =>
      r = queryValue p.m t (encRowA AL ((I : ℕ) / (p.K0 * p.N0)))
          (encColA AR ((J : ℕ) / (p.K0 * p.N0))) (outStrOfPos (stdLayout hmL) I J) ∧
        DSReadyA p t aX aY b0 AL AR μ' ∧ SameOutside μ μ' (aWD p b0) (3 * p.L + p.m)

section Proof

variable {lim : Limits} {P : Program} {d : ℕ} {p : Sec2.Par} {t : ℕ} {hmL : p.m ≤ p.L}
  {aX aY b0 : ℕ} {AL : ArrL p} {AR : ArrR p} {U : ℤ} {μ : ℕ → ℤ}

theorem queryAtReads_specA (hlim : Lim30 lim p t b0 U) (hds : DSReadyA p t aX aY b0 AL AR μ)
    {I J : ℕ} (hI : I < p.N) (hJ : J < p.N) :
    Ends lim P d queryAtReads ⟨frame [(I : ℤ), (J : ℤ), (b0 : ℤ)], μ⟩ 90
      (· = ⟨frame (queryAtRead p t b0 I J), μ⟩) := by
  have hw := hlim.std.space_le
  have hdir : b0 + 31 < lim.space ∧ p.aBAND b0 + p.N ≤ lim.space := by
    have := hlim.space
    obtain ⟨⟩ := areas p t b0
    omega
  have dir := hds.shared.dirCells
  have cellT : μ ((b0 : ℤ) + 31).toNat = (t : ℕ) :=
    (congrArg μ (toNat_natCast_add_natCast b0 31)).trans hds.cellT
  have bandI := hds.shared.band I hI
  have bandJ := hds.shared.band J hJ
  light_set (p.L : ℕ) using dir.levels
  light_set (p.m : ℕ) using dir.inner
  light_set (t : ℕ) using cellT
  light_set (p.Lo : ℕ) using dir.outer
  light_set (p.K0 : ℕ) using dir.blocks
  light_set (p.nB : ℕ) using dir.bands
  light_set (p.T : ℕ) using dir.leaves
  light_set (p.aBAND b0 : ℕ) using dir.band
  light_set (p.aBLOCK b0 : ℕ) using dir.block
  light_set (p.aDIG3 b0 : ℕ) using dir.digits
  light_set (aWD p b0 : ℕ) using dir.sharedEnd
  light_set (I / (p.K0 * p.N0) : ℕ) using bandI
  light_set (J / (p.K0 * p.N0) : ℕ) using bandJ
  rfl

theorem outArgs_preA (hlim : Lim30 lim p t b0 U) (hds : DSReadyA p t aX aY b0 AL AR μ)
    (hmL : p.m ≤ p.L) {I J : ℕ} (hI : I < p.N) (hJ : J < p.N) :
    OutDigitsPre lim μ (outArgs p b0 I J) := by
  have hgI : I / p.N0 % p.K0 < p.K0 := Nat.mod_lt _ (K0_pos hmL)
  have hgJ : J / p.N0 % p.K0 < p.K0 := Nat.mod_lt _ (K0_pos hmL)
  have hidx : I / p.N0 % p.K0 * p.K0 + J / p.N0 % p.K0 < p.KK := Nat.mul_add_lt_mul hgI hgJ
  have hsp := hlim.space
  have hmaskI := Nat.mul_add_le_mul hidx (le_refl p.L)
  have hrowI := Nat.mul_add_le_mul hI (le_refl p.Lo)
  have hrowJ := Nat.mul_add_le_mul hJ (le_refl p.Lo)
  have hLo : p.L - p.m = p.Lo := rfl
  obtain ⟨⟩ := areas p t b0
  refine'
    { std := hlim.std
      m_le := hmL
      gI_lt := hgI
      gJ_lt := hgJ
      index_lt := tableIndex_lt p.L p.m (⟨_, hgI⟩, ⟨_, hgJ⟩)
      segMask := segN_of_segB (hds.shared.mask _ hidx)
      segI := hds.shared.dig3 I hI
      segJ := hds.shared.dig3 J hJ
      lenI := length_digitList ..
      lenJ := length_digitList ..
      ltI := fun _ => lt_of_mem_digitList (by norm_num)
      ltJ := fun _ => lt_of_mem_digitList (by norm_num)
      spaceMasks := by change p.aMASK b0 + p.KK * p.L < lim.space; omega
      .. }
  all_goals
    simp only [outArgs, OutDigitsArgs.base]
    omega

theorem queryAtOut_specA (hOut : OutDigitsSpec lim P) (hlim : Lim30 lim p t b0 U)
    (hds : DSReadyA p t aX aY b0 AL AR μ) (hmL : p.m ≤ p.L) {I J : ℕ} (hI : I < p.N)
    (hJ : J < p.N) (hd : d + 1 ≤ lim.depth) :
    Ends lim P d queryAtOut ⟨frame (queryAtLocals p t b0 I J), μ⟩ (tOutDigits p.L + 40) fun σ' =>
      ∃ (r : ℤ) (μ' : ℕ → ℤ), σ' = ⟨frame (queryAtLocals p t b0 I J ++ [r]), μ'⟩ ∧
        SegN μ' (aWD p b0) (digitsO (outStrOfPos (stdLayout hmL) I J)) ∧
        SameOutside μ μ' (aWD p b0) p.L := by
  have hw := hlim.std.space_le
  have hpre := outArgs_preA hlim hds hmL hI hJ
  have blockI := hds.shared.block I hI
  have blockJ := hds.shared.block J hJ
  have hsp := hlim.space
  have hrowI := Nat.mul_add_le_mul hI (le_refl p.Lo)
  have hrowJ := Nat.mul_add_le_mul hJ (le_refl p.Lo)
  have hbound : b0 + 31 < lim.space ∧ p.aBLOCK b0 + p.N ≤ lim.space ∧
      p.aDIG3 b0 + p.N * p.Lo ≤ lim.space := by
    obtain ⟨⟩ := areas p t b0
    omega
  have hprodI : ((p.aDIG3 b0 + I * p.Lo : ℕ) : ℤ) ≤ lim.space := by
    exact_mod_cast (by omega : p.aDIG3 b0 + I * p.Lo ≤ lim.space)
  have hprodJ : ((p.aDIG3 b0 + J * p.Lo : ℕ) : ℤ) ≤ lim.space := by
    exact_mod_cast (by omega : p.aDIG3 b0 + J * p.Lo ≤ lim.space)
  have hI0 : (0 : ℤ) ≤ (I : ℤ) * p.Lo := by positivity
  have hJ0 : (0 : ℤ) ≤ (J : ℤ) * p.Lo := by positivity
  push_cast at hprodI hprodJ
  light_call (hOut _ μ hpre) using queryAtLocals, queryAtRead, outArgs, blockI, blockJ,
    hds.shared.dirCells.mask with r μ' h
  refine ⟨r, μ', rfl, ?_, h.2⟩
  rw [digitsO_outStrOfPos]
  exact h.1

/-- The arguments of the call of queryCore. -/
def coreArgsA (p : Sec2.Par) (t : ℕ) (hmL : p.m ≤ p.L) (b0 : ℕ) (AL : ArrL p) (AR : ArrR p)
    (μ : ℕ → ℤ) (I J : ℕ) : QueryCoreArgs where
  L := p.L
  m := p.m
  t := t
  encA := memRow p b0 μ (I / (p.K0 * p.N0))
  encB := memCol p b0 μ (J / (p.K0 * p.N0))
  η := outStrOfPos (stdLayout hmL) I J
  aA := p.aENCA b0 + I / (p.K0 * p.N0) * p.T
  aB := p.aENCB b0 + J / (p.K0 * p.N0) * p.T
  tr := aTR p b0
  root := (dsTriesA p t AL AR).root (tileOf p I J)
  wd := aWD p b0
  ss := aSS p b0
  box := aBOX p b0
  T := (dsTriesA p t AL AR).cells

theorem abs_enc_mul_leA (hlim : Lim30 lim p t b0 U) (hb : BoundA AL AR U) (β β' : ℕ)
    (τ : Leaf p.L) : |encRowA AL β τ * encColA AR β' τ| ≤ lim.word := by
  obtain ⟨hrow, hcol⟩ := abs_encA_le hb β β'
  rw [abs_mul]
  calc |encRowA AL β τ| * |encColA AR β' τ| ≤ (7 ^ p.L * U) * (7 ^ p.L * U) :=
        mul_le_mul (hrow τ) (hcol τ) (abs_nonneg _) ((abs_nonneg _).trans (hrow τ))
    _ ≤ 10 ^ p.m * ((7 ^ p.L * U) * (7 ^ p.L * U)) :=
        le_mul_of_one_le_left (mul_self_nonneg _) (one_le_pow₀ (by norm_num))
    _ ≤ lim.word := hlim.value

section Tile

variable (I J : Fin p.N)

theorem getElem?_tileOfA (hmL : p.m ≤ p.L) :
    (tileList p.nB (encRowA AL) (encColA AR))[tileOf p I J]?
      = some ⟨arrT (encRowA AL ((I : ℕ) / (p.K0 * p.N0))),
        arrT (encColA AR ((J : ℕ) / (p.K0 * p.N0)))⟩ :=
  getElem?_tileList p.nB _ _ (bandOf_lt_numBands hmL p.N I I.isLt)
    (bandOf_lt_numBands hmL p.N J J.isLt)

theorem coreArgs_agreeA (hSR : SharedReadyA p aX aY b0 AL AR μ) :
    RetAgree p.L p.m (arrT (coreArgsA p t hmL b0 AL AR μ I J).encA)
        (arrT (encRowA AL ((I : ℕ) / (p.K0 * p.N0)))) ∧
      RetAgree p.L p.m (arrT (coreArgsA p t hmL b0 AL AR μ I J).encB)
        (arrT (encColA AR ((J : ℕ) / (p.K0 * p.N0)))) :=
  ⟨retAgree_arrT fun τ hτ => memRow_eqA hSR (bandOf_lt_numBands hmL p.N I I.isLt) τ hτ,
    retAgree_arrT fun τ hτ => memCol_eqA hSR (bandOf_lt_numBands hmL p.N J J.isLt) τ hτ⟩

variable (ht : t ≤ p.m)

include ht

theorem coreArgs_walkA (l : List ℕ)
    (hl : l ∈ boxesOf p.m t (digitsO (coreArgsA p t hmL b0 AL AR μ I J).η)) :
    WalkOK (coreArgsA p t hmL b0 AL AR μ I J).T (coreArgsA p t hmL b0 AL AR μ I J).root l :=
  walkOK_allTries ht (getElem?_tileOfA (AL := AL) (AR := AR) I J hmL)
    (card_innerSetO_outStrOfPos (stdLayout hmL) I J) hl

theorem coreArgs_sumsA (hSR : SharedReadyA p aX aY b0 AL AR μ) (hlim : Lim30 lim p t b0 U)
    (hb : BoundA AL AR U) (j : ℕ) :
    |((coreArgsA p t hmL b0 AL AR μ I J).terms.take j).sum| ≤ lim.word := by
  obtain ⟨hrow, hcol⟩ := abs_encA_le hb ((I : ℕ) / (p.K0 * p.N0)) ((J : ℕ) / (p.K0 * p.N0))
  have hcard : (innerSetO (coreArgsA p t hmL b0 AL AR μ I J).η).card = p.m :=
    card_innerSetO_outStrOfPos (stdLayout hmL) I J
  have hterms := queryTerms_allTries ht (getElem?_tileOfA (AL := AL) (AR := AR) I J hmL) hcard
  obtain ⟨hA, hB⟩ := coreArgs_agreeA (t := t) I J hSR
  have hcongr := queryTerms_congr hA hB t
    (trieLookup (coreArgsA p t hmL b0 AL AR μ I J).T (coreArgsA p t hmL b0 AL AR μ I J).root) hcard
  rw [QueryCoreArgs.terms]
  exact (congrArg (fun l => |(l.take j).sum|) (hcongr.trans hterms)).trans_le
    ((abs_query_partial_sum_le hrow hcol ht hcard j).trans hlim.value)

theorem coreArgs_valueA (hSR : SharedReadyA p aX aY b0 AL AR μ) :
    trieQuery p.m t (arrT (coreArgsA p t hmL b0 AL AR μ I J).encA)
      (arrT (coreArgsA p t hmL b0 AL AR μ I J).encB) (coreArgsA p t hmL b0 AL AR μ I J).T
      (coreArgsA p t hmL b0 AL AR μ I J).root (digitsO (coreArgsA p t hmL b0 AL AR μ I J).η)
      = queryValue p.m t (encRowA AL ((I : ℕ) / (p.K0 * p.N0)))
          (encColA AR ((J : ℕ) / (p.K0 * p.N0))) (outStrOfPos (stdLayout hmL) I J) := by
  have hcard : (innerSetO (coreArgsA p t hmL b0 AL AR μ I J).η).card = p.m :=
    card_innerSetO_outStrOfPos (stdLayout hmL) I J
  obtain ⟨hA, hB⟩ := coreArgs_agreeA (t := t) I J hSR
  refine (trieQuery_congr hA hB t _ _ hcard).trans ?_
  exact trieQuery_allTries ht _ _ (getElem?_tileOfA I J hmL) hcard

end Tile

theorem coreArgs_preA (ht : t ≤ p.m) (hlim : Lim30 lim p t b0 U) (hb : BoundA AL AR U)
    (hds : DSReadyA p t aX aY b0 AL AR μ) (I J : Fin p.N)
    (hwd : SegN μ (aWD p b0) (digitsO (outStrOfPos (stdLayout hmL) I J))) :
    QueryCorePre lim μ (coreArgsA p t hmL b0 AL AR μ I J) := by
  have hβ : (I : ℕ) / (p.K0 * p.N0) < p.nB := bandOf_lt_numBands hmL p.N I I.isLt
  have hβ' : (J : ℕ) / (p.K0 * p.N0) < p.nB := bandOf_lt_numBands hmL p.N J J.isLt
  have hsp := hlim.space
  have hlen := length_dsTriesA_le p t AL AR
  have hrowA := Nat.mul_add_le_mul hβ (le_refl p.T)
  have hrowB := Nat.mul_add_le_mul hβ' (le_refl p.T)
  have hT : 10 ^ p.L = p.T := rfl
  obtain ⟨⟩ := areas p t b0
  refine'
    { std := hlim.std
      t_le := ht
      card := card_innerSetO_outStrOfPos (stdLayout hmL) I J
      segA := seg_memEnc μ _ p.L
      segB := seg_memEnc μ _ p.L
      segT := hds.trie
      segDigits := hwd
      walk := coreArgs_walkA I J ht
      sums := coreArgs_sumsA I J ht hds.shared hlim hb
      prod := fun τ hτ => by
        change |memRow p b0 μ _ τ * memCol p b0 μ _ τ| ≤ _
        rw [memRow_eqA hds.shared hβ τ hτ, memCol_eqA hds.shared hβ' τ hτ]
        exact abs_enc_mul_leA hlim hb _ _ τ
      pow := hlim.pow_le
      .. }
  all_goals
    simp only [coreArgsA]
    omega

theorem queryAtCore_specA (hCore : QueryCoreSpec lim P) (ht : t ≤ p.m)
    (hlim : Lim30 lim p t b0 U) (hb : BoundA AL AR U) (hds : DSReadyA p t aX aY b0 AL AR μ)
    (I J : Fin p.N) (hd : d + 2 ≤ lim.depth) (r : ℤ)
    (hwd : SegN μ (aWD p b0) (digitsO (outStrOfPos (stdLayout hmL) I J))) :
    Ends lim P d queryAtCore ⟨frame (queryAtLocals p t b0 I J ++ [r]), μ⟩
      (tQueryCore p.L p.m t + 60) fun σ' =>
        σ'.loc 0 = queryValue p.m t (encRowA AL ((I : ℕ) / (p.K0 * p.N0)))
          (encColA AR ((J : ℕ) / (p.K0 * p.N0))) (outStrOfPos (stdLayout hmL) I J) ∧
        SameOutside2 μ σ'.mem (aSS p b0) p.m (aBOX p b0) p.L := by
  have hw := hlim.std.space_le
  have hpre := coreArgs_preA ht hlim hb hds I J hwd
  have hvalue := coreArgs_valueA (hmL := hmL) (b0 := b0) (AL := AL) (AR := AR) I J ht hds.shared
  have dir := hds.shared.dirCells
  have htile := tileOf_lt I J hmL
  have cellRoot : μ (aROOTS p b0 + tileOf p I J)
      = ((dsTriesA p t AL AR).root (tileOf p I J) : ℕ) :=
    hds.roots.read (by rw [length_dsTriesA_roots]; exact htile)
  have hdir : b0 + 31 < lim.space ∧ aROOTS p b0 + p.nB * p.nB < lim.space := by
    have hsp := hlim.space
    obtain ⟨⟩ := areas p t b0
    omega
  have hmeets := (hCore _ μ hpre _ (by omega))
  have hencA := hpre.aA_lt
  have hencB := hpre.aB_lt
  generalize queryValue p.m t (encRowA AL ((I : ℕ) / (p.K0 * p.N0)))
    (encColA AR ((J : ℕ) / (p.K0 * p.N0))) (outStrOfPos (stdLayout hmL) I J) = val at hvalue ⊢
  simp only [coreArgsA, tileOf] at hmeets hvalue hencA hencB htile cellRoot
  unfold queryAtLocals queryAtRead
  generalize 10 ^ p.L = leaves at hencA hencB
  generalize (I : ℕ) / (p.K0 * p.N0) = β at *
  generalize (J : ℕ) / (p.K0 * p.N0) = β' at *
  generalize (dsTriesA p t AL AR).root (β * p.nB + β') = root at *
  have hencA' : ((p.aENCA b0 + β * p.T : ℕ) : ℤ) ≤ lim.space := by exact_mod_cast (by omega)
  have hencB' : ((p.aENCB b0 + β' * p.T : ℕ) : ℤ) ≤ lim.space := by exact_mod_cast (by omega)
  have hroot' : ((aROOTS p b0 + (β * p.nB + β') : ℕ) : ℤ) < lim.space := by
    exact_mod_cast (by omega)
  have hrow0 : (0 : ℤ) ≤ (β : ℤ) * p.T := by positivity
  have hcol0 : (0 : ℤ) ≤ (β' : ℤ) * p.T := by positivity
  have hband0 : (0 : ℤ) ≤ (β : ℤ) * p.nB := by positivity
  have haddr : ((aROOTS p b0 : ℤ) + ((β : ℤ) * p.nB + β')).toNat
      = aROOTS p b0 + (β * p.nB + β') := by exact_mod_cast Int.toNat_natCast _
  push_cast at hencA' hencB' hroot'
  light_call hmeets using dir.encA, dir.encB, haddr, cellRoot with r' μ' h
  refine ⟨?_, h.2⟩
  simp only [setLocal, List.cons_append, frame, List.getD_cons_zero]
  rw [h.1, hvalue]

/-- **queryAt** meets its specification for arbitrary input arrays. -/
theorem queryAtA_spec (hP : P[Proc.queryAt]? = some queryAtBody) (hOut : OutDigitsSpec lim P)
    (hCore : QueryCoreSpec lim P) : QueryAtASpec lim P := by
  intro p t hmL aX aY b0 AL AR U μ I J ht hlim hb hds
  refine fun d hd => ⟨queryAtBody, hP, ?_⟩
  unfold tQueryAt
  light_piece (queryAtReads_specA hlim hds I.isLt J.isLt) with _ rfl
  light_piece (queryAtAreas_spec hlim I J) with _ rfl
  light_piece (queryAtOut_specA hOut hlim hds hmL I.isLt J.isLt (by omega))
    with _ ⟨r, μ₁, rfl, hwd, same₁⟩
  have same₁' : SameOutside μ μ₁ (aWD p b0) (3 * p.L + p.m) := same₁.mono le_rfl (by omega)
  light_piece (queryAtCore_specA hCore ht hlim hb (hds.of_same same₁') I J (by omega) r hwd)
    with ⟨loc₂, μ₂⟩ ⟨hr, same₂⟩
  have same₂' : SameOutside μ μ₂ (aWD p b0) (3 * p.L + p.m) := by
    obtain ⟨⟩ := areas p t b0
    exact same₁'.then same₂ fun b hb => ⟨hb, by omega, by omega⟩
  exact ⟨hr, hds.of_same same₂', same₂'⟩

end Proof

end Light.Batch
