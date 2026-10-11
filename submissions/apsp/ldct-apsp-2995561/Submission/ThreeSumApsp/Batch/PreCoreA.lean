/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Batch.Ready
public import Submission.ThreeSumApsp.Programs.Sec4.Theorem30.Preprocessing

/-!
# The preprocessing of Theorem 30, for arbitrary input arrays

The two parts of preCore behind the shared stage (`preCoreAddr`, `preCoreFinish`) for the
invariant `SharedReadyA`: they only read the directory and the encodings, so the proofs of
`Sec4.preCoreAddr_spec` and `Sec4.preCoreFinish_spec` go through as they are.
-/

@[expose] public section

namespace Light.Batch

open ThreeSumApsp ThreeSumApsp.Spec Light.Sec4 Light.Sec4.PreCore

variable {lim : Limits} {P : Program} {d : ℕ} {p : Sec2.Par} {t : ℕ} {aX aY b0 : ℕ}
  {AL : ArrL p} {AR : ArrR p} {U : ℤ} {μ : ℕ → ℤ}

theorem preCoreAddr_specA (ht : t ≤ p.m) (hlim : Lim30 lim p t b0 U)
    (hSR : SharedReadyA p aX aY b0 AL AR μ) (r : ℤ) :
    Ends lim P d preCoreAddr ⟨frame (preShared p t aX aY b0 r), μ⟩ 38
      (· = ⟨frame (preLocals p t aX aY b0 r), μ⟩) := by
  have dir := hSR.dirCells
  light_facts hlim hlim.std
  obtain ⟨⟩ := areas p t b0
  unfold preLocals preShared
  have hsq : ((p.nB * p.nB : ℕ) : ℤ) ≤ lim.space := by
    exact_mod_cast (by omega : p.nB * p.nB ≤ lim.space)
  have htr : ((aROOTS p b0 + p.nB * p.nB : ℕ) : ℤ) = aTR p b0 := by
    exact_mod_cast (by omega : aROOTS p b0 + p.nB * p.nB = aTR p b0)
  have hsq0 : (0 : ℤ) ≤ (p.nB : ℤ) * p.nB := by positivity
  push_cast at hsq htr
  light_set (aWD p b0 : ℕ) using dir.sharedEnd
  light_set (p.nB : ℕ) using dir.bands
  light_set (aCUR p b0 : ℕ)
  light_set (aBOX p b0 : ℕ)
  light_set (aFP p b0 : ℕ)
  light_set (aROOTS p b0 : ℕ)
  light_set (p.m - t : ℕ)
  light_set (aTR p b0 : ℕ)
  rfl

theorem allArgs_preA (h : Lim30 lim p t b0 U) (ht : t ≤ p.m) (hmL : p.m ≤ p.L)
    (hb : BoundA AL AR U) (hSR : SharedReadyA p aX aY b0 AL AR μ)
    (hTM : TrieMem μ (aTR p b0) (trieCap p t) (aFP p b0) [0]) :
    AllTilesPre lim μ (allArgs p t b0 μ) := by
  have hsp := h.space
  have hT : 10 ^ p.L = p.T := rfl
  obtain ⟨⟩ := areas p t b0
  exact
    { std := h.std
      t_le := ht
      m_le := hmL
      value_le := ⟨7 ^ p.L * U, 7 ^ p.L * U,
        fun β hβ τ hτ => by
          change |memRow p b0 μ β τ| ≤ _
          rw [memRow_eqA hSR hβ τ hτ]
          exact (abs_encA_le hb β β).1 τ,
        fun β hβ τ hτ => by
          change |memCol p b0 μ β τ| ≤ _
          rw [memCol_eqA hSR hβ τ hτ]
          exact (abs_encA_le hb β β).2 τ, h.value⟩
      pow_le := h.pow_le
      cap_ge := le_rfl
      order := by simp only [allArgs]; rw [hT]; omega
      segA := fun β _ => seg_memEnc μ _ p.L
      segB := fun β _ => seg_memEnc μ _ p.L
      trie := hTM }

theorem preCoreFinish_specA (hAll : AllTilesSpec lim P) (hlim : Lim30 lim p t b0 U)
    (ht : t ≤ p.m) (hmL : p.m ≤ p.L) (hb : BoundA AL AR U) (hd : d + 5 ≤ lim.depth) (r : ℤ)
    (hSR : SharedReadyA p aX aY b0 AL AR μ) (hcellT : μ (b0 + 31) = t) :
    Ends lim P d preCoreFinish ⟨frame (preLocals p t aX aY b0 r), μ⟩
      (tAllTiles p.L p.m t p.nB + 28) fun σ' =>
      DSReadyA p t aX aY b0 AL AR σ'.mem ∧
        SameOutside μ σ'.mem (aCUR p b0) (top p t b0 - aCUR p b0) := by
  light_facts hlim hlim.std
  have hend : p.sharedEnd b0 = aWD p b0 := rfl
  obtain ⟨⟩ := areas p t b0
  unfold preLocals preShared
  light_store (aTR p b0) 0
  light_store (aFP p b0) 1
  have hTM := trieMem_start p t b0 μ
  have same : SameOutside μ (Function.update (Function.update μ (aTR p b0) 0) (aFP p b0) 1)
      (aCUR p b0) (top p t b0 - aCUR p b0) :=
    (SameOutside.refl.update (by omega) 0).update (by omega) 1
  generalize Function.update (Function.update μ (aTR p b0) 0) (aFP p b0) 1 = μ₁ at *
  have hSR₁ : SharedReadyA p aX aY b0 AL AR μ₁ :=
    hSR.of_agree fun b hb _ => same b (Or.inl (by omega))
  have dir := hSR₁.dirCells
  light_call (hAll _ μ₁ (allArgs_preA hlim ht hmL hb hSR₁ hTM))
    using allArgs, dir.encA, dir.encB, dir.leaves, Sec2.Par.T with r' μ₂ ⟨hTM₂, hroots, same₂⟩
  have htries : (allArgs p t b0 μ₁).tries = dsTriesA p t AL AR := allTries_mem_eqA hSR₁
  rw [htries] at hTM₂ hroots
  have same' : SameOutside μ μ₂ (aCUR p b0) (top p t b0 - aCUR p b0) :=
    same.then same₂ fun b hb =>
      ⟨hb, by change b < aCUR p b0 ∨ aTR p b0 + trieCap p t ≤ b; omega⟩
  exact ⟨⟨hSR.of_agree fun b hb _ => same' b (Or.inl (by omega)),
    (same' _ (Or.inl (by omega))).trans hcellT, hroots, hTM₂.seg⟩, same'⟩

end Light.Batch
