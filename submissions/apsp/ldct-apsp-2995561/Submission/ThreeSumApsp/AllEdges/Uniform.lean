/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.AllEdges.Claim
public import Submission.ThreeSumApsp.Programs.Sec3.Theorem19.ChooseBySize
public import Submission.ThreeSumApsp.RunningTimes.Sec3.Corollary15_16
public import Submission.ThreeSumApsp.TimeClaims.Sec3.Theorem19

/-!
# All-edges Exact Triangle in time `n^{3−0.00175}`, for all sizes

Theorem 19 with Corollary 16 for the all-edges host, and brute force below a threshold:
`claim_aeUniform : Claim.ExactTriangleUniform aeModel 0.00175 1`.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {d : ℕ}

/-- chooseAE(n, U, ab, bc, ac, out, fr): calls p₁ if n < n₀, and p₂ if not. -/
def aeBySizeBody (n₀ p₁ p₂ : ℕ) : Stmt :=
  .ite (v 0 <' k n₀) (.call p₁ [v 0, v 1, v 2, v 3, v 4, v 5, v 6] 0)
    (.call p₂ [v 0, v 1, v 2, v 3, v 4, v 5, v 6] 0)

theorem aeBySize_spec {P₀ R : Program} {n₀ p₁ p₂ : ℕ} {T₁ T₂ : ℕ → ℕ → ℕ} {r₁ r₂ : ℕ → ℕ → Need}
    (h₁ : Solves aeTask P₀ p₁ T₁ r₁) (h₂ : Solves aeTask P₀ p₂ T₂ r₂) {x : AEInst} {μ : ℕ → ℤ}
    {fr : ℕ} (hpre : x.Pre μ fr) (hok : (bySizeNeed n₀ r₁ r₂ x.n x.U).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (aeBySizeBody n₀ p₁ p₂) ⟨frame (aeTask.args x ++ [(fr : ℤ)]), μ⟩
      (bySizeTime n₀ T₁ T₂ x.n x.U + 2) fun σ' => aeTask.Post x μ fr (σ'.loc 0) σ'.mem := by
  have hword : ((n₀ + (r₁ x.n x.U).word + (r₂ x.n x.U).word : ℕ) : ℤ) ≤ lim.word := hok.word
  have hdep : d + (1 + (r₁ x.n x.U).depth + (r₂ x.n x.U).depth) ≤ lim.depth := hok.depth
  have hok₁ : (r₁ x.n x.U).Ok lim fr (d + 1) := hok.mono (by simp only [bySizeNeed]; omega)
    (by simp only [bySizeNeed]; omega) (by simp only [bySizeNeed]; omega)
  have hok₂ : (r₂ x.n x.U).Ok lim fr (d + 1) := hok.mono (by simp only [bySizeNeed]; omega)
    (by simp only [bySizeNeed]; omega) (by simp only [bySizeNeed]; omega)
  have hm₁ : Meets lim (P₀ ++ R) p₁ (d + 1) [x.n, x.U, x.ab, x.bc, x.ac, x.out, fr] μ (T₁ x.n x.U)
      (aeTask.Post x μ fr) := h₁.meets R x fr hpre hok₁
  have hm₂ : Meets lim (P₀ ++ R) p₂ (d + 1) [x.n, x.U, x.ab, x.bc, x.ac, x.out, fr] μ
      (T₂ x.n x.U) (aeTask.Post x μ fr) := h₂.meets R x fr hpre hok₂
  change Ends lim (P₀ ++ R) d (aeBySizeBody n₀ p₁ p₂)
    ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, x.out, fr], μ⟩ _ _
  unfold bySizeTime
  refine Ends.iteLast (fun hc => ?_) (fun hc => ?_)
  · rw [if_pos (show x.n < n₀ by simp at hc; omega)]
    exact Ends.callTo hm₁ fun _ _ h => h
  · rw [if_neg (show ¬ x.n < n₀ by simp at hc; omega)]
    exact Ends.callTo hm₂ fun _ _ h => h

/-- **Two algorithms for all-edges Exact Triangle, chosen by the size of the instance.** -/
theorem closure_aeChooseBySize : Closure.ChooseBySize aeModel := by
  refine fun n₀ => ⟨14, fun T₁ T₂ hT₁ hT₂ => ?_⟩
  obtain ⟨Q₁, p₁, Tn₁, r₁, hr₁, hs₁, ht₁⟩ := hT₁
  obtain ⟨Q₂, p₂, Tn₂, r₂, hr₂, hs₂, ht₂⟩ := hT₂
  have g₁ : Solves aeTask (Program.behind Q₁ Q₂) p₁ Tn₁ r₁ := hs₁.append _
  have g₂ : Solves aeTask (Program.behind Q₁ Q₂) (p₂ + Q₁.length) Tn₂ r₂ :=
    ChooseHost.solves_behind hs₂ Q₁
  refine ⟨Program.behind Q₁ Q₂ ++ [aeBySizeBody n₀ p₁ (p₂ + Q₁.length)],
    (Program.behind Q₁ Q₂).length, fun n U => bySizeTime n₀ Tn₁ Tn₂ n U + 2,
    bySizeNeed n₀ r₁ r₂, ChooseHost.polyNeed_bySize n₀ hr₁ hr₂, ?_, fun n U u hn hU hu => ?_⟩
  · refine ⟨aeBySizeBody n₀ p₁ (p₂ + Q₁.length), by simp, fun R lim d x μ fr hpre hok => ?_⟩
    rw [List.append_assoc]
    exact aeBySize_spec g₁ g₂ hpre hok
  · simp only [bySizeTime]
    push_cast
    split_ifs
    · linarith [ht₁ n U u hn hU hu]
    · linarith [ht₂ n U u hn hU hu]

/-- A larger time. -/
theorem closure_aeMono : Closure.MonoExactTriangle aeModel :=
  fun _ _ hle hT => SolvedIn.mono hT hle

/-- Theorem 19 by Corollary 26, for the all-edges host. -/
theorem claim_ae_theorem_19 : Claim.Theorem_19_explicit aeModel 0.00175 1 :=
  Theorem19.explicit_of_theorem_17_corollary_16 _ claim_ae_theorem_17₂₆ claim_corollary_16

/-- **All-edges Exact Triangle in time `K s^{3−0.00175} (log s + 1) (1 + log u)²`.** -/
theorem claim_aeUniform : Claim.ExactTriangleUniform aeModel 0.00175 1 :=
  exactTriangleUniform_of_explicit _ 1 (by norm_num) (by norm_num) claim_ae_theorem_19
    claim_aeBruteForce closure_aeChooseBySize closure_aeMono

end Light.Sec3
