/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Batch.ORunOracle
public import Submission.ThreeSumApsp.Batch.ONeedPoly
public import Submission.ThreeSumApsp.Filter2.Final

/-!
# APSP in time `n^{2.99556085}`

The batched counting oracle solves its task within `oTimeF`; with the bound on `oTimeF`
(`oTimeF_le`) and the polynomial need (`oNeed_poly`), the filter gives APSP in `n^{2.99556085}`.
-/

@[expose] public section

namespace Light.Batch

open ThreeSumApsp ThreeSumApsp.Batch Light.Sec4 Light.Filter2

/-- The time of a batch, by its terms. -/
theorem tOBatch_le {n s p : ℕ} (hn : 1 ≤ n) (hs : 1 ≤ s) (hp : 1 ≤ p) :
    tOBatch n s p + 8 ≤ tPreCore cShared30 (oPar n s p) (oT s p)
      + oKK s p * (n * n) * tQueryAt (oL s p) (oM s p) (oT s p)
      + 400 * (oKK s p * oNP n s p * oD s p + oKK s p * n * oDig p * (s + 1)
        + oKK s p * n * n + 1) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hSz⟩ := oParams_facts (n := n) hs hp
  unfold tOBatch tOBTail tWriteSrc tQueries tFill
  rw [hSz]
  generalize tPreCore cShared30 (oPar n s p) (oT s p) = P
  generalize tQueryAt (oL s p) (oM s p) (oT s p) = q
  generalize oKK s p = K
  generalize oNP n s p = N
  generalize oD s p = D
  generalize oDig p = k
  have h1 : K * n ≤ K * n * n := Nat.le_mul_of_pos_right _ hn
  have h2 : K ≤ K * n := Nat.le_mul_of_pos_right _ hn
  ring_nf at h1 h2 ⊢
  omega

/-- **The time of the oracle** is at most `oTimeF` with the constant `3 000 000`. -/
theorem tOracle_le {n U s p : ℕ} (hn : 1 ≤ n) (hs : 1 ≤ s) (hp : 1 ≤ p) :
    tOracle n U s p ≤ oTimeF 3000000 n U s p := by
  have h1 := tOParams_le (n := n) hs hp
  have h2 := tOTables_le (n := n) (U := U) (s := s) hp
  have h3 := Nat.mul_le_mul_left (oBat n s p) (tOBatch_le hn hs hp)
  have h4 : n * n ≤ n * n * (Nat.log 2 (U + 1) + 2) := Nat.le_mul_of_pos_right _ (by omega)
  unfold tOracle oTimeF
  rw [if_neg (by omega)]
  generalize tOParams n s p = a at h1 ⊢
  generalize tOTables n U s p = b at h2 ⊢
  generalize tOBatch n s p = c at h3 ⊢
  generalize tPreCore cShared30 (oPar n s p) (oT s p) = P at h3 ⊢
  generalize tQueryAt (oL s p) (oM s p) (oT s p) = q at h3 ⊢
  generalize 4 ^ oL s p = F at h1 ⊢
  ring_nf at h1 h2 h3 h4 ⊢
  omega

/-- **The batched counting oracle solves its task.** -/
theorem oracle_solves : SolvesN oracleTask oProg pOracle
    (fun ps => oTimeF 3000000 (ps.getD 0 0) (ps.getD 1 0) (ps.getD 2 0) (ps.getD 3 0)) oNeed := by
  refine ⟨oracleBody, by simpa using oProg_at 84 (R := []), fun R lim d x μ fr hpre hok => ?_⟩
  exact (oracle_ends R hpre hok).mono (tOracle_le hpre.n_pos hpre.s_pos hpre.p_pos) fun _ h => h

end Light.Batch

/-- **APSP is solved in time `O(n^{2.99556085})`.** -/
theorem apsp_299556085 : EndStatement.APSP.SolvedInTime (2.99556085 : ℚ) :=
  Light.Filter2.apsp_299556085_of_oracle Light.Batch.oracle_solves Light.Batch.oNeed_poly
    fun c κ => Light.Batch.oTimeF_le 3000000 c κ
