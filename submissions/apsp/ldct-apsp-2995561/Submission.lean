/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

APSP in time O(n^2.995561) on the word-RAM of `EndStatement`.
The proof extends the Lean development of anthropics/formal-math (3sum-apsp, commit
e1a4e6508154ea59f030480661590a9fe3018011, by Anthropic, after the paper of Josh Alman and
Virginia Vassilevska Williams, arXiv:2610.06783) with deterministic prime-by-prime filtering,
two-digit residue lifting and batched tensor slots (files under `Submission/ThreeSumApsp/Filter2`
and `Submission/ThreeSumApsp/Batch`). Prepared with Claude for xuanji (GitHub: ldct).
-/
import Submission.EndStatement
import Submission.ThreeSumApsp.Batch.Final

theorem Race.bound : EndStatement.APSP.SolvedInTime ((2995561 : Rat) / 1000000) := by
  have h : ((2995561 : Rat) / 1000000) = (2.995561 : ℚ) := by norm_num
  rw [h]
  exact apsp_2995561
