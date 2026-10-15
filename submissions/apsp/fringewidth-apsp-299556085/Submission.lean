/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

APSP in time O(n^2.99556085) on the word-RAM of `EndStatement`.

This is the proof of Li Xuanji (GitHub: ldct), bigospeedrun/verifier pull request #6, commit
a6e77d9a122e9e3137afbf2e1ac310b2032447f4, which extends the Lean development of anthropics/formal-math
(3sum-apsp, commit e1a4e6508154ea59f030480661590a9fe3018011, by Anthropic, after the paper of Josh Alman
and Virginia Vassilevska Williams, arXiv:2610.06783) with deterministic prime-by-prime filtering,
two-digit residue lifting and batched tensor slots. The algorithm and its parameters (c = 20,
θ = 56569/500000, σ = 0.0336175) are unchanged. The only change is a sharper numerical certificate of
those parameters: `Batch/Numbers.lean` now proves Γ(20, θ) > 0.0660254 (value 0.0660254068…) and
q(θ) < 0.4339741 (value 0.4339740645…) in place of 0.066025 and 0.433975, and the absorption constants
of `Batch/OBound.lean`, `Filter2/Final.lean`, `Filter2/Chain.lean` and `Batch/Final.lean` are lowered
accordingly, from 2.995561 to 2.99556085. Prepared with Claude (Claude Fable 5.1, Claude Code) for
fringewidth. Credits and notices of the inherited sources are retained in the files above.
-/
import Submission.EndStatement
import Submission.ThreeSumApsp.Batch.Final

theorem Race.bound : EndStatement.APSP.SolvedInTime ((59911217 : Rat) / 20000000) := by
  have h : ((59911217 : Rat) / 20000000) = (2.99556085 : ℚ) := by norm_num
  rw [h]
  exact apsp_299556085
