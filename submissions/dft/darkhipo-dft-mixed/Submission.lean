/-
Maintainer packaging for Big O Speedrun.
Claim authors: Dmitri Arkhipov. Other source credits are retained below.
Upstream: https://github.com/shea256/fourier-transform-below-nlogn
Commit: 9749945f0f3f7fa0edb22065c786f7106953f1db
Witness words: https://github.com/CrocSwap/integer-mult-bounds
Commit: 7732dd5e46863ff294b5e443661cb9d99abf4e01
Entry point: lean/complex588/Work/FourierC588/Main.lean, transform_mainC588.
Saving: 20099/16000000.

dmitriarkhipov submits this packaging and claims no new authorship of the
framework or the witness words. The 381-module proof closure is copied under
Submission/, changing local import paths only. This submission extends the
framework with a mixed-dispatch invocation interface (per-call provider
table), a widened gate-kind discipline (K2x: phase-A x-targets from x), and
a widened packed-vector tag region (64→128 bits) to accommodate the hybrid
certificate's gauge dataflow. The verifier independently supplies its trusted
challenge; the source's standalone challenge and wrapper are not used.

This bound uses the PR588/PR596 community witness words (complex-571-hpeq5:
ck × 53 calls, atm3 × 19 calls) re-hosted under the dedicated-bank framework
via the source-copy conversion (84 partial copies, the read-closure of
slot→x destinations), hyperplane-end promotion to full frame, width
unification padding, and a cyclic bank schedule (4824 banks, m=73). The
exact-rational rate is certified at δ = 20099/16000000 with positive slack.

Credits from the pinned upstream README:
We acknowledge **OpenAI** for the original framework and Fourier reduction;
**Douglas (Doug) Colkitt** for early network research and community
integration; **Rohan Arun** for fixed-basis/corner composition; and
**Swapnil Jain** for the adopted complex witnesses.

The framework and Lean engine are by **Jacob Sussman**. The #401/#377 geometry
is by **Dugongue** and **Zhihao Chen / jacklightChen**. The gauged Lean
extension is from **Nil Mamano's** published submission. The exact model and
all-length reduction are by **OpenAI**. The record proof (complex588) is by
**Jeremy Kothe** and **Ryan Shea** (shea256). The witness words
(complex-571-hpeq5) are from **CrocSwap/integer-mult-bounds**, building on
PR558 geometry and PR568/569/571/575/583 dependencies with their own credits.

Our additions: the mixed-dispatch per-call invocation table (G401.I), the K2x
gate-kind widening, the Bits.lean tag-region widening (64→128), the partial
source-copy conversion (84-copy closure), the hyperplane-end promotion, the
width unification padding, the ghost-free mirror fix, and the E1 proof
extension (ggeom401Tbl, bridge401_gcertTbl, dispatchTbl).

Previous bound: shea256/jeremykothe2 at 2466337/2000000000 (δ = 0.0012331685).
This submission: 123316855/100000000000 (δ = 0.00123316855), a +0.0000041% improvement.
-/

import Submission.Work.FourierC588.Main

open OAI OAI.PowerSaving Filter Asymptotics

/-- **The claimed saving.** `123316855/10^11` = 0.00123316855, strictly above the standing
record `12331685/10^10` = 0.0012331685 and strictly below the construction's certified
exponent delta `12331686/10^10` (the gap `alphaC588 < decimalExponentC588` is what absorbs
the `(log log n)^2` reduction overhead in `flight_littleC588`). -/
theorem Race.bound : ∃ order solve W, DFTProgram order solve W ∧
    (fun n : ℕ => (W n : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) * (Real.log (n : ℝ)) ^ (1 - (123316855 : ℝ) / 100000000000)) := by
  obtain ⟨order, solve, W, hprog, hbounds⟩ := transform_mainC588
  refine ⟨order, solve, W, hprog, ?_⟩
  exact hbounds.2.1
