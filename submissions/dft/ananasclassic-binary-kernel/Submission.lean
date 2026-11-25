import Submission.BinaryKernel.RootFinal
import Submission.BinaryKernel.Batch
import Submission.LegacyCredits

/-!
# Exact DFT on the Big O scalar/index RAM with saving just below one half

Submitted by Vladislav Kuznetsov (AnanasClassic), with OpenAI Codex.

OpenAI's binary normalized Walsh template (openai/math, commit
3344da59991ed94f9ba711217b29c1d760badfa6, family 379) supplies the
mathematical construction and strict call-rate inequality. The 155 imported
OpenAI modules in the NearSquareRoot and FiniteFourier trees retain their
original namespaces and have their imports relocated under Submission.
The template is chosen once, before the input length or vector is given.

This port implements the template in the challenge RAM. It constructs its
index and coefficient tables, groups and pads independent rows, runs one
recursive call per fiber, and bounds their total work. A pair of diagonal
passes converts the normalized Walsh transform into the two-point kernel
of the existing all-length DFT compiler. The exponent of the binary kernel
is strictly smaller than the target exponent, to absorb the compiler overhead.

The exact scalar/index RAM and original all-length reduction are by OpenAI.
The generic compiler and its exponent-parametric interface were taken from
bigospeedrun/verifier PR 222 (head c989bb57b9b141e80353e22df3e75709206b22e9).
The rate-to-DFT wrapper is from Gigabyte0x1337's PR 220. The compiler lineage,
prior submitter notices and Apache-2.0 license text are in LegacyCredits.lean.
The earlier numerical suppliers are historical predecessors of this compiler.
-/

open OAI.PowerSaving Filter Asymptotics

private theorem uniformBatch {A W : ℕ}
    (p : OAI.Computability.NearSquareRoot.KernelPass.Plan A W W) :
    DFTSpeedrun.HalfKernel.BatchLaw p := by
  intro ι s cl m b k h Z ha hw eqdim v sh sn kn ok exec
  exact DFTSpeedrun.Batch.fixed_s (p:=p) ha hw eqdim v sh sn kn ok exec

theorem Race.bound : ∃ order solve W, DFTProgram order solve W ∧
    (fun n : ℕ => (W n : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) * (Real.log (n : ℝ)) ^
        (1 - (4999999999999999999999999999999999999999 : ℝ) /
          9999999999999999999999999999999999999999)) :=
  DFTSpeedrun.HalfKernel.bound_of_batch (uniformBatch DFTSpeedrun.SelectedPlan.fixedPlan.program)

#print axioms Race.bound
