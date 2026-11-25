import Submission.BinaryKernel.ComplexPlan
import Submission.OAI.Computability.NearSquareRoot.KernelBinaryTemplate

/-! The strict normalized Walsh template at a rational exponent lying between
one half and the running-time exponent of the largest admissible saving below
one half. Its literal opcode data are fixed before the input size is chosen. -/

namespace DFTSpeedrun.SelectedPlan
open OAI.Computability.NearSquareRoot.KernelPass
open DFTSpeedrun.ComplexPlan

def D : ℕ := 10^40 - 1

noncomputable def beta : ℝ := ((2*D+1 : ℕ) : ℝ) / (4*D : ℕ)

noncomputable def saving : ℝ := ((D/2 : ℕ) : ℝ) / (D : ℝ)

theorem half_lt_beta : (1:ℝ)/2 < beta := by norm_num [beta,D]
theorem beta_lt_target : beta < 1-saving := by norm_num [beta,D,saving]

noncomputable def fixedPlan : Candidate :=
  binaryTemplate (2*D+1) (4*D) half_lt_beta

theorem fixedPlan_good : fixedPlan.Good (2*D+1) (4*D) :=
  binaryTemplate_good _ _ _

theorem strict_call_rate :
    (fixedPlan.program.calls : ℝ) / fixedPlan.rows < (fixedPlan.arity : ℝ)^beta :=
  fixedPlan_good.2.2.2

theorem normalized_batch (h : ℕ) (x : ComplexPlan.Bank fixedPlan.arity h fixedPlan.rows) :
    act fixedPlan.program h x = fun b y => ∑ u : Addr fixedPlan.arity h,
      (∏ c, ∏ j, (pairEntry (y c j) (u c j) : ℂ)) * x b u :=
  correct fixedPlan_good.2.2.1 x

end DFTSpeedrun.SelectedPlan
