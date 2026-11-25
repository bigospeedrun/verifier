import Submission.BinaryKernel.Target
import Submission.BinaryKernel.Dispatch
import Submission.BinaryKernel.PlanLeaves

/-! Eliminate every opcode and cost-bound hypothesis for the fixed binary
template. The remaining argument is the spectator batch implementation. -/
open OAI.PowerSaving Asymptotics Filter DFTSpeedrun
open DFTSpeedrun.HalfKernel DFTSpeedrun.SelectedPlan

namespace DFTSpeedrun.HalfKernel
noncomputable section

/-- Maximality among the positive-denominator fractions below one half
accepted by a forty-digit denominator field. -/
theorem maximal_strict_saving {p q : ℕ} (hq : 0 < q) (cap : q ≤ D) (strict : 2*p < q) :
    (p : ℝ)/q ≤ saving := by
  have odd : 2*(D/2)+1 = D := by norm_num [D]
  have hh := Nat.mul_le_mul_right D (show 2*p+1 ≤ q by omega)
  have width : q*D = 2*((D/2)*q)+q := by
    calc q*D = q*(2*(D/2)+1) := congrArg (q * ·) odd.symm
         _ = _ := by ring
  have frac : p*D ≤ (D/2)*q := by
    rw [Nat.add_mul,Nat.one_mul, Nat.mul_assoc,width] at hh
    omega
  apply (div_le_div_iff₀ (by exact_mod_cast hq) (by norm_num [D] : (0 : ℝ)<D)).2
  exact_mod_cast frac

private theorem large_of_body {cl : RAM.Paint} {m : Bool} {A W σ r : ℕ}
    (h : Body cl m A W σ r) : LargeBody cl m A W σ r := by
  refine (h.reindex (fun g : BigCtx cl A r => g.1)).mono (fun _ => le_rfl) ?_
  intro g
  simp [charge,g.2]

theorem bound_of_batch (batch : BatchLaw fixedPlan.program) :
    ∃ order solve W, DFTProgram order solve W ∧
      (fun n : ℕ => (W n : ℝ)) =O[atTop]
        (fun n : ℕ => (n : ℝ) * (Real.log (n : ℝ)) ^
          (1 - (4999999999999999999999999999999999999999 : ℝ) /
            9999999999999999999999999999999999999999)) := by
  have goal := bound_of_large (fun r _ cl m => large_of_body
    (assemble_body (cl:=cl) (m:=m) (r:=r) (by have := fixedPlan_good.1; omega)
      (by have := fixedPlan_good.2.1; omega) fixedPlan_good.2.2.1 batch
      (fun ha sh sv => ⟨PlanCompiler.xor_exec ha sh sv,PlanCompiler.scale_exec ha sh sv⟩)))
  simpa only [show saving = (4999999999999999999999999999999999999999 : ℝ) /
      9999999999999999999999999999999999999999 by norm_num [saving,D]] using goal

end
end DFTSpeedrun.HalfKernel
#print axioms DFTSpeedrun.HalfKernel.bound_of_batch
