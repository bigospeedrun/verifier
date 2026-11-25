import Submission.BinaryKernel.BatchPost
import Submission.BinaryKernel.BatchRun

namespace DFTSpeedrun.Batch
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open OAI.Computability.NearSquareRoot.KernelPass
noncomputable section

/-- With any fixed number of spectator pairs, execute the active plan on
exactly the rounded-up number of row banks and apply the spectator transform. -/
theorem fixed_s {ι : Type*} {A W s : ℕ} {cl m} {port : Port} {b : RAM.Bank port ι}
    {k h Z : ι → ℕ} (ha : 0 < A) (hw : 0 < W)
    (eqdim : ∀ i, A*(h i*2)+s*2=k i*2)
    (v : ∀ i, Bits (k i*2) → ℂ)
    (sh : Small b.B h) (sn : Small b.B fun i => 2^(k i*2))
    (kn : Knows m b.B (HalfKernel.Src cl) (fun i => (k i,(bits (k i*2)).tape (v i))) h)
    {p : Plan A W W} (ok : Correct p) (exec : PlanCompiler.Executes b m cl h Z p) :
    Able m b (HalfKernel.Src cl) (bundle cl)
      (fun i => (k i,(bits (k i*2)).tape (v i)))
      (fun i => (bits (k i*2)).tape (WalshBridge.normalized (k i*2) (v i)))
      (fun i => 2^(k i*2)) (fun i => ((4^s ⌈/⌉ W) * p.calls) * Z i) := by
  have run := run_groups ha hw eqdim v sh sn kn exec
  have post := reassemble (cl:=cl) (m:=m) hw eqdim v sn ok
  exact (run.save (Able.of_can post)).weaken (Dom.two _) (fun i => by simp [rows,groups])

end
end DFTSpeedrun.Batch
