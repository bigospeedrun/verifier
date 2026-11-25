import Submission.BinaryKernel.BatchPack
import Submission.BinaryKernel.FixedGather

namespace DFTSpeedrun.Batch
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open OAI.Computability.NearSquareRoot.KernelPass
open FixedRows AxisLayout
noncomputable section

theorem run_groups {ι : Type*} {A W s : ℕ} {cl m} {port : Port} {b : RAM.Bank port ι}
    {k h Z : ι → ℕ} (ha : 0 < A) (_hw : 0 < W)
    (eqdim : ∀ i, A*(h i*2)+s*2=k i*2)
    (v : ∀ i, Bits (k i*2) → ℂ)
    (sh : Small b.B h) (sn : Small b.B fun i => 2^(k i*2))
    (kn : Knows m b.B (HalfKernel.Src cl) (fun i => (k i,(bits (k i*2)).tape (v i))) h)
    {p : Plan A W W} (exec : PlanCompiler.Executes b m cl h Z p) :
    Able m b (HalfKernel.Src cl) (Ty.a (Ty.a (bundle cl)))
      (fun i => (k i,(bits (k i*2)).tape (v i))) (fun i => result (eqdim i) (v i) p)
      (fun i => 2^(k i*2)) (fun i => (groups s W * p.calls) * Z i) := by
  let V := fun g : Fin (groups s W) => fun i => bankTape (shape A (h i))
    (ComplexPlan.act p (h i) (input (eqdim i) (v i) g))
  have each (g : Fin (groups s W)) : Able m b (HalfKernel.Src cl) (Ty.a (bundle cl))
      (fun i => (k i,(bits (k i*2)).tape (v i))) (V g)
      (fun i => 2^(k i*2)) (fun i => p.calls * Z i) := by
    have pack := pack_group (W:=W) ha eqdim v sh sn kn g
    have core := exec (fun i => input (eqdim i) (v i) g)
    refine ((Able.of_can pack).comp core).weaken ⟨2,fun i => ?_⟩ (fun i => by simp)
    have hvol : PlanCompiler.volume A (h i) ≤ 2^(k i*2) := by
      rw [←eqdim i, pow_add, volume_bits]; exact Nat.le_mul_of_pos_right _ (by positivity)
    dsimp only; omega
  exact (FixedRows.collect (N:=groups s W) (s:=HalfKernel.Src cl) (t:=Ty.a (bundle cl)) (Z:=fun i => p.calls * Z i) V each).mono (fun _ => le_rfl) (fun i => by rw [Nat.mul_assoc])
end
end DFTSpeedrun.Batch
