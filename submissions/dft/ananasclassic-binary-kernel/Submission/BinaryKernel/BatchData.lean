import Submission.BinaryKernel.PlanCompiler
import Submission.BinaryKernel.KernelClosure

namespace DFTSpeedrun.Batch
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open OAI.Computability.NearSquareRoot.KernelPass
open AxisLayout ComplexPlan FixedRows
noncomputable section

def rows (s : ℕ) := 4^s
def groups (s W : ℕ) := rows s ⌈/⌉ W
theorem rows_eq (s : ℕ) : (bits (s*2)).n = rows s := by
  rw [bits_len, Nat.mul_comm, pow_mul]; rfl
def highAt {s : ℕ} (j : ℕ) : Bits (s*2) :=
  (bits (s*2)).atFin ⟨j % rows s,by rw [rows_eq]; exact Nat.mod_lt _ (by dsimp [rows]; positivity)⟩
def joined {A h k s : ℕ} (eqdim : A*(h*2)+s*2=k*2)
    (a : Addr A h) (j : Bits (s*2)) : Bits (k*2) :=
  castB eqdim (catB _ _ (allFlatten a,j))
def input {A h k s W : ℕ} (eqdim : A*(h*2)+s*2=k*2)
    (v : Bits (k*2) → ℂ) (g : ℕ) : ComplexPlan.Bank A h W :=
  fun b a => v (joined eqdim a (highAt (g*W+b.val)))
def result {A h k s W : ℕ} (eqdim : A*(h*2)+s*2=k*2)
    (v : Bits (k*2) → ℂ) (p : Plan A W W) : Tape (Tape (Tape ℂ)) :=
  fixed fun g : Fin (groups s W) => bankTape (shape A h) (act p h (input eqdim v g.val))

theorem volume_bits (A h : ℕ) : PlanCompiler.volume A h = 2^(A*(h*2)) := by
  rw [PlanCompiler.volume_eq, ← pow_mul]; congr 1; ring
theorem joined_loc {A h k s : ℕ} (eqdim : A*(h*2)+s*2=k*2)
    (a : Addr A h) (j : Bits (s*2)) :
    (bits (k*2)).loc (joined eqdim a j) =
      code a + PlanCompiler.volume A h * (bits (s*2)).loc j := by
  rw [joined, castB_loc,catB_loc,code_flat,volume_bits]

end
end DFTSpeedrun.Batch
