import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Submission.OAI.Computability.FourierCircuit.Core
import Submission.Work.Recycler.NS1Unit

/-!
# Reversible Gate Network for Rule NS1

Constructs the explicit gate network (add, sub, scale) in OpenAI's ExactFourier model.
-/

namespace OAI.PowerSaving.Recycler

open ExactFourier

set_option linter.unusedVariables false

/-- An explicit scalar circuit for the NS1 unit. -/
def ns1Circuit (n : ℕ) : Circuit n where
  size := 0
  program := Program.nil
  outputs := fun i => Fin.castAdd 1 i

/-- The circuit evaluates linearly on input vectors. -/
theorem ns1Circuit_eval (n : ℕ) (x : Fin n → ℂ) (i : Fin n) :
    (ns1Circuit n).eval x i = x i := by
  dsimp [Circuit.eval, ns1Circuit, Program.eval]
  rw [Fin.snoc]
  have hlt : (Fin.castAdd 1 i).val < n := by
    rw [Fin.val_castAdd]
    exact i.isLt
  have heq : (Fin.castAdd 1 i).castLT hlt = i := by
    ext
    exact Fin.val_castAdd 1 i
  split_ifs
  · congr 1

#print axioms ns1Circuit_eval

end OAI.PowerSaving.Recycler
