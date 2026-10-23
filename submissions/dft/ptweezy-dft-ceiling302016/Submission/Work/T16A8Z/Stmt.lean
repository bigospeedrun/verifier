import Submission.Work.Scratch.Engine
import Submission.OAI.Computability.FourierTransform.TensorProgram
-- changed for the tensor-power extension (30103/10000000); see Submission.lean

/-!
# The engine statement of the instance `T16A8Z` (tensor power of the RAW p16a8z unit)

New file, not a copy of an OpenAI file.  `MX.T16A8Z.EngineStmt` is OpenAI's `hills_program` statement (lines 95-99 of
lean/OAI/Computability/FourierTransform/TensorProgram.lean of github.com/openai/math, commit fd4aeeb, Apache-2.0) as a
proposition, with the envelope `envelope z k = ⌈(k+1)^z⌉` at the seam exponent `z = 1 - 3020159999999/10^15` in the place
of `hills`, for index types `ι` in one universe.  DFT figure of the chain: `1 - 302015999999/10^14` (rate point
`1 - 4719/1562500` < seam exponent < statement exponent).

The integration supplies ONE theorem, in the module `Work.T16A8Z.Engine`:

    theorem OAI.PowerSaving.MX.T16A8Z.engine : OAI.PowerSaving.MX.T16A8Z.EngineStmt.{0}

and the seam of `Work.FourierT16A8Z` uses it through `EngineStmt.lift`, which gives every universe from universe 0 by
OpenAI's `Able.reindex` along `i ↦ ⟨k i, v i⟩ : Σ n, (Bits n → ℂ)`.
(Template: the head-cut instance's `Work/L2979_HalitZiyaV2_Hc/Stmt.lean`, numbers changed.)
-/

namespace OAI
namespace PowerSaving
namespace MX
namespace T16A8Z
open Binary Matrix Finset RAM RAM.Ty
universe u

/-- The seam's engine fact at `1 - 3020159999999/10^15`, index types in universe `w`. -/
def EngineStmt.{w} : Prop :=
  ∀ (cl : Paint) (m : Bool) {ι : Type w} (k : ι→ℕ) (v : ∀ i, Bits (k i) → ℂ),
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*envelope (1 - 3020159999999/(10:ℝ)^15) (k i))

/-- The engine fact for index types in universe 0 gives it in every universe (`Able.reindex`). -/
theorem EngineStmt.lift (h : EngineStmt.{0}) (cl : Paint) (m : Bool) {ι : Type u} (k : ι→ℕ)
    (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*envelope (1 - 3020159999999/(10:ℝ)^15) (k i)) :=
  Able.reindex (h cl m (fun j : (Σ n : ℕ, (Bits n → ℂ)) => j.1) (fun j => j.2))
    (fun i => (⟨k i, v i⟩ : Σ n : ℕ, (Bits n → ℂ)))

end T16A8Z
end MX
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.MX.T16A8Z.EngineStmt.lift
