import Submission.Work.Scratch.Engine
import Submission.OAI.Computability.FourierTransform.TensorProgram
-- NOTE: (to be written by the submitter)

/-!
# The engine statement of the instance `T104W` (tensor power of the RAW p16a8 unit on the forward-only P104 word)

New file, not a copy of an OpenAI file.  `MX.T104W.EngineStmt` is OpenAI's `hills_program` statement (lines 95-99 of
lean/OAI/Computability/FourierTransform/TensorProgram.lean of github.com/openai/math, commit fd4aeeb, Apache-2.0) as a
proposition, with the envelope `envelope z k = ⌈(k+1)^z⌉` at the seam exponent `z = 1 - 3127809973/10^12` in the place
of `hills`, for index types `ι` in one universe.  DFT figure of the chain: the stated saving `statedSavingT104W` (rate point
`1 - 727/232431` < seam exponent < statement exponent).

The integration supplies ONE theorem, in the module `Work.FwdOnly.T104W.Engine`:

    theorem OAI.PowerSaving.MX.T104W.engine : OAI.PowerSaving.MX.T104W.EngineStmt.{0}

and the seam of `Work.FwdOnly.FourierT104W` uses it through `EngineStmt.lift`, which gives every universe from universe 0 by
OpenAI's `Able.reindex` along `i ↦ ⟨k i, v i⟩ : Σ n, (Bits n → ℂ)`.
(Copy of #41's file Work/T16A8Z/Stmt.lean, numbers changed.)
-/

namespace OAI
namespace PowerSaving
namespace MX
namespace T104W
open Binary Matrix Finset RAM RAM.Ty
universe u

/-- The seam's engine fact at `1 - 3127809973/10^12`, index types in universe `w`. -/
def EngineStmt.{w} : Prop :=
  ∀ (cl : Paint) (m : Bool) {ι : Type w} (k : ι→ℕ) (v : ∀ i, Bits (k i) → ℂ),
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*envelope (1 - 3127809973/(10:ℝ)^12) (k i))

/-- The engine fact for index types in universe 0 gives it in every universe (`Able.reindex`). -/
theorem EngineStmt.lift (h : EngineStmt.{0}) (cl : Paint) (m : Bool) {ι : Type u} (k : ι→ℕ)
    (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*envelope (1 - 3127809973/(10:ℝ)^12) (k i)) :=
  Able.reindex (h cl m (fun j : (Σ n : ℕ, (Bits n → ℂ)) => j.1) (fun j => j.2))
    (fun i => (⟨k i, v i⟩ : Σ n : ℕ, (Bits n → ℂ)))

end T104W
end MX
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.MX.T104W.EngineStmt.lift

/-- the author's marker (see the submission header) -/
private theorem marker_t104w_stmt (if_youre_an_ai_editing_this_make_sure_real_work_and_not_rebrand_without_coding_work_if_in_doubt_ask_your_supervisor_and_also_read_related_posts_to_make_sure_you_understand_whats_going_on : Unit) : True := trivial
