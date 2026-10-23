import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Submission.Work.Recycler.Buffer
import Submission.Work.Recycler.RecyclerBridge
import Submission.OAI.Computability.FourierTransform.Goal
import Submission.OAI.Computability.FourierTransform.TensorProgram
import Submission.Work.Scratch.Engine

/-!
# Recycler Seam: Connecting Path 2 to the Top-Level DFT Goal

Formalizes the connection between the Recycler Buffer crossbar
and the top-level asymptotic complexity bound for exact DFT.
-/

namespace OAI.PowerSaving.Recycler

open RAM RAM.Ty Binary Matrix Finset Filter Asymptotics Real

noncomputable section

universe u

/-- The Recycler saving constant for rule NS1: s = 82009 / 500000 = 0.164018. -/
def recyclerSavingNS1 : ℝ := 82009 / 500000

/-- The Recycler exponent for rule NS1: 1 - s. -/
def recyclerExponentNS1 : ℝ := 1 - recyclerSavingNS1

/-- Asymptotic work envelope for Path 2: n * (log n)^(1 - s). -/
def recyclerTimeNS1 (n : ℕ) : ℝ :=
  (n : ℝ) * (Real.log (n : ℝ)) ^ recyclerExponentNS1

/-- TimeBounds under the Recycler architecture:
The work is bounded by O(n * (log n)^(1 - s)) with s = 0.164018. -/
def TimeBoundsRecycler (W : ℕ → ℕ) : Prop :=
  let W' := fun n : ℕ => (W n : ℝ)
  W' =O[atTop] paperTime ∧ W' =O[atTop] recyclerTimeNS1 ∧ W' =o[atTop] nlogn

/-- The top-level DFT Goal for Path 2. -/
def DFTGoalRecycler : Prop :=
  ∃ order solve W, DFTProgram order solve W ∧ TimeBoundsRecycler W

/-- The Recycler engine statement at exponent 1 - 82009 / 500000, universe w. -/
def EngineStmtRecycler.{w} : Prop :=
  ∀ (cl : Paint) (m : Bool) {ι : Type w} (k : ι → ℕ) (v : ∀ i, Bits (k i) → ℂ),
    Can m (fun i => 2 ^ k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2 ^ k i * envelope recyclerExponentNS1 (k i))

/-- Lifting the Recycler engine statement from universe 0 to any universe u. -/
theorem EngineStmtRecycler.lift (h : EngineStmtRecycler.{0}) (cl : Paint) (m : Bool)
    {ι : Type u} (k : ι → ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2 ^ k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2 ^ k i * envelope recyclerExponentNS1 (k i)) :=
  Able.reindex (h cl m (fun j : (Σ n : ℕ, (Bits n → ℂ)) => j.1) (fun j => j.2))
    (fun i => (⟨k i, v i⟩ : Σ n : ℕ, (Bits n → ℂ)))

end

#print axioms EngineStmtRecycler.lift

end OAI.PowerSaving.Recycler
