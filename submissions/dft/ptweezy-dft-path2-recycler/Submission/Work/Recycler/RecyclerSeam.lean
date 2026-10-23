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

/-- Explicit work allowance under Path 2: Nat.ceil of recyclerTimeNS1. -/
def recyclerWork (n : ℕ) : ℕ :=
  if n = 0 then 0 else Nat.ceil (recyclerTimeNS1 n)

lemma recyclerTime_pos {n : ℕ} (hn : 2 ≤ n) : 0 < recyclerTimeNS1 n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  exact mul_pos hn' (Real.rpow_pos_of_pos hlog _)

/-- The Path 2 work allowance is strictly O(n (log n)^(1 - 82009/500000)). -/
theorem recyclerWork_isBigO :
    (fun n : ℕ => (recyclerWork n : ℝ)) =O[atTop] recyclerTimeNS1 := by
  refine isBigO_iff.mpr ⟨2, ?_⟩
  filter_upwards [eventually_ge_atTop 3] with n hn
  have hpos : 0 < recyclerTimeNS1 n := recyclerTime_pos (by omega)
  have hne : ¬ (n = 0) := by omega
  dsimp [recyclerWork]
  rw [if_neg hne]
  have hceil : (Nat.ceil (recyclerTimeNS1 n) : ℝ) ≤ recyclerTimeNS1 n + 1 := (Nat.ceil_lt_add_one hpos.le).le
  have hlog : 1 ≤ Real.log (n : ℝ) := by
    have he : Real.exp 1 ≤ (3 : ℝ) := by
      have := Real.exp_one_lt_d9
      linarith
    have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (he.trans hn3)
  have h1_le : 1 ≤ recyclerTimeNS1 n := by
    dsimp [recyclerTimeNS1]
    have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    have hrpow : 1 ≤ (Real.log (n : ℝ)) ^ recyclerExponentNS1 := by
      have hexp_pos : 0 ≤ recyclerExponentNS1 := by
        dsimp [recyclerExponentNS1, recyclerSavingNS1]
        norm_num
      exact Real.one_le_rpow hlog hexp_pos
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (n : ℝ) * (Real.log (n : ℝ)) ^ recyclerExponentNS1 := mul_le_mul hn1 hrpow zero_le_one (by positivity)
  have hceil_pos : 0 ≤ (Nat.ceil (recyclerTimeNS1 n) : ℝ) := by positivity
  rw [abs_of_nonneg hceil_pos, abs_of_pos hpos]
  linarith

#print axioms recyclerWork_isBigO

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
