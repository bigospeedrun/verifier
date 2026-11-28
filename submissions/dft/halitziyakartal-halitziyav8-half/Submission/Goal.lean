/-
OpenAI's FourierTransform/Goal.lean, reduced to what the challenge statement reaches.

This file holds exactly the Goal-layer declarations that the type of `Race.bound` reaches:
`OAI.ExactFourier.zeta` (moved here from FourierCircuit/Core.lean, whose other declarations were
unreached and are deleted together with that file), `root`, `Vec`, `dft`, `dftInKind`, `dftOutKind`
and `DFTProgram`, each with its full name and term unchanged (reached declarations may move between files but keep both). The unreached declarations
that this tree's other theorems use (`conv`, `ConvProgram`, `convInKind`, `convOutKind`, `paperM`,
`paperW`, `paperDelta`, `paperMultiplier`, `theta`, `paperTime`, `nlogn`) moved unchanged, under
the same full names, to the top of DFTPrograms.lean; `TimeBounds`, `DFTGoal`, `ConvGoal`,
`decimalExponent`, `decimalTime` and `dftMatrix` are deleted (unreached declarations may be deleted).
The import is the smallest Mathlib module giving `Real.pi`, `Complex.exp` and finite sums.
-/
import Submission.RAM
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace OAI

namespace ExactFourier
noncomputable def zeta (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / (n : ℂ))
end ExactFourier

/-! Main proof targets. -/
namespace PowerSaving
noncomputable section
open RAM RAM.Ty

/-- Positive-sign, canonical roots. Need only at positive order. -/
abbrev root := ExactFourier.zeta

abbrev Vec (n : ℕ) := Fin n → ℂ

def dft (n : ℕ) (x : Vec n) : Vec n :=
  fun j => ∑ k, (root n) ^ (j.val*k.val) * x k

abbrev dftInKind := p w (p sc (a (c Paint.left)))
abbrev dftOutKind := a (c Paint.left)

/-- Include an integer and address bound polynomial in n. Constants inside this bound are
  immaterial (a constant number of logarithmic sized words is allowed). W n is the work
  allowance, including the order program, one root primitive and the transform program.
  The order program takes only the length, so its result specifies the root explicitly. -/
def DFTProgram (order : Prog false w w) (solve : Prog false dftInKind dftOutKind)
    (W : ℕ → ℕ) : Prop :=
  ∃ cBound : ℕ, ∀ n : ℕ, 0<n →
    let cap := (n+2)^cBound
    let d := run order n
    W n + 10*(n+2) ≤ cap ∧ d.peak ≤ cap ∧ d.valid ∧
    0 < d.val ∧ d.val < 1024*n^3 ∧ d.val ≤ cap ∧
    ∀ x : Vec n,
      let result := run solve (n, root d.val, (⟨n,x⟩ : Tape ℂ))
      result.valid ∧ result.peak ≤ cap ∧ d.work+1+result.work ≤ W n ∧
      result.val = (⟨n, dft n x⟩ : Tape ℂ)

end
end PowerSaving

end OAI
