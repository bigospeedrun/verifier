import OAI.NumberTheory.DirichletL.Nonvanishing
import Lean.Util.CollectAxioms

open scoped _root_.DirichletCharacter

-- Match the source comparator: all positive moduli, all characters, and the
-- sole excluded principal-character pole at s = 1.
example {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (7 / 8 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re χ hs hpole

open Lean in
run_cmd do
  let axioms ← collectAxioms `OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re
  for ax in axioms.toList do
    unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
      throwError "Unexpected axiom in Dirichlet theorem: {ax}"
  IO.println s!"AUDIT_AXIOMS={String.intercalate "," (axioms.toList.map toString)}"
  IO.println "AUDIT_SCOPE=passed"
