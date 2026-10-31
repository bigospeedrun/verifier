import OAI.NumberTheory.DirichletL.Nonvanishing
import Lean.Util.CollectAxioms

example {s : ℂ} (hs : (7 / 8 : ℝ) < s.re) :
    _root_.riemannZeta s ≠ 0 :=
  OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re hs

open Lean in
run_cmd do
  let axioms ← collectAxioms `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re
  for ax in axioms.toList do
    unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
      throwError "Unexpected axiom in zeta theorem: {ax}"
  IO.println s!"AUDIT_AXIOMS={String.intercalate "," (axioms.toList.map toString)}"
  IO.println "AUDIT_SCOPE=passed"
