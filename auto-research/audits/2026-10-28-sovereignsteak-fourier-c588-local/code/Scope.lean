import Work.FourierC588.Main
import Lean.Util.CollectAxioms

example : OAI.PowerSaving.decimalExponentC588 =
    1 - (12331685 : ℝ) / (10 ^ (10 : ℕ)) := rfl

example : OAI.PowerSaving.DFTGoalC588 :=
  OAI.PowerSaving.transform_mainC588

example : OAI.PowerSaving.ConvGoalC588 :=
  OAI.PowerSaving.convolution_mainC588

open Lean in
run_cmd do
  for name in [`OAI.PowerSaving.transform_mainC588,
      `OAI.PowerSaving.convolution_mainC588,
      `OAI.PowerSaving.RAM.hillsC588_program] do
    let axioms ← collectAxioms name
    for ax in axioms.toList do
      unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
        throwError "Unexpected axiom in {name}: {ax}"
    IO.println s!"AUDIT_AXIOMS_{name}={String.intercalate "," (axioms.toList.map toString)}"
  IO.println "AUDIT_SCOPE=passed"
