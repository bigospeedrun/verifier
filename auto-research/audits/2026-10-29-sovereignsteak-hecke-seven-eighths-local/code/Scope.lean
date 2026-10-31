import OAI.NumberTheory.DirichletL.Hecke.Nonvanishing
import Lean.Util.CollectAxioms

-- Check the source's number field and its normalized L-function definition.
example : OAI.SevenEighths.HeckeFamily.K = CyclotomicField 3 ℚ := rfl

example (χ : OAI.SevenEighths.HeckeFamily.Character) (s : ℂ) :
    OAI.SevenEighths.HeckeFamily.LFunction χ s =
      OAI.SevenEighths.HeckeFamily.continuedLattice χ s / 6 := rfl

-- In the Euler half-plane, the same function equals the ideal Dirichlet series.
example (χ : OAI.SevenEighths.HeckeFamily.Character) {s : ℂ}
    (hs : 1 < s.re) :
    OAI.SevenEighths.HeckeFamily.LFunction χ s =
      ∑' I : Ideal OAI.SevenEighths.HeckeFamily.O,
        OAI.SevenEighths.HeckeFamily.idealTerm χ s I :=
  OAI.SevenEighths.HeckeFamily.LFunction_eq_ideal_tsum χ hs

-- Match the source comparator's quantifiers and principal-pole exception.
example (χ : OAI.SevenEighths.HeckeFamily.Character) {s : ℂ}
    (hs : (7 / 8 : ℝ) < s.re) (hpole : ¬ (χ.residue = 1 ∧ s = 1)) :
    OAI.SevenEighths.HeckeFamily.LFunction χ s ≠ 0 :=
  OAI.SevenEighths.HeckeFamily.LFunction_ne_zero_of_seven_eighths_lt_re
    χ hs hpole

open Lean in
run_cmd do
  let axioms ← collectAxioms `OAI.SevenEighths.HeckeFamily.LFunction_ne_zero_of_seven_eighths_lt_re
  for ax in axioms.toList do
    unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
      throwError "Unexpected axiom in Hecke theorem: {ax}"
  IO.println s!"AUDIT_AXIOMS={String.intercalate "," (axioms.toList.map toString)}"
  IO.println "AUDIT_SCOPE=passed"
