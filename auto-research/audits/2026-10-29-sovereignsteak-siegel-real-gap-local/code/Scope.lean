import OAI.NumberTheory.SiegelZeros.Conclusions.Theorem
import OAI.NumberTheory.SiegelZeros.Characters.DirichletRealZeroBoundProof
import Lean.Util.CollectAxioms

-- One positive constant works for every modulus, every primitive nonprincipal
-- real-valued character, and every real zero in (0, 1). No parity restriction.
example :
    ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ χ : DirichletCharacter ℂ q,
        χ.IsPrimitive → χ ≠ 1 → (∀ a : ZMod q, (χ a).im = 0) →
        ∀ β : ℝ, 0 < β → β < 1 → χ.LFunction (β : ℂ) = 0 →
          c ≤ (1 - β) * Real.log (q : ℝ) :=
  OAI.SiegelZeros.WeightedTorusJets.exists_absolute_real_zero_gap

-- The source also exports the comparator's conjunctive premise form.
example :
    ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ χ : DirichletCharacter ℂ q,
        χ.IsPrimitive → χ ≠ 1 → (∀ a : ZMod q, (χ a).im = 0) →
        ∀ β : ℝ,
          (0 < β ∧ β < 1 ∧ DirichletCharacter.LFunction χ (β : ℂ) = 0) →
            c ≤ (1 - β) * Real.log (q : ℝ) :=
  OAI.SiegelZeros.WeightedTorusJets.dirichletRealZeroBound_proof

open Lean in
run_cmd do
  for name in [`OAI.SiegelZeros.WeightedTorusJets.exists_absolute_real_zero_gap,
      `OAI.SiegelZeros.WeightedTorusJets.dirichletRealZeroBound_proof] do
    let axioms ← collectAxioms name
    for ax in axioms.toList do
      unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
        throwError "Unexpected axiom in {name}: {ax}"
    IO.println s!"AUDIT_AXIOMS_{name}={String.intercalate "," (axioms.toList.map toString)}"
  IO.println "AUDIT_SCOPE=passed"
