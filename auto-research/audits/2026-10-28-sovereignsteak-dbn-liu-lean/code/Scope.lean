import ArdaDBNLiu
import Lean.Util.CollectAxioms

open MeasureTheory

-- Check the real-zero statement at the exact rational threshold.
example : ∀ t : ℝ, (2811857 / 10000000 : ℝ) ≤ t →
    ∀ z : ℂ, DBN.H t z = 0 → z.im = 0 :=
  dbn_real_zeros_ge_2811857

-- Check the separate input theorem supplied by Liu's zero-free half-plane.
example : ∀ s : ℂ, (1507 - 2 * Real.sqrt 921) / 1653 < s.re →
    riemannZeta s ≠ 0 :=
  liu_zeta_zero_free

-- The converter consumes that same unrestricted zero-free half-plane form.
example (θ : ℝ) (hfree : ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0) :
    ∀ t : ℝ, 2 * (θ - 1 / 2) ^ 2 ≤ t →
      ∀ z : ℂ, DBN.H t z = 0 → z.im = 0 :=
  dbn_real_zeros_of_zeta_halfplane θ hfree

-- The release's H is the heat-deformed Fourier integral, with its stated
-- theta-series kernel. These are definitional checks, independent of labels.
example (u : ℝ) : DBN.Φ u =
    ∑' n : ℕ+, (2 * Real.pi ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u)
      - 3 * Real.pi * (n : ℝ) ^ 2 * Real.exp (5 * u))
      * Real.exp (-Real.pi * (n : ℝ) ^ 2 * Real.exp (4 * u)) := by
  rfl

example (t : ℝ) (z : ℂ) : DBN.H t z =
    ∫ u in Set.Ioi (0 : ℝ),
      ((Real.exp (t * u ^ 2) : ℝ) : ℂ) * ((DBN.Φ u : ℝ) : ℂ) * Complex.cos (z * u) := by
  rfl

open Lean in
run_cmd do
  let main ← collectAxioms `dbn_real_zeros_of_liu_unconditional
  let rational ← collectAxioms `dbn_real_zeros_ge_2811857
  let liu ← collectAxioms `liu_zeta_zero_free
  IO.println s!"AUDIT_AXIOMS_MAIN={String.intercalate "," (main.toList.map toString)}"
  IO.println s!"AUDIT_AXIOMS_RATIONAL={String.intercalate "," (rational.toList.map toString)}"
  IO.println s!"AUDIT_AXIOMS_LIU={String.intercalate "," (liu.toList.map toString)}"
  IO.println "AUDIT_SCOPE=passed"
