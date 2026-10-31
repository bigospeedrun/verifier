/- Modified 2026-10-30: numerical rate refinement of Kartal PR #41.
New certified rate 0.00302016595, tensor power 11640, final saving 0.0030201659.
Original circuit, proof framework and authorship are retained. See README.md.
In Submission.lean, the original headers below are historical provenance:
their constants describe earlier results, not this refinement.
-/
import Submission.Work.T16A8Z.RawCert
import Submission.Work.T16A8Z.TensorG
-- changed for the tensor-power extension (30201659/10000000000); see Submission.lean

/-!
# THE engine theorem of the instance T16A8Z (Route E: tensor power of the RAW p16a8z unit)

`MX.T16A8Z.engine : MX.T16A8Z.EngineStmt.{0}`: OpenAI's `hills_program` statement at the seam exponent
`1 - 3020165925/10^12` (DFT figure 0.0030201659), from the RAW p16a8z certificate with `G` copies (`PB.T16A8Z.RawCert16Z`,
which exists by `PB.T16A8Z.rawCert16Z_ex`) and the tensor engine `PB.T16A8Z.tensorEngine16Z`.
-/

namespace OAI
namespace PowerSaving
namespace MX
namespace T16A8Z

/-- **THE ENGINE THEOREM OF T16A8Z.** -/
theorem engine : EngineStmt.{0} := by
  obtain ⟨α, ρ, σ, i1, i2, i3, i4, i5, i6, hc⟩ := PB.T16A8Z.rawCert16Z_ex
  exact @PB.T16A8Z.tensorEngine16Z α ρ σ i1 i2 i3 i4 i5 i6 hc

end T16A8Z
end MX
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.MX.T16A8Z.engine
