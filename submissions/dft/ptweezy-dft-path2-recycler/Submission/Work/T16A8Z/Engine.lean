import Submission.Work.T16A8Z.RawCert
import Submission.Work.T16A8Z.TensorG
-- changed for the tensor-power extension (30103/10000000); see Submission.lean

/-!
# THE engine theorem of the instance T16A8Z (Route E: tensor power of the RAW p16a8z unit)

`MX.T16A8Z.engine : MX.T16A8Z.EngineStmt.{0}`: OpenAI's `hills_program` statement at the seam exponent
`1 - 3020159999999/10^15` (DFT figure 3.0201599e-3), from the RAW p16a8z certificate with `G` copies (`PB.T16A8Z.RawCert16Z`,
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
