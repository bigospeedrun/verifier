import Submission.Work.GCert.Data.S2979ZGlue401
-- changed for the tensor-power extension (30103/10000000); see Submission.lean

/-! The #4470 patched #2979 word as the provider of the p16a8 unit (Route E): `ginvZ`, a windowed package
`KLW.GInvEW (Fin 9) (Fin 112) (Fin 408) (Fin 8) okW`, and its price.  No `sorry`. -/

namespace PWGZ
open OAI.PowerSaving OAI.PowerSaving.CB

/-- the provider: the #4470 patched #2979 word -/
noncomputable def ginvZ : KLW.GInvEW (Fin 9) (Fin 112) (Fin 408) (Fin 8) GXD.S2979Z.okW := GXD.S2979Z.ginvW

/-- its price: the kernel counts of `Gen.S2979ZHist` -/
theorem ginvZ_cost (φ : ℕ → ℝ) : ginvZ.cost φ = GXD.S2979Z.invPrice φ := GXD.S2979Z.ginv_cost φ

end PWGZ
#print axioms PWGZ.ginvZ_cost
