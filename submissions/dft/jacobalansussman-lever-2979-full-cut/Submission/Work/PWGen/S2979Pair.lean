import Submission.Work.GCert.Data.S2979BGlue401
import Submission.Work.GCert.Data.S2979EGlue401

/-!
# (key: x-words) the two #2979 provider packages side by side, for the two-provider dispatch

x-words, round wht45/lever2979, 19 Oct 2026 (p-wgen's `Work/PWGen/S5Pair.lean` with the #2979 words; every name
carries 2979, namespace `PWG2979`, so it sits next to the #3945 modules in one tree).  `GXD.S2979B.ginvW` (gauge44)
and `GXD.S2979E.ginvW` (extra) are windowed packages `KLW.GInvEW (Fin 9) (Fin 112) (Fin 408) (Fin 99) okW` with the
same window condition (each word's `okW` is the same lambda) and the same target vectors (the two words have the same
112 ports, checked by the kernel).  Here both are stated over `GXD.S2979B.okW`, with `tv_eq` in the shape of
`XHostD.Prov2.mk'`'s hypothesis (`I1.tv = I0.tv` with `I0 := extra`, `I1 := gauge44`), and their prices.  No `sorry`.
-/

namespace PWG2979
open OAI.PowerSaving OAI.PowerSaving.CB

/-- provider 0: the extra word of #2979 -/
noncomputable def ginvE : KLW.GInvEW (Fin 9) (Fin 112) (Fin 408) (Fin 99) GXD.S2979B.okW := GXD.S2979E.ginvW
/-- provider 1: the gauge44 word of #2979 -/
noncomputable def ginvB : KLW.GInvEW (Fin 9) (Fin 112) (Fin 408) (Fin 99) GXD.S2979B.okW := GXD.S2979B.ginvW

theorem okW_eq : @GXD.S2979E.okW = @GXD.S2979B.okW := rfl

theorem ports_eq : GXD.S2979B.wc.ports = GXD.S2979E.wc.ports := by decide +kernel

/-- the same target vectors (`I1.tv = I0.tv` with `I0 := ginvE`, `I1 := ginvB`) -/
theorem tv_eq : ginvB.tv = ginvE.tv := by
  funext t
  show GXD.S2979B.wc.tv t = GXD.S2979E.wc.tv t
  unfold KLW.WCert.tv
  rw [ports_eq]
  try rfl

theorem ginvE_cost (φ : ℕ → ℝ) : ginvE.cost φ = GXD.S2979E.invPrice φ := GXD.S2979E.ginv_cost φ
theorem ginvB_cost (φ : ℕ → ℝ) : ginvB.cost φ = GXD.S2979B.invPrice φ := GXD.S2979B.ginv_cost φ

/-- the two words cost the same at every price list (same local profile) -/
theorem same_price (φ : ℕ → ℝ) : ginvE.cost φ = ginvB.cost φ := by
  rw [ginvE_cost, ginvB_cost]
  unfold GXD.S2979E.invPrice GXD.S2979B.invPrice
  try rfl

end PWG2979

#print axioms PWG2979.tv_eq
#print axioms PWG2979.same_price
#print axioms PWG2979.ginvE_cost
#print axioms PWG2979.ginvB_cost
