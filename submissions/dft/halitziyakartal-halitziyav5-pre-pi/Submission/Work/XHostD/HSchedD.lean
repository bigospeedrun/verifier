import Submission.Work.XHostR.HSchedR
import Submission.Work.Bridge401.Sched
import Submission.Work.XHostD.Prov

/-!
# XHostD.HSchedD: the residual conditions of a per-run host schedule with PER-CALL residuals

fsp-perrun's `HostSchedR.fitsR` takes ONE residual per slot (`r : Sl → ℕ`, from the single invocation's entrance labels).
With two provider words the residual of slot `q` depends on the call: `r k q` in sub-stage `k = 9 ρ + l`, here
`D.resK dispK k q = |H| - dim ((D.P (dispK k)).ent q)`.  `fitsRK` is `fitsR` with `LHK` (FramesK) for `LH`: banks see
the residual of the call they serve, and the host chain of kind `c` in run `ρ` sees the calls `9 ρ + kz c + k`.
`fitsRK_const`: a constant residual is exactly fsp-perrun's condition, so every table checked today stays valid.
`hWnD`: every per-call climb `entW X ((D.P (dispK k)).ent q)` has the host form `host_framesK` needs, with rank
`D.resK dispK k q` (Mamano / Shea's `entW_form`).  Written by lg-a2a4 (wht43, 14 Oct 2026); prepared with assistance
from Claude.  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace XHostD
open Binary Matrix Finset GF CB B401 GX XHost XHostR
noncomputable section

section Fits
variable {Sl T : Type} [Fintype Sl] [DecidableEq Sl] [DecidableEq T]

/-- **The residual conditions with per-call residuals** `r k q` (`k = 9 ρ + l`). -/
def fitsRK (S : HostSchedR Sl T) (r : ℕ → Sl → ℕ) : Prop :=
  (∀ b, LHK (bUseR S.hostAt S.bk) r 72 b + S.pad b = 73) ∧
  (∀ b, S.pad b < 73) ∧
  (∀ ρ c j, LHK (hUse (S.hostAt ρ) c (kz c)) (fun k q => r (9 * ρ.val + kz c + k) q) (kK c) j
      + S.hrem ρ c j = rankOf c.val)

/-- a constant residual: fsp-perrun's `fitsR`, unchanged. -/
theorem fitsRK_const (S : HostSchedR Sl T) (r : Sl → ℕ) : fitsRK S (fun _ => r) ↔ S.fitsR r := Iff.rfl

end Fits

section Climb
variable {ι H T Sl C α Γ : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C] [Fintype α] [DecidableEq α]

/-- the per-call climbs have host form, with the call's own residual. -/
lemma hWnD (D : ProvF ι H T Sl C) (dispK : ℕ → ι) (X : ℕ → Γ → BXMap H α) :
    ∀ k, ∀ d q, ∃ (C C' : CMat α) (R : Finset α), Free C ∧ Free C' ∧ R.card = D.resK dispK k q ∧
      entW (X k d) ((D.P (dispK k)).ent q) = C * pk R * C' :=
  fun k d q => entW_form (X k d) ((D.P (dispK k)).ent q)

/-- with the dispatched invocation `D.call`: its entrance labels are the provider's. -/
lemma call_entW (D : ProvF ι H T Sl C) {κ : Type} (disp : κ → ι) (c : κ) (X : BXMap H α) (q : Sl) :
    entW X ((D.call disp c).ent q) = entW X ((D.P (disp c)).ent q) := rfl

end Climb
end
end XHostD
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.XHostD.fitsRK_const
#print axioms OAI.PowerSaving.XHostD.hWnD
