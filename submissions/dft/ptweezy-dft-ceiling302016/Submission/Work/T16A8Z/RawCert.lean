import Submission.Work.T16A8Z.Hole
import Submission.Work.P16A8.RawZ
-- changed for the tensor-power extension (30103/10000000); see Submission.lean

/-!
# Route E: the RAW p16a8z certificate exists

The p16a8z builder's `OAI.PowerSaving.P16A8.Z.rawCert_exists` (Submission/Work/P16A8/RawZ.lean) is `PB.T16A8Z.RawCert16Z` with
the two lists named `P16A8.Z.Traw` (= `rawTgt16Z`) and `P16A8.Z.Praw` (= `rawPaid16Z`), the same literals.
-/

namespace OAI
namespace PowerSaving
namespace PB
namespace T16A8Z

lemma rawTgt16Z_eq_Traw : rawTgt16Z = P16A8.Z.Traw := rfl
lemma rawPaid16Z_eq_Praw : rawPaid16Z = P16A8.Z.Praw := rfl

/-- **The RAW p16a8z certificate with `G` copies exists.** -/
theorem rawCert16Z_ex : ∃ (α ρ σ : Type) (_ : Fintype α) (_ : DecidableEq α) (_ : Fintype ρ) (_ : DecidableEq ρ)
    (_ : Fintype σ) (_ : DecidableEq σ), RawCert16Z α ρ σ := by
  obtain ⟨α, ρ, σ, i1, i2, i3, i4, i5, i6, e, tr, tz, wd, G, he, hind, hP, hw, hG, hα, htr, hcnt, hhist⟩ :=
    P16A8.Z.rawCert_exists
  refine ⟨α, ρ, σ, i1, i2, i3, i4, i5, i6, ?_⟩
  unfold RawCert16Z
  refine ⟨e, tr, tz, wd, G, he, hind, hP, hw, hG, hα, htr, fun r => ?_, fun r => ?_⟩
  · rw [rawTgt16Z_eq_Traw]; exact hcnt r
  · rw [rawPaid16Z_eq_Praw]; exact hhist r

end T16A8Z
end PB
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.PB.T16A8Z.rawCert16Z_ex
