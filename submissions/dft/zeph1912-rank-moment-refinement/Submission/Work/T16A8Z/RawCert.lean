/- Modified 2026-10-30: numerical rate refinement of Kartal PR #41.
New certified rate 0.00302016595, tensor power 11640, final saving 0.0030201659.
Original circuit, proof framework and authorship are retained. See README.md.
In Submission.lean, the original headers below are historical provenance:
their constants describe earlier results, not this refinement.
-/
import Submission.Work.T16A8Z.Hole
import Submission.Work.P16A8.RawZ
-- changed for the tensor-power extension (30201659/10000000000); see Submission.lean

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
