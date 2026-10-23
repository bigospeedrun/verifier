import Submission.Work.Fresh.Helpers
import Submission.Work.P4L.View
-- changed for the tensor-power extension (30103/10000000); see Submission.lean

/-!
# P4-L, part 10: the fresh helpers of one call

Every slot `q` of the call of stage `k` serves its own fresh helper `(g, k, q)` (P4-L-fresh).  By `FH.fresh_frames`
(one sub-stage, `use 0 q = some q`, residual `card H - dim (ent q)`, gauged residual matrix `entW`): a free adapter
before the call, the call's residual `Wn`, and ONE top-up block after it take the helper from `1` to `pk D`, `D` any
set `D q` of coordinates with `|D q| ≥` the residual rank (raw form: equal, so the end step is free).
No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace P4L
open Binary Matrix Finset RAM SS CB RF BR GF GX XHostTW FH XHostD

noncomputable section

section Fresh
variable {H T Sl C α Γ : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C] [Fintype α] [DecidableEq α]
  [Fintype Γ] [DecidableEq Γ]

/-- the fresh helpers of the call of stage `k`, all gauges. -/
def freshSet (k : Fin 9) : Finset (PRole Γ T Sl C) :=
  (Finset.univ : Finset (Γ × Sl)).image fun p => freshR p.1 k p.2

lemma mem_freshSet (k : Fin 9) (r : PRole Γ T Sl C) :
    r ∈ freshSet (Γ := Γ) (T := T) (Sl := Sl) (C := C) k ↔ ∃ g q, r = freshR g k q := by
  unfold freshSet
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨g, q⟩, -, rfl⟩; exact ⟨g, q, rfl⟩
  · rintro ⟨g, q, rfl⟩; exact ⟨(g, q), Finset.mem_univ _, rfl⟩

lemma mainR_not_fresh (k : Fin 9) (g : Γ) (i : R8) (t : T) :
    mainR (Sl := Sl) (C := C) g i t ∉ freshSet (Γ := Γ) (T := T) (Sl := Sl) (C := C) k := by
  rw [mem_freshSet]
  rintro ⟨g', q, h⟩
  cases h

/-- **the frames of the fresh helpers of one call** (`FH.fresh_frames`, one sub-stage), as matrices on each helper:
an adapter `Zp` from `1`, the residual `Wn`, an end step from `Wn * Zp` to `pk (D q)` of rank `|D q| - r q` (FREE in the
raw form `|D q| = r q`; the separated form pads to `|D| = 9` afterwards). -/
theorem fresh_call (Wn : Γ → Sl → CMat α) (r : Sl → ℕ)
    (hWn : ∀ d q, ∃ (C C' : CMat α) (R : Finset α), Free C ∧ Free C' ∧ R.card = r q ∧ Wn d q = C * pk R * C')
    (D : Sl → Finset α) (hload : ∀ q, r q ≤ (D q).card) (hrk : ∀ q, (D q).card - r q < Fintype.card α) :
    ∃ Zp : Γ → Sl → CMat α,
      (∀ d q, GReach 1 (Zp d q) (fun _ => 0)) ∧
      (∀ d q, GReach (Wn d q * Zp d q) (pk (D q)) (fun φ => bcost φ ((D q).card - r q))) := by
  have hinj : ∀ k < 1, OneUseK (fun (_ : ℕ) (q : Sl) => (some q : Option Sl)) k := by
    intro k _ q q' j h h'
    simp only [Option.some.injEq] at h h'
    exact h.trans h'.symm
  have hLH : ∀ q, LHK (fun (_ : ℕ) (q : Sl) => (some q : Option Sl)) (fun _ q => r q) 1 q = r q := by
    intro q
    simp [LHK, rrHK, Finset.filter_eq']
  obtain ⟨Zb, Zp, h0, hP, hU, hN, hE⟩ := fresh_frames (Γ := Γ) (fun _ q => some q) (fun _ q => r q)
    (fun _ d q => Wn d q) 1 hinj (fun _ _ d q => hWn d q) D
    (fun q => by rw [hLH]; exact hload q) (fun q => by rw [hLH]; exact hrk q)
  refine ⟨Zp 0, fun d q => ?_, fun d q => ?_⟩
  · have h := hP 0 Nat.one_pos d q
    rw [h0] at h
    exact h
  · have h1 := hU 0 Nat.one_pos d q q rfl
    have h2 := hE d q
    rw [hLH, ← h1] at h2
    exact h2

end Fresh

end
end P4L
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.P4L.fresh_call
