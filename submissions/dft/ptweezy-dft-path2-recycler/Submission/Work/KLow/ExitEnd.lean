import Submission.XExit.Halves

/-!
# (key: k-lower) Exit helpers need NO tail gate when the hub's tail is part of phase B

k-lower, 13 Oct 2026.  Lower the hub's tail (the early cleanup of the exit helpers, run at their exit frames) as the
last gates of phase B.  Then Shea's end gate `g8 Mti` ("slots := rows of the inverse") never joins an exit helper to
another role, provided the total matrix `Mt` of the extended main phase satisfies two FINITE conditions:

* `ExitRows E Mt`  every exit row of `Mt` is zero off the diagonal (the word restores the exit helper up to a unit);
* `ExitCols E Mt`  every exit column of `Mt` is zero at every other SLOT row (x rows: automatic, y rows: free).

`exit_hGr` / `exit_hHr` are exactly the rest-gate fields `hGr` / `hHr` of x-exit-lean's `GLabX` for
`Gr = g8 Mti`, `Hr = (h8 Mt)ᵀ` (with `Gt = Ht = 1`, tail labels = the labels after phase B).
Credits: the end gates `g8`, `h8` and the dirt rule are Jacob Sussman's (wht-power-saving-lean, Apache-2.0);
`GScal` is DFT Bridge3's / Nil Mamano's (Ryan Shea's lean/complex588); `restOk`, `GLabX` are x-exit-lean's; the tail
and the exit frames are the hub's (#591/#593/#599, Kothe's #799 lineage).  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace XEX
open Binary Matrix Finset RAM SS CB BR CR GF RF GX B401
noncomputable section

section ExitEnd
variable {T Sl : Type} [Fintype T] [DecidableEq T] [Fintype Sl] [DecidableEq Sl]

/-- every exit row of `M` is zero off the diagonal -/
def ExitRows (E : Finset Sl) (M : Matrix (L3 T Sl) (L3 T Sl) ℚ) : Prop :=
  ∀ e ∈ E, ∀ j, j ≠ lS e → M (lS e) j = 0

/-- every exit column of `M` is zero at every other slot row -/
def ExitCols (E : Finset Sl) (M : Matrix (L3 T Sl) (L3 T Sl) ℚ) : Prop :=
  ∀ e ∈ E, ∀ q, q ≠ e → M (lS q) (lS e) = 0

/-- off the diagonal, `g8` / `h8` keep the slot rows of their argument and nothing else -/
lemma g8_off (M : Matrix (L3 T Sl) (L3 T Sl) ℚ) {i j : L3 T Sl} (e : i ≠ j) :
    g8 M i j = (1 - iX i - iY i) * M i j := by
  simp only [g8, PX, PY, Matrix.add_apply, Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply,
    Matrix.diagonal_mul, Matrix.diagonal_apply_ne _ e]
  ring

lemma h8_off (M : Matrix (L3 T Sl) (L3 T Sl) ℚ) {i j : L3 T Sl} (e : i ≠ j) :
    h8 M i j = (1 - iX i - iY i) * M i j := by
  simp only [h8, PX, PY, Matrix.add_apply, Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply,
    Matrix.diagonal_mul, Matrix.diagonal_apply_ne _ e]
  ring

lemma slot_row {i : L3 T Sl} (hx : iX i = 0) (hy : iY i = 0) : ∃ q, i = lS q := by
  rcases i with ((t|t)|q)
  · simp [iX] at hx
  · simp [iY] at hy
  · exact ⟨q, rfl⟩

variable {E : Finset Sl} {M Mi : Matrix (L3 T Sl) (L3 T Sl) ℚ}

/-- an exit row of `M` restored up to a unit: the diagonal entry is a unit and the row of the inverse is zero off
the diagonal. -/
lemma exit_row_inv (hmi : M * Mi = 1) (hR : ExitRows E M) {e : Sl} (he : e ∈ E) :
    M (lS e) (lS e) ≠ 0 ∧ ∀ j, j ≠ lS e → Mi (lS e) j = 0 := by
  have key : ∀ j, (M * Mi) (lS e) j = M (lS e) (lS e) * Mi (lS e) j := by
    intro j
    rw [Matrix.mul_apply, Finset.sum_eq_single (lS e)]
    · intro k _ hk; rw [hR e he k hk, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have h1 : M (lS e) (lS e) * Mi (lS e) (lS e) = 1 := by
    rw [← key, hmi, Matrix.one_apply_eq]
  have hne : M (lS e) (lS e) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at h1; exact zero_ne_one h1
  refine ⟨hne, fun j hj => ?_⟩
  have h2 : M (lS e) (lS e) * Mi (lS e) j = 0 := by
    rw [← key, hmi, Matrix.one_apply_ne (Ne.symm hj)]
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd h hne
  · exact h

/-- an exit column of the inverse is zero at every other slot row. -/
lemma exit_col_inv (him : Mi * M = 1) (hmi : M * Mi = 1) (hR : ExitRows E M) (hC : ExitCols E M)
    (hx : ∀ (t : T) j, M (lX t) j = if lX t = j then 1 else 0) (hiy : Mi * PY = PY)
    {e : Sl} (he : e ∈ E) {q : Sl} (hq : q ≠ e) : Mi (lS q) (lS e) = 0 := by
  have hne := (exit_row_inv hmi hR he).1
  have key : (Mi * M) (lS q) (lS e) = Mi (lS q) (lS e) * M (lS e) (lS e) := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (lS e)]
    · intro k _ hk
      rcases k with ((t|t)|q')
      · have : M (lX t) (lS e) = 0 := by rw [hx t]; simp
        rw [this, mul_zero]
      · rw [col_y_zero hiy q t, zero_mul]
      · have hq' : q' ≠ e := fun h => hk (by rw [h])
        rw [hC e he q' hq', mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have h0 : (Mi * M) (lS q) (lS e) = 0 := by
    rw [him, Matrix.one_apply_ne]
    intro h; exact hq (by cases h; rfl)
  rw [key] at h0
  rcases mul_eq_zero.mp h0 with h | h
  · exact h
  · exact absurd h hne

lemma iE_lS (q : Sl) : iE E (lS q : L3 T Sl) = if q ∈ E then 1 else 0 := rfl

/-- **The forward rest gate `g8 Mti` touches neither y roles nor exit slots.** -/
theorem exit_hGr (him : Mi * M = 1) (hmi : M * Mi = 1) (hR : ExitRows E M) (hC : ExitCols E M)
    (hx : ∀ (t : T) j, M (lX t) j = if lX t = j then 1 else 0) (hiy : Mi * PY = PY) :
    ∀ i j, i ≠ j → g8 Mi i j ≠ 0 → restOk E i ∧ restOk E j := by
  intro i j e h
  have f := g8_facts hiy
  obtain ⟨hix, hiy', hjy⟩ := offdiag_s f.1 f.2.1 f.2.2 h e
  obtain ⟨q, rfl⟩ := slot_row hix hiy'
  rw [g8_off _ e, hix, hiy', sub_zero, sub_zero, one_mul] at h
  refine ⟨⟨hiy', ?_⟩, ⟨hjy, ?_⟩⟩
  · rw [iE_lS]
    by_cases hq : q ∈ E
    · exact absurd ((exit_row_inv hmi hR hq).2 j (Ne.symm e)) h
    · rw [if_neg hq]
  · rcases j with ((t|t)|e')
    · simp [iE]
    · simp [iY] at hjy
    · rw [iE_lS]
      by_cases he' : e' ∈ E
      · have hqe : q ≠ e' := fun h' => e (by rw [h'])
        exact absurd (exit_col_inv him hmi hR hC hx hiy he' hqe) h
      · rw [if_neg he']

/-- **The backward rest gate `(h8 Mt)ᵀ` touches neither y roles nor exit slots.** -/
theorem exit_hHr (hmy : M * PY = PY) (hR : ExitRows E M) (hC : ExitCols E M) :
    ∀ i j, i ≠ j → (h8 M)ᵀ i j ≠ 0 → restOk E i ∧ restOk E j := by
  intro i j e h
  have h' : h8 M j i ≠ 0 := h
  have f := h8_facts hmy
  obtain ⟨hjx, hjy, hiy⟩ := offdiag_s f.1 f.2.1 f.2.2 h' (Ne.symm e)
  obtain ⟨q, rfl⟩ := slot_row hjx hjy
  rw [h8_off _ (Ne.symm e), hjx, hjy, sub_zero, sub_zero, one_mul] at h'
  refine ⟨⟨hiy, ?_⟩, ⟨hjy, ?_⟩⟩
  · rcases i with ((t|t)|e')
    · simp [iE]
    · simp [iY] at hiy
    · rw [iE_lS]
      by_cases he' : e' ∈ E
      · have hqe : q ≠ e' := fun h' => e (by rw [h'])
        exact absurd (hC e' he' q hqe) h'
      · rw [if_neg he']
  · rw [iE_lS]
    by_cases hq : q ∈ E
    · exact absurd (hR q hq i e) h'
    · rw [if_neg hq]

/-- the two fields for a gauged scalar half. -/
theorem exit_hGr_scal {C : Type} [Fintype C] [DecidableEq C] (S : GScal T Sl C)
    (hR : ExitRows E S.toScal.Mt) (hC : ExitCols E S.toScal.Mt) :
    ∀ i j, i ≠ j → g8 S.toScal.Mti i j ≠ 0 → restOk E i ∧ restOk E j :=
  exit_hGr S.toScal.im S.toScal.mi hR hC (fun t j => S.toScal.hx t j) S.toScal.hiy

theorem exit_hHr_scal {C : Type} [Fintype C] [DecidableEq C] (S : GScal T Sl C)
    (hR : ExitRows E S.toScal.Mt) (hC : ExitCols E S.toScal.Mt) :
    ∀ i j, i ≠ j → (h8 S.toScal.Mt)ᵀ i j ≠ 0 → restOk E i ∧ restOk E j :=
  exit_hHr S.toScal.hmy hR hC

end ExitEnd
end
end XEX
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.XEX.exit_hGr
#print axioms OAI.PowerSaving.XEX.exit_hHr
#print axioms OAI.PowerSaving.XEX.exit_hGr_scal
