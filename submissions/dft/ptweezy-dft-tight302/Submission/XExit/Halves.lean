import Submission.Work.Gauge.Inv
import Submission.XExit.Pack
import Mathlib.Tactic.NoncommRing

/-!
# (key: x-exit) The label half with EXIT labels: `GLabX`, and THE EXIT INVOCATION THEOREM `GLabX.inv : GInvX`

Shea's / DFT Bridge3's `GLab` (Gauge/Def+Inv) ends every slot at a FULL label: after the label routes the slots go
(free) to the old frame of `1`, the end gate `g8 Mti` ("slots := rows of the inverse") runs on old frames, and the
slots go (free) to the full label in the base of their entrance.  `GLabX` lets the slots of a set `E` end at an exit
label `exl q` (same base as `ent q`, `ent q ⊆ exl q`; hyperplane exits dim 8, cold exits dim 4), as the hub's
hyperplane-ended helpers do (#593/#599, `research/hyperplane-end-lean`: the single cleanup gate of a helper runs in a
tail phase at the join `U` of its frame and its partner's frame; the rest of the cleanup never touches it).

The end gate is split, and the split is CERTIFICATE DATA (finite facts, decidable per instance):
* forward  `Gr * Gt = g8 Mti`       (`hGsplit`)  `Gt` = the TAIL (runs at the tail labels `labT`),
                                                 `Gr` = the REST (runs at old frames);
* backward `Hr * Ht = (h8 Mt)ᵀ`     (`hHsplit`)  the inverse-transpose word, same two phases;
* adapter conditions: an off-diagonal entry of a tail gate joins two roles with the SAME tail label (`hGt`, `hHt`);
  an off-diagonal entry of a rest gate joins two roles that are neither y roles nor exit slots (`hGr`, `hHr`), so the
  exit slots are never touched after the tail.
For the hub's hyperplane-ended helpers (one cleanup gate `h -= p` moved right after part B; the rest `R` of the cleanup
never reads or writes `h`): `Gt` = that gate, `Gr` = `R`; backward `Ht` = its inverse-transpose `p += h`,
`Hr = (h8 R⁻¹)ᵀ`.  The specific "rows of `Mti` / columns of `Mtᵀ`" choice is `(gE, gR)` / `(hE, hR)` with
`g8_split`, `h8_split`, `gE_legal`, `gR_legal`, `hE_legal`, `hR_legal` (conditions `hF1`, `hT1`; `hF2`, `hT2`, `hT3`);
it needs `Mt (exit, rest) = 0`, which FAILS when a partner `p` is an ordinary helper, so the general form is the one
to use for the hub words.
The label route gains one phase: `pT : labB → labT` (price `rT`), `pF : labT → labF`.

Result: `GLabX.inv : GInvX` with exit labels `exq q = exl q` (q ∈ E) or `(ent q).top` (q ∉ E), price `GLabX.cost`;
with XExit/Pack's reduction, `engine_of_ginv_401` applies (bank residual `dim exq - dim ent`).

Credits: Jacob Sussman's `Lab.inv` / dirt gates / engine (wht-power-saving-lean, Apache-2.0); DFT Bridge3's `GLab.inv`
(Gauge/Inv, in Ryan Shea's shea256/fourier-transform-below-nlogn lean/complex588, Nil Mamano's gauged extension) on
Dugongue's #401; the hyperplane / cold exits and the tail-gate argument are the hub's (CrocSwap/integer-mult-bounds
#593/#599/#604, Kothe's #799 lineage).  This file is a modified copy of Gauge/Inv.  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace XEX
open Binary Matrix Finset RAM SS CB BR CR GF RF GX B401
noncomputable section

section Split
variable {T Sl : Type} [Fintype T] [DecidableEq T] [Fintype Sl] [DecidableEq Sl]

/-- indicator of the exit slots. -/
def iE (E : Finset Sl) : L3 T Sl → ℚ := Sum.elim (fun _ => 0) (fun q => if q ∈ E then 1 else 0)
/-- indicator of the other slots. -/
def iR (E : Finset Sl) : L3 T Sl → ℚ := Sum.elim (fun _ => 0) (fun q => if q ∈ E then 0 else 1)
def PE (E : Finset Sl) : Matrix (L3 T Sl) (L3 T Sl) ℚ := Matrix.diagonal (iE E)
def PR (E : Finset Sl) : Matrix (L3 T Sl) (L3 T Sl) ℚ := Matrix.diagonal (iR E)

lemma PR_PE (E : Finset Sl) : (PR E : Matrix (L3 T Sl) (L3 T Sl) ℚ) * PE E = 0 := by
  unfold PR PE
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_zero]
  congr 1
  funext i
  rcases i with (a|q)
  · simp [iR, iE]
  · by_cases h : q ∈ E <;> simp [iR, iE, h]

lemma sum_P (E : Finset Sl) : (PX : Matrix (L3 T Sl) (L3 T Sl) ℚ) + PY + PE E + PR E = 1 := by
  unfold PX PY PE PR
  simp only [Matrix.diagonal_add]
  rw [← Matrix.diagonal_one]
  congr 1
  funext i
  rcases i with ((t|t)|q)
  · simp [iX, iY, iR, iE]
  · simp [iX, iY, iR, iE]
  · by_cases h : q ∈ E <;> simp [iX, iY, iR, iE, h]

lemma PX_T : (PX : Matrix (L3 T Sl) (L3 T Sl) ℚ)ᵀ = PX := by unfold PX; exact Matrix.diagonal_transpose _
lemma PY_T : (PY : Matrix (L3 T Sl) (L3 T Sl) ℚ)ᵀ = PY := by unfold PY; exact Matrix.diagonal_transpose _
lemma PE_T (E : Finset Sl) : (PE E : Matrix (L3 T Sl) (L3 T Sl) ℚ)ᵀ = PE E := by
  unfold PE; exact Matrix.diagonal_transpose _
lemma PR_T (E : Finset Sl) : (PR E : Matrix (L3 T Sl) (L3 T Sl) ℚ)ᵀ = PR E := by
  unfold PR; exact Matrix.diagonal_transpose _

/-- the TAIL gate (forward): rows of the exit slots. -/
def gE (E : Finset Sl) (M : Matrix (L3 T Sl) (L3 T Sl) ℚ) : Matrix (L3 T Sl) (L3 T Sl) ℚ := 1 - PE E + PE E * M
/-- the REST gate (forward): rows of the other slots. -/
def gR (E : Finset Sl) (M : Matrix (L3 T Sl) (L3 T Sl) ℚ) : Matrix (L3 T Sl) (L3 T Sl) ℚ := 1 - PR E + PR E * M
/-- the TAIL gate (backward): columns of the exit slots. -/
def hE (E : Finset Sl) (M : Matrix (L3 T Sl) (L3 T Sl) ℚ) : Matrix (L3 T Sl) (L3 T Sl) ℚ := 1 - PE E + M * PE E
/-- the REST gate (backward): columns of the other slots. -/
def hR (E : Finset Sl) (M : Matrix (L3 T Sl) (L3 T Sl) ℚ) : Matrix (L3 T Sl) (L3 T Sl) ℚ := 1 - PR E + M * PR E

/-- **The forward end gate splits**: tail rows first, then the rest, if no rest row reads an exit slot. -/
theorem g8_split (E : Finset Sl) (M : Matrix (L3 T Sl) (L3 T Sl) ℚ) (h : PR E * M * PE E = 0) :
    gR E M * gE E M = g8 M := by
  have key : (1 - PR E + PR E * M) * (1 - PE E + PE E * M)
      = (1 - PE E - PR E + (PE E + PR E) * M) + PR E * PE E - PR E * PE E * M - PR E * M * PE E
        + PR E * M * PE E * M := by noncomm_ring
  have h1 : (1 : Matrix (L3 T Sl) (L3 T Sl) ℚ) - PE E - PR E = PX + PY := by
    rw [← sum_P E]; abel
  have h2 : (1 : Matrix (L3 T Sl) (L3 T Sl) ℚ) - PX - PY = PE E + PR E := by
    rw [← sum_P E]; abel
  unfold gR gE g8
  rw [key, PR_PE, h, h1, h2]
  simp

/-- **The backward end gate (inverse-transpose) splits**: tail columns first, then the rest, if no exit row of `Mt`
meets a rest slot. -/
theorem h8_split (E : Finset Sl) (M : Matrix (L3 T Sl) (L3 T Sl) ℚ) (h : PR E * Mᵀ * PE E = 0) :
    hR E Mᵀ * hE E Mᵀ = (h8 M)ᵀ := by
  have key : (1 - PR E + Mᵀ * PR E) * (1 - PE E + Mᵀ * PE E)
      = (1 - PE E - PR E + Mᵀ * (PE E + PR E)) + PR E * PE E - PR E * Mᵀ * PE E - Mᵀ * (PR E * PE E)
        + Mᵀ * (PR E * Mᵀ * PE E) := by noncomm_ring
  have h1 : (1 : Matrix (L3 T Sl) (L3 T Sl) ℚ) - PE E - PR E = PX + PY := by
    rw [← sum_P E]; abel
  have h2 : (1 : Matrix (L3 T Sl) (L3 T Sl) ℚ) - PX - PY = PE E + PR E := by
    rw [← sum_P E]; abel
  have hT : (h8 M)ᵀ = PX + PY + Mᵀ * (PE E + PR E) := by
    unfold h8
    rw [h2, Matrix.transpose_add, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_add,
      PX_T, PY_T, PE_T, PR_T]
  unfold hR hE
  rw [key, PR_PE, h, h1, hT]
  simp

/-- an entrywise condition gives the matrix condition `PR * M * PE = 0`. -/
lemma PR_M_PE (E : Finset Sl) (M : Matrix (L3 T Sl) (L3 T Sl) ℚ)
    (h : ∀ q q', q ∉ E → q' ∈ E → M (lS q) (lS q') = 0) : PR E * M * PE E = 0 := by
  ext i j
  simp only [PR, PE, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.zero_apply]
  rcases i with (a|q)
  · simp [iR]
  · rcases j with (b|q')
    · simp [iE]
    · by_cases hq : q ∈ E
      · simp [iR, hq]
      · by_cases hq' : q' ∈ E
        · simp [iR, iE, hq, hq', h q q' hq hq']
        · simp [iE, hq']

lemma gE_off (E : Finset Sl) (M : Matrix (L3 T Sl) (L3 T Sl) ℚ) {i j : L3 T Sl} (e : i ≠ j) :
    gE E M i j = iE E i * M i j := by
  simp [gE, PE, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply_ne e, Matrix.diagonal_apply_ne _ e,
    Matrix.diagonal_mul]

lemma gR_off (E : Finset Sl) (M : Matrix (L3 T Sl) (L3 T Sl) ℚ) {i j : L3 T Sl} (e : i ≠ j) :
    gR E M i j = iR E i * M i j := by
  simp [gR, PR, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply_ne e, Matrix.diagonal_apply_ne _ e,
    Matrix.diagonal_mul]

lemma hE_off (E : Finset Sl) (M : Matrix (L3 T Sl) (L3 T Sl) ℚ) {i j : L3 T Sl} (e : i ≠ j) :
    hE E M i j = M i j * iE E j := by
  simp [hE, PE, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply_ne e, Matrix.diagonal_apply_ne _ e,
    Matrix.mul_diagonal]

lemma hR_off (E : Finset Sl) (M : Matrix (L3 T Sl) (L3 T Sl) ℚ) {i j : L3 T Sl} (e : i ≠ j) :
    hR E M i j = M i j * iR E j := by
  simp [hR, PR, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply_ne e, Matrix.diagonal_apply_ne _ e,
    Matrix.mul_diagonal]

/-- unit y columns: a slot row has no y entry. -/
lemma col_y_zero {M : Matrix (L3 T Sl) (L3 T Sl) ℚ} (h : M * PY = PY) (q : Sl) (t : T) :
    M (lS q) (lY t) = 0 := by
  have h' := congrFun (congrFun h (lS q)) (lY t)
  simpa [PY, Matrix.mul_diagonal, iY, Matrix.diagonal_apply] using h'

/-- a role the REST gate may touch: not a y role, not an exit slot (so it sits at the old frame of `1`). -/
abbrev restOk (E : Finset Sl) (i : L3 T Sl) : Prop := iY i = 0 ∧ iE E i = 0

/-- the specific forward choice `(gE, gR)` is legal: tail rows read only roles at the tail label of the slot
(`hF1`), rest rows read no exit slot (`hT1`). -/
lemma gE_legal {β : Type} (E : Finset Sl) (M : Matrix (L3 T Sl) (L3 T Sl) ℚ) (lab : L3 T Sl → β)
    (hF1 : ∀ q j, q ∈ E → M (lS q) j ≠ 0 → lab j = lab (lS q)) :
    ∀ i j, i ≠ j → gE E M i j ≠ 0 → lab i = lab j := by
  intro i j e hij
  rw [gE_off E M e] at hij
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hij
  rcases i with (a|q)
  · exact absurd (by simp [iE]) h1
  · have hq : q ∈ E := by
      by_contra hq
      exact h1 (by simp [iE, hq])
    exact (hF1 q j hq h2).symm

lemma gR_legal (E : Finset Sl) (M : Matrix (L3 T Sl) (L3 T Sl) ℚ) (hiy : M * PY = PY)
    (hT1 : ∀ q q', q ∉ E → q' ∈ E → M (lS q) (lS q') = 0) :
    ∀ i j, i ≠ j → gR E M i j ≠ 0 → restOk E i ∧ restOk E j := by
  intro i j e hij
  rw [gR_off E M e] at hij
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hij
  rcases i with (a|q)
  · exact absurd (by simp [iR]) h1
  · have hq : q ∉ E := fun hq => h1 (by simp [iR, hq])
    refine ⟨⟨by simp [iY], by simp [iE, hq]⟩, ?_⟩
    rcases j with ((t|t)|q')
    · exact ⟨by simp [iY], by simp [iE]⟩
    · exact absurd (col_y_zero hiy q t) h2
    · by_cases hq' : q' ∈ E
      · exact absurd (hT1 q q' hq hq') h2
      · exact ⟨by simp [iY], by simp [iE, hq']⟩

/-- the specific backward choice `(hE, hR)` (exit columns of `Mtᵀ` first) is legal under `hF2`, `hT3`. -/
lemma hE_legal {β : Type} (E : Finset Sl) (M : Matrix (L3 T Sl) (L3 T Sl) ℚ) (lab : L3 T Sl → β)
    (hF2 : ∀ q i, q ∈ E → M (lS q) i ≠ 0 → lab i = lab (lS q)) :
    ∀ i j, i ≠ j → hE E Mᵀ i j ≠ 0 → lab i = lab j := by
  intro i j e hij
  rw [hE_off E _ e, Matrix.transpose_apply] at hij
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hij
  rcases j with (a|q)
  · exact absurd (by simp [iE]) h2
  · have hq : q ∈ E := by
      by_contra hq
      exact h2 (by simp [iE, hq])
    exact hF2 q i hq h1

lemma hR_legal (E : Finset Sl) (M : Matrix (L3 T Sl) (L3 T Sl) ℚ) (hmy : M * PY = PY)
    (hT3 : ∀ q q', q ∉ E → q' ∈ E → M (lS q) (lS q') = 0) :
    ∀ i j, i ≠ j → hR E Mᵀ i j ≠ 0 → restOk E i ∧ restOk E j := by
  intro i j e hij
  rw [hR_off E _ e, Matrix.transpose_apply] at hij
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hij
  rcases j with (a|q)
  · exact absurd (by simp [iR]) h2
  · have hq : q ∉ E := fun hq => h2 (by simp [iR, hq])
    refine ⟨?_, ⟨by simp [iY], by simp [iE, hq]⟩⟩
    rcases i with ((t|t)|q')
    · exact ⟨by simp [iY], by simp [iE]⟩
    · exact absurd (col_y_zero hmy q t) h1
    · by_cases hq' : q' ∈ E
      · exact absurd (hT3 q q' hq hq') h1
      · exact ⟨by simp [iY], by simp [iE, hq']⟩

end Split

section Lab
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]

/-- **The label half with exit labels.** -/
structure GLabX (H : Type) [Fintype H] [DecidableEq H] {T Sl C : Type} [Fintype T] [DecidableEq T]
    [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C] (S : GScal T Sl C) where
  tv : T → Space H
  hunit : ∀ t, dot (tv t) (tv t) = 1
  hgap : ∀ t, ∃ p, tv t p = 0
  ent : Sl → SLbl H
  E : Finset Sl
  exl : Sl → SLbl H
  hexG : ∀ q ∈ E, (exl q).G = (ent q).G
  hexs : ∀ q ∈ E, (ent q).s ⊆ (exl q).s
  lab0 : L3 T Sl → SLbl H
  labA : L3 T Sl → SLbl H
  labB : L3 T Sl → SLbl H
  labT : L3 T Sl → SLbl H
  labF : L3 T Sl → SLbl H
  cen : C → SLbl H
  z0 : SLbl H
  hz0 : z0.dim = 0
  h0x : ∀ t, (lab0 (lX t)).dim = 1 ∧ (lab0 (lX t)).Mem (tv t)
  h0y : ∀ t, (lab0 (lY t)).dim = 0
  h0s' : ∀ q, lab0 (lS q) = ent q
  hent : ∀ q, q ∉ S.gauged → (ent q).dim = 0
  hAy : ∀ t, labA (lY t) = z0
  hAc : ∀ k q, S.Cc k q ≠ 0 → cen k = labA (lS q)
  hcen : ∀ k, 0 < (cen k).dim
  hFx : ∀ t, (labF (lX t)).dim = Fintype.card H
  hFs : ∀ q, q ∉ E → (labF (lS q)).dim = Fintype.card H
  hFe : ∀ q, q ∈ E → labF (lS q) = exl q
  hFy : ∀ t, (labF (lY t)).dim + 1 = Fintype.card H ∧
    ∀ x, (labF (lY t)).Mem x → dot (tv t) x = 0
  Gt : Matrix (L3 T Sl) (L3 T Sl) ℚ
  Gr : Matrix (L3 T Sl) (L3 T Sl) ℚ
  Ht : Matrix (L3 T Sl) (L3 T Sl) ℚ
  Hr : Matrix (L3 T Sl) (L3 T Sl) ℚ
  hGsplit : Gr * Gt = g8 S.toScal.Mti
  hHsplit : Hr * Ht = (h8 S.toScal.Mt)ᵀ
  hGt : ∀ i j, i ≠ j → Gt i j ≠ 0 → labT i = labT j
  hHt : ∀ i j, i ≠ j → Ht i j ≠ 0 → labT i = labT j
  hGr : ∀ i j, i ≠ j → Gr i j ≠ 0 → restOk E i ∧ restOk E j
  hHr : ∀ i j, i ≠ j → Hr i j ≠ 0 → restOk E i ∧ restOk E j
  rA : List ℕ
  rB : List ℕ
  rT : List ℕ
  rF : List ℕ
  pA : ∀ {α : Type} [Fintype α] [DecidableEq α] (X : BXMap H α),
    Fintype.card H < Fintype.card α →
    GRoute (fun r => X.Φ (lab0 r)) (fun r => X.Φ (labA r)) (actPoint S.MA)
        (fun φ => rcost φ rA) ∧
    GRoute (fun r => X.Φ (lab0 r)) (fun r => X.Φ (labA r)) (actPoint S.MAiᵀ)
        (fun φ => rcost φ rA)
  pB : ∀ {α : Type} [Fintype α] [DecidableEq α] (X : BXMap H α),
    Fintype.card H < Fintype.card α →
    GRoute (fun r => X.Φ (labA r)) (fun r => X.Φ (labB r)) (actPoint S.MB)
        (fun φ => rcost φ rB) ∧
    GRoute (fun r => X.Φ (labA r)) (fun r => X.Φ (labB r)) (actPoint S.MBiᵀ)
        (fun φ => rcost φ rB)
  pT : ∀ {α : Type} [Fintype α] [DecidableEq α] (X : BXMap H α),
    Fintype.card H < Fintype.card α →
    GRoute (fun r => X.Φ (labB r)) (fun r => X.Φ (labT r)) id (fun φ => rcost φ rT)
  pF : ∀ {α : Type} [Fintype α] [DecidableEq α] (X : BXMap H α),
    Fintype.card H < Fintype.card α →
    GRoute (fun r => X.Φ (labT r)) (fun r => X.Φ (labF r)) id (fun φ => rcost φ rF)

/-- price of one exit-labelled invocation. -/
def GLabX.cost {S : GScal T Sl C} (L : GLabX H S) (φ : ℕ → ℝ) : ℝ :=
  rcost φ L.rA + (∑ k, bcost φ (L.cen k).dim) + rcost φ L.rB + rcost φ L.rT + rcost φ L.rF

/-- the exit label of each slot in the package: `exl q` for `q ∈ E`, the full label of its entrance base otherwise. -/
def GLabX.exq {S : GScal T Sl C} (L : GLabX H S) (q : Sl) : SLbl H :=
  if q ∈ L.E then L.exl q else (L.ent q).top

variable {α : Type} [Fintype α] [DecidableEq α]
variable {S : GScal T Sl C} (L : GLabX H S) (W : GWin H α)

/-- live frames before the rest gate: old frames, exit slots at their exit labels. -/
def finX : L3 T Sl → CMat α :=
  Sum.elim (Sum.elim (fun _ => W.Xm.Φ 1) (fun t => W.Xm.Φ (1 + tt (L.tv t))))
    (fun q => if q ∈ L.E then W.X.Φ (L.exl q) else W.Xm.Φ 1)

/-- live frames at the end: old frames of x and y, exit labels of the slots. -/
def gen2X : L3 T Sl → CMat α :=
  Sum.elim (Sum.elim (fun _ => W.Xm.Φ 1) (fun t => W.Xm.Φ (1 + tt (L.tv t)))) (fun q => W.X.Φ (L.exq q))

theorem GLabX.pre : GRoute (gst0 W L.tv L.ent) (gst1 W L.tv L.ent S.gauged) id (fun _ => 0) := by
  refine (GRoute.reach_all _ _ (fun _ _ => 0) ?_).cast (fun φ => by simp)
  rintro ((t|t)|q)
  · exact GReach.refl _
  · exact GReach.refl _
  · show GReach (W.X.Φ (L.ent q)) (if q ∈ S.gauged then W.X.Φ (L.ent q) else W.Xm.Φ 0) _
    by_cases hq : q ∈ S.gauged
    · rw [if_pos hq]; exact GReach.refl _
    · rw [if_neg hq]; exact W.zeroB _ (L.hent q hq)

theorem GLabX.ad0 :
    GRoute (gst1 W L.tv L.ent S.gauged) (fun r => W.X.Φ (L.lab0 r)) id (fun _ => 0) := by
  refine (GRoute.reach_all _ _ (fun _ _ => 0) ?_).cast (fun φ => by simp)
  rintro ((t|t)|q)
  · obtain ⟨p, hp⟩ := L.hgap t
    obtain ⟨A, k, hA⟩ := exists_base_one (L.tv t) (L.hunit t) p hp
    have h := W.line A k (L.lab0 (lX t)) (L.h0x t).1 (by rw [hA]; exact (L.h0x t).2)
    rw [hA] at h
    exact h
  · exact W.zero _ (L.h0y t)
  · show GReach (if q ∈ S.gauged then W.X.Φ (L.ent q) else W.Xm.Φ 0) (W.X.Φ (L.lab0 (lS q))) _
    rw [L.h0s' q]
    by_cases hq : q ∈ S.gauged
    · rw [if_pos hq]; exact GReach.refl _
    · rw [if_neg hq]; exact W.zero _ (L.hent q hq)

/-- (free) the end labels to the old frames, exit slots stay at their exit labels. -/
theorem GLabX.adF : GRoute (fun r => W.X.Φ (L.labF r)) (finX L W) id (fun _ => 0) := by
  refine (GRoute.reach_all _ _ (fun _ _ => 0) ?_).cast (fun φ => by simp)
  rintro ((t|t)|q)
  · exact W.full _ (L.hFx t)
  · obtain ⟨p, hp⟩ := L.hgap t
    obtain ⟨A, k, hA⟩ := exists_base_one (L.tv t) (L.hunit t) p hp
    have h := W.perp A k (L.labF (lY t)) (L.hFy t).1 (by rw [hA]; exact (L.hFy t).2)
    rw [hA] at h
    exact h
  · show GReach (W.X.Φ (L.labF (lS q))) (if q ∈ L.E then W.X.Φ (L.exl q) else W.Xm.Φ 1) _
    by_cases hq : q ∈ L.E
    · rw [if_pos hq, L.hFe q hq]; exact GReach.refl _
    · rw [if_neg hq]; exact W.full _ (L.hFs q hq)

/-- (free) the other slots from the old frame of `1` to the full label of their entrance base. -/
theorem GLabX.post : GRoute (finX L W) (gen2X L W) id (fun _ => 0) := by
  refine (GRoute.reach_all _ _ (fun _ _ => 0) ?_).cast (fun φ => by simp)
  rintro ((t|t)|q)
  · exact GReach.refl _
  · exact GReach.refl _
  · show GReach (if q ∈ L.E then W.X.Φ (L.exl q) else W.Xm.Φ 1) (W.X.Φ (L.exq q)) _
    unfold GLabX.exq
    by_cases hq : q ∈ L.E
    · rw [if_pos hq, if_pos hq]; exact GReach.refl _
    · rw [if_neg hq, if_neg hq]; exact W.topN _ (SLbl.top_dim _)

lemma GLabX.cfacts (hb : Fintype.card H < Fintype.card α) (k : C) :
    (∀ x, L.z0.Mem x → (L.cen k).Mem x) ∧ L.z0.dim < (L.cen k).dim ∧
    (L.cen k).dim - L.z0.dim < Fintype.card α := by
  refine ⟨fun x hx => ?_, by rw [L.hz0]; exact L.hcen k, ?_⟩
  · rw [mem_dim_zero L.z0 L.hz0 hx]
    exact insub_zero _ _
  · have h1 : (L.cen k).dim ≤ Fintype.card H := Finset.card_le_univ _
    omega

lemma GLabX.cdn (k : C) :
    GReach (W.X.Φ (L.cen k)) (W.X.Φ L.z0) (fun φ => bcost φ (L.cen k).dim) := by
  obtain ⟨h0, h1, h2⟩ := L.cfacts W.big k
  have h := (W.X.fmv_sup L.z0 (L.cen k) h0 h1 h2).reach
  have h' : GReach (W.X.Φ (L.cen k)) (W.X.Φ L.z0)
      (fun φ => rcost φ [(L.cen k).dim - L.z0.dim]) := GReach.ofReach h
  exact h'.cast (fun φ => by rw [rcost_single, L.hz0, Nat.sub_zero])

lemma GLabX.cupk (k : C) :
    GReach (W.X.Φ L.z0) (W.X.Φ (L.cen k)) (fun φ => bcost φ (L.cen k).dim) := by
  obtain ⟨h0, h1, h2⟩ := L.cfacts W.big k
  have h := (W.X.fmv_sub L.z0 (L.cen k) h0 h1 h2).reach
  have h' : GReach (W.X.Φ L.z0) (W.X.Φ (L.cen k))
      (fun φ => rcost φ [(L.cen k).dim - L.z0.dim]) := GReach.ofReach h
  exact h'.cast (fun φ => by rw [rcost_single, L.hz0, Nat.sub_zero])

theorem GLabX.cdown (Sf : L3 T Sl → CMat α) :
    GRoute (glue Sf (fun k => W.X.Φ (L.cen k))) (glue Sf (fun _ : C => W.X.Φ L.z0)) id
      (fun φ => ∑ k, bcost φ (L.cen k).dim) :=
  greach_copies Sf _ _ _ (fun k => L.cdn W k)

theorem GLabX.cup (Sf : L3 T Sl → CMat α) :
    GRoute (glue Sf (fun _ : C => W.X.Φ L.z0)) (glue Sf (fun k => W.X.Φ (L.cen k))) id
      (fun φ => ∑ k, bcost φ (L.cen k).dim) :=
  greach_copies Sf _ _ _ (fun k => L.cupk W k)

lemma GLabX.gate_ok {i j : L3 T Sl} (t : T) (q : Sl) (hi : i = lY t) (hj : j = lS q)
    (hM : S.toScal.Mt (lY t) (lS q) ≠ 0) :
    gst1 W L.tv L.ent S.gauged i = gst1 W L.tv L.ent S.gauged j := by
  subst hi; subst hj
  have hq : q ∉ S.gauged := fun hq => hM (S.hE q hq t)
  show W.Xm.Φ 0 = if q ∈ S.gauged then W.X.Φ (L.ent q) else W.Xm.Φ 0
  rw [if_neg hq]

/-- every role the rest gate touches sits at the old frame of `1`. -/
lemma GLabX.finX_one {i : L3 T Sl} (h : restOk L.E i) : finX L W i = W.Xm.Φ 1 := by
  obtain ⟨h1, h2⟩ := h
  rcases i with ((t|t)|q)
  · rfl
  · simp [iY] at h1
  · have hq : q ∉ L.E := fun hq => by simp [iE, hq] at h2
    show (if q ∈ L.E then W.X.Φ (L.exl q) else W.Xm.Φ 1) = _
    rw [if_neg hq]

/-- the forward TAIL gate is legal at the tail labels (`hGt`). -/
theorem GLabX.tailF : GRoute (fun r => W.X.Φ (L.labT r)) (fun r => W.X.Φ (L.labT r))
    (actPoint L.Gt) (fun _ => 0) :=
  GRoute.gate _ _ _ (fun i j hij => by
    by_cases e : i = j
    · subst e; rfl
    · exact congrArg W.X.Φ (L.hGt i j e hij))

/-- the forward REST gate is legal at `finX` (`hGr`: it touches neither y roles nor exit slots). -/
theorem GLabX.restF : GRoute (finX L W) (finX L W) (actPoint L.Gr) (fun _ => 0) :=
  GRoute.gate _ _ _ (fun i j hij => by
    by_cases e : i = j
    · subst e; rfl
    · obtain ⟨hi, hj⟩ := L.hGr i j e hij
      rw [L.finX_one W hi, L.finX_one W hj])

/-- the backward TAIL gate (inverse-transpose) is legal at the tail labels (`hHt`). -/
theorem GLabX.tailB : GRoute (fun r => W.X.Φ (L.labT r)) (fun r => W.X.Φ (L.labT r))
    (actPoint L.Ht) (fun _ => 0) :=
  GRoute.gate _ _ _ (fun i j hij => by
    by_cases e : i = j
    · subst e; rfl
    · exact congrArg W.X.Φ (L.hHt i j e hij))

/-- the backward REST gate is legal at `finX` (`hHr`). -/
theorem GLabX.restB : GRoute (finX L W) (finX L W) (actPoint L.Hr) (fun _ => 0) :=
  GRoute.gate _ _ _ (fun i j hij => by
    by_cases e : i = j
    · subst e; rfl
    · obtain ⟨hi, hj⟩ := L.hHr i j e hij
      rw [L.finX_one W hi, L.finX_one W hj])

/-- **Forward word on clean frames, exit labels.** -/
theorem GLabX.fwd_erasedX (c0 c1 : C → CMat α) :
    GRoute (iin W.Xm L.tv (fun q => W.X.Φ (L.ent q)) c0)
      (iout W.Xm L.tv (fun q => W.X.Φ (L.exq q)) c1) shearF L.cost := by
  have a1 : GRoute (gst1 W L.tv L.ent S.gauged) (gst1 W L.tv L.ent S.gauged)
      (actPoint (g1 S.toScal.Mt)) (fun _ => 0) :=
    GRoute.gate (g1 S.toScal.Mt) _ _ (fun i j hij => by
      by_cases e : i = j
      · subst e; rfl
      · obtain ⟨t, q, hi, hj, hM⟩ := g1_off hij e
        exact L.gate_ok W t q hi hj hM)
  have seg1 : GRoute (gst0 W L.tv L.ent) (fun r => W.X.Φ (L.labA r))
      S.toScal.f1 (fun φ => rcost φ L.rA) :=
    ((((L.pre W).trans a1).trans (L.ad0 W)).trans (L.pA W.X W.big).1).cast (fun φ => by simp)
  have seg2' := ((((((L.pB W.X W.big).1.trans (L.pT W.X W.big)).trans (L.tailF W)).trans
    (L.pF W.X W.big)).trans (L.adF W)).trans (L.restF W)).trans (L.post W)
  have seg2 : GRoute (fun r => W.X.Φ (L.labA r)) (gen2X L W)
      S.toScal.f2 (fun φ => rcost φ L.rB + rcost φ L.rT + rcost φ L.rF) := by
    refine (seg2'.castg (funext fun u => ?_)).cast (fun φ => by simp)
    show actPoint L.Gr (actPoint L.Gt (actPoint S.MB u))
      = actPoint (g8 S.toScal.Mti) (actPoint S.MB u)
    rw [← CR.actPoint_mul, L.hGsplit]
  have e0 : GRoute (iin W.Xm L.tv (fun q => W.X.Φ (L.ent q)) c0)
      (glue (gst0 W L.tv L.ent) (fun k => W.X.Φ (L.cen k))) eraseC (fun _ => 0) :=
    GRoute.ofX (xerase (fun t => rfl) (fun t => rfl) (fun q => rfl))
  have L1 := glift_live (fun k => W.X.Φ (L.cen k)) seg1
  have m1 : GRoute (glue (fun r => W.X.Φ (L.labA r)) (fun k => W.X.Φ (L.cen k)))
      (glue (fun r => W.X.Φ (L.labA r)) (fun k => W.X.Φ (L.cen k)))
      (fun z => addBlk bC (ap S.Cc (z ∘ bS)) z) (fun _ => 0) :=
    GRoute.ofX (xgate_shear bC bS bS_inj S.Cc (fun k q h => congrArg W.X.Φ (L.hAc k q h)))
  have m2 := L.cdown W (fun r => W.X.Φ (L.labA r))
  have m3 : GRoute (glue (fun r => W.X.Φ (L.labA r)) (fun _ : C => W.X.Φ L.z0))
      (glue (fun r => W.X.Φ (L.labA r)) (fun _ : C => W.X.Φ L.z0))
      (fun z => addBlk bY (ap S.Jr (z ∘ bC)) z) (fun _ => 0) :=
    GRoute.ofX (xgate_shear bY bC bC_inj S.Jr (fun t k _ => congrArg W.X.Φ (L.hAy t)))
  have L2 := glift_live (fun _ : C => W.X.Φ L.z0) seg2
  have e1 : GRoute (glue (gen2X L W) (fun _ : C => W.X.Φ L.z0))
      (iout W.Xm L.tv (fun q => W.X.Φ (L.exq q)) c1) eraseC (fun _ => 0) :=
    GRoute.ofX (xerase (fun t => rfl) (fun t => rfl) (fun q => rfl))
  have tot := (((((e0.trans L1).trans m1).trans m2).trans m3).trans L2).trans e1
  refine (tot.castg (g' := shearF) (funext fun z => S.toScal.fwd_scalar z)).cast (fun φ => ?_)
  simp only [GLabX.cost, zero_add, add_zero]
  ring

/-- **Backward word on clean frames, exit labels** (the inverse-transpose). -/
theorem GLabX.bwd_erasedX (c0 c1 : C → CMat α) :
    GRoute (iin W.Xm L.tv (fun q => W.X.Φ (L.ent q)) c0)
      (iout W.Xm L.tv (fun q => W.X.Φ (L.exq q)) c1) shearB L.cost := by
  have a1 : GRoute (gst1 W L.tv L.ent S.gauged) (gst1 W L.tv L.ent S.gauged)
      (actPoint (g1i S.toScal.Mt)ᵀ) (fun _ => 0) :=
    GRoute.gate (g1i S.toScal.Mt)ᵀ _ _ (fun i j hij => by
      by_cases e : i = j
      · subst e; rfl
      · have hij' : g1i S.toScal.Mt j i ≠ 0 := hij
        obtain ⟨t, q, hj, hi, hM⟩ := g1i_off hij' (Ne.symm e)
        exact (L.gate_ok W t q hj hi hM).symm)
  have seg1 : GRoute (gst0 W L.tv L.ent) (fun r => W.X.Φ (L.labA r))
      S.toScal.b1 (fun φ => rcost φ L.rA) :=
    ((((L.pre W).trans a1).trans (L.ad0 W)).trans (L.pA W.X W.big).2).cast (fun φ => by simp)
  have seg2' := ((((((L.pB W.X W.big).2.trans (L.pT W.X W.big)).trans (L.tailB W)).trans
    (L.pF W.X W.big)).trans (L.adF W)).trans (L.restB W)).trans (L.post W)
  have seg2 : GRoute (fun r => W.X.Φ (L.labA r)) (gen2X L W)
      S.toScal.b2 (fun φ => rcost φ L.rB + rcost φ L.rT + rcost φ L.rF) := by
    refine (seg2'.castg (funext fun u => ?_)).cast (fun φ => by simp)
    show actPoint L.Hr (actPoint L.Ht (actPoint S.MBiᵀ u))
      = actPoint (h8 S.toScal.Mt)ᵀ (actPoint S.MBiᵀ u)
    rw [← CR.actPoint_mul, L.hHsplit]
  have e0 : GRoute (iin W.Xm L.tv (fun q => W.X.Φ (L.ent q)) c0)
      (glue (gst0 W L.tv L.ent) (fun _ : C => W.X.Φ L.z0)) eraseC (fun _ => 0) :=
    GRoute.ofX (xerase (fun t => rfl) (fun t => rfl) (fun q => rfl))
  have L1 := glift_live (fun _ : C => W.X.Φ L.z0) seg1
  have m1 : GRoute (glue (fun r => W.X.Φ (L.labA r)) (fun _ : C => W.X.Φ L.z0))
      (glue (fun r => W.X.Φ (L.labA r)) (fun _ : C => W.X.Φ L.z0))
      (fun z => addBlk bC (ap S.Jrᵀ (z ∘ bY)) z) (fun _ => 0) :=
    GRoute.ofX (xgate_shear bC bY bY_inj S.Jrᵀ (fun k t _ => (congrArg W.X.Φ (L.hAy t)).symm))
  have m2 := L.cup W (fun r => W.X.Φ (L.labA r))
  have m3 : GRoute (glue (fun r => W.X.Φ (L.labA r)) (fun k => W.X.Φ (L.cen k)))
      (glue (fun r => W.X.Φ (L.labA r)) (fun k => W.X.Φ (L.cen k)))
      (fun z => addBlk bS (ap (-S.Ccᵀ) (z ∘ bC)) z) (fun _ => 0) :=
    GRoute.ofX (xgate_shear bS bC bC_inj (-S.Ccᵀ)
      (fun q k h => (congrArg W.X.Φ (L.hAc k q (ne_of_negT S.Cc h))).symm))
  have L2 := glift_live (fun k => W.X.Φ (L.cen k)) seg2
  have e1 : GRoute (glue (gen2X L W) (fun k => W.X.Φ (L.cen k)))
      (iout W.Xm L.tv (fun q => W.X.Φ (L.exq q)) c1) eraseC (fun _ => 0) :=
    GRoute.ofX (xerase (fun t => rfl) (fun t => rfl) (fun q => rfl))
  have tot := (((((e0.trans L1).trans m1).trans m2).trans m3).trans L2).trans e1
  refine (tot.castg (g' := shearB) (funext fun z => S.toScal.bwd_scalar z)).cast (fun φ => ?_)
  simp only [GLabX.cost, zero_add, add_zero]
  ring

/-- **THE EXIT INVOCATION THEOREM.**  An exit-labelled certificate is an exit-frame package, with price `L.cost`. -/
def GLabX.inv : GInvX H T Sl C where
  tv := L.tv
  hunit := L.hunit
  hgap := L.hgap
  cost := L.cost
  ent := L.ent
  ex := L.exq
  hexG := fun q => by
    unfold GLabX.exq
    by_cases h : q ∈ L.E
    · rw [if_pos h]; exact L.hexG q h
    · rw [if_neg h]; rfl
  hexs := fun q => by
    unfold GLabX.exq
    by_cases h : q ∈ L.E
    · rw [if_pos h]; exact L.hexs q h
    · rw [if_neg h]; exact Finset.subset_univ _
  fwd := fun W N Wn hN hW Z c0 c1 =>
    gdirtyE W.Xm L.tv _ _ N Wn hN hW Z c0 c1 (L.fwd_erasedX W c0 c1)
      (shearF_comm (fun _ => 1) (fun q => N q * Z q) (fun _ => 1))
  bwd := fun W N Wn hN hW Z c0 c1 =>
    gdirtyE W.Xm L.tv _ _ N Wn hN hW Z c0 c1 (L.bwd_erasedX W c0 c1)
      (shearB_comm (fun _ => 1) (fun q => N q * Z q) (fun _ => 1))

@[simp] lemma GLabX.inv_cost (φ : ℕ → ℝ) : L.inv.cost φ = L.cost φ := rfl
@[simp] lemma GLabX.inv_ent : L.inv.ent = L.ent := rfl
@[simp] lemma GLabX.inv_ex : L.inv.ex = L.exq := rfl

/-- the bank residual of a slot of an exit-labelled certificate: `dim exl - dim ent` (exit), `card H - dim ent` (other). -/
lemma GLabX.res (q : Sl) : (L.inv.ex q).dim - (L.inv.ent q).dim =
    if q ∈ L.E then (L.exl q).dim - (L.ent q).dim else Fintype.card H - (L.ent q).dim := by
  show (L.exq q).dim - (L.ent q).dim = _
  unfold GLabX.exq
  by_cases h : q ∈ L.E
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, SLbl.top_dim]

end Lab
end
end XEX
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.XEX.g8_split
#print axioms OAI.PowerSaving.XEX.h8_split
#print axioms OAI.PowerSaving.XEX.GLabX.fwd_erasedX
#print axioms OAI.PowerSaving.XEX.GLabX.bwd_erasedX
#print axioms OAI.PowerSaving.XEX.GLabX.inv
#print axioms OAI.PowerSaving.XEX.gR_legal
#print axioms OAI.PowerSaving.XEX.hR_legal
