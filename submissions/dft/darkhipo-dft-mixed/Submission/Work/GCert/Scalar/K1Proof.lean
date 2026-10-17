import Submission.Work.GCert.Scalar.Main

/-!
# (key: gx-scalar) K1, route D2: the `(X,A)` row invariant and the renegotiated `hx`

**Goal.** `ScalOK.hx` (`Main.lean:95`) says the x-rows of `Mt = MB * scatM (Jrm * Ccm) * MA`
are unit rows.  Its present proof factors through `ScalOK.xu : XU (Mt)`, and `XU` needs *every
add into an x role to read an x role* (`XU_mic`).  The K2s widening of `okAK` (admitting
`slot → x`: target `x`, source slot) falsifies that conjunct (`okAK`'s last conjunct is
`t < v → s < v`), so the present proof dies — although the *statement* stays true: the s→x dirt
cancels exactly in the composite `MB * scatM (Jrm * Ccm) * MA` (numerically verified,
`SWEEP.md` round 25: `PX * Mt = PX`, `PX * Mt * PS = 0` on the raw ck word).

**What this file provides (the design `k1-invariant-design.md` §2a).**  Track, for the x-rows of
a matrix, the pair `(X, A)`: `X` the x-block, `A` the slot-block.

* `XARow M X A`  the row description (no y columns at all);
* the five add steps — `addXX`, `addXS`, `addSX`, `addSS`, `addY` — mirroring `XU_mic`;
* `XARow.mul_matP`, `XARow.mul_scatM`, so the whole program `addsA ++ scatAdds ++ addsB`
  right-multiplies onto the identity;
* `XGateOK` (the single condition that makes the induction close: *every gate writing a y role
  reads a y role*) and its proof for `addsA`, `scatAdds`, `addsB` from `ScalOK`;
* `ScalOK.XARow_Mt : ∃ X A, XARow (Mt c hv) X A`;
* `ScalOK.mt_ycol : Mt (lX t) (lY S) = 0`  (the y columns of the x rows);
* `ScalOK.hx_of_slotFeed`  the reduction of `hx` to the two facts `X = 1` (from `XRun.xcol`)
  and `A = 0`;
* `ScalOK.slotFeed_zero`  **the key cancellation lemma** — the only `sorry` in this file.  See
  its docstring for the measurement that isolates it and for why the `(X,A)` induction does not
  by itself deliver it.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace GS
open SSC GXD OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM OAI.PowerSaving.SS
  OAI.PowerSaving.CB OAI.PowerSaving.CR Finset Matrix

variable {c : Raw}

/-! ## 1. the generic `(X,A)` invariant -/

section Generic
variable {T Sl : Type} [Fintype T] [DecidableEq T] [Fintype Sl] [DecidableEq Sl]

/-- the row description: the x-row `lX t` of `M` is the `X`-combination of the x columns plus
the `A`-combination of the slot columns, and **nothing** on the y columns -/
def XARow (M : Matrix (L3 T Sl) (L3 T Sl) ℚ) (X : Matrix T T ℚ) (A : Matrix T Sl ℚ) : Prop :=
  ∀ (t : T) (j : L3 T Sl),
    M (lX t) j = (∑ σ : T, X t σ * (if j = lX σ then (1 : ℚ) else 0))
      + (∑ q : Sl, A t q * (if j = lS q then (1 : ℚ) else 0))

/-- the condition that closes the induction: every gate writing a y role reads a y role -/
def XGateOK {T Sl : Type} (un : Nat → L3 T Sl) (l : List (Nat × Nat × Co)) : Prop :=
  ∀ x ∈ l, ∀ S : T, un x.2.1 = lY S → ∃ S' : T, un x.1 = lY S'

theorem XGateOK.append {un : Nat → L3 T Sl} {l l' : List (Nat × Nat × Co)}
    (h1 : XGateOK un l) (h2 : XGateOK un l') : XGateOK un (l ++ l') :=
  fun x hx => (List.mem_append.mp hx).elim (h1 x) (h2 x)

@[simp] theorem lX_eq_lX {σ σ' : T} : ((lX σ : L3 T Sl) = lX σ') ↔ σ = σ' :=
  ⟨fun h => Sum.inl.inj (Sum.inl.inj h), fun h => by rw [h]⟩

@[simp] theorem lY_eq_lY {σ σ' : T} : ((lY σ : L3 T Sl) = lY σ') ↔ σ = σ' :=
  ⟨fun h => Sum.inr.inj (Sum.inl.inj h), fun h => by rw [h]⟩

@[simp] theorem lS_eq_lS {q q' : Sl} : ((lS q : L3 T Sl) = lS q') ↔ q = q' :=
  ⟨fun h => Sum.inr.inj h, fun h => by rw [h]⟩

@[simp] theorem lX_ne_lY {σ S : T} : (lX σ : L3 T Sl) ≠ lY S := fun h => by cases h

@[simp] theorem lX_ne_lS {σ : T} {q : Sl} : (lX σ : L3 T Sl) ≠ lS q := fun h => by cases h

@[simp] theorem lY_ne_lS {σ : T} {q : Sl} : (lY σ : L3 T Sl) ≠ lS q := fun h => by cases h

/-! ### 1.1 the two sums, at a single column -/

theorem sum_lX_at (X : Matrix T T ℚ) (t σ : T) :
    (∑ σ' : T, X t σ' * (if (lX σ : L3 T Sl) = lX σ' then (1 : ℚ) else 0)) = X t σ := by
  rw [Finset.sum_eq_single σ
    (fun b _ hb => by rw [if_neg (fun h => hb (Sum.inl.inj (Sum.inl.inj h)).symm), mul_zero])
    (fun hb => absurd (Finset.mem_univ σ) hb)]
  rw [if_pos rfl, mul_one]

theorem sum_lY_at (X : Matrix T T ℚ) (t S : T) :
    (∑ σ' : T, X t σ' * (if (lY S : L3 T Sl) = lX σ' then (1 : ℚ) else 0)) = 0 :=
  Finset.sum_eq_zero fun σ' _ => by rw [if_neg (fun h => by cases h), mul_zero]

theorem sum_lS_at (X : Matrix T T ℚ) (t : T) (q : Sl) :
    (∑ σ' : T, X t σ' * (if (lS q : L3 T Sl) = lX σ' then (1 : ℚ) else 0)) = 0 :=
  Finset.sum_eq_zero fun σ' _ => by rw [if_neg (fun h => by cases h), mul_zero]

theorem sum_s_at (A : Matrix T Sl ℚ) (t : T) (q : Sl) :
    (∑ q' : Sl, A t q' * (if (lS q : L3 T Sl) = lS q' then (1 : ℚ) else 0)) = A t q := by
  rw [Finset.sum_eq_single q
    (fun b _ hb => by rw [if_neg (fun h => hb (Sum.inr.inj h).symm), mul_zero])
    (fun hb => absurd (Finset.mem_univ q) hb)]
  rw [if_pos rfl, mul_one]

theorem sum_s_at_x (A : Matrix T Sl ℚ) (t σ : T) :
    (∑ q : Sl, A t q * (if (lX σ : L3 T Sl) = lS q then (1 : ℚ) else 0)) = 0 :=
  Finset.sum_eq_zero fun q _ => by rw [if_neg (fun h => by cases h), mul_zero]

theorem sum_s_at_y (A : Matrix T Sl ℚ) (t S : T) :
    (∑ q : Sl, A t q * (if (lY S : L3 T Sl) = lS q then (1 : ℚ) else 0)) = 0 :=
  Finset.sum_eq_zero fun q _ => by rw [if_neg (fun h => by cases h), mul_zero]

/-- the single-column update of a sum: `∑ (v + c·δ_{i₀})·[j = e i]` -/
theorem sum_delta {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι → L3 T Sl) (v : ι → ℚ)
    (i0 : ι) (w : ℚ) (j : L3 T Sl) :
    (∑ i, (v i + (if i = i0 then w else 0)) * (if j = e i then (1 : ℚ) else 0))
      = (∑ i, v i * (if j = e i then (1 : ℚ) else 0)) + (if j = e i0 then w else 0) := by
  trans ∑ i, (v i * (if j = e i then (1 : ℚ) else 0)
    + (if i = i0 then w else 0) * (if j = e i then (1 : ℚ) else 0))
  · exact Finset.sum_congr rfl (fun i _ => add_mul _ _ _)
  · rw [Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single i0 (fun b _ hb => by rw [if_neg hb, zero_mul])
      (fun hb => absurd (Finset.mem_univ i0) hb)]
    by_cases h : j = e i0 <;> simp [h]

/-! ### 1.2 reading the invariant at a single column -/

theorem XARow.eval_x {M : Matrix (L3 T Sl) (L3 T Sl) ℚ} {X : Matrix T T ℚ}
    {A : Matrix T Sl ℚ} (h : XARow M X A) (t σ : T) : M (lX t) (lX σ) = X t σ := by
  rw [h t (lX σ), sum_lX_at X t σ, sum_s_at_x A t σ, add_zero]

theorem XARow.eval_s {M : Matrix (L3 T Sl) (L3 T Sl) ℚ} {X : Matrix T T ℚ}
    {A : Matrix T Sl ℚ} (h : XARow M X A) (t : T) (q : Sl) : M (lX t) (lS q) = A t q := by
  rw [h t (lS q), sum_lS_at X t q, sum_s_at A t q, zero_add]

theorem XARow.eval_y {M : Matrix (L3 T Sl) (L3 T Sl) ℚ} {X : Matrix T T ℚ}
    {A : Matrix T Sl ℚ} (h : XARow M X A) (t S : T) : M (lX t) (lY S) = 0 := by
  rw [h t (lY S), sum_lY_at X t S, sum_s_at_y A t S, add_zero]

/-- the entry forms of the identity and zero matrices at the two index types -/
theorem one_l3 (i j : L3 T Sl) :
    (1 : Matrix (L3 T Sl) (L3 T Sl) ℚ) i j = if i = j then (1 : ℚ) else 0 := Matrix.one_apply

theorem one_T (i j : T) : (1 : Matrix T T ℚ) i j = if i = j then (1 : ℚ) else 0 :=
  Matrix.one_apply

theorem zero_Tl (i : T) (j : Sl) : (0 : Matrix T Sl ℚ) i j = 0 := rfl

theorem XARow.one :
    XARow (1 : Matrix (L3 T Sl) (L3 T Sl) ℚ) (1 : Matrix T T ℚ) (0 : Matrix T Sl ℚ) := by
  intro t j
  rcases j with (σ | S) | q
  · rw [sum_lX_at (1 : Matrix T T ℚ) t σ, sum_s_at_x (0 : Matrix T Sl ℚ) t σ,
      one_l3, one_T]
    by_cases h : t = σ <;> simp [h]
  · rw [sum_lY_at (1 : Matrix T T ℚ) t S, sum_s_at_y (0 : Matrix T Sl ℚ) t S, one_l3]
    simp
  · rw [sum_lS_at (1 : Matrix T T ℚ) t q, sum_s_at (0 : Matrix T Sl ℚ) t q, one_l3]
    simp

/-! ### 1.3 the five add steps (right multiplication by `addMat (un x.1) (un x.2.1) c`) -/

/-- a gate writing a y column: the x and slot entries of the tracked row are unchanged -/
theorem XARow.addY {M : Matrix (L3 T Sl) (L3 T Sl) ℚ} {X : Matrix T T ℚ}
    {A : Matrix T Sl ℚ} (h : XARow M X A) (S : T) (b : L3 T Sl) (c : ℚ) :
    XARow (M * addMat (lY S) b c) X A := by
  intro t j
  rw [mul_addMat_apply, h t j, h.eval_y t S, mul_zero]
  by_cases hb : j = b
  · rw [if_pos hb, add_zero]
  · rw [if_neg hb, add_zero]

/-- `x → x`: the written column `lX τ` reads the column `lX σ` -/
theorem XARow.addXX {M : Matrix (L3 T Sl) (L3 T Sl) ℚ} {X : Matrix T T ℚ}
    {A : Matrix T Sl ℚ} (h : XARow M X A) (σ τ : T) (c : ℚ) :
    XARow (M * addMat (lX σ) (lX τ) c)
      (X + Matrix.of (fun (t : T) (τ' : T) => if τ' = τ then c * X t σ else 0)) A := by
  intro t j
  rw [mul_addMat_apply, h t j, h.eval_x t σ]
  rw [show (∑ σ' : T, (X + Matrix.of (fun (t : T) (τ' : T) =>
          if τ' = τ then c * X t σ else 0)) t σ' * (if j = lX σ' then (1 : ℚ) else 0))
        = (∑ σ' : T, X t σ' * (if j = lX σ' then (1 : ℚ) else 0))
          + (if j = lX τ then c * X t σ else 0) from by
      rw [← sum_delta (fun σ' : T => lX σ') (fun σ' : T => X t σ') τ (c * X t σ) j]
      exact Finset.sum_congr rfl (fun σ' _ => by rw [Matrix.add_apply, Matrix.of_apply])]
  ring

/-- `slot → x` (the K2s gate): the written column `lS q` reads the column `lX σ` — this is the
`A` update the design calls `XARow.addX` -/
theorem XARow.addXS {M : Matrix (L3 T Sl) (L3 T Sl) ℚ} {X : Matrix T T ℚ}
    {A : Matrix T Sl ℚ} (h : XARow M X A) (σ : T) (q : Sl) (c : ℚ) :
    XARow (M * addMat (lX σ) (lS q) c) X
      (A + Matrix.of (fun (t : T) (q' : Sl) => if q' = q then c * X t σ else 0)) := by
  intro t j
  rw [mul_addMat_apply, h t j, h.eval_x t σ]
  rw [show (∑ q' : Sl, (A + Matrix.of (fun (t : T) (q' : Sl) =>
          if q' = q then c * X t σ else 0)) t q' * (if j = lS q' then (1 : ℚ) else 0))
        = (∑ q' : Sl, A t q' * (if j = lS q' then (1 : ℚ) else 0))
          + (if j = lS q then c * X t σ else 0) from by
      rw [← sum_delta (fun q' : Sl => lS q') (fun q' : Sl => A t q') q (c * X t σ) j]
      exact Finset.sum_congr rfl (fun q' _ => by rw [Matrix.add_apply, Matrix.of_apply])]
  ring

/-- `x → slot`: the written column `lX τ` reads the column `lS q` (the `A` enters `X`) -/
theorem XARow.addSX {M : Matrix (L3 T Sl) (L3 T Sl) ℚ} {X : Matrix T T ℚ}
    {A : Matrix T Sl ℚ} (h : XARow M X A) (q : Sl) (τ : T) (c : ℚ) :
    XARow (M * addMat (lS q) (lX τ) c)
      (X + Matrix.of (fun (t : T) (τ' : T) => if τ' = τ then c * A t q else 0)) A := by
  intro t j
  rw [mul_addMat_apply, h t j, h.eval_s t q]
  rw [show (∑ σ' : T, (X + Matrix.of (fun (t : T) (τ' : T) =>
          if τ' = τ then c * A t q else 0)) t σ' * (if j = lX σ' then (1 : ℚ) else 0))
        = (∑ σ' : T, X t σ' * (if j = lX σ' then (1 : ℚ) else 0))
          + (if j = lX τ then c * A t q else 0) from by
      rw [← sum_delta (fun σ' : T => lX σ') (fun σ' : T => X t σ') τ (c * A t q) j]
      exact Finset.sum_congr rfl (fun σ' _ => by rw [Matrix.add_apply, Matrix.of_apply])]
  ring

/-- `slot → slot`: the written column `lS q₁` reads the column `lS q₀` -/
theorem XARow.addSS {M : Matrix (L3 T Sl) (L3 T Sl) ℚ} {X : Matrix T T ℚ}
    {A : Matrix T Sl ℚ} (h : XARow M X A) (q₀ q₁ : Sl) (c : ℚ) :
    XARow (M * addMat (lS q₀) (lS q₁) c) X
      (A + Matrix.of (fun (t : T) (q' : Sl) => if q' = q₁ then c * A t q₀ else 0)) := by
  intro t j
  rw [mul_addMat_apply, h t j, h.eval_s t q₀]
  rw [show (∑ q' : Sl, (A + Matrix.of (fun (t : T) (q' : Sl) =>
          if q' = q₁ then c * A t q₀ else 0)) t q' * (if j = lS q' then (1 : ℚ) else 0))
        = (∑ q' : Sl, A t q' * (if j = lS q' then (1 : ℚ) else 0))
          + (if j = lS q₁ then c * A t q₀ else 0) from by
      rw [← sum_delta (fun q' : Sl => lS q') (fun q' : Sl => A t q') q₁ (c * A t q₀) j]
      exact Finset.sum_congr rfl (fun q' _ => by rw [Matrix.add_apply, Matrix.of_apply])]
  ring

/-- the single add step, in `∃` form: the role hypotheses decide which of the five applies -/
theorem XARow.addMat_exists {M : Matrix (L3 T Sl) (L3 T Sl) ℚ} {X : Matrix T T ℚ}
    {A : Matrix T Sl ℚ} (h : XARow M X A) (a b : L3 T Sl) (c : ℚ)
    (hy : ∀ S : T, b = lY S → ∃ S' : T, a = lY S') :
    ∃ X' A', XARow (M * addMat a b c) X' A' := by
  rcases a with (σ | S) | q
  · rcases b with (τ | T') | q'
    · exact ⟨_, _, h.addXX σ τ c⟩
    · obtain ⟨S', hS'⟩ := hy T' rfl
      exact absurd hS' (by intro hh; cases hh)
    · exact ⟨_, _, h.addXS σ q' c⟩
  · rcases b with (τ | T') | q' <;> exact ⟨_, _, h.addY S _ c⟩
  · rcases b with (τ | T') | q'
    · exact ⟨_, _, h.addSX q τ c⟩
    · obtain ⟨S', hS'⟩ := hy T' rfl
      exact absurd hS' (by intro hh; cases hh)
    · exact ⟨_, _, h.addSS q q' c⟩

end Generic

/-! ## 2. the whole program right-multiplies onto the identity -/

section Program
variable {T Sl : Type} [Fintype T] [DecidableEq T] [Fintype Sl] [DecidableEq Sl]

/-- right multiplication by a gate product: peel the head of the list last -/
theorem XARow.mul_matP {M : Matrix (L3 T Sl) (L3 T Sl) ℚ} {X : Matrix T T ℚ}
    {A : Matrix T Sl ℚ} (h : XARow M X A) (un : Nat → L3 T Sl) (l : List (Nat × Nat × Co))
    (hy : XGateOK un l) : ∃ X' A', XARow (M * matP un (mic l)) X' A' := by
  induction l with
  | nil =>
    refine ⟨X, A, ?_⟩
    show XARow (M * 1) X A
    rw [Matrix.mul_one]
    exact h
  | cons x l ih =>
    obtain ⟨X1, A1, h1⟩ := ih (fun y hy1 => hy y (List.mem_cons_of_mem _ hy1))
    have e : matP un (mic (x :: l))
        = matP un (mic l) * addMat (un x.1) (un x.2.1) (toCoef x.2.2).val := rfl
    rw [e, ← Matrix.mul_assoc]
    exact XARow.addMat_exists h1 (un x.1) (un x.2.1) (toCoef x.2.2).val
      (hy x (List.mem_cons_self ..))

/-- right multiplication by the scatter: an x row has no y entries, so nothing moves -/
theorem XARow.mul_scatM {M : Matrix (L3 T Sl) (L3 T Sl) ℚ} {X : Matrix T T ℚ}
    {A : Matrix T Sl ℚ} (h : XARow M X A) (K : Matrix T Sl ℚ) :
    XARow (M * scatM K) X A := by
  intro t j
  have hzero : (M * embYS K) (lX t) j = 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    rcases k with (σ | S) | q
    · rw [embYS_rowX, mul_zero]
    · rw [h.eval_y t S, zero_mul]
    · rw [show embYS K (lS q) j = 0 from by simp [embYS], mul_zero]
  rw [scatM, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, hzero, add_zero, h t j]

end Program

/-! ## 3. the main phase: `∃ X A, XARow (Mt) X A` -/

section Concrete
variable {c : Raw}

theorem XGateOK.addsA (K : ScalOK c) : XGateOK (unemb c K.hv) (addsA c) := by
  intro x hx S h
  obtain ⟨h1, h2, _, h4, _⟩ := K.addA x hx
  obtain ⟨hy1, hy2⟩ := unemb_of_y K.hv x.2.1 h2 S h
  rcases h4 with h' | h' <;> exact absurd h' (by omega)

theorem XGateOK.addsB (K : ScalOK c) : XGateOK (unemb c K.hv) (addsB c) := by
  intro x hx S h
  obtain ⟨h1, h2, hne, _, h5⟩ := K.addB x hx
  obtain ⟨hy1, hy2⟩ := unemb_of_y K.hv x.2.1 h2 S h
  obtain ⟨t1, t2⟩ := h5 hy1 hy2
  exact ⟨⟨x.1 - c.v, by omega⟩, unemb_y K.hv x.1 t1 t2⟩

/-- every element of a scatter block has its target in the row range -/
theorem mem_scatAddsFrom_range {ret : List (Nat × Nat)} {rows : List (List (Nat × Co))}
    {t0 : Nat} {x : Nat × Nat × Co} (hx : x ∈ scatAddsFrom ret t0 rows) :
    t0 ≤ x.1 ∧ x.1 < t0 + rows.length := by
  induction rows generalizing t0 with
  | nil => exact absurd hx (by simp [scatAddsFrom])
  | cons l rows ih =>
    rw [scatAddsFrom, List.mem_append] at hx
    rcases hx with hx | hx
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact ⟨le_refl _, by rw [List.length_cons]; omega⟩
    · obtain ⟨h1, h2⟩ := ih hx
      exact ⟨by omega, by rw [List.length_cons]; omega⟩

theorem XGateOK.scatAdds (K : ScalOK c) (hsh : ScatShape c) :
    XGateOK (unemb c K.hv) (scatAdds c) := by
  intro x hx S _
  obtain ⟨_, hlen⟩ := hsh
  obtain ⟨h1, h2⟩ := mem_scatAddsFrom_range hx
  exact ⟨⟨x.1 - c.v, by omega⟩, unemb_y K.hv x.1 h1 (by omega)⟩

/-- **the x-rows of `Mt` carry the `(X,A)` description** -/
theorem XARow_Mt (K : ScalOK c) (hsh : ScatShape c) :
    ∃ X A, XARow (Mt c K.hv) X A := by
  have h0 : XARow (1 : Matrix (Rl c) (Rl c) ℚ) (1 : Matrix (Fin c.v) (Fin c.v) ℚ)
      (0 : Matrix (Fin c.v) (Fin c.R) ℚ) := XARow.one
  obtain ⟨X1, A1, h1⟩ := XARow.mul_matP h0 (unemb c K.hv) (addsB c) (XGateOK.addsB K)
  have h2 : XARow (MB c K.hv * scatM (Jrm c * Ccm c)) X1 A1 := by
    simpa [MB] using XARow.mul_scatM h1 (Jrm c * Ccm c)
  obtain ⟨X3, A3, h3⟩ := XARow.mul_matP h2 (unemb c K.hv) (addsA c) (XGateOK.addsA K)
  exact ⟨X3, A3, by simpa [Mt, MA, Matrix.mul_assoc] using h3⟩

/-- **the y columns of the x rows are zero** (the part of `hx` that the invariant gives free) -/
theorem mt_ycol (K : ScalOK c) (t S : Fin c.v) : Mt c K.hv (lX t) (lY S) = 0 := by
  obtain ⟨lo, n, _, _, hrun⟩ := K.hs 0 K.hv
  obtain ⟨p, a0, a1, a2, a3, hp, hi, rA, rS, hsh, rB, hsm, fx, fy⟩ := hrun
  obtain ⟨X, A, h⟩ := XARow_Mt K hsh
  exact h.eval_y t S

/-- **the x block of `Mt` is the identity**: read off `XRun.xcol`; the `(X,A)` invariant
produces the x block `X` of *every* pair, and `xcol` pins it -/
theorem mt_xcol (K : ScalOK c) (t τ : Fin c.v) :
    Mt c K.hv (lX t) (lX τ) = if t = τ then 1 else 0 := by
  obtain ⟨lo, n, hlo, hhi, hrun⟩ := K.hs τ.val τ.isLt
  exact (XRun.xcol K.hv hrun τ hlo hhi).1 t

/-- **THE KEY CANCELLATION LEMMA (route D2's residual).**  The slot block of the x rows of `Mt`
is zero: `Mt (lX t) (lS q) = 0` for every `t`, `q`.

Measured (exact rationals, `SWEEP.md` round 25, `k1_pxmps_check.py`): on the raw +8.82% ck word
(728 × 728, all `slot → x` adds present) the full `112 × 504` block `PX * Mt * PS` is exactly
zero, and `PX * Mt = PX`.  So the statement below is TRUE; it is the *proof* that is missing.

Why the `(X,A)` induction does not deliver it.  `XARow_Mt` gives an exact pair `(X,A)`, so
`A t q = Mt (lX t) (lS q)`; but `A` is *not* deducible to `0` from the invariant.  Measured:
`A` is updated only by gates with `un x.1 ∈ x`, `un x.2.1 ∈ slot` (the K2s gate, `XARow.addXS` —
224 of them in phase A, 31 in phase B of the raw word) and by `slot → slot` gates
(`XARow.addSS`, homogeneous, preserves `A = 0`).  The K2s gates make `A ≠ 0`: after phase A alone
the x rows of `MA` carry **110** nonzero slot entries (56 of the 112 rows), and after phase B the
row `lX t` of `MB` carries **368** such entries (56 rows).  The two cancel only *in the product*
`MB * MA`: `PX * MB * MA = PX` (measured; the scatter changes no x row, `XARow.mul_scatM`).
So `slotFeed = 0` is a *global* algebraic identity between phase B and the inverse of phase A —
`PX * MB = PX * MAi` (`MAi * MA = 1`, `ScalOK.hAi`) — and not a per-add fact that any induction
carrying only `(X, A)` can see.  The design's §2b/§2c claim that `slotFeed = 0` is a corollary of
§2a is, as written, false: §2c's "both updates preserve `A = 0`" holds only when `X t σ = 0`, and
the design's own `XARow.addX` has `A' t q = A t q + c * X t σ` with `X` generally nonzero.

What a successor needs is an invariant that relates `A` to *the x rows of the phase-B product*
(equivalently, that identifies the x rows of `MB` with those of `MAi`), or a new `XRun` field
(D1) certifying that every slot read by an x target is empty at read time. -/
theorem slotFeed_zero (K : ScalOK c) (t : Fin c.v) (q : Fin c.R) :
    Mt c K.hv (lX t) (lS q) = 0 := by
  sorry

/-- **renegotiated `hx`**, consuming the key lemma: `hx`'s statement is unchanged; its proof no
longer goes through `XU (Mt)` (which the K2s widening falsifies), but through the `(X,A)` invariant
(x and y blocks) plus `slotFeed_zero` (the slot block). -/
theorem hx_of_slotFeed (K : ScalOK c)
    (hA : ∀ (t : Fin c.v) (q : Fin c.R), Mt c K.hv (lX t) (lS q) = 0)
    (t : Fin c.v) (j : Rl c) :
    Mt c K.hv (lX t) j = if lX t = j then 1 else 0 := by
  rcases j with (τ | S) | q
  · obtain ⟨lo, n, hlo, hhi, hrun⟩ := K.hs τ.val τ.isLt
    have h1 := (XRun.xcol K.hv hrun τ hlo hhi).1 t
    show Mt c K.hv (lX t) (lX τ) = _
    rw [h1]
    by_cases e : t = τ
    · rw [if_pos e, e, if_pos rfl]
    · rw [if_neg e, if_neg (fun hh => e (Sum.inl.inj (Sum.inl.inj hh)))]
  · show Mt c K.hv (lX t) (lY S) = _
    rw [mt_ycol K t S, if_neg (fun hh => by cases hh)]
  · show Mt c K.hv (lX t) (lS q) = _
    rw [hA t q, if_neg (fun hh => by cases hh)]

end Concrete

#print axioms XARow.one
#print axioms XARow.addXX
#print axioms XARow.addXS
#print axioms XARow.addSX
#print axioms XARow.addSS
#print axioms XARow.addY
#print axioms XARow.addMat_exists
#print axioms XARow.mul_matP
#print axioms XARow.mul_scatM
#print axioms XGateOK.addsA
#print axioms XGateOK.addsB
#print axioms XGateOK.scatAdds
#print axioms XARow_Mt
#print axioms mt_ycol
#print axioms hx_of_slotFeed
#print axioms slotFeed_zero

end GS
