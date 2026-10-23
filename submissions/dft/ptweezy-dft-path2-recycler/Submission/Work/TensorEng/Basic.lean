import Submission.Work.Mixed.HeadM1
import Submission.Work.GFrame.Engine.Free

/-!
# T1 (tensor product of certified words), part 1: Kronecker directions, digit maps, transported matrices

Compiled read-only against the leader's engine (`Submission.*` oleans of the frozen retune tree).

For a family `w : J → Space β` (a basis of `Space β` when `|J| = |β|` and `w` is independent) the digit map
`Ψ_w y = ∑_j y_j ⊗ w_j : (J → Space α) → Space (α × β)` is an additive bijection (`psiEquiv`).  A matrix on digit
tuples is transported to `Space (α × β)` by `trp`.  The matrices of the leader's letters, acting on the digits of
`D ⊆ J` only (`dop D A`), transport to matrices of letters of the product label space:

* `trp_dop_shift` : a digitwise shift is ONE shift;
* `trp_dop_dir_single` : `dir z` on one digit `d` is `dir (z ⊗ w_d)`.

-- changed for the tensor-power extension (30103/10000000); see Submission.lean
-/

namespace TensorEng
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.GF Matrix Finset

noncomputable section

section Digits
variable {α β J : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype J] [DecidableEq J]

/-- Kronecker vector `z ⊗ t ∈ Space (α × β)`. -/
def kron (z : Space α) (t : Space β) : Space (α × β) := fun p => z p.1 * t p.2

/-- The digit map `Ψ_w y = ∑_j y_j ⊗ w_j`. -/
def psi (w : J → Space β) (y : J → Space α) : Space (α × β) := fun p => ∑ j, y j p.1 * w j p.2

lemma psi_add (w : J → Space β) (y y' : J → Space α) : psi w (y + y') = psi w y + psi w y' := by
  funext p
  simp only [psi, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma psi_single (w : J → Space β) (d : J) (z : Space α) : psi w (Pi.single d z) = kron z (w d) := by
  funext p
  simp only [psi, kron]
  rw [Finset.sum_eq_single d]
  · simp
  · intro j _ hj
    simp [hj]
  · intro h; exact absurd (Finset.mem_univ d) h

lemma psi_injective (w : J → Space β) (hw : LinearIndependent F w) :
    Function.Injective (psi (α := α) w) := by
  intro y y' h
  funext j a
  have hrow : ∑ k, (y k a - y' k a) • w k = 0 := by
    funext b
    have hb := congr_fun h (a, b)
    simp only [psi] at hb
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib, hb, sub_self,
      Pi.zero_apply]
  have := Fintype.linearIndependent_iff.1 hw (fun k => y k a - y' k a) hrow j
  exact sub_eq_zero.1 this

lemma psi_bijective (w : J → Space β) (hw : LinearIndependent F w) (hJ : Fintype.card J = Fintype.card β) :
    Function.Bijective (psi (α := α) w) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨psi_injective w hw, ?_⟩
  simp only [Fintype.card_fun, Fintype.card_prod, ZMod.card, hJ]
  ring

/-- The digit map of a basis as an equivalence. -/
def psiEquiv (w : J → Space β) (hw : LinearIndependent F w) (hJ : Fintype.card J = Fintype.card β) :
    (J → Space α) ≃ Space (α × β) :=
  Equiv.ofBijective _ (psi_bijective w hw hJ)

@[simp] lemma psiEquiv_apply (w : J → Space β) (hw : LinearIndependent F w)
    (hJ : Fintype.card J = Fintype.card β) (y : J → Space α) : psiEquiv w hw hJ y = psi w y := rfl

/-! ### operators on chosen digits -/

/-- `A` on the digits of `D`, the identity on the others. -/
def dop (D : Finset J) (A : CMat α) : Matrix (J → Space α) (J → Space α) ℂ :=
  digitProd (fun j => if j ∈ D then A else (1 : CMat α))

lemma dop_mul (D : Finset J) (A B : CMat α) : dop D A * dop D B = dop D (A * B) := by
  unfold dop
  rw [digitProd_mul]
  congr 1
  funext j
  split_ifs <;> simp

lemma dop_one (D : Finset J) : dop D (1 : CMat α) = 1 := by
  unfold dop
  simp only [ite_self]
  exact digitProd_one

/-- On a single digit, `dop` is linear. -/
lemma dop_single_lin (d : J) (a b : ℂ) (A B : CMat α) :
    dop {d} (a • A + b • B) = a • dop {d} A + b • dop {d} B := by
  ext y y'
  simp only [dop, Matrix.add_apply, Matrix.smul_apply, digitProd_apply, smul_eq_mul, Finset.mem_singleton]
  rw [Fintype.prod_eq_mul_prod_compl d (fun j => (if j = d then a • A + b • B else (1 : CMat α)) (y j) (y' j)),
    Fintype.prod_eq_mul_prod_compl d (fun j => (if j = d then A else (1 : CMat α)) (y j) (y' j)),
    Fintype.prod_eq_mul_prod_compl d (fun j => (if j = d then B else (1 : CMat α)) (y j) (y' j))]
  beta_reduce
  have hrest : ∀ N : J → CMat α, (∀ j, j ≠ d → N j = 1) →
      ∏ j ∈ ({d}ᶜ : Finset J), N j (y j) (y' j) = ∏ j ∈ ({d}ᶜ : Finset J), (1 : CMat α) (y j) (y' j) := by
    intro N hN
    apply Finset.prod_congr rfl
    intro j hj
    rw [Finset.mem_compl, Finset.mem_singleton] at hj
    rw [hN j hj]
  rw [hrest (fun j => if j = d then a • A + b • B else 1) (fun j hj => by simp [hj]),
    hrest (fun j => if j = d then A else 1) (fun j hj => by simp [hj]),
    hrest (fun j => if j = d then B else 1) (fun j hj => by simp [hj])]
  rw [if_pos rfl, if_pos rfl, if_pos rfl]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-! ### transport along a bijection of the labels -/

/-- Transport of a matrix along a bijection of its label set. -/
def trp {γ δ : Type*} (E : γ ≃ δ) (M : Matrix γ γ ℂ) : Matrix δ δ ℂ := M.submatrix E.symm E.symm

lemma trp_apply {γ δ : Type*} (E : γ ≃ δ) (M : Matrix γ γ ℂ) (x y : δ) :
    trp E M x y = M (E.symm x) (E.symm y) := rfl

lemma trp_mul {γ δ : Type*} [Fintype γ] [Fintype δ] (E : γ ≃ δ) (M N : Matrix γ γ ℂ) :
    trp E (M * N) = trp E M * trp E N := by
  unfold trp
  rw [submatrix_mul_equiv]

lemma trp_one {γ δ : Type*} [DecidableEq γ] [DecidableEq δ] (E : γ ≃ δ) :
    trp E (1 : Matrix γ γ ℂ) = 1 :=
  submatrix_one_equiv _

lemma trp_add {γ δ : Type*} (E : γ ≃ δ) (M N : Matrix γ γ ℂ) : trp E (M + N) = trp E M + trp E N := rfl

lemma trp_smul {γ δ : Type*} (E : γ ≃ δ) (c : ℂ) (M : Matrix γ γ ℂ) : trp E (c • M) = c • trp E M := rfl

lemma trp_mulVec {γ δ : Type*} [Fintype γ] [Fintype δ] (E : γ ≃ δ) (M : Matrix γ γ ℂ) (x : δ → ℂ) :
    trp E M *ᵥ x = (M *ᵥ (x ∘ E)) ∘ E.symm := by
  unfold trp
  rw [submatrix_mulVec_equiv, Equiv.symm_symm]

/-! ### the leader's letters, transported -/

/-- A digitwise shift is ONE shift of the product label space. -/
lemma trp_dop_shift {δ : Type*} [Fintype δ] [DecidableEq δ] (E : (J → Space α) ≃ Space δ)
    (hE : ∀ y y', E (y + y') = E y + E y') (D : Finset J) (z : Space α) :
    trp E (dop D (Binary.shift z)) = Binary.shift (E (fun j => if j ∈ D then z else 0)) := by
  set v : J → Space α := fun j => if j ∈ D then z else 0 with hv
  ext x y
  rw [trp_apply, dop, digitProd_apply]
  have h1 : ∀ j, (if j ∈ D then Binary.shift z else (1 : CMat α)) (E.symm x j) (E.symm y j)
      = if (E.symm x + v) j = E.symm y j then (1 : ℂ) else 0 := by
    intro j
    by_cases hj : j ∈ D
    · rw [if_pos hj]
      simp [Binary.shift, hv, hj]
    · rw [if_neg hj]
      simp [hv, hj, Matrix.one_apply]
  rw [Finset.prod_congr rfl (fun j _ => h1 j), OAI.PowerSaving.prod_delta]
  show _ = (if x + E v = y then (1 : ℂ) else 0)
  have h2 : (E.symm x + v = E.symm y) ↔ (x + E v = y) := by
    constructor
    · intro h
      have := congrArg E h
      rw [hE, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
      exact this
    · intro h
      apply E.injective
      rw [hE, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact h
  by_cases h : x + E v = y
  · rw [if_pos (h2.2 h), if_pos h]
  · rw [if_neg (fun h' => h (h2.1 h')), if_neg h]

/-- `dir z` on one digit `d` is `dir (Ψ (single d z))`; for `Ψ = psiEquiv w` this is `dir (z ⊗ w_d)`. -/
lemma trp_dop_dir_single {δ : Type*} [Fintype δ] [DecidableEq δ] (E : (J → Space α) ≃ Space δ)
    (hE : ∀ y y', E (y + y') = E y + E y') (d : J) (z : Space α) :
    trp E (dop {d} (dir z)) = dir (E (Pi.single d z)) := by
  have hdir : dir z = ca • (1 : CMat α) + cb • Binary.shift z := rfl
  rw [hdir, dop_single_lin, dop_one, trp_add, trp_smul, trp_smul, trp_one, trp_dop_shift E hE]
  have hv : (fun j => if j ∈ ({d} : Finset J) then z else 0) = (Pi.single d z : J → Space α) := by
    funext j
    by_cases h : j = d
    · subst h; simp
    · simp [h]
  rw [hv]
  rfl

lemma trp_dop_dir_kron (w : J → Space β) (hw : LinearIndependent F w) (hJ : Fintype.card J = Fintype.card β)
    (d : J) (z : Space α) :
    trp (psiEquiv w hw hJ) (dop {d} (dir z)) = dir (kron z (w d)) := by
  rw [trp_dop_dir_single _ (fun y y' => psi_add w y y'), psiEquiv_apply, psi_single]

end Digits

end

end TensorEng
