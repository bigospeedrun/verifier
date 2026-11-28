-- Coordinatewise matrix products and the one-bit Fourier frame.
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Choose.Factorization
import Submission.RAM
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Mul
set_option linter.all false

section

/-! Coordinatewise matrix products and the one-bit Fourier frame. Every `walshConj` fact comes from
`walshConj_eq_of_intertwine`: a matrix intertwining `walshMat` with a diagonal is the `walshConj` of it. -/

namespace OAI
namespace PowerSaving
open Matrix Finset

section Coordinatewise
variable {ι S : Type*} [Fintype ι] [CommSemiring S] {A B C : ι → Type*}

def digitProd (P : ∀ i, Matrix (A i) (B i) S) : Matrix (∀ i, A i) (∀ i, B i) S :=
  Matrix.of fun a b => ∏ i, P i (a i) (b i)

@[simp] theorem digitProd_apply (P : ∀ i, Matrix (A i) (B i) S) (a : ∀ i, A i) (b : ∀ i, B i) :
    digitProd P a b = ∏ i, P i (a i) (b i) := rfl

section Diag
variable [∀ i, DecidableEq (A i)] [DecidableEq (∀ i, A i)]

/-- A product of guarded factors is `∏ g` when every guard holds, i.e. when `a = b`, and `0` otherwise. -/
theorem prod_ite_eqs (a b : ∀ i, A i) (g : ι → S) :
    ∏ i, (if a i = b i then g i else 0) = if a = b then ∏ i, g i else 0 := by
  rw [Finset.prod_ite_zero]
  exact if_congr (by simp [funext_iff]) rfl rfl

theorem prod_delta (a b : ∀ i, A i) :
    ∏ i, (if a i = b i then (1:S) else 0) = if a = b then 1 else 0 := by
  rw [prod_ite_eqs, prod_const_one]

theorem digitProd_diagonal (w : ∀ i, A i → S) :
    digitProd (fun i => diagonal (w i)) = diagonal (fun a => ∏ i, w i (a i)) := by
  ext a b
  rw [digitProd_apply, diagonal_apply, ← prod_ite_eqs]
  exact prod_congr rfl fun i _ => diagonal_apply _ _ _

theorem digitProd_one : digitProd (fun i => (1 : Matrix (A i) (A i) S)) = 1 := by
  simpa only [diagonal_one, prod_const_one] using digitProd_diagonal (fun (i : ι) (_ : A i) => (1:S))

end Diag

theorem digitProd_smul (c : ι → S) (P : ∀ i, Matrix (A i) (B i) S) :
    digitProd (fun i => c i • P i) = (∏ i, c i) • digitProd P := by
  ext a b
  simp only [digitProd_apply, smul_apply, smul_eq_mul, prod_mul_distrib]

theorem digitProd_mul [∀ i, Fintype (B i)] [DecidableEq ι]
    (P : ∀ i, Matrix (A i) (B i) S) (Q : ∀ i, Matrix (B i) (C i) S) :
    digitProd P * digitProd Q = digitProd (fun i => P i * Q i) := by
  ext a c
  simp only [mul_apply, digitProd_apply]
  rw [Finset.prod_univ_sum]
  exact Fintype.sum_congr _ _ fun t => (prod_mul_distrib).symm

end Coordinatewise

end PowerSaving
end OAI

namespace OAI
namespace PowerSaving.Binary
open Finset Matrix

abbrev F := ZMod 2
abbrev Space (α : Type*) := α → F

lemma bit_cases (x : F) : x=0 ∨ x=1 :=
  match x with
  | 0 => .inl rfl
  | 1 => .inr rfl

@[simp] theorem cancel (x : F) : x+x=0 := CharTwo.add_self_eq_zero x

@[simp] theorem binary_cancel {α : Type*} (x : Space α) : x+x=0 := funext fun i => cancel (x i)

section Dot
variable {α : Type*} [Fintype α]

def dot (x y : Space α) : F := x ⬝ᵥ y

@[simp] theorem dot_add_left (x y z : Space α) :
    dot (x+y) z = dot x z + dot y z := add_dotProduct x y z

@[simp] theorem dot_add_right (x y z : Space α) :
    dot x (y+z) = dot x y + dot x z := dotProduct_add x y z

@[simp] theorem dot_zero_left (x : Space α) : dot 0 x = 0 := zero_dotProduct x

variable [DecidableEq α]

def eu (i : α) : Space α := fun j => if i=j then 1 else 0

@[simp] theorem dot_eu_left (x : Space α) (i : α) : dot (eu i) x = x i := by
  have h : eu i = Pi.single i 1 := funext fun j => by simp [eu, Pi.single_apply, eq_comm]
  rw [dot, h, single_dotProduct, one_mul]

end Dot

end PowerSaving.Binary
end OAI

namespace OAI
namespace PowerSaving.Binary
open Matrix Finset Complex
noncomputable section

/-- The sign character `(-1)^i` and the quarter-turn character `I^i` of a bit. -/
def sign (i : F) : ℂ := if i=0 then 1 else -1
def phaseI (i : F) : ℂ := if i=0 then 1 else I

theorem one_ne : (1:F) ≠ 0 := by decide

lemma sumF {M : Type*} [AddCommMonoid M] (f : F → M) : ∑ i, f i = f 0 + f 1 := Fin.sum_univ_two f

private lemma forall_bit {P : F → Prop} (h0 : P 0) (h1 : P 1) : ∀ i, P i := by
  intro i; rcases bit_cases i with rfl | rfl <;> assumption

private lemma sign_zero_val : sign 0 = 1 := if_pos rfl
private lemma sign_one_val : sign 1 = -1 := if_neg one_ne
private lemma phaseI_zero_val : phaseI 0 = 1 := if_pos rfl
private lemma phaseI_one_val : phaseI 1 = I := if_neg one_ne
private lemma bit_one_mul_one : (1:F) * 1 = 1 := rfl

lemma sign_add (i j : F) : sign (i+j) = sign i * sign j := by
  revert i j
  refine forall_bit (fun j => by simp [sign]) (forall_bit ?_ ?_)
  · simp [sign]
  · rw [CharTwo.add_self_eq_zero, sign_one_val]; simp [sign]

lemma phaseI_sq (i : F) : phaseI i * phaseI i = sign i := by
  revert i
  refine forall_bit (by simp [phaseI, sign]) ?_
  rw [phaseI_one_val, sign_one_val, I_mul_I]

lemma sign_sum {α : Type*} (v : α → F) (s : Finset α) :
    sign (∑ i ∈ s, v i) = ∏ i ∈ s, sign (v i) := by
  classical
  refine Finset.induction_on s (by simp [sign]) fun a t ha ih => ?_
  rw [sum_insert ha, prod_insert ha, sign_add, ih]

variable {α : Type*} [Fintype α]

def phaseProd (x : Space α) : ℂ := ∏ i, phaseI (x i)

def littleH : Matrix F F ℂ := fun i j => sign (i*j)
def ca : ℂ := (1+I)/2
def cb : ℂ := (1-I)/2
def littleC : Matrix F F ℂ := fun i j => if i=j then ca else cb

private lemma ca_cb_sign (t : F) : ca + cb * sign t = phaseI t := by
  revert t
  refine forall_bit ?_ ?_
  · rw [sign_zero_val, phaseI_zero_val, ca, cb]; ring
  · rw [sign_one_val, phaseI_one_val, ca, cb]; ring

abbrev CMat (α : Type*) := Matrix (Space α) (Space α) ℂ
def rippleMat (α : Type*) [Fintype α] : CMat α := digitProd fun _ => littleC
def walshMat (α : Type*) [Fintype α] : CMat α := digitProd fun _ => littleH

private lemma walshMat_entry (x y : Space α) : walshMat α x y = sign (dot x y) := by
  rw [walshMat, digitProd_apply, dot, dotProduct, sign_sum]; rfl

variable [DecidableEq α]

private lemma littleH_sq : littleH * littleH = (2:ℂ) • 1 := by
  ext i k
  rw [mul_apply, sumF, smul_apply, one_apply]
  revert i k
  refine forall_bit (forall_bit ?_ ?_) (forall_bit ?_ ?_) <;>
    simp [littleH, sign] <;> norm_num

/-- The Hadamard frame squares to `2^|α|`. -/
private lemma walshMat_sq : walshMat α * walshMat α = ((2:ℂ) ^ Fintype.card α) • 1 := by
  rw [walshMat, digitProd_mul]
  simp only [littleH_sq]
  rw [digitProd_smul (fun _ => (2:ℂ)), digitProd_one, prod_const, card_univ]

private lemma two_pow_ne : ((2:ℂ) ^ Fintype.card α) ≠ 0 := pow_ne_zero _ two_ne_zero

def walshConj (f : Space α → ℂ) : CMat α :=
  ((2:ℂ) ^ Fintype.card α)⁻¹ • (walshMat α * diagonal f * walshMat α)

private lemma walshConj_walshMat (f : Space α → ℂ) : walshConj f * walshMat α = walshMat α * diagonal f := by
  rw [walshConj, smul_mul, Matrix.mul_assoc _ (walshMat α), walshMat_sq, Matrix.mul_smul, Matrix.mul_one, smul_smul,
    inv_mul_cancel₀ two_pow_ne, one_smul]

/-- A matrix `M` with `M * walshMat = walshMat * diagonal f` is `walshConj f`. -/
theorem walshConj_eq_of_intertwine {M : CMat α} {f : Space α → ℂ}
    (h : M * walshMat α = walshMat α * diagonal f) : walshConj f = M := by
  rw [walshConj, ← h, Matrix.mul_assoc, walshMat_sq, Matrix.mul_smul, Matrix.mul_one, smul_smul,
    inv_mul_cancel₀ two_pow_ne, one_smul]

lemma walshConj_one : walshConj (fun _ : Space α => 1) = 1 :=
  walshConj_eq_of_intertwine (by rw [diagonal_one, Matrix.one_mul, Matrix.mul_one])

lemma walshConj_mul (f g : Space α → ℂ) :
    walshConj f * walshConj g = walshConj fun x => f x * g x := by
  refine (walshConj_eq_of_intertwine ?_).symm
  rw [Matrix.mul_assoc, walshConj_walshMat, ← Matrix.mul_assoc, walshConj_walshMat, Matrix.mul_assoc,
    diagonal_mul_diagonal]

lemma walshConj_phaseProd : walshConj (phaseProd : Space α → ℂ) = rippleMat α := by
  refine walshConj_eq_of_intertwine ?_
  have h1 : littleC * littleH = littleH * diagonal phaseI := by
    ext i k
    rw [mul_apply, sumF, mul_diagonal]
    revert i k
    refine forall_bit (forall_bit ?_ ?_) (forall_bit ?_ ?_) <;>
      simp only [littleC, littleH, mul_zero, zero_mul, bit_one_mul_one, sign_zero_val, sign_one_val,
        phaseI_zero_val, phaseI_one_val, ite_true, if_neg one_ne, if_neg one_ne.symm, ca, cb] <;> ring
  have h2 : diagonal (phaseProd : Space α → ℂ) = digitProd (fun _ : α => diagonal phaseI) :=
    (digitProd_diagonal _).symm
  rw [h2, rippleMat, walshMat, digitProd_mul, digitProd_mul]
  simp only [h1]

def shift (z : Space α) : CMat α :=
  fun i j => if i+z = j then 1 else 0

def dir (z : Space α) : CMat α := ca • 1 + cb • shift z

lemma dir_phase (z : Space α) : dir z = walshConj (fun x => phaseI (dot z x)) := by
  refine (walshConj_eq_of_intertwine ?_).symm
  ext i j
  have hs : (shift z * walshMat α) i j = walshMat α (i + z) j := by
    rw [mul_apply, sum_eq_single (i + z) (fun k _ hk => by simp [shift, Ne.symm hk])
      (fun h => absurd (mem_univ _) h)]
    simp [shift]
  rw [dir, Matrix.add_mul, smul_mul, smul_mul, Matrix.one_mul, add_apply, smul_apply, smul_apply,
    hs, mul_diagonal, walshMat_entry, walshMat_entry, dot_add_left, sign_add, smul_eq_mul, smul_eq_mul,
    ← ca_cb_sign]
  ring

end
end PowerSaving.Binary
end OAI

namespace OAI
namespace PowerSaving.ReelKit
open Finset

theorem sum_blocks {M : Type*} [AddCommMonoid M] (q b : ℕ) (f : ℕ → M) :
    ∑ i ∈ range (q*b), f i = ∑ j ∈ range q, ∑ i ∈ range b, f (j*b + i) := by
  rw [← Fin.sum_univ_eq_sum_range, ← finProdFinEquiv.sum_comp, Fintype.sum_prod_type,
    ← Fin.sum_univ_eq_sum_range]
  refine Fintype.sum_congr _ _ fun j => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun i => f (j*b + i))]
  exact Fintype.sum_congr _ _ fun i => by simp [finProdFinEquiv, add_comm, mul_comm]

end PowerSaving.ReelKit
end OAI
end
