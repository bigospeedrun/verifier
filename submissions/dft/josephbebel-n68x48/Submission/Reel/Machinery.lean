--might be  containing modified Apache-2.0 codes pieces from one or several sources; notices and credits: Credits.lean
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Choose.Factorization
import Submission.Compiler.Layout
import Submission.Algebra.DFTIdentities

namespace OAI
namespace PowerSaving
open Matrix Finset
variable {J : Type*} [Fintype J]
variable {κ : J → Type*} {μ : J → Type*} {ν : J → Type*}
variable {R : Type*} [CommSemiring R]

def digitProd (M : ∀ j, Matrix (κ j) (μ j) R) :
    Matrix ((j:J) → κ j) ((j:J) → μ j) R :=
  fun x y => ∏ j, M j (x j) (y j)

@[simp] theorem digitProd_apply (M : ∀ j, Matrix (κ j) (μ j) R) x y :
    digitProd M x y = ∏ j, M j (x j) (y j) := rfl

theorem prod_ite_eqs [∀ j, DecidableEq (κ j)] [DecidableEq ((j:J) → κ j)]
    (x y : (j:J) → κ j) (f : J → R) :
    ∏ j:J, (if x j = y j then f j else 0) = if x=y then ∏ j, f j else 0 := by
  split_ifs with h
  · subst h; simp
  · obtain ⟨j, hj⟩ := Function.ne_iff.mp h
    exact prod_eq_zero (mem_univ j) (if_neg hj)

theorem prod_delta [∀ j, DecidableEq (κ j)] [DecidableEq ((j:J) → κ j)]
    (x y : (j:J) → κ j) :
    ∏ j:J, (if x j = y j then (1:R) else 0)
    = if x=y then 1 else 0 := by simpa using prod_ite_eqs x y fun _ => (1:R)

theorem digitProd_one [∀ j, DecidableEq (κ j)] [DecidableEq ((j:J) → κ j)] :
    digitProd (fun j:J => (1:Matrix (κ j) (κ j) R)) = 1 := by
  ext x y; simp only [digitProd_apply, one_apply]; exact prod_delta x y

theorem digitProd_diagonal [∀ j, DecidableEq (κ j)] [DecidableEq ((j:J) → κ j)]
    (d : ∀ j, κ j → R) :
    digitProd (fun j => Matrix.diagonal (d j))
      = Matrix.diagonal (fun x => ∏ j, d j (x j)) := by
  ext x y; simp only [digitProd_apply, diagonal_apply]; exact prod_ite_eqs x y _

theorem digitProd_mul [∀ j, Fintype (μ j)] [DecidableEq J]
    (M : ∀ j, Matrix (κ j) (μ j) R) (N : ∀ j, Matrix (μ j) (ν j) R) :
    digitProd M * digitProd N = digitProd (fun j => M j * N j) := by
  ext x z; simp only [mul_apply, digitProd_apply, Fintype.prod_sum, prod_mul_distrib]

end PowerSaving
end OAI

namespace OAI
namespace PowerSaving.Binary
open Finset Matrix

abbrev F := ZMod 2
abbrev Space (α : Type*) := α → F

lemma bit_cases (x : F) : x=0 ∨ x=1 := by revert x; decide

@[simp] theorem cancel (x : F) : x+x=0 := by revert x; decide

@[simp] theorem binary_cancel {α : Type*} (x : Space α) : x+x=0 := funext fun i => cancel (x i)

section Dot
variable {α : Type*} [Fintype α]

def dot (x y : Space α) := ∑ i : α, x i * y i

theorem dot_symm (x y : Space α) : dot x y = dot y x := by simp [dot, mul_comm]

@[simp] theorem dot_add_left (x y z : Space α) :
    dot (x+y) z = dot x z + dot y z := by simp [dot, add_mul, sum_add_distrib]

@[simp] theorem dot_add_right (x y z : Space α) :
    dot x (y+z) = dot x y + dot x z := by simp [dot, mul_add, sum_add_distrib]

@[simp] theorem dot_smul_left (a : F) (x y : Space α) :
    dot (a • x) y = a * dot x y := by simp [dot, mul_sum, mul_assoc]

@[simp] theorem dot_smul_right (a : F) (x y : Space α) :
    dot x (a • y) = a * dot x y := by simp [dot, mul_sum, mul_left_comm]

@[simp] theorem dot_zero_left (x : Space α) : dot 0 x = 0 := by simp [dot]

theorem dot_sum {β : Type*} (x : Space α) (s : Finset β) (f : β → Space α) :
    dot x (∑ j ∈ s, f j) = ∑ j ∈ s, dot x (f j) := by
  simp only [dot, Finset.sum_apply, mul_sum]; exact sum_comm

variable [DecidableEq α]

def eu (i : α) : Space α := fun j => if i=j then 1 else 0

@[simp] theorem dot_eu_left (x : Space α) (i : α) : dot (eu i) x = x i := by simp [dot, eu]

@[simp] theorem dot_eu_right (x : Space α) (i : α) : dot x (eu i) = x i := by simp [dot, eu]

end Dot

structure OBase (α : Type*) [Fintype α] [DecidableEq α] where
  v : α → Space α
  rows : ∀ i j, dot (v i) (v j) = if i=j then 1 else 0

namespace OBase
variable {α : Type*} [Fintype α] [DecidableEq α]

@[simp] theorem self (A : OBase α) (i : α) : dot (A.v i) (A.v i)=1 := by simpa using A.rows i i

def canonical (α : Type*) [Fintype α] [DecidableEq α] : OBase α :=
  ⟨eu, fun i j => by simp [eu]⟩

def mat (A : OBase α) (s : Finset α) : Matrix α α F :=
  fun i j => ∑ k ∈ s, A.v k i * A.v k j

@[simp] theorem mat_univ (A : OBase α) : A.mat univ = 1 := by
  let V : Matrix α α F := Matrix.of fun k i => A.v k i
  have h : V * Vᵀ = 1 := by ext i j; simpa [V, mul_apply, dot, one_apply] using A.rows i j
  have h' : Vᵀ * V = 1 := mul_eq_one_comm.mp h
  ext i j; simpa [V, mat, mul_apply, one_apply] using congrFun (congrFun h' i) j

theorem mat_sub (A : OBase α) (s t : Finset α) (h : t ⊆ s) :
    A.mat (s \ t) = A.mat s - A.mat t := by ext; simp [mat, sum_sdiff_eq_sub h]

def proj (A : OBase α) (s : Finset α) (x : Space α) : Space α :=
  ∑ k ∈ s, dot (A.v k) x • A.v k

theorem proj_apply (A : OBase α) (s : Finset α) (x : Space α) (i : α) :
    A.proj s x i = ∑ j, A.mat s i j*x j := by
  simp only [proj, mat, dot, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sum_mul]
  rw [sum_comm]; exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

@[simp] theorem proj_univ (A : OBase α) (x : Space α) : A.proj univ x = x := by
  funext i; simp [proj_apply, one_apply]

section Adapt
def tv (w x : Space α) := x + dot w x • w

omit [DecidableEq α] in
lemma tv_isom (w x y : Space α) (h : dot w w = 0) : dot (tv w x) (tv w y) = dot x y := by
  simp only [tv, dot_add_left, dot_add_right, dot_smul_left, dot_smul_right, h, dot_symm x w]
  linear_combination cancel (dot w x * dot w y)

def acted (A : OBase α) (w : Space α) (h : dot w w=0) : OBase α :=
  ⟨fun i => tv w (A.v i), fun i j => by rw [tv_isom _ _ _ h]; apply A.rows⟩

def adapt (A : OBase α) (i : α) (t : Space α) (h1 : dot t t=1)
    (h2 : dot t (A.v i) = 0) : OBase α :=
  acted A (t + A.v i) (by simp [h1, h2, dot_symm (A.v i) t])

theorem adapt_pivot (A : OBase α) (i : α) (t : Space α)
    (h1 : dot t t=1) (h2 : dot t (A.v i) = 0) :
    (adapt A i t h1 h2).v i = t := by
  show A.v i + dot (t + A.v i) (A.v i) • (t + A.v i) = t
  rw [dot_add_left, h2, A.self, zero_add, one_smul, add_comm t, ← add_assoc, binary_cancel, zero_add]

end Adapt
end OBase
end PowerSaving.Binary
end OAI

namespace OAI
namespace PowerSaving.Binary
open Matrix Finset Complex
noncomputable section

def sign (i : F) : ℂ := if i=0 then 1 else -1
def tint (i : F) : ℂ := if i=0 then 1 else I

theorem one_ne : (1:F) ≠ 0 := by decide

lemma sumF {M : Type*} [AddCommMonoid M] (f : F → M) : ∑ i, f i = f 0 + f 1 := Fin.sum_univ_two f

lemma sign_add (i j : F) : sign (i+j) = sign i * sign j := by
  rcases bit_cases i with rfl|rfl <;> rcases bit_cases j with rfl|rfl <;> simp [sign, one_ne]

lemma sign_sq (i : F) : sign i * sign i = 1 := by
  rcases bit_cases i with rfl|rfl <;> simp [sign]

lemma tint_sq (i : F) : tint i * tint i = sign i := by
  rcases bit_cases i with rfl|rfl <;> simp [tint, sign, one_ne]

lemma sign_sum {α : Type*} (v : α → F) (s : Finset α) :
    sign (∑ i ∈ s, v i) = ∏ i ∈ s, sign (v i) := by
  induction s using Finset.cons_induction with
  | empty => simp [sign]
  | cons a s h ih => rw [sum_cons, prod_cons, sign_add, ih]

variable {α : Type*} [Fintype α]

def lum (x : Space α) : ℂ := ∏ i, tint (x i)

@[simp] lemma lum_zero : lum (0 : Space α) = 1 := by simp [lum, tint]

lemma lum_add (x y : Space α) :
    lum (x+y) = lum x * lum y * sign (dot x y) := by
  simp only [lum, dot, sign_sum, ← prod_mul_distrib, Pi.add_apply]
  exact prod_congr rfl fun i _ => by
    rcases bit_cases (x i) with h|h <;> rcases bit_cases (y i) with g|g <;> simp [h, g, tint, sign, one_ne]

lemma lum_sq (x : Space α) : lum x * lum x = sign (dot x x) := by
  simp only [lum, dot, sign_sum, ← prod_mul_distrib]
  exact prod_congr rfl fun i _ => by rcases bit_cases (x i) with h|h <;> simp [h, tint, sign, one_ne]

lemma lum_nonzero (x : Space α) : lum x ≠ 0 :=
  prod_ne_zero_iff.mpr fun i _ => by unfold tint; split <;> simp [I_ne_zero]

lemma lum_of_unit (x : Space α) (h : dot x x=1) :
    lum x = I ∨ lum x = -I := by
  have e := lum_sq x
  rw [h] at e; simp only [sign, one_ne, if_false] at e
  rcases mul_eq_zero.mp (show (lum x - I) * (lum x - -I) = 0 by linear_combination e - I_sq) with g|g
  · exact .inl (sub_eq_zero.mp g)
  · exact .inr (sub_eq_zero.mp g)

def littleH : Matrix F F ℂ := fun i j => sign (i*j)
def littleH' : Matrix F F ℂ := fun i j => sign (i*j)/2
def ca : ℂ := (1+I)/2
def cb : ℂ := (1-I)/2
def littleC : Matrix F F ℂ := fun i j => if i=j then ca else cb

lemma little_phase :
    littleC * littleH = littleH * diagonal tint := by
  ext i j; rw [mul_apply, sumF, mul_diagonal]
  rcases bit_cases i with rfl|rfl <;> rcases bit_cases j with rfl|rfl <;>
    simp [littleC, littleH, sign, tint, ca, cb, one_ne] <;> ring

abbrev CMat (α : Type*) := Matrix (Space α) (Space α) ℂ
def kernel (α : Type*) [Fintype α] : CMat α := digitProd fun _ => littleC
def wal (α : Type*) [Fintype α] : CMat α := digitProd fun _ => littleH
def walI (α : Type*) [Fintype α] : CMat α := digitProd fun _ => littleH'

lemma wal_apply (x y : Space α) : wal α x y = sign (dot x y) := by
  simp [wal, littleH, dot, sign_sum]

variable [DecidableEq α]

lemma little_inv : littleH * littleH' = 1 ∧ littleH' * littleH = 1 := by
  constructor <;> ext i j <;> rw [mul_apply, sumF] <;>
  rcases bit_cases i with rfl|rfl <;> rcases bit_cases j with rfl|rfl <;>
    simp [littleH, littleH', sign, one_ne] <;> norm_num

lemma wal_right (α : Type*) [Fintype α] [DecidableEq α] :
    wal α * walI α = 1 := by rw [wal, walI, digitProd_mul]; simp only [little_inv.1]; exact digitProd_one

lemma wal_left (α : Type*) [Fintype α] [DecidableEq α] :
    walI α * wal α = 1 := by rw [wal, walI, digitProd_mul]; simp only [little_inv.2]; exact digitProd_one

def wrap (f : Space α → ℂ) : CMat α := wal α * diagonal f * walI α

lemma wrap_of (M : CMat α) (f : Space α → ℂ)
    (h : M * wal α = wal α * diagonal f) : wrap f = M := by
  rw [wrap, ← h, Matrix.mul_assoc, wal_right, Matrix.mul_one]

lemma wrap_wal (f : Space α → ℂ) : wrap f * wal α = wal α * diagonal f := by
  rw [wrap, Matrix.mul_assoc, wal_left, Matrix.mul_one]

lemma wrap_one : wrap (fun _ : Space α => 1) = 1 := wrap_of _ _ (by rw [diagonal_one]; simp)

lemma wrap_mul (f g : Space α → ℂ) :
    wrap f * wrap g = wrap fun x => f x * g x := by
  refine (wrap_of _ _ ?_).symm
  rw [Matrix.mul_assoc, wrap_wal, ← Matrix.mul_assoc, wrap_wal, Matrix.mul_assoc,
    diagonal_mul_diagonal]

lemma wrap_comm (f g : Space α → ℂ) : wrap f * wrap g = wrap g * wrap f := by
  simp only [wrap_mul, mul_comm]

lemma wrap_lum : wrap (lum : Space α → ℂ) = kernel α := by
  apply wrap_of
  rw [show diagonal (lum : Space α → ℂ) = digitProd (fun _ => diagonal tint) from
    (digitProd_diagonal _).symm, kernel, wal, digitProd_mul, digitProd_mul]
  simp only [little_phase]

def shift (z : Space α) : CMat α :=
  fun i j => if i+z = j then 1 else 0

lemma shift_phase (z : Space α) : shift z = wrap (fun x => sign (dot z x)) := by
  refine (wrap_of _ _ ?_).symm
  ext i j; rw [mul_diagonal, mul_apply]; simp [shift, wal_apply, sign_add]

lemma shift_sq (z : Space α) : shift z * shift z = 1 := by
  rw [shift_phase, wrap_mul, ← wrap_one]; simp only [sign_sq]

def dir (z : Space α) : CMat α := ca • 1 + cb • shift z

lemma dir_phase (z : Space α) : dir z = wrap (fun x => tint (dot z x)) := by
  refine (wrap_of _ _ ?_).symm
  rw [dir, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, shift_phase, wrap_wal]
  ext i j; simp only [Matrix.add_apply, Matrix.smul_apply, mul_diagonal, smul_eq_mul]
  rcases bit_cases (dot z j) with h|h <;> simp [h, sign, tint, ca, cb, one_ne] <;> ring

def frame (A : OBase α) (s : Finset α) := wrap fun x => lum (A.proj s x)

@[simp] lemma frame_zero (A : OBase α) : frame A ∅ = 1 := by simp [frame, OBase.proj, wrap_one]

@[simp] lemma frame_univ (A : OBase α) : frame A univ = kernel α := by
  rw [frame, ← wrap_lum]; simp only [OBase.proj_univ]

def delta (z : Space α) := wrap fun x => lum (dot z x • z)

lemma frame_ins (A : OBase α) (s : Finset α) (i : α) (hi : i ∉ s) :
    frame A (insert i s) = delta (A.v i) * frame A s := by
  rw [frame, frame, delta, wrap_mul]; congr 1; funext x
  rw [show A.proj (insert i s) x = dot (A.v i) x • A.v i + A.proj s x from sum_insert hi, lum_add,
    show dot (dot (A.v i) x • A.v i) (A.proj s x) = 0 by
      simp [OBase.proj, dot_sum, A.rows, hi]]
  simp [sign]

lemma delta_pos (z : Space α) (h : lum z = I) :
    delta z = dir z := by
  rw [dir_phase, delta]; congr 1; funext x
  rcases bit_cases (dot z x) with e|e <;> simp [e, h, tint, one_ne]

lemma delta_neg (z : Space α) (h : lum z = -I) :
    delta z = shift z * dir z := by
  rw [shift_phase, dir_phase, wrap_mul, delta]; congr 1; funext x
  rcases bit_cases (dot z x) with e|e <;> simp [e, h, tint, sign, one_ne]

end
end PowerSaving.Binary
end OAI

namespace OAI
namespace PowerSaving.ReelKit
open Binary Spectral Matrix Finset
noncomputable section

structure Stroke where
  ix : ℕ → ℕ
  dye : Line
  partner : ℕ → ℕ

namespace Stroke

def applyM (u : Stroke) (x : Line) : Line := fun i => u.dye i * x (u.ix i)

def applyC (u : Stroke) (x : Line) : Line := fun i =>
  if u.partner i = i then x i else ca * x i + cb * x (u.partner i)

def send (u : Stroke) (x : Line) := u.applyC (u.applyM x)

structure Sound (u : Stroke) (n : ℕ) : Prop where
  bdix : ∀ i < n, u.ix i < n
  bdp : ∀ i < n, u.partner i < n
  pair : ∀ i, u.partner (u.partner i)=i
  awayix : ∀ i, n ≤ i → u.ix i=i
  awayp : ∀ i, n ≤ i → u.partner i=i
  awayd : ∀ i, n ≤ i → u.dye i=1

namespace Sound
variable {u : Stroke} {n n' : ℕ}

lemma wider (h : u.Sound n) (hn : n ≤ n') : u.Sound n' :=
  ⟨fun i hi => if g : i < n then (h.bdix i g).trans_le hn else by rw [h.awayix i (by omega)]; exact hi,
   fun i hi => if g : i < n then (h.bdp i g).trans_le hn else by rw [h.awayp i (by omega)]; exact hi,
   h.pair, fun i _ => h.awayix i (by omega), fun i _ => h.awayp i (by omega),
   fun i _ => h.awayd i (by omega)⟩

lemma send_away (h : u.Sound n) (x : Line) {i : ℕ} (hi : n ≤ i) : u.send x i = x i := by
  simp [send, applyC, applyM, h.awayp i hi, h.awayix i hi, h.awayd i hi]

lemma send_congr (h : u.Sound n) {x y : Line} (e : ∀ k < n, x k = y k) {i : ℕ} (hi : i < n) :
    u.send x i = u.send y i := by
  simp only [send, applyC, applyM, e _ (h.bdix i hi), e _ (h.bdix _ (h.bdp i hi))]

end Sound

def unmark : Stroke := ⟨id,fun _ => 1,id⟩

lemma sound_unmark (n : ℕ) : unmark.Sound n :=
  ⟨fun _ hi => hi, fun _ hi => hi, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

def plain (n : ℕ) (l : ℕ→ℕ) (d : Line) : Stroke :=
  ⟨fun i => if i < n then l i else i, fun i => if i < n then d i else 1, id⟩

lemma plain_sound {n : ℕ} {l : ℕ → ℕ} (d : Line) (h : ∀ i < n, l i < n) : (plain n l d).Sound n :=
  ⟨fun i hi => by simp [plain, hi, h i hi], fun _ hi => hi, fun _ => rfl,
   fun i hi => by simp [plain, show ¬ i < n by omega], fun _ _ => rfl,
   fun i hi => by simp [plain, show ¬ i < n by omega]⟩

lemma plain_send (n : ℕ) (l : ℕ → ℕ) (d x : Line) (i : ℕ) :
    (plain n l d).send x i = if i < n then d i * x (l i) else x i := by
  by_cases h : i < n <;> simp [send, applyC, applyM, plain, h]

def beside (p : ℕ) (u v : Stroke) : Stroke where
  ix i := if i<p then u.ix i else p+v.ix (i-p)
  dye i := if i<p then u.dye i else v.dye (i-p)
  partner i := if i<p then u.partner i else p+v.partner (i-p)

lemma Sound.beside {p q : ℕ} {a b : Stroke} (h : a.Sound p) (g : b.Sound q) :
    (beside p a b).Sound (p+q) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i => ?_, fun i hi => ?_, fun i hi => ?_,
    fun i hi => ?_⟩ <;> simp only [Stroke.beside]
  · split_ifs with c
    · have := h.bdix i c; omega
    · have := g.bdix (i-p) (by omega); omega
  · split_ifs with c
    · have := h.bdp i c; omega
    · have := g.bdp (i-p) (by omega); omega
  · by_cases c : i < p
    · simp [c, h.bdp i c, h.pair]
    · simp [c, g.pair]; omega
  all_goals simp only [if_neg (show ¬ i < p by omega), g.awayix (i-p) (by omega),
    g.awayp (i-p) (by omega), g.awayd (i-p) (by omega)]
  all_goals omega

lemma send_beside {p : ℕ} {a : Stroke} (b : Stroke) (h : a.Sound p) (x : Line) (i : ℕ) :
    (beside p a b).send x i = if i < p then a.send x i else b.send (fun k => x (p+k)) (i-p) := by
  by_cases hi : i < p
  · simp [send, applyC, applyM, beside, hi, h.bdp i hi]
  · have e : (p + b.partner (i-p) = i) ↔ (b.partner (i-p) = i-p) := by omega
    simp [send, applyC, applyM, beside, hi, e]

end Stroke
open Stroke

structure Reel where
  beats : ℕ
  atBeat : ℕ → Stroke

namespace Reel

def reach (p : Reel) (x : Line) : ℕ → Line
  | 0 => x
  | t+1 => (p.atBeat t).send (reach p x t)

def go (p : Reel) (x : Line) := p.reach x p.beats

def Sound (p : Reel) (n : ℕ) : Prop := ∀ t<p.beats, (p.atBeat t).Sound n

namespace Sound
variable {u : Reel} {n n' : ℕ}
lemma wider (h : u.Sound n) (hn : n ≤ n') : u.Sound n' := fun t ht => (h t ht).wider hn
end Sound

def wait (d : ℕ) : Reel := ⟨d,fun _ => unmark⟩

lemma sound_wait (d n : ℕ) : (wait d).Sound n := fun _ _ => sound_unmark n

def tick (s : Stroke) : Reel := ⟨1,fun _ => s⟩

lemma sound_tick {s : Stroke} {n : ℕ} (h : s.Sound n) : (tick s).Sound n := fun _ _ => h

def stack (a b : Reel) : Reel :=
  ⟨a.beats+b.beats,fun i => if i<a.beats then a.atBeat i else b.atBeat (i-a.beats)⟩

lemma Sound.stack {n : ℕ} {a b : Reel} (h : a.Sound n) (g : b.Sound n) :
    (a.stack b).Sound n := fun t ht => by
  simp only [Reel.stack] at ht ⊢
  split_ifs with c
  · exact h t c
  · exact g _ (by omega)

def parallel (p : ℕ) (a b : Reel) : Reel :=
  ⟨a.beats, fun i => beside p (a.atBeat i) (b.atBeat i)⟩

theorem Sound.parallel {p q : ℕ} {a b : Reel} (h : a.Sound p) (g : b.Sound q)
    (hl : a.beats=b.beats) :
    (Reel.parallel p a b).Sound (p+q) :=
  fun t ht => (h t ht).beside (g t (hl ▸ ht))

def atBase (p : ℕ) (a : Reel) : Reel := parallel p (wait a.beats) a

def swatch (n : ℕ) (d : Line) : Reel :=
  tick (Stroke.plain n id d)

def lace (n : ℕ) (q : ℕ→ℕ) : Reel :=
  tick (Stroke.plain n q (fun _ => 1))

variable {p a b : Reel} {n : ℕ}

@[simp] lemma go_tick (s : Stroke) (x : Line) : (tick s).go x = s.send x := rfl

lemma go_stack (a b : Reel) (x : Line) : (a.stack b).go x = b.go (a.go x) := by
  have h1 : ∀ t ≤ a.beats, (a.stack b).reach x t = a.reach x t := fun t ht => by
    induction t with
    | zero => rfl
    | succ t ih => simp only [reach]; rw [ih (by omega)]; simp [stack, show t < a.beats by omega]
  have h2 : ∀ s, (a.stack b).reach x (a.beats + s) = b.reach (a.go x) s := fun s => by
    induction s with
    | zero => exact h1 _ le_rfl
    | succ s ih => rw [← add_assoc]; simp only [reach]; rw [ih]; simp [stack]
  exact h2 b.beats

@[simp] lemma go_wait (d : ℕ) (x : Line) : (wait d).go x = x := by
  have : ∀ t, (wait d).reach x t = x := fun t => by
    induction t with
    | zero => rfl
    | succ t ih => show unmark.send _ = _; rw [ih]; funext i; simp [send, applyC, applyM, unmark]
  exact this d

lemma go_away (h : p.Sound n) (x : Line) {i : ℕ} (hi : n ≤ i) : p.go x i = x i := by
  have : ∀ t ≤ p.beats, p.reach x t i = x i := fun t ht => by
    induction t with
    | zero => rfl
    | succ t ih => simp only [reach]; rw [(h t (by omega)).send_away _ hi, ih (by omega)]
  exact this _ le_rfl

lemma go_parallel {q : ℕ} (h : a.Sound q) (hl : a.beats = b.beats) (x : Line) (i : ℕ) :
    (parallel q a b).go x i = if i < q then a.go x i else b.go (fun k => x (q+k)) (i-q) := by
  have H : ∀ t ≤ a.beats, (parallel q a b).reach x t =
      fun i => if i < q then a.reach x t i else b.reach (fun k => x (q+k)) t (i-q) := fun t ht => by
    induction t with
    | zero => funext i; split_ifs <;> simp only [reach]; congr 1; omega
    | succ t ih =>
      funext i
      show (beside q (a.atBeat t) (b.atBeat t)).send _ i = _
      rw [send_beside _ (h t (by omega)), ih (by omega)]
      split_ifs with c
      · exact (h t (by omega)).send_congr (fun k hk => if_pos hk) c
      · congr 1; funext k; simp
  show _ = if i < q then a.reach x a.beats i else b.reach _ b.beats (i - q)
  rw [← hl]; exact congrFun (H _ le_rfl) i

lemma go_atBase (o : ℕ) (r : Reel) (x : Line) (i : ℕ) :
    (atBase o r).go x i = if i < o then x i else r.go (fun k => x (o+k)) (i-o) := by
  rw [atBase, go_parallel (b := r) (sound_wait r.beats o) rfl, go_wait]

lemma swatch_go (n : ℕ) (d x : Line) (i : ℕ) :
    (swatch n d).go x i = if i < n then d i * x i else x i := plain_send n id d x i

lemma lace_go (n : ℕ) (q : ℕ → ℕ) (x : Line) (i : ℕ) :
    (lace n q).go x i = if i < n then x (q i) else x i := by simp [lace, plain_send]

lemma sound_swatch (n : ℕ) (d : Line) : (swatch n d).Sound n :=
  sound_tick (plain_sound d fun _ hi => hi)

@[simp] lemma beats_stack (a b : Reel) : (a.stack b).beats = a.beats + b.beats := rfl
@[simp] lemma beats_tick (s : Stroke) : (tick s).beats = 1 := rfl
@[simp] lemma beats_wait (d : ℕ) : (wait d).beats = d := rfl
@[simp] lemma beats_parallel (q : ℕ) (a b : Reel) : (parallel q a b).beats = a.beats := rfl

end Reel
end
end PowerSaving.ReelKit
end OAI

namespace OAI
namespace PowerSaving.ReelKit
open Reel Stroke Spectral
noncomputable section

structure Zone where
  lo : ℕ
  wide : ℕ

namespace Zone

def has (u : Zone) (i : ℕ) : Prop := u.lo ≤ i ∧ i < u.lo+u.wide

instance instDecidableHas (u : Zone) (i : ℕ) : Decidable (u.has i) :=
  inferInstanceAs (Decidable (_ ∧ _))

def Fits (u : Zone) (n : ℕ) : Prop := ∀ i, u.has i → i < n

def Sep (u v : Zone) : Prop := ∀ i, u.has i → ¬ v.has i

lemma Sep.symm {u v : Zone} (h : u.Sep v) : v.Sep u := fun i h1 h2 => h i h2 h1

def peek (u : Zone) (x : Line) : Line := fun k => x (u.lo + k)

def enter (u : Zone) (T : Line → Line) (x : Line) : Line :=
  fun j => if u.has j then T (u.peek x) (j - u.lo) else x j

def slim (u : Zone) (n : ℕ) : Zone := ⟨u.lo,n⟩

lemma slim_has {u : Zone} {n i : ℕ} (hn : n ≤ u.wide) (h : (u.slim n).has i) : u.has i :=
  ⟨h.1, lt_of_lt_of_le h.2 (Nat.add_le_add_left hn _)⟩

lemma Fits.slim {u : Zone} {v n : ℕ} (h : u.Fits v) (hn : n ≤ u.wide) :
    (u.slim n).Fits v := fun i hi => h i (slim_has hn hi)

lemma has_add {u : Zone} {k : ℕ} (hk : k < u.wide) : u.has (u.lo + k) := ⟨by omega, by omega⟩

lemma not_has {u v : Zone} (h : u.Sep v) {k : ℕ} (hk : k < v.wide) : ¬ u.has (v.lo + k) :=
  fun hh => h _ hh (has_add hk)

lemma has_cases {u : Zone} {j : ℕ} (h : u.has j) : ∃ k < u.wide, j = u.lo + k :=
  ⟨j - u.lo, by have := h.1; have := h.2; omega, by have := h.1; omega⟩

end Zone
open Zone

def cameo (a b c d : Reel) : Reel := ((a.stack b).stack c).stack d

def lift (D : Zone) (T : Line → Line) (x : Line) : Line :=
  fun j => if D.has j then T x (j - D.lo) else 0

lemma lift_app (Z : Zone) (T : Line → Line) (y : Line) (j : ℕ) :
    lift Z T y j = if Z.has j then T y (j - Z.lo) else 0 := rfl

def Adds (r : Reel) (D : Zone) (T : Line → Line) : Prop :=
  ∀ x j, r.go x j = if D.has j then x j + T x (j - D.lo) else x j

theorem Adds.go {r : Reel} {D : Zone} {T : Line → Line} (h : Adds r D T) (x : Line) :
    r.go x = x + lift D T x := by
  funext j; rw [h x j]; simp only [Pi.add_apply, lift]; split_ifs <;> simp

structure Acts (r : Reel) (rd wr : ℕ → Prop) (D : Line → Line) : Prop where
  go : ∀ x, r.go x = x + D x
  add : ∀ x y, D (x + y) = D x + D y
  reads : ∀ x y, (∀ j, rd j → x j = y j) → D x = D y
  writes : ∀ x j, ¬ wr j → D x j = 0

lemma lift_congr {Z : Zone} {T T' : Line → Line} (h : ∀ x k, k < Z.wide → T x k = T' x k)
    (x : Line) : lift Z T x = lift Z T' x := by
  funext j; simp only [lift]; split_ifs with hj
  · exact h _ _ (by have := hj.1; have := hj.2; omega)
  · rfl

lemma lift_neg {Z : Zone} {T T' : Line → Line} (e : ∀ x k, T' x k = -T x k) (x : Line) :
    lift Z T' x = -lift Z T x := by
  funext j; simp only [lift_app, Pi.neg_apply, e]; split_ifs <;> simp

namespace Acts
variable {r a b c d : Reel} {rd wr r2 w2 : ℕ → Prop} {D D2 : Line → Line}

theorem congr {D' : Line → Line} (h : Acts r rd wr D) (e : ∀ x, D x = D' x) : Acts r rd wr D' := by
  obtain rfl : D = D' := funext e
  exact h

theorem of {S Z : Zone} (G : Line → Line)
    (hg : Adds r Z fun x => G (S.peek x))
    (ha : ∀ x y, G (x + y) = G x + G y)
    (hr : ∀ x y, (∀ k < S.wide, x k = y k) → ∀ k < Z.wide, G x k = G y k) :
    Acts r S.has Z.has (lift Z fun x => G (S.peek x)) where
  go := hg.go
  add x y := by
    funext j; simp only [lift, Pi.add_apply]; split_ifs
    · exact congrFun (ha (S.peek x) (S.peek y)) _
    · simp
  reads x y hxy := by
    funext j; simp only [lift]; split_ifs with hj
    · exact hr _ _ (fun k hk => hxy _ (has_add hk)) _ (by have := hj.1; have := hj.2; omega)
    · rfl
  writes x j hj := if_neg hj

lemma keep (h : Acts r rd wr D) {y E : Line} (hE : ∀ j, rd j → E j = 0) : D (y + E) = D y :=
  h.reads _ _ fun j hj => by rw [Pi.add_apply, hE j hj, add_zero]

theorem inn {Z : Zone} {T : Line → Line} (h : Acts r rd Z.has (lift Z T)) (x : Line) {k : ℕ}
    (hk : k < Z.wide) : r.go x (Z.lo + k) = x (Z.lo + k) + T x k := by
  simp [h.go, lift, has_add hk]

theorem out {Z : Zone} (h : Acts r rd Z.has D) (x : Line) {j : ℕ}
    (hj : j < Z.lo ∨ Z.lo + Z.wide ≤ j) : r.go x j = x j := by
  simp [h.go, h.writes x j (by unfold Zone.has; omega)]

theorem cameo (ha : Acts a rd wr D) (hb : Acts b r2 w2 D2)
    (hc : Acts c rd wr fun x => -D x) (hd : Acts d r2 w2 fun x => -D2 x)
    (h1 : ∀ j, rd j → ¬ wr j) (h2 : ∀ j, rd j → ¬ w2 j) (h3 : ∀ j, r2 j → ¬ w2 j) :
    Acts (ReelKit.cameo a b c d) rd w2 (fun x => D2 (D x)) where
  go x := by
    have k1 : D (x + D x) = D x := ha.keep fun j hj => ha.writes x j (h1 j hj)
    have k2 : ∀ y, D (y + D2 y) = D y := fun y => ha.keep fun j hj => hb.writes y j (h2 j hj)
    have k3 : ∀ y, D2 (x + D2 y) = D2 x := fun y => hb.keep fun j hj => hb.writes y j (h3 j hj)
    simp only [ReelKit.cameo, go_stack, ha.go, hb.go, hc.go, hd.go]
    rw [k2, k1, show x + D x + D2 (x + D x) + -D x = x + D2 (x + D x) by abel, k3, hb.add]; abel
  add x y := by rw [ha.add, hb.add]
  reads x y h := by rw [ha.reads x y h]
  writes x j h := hb.writes _ j h

end Acts
end
end PowerSaving.ReelKit
end OAI

namespace OAI
namespace PowerSaving.ReelKit
open Zone Reel Stroke Spectral Binary Complex Finset
noncomputable section

lemma Sep.slim_left {u v : Zone} (h : u.Sep v) {n : ℕ} (hn : n ≤ u.wide) : (u.slim n).Sep v :=
  fun i hi => h i (slim_has hn hi)

lemma enter_on (Z : Zone) (T : Line → Line) (x : Line) {k : ℕ} (hk : k < Z.wide) :
    Z.enter T x (Z.lo + k) = T (Z.peek x) k := by
  rw [enter, if_pos (has_add hk), Nat.add_sub_cancel_left]

lemma enter_off {Z Y : Zone} (h : Z.Sep Y) (T : Line → Line) (x : Line) {k : ℕ}
    (hk : k < Y.wide) : Z.enter T x (Y.lo + k) = x (Y.lo + k) := if_neg (not_has h hk)

lemma enter_off' {Z : Zone} {T : Line → Line} {x : Line} {j : ℕ} (h : ¬ Z.has j) :
    Z.enter T x j = x j := if_neg h

lemma cyc_formula' {u : ℂ} {n : ℕ} (hu : PrimRoot u n) (x h : Line) {i : ℕ} (hi : i < n) :
    (n:ℂ)⁻¹ * freq n u⁻¹ (fun j => freq n u h j * freq n u x j) i = cyclic n h x i :=
  Spectral.cyc_formula hu x h hi

lemma range_pad' (n N : ℕ) (h : n ≤ N) (x : Line) :
    ∑ i ∈ range N, (if i < n then x i else 0) = ∑ i ∈ range n, x i :=
  Spectral.range_pad n N h x

lemma freq_add' (n : ℕ) (u : ℂ) (a b : Line) (i : ℕ) :
    freq n u (fun m => a m + b m) i = freq n u a i + freq n u b i := by
  simp only [freq, mul_add, sum_add_distrib]

def shade (u v : Zone) (f g : Line) : Reel :=
  tick ⟨id, (fun i => if u.has i then f (i-u.lo) else if v.has i then g (i-v.lo)
          else 1),id⟩

def jumps (u v : Zone) (i : ℕ) :=
  if u.has i then v.lo+(i-u.lo)
  else if v.has i then u.lo+(i-v.lo) else i

def snap (u v : Zone) : Reel := tick ⟨id,fun _ => 1,jumps u v⟩

lemma jumps_u {u v : Zone} {k : ℕ} (hk : k < u.wide) : jumps u v (u.lo+k) = v.lo+k := by
  rw [jumps, if_pos (has_add hk), Nat.add_sub_cancel_left]

lemma jumps_v {u v : Zone} (h : u.Sep v) {k : ℕ} (hk : k < v.wide) :
    jumps u v (v.lo+k) = u.lo+k := by
  rw [jumps, if_neg (not_has h hk), if_pos (has_add hk), Nat.add_sub_cancel_left]

lemma jumps_off {u v : Zone} {j : ℕ} (h1 : ¬ u.has j) (h2 : ¬ v.has j) : jumps u v j = j := by
  rw [jumps, if_neg h1, if_neg h2]

lemma sound_shade {u v : Zone} {n : ℕ} {f g : Line} (hu : u.Fits n) (hv : v.Fits n) :
    (shade u v f g).Sound n :=
  sound_tick ⟨fun _ hi => hi, fun _ hi => hi, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun i hi => by
      simp only; rw [if_neg fun c => by have := hu i c; omega, if_neg fun c => by have := hv i c; omega]⟩

lemma sound_snap {u v : Zone} {n : ℕ} (hu : u.Fits n) (hv : v.Fits n) (hw : u.Sep v)
    (he : u.wide = v.wide) : (snap u v).Sound n := by
  refine sound_tick ⟨fun _ hi => hi, fun i hi => ?_, fun i => ?_, fun _ _ => rfl,
    fun i hi => jumps_off (fun c => by have := hu i c; omega) (fun c => by have := hv i c; omega),
    fun _ _ => rfl⟩
  · show jumps u v i < n
    by_cases a : u.has i
    · obtain ⟨k, hk, rfl⟩ := has_cases a; rw [jumps_u hk]; exact hv _ (has_add (by omega))
    · by_cases b : v.has i
      · obtain ⟨k, hk, rfl⟩ := has_cases b; rw [jumps_v hw hk]; exact hu _ (has_add (by omega))
      · rwa [jumps_off a b]
  · show jumps u v (jumps u v i) = i
    by_cases a : u.has i
    · obtain ⟨k, hk, rfl⟩ := has_cases a; rw [jumps_u hk, jumps_v hw (by omega)]
    · by_cases b : v.has i
      · obtain ⟨k, hk, rfl⟩ := has_cases b; rw [jumps_v hw hk, jumps_u (by omega)]
      · rw [jumps_off a b, jumps_off a b]

macro "sound_tac" : tactic => `(tactic| repeat' (first | assumption | apply Reel.Sound.stack | apply sound_shade | apply sound_snap | apply sound_tick | apply plain_sound | (intro i hi; (first | exact hi | omega))))

def butterflyReel (u v : Zone) : Reel :=
  ((shade u v (fun _ => 1) (fun _ => I)).stack (snap u v)).stack
    (shade u v (fun _ => 1-I) (fun _ => 1+I))

def brick (u v : Zone) : Reel :=
  ((((butterflyReel u v).stack (shade u v (fun _ => -3) (fun _ => 1))).stack
      (butterflyReel u v)).stack (shade u v (fun _ => 2) (fun _ => 1))).stack (butterflyReel u v)

def spark (u v : Zone) (f : Line) : Reel :=
  ((shade u v (fun i => (4*f i/5)⁻¹) (fun _ => 1)).stack (brick u v)).stack
    (shade u v (fun i => (-1/8)*(4*f i/5)) (fun _ => -1/6))

def blaze (f : Line) : Line := fun i => 1+ f i * starRingEnd ℂ (f i)

def addScaledReel (dst src : Zone) (f : Line) : Reel :=
  (spark dst src (blaze f)).stack (spark dst src (fun i => f i-blaze f i))

lemma blaze_ne (f : Line) (i : ℕ) : blaze f i ≠ 0 := fun e => by
  have := congrArg Complex.re e
  simp only [blaze, add_re, one_re, mul_conj, ofReal_re, zero_re] at this
  linarith [normSq_nonneg (f i)]

lemma after_ne (f : Line) (i : ℕ) : f i-blaze f i ≠ 0 := fun e => by
  have := congrArg Complex.re e
  simp only [blaze, sub_re, add_re, one_re, mul_conj, ofReal_re, zero_re, normSq_apply] at this
  nlinarith [sq_nonneg (2*(f i).re - 1), sq_nonneg (f i).im]

def Twin (r : Reel) (u v : Zone) (f : ℕ → ℂ → ℂ → ℂ × ℂ) : Prop :=
  ∀ x, (∀ k < u.wide, r.go x (u.lo+k) = (f k (x (u.lo+k)) (x (v.lo+k))).1 ∧
      r.go x (v.lo+k) = (f k (x (u.lo+k)) (x (v.lo+k))).2) ∧
    ∀ j, ¬ u.has j → ¬ v.has j → r.go x j = x j

section
variable {u v : Zone} (hv : u.wide=v.wide) (hw : u.Sep v)
include hv hw

theorem Twin.stack {a b : Reel} {f g : ℕ → ℂ → ℂ → ℂ × ℂ} (ha : Twin a u v f)
    (hb : Twin b u v g) : Twin (a.stack b) u v (fun i p q => g i (f i p q).1 (f i p q).2) :=
  fun x => ⟨fun k hk => by
    rw [go_stack, ((hb _).1 k hk).1, ((hb _).1 k hk).2, ((ha x).1 k hk).1, ((ha x).1 k hk).2]
    exact ⟨rfl, rfl⟩, fun j h1 h2 => by rw [go_stack, (hb _).2 j h1 h2, (ha x).2 j h1 h2]⟩

omit hv hw in
theorem Twin.congr {r : Reel} {f g : ℕ → ℂ → ℂ → ℂ × ℂ} (h : Twin r u v f)
    (e : ∀ i p q, f i p q = g i p q) : Twin r u v g := by
  obtain rfl : f = g := funext fun i => funext fun p => funext fun q => e i p q
  exact h

lemma shade_twin (f g : Line) :
    Twin (shade u v f g) u v (fun k p q => (f k * p, g k * q)) := fun x => by
  have e : ∀ j, (shade u v f g).go x j =
      (if u.has j then f (j-u.lo) else if v.has j then g (j-v.lo) else 1) * x j := fun j => by
    simp [shade, send, applyC, applyM]
  refine ⟨fun k hk => ⟨?_, ?_⟩, fun j h1 h2 => ?_⟩ <;> rw [e]
  · rw [if_pos (has_add hk), Nat.add_sub_cancel_left]
  · rw [if_neg (not_has hw (by omega)), if_pos (has_add (by omega)), Nat.add_sub_cancel_left]
  · rw [if_neg h1, if_neg h2, one_mul]

lemma snap_twin : Twin (snap u v) u v (fun _ p q => (ca*p + cb*q, ca*q + cb*p)) := fun x => by
  have e : ∀ j, (snap u v).go x j =
      if jumps u v j = j then x j else ca * x j + cb * x (jumps u v j) := fun j => by
    simp [snap, send, applyC, applyM]
  have d : ∀ k < u.wide, v.lo + k ≠ u.lo + k := fun k hk c =>
    hw _ (has_add hk) (by rw [← c]; exact has_add (by omega))
  refine ⟨fun k hk => ⟨?_, ?_⟩, fun j h1 h2 => ?_⟩ <;> rw [e]
  · rw [jumps_u hk, if_neg (d k hk)]
  · rw [jumps_v hw (by omega), if_neg (d k hk).symm]
  · rw [jumps_off h1 h2, if_pos rfl]

lemma hinge_twin : Twin (butterflyReel u v) u v (fun _ p q => (p+q, p-q)) :=
  (((shade_twin hv hw _ _).stack hv hw (snap_twin hv hw)).stack hv hw (shade_twin hv hw _ _)).congr
    fun i p q => by
      simp only [ca, cb, Prod.mk.injEq]
      exact ⟨by linear_combination (-p/2 + (I-2)*q/2) * I_sq,
        by linear_combination ((I+2)*q/2 - p/2) * I_sq⟩

lemma brick_twin : Twin (brick u v) u v (fun _ p q => (-8*p - 10*q, -6*q)) :=
  (((((hinge_twin hv hw).stack hv hw (shade_twin hv hw _ _)).stack hv hw (hinge_twin hv hw)).stack
    hv hw (shade_twin hv hw _ _)).stack hv hw (hinge_twin hv hw)).congr fun i p q => by
      simp only [Prod.mk.injEq]; constructor <;> ring

lemma spark_twin {f : Line} (hf : ∀ i, f i ≠ 0) :
    Twin (spark u v f) u v (fun i p q => (p + f i * q, q)) :=
  (((shade_twin hv hw _ _).stack hv hw (brick_twin hv hw)).stack hv hw (shade_twin hv hw _ _)).congr
    fun i p q => by
      simp only [Prod.mk.injEq]; have := hf i
      constructor <;> field_simp <;> ring

theorem flash_adds (f : Line) : Adds (addScaledReel u v f) u (fun x k => f k * v.peek x k) := by
  intro x j
  rw [addScaledReel]
  obtain ⟨h1, h2⟩ := ((spark_twin hv hw (blaze_ne f)).stack hv hw (spark_twin hv hw (after_ne f))) x
  split_ifs with hj
  · obtain ⟨k, hk, rfl⟩ := has_cases hj
    rw [(h1 k hk).1, Nat.add_sub_cancel_left]; simp only [Zone.peek]; ring
  · by_cases c : v.has j
    · obtain ⟨k, hk, rfl⟩ := has_cases c; exact (h1 k (by omega)).2
    · exact h2 j hj c

theorem flash_acts (f : Line) :
    Acts (addScaledReel u v f) v.has u.has (lift u fun x k => f k * v.peek x k) :=
  Acts.of (fun z k => f k * z k) (flash_adds hv hw f) (fun x y => funext fun k => mul_add _ _ _)
    fun x y e k hk => by show f k * x k = f k * y k; rw [e k (by omega)]

end

section
variable {u v : Zone} {n : ℕ} (h : u.Fits n) (g : v.Fits n) (hv : u.wide=v.wide) (hw : u.Sep v)
include h g hv hw
lemma sound_hinge : (butterflyReel u v).Sound n := by sound_tac
lemma sound_flash (f : Line) : (addScaledReel u v f).Sound n := by sound_tac
end

@[simp] lemma beats_flash (u v : Zone) (f : Line) : (addScaledReel u v f).beats = 26 := rfl

def initial (n : ℕ) : Zone := ⟨0,n⟩
def ending (n : ℕ) : Zone := ⟨n,n⟩

lemma half_sep (n : ℕ) : (initial n).Sep (ending n) :=
  fun i (h1 : 0 ≤ i ∧ i < 0 + n) (h2 : n ≤ i ∧ i < n + n) => by omega

def deal (n i : ℕ) := if i<n then 2*i else 2*(i-n)+1

def foldPair (n : ℕ) (u : ℂ) : Reel :=
  (shade (initial n) (ending n) (fun _ => 1) (fun i => u^i)).stack
    (butterflyReel (initial n) (ending n))

def duo (n : ℕ) (u : ℂ) (r : Reel) : Reel :=
  ((lace (n+n) (deal n)).stack (parallel n r r)).stack (foldPair n u)

def fftReel : ℕ → ℂ → Reel
  | 0,_ => wait 0
  | d+1,u => duo (2^d) u (fftReel d (u^2))

lemma sound_pulse (d : ℕ) (u : ℂ) : (fftReel d u).Sound (2^d) := by
  induction d generalizing u with
  | zero => exact sound_wait 0 _
  | succ d ih =>
    rw [pow_succ, mul_two]
    have h1 : (initial (2^d)).Fits (2^d+2^d) := fun i hi => by simp only [Zone.has, initial] at hi; omega
    have h2 : (ending (2^d)).Fits (2^d+2^d) := fun i hi => by simp only [Zone.has, ending] at hi; omega
    exact ((sound_tick (plain_sound _ fun i hi => by unfold deal; split <;> omega)).stack
      (Sound.parallel (ih _) (ih _) rfl)).stack
      ((sound_shade h1 h2).stack (sound_hinge h1 h2 rfl (half_sep _)))

lemma beats_pulse (d : ℕ) (u : ℂ) : (fftReel d u).beats=5*d := by
  induction d generalizing u with
  | zero => rfl
  | succ d ih =>
    show (duo (2^d) u (fftReel d (u^2))).beats = _
    simp only [duo, foldPair, butterflyReel, lace, shade, snap, beats_stack, beats_tick,
      beats_parallel, ih]; ring

def backPulse (d : ℕ) (u : ℂ) : Reel :=
  (fftReel d u⁻¹).stack (swatch (2^d) (fun _ => (((2^d:ℕ):ℂ))⁻¹))

lemma pulse_go {d : ℕ} {u : ℂ} (hu : PrimRoot u (2^d)) (x : Line) {i : ℕ} (hi : i < 2^d) :
    (fftReel d u).go x i = freq (2^d) u x i := by
  induction d generalizing u x i with
  | zero =>
    obtain rfl : i = 0 := by simp at hi; omega
    simp [fftReel, freq]
  | succ d ih =>
    rw [pow_succ, mul_two] at hu hi ⊢
    rw [fftReel, duo, go_stack, go_stack]
    have hs := sound_pulse d (u^2)
    have hpos : 0 < 2^d := Nat.two_pow_pos d
    have hu2 := even_prim hu
    generalize 2^d = n at *
    set Y := (parallel n (fftReel d (u^2)) (fftReel d (u^2))).go ((lace (n+n) (deal n)).go x) with hY
    have E : ∀ k < n, Y k = freq n (u^2) (fun j => x (2*j)) k := fun k hk => by
      rw [hY, go_parallel hs rfl, if_pos hk, ih hu2 _ hk]
      exact congrFun (freq_congr (fun j hj => by rw [lace_go, if_pos (by omega)]; simp [deal, hj]) _) k
    have O : ∀ k < n, Y (n+k) = freq n (u^2) (fun j => x (2*j+1)) k := fun k hk => by
      rw [hY, go_parallel hs rfl, if_neg (by omega), Nat.add_sub_cancel_left, ih hu2 _ hk]
      exact congrFun (freq_congr (fun j hj => by rw [lace_go, if_pos (by omega)]; simp [deal]) _) k
    have T := (Twin.stack (u := initial n) (v := ending n) rfl (half_sep n)
      (shade_twin (u := initial n) (v := ending n) rfl (half_sep n) (fun _ => 1) (fun i => u^i))
      (hinge_twin rfl (half_sep n)) Y).1
    by_cases c : i < n
    · have := (T i c).1; simp only [initial, ending, zero_add] at this
      refine this.trans ?_; rw [E i c, O i c, freq_eo]; ring
    · obtain ⟨k, rfl⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
      have := (T k (show k < n by omega)).2; simp only [initial, ending, zero_add] at this
      refine this.trans ?_; rw [E k (by omega), O k (by omega), freq_eo' hpos hu]; ring

lemma sound_back (d : ℕ) (u : ℂ) : (backPulse d u).Sound (2^d) :=
  (sound_pulse d _).stack (sound_swatch _ _)

lemma back_go {d : ℕ} {u : ℂ} (hu : PrimRoot u (2^d)) (x : Line) {i : ℕ} (hi : i < 2^d) :
    (backPulse d u).go x i = ((2^d:ℕ):ℂ)⁻¹ * freq (2^d) u⁻¹ x i := by
  rw [backPulse, go_stack, swatch_go, if_pos hi, pulse_go hu.inv x hi]

lemma atBase_enter {P : Reel} {Z : Zone} {T : Line → Line} (hP : P.Sound Z.wide)
    (hT : ∀ y i, i < Z.wide → P.go y i = T y i) (x : Line) :
    (atBase Z.lo P).go x = Z.enter T x := by
  funext j; rw [go_atBase, Zone.enter]
  by_cases a : j < Z.lo
  · rw [if_pos a, if_neg (show ¬ Z.has j from fun h => by have := h.1; omega)]
  · rw [if_neg a]
    by_cases c : j < Z.lo + Z.wide
    · rw [if_pos (show Z.has j from ⟨by omega, c⟩)]; exact hT _ _ (by omega)
    · rw [if_neg (show ¬ Z.has j from fun h => by have := h.2; omega), go_away hP _ (by omega)]
      show x (Z.lo + (j - Z.lo)) = x j; congr 1; omega

def cyclicConvReel (d : ℕ) (r : ℂ) (u v : Zone) (h : Line) : Reel :=
  let p := fftReel d r; let b := backPulse d r
  let f := addScaledReel v u (freq (2^d) r h)
  ((((atBase u.lo p).stack (atBase v.lo p)).stack f).stack (atBase u.lo b)).stack
    (atBase v.lo b)

lemma cyclic_neg (n : ℕ) (h x : Line) : cyclic n (fun i => -h i) x = -cyclic n h x := by
  funext i; simp [cyclic, sum_neg_distrib]

section
variable {d : ℕ} {r : ℂ} {u v : Zone} (hr : PrimRoot r (2^d)) (hu : u.wide = 2^d)
  (hv : v.wide = 2^d) (huv : u.Sep v)
include hr hu hv huv

lemma conv_acts (h : Line) :
    Acts (cyclicConvReel d r u v h) u.has v.has (lift v fun x => cyclic (2^d) h (u.peek x)) := by
  have hB : ∀ {Z : Zone}, Z.wide = 2^d → ∀ y, (atBase Z.lo (fftReel d r)).go y =
      Z.enter (freq (2^d) r) y ∧ (atBase Z.lo (backPulse d r)).go y =
      Z.enter (fun z i => ((2^d:ℕ):ℂ)⁻¹ * freq (2^d) r⁻¹ z i) y := fun hZ y =>
    ⟨atBase_enter (hZ ▸ sound_pulse d r) (fun y i hi => pulse_go hr y (hZ ▸ hi)) y,
     atBase_enter (hZ ▸ sound_back d r) (fun y i hi => back_go hr y (hZ ▸ hi)) y⟩
  have hF := flash_adds (hv.trans hu.symm) huv.symm (freq (2^d) r h)
  refine Acts.of (fun z => cyclic (2^d) h z) (fun x j => ?_)
    (fun x y => by funext i; simp only [cyclic, Pi.add_apply, mul_add, sum_add_distrib])
    (fun x y e k _ => sum_congr rfl fun j hj => by
      rw [e j (by have := mem_range.mp hj; omega)])
  simp only [cyclicConvReel, go_stack, (hB hu _).1, (hB hv _).1, (hB hu _).2, (hB hv _).2]
  set IF := fun z i => ((2^d:ℕ):ℂ)⁻¹ * freq (2^d) r⁻¹ z i
  set s2 := v.enter (freq (2^d) r) (u.enter (freq (2^d) r) x) with hs2
  set s3 := (addScaledReel v u (freq (2^d) r h)).go s2 with hs3
  have f1 : ∀ m < 2^d, s2 (u.lo + m) = freq (2^d) r (u.peek x) m := fun m hm => by
    rw [hs2, enter_off huv.symm _ _ (by omega), enter_on _ _ _ (by omega)]
  have f2 : ∀ m < 2^d, s2 (v.lo + m) = freq (2^d) r (v.peek x) m := fun m hm => by
    rw [hs2, enter_on _ _ _ (by omega)]
    exact congrFun (freq_congr (fun i hi => enter_off huv _ _ (by omega)) _) m
  have f3 : ∀ m < 2^d, s3 (v.lo + m) = s2 (v.lo + m) + freq (2^d) r h m * s2 (u.lo + m) :=
    fun m hm => by rw [hs3, hF, if_pos (has_add (by omega)), Nat.add_sub_cancel_left] <;> rfl
  have f4 : ∀ m < 2^d, s3 (u.lo + m) = s2 (u.lo + m) := fun m hm => by
    rw [hs3, hF, if_neg (not_has huv.symm (by omega))]
  by_cases hvj : v.has j
  · obtain ⟨k, hk, rfl⟩ := has_cases hvj
    have e : ∀ m < 2^d, v.peek (u.enter IF s3) m =
        freq (2^d) r (v.peek x) m + freq (2^d) r h m * freq (2^d) r (u.peek x) m := fun m hm => by
      show u.enter IF s3 (v.lo + m) = _
      rw [enter_off huv _ _ (by omega), f3 m hm, f2 m hm, f1 m hm]
    rw [if_pos hvj, enter_on _ _ _ hk, Nat.add_sub_cancel_left]
    show _ * freq _ _ _ k = _
    rw [freq_congr e, freq_add', mul_add, freq_inv hr _ k (by omega),
      cyc_formula' hr _ h (i := k) (by omega)] <;> rfl
  · rw [if_neg hvj, enter_off' hvj]
    by_cases huj : u.has j
    · obtain ⟨k, hk, rfl⟩ := has_cases huj
      rw [enter_on _ _ _ hk]
      show _ * freq _ _ _ k = _
      rw [freq_congr (x := u.peek s3) (fun m hm => (f4 m hm).trans (f1 m hm)),
        freq_inv hr _ k (by omega)] <;> rfl
    · rw [enter_off' huj, hs3, hF, if_neg hvj, hs2, enter_off' hvj, enter_off' huj]

lemma conv_neg (h : Line) : Acts (cyclicConvReel d r u v (fun i => -h i)) u.has v.has
    (fun x => -lift v (fun x => cyclic (2^d) h (u.peek x)) x) :=
  (conv_acts hr hu hv huv _).congr (lift_neg fun _ _ => by simp [cyclic_neg])

end
end
end PowerSaving.ReelKit
end OAI

namespace OAI
namespace PowerSaving.ReelKit
open Reel Stroke Zone Spectral Finset Matrix
noncomputable section

def trail (u a : Zone) (t : ℂ) : Reel :=
  addScaledReel (a.slim u.wide) u (fun _ => t)

def slice (a v : Zone) (t : ℂ) : Reel :=
  addScaledReel v (a.slim v.wide) (fun _ => t)

def pad (w : ℕ) (z : Line) : Line := fun k => if k < w then z k else 0

def trim (t : ℂ) (x : Line) : Line := fun i => t*x i

def duct (d : ℕ) (r : ℂ) (u a b : Zone) (h : Line) : Reel :=
  cameo (trail u a 1) (cyclicConvReel d r a b h) (trail u a (-1))
    (cyclicConvReel d r a b (fun i => -h i))

def well (d : ℕ) (r : ℂ) (u v a b : Zone) (h : Line) : Reel :=
  cameo (duct d r u a b h) (slice b v 1)
    (duct d r u a b (fun i => -h i)) (slice b v (-1))

def skirt (b e s l m : ℕ) (h : Line) : Line :=
  fun k =>
    if k<b then
      if k<s then rise h (m+k) l else 0
    else
      if 0<s ∧ 2*b-k<e then rise h m (l+(2*b-k)) else 0

def toeplitzBlockReel (k : ℕ) (r : ℂ) (u v a b : Zone) (l m : ℕ) (h : Line) : Reel :=
  well (k+1) r u v a b (skirt (2^k) u.wide v.wide l m h)

lemma rise_neg (h : Line) (i j : ℕ) : rise (fun i => -h i) i j = -rise h i j := by
  unfold rise; split_ifs <;> simp

lemma trail_acts {u a : Zone} (hu : u.wide ≤ a.wide) (hua : u.Sep a) (t : ℂ) :
    Acts (trail u a t) u.has (a.slim u.wide).has (lift (a.slim u.wide) fun x k => t * u.peek x k) :=
  flash_acts (u := a.slim u.wide) (v := u) rfl (Sep.slim_left hua.symm hu) (fun _ => t)

lemma slice_acts {b v : Zone} (hv : v.wide ≤ b.wide) (hvb : v.Sep b) (t : ℂ) :
    Acts (slice b v t) (b.slim v.wide).has v.has (lift v fun x k => t * (b.slim v.wide).peek x k) :=
  flash_acts (u := v) (v := b.slim v.wide) rfl (Sep.slim_left hvb.symm hv).symm (fun _ => t)

section
variable {d : ℕ} {r : ℂ} {u v a b : Zone} (hr : PrimRoot r (2^d)) (ha : a.wide = 2^d)
  (hb : b.wide = 2^d) (hab : a.Sep b) (hu : u.wide ≤ a.wide) (hua : u.Sep a) (hub : u.Sep b)
include hr ha hb hab hu hua hub

lemma duct_acts (h : Line) : Acts (duct d r u a b h) u.has b.has
    (lift b fun x => cyclic (2^d) h (pad u.wide (u.peek x))) := by
  refine (Acts.cameo (trail_acts hu hua 1) (conv_acts hr ha hb hab h)
    ((trail_acts hu hua (-1)).congr (lift_neg fun _ _ => by ring)) (conv_neg hr ha hb hab h)
    (Sep.slim_left hua.symm hu).symm hub hab).congr fun x => ?_
  beta_reduce
  have e : a.peek (lift (a.slim u.wide) (fun x k => 1 * u.peek x k) x) = pad u.wide (u.peek x) := by
    funext k; by_cases hk : k < u.wide <;> simp [Zone.peek, lift, Zone.slim, Zone.has, pad, hk]
  funext j; rw [lift_app, lift_app, e]

lemma duct_neg (h : Line) : Acts (duct d r u a b (fun i => -h i)) u.has b.has
    (fun x => -lift b (fun x => cyclic (2^d) h (pad u.wide (u.peek x))) x) :=
  (duct_acts hr ha hb hab hu hua hub _).congr (lift_neg fun _ _ => by simp [cyclic_neg])

lemma well_acts (hv : v.wide ≤ b.wide) (hvb : v.Sep b) (huv : u.Sep v) (h : Line) :
    Acts (well d r u v a b h) u.has v.has
      (lift v fun x => cyclic (2^d) h (pad u.wide (u.peek x))) := by
  refine (Acts.cameo (duct_acts hr ha hb hab hu hua hub h) (slice_acts hv hvb 1)
    (duct_neg hr ha hb hab hu hua hub h) ((slice_acts hv hvb (-1)).congr (lift_neg fun _ _ => by ring))
    hub huv (Sep.slim_left hvb.symm hv)).congr fun x => ?_
  beta_reduce
  funext j; rw [lift_app, lift_app]; split_ifs with hj
  · have hk : j - v.lo < b.wide := by have := hj.1; have := hj.2; omega
    show 1 * lift b _ x (b.lo + (j - v.lo)) = _
    rw [lift_app, if_pos (has_add hk), Nat.add_sub_cancel_left, one_mul]
  · rfl

end

lemma skirt_cyc {b e s l m i : ℕ} (h : Line) (he : e ≤ b) (hi : i < s) (hs : s ≤ b) (z : Line) :
    cyclic (2*b) (skirt b e s l m h) (pad e z) i = ∑ j ∈ range e, rise h (m+i) (l+j) * z j := by
  unfold cyclic pad
  simp only [mul_ite, mul_zero]
  rw [range_pad' e (2*b) (by omega)]
  refine sum_congr rfl fun j hj => ?_
  have hj := mem_range.mp hj
  congr 1
  unfold predAt skirt
  by_cases hji : j ≤ i
  · have c : (l ≤ m + (i-j)) ↔ (l + j ≤ m + i) := by omega
    have e1 : m + (i-j) - l = m + i - (l+j) := by omega
    simp only [hji, ↓reduceIte, show i - j < b by omega, show i - j < s by omega, rise, c, e1]
  · have c : (l + (j-i) ≤ m) ↔ (l + j ≤ m + i) := by omega
    have e1 : m - (l + (j-i)) = m + i - (l+j) := by omega
    have e2 : 2*b - (i + 2*b - j) = j - i := by omega
    simp only [hji, ↓reduceIte, show ¬ i + 2*b - j < b by omega, e2,
      show (0 < s ∧ j - i < e) ↔ True from ⟨fun _ => trivial, fun _ => ⟨by omega, by omega⟩⟩,
      rise, c, e1]

def blockOp (w l m : ℕ) (h : Line) (z : Line) (i : ℕ) : ℂ :=
  ∑ j ∈ range w, rise h (m+i) (l+j) * z j

section
variable {k : ℕ} {r : ℂ} {u v a b : Zone} (hr : PrimRoot r (2^(k+1))) (ha : a.wide = 2^(k+1))
  (hb : b.wide = 2^(k+1)) (hab : a.Sep b) (hu : u.wide ≤ 2^k) (hua : u.Sep a) (hub : u.Sep b)
  (hv : v.wide ≤ 2^k) (hvb : v.Sep b) (huv : u.Sep v)
include hr ha hb hab hu hua hub hv hvb huv

lemma block_acts (l m : ℕ) (h : Line) : Acts (toeplitzBlockReel k r u v a b l m h) u.has v.has
    (lift v fun x => blockOp u.wide l m h (u.peek x)) := by
  have h2 : 2^k ≤ 2^(k+1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine (well_acts hr ha hb hab (by omega) hua hub (by omega) hvb huv _).congr
    fun x => lift_congr (fun x i hi => ?_) x
  rw [pow_succ']; exact skirt_cyc h hu hi hv _

lemma block_neg (l m : ℕ) (h : Line) :
    Acts (toeplitzBlockReel k r u v a b l m (fun i => -h i)) u.has v.has
    (fun x => -lift v (fun x => blockOp u.wide l m h (u.peek x)) x) :=
  (block_acts hr ha hb hab hu hua hub hv hvb huv l m _).congr (lift_neg fun _ _ => by
    simp [blockOp, rise_neg])

end

def strand (a : ℕ → Reel) : ℕ → Reel
  | 0 => wait 0
  | i+1 => (strand a i).stack (a i)

lemma beat_strand {a : ℕ→Reel} (n d : ℕ) (h : ∀ i<n,(a i).beats=d) :
    (strand a n).beats=n*d := by
  induction n with
  | zero => simp [strand, wait]
  | succ n ih =>
    show (strand a n).beats + (a n).beats = _
    rw [ih (fun i hi => h i (by omega)), h n (by omega)]; ring

lemma sound_strand {a : ℕ → Reel} {n N : ℕ} (h : ∀ i < n, (a i).Sound N) : (strand a n).Sound N := by
  induction n with
  | zero => exact sound_wait 0 N
  | succ n ih => exact (ih fun i hi => h i (by omega)).stack (h n (by omega))

def quay (b j : ℕ) : Zone := ⟨j*b,b⟩
def jetty (p w b s : ℕ) : Zone := ⟨p+s*b,min b (w-s*b)⟩

def riprap (a : ℕ → ℕ → ℕ → Reel) (l : ℕ) : Reel :=
  strand (fun s => strand (fun c => strand (fun j => a s c j) l) l) l

def Gains (r : Reel) (P : ℕ) (D : Line → Line) : Prop :=
  ∀ x, r.go x = x + D x ∧ (∀ i < P, D x i = 0) ∧ ∀ y, (∀ i < P, x i = y i) → D x = D y

theorem Gains.congr {r : Reel} {P : ℕ} {D D' : Line → Line} (h : Gains r P D)
    (e : ∀ x, D x = D' x) : Gains r P D' := by
  obtain rfl : D = D' := funext e
  exact h

lemma Acts.gains {r : Reel} {rd wr : ℕ → Prop} {D : Line → Line} {P : ℕ} (h : Acts r rd wr D)
    (hr : ∀ j, rd j → j < P) (hw : ∀ j, wr j → P ≤ j) : Gains r P D := fun x =>
  ⟨h.go x, fun i hi => h.writes x i (fun hh => by have := hw i hh; omega),
    fun y hy => h.reads x y (fun j hj => hy j (hr j hj))⟩

lemma strand_gains {a : ℕ → Reel} {D : ℕ → Line → Line} {P n : ℕ}
    (h : ∀ i < n, Gains (a i) P (D i)) : Gains (strand a n) P (fun x => ∑ i ∈ range n, D i x) := by
  induction n with
  | zero => exact fun x => ⟨by simp [strand], fun _ _ => by simp, fun _ _ => by simp⟩
  | succ n ih =>
    intro x
    obtain ⟨g1, g2, g3⟩ := ih (fun i hi => h i (by omega)) x
    obtain ⟨f1, f2, f3⟩ := h n (by omega) x
    simp only at g1 g2 g3
    simp only [sum_range_succ]
    refine ⟨?_, fun i hi => by rw [Pi.add_apply, g2 i hi, f2 i hi, add_zero],
      fun y e => by rw [g3 y e, f3 y e]⟩
    rw [strand, go_stack, (h n (by omega) _).1, g1, (h n (by omega) (x + ∑ i ∈ range n, D i x)).2.2 x
      fun i hi => by rw [Pi.add_apply, g2 i hi, add_zero], add_assoc]

lemma riprap_gains {a : ℕ → ℕ → ℕ → Reel} {l P : ℕ} {D : ℕ → ℕ → ℕ → Line → Line}
    (h : ∀ s < l, ∀ c < l, ∀ j < l, Gains (a s c j) P (D s c j)) :
    Gains (riprap a l) P (fun x => ∑ s ∈ range l, ∑ c ∈ range l, ∑ j ∈ range l, D s c j x) :=
  strand_gains fun s hs => strand_gains fun c hc => strand_gains fun j hj => h s hs c hc j hj

theorem sum_blocks {M : Type*} [AddCommMonoid M] (q b : ℕ) (f : ℕ → M) :
    ∑ i ∈ range (q*b), f i = ∑ j ∈ range q, ∑ i ∈ range b, f (j*b + i) := by
  induction q with
  | zero => simp
  | succ q ih => rw [add_mul, one_mul, sum_range_add, ih, sum_range_succ]

def far (b j : ℕ) := if j<8 then 8*b else 0
def trestle (b j : ℕ) : Zone := ⟨far b j, b⟩
def barrier (b j : ℕ) : Zone := ⟨far b j + b, 2*b⟩
def lockBay (b j : ℕ) : Zone := ⟨far b j + 3*b,2*b⟩

structure Wharf (p : ℕ) (u v z l m : Zone) : Prop where
  fitsU : u.Fits p
  fitsV : v.Fits p
  fitsZ : z.Fits p
  fitsL : l.Fits p
  fitsM : m.Fits p
  uz : u.Sep z
  ul : u.Sep l
  um : u.Sep m
  lm : l.Sep m
  zl : z.Sep l
  zm : z.Sep m
  uv : u.Sep v
  zv : z.Sep v
  vm : v.Sep m

def toeplitzPairReel (k : ℕ) (r : ℂ) (u v z l m : Zone) (b e y : ℕ) (h g : Line) : Reel :=
  cameo (toeplitzBlockReel k r u z l m b e g) (toeplitzBlockReel k r z v l m e y h)
    (toeplitzBlockReel k r u z l m b e (fun i => -g i)) (toeplitzBlockReel k r z v l m e y (fun i => -h i))

structure Slips (k : ℕ) (u v z l m : Zone) : Prop where
  uw : u.wide ≤ 2^k
  vw : v.wide ≤ 2^k
  zw : z.wide ≤ 2^k
  lw : l.wide=2^(k+1)
  mw : m.wide=2^(k+1)

lemma cliff_acts {k n : ℕ} {r : ℂ} {u v z l m : Zone} (b e y : ℕ) (h g : Line)
    (hr : PrimRoot r (2^(k+1))) (H : Slips k u v z l m) (hf : Wharf n u v z l m) :
    Acts (toeplitzPairReel k r u v z l m b e y h g) u.has v.has (lift v fun x i =>
      ∑ c ∈ range z.wide, rise h (y+i) (e+c) * ∑ j ∈ range u.wide, rise g (e+c) (b+j) * u.peek x j) := by
  refine (Acts.cameo (block_acts hr H.lw H.mw hf.lm H.uw hf.ul hf.um H.zw hf.zm hf.uz b e g)
    (block_acts hr H.lw H.mw hf.lm H.zw hf.zl hf.zm H.vw hf.vm hf.zv e y h)
    (block_neg hr H.lw H.mw hf.lm H.uw hf.ul hf.um H.zw hf.zm hf.uz b e g)
    (block_neg hr H.lw H.mw hf.lm H.zw hf.zl hf.zm H.vw hf.vm hf.zv e y h)
    hf.uz hf.uv hf.zv).congr fun x => ?_
  beta_reduce
  funext j; rw [lift_app, lift_app]; split_ifs
  · refine sum_congr rfl fun c hc => ?_
    show _ * lift z _ x (z.lo + c) = _
    rw [lift_app, if_pos (has_add (mem_range.mp hc)), Nat.add_sub_cancel_left] <;> rfl
  · rfl

def toeplitzGridCell (k : ℕ) (r : ℂ) (w : ℕ) (h g : Line) (s c j : ℕ) : Reel :=
  let b := 2^k
  let p := 16*b
  toeplitzPairReel k r (quay b j) (jetty p w b s) (trestle b j) (barrier b j)
    (lockBay b j) (j*b) (c*b) (p+s*b) h g

def toeplitzGridReel (k : ℕ) (r : ℂ) (w : ℕ) (h g : Line) : Reel :=
  riprap (toeplitzGridCell k r w h g) 16

lemma beats_conv (d : ℕ) (r : ℂ) (u v : Zone) (h : Line) :
    (cyclicConvReel d r u v h).beats = 20*d+28 := by
  show (fftReel d r).beats + (fftReel d r).beats + 26 + ((fftReel d r⁻¹).beats + 1)
    + ((fftReel d r⁻¹).beats + 1) = _
  rw [beats_pulse, beats_pulse]; ring

lemma beats_well (d : ℕ) (r : ℂ) (u v a b : Zone) (h : Line) :
    (well d r u v a b h).beats = 80*d+268 := by
  simp only [well, duct, cameo, trail, slice, beats_stack, beats_flash, beats_conv]; ring

lemma beats_gravel (k : ℕ) (r : ℂ) (w : ℕ) (h g : Line) (s c j : ℕ) :
    (toeplitzGridCell k r w h g s c j).beats=4*(80*k+348) := by
  simp only [toeplitzGridCell, toeplitzPairReel, toeplitzBlockReel, cameo, beats_stack, beats_well]
  ring

def naiveToeplitzCell (p w : ℕ) (h g : Line) (s c j : ℕ) : Reel :=
  if s<w then addScaledReel (jetty p w 1 s) (quay 1 j) (fun _ => rise h (p+s) c*rise g c j)
  else wait 26

def naiveToeplitzReel (p w : ℕ) (h g : Line) : Reel := riprap (naiveToeplitzCell p w h g) p

lemma beats_speck (p w : ℕ) (h g : Line) (s c j : ℕ) :
    (naiveToeplitzCell p w h g s c j).beats=26 := by
  unfold naiveToeplitzCell; split_ifs <;> rfl

lemma beats_riprap {a : ℕ → ℕ → ℕ → Reel} {l d : ℕ} (h : ∀ s c j, (a s c j).beats = d) :
    (riprap a l).beats = l*(l*(l*d)) :=
  beat_strand _ _ fun _ _ => beat_strand _ _ fun _ _ => beat_strand _ _ fun _ _ => h _ _ _

def bridgeOp (p w : ℕ) (h g : Line) (x : Line) (i : ℕ) : ℂ :=
  if p ≤ i ∧ i < p + w then toeplitzApply p h (toeplitzApply p g x) i else 0

lemma naive_gains {p w : ℕ} (h g : Line) (hw : w ≤ p) :
    Gains (naiveToeplitzReel p w h g) p (bridgeOp p w h g) := by
  have cell : ∀ s < p, ∀ c < p, ∀ j < p, Gains (naiveToeplitzCell p w h g s c j) p
      (fun x i => if s < w ∧ i = p + s then rise h (p+s) c * rise g c j * x j else 0) := by
    intro s _ c _ j hj
    unfold naiveToeplitzCell; split_ifs with hs
    · refine ((flash_acts (u := jetty p w 1 s) (v := quay 1 j) (by simp only [jetty, quay]; omega)
        (fun i (h1 : p + s*1 ≤ i ∧ _) (h2 : j*1 ≤ i ∧ i < j*1 + 1) => by omega) _).gains
        (fun i (q : j*1 ≤ i ∧ i < j*1 + 1) => by omega) (fun i (q : p + s*1 ≤ i ∧ _) => by omega)).congr
        fun x => funext fun i => ?_
      simp only [lift, Zone.has, jetty, quay, Zone.peek, mul_one]
      by_cases hi : i = p + s
      · subst hi; rw [if_pos (by omega), if_pos ⟨hs, rfl⟩]; simp
      · rw [if_neg (by omega), if_neg (by omega)]
    · exact fun x => ⟨by funext i; simp [hs], fun _ _ => by simp [hs],
        fun _ _ => by funext i; simp [hs]⟩
  refine (riprap_gains cell).congr fun x => funext fun i => ?_
  simp only [Finset.sum_apply, bridgeOp]
  split_ifs with hi
  · rw [sum_eq_single (i - p) (fun s _ hs => sum_eq_zero fun c _ =>
      sum_eq_zero fun j _ => if_neg (by omega)) (fun h' => absurd (mem_range.2
      (by omega)) h')]
    simp only [toeplitzApply, Finset.mul_sum]
    refine sum_congr rfl fun c _ => sum_congr rfl fun j _ => ?_
    rw [if_pos (show i - p < w ∧ i = p + (i - p) by omega), Nat.add_sub_cancel' hi.1]; ring
  · exact sum_eq_zero fun s _ => sum_eq_zero fun c _ => sum_eq_zero
      fun j _ => if_neg (by omega)

lemma cell_zones {k w s j : ℕ} (hs : s < 16) (hj : j < 16) (hw : w ≤ 16*2^k) :
    Slips k (quay (2^k) j) (jetty (16*2^k) w (2^k) s) (trestle (2^k) j) (barrier (2^k) j)
      (lockBay (2^k) j) ∧
    Wharf (16*2^k + w) (quay (2^k) j) (jetty (16*2^k) w (2^k) s) (trestle (2^k) j)
      (barrier (2^k) j) (lockBay (2^k) j) := by
  refine ⟨⟨le_rfl, min_le_left _ _, le_rfl, by show 2 * 2^k = 2^(k+1); ring,
    by show 2 * 2^k = 2^(k+1); ring⟩, ?_⟩
  generalize 2^k = b at hw ⊢
  have q1 : j < 8 → j*b + b ≤ 8*b := fun h8 => by
    have := Nat.mul_le_mul_right b (show j + 1 ≤ 8 by omega); rwa [add_mul, one_mul] at this
  have q2 : 8 ≤ j → 8*b ≤ j*b := fun h8 => Nat.mul_le_mul_right b h8
  have q3 : j*b + b ≤ 16*b := by
    have := Nat.mul_le_mul_right b (show j + 1 ≤ 16 by omega); rwa [add_mul, one_mul] at this
  have hf8 : j < 8 → far b j = 8*b := fun h => if_pos h
  have hf0 : 8 ≤ j → far b j = 0 := fun h => if_neg (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · intro i h1
    try intro h2
    simp only [Zone.has, quay, jetty, trestle, barrier, lockBay] at *
    rcases Nat.lt_or_ge j 8 with h8 | h8
    · have := q1 h8; have := hf8 h8; omega
    · have := q2 h8; have := hf0 h8; omega

lemma grid_gains {k w : ℕ} {r : ℂ} (h g : Line) (hr : PrimRoot r (2^(k+1))) (hw : w ≤ 16*2^k) :
    Gains (toeplitzGridReel k r w h g) (16*2^k) (bridgeOp (16*2^k) w h g) := by
  have hb : 0 < 2^k := Nat.two_pow_pos k
  refine (riprap_gains fun s hs c _ j hj => (cliff_acts (j*2^k) (c*2^k) (16*2^k+s*2^k) h g hr
    (cell_zones hs hj hw).1 (cell_zones hs hj hw).2).gains (fun i q => ?_) fun i q => ?_).congr
    fun x => funext fun i => ?_
  · have := Nat.mul_le_mul_right (2^k) (show j+1 ≤ 16 by omega)
    simp only [Zone.has, quay] at q; rw [add_mul, one_mul] at this; omega
  · simp only [Zone.has, jetty] at q; omega
  simp only [Finset.sum_apply, bridgeOp, lift_app]
  split_ifs with hi
  · set s0 := (i - 16*2^k)/2^k
    have d1 : s0*2^k ≤ i - 16*2^k := Nat.div_mul_le_self _ _
    have d2 : i - 16*2^k < s0*2^k + 2^k := Nat.lt_div_mul_add hb
    rw [sum_eq_single s0 (fun s _ hs => sum_eq_zero fun c _ => sum_eq_zero
      fun j _ => if_neg (by
        simp only [Zone.has, jetty]; rintro ⟨q1, q2⟩
        exact hs (Nat.div_eq_of_lt_le (by omega) (by rw [add_mul, one_mul]; omega)).symm))
      (fun h' => absurd (mem_range.2 (show (i - 16*2^k)/2^k < 16 from
        (Nat.div_lt_iff_lt_mul hb).2 (by omega))) h')]
    have hc : (jetty (16*2^k) w (2^k) s0).has i := by simp only [Zone.has, jetty]; omega
    have e : 16*2^k + s0*2^k + (i - (16*2^k + s0*2^k)) = i := by omega
    simp only [hc, if_true]
    simp only [jetty, e, Zone.peek, quay, trestle, toeplitzApply, sum_blocks 16 (2^k)]
    refine sum_congr rfl fun c _ => ?_
    rw [sum_comm]; exact sum_congr rfl fun c' _ => (Finset.mul_sum _ _ _).symm
  · exact sum_eq_zero fun s _ => sum_eq_zero fun c _ => sum_eq_zero
      fun j _ => if_neg (by simp only [Zone.has, jetty]; omega)

def reachSize (e : ℕ) : ℕ :=
  if e<4 then let p := 2^e; p*(p*(p*26))
  else 16*(16*(16*(4*(80*(e-4)+348))))

def toeplitzBridge (e w : ℕ) (h g r : Line) : Reel :=
  if e<4 then naiveToeplitzReel (2^e) w h g else toeplitzGridReel (e-4) (r (e-4+1)) w h g

def Springs (e : ℕ) (r : Line) : Prop :=
  ∀ i ≤ e, Spectral.PrimRoot (r i) (2^i)

def chorus : ℕ → ℕ
  | 0 => 1
  | e+1 => chorus e + reachSize e

def hoop (e v : ℕ) (h g r : Line) (a b : Reel) : Reel :=
  let n := 2^e
  (parallel (min n v) a b).stack
    (if n<v then toeplitzBridge e (v-n) h g r else wait (reachSize e))

def toeplitzReel (h g r : Line) : ℕ → ℕ → Reel
  | 0,v => swatch v (fun _ => h 0)
  | e+1,v => hoop e v h g r (toeplitzReel h g r e (min (2^e) v)) (toeplitzReel h g r e (v-2^e))

lemma beats_harp (h g r : Line) (e v : ℕ) :
    (toeplitzReel h g r e v).beats=chorus e := by
  induction e generalizing v with
  | zero => rfl
  | succ e ih =>
    simp only [toeplitzReel, hoop, beats_stack, beats_parallel, ih, chorus]
    congr 1
    split_ifs
    · unfold toeplitzBridge reachSize; split_ifs
      · exact beats_riprap fun _ _ _ => beats_speck _ _ _ _ _ _ _
      · exact beats_riprap fun _ _ _ => beats_gravel _ _ _ _ _ _ _ _
    · rfl

lemma chorus_le (e : ℕ) :
    chorus e ≤ 10000000*(e+1)^2 := by
  induction e with
  | zero => simp [chorus]
  | succ e ih =>
    have : reachSize e ≤ 10000000*(2*e+3) := by
      unfold reachSize; split_ifs
      · interval_cases e <;> simp
      · omega
    simp only [chorus]; nlinarith

lemma fits_of {u : Zone} {n : ℕ} (h : u.lo + u.wide ≤ n) : u.Fits n :=
  fun i hi => by have := hi.2; omega

lemma sound_atBase {o N : ℕ} {P : Reel} (h : P.Sound N) (n : ℕ) (hn : o + N ≤ n) :
    (atBase o P).Sound n := (Sound.parallel (sound_wait _ o) h rfl).wider hn

lemma sound_conv {n d : ℕ} {r : ℂ} {u v : Zone} {h : Line} (hu : u.Fits n) (hv : v.Fits n)
    (huw : u.wide = 2^d) (hvw : v.wide = 2^d) (huv : u.Sep v) : (cyclicConvReel d r u v h).Sound n := by
  have e : ∀ {z : Zone}, z.Fits n → z.wide = 2^d → z.lo + 2^d ≤ n := fun hz hw => by
    have := hz (_ + (2^d - 1)) ⟨Nat.le_add_right _ _, by have := Nat.two_pow_pos d; omega⟩; omega
  exact ((((sound_atBase (sound_pulse d r) n (e hu huw)).stack (sound_atBase (sound_pulse d r) n
    (e hv hvw))).stack (sound_flash hv hu (by omega) huv.symm _)).stack (sound_atBase
    (sound_back d r) n (e hu huw))).stack (sound_atBase (sound_back d r) n (e hv hvw))

lemma sound_well {n d : ℕ} {r : ℂ} {u v a b : Zone} {h : Line} (ha : a.Fits n) (hb : b.Fits n)
    (haw : a.wide = 2^d) (hbw : b.wide = 2^d) (hab : a.Sep b) (hu : u.Fits n) (hv : v.Fits n)
    (hua : u.Sep a) (hu' : u.wide ≤ a.wide) (hv' : v.wide ≤ b.wide) (hvb : v.Sep b) :
    (well d r u v a b h).Sound n := by
  have ta : ∀ t, (trail u a t).Sound n := fun t =>
    sound_flash (ha.slim hu') hu rfl (Sep.slim_left hua.symm hu') _
  have sb : ∀ t, (slice b v t).Sound n := fun t =>
    sound_flash hv (hb.slim hv') rfl (Sep.slim_left hvb.symm hv').symm _
  have c : ∀ h, (cyclicConvReel d r a b h).Sound n := fun _ => sound_conv ha hb haw hbw hab
  exact ((((((ta 1).stack (c _)).stack (ta _)).stack (c _)).stack (sb 1)).stack
    ((((ta 1).stack (c _)).stack (ta _)).stack (c _))).stack (sb _)

lemma sound_pair {n k : ℕ} {r : ℂ} {u v z l m : Zone} {b e y : ℕ} {h g : Line}
    (H : Slips k u v z l m) (hf : Wharf n u v z l m) :
    (toeplitzPairReel k r u v z l m b e y h g).Sound n := by
  have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (Nat.le_succ k)
  have ⟨H1, H2, H3, H4, H5⟩ := H
  have b1 : ∀ g, (toeplitzBlockReel k r u z l m b e g).Sound n := fun g =>
    sound_well hf.fitsL hf.fitsM H4 H5 hf.lm hf.fitsU hf.fitsZ hf.ul (by omega) (by omega) hf.zm
  have b2 : ∀ h, (toeplitzBlockReel k r z v l m e y h).Sound n := fun h =>
    sound_well hf.fitsL hf.fitsM H4 H5 hf.lm hf.fitsZ hf.fitsV hf.zl (by omega) (by omega) hf.vm
  exact (((b1 g).stack (b2 h)).stack (b1 _)).stack (b2 _)

lemma desc_num {e : ℕ} (h : ¬ e < 4) : 2^e = 16*2^(e-4) := by
  rw [show (16:ℕ) = 2^4 by norm_num, ← pow_add]; congr 1; omega

lemma sound_bridge {e w : ℕ} (h g r : Line) (hw : w ≤ 2^e) :
    (toeplitzBridge e w h g r).Sound (2^e + w) := by
  unfold toeplitzBridge; split_ifs with he
  · refine sound_strand fun s _ => sound_strand fun c _ => sound_strand fun j hj => ?_
    unfold naiveToeplitzCell; split_ifs with hs
    · exact sound_flash (u := jetty (2^e) w 1 s) (v := quay 1 j) (fits_of (by simp only [jetty]; omega)) (fits_of (by simp only [quay]; omega))
        (by simp only [jetty, quay]; omega)
        (fun i (h1 : 2^e + s*1 ≤ i ∧ _) (h2 : j*1 ≤ i ∧ i < j*1 + 1) => by omega) _
    · exact sound_wait _ _
  · rw [desc_num he] at hw ⊢
    exact sound_strand fun s hs => sound_strand fun c _ => sound_strand fun j hj =>
      sound_pair (cell_zones hs hj hw).1 (cell_zones hs hj hw).2

lemma bridge_gains {e w : ℕ} (h g r : Line) (hw : w ≤ 2^e) (hr : Springs e r) :
    Gains (toeplitzBridge e w h g r) (2^e) (bridgeOp (2^e) w h g) := by
  unfold toeplitzBridge; split_ifs with he
  · exact naive_gains h g hw
  · rw [desc_num he] at hw ⊢; exact grid_gains h g (hr _ (by omega)) hw

lemma sound_harp (h g r : Line) (e v : ℕ) (hv : v ≤ 2^e) :
    (toeplitzReel h g r e v).Sound v := by
  induction e generalizing v with
  | zero => exact sound_swatch _ _
  | succ e ih =>
    rw [pow_succ] at hv
    have hp := Sound.parallel (ih (min (2^e) v) (min_le_left _ _)) (ih (v - 2^e) (by omega))
      (by rw [beats_harp, beats_harp])
    rw [show min (2^e) v + (v - 2^e) = v by omega] at hp
    refine hp.stack ?_
    split_ifs
    · have := sound_bridge (e := e) (w := v - 2^e) h g r (by omega)
      rwa [show 2^e + (v - 2^e) = v by omega] at this
    · exact sound_wait _ _

lemma harp_go {h r : Line} (h0 : h 0 ≠ 0) : ∀ e v, v ≤ 2^e → Springs e r → ∀ x, ∀ i < v,
    (toeplitzReel h (toeplitzInv h) r e v).go x i = toeplitzApply v h x i
  | 0, v, hv, _, x, i, hi => by
    rw [toeplitzReel, swatch_go, if_pos hi]
    obtain rfl : v = 1 := by simp at hv; omega
    obtain rfl : i = 0 := by omega
    simp [toeplitzApply, rise]
  | e+1, v, hv, hr, x, i, hi => by
    rw [pow_succ] at hv
    have hr' : Springs e r := fun i hi => hr i (by omega)
    have A := harp_go h0 e _ (min_le_left (2^e) v) hr'
    have B := harp_go h0 e (v - 2^e) (by omega) hr'
    have P := go_parallel (sound_harp h (toeplitzInv h) r e _ (min_le_left (2^e) v))
      ((beats_harp ..).trans (beats_harp h (toeplitzInv h) r e (v - 2^e)).symm) x
    simp only [toeplitzReel, hoop, go_stack]
    split_ifs with c
    · rw [min_eq_left c.le] at A P ⊢
      have Y := fun j (hj : j < 2^e) => (P j).trans (by rw [if_pos hj, A x j hj])
      rw [((bridge_gains h (toeplitzInv h) r (by omega) hr') _).1, Pi.add_apply, bridgeOp,
        stencil_congr _ _ Y, stencil_congr _ _ fun c hc => recoil_back _ h x h0 c hc]
      have e1 := stencil_left (2^e) (v - 2^e) h x
      have e2 := stencil_right (2^e) (v - 2^e) h x
      rw [Nat.add_sub_cancel' c.le] at e1 e2
      by_cases ci : i < 2^e
      · rw [if_neg (by omega), add_zero, Y i ci, e1 i ci]
      · obtain ⟨k, rfl⟩ : ∃ k, i = 2^e + k := ⟨i - 2^e, by omega⟩
        rw [if_pos (by omega), P, if_neg (by omega), Nat.add_sub_cancel_left, B _ _ (by omega), e2]
        exact add_comm _ _
    · rw [min_eq_right (by omega)] at A P ⊢
      rw [go_wait, P, if_pos hi, A x i hi]

def Creates (p : Reel) (n : ℕ) (M : RootMat n) : Prop :=
  ∀ x, front n (p.go x)=M *ᵥ front n x

def echo (n : ℕ) : Reel := lace n fun i => n-1-i

def coda (n : ℕ) (u : Reel) : Reel := ((echo n).stack u).stack (echo n)

def voices (n : ℕ) (u : ℂ) (p : Reel) : Reel :=
  ((swatch n (roof u)).stack p).stack (swatch n (gap u))

def repeatV (n : ℕ) (u : ℂ) (p : Reel) : Reel :=
  ((swatch n (gap u)).stack (coda n p)).stack (swatch n (roof u))

def ode (n : ℕ) (u : ℂ) (p : Reel) : Reel :=
  ((repeatV n u p).stack (swatch n (fun i => (vandDiag u i)⁻¹))).stack (voices n u p)

def vandermondeReel (n : ℕ) (e : ℕ) (u : ℂ) (r : Line) : Reel :=
  let h := floorH u
  ode n u (toeplitzReel h (toeplitzInv h) r e n)

lemma sound_ballad (n e : ℕ) (u : ℂ) (r : Line) (h : n ≤ 2^e) :
    (vandermondeReel n e u r).Sound n := by
  have hT := sound_harp (floorH u) (toeplitzInv (floorH u)) r e n h
  have he : (echo n).Sound n := sound_tick (plain_sound _ fun i hi => by omega)
  exact ((((sound_swatch n _).stack ((he.stack hT).stack he)).stack (sound_swatch n _)).stack
    (sound_swatch n _)).stack (((sound_swatch n _).stack hT).stack (sound_swatch n _))

lemma creates_stack {a b : Reel} {n : ℕ} {M N : RootMat n} (ha : Creates a n M)
    (hb : Creates b n N) : Creates (a.stack b) n (N * M) := fun x => by
  rw [go_stack, hb, ha, Matrix.mulVec_mulVec]

lemma creates_swatch (n : ℕ) (d : Line) : Creates (swatch n d) n (fade n d) := fun x => by
  funext i; simp [front, swatch_go, fade, Matrix.mulVec_diagonal]

lemma creates_T {n : ℕ} {T : Reel} {h : Line} (hT : ∀ x i, i < n → T.go x i = toeplitzApply n h x i) :
    Creates T n (stairs n h) := fun x => by
  rw [← front_stencil]; funext i; exact hT x i i.isLt

lemma creates_coda {n : ℕ} {T : Reel} {h : Line}
    (hT : ∀ x i, i < n → T.go x i = toeplitzApply n h x i) :
    Creates (coda n T) n (stairs n h)ᵀ := fun x => by
  rw [← front_creep]; funext i
  have hi := i.isLt
  simp only [front, coda, go_stack, echo, lace_go, if_pos hi]
  rw [hT _ (n - 1 - i) (by omega), stencil_congr n h (y := fun j => x (n-1-j))
    (fun j hj => by rw [lace_go, if_pos hj])]
  exact stencil_reversed n h x i hi

lemma vandermondeReel_creates (n e : ℕ) (u : ℂ) (r : Line) (h : n ≤ 2^e) (hr : Springs e r)
    (hu : Spectral.PrimRoot u n) :
    Creates (vandermondeReel n e u r) n (rootVandermonde n u) := by
  have h0 : floorH u 0 ≠ 0 := by simp [floorH, gap]
  have hT := harp_go h0 e n h hr
  have key : Creates (vandermondeReel n e u r) n _ :=
    creates_stack (creates_stack (creates_stack (creates_stack (creates_swatch n (gap u))
      (creates_coda hT)) (creates_swatch n (roof u))) (creates_swatch n fun i => (vandDiag u i)⁻¹))
      (creates_stack (creates_stack (creates_swatch n (roof u)) (creates_T hT))
        (creates_swatch n (gap u)))
  intro x
  rw [key x, rootVandermonde_factor n u hu]
  congr 1
  simp only [vandLower, fade, transpose_mul, diagonal_transpose, Matrix.mul_assoc]

def vandermondeBeats (e : ℕ) := 2*chorus e+7

lemma beats_ballad (n e : ℕ) (u : ℂ) (r : Line) :
    (vandermondeReel n e u r).beats=vandermondeBeats e := by
  simp only [vandermondeReel, ode, repeatV, voices, coda, echo, lace, swatch, beats_stack,
    beats_tick, beats_harp, vandermondeBeats]
  ring

lemma score_le (e : ℕ) : vandermondeBeats e ≤ 20000000*(e+1)^2+7 := by
  unfold vandermondeBeats; have := chorus_le e; linarith

end
end PowerSaving.ReelKit
end OAI

namespace OAI
namespace PowerSaving
noncomputable section
namespace AxisTensor
open ReelKit Stroke Reel Spectral Matrix Finset Binary

abbrev Axes := ℕ → ℕ

def extent (r : Axes) : ℕ → ℕ
  | 0 => 1
  | j+1 => extent r j*r j

def Splits (r : Axes) (l : ℕ) := ∀ t<l, 2≤r t

namespace Splits
variable {r : Axes} {l : ℕ}

lemma cut (h : Splits r l) {j : ℕ} (g : j ≤ l) :
    Splits r j := fun t ht => h t (by omega)

lemma extent_pos (h : Splits r l) :
    0<extent r l := by
  induction l with
  | zero => exact Nat.one_pos
  | succ l ih => exact Nat.mul_pos (ih (h.cut (by omega))) (by have := h l (by omega); omega)

lemma extent_le {j : ℕ} (h : Splits r l) (hj : j≤l) :
    extent r j ≤ extent r l := by
  induction l with
  | zero =>
    obtain rfl : j = 0 := by omega
    exact le_rfl
  | succ l ih =>
    rcases Nat.lt_or_ge j (l+1) with hj' | hj'
    · exact (ih (h.cut (by omega)) (by omega)).trans
        (le_mul_of_one_le_right (Nat.zero_le _) (by have := h l (by omega); omega))
    · obtain rfl : j = l+1 := by omega
      exact le_rfl

lemma axes_le (h : Splits r l) :
    l < extent r l := by
  induction l with
  | zero => exact Nat.one_pos
  | succ l ih =>
    have := ih (h.cut (by omega)); have := h l (by omega)
    show l + 1 < extent r l * r l; nlinarith

lemma tree_bound (h : Splits r l) :
    ∑ j ∈ range (l+1), extent r j < 2*extent r l := by
  induction l with
  | zero => simp [extent]
  | succ l ih =>
    rw [sum_range_succ]
    have := ih (h.cut (by omega)); have := h l (by omega)
    have : 2 * extent r l ≤ extent r (l+1) := by show _ ≤ extent r l * r l; nlinarith
    omega

lemma div_lt (h : Splits r (l+1)) {i} (hi : i<extent r (l+1)) :
    i / r l < extent r l := (Nat.div_lt_iff_lt_mul (by have := h l (by omega); omega)).2 hi

lemma mod_lt (h : Splits r (l+1)) (i : ℕ) :
    i%r l < r l := Nat.mod_lt _ (by have := h l (by omega); omega)

lemma join_lt (_h : Splits r (l+1)) {a b} (ha : a < extent r l) (hb : b < r l) :
    a*r l+b < extent r (l+1) := DigitArith.lt_join ha hb

end Splits

abbrev Wood := ℕ → ℕ → ℂ

def knot (n : ℕ) (A B : Wood) : Wood := fun i k => ∑ j ∈ range n, A i j * B j k

def graft (r : ℕ) (X : Wood) (v : Line) : Line := fun i =>
  ∑ k ∈ range r, X i k*v k

def white : Wood := fun i j => if j=i then 1 else 0

def frame (n : ℕ) (X : Wood) : RootMat n := fun i j => X i.val j.val

def axisKron (r : Axes) (X : ℕ → Wood) : ℕ → Wood
  | 0 => fun _ _ => 1
  | j+1 => fun i k => axisKron r X j (i/r j) (k/r j) * X j (i%r j) (k%r j)

def leafM (u : Stroke) : Wood :=
  fun i j => if j=u.ix i then u.dye i else 0

def leafC (u : Stroke) : Wood :=
  fun i j =>
    if u.partner i=i then white i j
    else (if j=i then ca else 0)+(if j=u.partner i then cb else 0)

def trunk (q : Reel) (n : ℕ) : ℕ → Wood
  | 0 => white
  | t+1 => knot n (leafC (q.atBeat t)) (knot n (leafM (q.atBeat t)) (trunk q n t))

def axisRun (r : Axes) (l : ℕ) (p : ℕ → Reel) (x : Line) : ℕ → Line
  | 0 => x
  | t+1 =>
    let M := axisKron r (fun i => leafM ((p i).atBeat t)) l
    let C := axisKron r (fun i => leafC ((p i).atBeat t)) l
    graft (extent r l) C (graft (extent r l) M (axisRun r l p x t))

lemma graft_graft (n : ℕ) (A B : Wood) (x : Line) :
    graft n A (graft n B x) = graft n (knot n A B) x := by
  funext i
  simp only [graft, knot, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact sum_comm

lemma graft_congr {n : ℕ} (A : Wood) {x y : Line} (e : ∀ j < n, x j = y j) (i : ℕ) :
    graft n A x i = graft n A y i :=
  sum_congr rfl fun j hj => by rw [e j (mem_range.mp hj)]

lemma graft_white {n i : ℕ} (x : Line) (hi : i < n) : graft n white x i = x i := by
  simp [graft, white, hi]

lemma graft_ext {n : ℕ} {A B : Wood} (h : ∀ y, ∀ i < n, graft n A y i = graft n B y i)
    {i k : ℕ} (hi : i < n) (hk : k < n) : A i k = B i k := by
  simpa [graft, hk] using h (fun j => if j = k then 1 else 0) i hi

lemma send_graft {u : Stroke} {n : ℕ} (h : u.Sound n) (x : Line) {i : ℕ} (hi : i < n) :
    u.send x i = graft n (leafC u) (graft n (leafM u) x) i := by
  rw [graft_congr _ (x := graft n (leafM u) x) (y := applyM u x) (fun j hj => by
    simp [graft, leafM, applyM, h.bdix j hj])]
  show applyC u (applyM u x) i = _
  by_cases hp : u.partner i = i
  · simp [applyC, graft, leafC, white, hp, hi]
  · simp [applyC, graft, leafC, hp, add_mul, sum_add_distrib, hi, h.bdp i hi]

lemma reach_graft {q : Reel} {n : ℕ} (h : q.Sound n) (x : Line) :
    ∀ t ≤ q.beats, ∀ i < n, q.reach x t i = graft n (trunk q n t) x i := by
  intro t; induction t with
  | zero => intro _ i hi; exact (graft_white x hi).symm
  | succ t ih =>
    intro ht i hi
    show (q.atBeat t).send (q.reach x t) i = _
    rw [send_graft (h t (by omega)) _ hi,
      graft_congr _ (fun k hk => graft_congr _ (fun j hj => ih (by omega) j hj) k),
      graft_graft n (leafM (q.atBeat t)) (trunk q n t) x, graft_graft] <;> rfl

lemma canopy_knot (r : Axes) (A B : ℕ → Wood) (l : ℕ) :
    knot (extent r l) (axisKron r A l) (axisKron r B l) = axisKron r (fun j => knot (r j) (A j) (B j)) l := by
  induction l with
  | zero => funext i k; simp [knot, axisKron, extent]
  | succ l ih =>
    funext i k
    simp only [axisKron]
    rw [← ih]
    simp only [knot, extent]
    rw [sum_blocks, Finset.sum_mul]
    refine sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine sum_congr rfl fun c hc => ?_
    rw [DigitArith.div_join (mem_range.mp hc), DigitArith.mod_join (mem_range.mp hc)]; ring

lemma canopy_congr {r : Axes} {l : ℕ} (h : Splits r l) {A B : ℕ → Wood}
    (e : ∀ j < l, ∀ a < r j, ∀ c < r j, A j a c = B j a c) :
    ∀ i < extent r l, ∀ k < extent r l, axisKron r A l i k = axisKron r B l i k := by
  induction l with
  | zero => intro i _ k _; rfl
  | succ l ih =>
    intro i hi k hk
    simp only [axisKron]
    rw [ih (h.cut (by omega)) (fun j hj => e j (by omega)) _ (h.div_lt hi) _ (h.div_lt hk),
      e l (by omega) _ (h.mod_lt i) _ (h.mod_lt k)]

lemma canopy_white {r : Axes} {l : ℕ} (h : Splits r l) :
    ∀ i < extent r l, ∀ k < extent r l, axisKron r (fun _ => white) l i k = white i k := by
  induction l with
  | zero =>
    intro i hi k hk
    simp only [extent, Nat.lt_one_iff] at hi hk; subst hi; subst hk; simp [axisKron, white]
  | succ l ih =>
    intro i hi k hk
    simp only [axisKron]
    rw [ih (h.cut (by omega)) _ (h.div_lt hi) _ (h.div_lt hk)]
    simp only [white]
    by_cases e : k = i
    · subst e; simp
    · rw [if_neg e]
      have : ¬ (k / r l = i / r l ∧ k % r l = i % r l) := fun ⟨h1, h2⟩ =>
        e (by rw [← Nat.div_add_mod k (r l), ← Nat.div_add_mod i (r l), h1, h2])
      by_cases h1 : k / r l = i / r l <;> simp_all

theorem axisRun_eq_kron (r : Axes) (l : ℕ) (p : ℕ → Reel) (h : Splits r l) (b : ℕ)
    (hs : ∀ j<l, (p j).Sound (r j)) (hb : ∀ j<l, (p j).beats=b)
    (X : ℕ → Wood) (hx : ∀ j<l, Creates (p j) (r j) (frame (r j) (X j)))
    (x : Line) (i : ℕ) (hi : i<extent r l) :
    axisRun r l p x b i = graft (extent r l) (axisKron r X l) x i := by
  have run : ∀ t ≤ b, ∀ i < extent r l, axisRun r l p x t i =
      graft (extent r l) (axisKron r (fun j => trunk (p j) (r j) t) l) x i := by
    intro t; induction t with
    | zero =>
      intro _ i hi
      refine (graft_white x hi).symm.trans (sum_congr rfl fun k hk => ?_)
      rw [show axisKron r (fun j => trunk (p j) (r j) 0) l i k = white i k from
        canopy_white h i hi k (mem_range.mp hk)]
    | succ t ih =>
      intro ht i hi
      show graft _ _ (graft _ _ (axisRun r l p x t)) i = _
      rw [graft_congr _ (fun k hk => graft_congr _ (fun j hj => ih (by omega) j hj) k),
        graft_graft (extent r l) (axisKron r (fun j => leafM ((p j).atBeat t)) l), graft_graft,
        canopy_knot, canopy_knot] <;> rfl
  rw [run b le_rfl i hi]
  refine sum_congr rfl fun k hk => congrArg (· * x k) (canopy_congr h (fun j hj a ha c hc =>
    graft_ext (fun y i hi => ?_) ha hc) i hi k (mem_range.1 hk))
  have := congrFun (hx j hj y) ⟨i, hi⟩
  simp only [front, AxisTensor.frame, Matrix.mulVec, dotProduct] at this
  rw [← reach_graft (hs j hj) y b (hb j hj).ge i hi, show (p j).reach y b i = (p j).go y i by
    unfold Reel.go; rw [hb j hj], this]
  exact Fin.sum_univ_eq_sum_range (fun c => X j i c * y c) _

end AxisTensor
end
end PowerSaving
end OAI

namespace OAI
namespace PowerSaving.AxisTensor
open ReelKit Finset
noncomputable section

structure Reloc (n : ℕ) (q : ℕ → ℕ) : Prop where
  bd : ∀ j<n, q j<n
  inj : ∀ i<n, ∀ j<n, q i=q j → i=j

def seek (n : ℕ) (q : ℕ → ℕ) (i : ℕ) : ℕ := by
  classical
  exact if h : ∃ j : ℕ, j<n ∧ q j=i then Classical.choose h else 0

namespace Reloc
variable {n : ℕ} {q : ℕ→ℕ}

lemma image (h : Reloc n q) {i : ℕ} (hi : i < n) : ∃ j, j < n ∧ q j = i := by
  obtain ⟨j, hj, e⟩ := surj_on_of_inj_on_of_card_le (s := range n) (t := range n)
    (fun j _ => q j) (fun j hj => mem_range.2 (h.bd j (mem_range.1 hj)))
    (fun a b ha hb e => h.inj a (mem_range.1 ha) b (mem_range.1 hb) e) le_rfl i (mem_range.2 hi)
  exact ⟨j, mem_range.1 hj, e.symm⟩

lemma seeks (h : Reloc n q) {i : ℕ} (hi : i<n) :
    seek n q i < n ∧ q (seek n q i) = i := by
  have he := h.image hi
  unfold seek; rw [dif_pos he]; exact Classical.choose_spec he

lemma seeks_at (h : Reloc n q) {i : ℕ} (hi : i<n) :
    seek n q (q i) = i := by
  obtain ⟨h1, h2⟩ := h.seeks (h.bd i hi)
  exact h.inj _ h1 _ hi h2

lemma sum {A : Type*} [AddCommMonoid A] (h : Reloc n q) (f : ℕ → A) :
    ∑ i ∈ range n, f (q i) = ∑ i ∈ range n, f i :=
  sum_nbij q (fun a ha => mem_range.2 (h.bd a (mem_range.1 ha)))
    (fun a ha b hb e => h.inj a (mem_range.1 ha) b (mem_range.1 hb) e)
    (fun i hi => let ⟨j, hj, e⟩ := h.image (mem_range.1 hi); ⟨j, mem_range.2 hj, e⟩)
    (fun _ _ => rfl)

lemma sow {A : Type*} (h : Reloc n q) (f : ℕ → A) (z : A) :
    Tape.sow n n z (fun i => (q i,f i)) = Tape.tab n (fun i => f (seek n q i)) := by
  refine Tape.ext_look (by simp [Tape.tab]) z fun i hi => ?_
  simp only [Tape.len_sow] at hi
  obtain ⟨h1, h2⟩ := h.seeks hi
  rw [Tape.sow_look_written hi h1 h2 (fun s hs1 hs2 e => by
    have := h.inj s hs2 _ h1 (e.trans h2.symm); omega), Tape.look_tab, if_pos hi]

end Reloc

structure PowBlock where
  start : ℕ
  width : ℕ
  height : ℕ
  seat : ℕ
deriving DecidableEq

namespace PowBlock

def tip (s : PowBlock) := s.start+s.width
def addr (s : PowBlock) := s.start+s.seat

structure Mark (s : PowBlock) (n l : ℕ) : Prop where
  endsBy : s.tip ≤ n
  size : s.width=2^s.height
  tall : s.height ≤ l
  place : s.seat < s.width

namespace Mark
variable {s : PowBlock} {n l : ℕ}
lemma positive (h : Mark s n l) : 0<s.width := by rw [h.size]; positivity
lemma starts (h : Mark s n l) : s.start < s.tip := by
  have := h.positive; unfold tip; omega
end Mark

def same (s t : PowBlock) : Prop :=
  s.start=t.start ∧ s.width=t.width ∧ s.height=t.height

def fits (s t : PowBlock) : Prop :=
  same s t ∨ s.tip ≤ t.start ∨ t.tip ≤ s.start

structure PowBlockCover (n l : ℕ) (f : ℕ → PowBlock) : Prop where
  mark : ∀ i<n, (f i).Mark n l
  seam : ∀ i<n, ∀ j<n, (f i).fits (f j)
  fiber : ∀ i<n, ∀ j<n, (f i).addr=(f j).addr → i=j

def patch (n : ℕ) (f : ℕ → PowBlock) (j : ℕ) :=
  f (seek n (fun i => (f i).addr) j)

namespace PowBlockCover
variable {n l : ℕ} {f : ℕ → PowBlock}

lemma reloc (h : PowBlockCover n l f) : Reloc n fun i => (f i).addr :=
  ⟨fun j hj => by
    show (f j).addr < n
    have := (h.mark j hj).endsBy; have := (h.mark j hj).place; unfold addr; unfold tip at *; omega,
   h.fiber⟩

lemma matches_of_eq (h : PowBlockCover n l f) {i j : ℕ} (hi : i<n) (hj : j<n)
    (H : (f i).start=(f j).start) :
    (f i).same (f j) := by
  have := (h.mark i hi).starts; have := (h.mark j hj).starts
  rcases h.seam i hi j hj with e | e | e
  · exact e
  · omega
  · omega

lemma patch_addr (h : PowBlockCover n l f) {i : ℕ} (hi : i<n) :
    (patch n f i).addr=i := (h.reloc.seeks hi).2

lemma patch_mark (h : PowBlockCover n l f) {i : ℕ} (hi : i<n) :
    (patch n f i).Mark n l := h.mark _ (h.reloc.seeks hi).1

lemma patch_align (h : PowBlockCover n l f) {i j : ℕ} (hi : i<n) (H : (f i).start ≤ j)
    (G : j < (f i).tip) : (patch n f j).same (f i) ∧ (patch n f j).seat=j-(f i).start := by
  obtain ⟨h1, h2⟩ := h.reloc.seeks (lt_of_lt_of_le G (h.mark i hi).endsBy)
  set t := seek n (fun i => (f i).addr) j
  have hp := (h.mark _ h1).place
  have e : (f t).start + (f t).seat = j := h2
  have hs : (f t).same (f i) := by
    rcases h.seam _ h1 i hi with s | s | s
    · exact s
    all_goals unfold tip at s G; omega
  exact ⟨hs, show (f t).seat = _ by rw [← hs.1]; omega⟩

end PowBlockCover

def fringe (r : ℕ) (s t : PowBlock) : PowBlock :=
  ⟨s.start*r + s.width*t.start, s.width*t.width, s.height+t.height,
    s.seat*t.width + t.seat⟩

lemma Mark.fringe {s t : PowBlock} {n i r j : ℕ} (h : Mark s n i) (g : Mark t r j) :
    Mark (fringe r s t) (n*r) (i+j) where
  endsBy := by
    have a := Nat.mul_le_mul_left s.width (show t.start + t.width ≤ r from g.endsBy)
    have b := Nat.mul_le_mul_right r (show s.start + s.width ≤ n from h.endsBy)
    show s.start*r + s.width*t.start + s.width*t.width ≤ n*r
    nlinarith
  size := by show s.width*t.width = 2^(s.height+t.height); rw [h.size, g.size, pow_add]
  tall := by show s.height+t.height ≤ i+j; have := h.tall; have := g.tall; omega
  place := by
    show s.seat*t.width + t.seat < s.width*t.width
    have := h.place; have := g.place
    have := Nat.mul_le_mul_right t.width (show s.seat + 1 ≤ s.width by omega)
    nlinarith

lemma fr_unique {s t s' t' : PowBlock} (r j : ℕ) (hg : Mark t r j) (hg' : Mark t' r j)
    {n i : ℕ} (_ha : Mark s n i) (_ha' : Mark s' n i) (hs : s.fits s') (ht : t.fits t')
    (H : (fringe r s t).start < (fringe r s' t').tip)
    (G : (fringe r s' t').start < (fringe r s t).tip) :
    s.same s' ∧ t.same t' := by
  simp only [fringe, tip] at H G
  have e1 : t.start + t.width ≤ r := hg.endsBy
  have e2 : t'.start + t'.width ≤ r := hg'.endsBy
  rcases hs with hs | hs | hs
  · refine ⟨hs, ?_⟩
    obtain ⟨a1, a2, -⟩ := hs
    rw [← a1, ← a2] at H G
    rcases ht with ht | ht | ht
    · exact ht
    · exfalso; have := Nat.mul_le_mul_left s.width (show t.start + t.width ≤ t'.start from ht)
      nlinarith
    · exfalso; have := Nat.mul_le_mul_left s.width (show t'.start + t'.width ≤ t.start from ht)
      nlinarith
  · exfalso
    have := Nat.mul_le_mul_left s.width e1
    have := Nat.mul_le_mul_right r (show s.start + s.width ≤ s'.start from hs)
    nlinarith [Nat.zero_le (s'.width * t'.start)]
  · exfalso
    have := Nat.mul_le_mul_left s'.width e2
    have := Nat.mul_le_mul_right r (show s'.start + s'.width ≤ s.start from hs)
    nlinarith [Nat.zero_le (s.width * t.start)]

def attach (r : ℕ) (u v : ℕ → PowBlock) : ℕ → PowBlock := fun i =>
  fringe r (u (i/r)) (v (i%r))

lemma attach_quilt {n r i j : ℕ} {f g : ℕ → PowBlock} (hr : 0 < r) (hf : PowBlockCover n i f)
    (hg : PowBlockCover r j g) : PowBlockCover (n*r) (i+j) (attach r f g) := by
  have dv : ∀ k < n*r, k / r < n := fun k hk => (Nat.div_lt_iff_lt_mul hr).2 hk
  have md : ∀ k, k % r < r := fun k => Nat.mod_lt _ hr
  have mk : ∀ k < n*r, (attach r f g k).Mark (n*r) (i+j) := fun k hk =>
    (hf.mark _ (dv k hk)).fringe (hg.mark _ (md k))
  have ov : ∀ k < n*r, ∀ k' < n*r, (attach r f g k).start < (attach r f g k').tip →
      (attach r f g k').start < (attach r f g k).tip →
      (f (k/r)).same (f (k'/r)) ∧ (g (k%r)).same (g (k'%r)) := fun k hk k' hk' H G =>
    fr_unique r j (hg.mark _ (md k)) (hg.mark _ (md k')) (hf.mark _ (dv k hk))
      (hf.mark _ (dv k' hk')) (hf.seam _ (dv k hk) _ (dv k' hk')) (hg.seam _ (md k) _ (md k')) H G
  refine ⟨mk, fun k hk k' hk' => ?_, fun k hk k' hk' e => ?_⟩
  · by_cases H : (attach r f g k).start < (attach r f g k').tip
    · by_cases G : (attach r f g k').start < (attach r f g k).tip
      · obtain ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩⟩ := ov k hk k' hk' H G
        left
        refine ⟨?_, ?_, ?_⟩ <;> simp only [attach, fringe, a1, a2, a3, b1, b2, b3]
      · right; left; omega
    · right; right; omega
  · have pk := (mk k hk).place; have pk' := (mk k' hk').place
    have H : (attach r f g k).start < (attach r f g k').tip := by
      unfold addr at e; unfold tip; omega
    have G : (attach r f g k').start < (attach r f g k).tip := by
      unfold addr at e; unfold tip; omega
    obtain ⟨⟨a1, a2, -⟩, ⟨b1, b2, -⟩⟩ := ov k hk k' hk' H G
    have pt := (hg.mark _ (md k)).place; have pt' := (hg.mark _ (md k')).place
    simp only [attach, fringe, addr] at e
    rw [← a1, ← a2, ← b1, ← b2] at e
    rw [← b2] at pt'
    have e2 : (f (k/r)).seat * (g (k%r)).width + (g (k%r)).seat =
        (f (k'/r)).seat * (g (k%r)).width + (g (k'%r)).seat := by omega
    have s1 := DigitArith.div_join (a := (f (k/r)).seat) pt
    have s2 := DigitArith.mod_join (a := (f (k/r)).seat) pt
    rw [e2, DigitArith.div_join pt'] at s1
    rw [e2, DigitArith.mod_join pt'] at s2
    have q1 := hf.fiber _ (dv k hk) _ (dv k' hk') (by unfold addr; rw [a1, s1])
    have q2 := hg.fiber _ (md k) _ (md k') (by unfold addr; rw [b1, s2])
    rw [← Nat.div_add_mod k r, ← Nat.div_add_mod k' r, q1, q2]

end PowBlock

namespace PairBlocks
open ReelKit Stroke PowBlock
variable (u : Stroke)
def crown (i : ℕ) := min i (u.partner i)
def thickness (i : ℕ) := if i=u.partner i then 1 else 2
def up (i : ℕ) := if i=u.partner i then 0 else 1
def trim (i : ℕ) := if i=crown u i then thickness u i else 0
def tier (i : ℕ) := if i=crown u i then 0 else 1
def sums (i : ℕ) := ∑ a ∈ range i, trim u a
def block (i : ℕ) : PowBlock :=
  ⟨sums u (crown u i), thickness u i, up u i, tier u i⟩
variable {u}

lemma crown_partner {n i : ℕ} (h : u.Sound n) : crown u (u.partner i)=crown u i := by
  unfold crown; rw [h.pair, min_comm]

lemma crown_class {n i j : ℕ} (h : u.Sound n) (g : crown u i=crown u j) :
    j=i ∨ j=u.partner i := by
  unfold crown at g
  rcases min_choice i (u.partner i) with a|a <;> rcases min_choice j (u.partner j) with b|b <;>
    rw [a, b] at g
  · exact .inl g.symm
  · right; rw [g, h.pair]
  · exact .inr g.symm
  · left; rw [← h.pair j, ← g, h.pair]

lemma crown_idem {n a : ℕ} (h : u.Sound n) : crown u (crown u a) = crown u a := by
  rcases min_choice a (u.partner a) with e|e <;> rw [show crown u a = _ from e]
  · exact e
  · rw [crown_partner h]; exact e

lemma thick_eq {n i j : ℕ} (h : u.Sound n) (g : crown u i=crown u j) :
    thickness u j = thickness u i ∧ up u j = up u i := by
  rcases crown_class h g with rfl|rfl
  · exact ⟨rfl, rfl⟩
  · unfold thickness up; rw [h.pair]; constructor <;> split_ifs <;> first | rfl | omega

lemma trim_crown {n a : ℕ} (h : u.Sound n) : trim u (crown u a) = thickness u a := by
  unfold trim; rw [if_pos (crown_idem h).symm]; exact (thick_eq h (crown_idem (a := a) h).symm).1

lemma sum_trim {n : ℕ} (h : u.Sound n) : sums u n = n := by
  have key : ∀ a < n, trim u a = ((range n).filter fun b => crown u b = a).card := fun a ha => by
    unfold trim; split_ifs with c
    · have : (range n).filter (fun b => crown u b = a) = {a, u.partner a} := by
        ext b; simp only [mem_filter, mem_range, mem_insert, mem_singleton]
        constructor
        · rintro ⟨-, e⟩; exact crown_class h (c.symm.trans e.symm)
        · rintro (rfl|rfl)
          · exact ⟨ha, c.symm⟩
          · exact ⟨h.bdp _ ha, by rw [crown_partner h, ← c]⟩
      rw [this, thickness]; split_ifs with d
      · rw [← d]; simp
      · exact (card_pair d).symm
    · refine (card_eq_zero.2 (filter_eq_empty_iff.2 fun b _ e => c ?_)).symm
      rw [← e, crown_idem h]
  unfold sums
  rw [sum_congr rfl fun a ha => key a (mem_range.mp ha), ← card_eq_sum_card_fiberwise (f := crown u)
    fun b hb => mem_range.2 ((min_le_left _ _).trans_lt (mem_range.1 hb)), card_range]

theorem before {n a b : ℕ} (h : u.Sound n) (lt : crown u a < crown u b) :
    (block u a).tip ≤ (block u b).start := by
  have m := sum_le_sum_of_subset (f := trim u) (range_mono (show crown u a + 1 ≤ crown u b by omega))
  rw [sum_range_succ, trim_crown h] at m; exact m

lemma marked {n i : ℕ} (h : u.Sound n) (hi : i<n) : (block u i).Mark n 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have m := sum_le_sum_of_subset (f := trim u) (range_mono (show crown u i + 1 ≤ n by
      have := min_le_left i (u.partner i); unfold crown; omega))
    rw [sum_range_succ, trim_crown h, show ∑ a ∈ range n, trim u a = n from sum_trim h] at m; exact m
  · show thickness u i = 2^(up u i); unfold thickness up; split_ifs <;> rfl
  · show up u i ≤ 1; unfold up; split_ifs <;> omega
  · show tier u i < thickness u i; unfold tier thickness crown; split_ifs <;> omega

lemma class_of_start {n i j : ℕ} (h : u.Sound n) (hi : i<n) (hj : j<n)
    (g : (block u i).start=(block u j).start) :
    crown u i=crown u j := by
  have p1 := (marked h hi).starts; have p2 := (marked h hj).starts
  rcases lt_trichotomy (crown u i) (crown u j) with c|c|c
  · have := before h c; omega
  · exact c
  · have := before h c; omega

lemma tier_partner_ne {n i : ℕ} (h : u.Sound n) (g : u.partner i ≠ i) :
    tier u (u.partner i) ≠ tier u i := by
  unfold tier; rw [crown_partner h]; unfold crown; split_ifs <;> omega

lemma quilt {n : ℕ} (h : u.Sound n) : PowBlockCover n 1 (block u) := by
  refine ⟨fun i hi => marked h hi, fun i hi j hj => ?_, fun i hi j hj e => ?_⟩
  · rcases lt_trichotomy (crown u i) (crown u j) with c|c|c
    · exact .inr (.inl (before h c))
    · obtain ⟨a, b⟩ := thick_eq h c
      exact .inl ⟨by show sums u _ = sums u _; rw [c], a.symm, b.symm⟩
    · exact .inr (.inr (before h c))
  · have pi := (marked h hi).place; have pj := (marked h hj).place
    unfold addr at e
    rcases lt_trichotomy (crown u i) (crown u j) with c|c|c
    · have := before h c; unfold tip at *; omega
    · rcases crown_class h c with d|d
      · exact d.symm
      · by_cases q : u.partner i = i
        · rw [d, q]
        · have := tier_partner_ne h q; rw [← d] at this
          simp only [block] at e; rw [c] at e; omega
    · have := before h c; unfold tip at *; omega

end PairBlocks
open PowBlock PairBlocks

def seed : PowBlock := ⟨0,1,0,0⟩

def strokeBlocks (r : Axes) (u : ℕ → Stroke) : ℕ → ℕ → PowBlock
  | 0 => fun _ => seed
  | l+1 => attach (r l) (strokeBlocks r u l) (block (u l))

lemma mosaic_quilt (r : Axes) (l : ℕ) (u : ℕ→Stroke)
    (h : Splits r l) (g : ∀ i<l, (u i).Sound (r i)) :
    PowBlockCover (extent r l) l (strokeBlocks r u l) := by
  induction l with
  | zero =>
    refine ⟨fun i hi => ⟨?_, rfl, le_rfl, Nat.one_pos⟩, fun i _ j _ => Or.inl ⟨rfl, rfl, rfl⟩,
      fun i hi j hj _ => ?_⟩
    · show 0 + 1 ≤ 1; omega
    · simp only [extent] at hi hj; omega
  | succ l ih =>
    exact attach_quilt (by have := h l (by omega); omega) (ih (h.cut (by omega))
      (fun i hi => g i (by omega))) (quilt (g l (by omega)))

end
end PowerSaving.AxisTensor
end OAI

namespace OAI
namespace PowerSaving.AxisTensor
open Finset Spectral
noncomputable section

structure CoprimeAxes (r : Axes) (l : ℕ) : Prop where
  good : Splits r l
  apart : ∀ i<l, (r i).Coprime (extent r i)

lemma CoprimeAxes.cut {r : Axes} {l : ℕ} (h : CoprimeAxes r l) {i : ℕ} (hi : i ≤ l) :
    CoprimeAxes r i := ⟨h.good.cut hi, fun j hj => h.apart j (by omega)⟩

def tide (p r a b : ℕ) := (a*r+b*p)%(p*r)

def crtIndex (r : Axes) : ℕ → ℕ → ℕ
  | 0 => fun _ => 0
  | l+1 => fun i =>
    tide (extent r l) (r l) (crtIndex r l (i/r l)) (i%r l)

def axisRoot (Z : ℂ) (N q : ℕ) := Z^((N/q)*(N/q))

def gale (Z : ℂ) : Wood := fun i j => Z^(i*j)

lemma split_axis {r : Axes} {l : ℕ} (h : CoprimeAxes r l) :
    ∀ i < l, r i ∣ extent r l ∧ (r i).Coprime (extent r l / r i) := by
  induction l with
  | zero => intro i hi; omega
  | succ l ih =>
    intro i hi
    have hr : 0 < r l := by have := h.good l (by omega); omega
    rcases Nat.lt_or_ge i l with hil | hil
    · obtain ⟨d, c⟩ := ih (h.cut (by omega)) i hil
      refine ⟨Dvd.dvd.mul_right d _, ?_⟩
      show (r i).Coprime (extent r l * r l / r i)
      rw [← Nat.div_mul_right_comm d]
      exact c.mul_right (Nat.Coprime.coprime_dvd_right d (h.apart l (by omega))).symm
    · obtain rfl : i = l := by omega
      refine ⟨dvd_mul_left _ _, ?_⟩
      show (r i).Coprime (extent r i * r i / r i)
      rw [Nat.mul_div_cancel _ hr]; exact h.apart i (by omega)

lemma prim_pow_coprime {ζ : ℂ} {k m : ℕ} (h : PrimRoot ζ k) (hc : m.Coprime k) :
    PrimRoot (ζ^m) k :=
  ⟨by rw [← pow_mul, mul_comm, pow_mul, h.pow_eq_one, one_pow],
   fun l hl => hc.symm.dvd_mul_left.mp (h.dvd_of_pow_eq_one _ (by rw [pow_mul, hl]))⟩

lemma spray_axis {Z : ℂ} {r : Axes} {l : ℕ} (h : CoprimeAxes r l)
    (hh : Spectral.PrimRoot Z (extent r l)) :
    ∀ i<l, Spectral.PrimRoot (axisRoot Z (extent r l) (r i)) (r i) := fun i hi => by
  obtain ⟨d, c⟩ := split_axis h i hi
  have hE := h.good.extent_pos
  have hri : 0 < r i := by have := h.good i hi; omega
  have hp : 0 < extent r l / r i := Nat.div_pos (Nat.le_of_dvd hE d) hri
  have h1 := hh.pow_of_dvd (Nat.pos_iff_ne_zero.mp hp) (Nat.div_dvd_of_dvd d)
  rw [Nat.div_div_self d (by omega)] at h1
  unfold axisRoot; rw [pow_mul]
  exact prim_pow_coprime h1 c.symm

lemma tide_inj {p r a b a' b' : ℕ} (hc : p.Coprime r) (ha : a < p) (ha' : a' < p) (hb : b < r)
    (hb' : b' < r) (e : tide p r a b = tide p r a' b') : a = a' ∧ b = b' := by
  unfold tide at e
  have e1 : (a*r+b*p) % (p*r) % p = (a'*r+b'*p) % (p*r) % p := by rw [e]
  have e2 : (a*r+b*p) % (p*r) % r = (a'*r+b'*p) % (p*r) % r := by rw [e]
  rw [Nat.mod_mod_of_dvd _ (dvd_mul_right p r), Nat.mod_mod_of_dvd _ (dvd_mul_right p r),
    Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right] at e1
  rw [Nat.mod_mod_of_dvd _ (dvd_mul_left r p), Nat.mod_mod_of_dvd _ (dvd_mul_left r p),
    add_comm (a*r), add_comm (a'*r), Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right] at e2
  have f1 := Nat.ModEq.cancel_right_of_coprime hc e1
  have f2 := Nat.ModEq.cancel_right_of_coprime hc.symm e2
  unfold Nat.ModEq at f1 f2
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha'] at f1
  rw [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hb'] at f2
  exact ⟨f1, f2⟩

theorem ford_rel {r : Axes} {l : ℕ} (h : CoprimeAxes r l) :
    Reloc (extent r l) (crtIndex r l) := by
  induction l with
  | zero => exact ⟨fun _ _ => Nat.one_pos, fun i hi j hj _ => by simp only [extent] at hi hj; omega⟩
  | succ l ih =>
    have R := ih (h.cut (by omega))
    have g := h.good
    have hr : 0 < r l := by have := g l (by omega); omega
    have hE := (g.cut (Nat.le_succ l)).extent_pos
    refine ⟨fun j _ => Nat.mod_lt _ (Nat.mul_pos hE hr), fun i hi j hj e => ?_⟩
    obtain ⟨e1, e2⟩ := tide_inj (h.apart l (by omega)).symm (R.bd _ (g.div_lt hi))
      (R.bd _ (g.div_lt hj)) (g.mod_lt i) (g.mod_lt j) e
    have := R.inj _ (g.div_lt hi) _ (g.div_lt hj) e1
    rw [← Nat.div_add_mod i (r l), ← Nat.div_add_mod j (r l), this, e2]

lemma pow_eq_of_mod {z : ℂ} {N a b : ℕ} (hz : z^N = 1) (h : a % N = b % N) : z^a = z^b := by
  rw [← power_mod hz a, h, power_mod hz]

lemma canopy_pow {r : Axes} {E : ℕ} {z : ℂ} (hz : z^E = 1) : ∀ l Q, E = Q * extent r l →
    (∀ j < l, 0 < r j) → ∀ i k, axisKron r (fun j => gale (axisRoot z E (r j))) l i k =
      z^(Q*Q*(crtIndex r l i * crtIndex r l k))
  | 0, _, _, _, _, _ => by simp [axisKron, crtIndex]
  | l+1, Q, hE, hp, i, k => by
    have hr := hp l (by omega)
    simp only [extent] at hE
    have hd : E / r l = Q * extent r l := by rw [hE, ← mul_assoc, Nat.mul_div_cancel _ hr]
    show axisKron r _ l (i / r l) (k / r l) * gale (axisRoot z E (r l)) (i % r l) (k % r l) =
      z^(Q*Q*(tide (extent r l) (r l) (crtIndex r l (i / r l)) (i % r l) *
        tide (extent r l) (r l) (crtIndex r l (k / r l)) (k % r l)))
    rw [canopy_pow hz l (Q * r l) (by rw [hE]; ring) fun j hj => hp j (by omega)]
    simp only [gale, axisRoot, tide, hd]
    rw [← pow_mul, ← pow_add]
    refine pow_eq_of_mod hz ?_
    generalize crtIndex r l (i / r l) = a; generalize crtIndex r l (k / r l) = a'
    generalize i % r l = b; generalize k % r l = b'
    generalize extent r l = P at hE ⊢; generalize r l = R at hE ⊢
    subst hE
    have M := ((Nat.mod_modEq (a*R+b*P) (P*R)).mul (Nat.mod_modEq (a'*R+b'*P) (P*R))).mul_left'
      (Q*Q)
    rw [show Q*Q*(P*R) = Q*(Q*(P*R)) by ring] at M
    refine ((M.of_mul_left Q).trans ?_).symm
    rw [show Q*Q*((a*R+b*P)*(a'*R+b'*P)) = Q*R*(Q*R)*(a*a') + Q*P*(Q*P)*(b*b') +
      Q*(P*R)*(Q*(a*b'+a'*b)) by ring]
    exact Nat.add_mul_mod_self_left _ _ _

lemma crt_freq {r : Axes} {l : ℕ} {z : ℂ} (h : CoprimeAxes r l)
    (hh : Spectral.PrimRoot z (extent r l)) (x : Line) (i : ℕ) (hi : i<extent r l) :
    graft (extent r l) (axisKron r (fun i => gale (axisRoot z (extent r l) (r i))) l)
      (fun j => x (crtIndex r l j)) i =
    freq (extent r l) z x (crtIndex r l i) := by
  simp only [graft, canopy_pow hh.pow_eq_one l 1 (one_mul _).symm fun j hj => by
    have := h.good j hj; omega, one_mul]
  exact (ford_rel h).sum (fun m => z^(crtIndex r l i * m) * x m)

end
end PowerSaving.AxisTensor
end OAI

namespace OAI
namespace PowerSaving.Modulus
open Finset Real
noncomputable section

def axisBudget (n : ℕ) := Nat.log 2 (2*n)+1

lemma stack_above (n : ℕ) :
    2*n < 2^axisBudget n := Nat.lt_pow_succ_log_self (by norm_num) _

lemma stack_pow (n : ℕ) (hn : 0<n) :
    2^axisBudget n ≤ 4*n := by
  unfold axisBudget; rw [pow_succ]
  have := Nat.pow_log_le_self 2 (show 2*n ≠ 0 by omega); omega

lemma stack_le (n : ℕ) (hn : 0<n) :
    axisBudget n ≤ 4*n := by
  have := stack_pow n hn; have : axisBudget n < 2^axisBudget n := Nat.lt_two_pow_self; omega

def primeSearchBound (k : ℕ) := (16*(k+4))^2

def Bar (i : ℕ) := Nat.Prime i ∧ i>2

instance (i) : Decidable (Bar i) := inferInstanceAs (Decidable (_ ∧ _))

def bars (p : ℕ) := ((range p).filter Bar).card

lemma bars_succ (p : ℕ) : bars (p+1) = bars p + if Bar p then 1 else 0 := by
  unfold bars; rw [card_filter, card_filter, sum_range_succ]

lemma oddPrime_count_ge (S : ℕ) : S ≤ bars (primeSearchBound S + 1) := by
  by_contra hS
  push_neg at hS
  have hB : primeSearchBound S = 2 * (128*(S+4)^2) := by unfold primeSearchBound; ring
  generalize hm : 128*(S+4)^2 = m at hB
  have m4 : 4 ≤ m := by rw [← hm]; nlinarith
  have hcb : Nat.centralBinom m ≤ (2*m) ^ ((range (2*m+1)).filter Nat.Prime).card := by
    calc Nat.centralBinom m = ∏ p ∈ range (2*m+1), p ^ (Nat.centralBinom m).factorization p :=
          (Nat.prod_pow_factorization_centralBinom m).symm
      _ ≤ ∏ p ∈ range (2*m+1), (if p.Prime then 2*m else 1) :=
          prod_le_prod' fun p _ => by
            split_ifs with hp
            · rw [Nat.centralBinom_eq_two_mul_choose]
              exact Nat.pow_factorization_choose_le (by omega)
            · rw [Nat.factorization_eq_zero_of_not_prime _ hp, pow_zero]
      _ = _ := by rw [prod_ite, prod_const, prod_const_one, mul_one]
  have hπ : ((range (2*m+1)).filter Nat.Prime).card ≤ S := by
    have h1 : (range (2*m+1)).filter Nat.Prime ⊆ insert 2 ((range (2*m+1)).filter Bar) := by
      intro p hp
      rw [mem_filter] at hp
      rw [mem_insert, mem_filter]
      by_cases h2 : p = 2
      · exact Or.inl h2
      · exact Or.inr ⟨hp.1, hp.2, by have := hp.2.two_le; omega⟩
    have := (card_le_card h1).trans (card_insert_le _ _)
    unfold bars at hS; rw [hB] at hS
    omega
  have h5 : (2*m)^(S+1) ≤ 4^m := by
    have hN : 2*m = (16*(S+4))*(16*(S+4)) := by rw [← hm]; ring
    have hNle : 16*(S+4) ≤ 2^(16*(S+4)) := Nat.lt_two_pow_self.le
    calc (2*m)^(S+1) = (16*(S+4))^(2*(S+1)) := by rw [hN, ← sq, ← pow_mul]
      _ ≤ (2^(16*(S+4)))^(2*(S+1)) := Nat.pow_le_pow_left hNle _
      _ = 2^(16*(S+4)*(2*(S+1))) := by rw [← pow_mul]
      _ ≤ 2^((16*(S+4))*(16*(S+4))) :=
          Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (by omega))
      _ = 4^m := by rw [← hN, pow_mul]; norm_num
  have h3 := Nat.four_pow_lt_mul_centralBinom m m4
  have h4 : (2*m) ^ ((range (2*m+1)).filter Nat.Prime).card ≤ (2*m)^S :=
    Nat.pow_le_pow_right (by omega) hπ
  have h6 : m * (2*m)^S ≤ (2*m)^(S+1) := by
    rw [pow_succ, mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
  have := Nat.mul_le_mul_left m (hcb.trans h4)
  omega

end
end PowerSaving.Modulus
end OAI

namespace OAI
namespace PowerSaving.Modulus
open AxisTensor
noncomputable section

structure PrimeList where
  l : ℕ
  q : Axes
  vol : ℕ

namespace PrimeList

def empty : PrimeList := ⟨0,fun _ => 0,1⟩

def pushQ (x : PrimeList) (p : ℕ) : PrimeList :=
  ⟨x.l+1,fun i => if i=x.l then p else x.q i, x.vol*p⟩

structure Square (x : PrimeList) : Prop where
  agrees : x.vol=extent x.q x.l
  isles : CoprimeAxes x.q x.l

variable {x : PrimeList}

lemma extent_congr {r r' : Axes} {l : ℕ} (h : ∀ i < l, r i = r' i) : extent r l = extent r' l := by
  induction l with
  | zero => rfl
  | succ l ih =>
    show extent r l * r l = extent r' l * r' l
    rw [ih (fun i hi => h i (by omega)), h l (by omega)]

theorem Square.push (h : x.Square) {p : ℕ} (hp : 2 ≤ p) (hc : p.Coprime x.vol) :
    (x.pushQ p).Square := by
  have ec : ∀ j ≤ x.l, extent (x.pushQ p).q j = extent x.q j := fun j hj =>
    extent_congr fun i hi => if_neg (by omega)
  refine ⟨?_, ⟨fun t ht => ?_, fun i hi => ?_⟩⟩
  · show x.vol * p = extent (x.pushQ p).q x.l * (x.pushQ p).q x.l
    rw [ec _ le_rfl, ← h.agrees]; show _ = x.vol * (if x.l = x.l then p else _); rw [if_pos rfl]
  · show 2 ≤ if t = x.l then p else x.q t
    split_ifs with e
    · exact hp
    · exact h.isles.good t (by have : t < x.l + 1 := ht; omega)
  · have hi' : i < x.l + 1 := hi
    rw [ec i (by omega)]
    show (if i = x.l then p else x.q i).Coprime _
    split_ifs with e
    · subst e; rw [← h.agrees]; exact hc
    · exact h.isles.apart i (by omega)

end PrimeList
open PrimeList

def greedyPrimes (N : ℕ) : ℕ → PrimeList
  | 0 => PrimeList.empty
  | p+1 =>
    let x := greedyPrimes N p
    if Bar p ∧ x.vol*p ≤ N then x.pushQ p else x

structure Baler (N p : ℕ) (x : PrimeList) : Prop where
  square : x.Square
  odd : Odd x.vol
  top : x.vol ≤ N
  pw : 3^x.l ≤ x.vol
  vars : ∀ i<x.l, Bar (x.q i) ∧ x.q i<p
  more : ∀ q, p≤q → Bar q → q.Coprime x.vol
  hit : x.l=bars p ∨ ∃ q<p, Bar q ∧ N<x.vol*q

lemma reap_baler {N : ℕ} (hN : 1 ≤ N) : ∀ p, Baler N p (greedyPrimes N p) := by
  intro p; induction p with
  | zero =>
    exact ⟨⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩,
      odd_one, hN, le_rfl, fun _ h => absurd h (Nat.not_lt_zero _), fun q _ _ => q.coprime_one_right,
      .inl (by simp [bars, greedyPrimes, PrimeList.empty])⟩
  | succ p ih =>
    show Baler N (p+1) (if Bar p ∧ (greedyPrimes N p).vol*p ≤ N then _ else _)
    generalize greedyPrimes N p = x at ih
    have hb := bars_succ p
    split_ifs with hc
    · obtain ⟨hbar, hle⟩ := hc
      have hp3 : 3 ≤ p := hbar.2
      have hodd : Odd p := hbar.1.odd_of_ne_two (by omega)
      refine ⟨ih.square.push (by omega) (ih.more p le_rfl hbar), ih.odd.mul hodd, hle, ?_, ?_, ?_, ?_⟩
      · show 3^(x.l+1) ≤ x.vol * p
        rw [pow_succ]; exact Nat.mul_le_mul ih.pw hp3
      · intro i hi
        show Bar (if i = x.l then p else x.q i) ∧ (if i = x.l then p else x.q i) < p + 1
        split_ifs with e
        · exact ⟨hbar, by omega⟩
        · have := ih.vars i (by have : i < x.l + 1 := hi; omega); exact ⟨this.1, by omega⟩
      · intro q hq hbq
        exact (ih.more q (by omega) hbq).mul_right
          ((Nat.coprime_primes hbq.1 hbar.1).mpr (by omega))
      · rw [hb, if_pos hbar]
        rcases ih.hit with e | ⟨q, hq, hbq, hlt⟩
        · left; show x.l + 1 = _; omega
        · exact .inr ⟨q, by omega, hbq, show N < x.vol * p * q by
            nlinarith [Nat.mul_le_mul_left (x.vol * q) (show 1 ≤ p by omega)]⟩
    · refine ⟨ih.square, ih.odd, ih.top, ih.pw, fun i hi => ⟨(ih.vars i hi).1,
        by have := (ih.vars i hi).2; omega⟩, fun q hq hbq => ih.more q (by omega) hbq, ?_⟩
      rw [hb]
      rcases ih.hit with e | ⟨q, hq, hbq, hlt⟩
      · by_cases hbar : Bar p
        · right; exact ⟨p, by omega, hbar, by push_neg at hc; exact hc hbar⟩
        · left; rw [if_neg hbar]; omega
      · right; exact ⟨q, by omega, hbq, hlt⟩

def primeSearchLimit (n : ℕ) := primeSearchBound (axisBudget n)

def oddPart (n : ℕ) := greedyPrimes (2*n) (primeSearchLimit n+1)

def twoPartFill (N p : ℕ) : ℕ→ℕ
  | 0 => 1
  | k+1 => let q := twoPartFill N p k
           if p*q<N then q*2 else q

lemma fill_spec {N v : ℕ} (hv : 0 < v) (hvN : v < N) : ∀ k, (∃ c, twoPartFill N v k = 2^c) ∧
    v * twoPartFill N v k < 2*N ∧ (N ≤ v * twoPartFill N v k ∨ twoPartFill N v k = 2^k) ∧
    (1 ≤ k → 2 ≤ twoPartFill N v k) := by
  intro k; induction k with
  | zero => exact ⟨⟨0, rfl⟩, by show v * 1 < 2*N; omega, Or.inr rfl, fun h => absurd h (by omega)⟩
  | succ k ih =>
    obtain ⟨⟨c, hc⟩, h2, h3, h4⟩ := ih
    rw [show twoPartFill N v (k+1) = if v * twoPartFill N v k < N then twoPartFill N v k * 2
      else twoPartFill N v k from rfl]
    have one : 1 ≤ twoPartFill N v k := by rw [hc]; exact Nat.one_le_two_pow
    split_ifs with e
    · refine ⟨⟨c+1, by rw [hc, pow_succ]⟩, by rw [← mul_assoc]; omega, ?_, fun _ => by omega⟩
      rcases h3 with h3 | h3
      · omega
      · right; rw [h3, pow_succ]
    · refine ⟨⟨c, hc⟩, h2, Or.inl (by omega), fun _ => ?_⟩
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; simp [twoPartFill] at e; omega
      · exact h4 hk

def twoPart (n : ℕ) := twoPartFill (2*n) (oddPart n).vol (axisBudget n)

def modulusAxes (n : ℕ) := (oddPart n).pushQ (twoPart n)

def axisLogBound (n : ℕ) := Nat.log 2 (2*primeSearchLimit n)+2

lemma limit_pos (n : ℕ) : 1 ≤ primeSearchLimit n := by
  unfold primeSearchLimit primeSearchBound; show 0 < _; positivity

lemma orderE_small (n : ℕ) :
    2^axisLogBound n ≤ 8*primeSearchLimit n := by
  have := Nat.pow_log_le_self 2 (show 2*primeSearchLimit n ≠ 0 by have := limit_pos n; omega)
  have e : 2^axisLogBound n = 2^(Nat.log 2 (2*primeSearchLimit n)) * 4 := by
    unfold axisLogBound; rw [pow_add]; norm_num
  omega

lemma limit_lt (n : ℕ) : 2 * primeSearchLimit n < 2^axisLogBound n := by
  have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (2*primeSearchLimit n)
  have e : 2^axisLogBound n = 2^(Nat.log 2 (2*primeSearchLimit n)) * 4 := by
    unfold axisLogBound; rw [pow_add]; norm_num
  rw [pow_succ] at this; omega

structure ModulusSpec (n : ℕ) (x : PrimeList) : Prop where
  square : x.Square
  lower : 2*n ≤ x.vol
  upper : x.vol < 4*n
  count : x.l ≤ axisBudget n
  sizes : ∀ i<x.l,x.q i≤2^axisLogBound n

theorem modulusAxes_spec (n : ℕ) (hn : 0<n) :
    ModulusSpec n (modulusAxes n) := by
  have B : Baler (2*n) (primeSearchLimit n + 1) (oddPart n) := reap_baler (by omega) _
  have hL := limit_lt n
  set x := oddPart n with hx
  have hv : 0 < x.vol := B.odd.pos
  have hvN : x.vol < 2*n := B.top.lt_of_ne fun h => by
    obtain ⟨k, hk⟩ := B.odd; omega
  have h2S := stack_above n
  obtain ⟨q, hq, hbq, hlt⟩ : ∃ q < primeSearchLimit n + 1, Bar q ∧ 2*n < x.vol * q := by
    rcases B.hit with e | e
    · have c1 : axisBudget n ≤ x.l := by rw [e]; exact oddPrime_count_ge _
      have := Nat.pow_le_pow_right (show 0 < 3 by norm_num) c1
      have := Nat.pow_le_pow_left (show 2 ≤ 3 by norm_num) (axisBudget n)
      have := B.pw; have := B.top; omega
    · exact e
  obtain ⟨⟨c, hc⟩, f2, f3, f4⟩ := fill_spec hv hvN (axisBudget n)
  have hS1 : 1 ≤ axisBudget n := by unfold axisBudget; omega
  have ht := f4 hS1
  have hlow : 2*n ≤ x.vol * twoPart n := by
    rcases f3 with f3 | f3
    · exact f3
    · show 2*n ≤ x.vol * twoPartFill (2*n) x.vol (axisBudget n)
      rw [f3]; nlinarith
  have hodd2 : (twoPart n).Coprime x.vol := by
    show (twoPartFill _ _ _).Coprime _
    rw [hc]; refine .pow_left c ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 fun ⟨j, hj⟩ => ?_)
    obtain ⟨k, hk⟩ := B.odd; omega
  have htq : twoPart n < 2 * q := by
    have : x.vol * twoPart n < x.vol * (2 * q) := by
      show x.vol * twoPartFill (2*n) x.vol (axisBudget n) < _; nlinarith
    exact Nat.lt_of_mul_lt_mul_left this
  refine ⟨B.square.push ht hodd2, hlow,
    by show x.vol * twoPartFill (2*n) x.vol (axisBudget n) < 4*n; omega, ?_, ?_⟩
  · show x.l + 1 ≤ axisBudget n
    have h3 : 2^x.l ≤ 3^x.l := Nat.pow_le_pow_left (by norm_num) _
    have := Nat.le_log_of_pow_le (by norm_num : 1 < 2) (show 2^x.l ≤ 2*n by have := B.pw; omega)
    unfold axisBudget; omega
  · intro i hi
    show (if i = x.l then twoPart n else x.q i) ≤ _
    split_ifs with e
    · omega
    · have := (B.vars i (by have : i < x.l + 1 := hi; omega)).2; omega

def IsLargeLen (n : ℕ) := 2^axisLogBound n ≤ n

instance (n) : Decidable (IsLargeLen n) := inferInstanceAs (Decidable (_ ≤ _))

def largeWorkModulus (n : ℕ) := (2*n)*(modulusAxes n).vol*2^axisLogBound n

def workModulus (n : ℕ) := if IsLargeLen n then largeWorkModulus n else n

theorem receipt_bound (n : ℕ) (hn : 0<n) :
    0<workModulus n ∧ workModulus n < 8*n^3 := by
  have S := modulusAxes_spec n hn
  unfold workModulus
  split_ifs with h
  · have hP : 0 < 2^axisLogBound n := by positivity
    have h1 : IsLargeLen n := h
    unfold IsLargeLen at h1
    unfold largeWorkModulus
    have a := S.upper; have b := S.lower
    constructor
    · exact Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) hP
    · have h2 : 2*n*(modulusAxes n).vol*2^axisLogBound n ≤ 2*n*(modulusAxes n).vol*n :=
        Nat.mul_le_mul_left _ h1
      have h3 := mul_lt_mul_of_pos_left a (show 0 < 2*n*n by positivity)
      nlinarith
  · exact ⟨hn, by have := Nat.le_self_pow (show 3 ≠ 0 by norm_num) n; omega⟩

lemma express_eta (n : ℕ) : 2*n ∣ largeWorkModulus n :=
  ⟨(modulusAxes n).vol*2^axisLogBound n, by unfold largeWorkModulus; ring⟩

lemma express_volume (n : ℕ) : (modulusAxes n).vol ∣ largeWorkModulus n :=
  ⟨2*n*2^axisLogBound n, by unfold largeWorkModulus; ring⟩

lemma express_halo (n : ℕ) (j : ℕ) (hj : j≤axisLogBound n) : 2^j ∣ largeWorkModulus n :=
  (pow_dvd_pow 2 hj).trans (dvd_mul_left _ _)

lemma express_I (n : ℕ) : 4 ∣ largeWorkModulus n :=
  express_halo n 2 (by unfold axisLogBound; omega)

end
end PowerSaving.Modulus
end OAI

namespace OAI
namespace PowerSaving.RAM
open Ty Modulus AxisTensor Finset
noncomputable section

namespace Bench
universe U V
variable {ι : Type U} {κ : Type V} {m : Bool} {b : Bench m ι} {q : Bench m κ}
  {N k S : ι→ℕ}

def cartTy := p (p w w) (a w)

def cartT (x : PrimeList) : T cartTy := ((x.l,x.vol),Tape.tab x.l x.q)

structure Lade (b : Bench m ι) (S : ι→ℕ) (x : ι→PrimeList) : Prop where
  tape : b.Dry S cartTy fun i => cartT (x i)
  countB : Small b.size fun i => (x i).l
  volume : Small b.size fun i => (x i).vol
  countS : Small S fun i => (x i).l

namespace Lade
variable {x : ι→PrimeList}

lemma dimL (h : b.Lade S x) : b.Grain S fun i => (x i).l := ⟨h.tape.fst.fst, h.countB⟩

lemma volL (h : b.Lade S x) : b.Grain S fun i => (x i).vol := ⟨h.tape.fst.snd, h.volume⟩

lemma dataL (h : b.Lade S x) :
    b.Dry S (a w) fun i => Tape.tab (x i).l (x i).q := h.tape.snd

end Lade

lemma barG {c : Bench m ι} {S' r : ι → ℕ} (hr : c.Grain S' r) (hs : Small S' r) :
    c.Grain S' fun i => if Bar (r i) then 1 else 0 := by
  let cnt : ι → ℕ → ℕ := fun i j => ∑ d ∈ range j,
    (if 1 < d then 1 else 0) * (if r i % d < 1 then 1 else 0)
  have cle : ∀ i j, cnt i j ≤ j := fun i j =>
    (sum_le_sum (g := fun _ => 1) fun d _ => by split_ifs <;> simp).trans (by simp)
  have I := Instant.climbs (t := w) c r cnt
  have hj := strideG (t := w) hr cnt
  have tok : (c.climbs r w cnt).Grain (fun d => S' d.i) fun d => cnt d.i d.j :=
    ⟨Dry.token (t := w) c r S' cnt, (hr.small.reindex During.i).mono fun d => (cle _ _).trans d.hj.le⟩
  have step := tok.add ((Grain.cmp (Grain.wc 1) hj).mul
    (Grain.cmp ((hr.transfer I).residue hj) (Grain.wc 1)))
  have cG : c.Grain S' fun i => cnt i (r i) :=
    ⟨cycleG (t := w) hr hs cnt ((Dry.wc 0).congr fun i => by simp [cnt])
      (step.dry.congr fun d => by simp only [cnt, sum_range_succ]),
     hr.small.mono fun i => cle _ _⟩
  refine ((Grain.cmp (Grain.wc 2) hr).mul (Grain.cmp cG (Grain.wc 1))).congr fun i => ?_
  have key : cnt i (r i) = 0 ↔ ∀ d < r i, ¬ (1 < d ∧ r i % d = 0) := by
    simp only [cnt]; rw [sum_eq_zero_iff]
    constructor
    · intro hz d hd hh
      have := hz d (mem_range.2 hd); simp [hh.1, hh.2] at this
    · intro hz d hd
      have := hz d (mem_range.1 hd)
      by_cases h1 : 1 < d
      · rw [if_pos h1, if_neg (fun h3 => this ⟨h1, by omega⟩), mul_zero]
      · rw [if_neg h1, zero_mul]
  by_cases h2 : 2 < r i
  · rw [if_pos h2, one_mul]
    have e : Bar (r i) ↔ cnt i (r i) < 1 := by
      rw [Nat.lt_one_iff, key]
      constructor
      · rintro ⟨hp, -⟩ d hd ⟨h1, h3⟩
        exact (Nat.prime_def_lt'.1 hp).2 d h1 hd (Nat.dvd_of_mod_eq_zero h3)
      · intro hz
        exact ⟨Nat.prime_def_lt'.2 ⟨by omega, fun d h1 hd hdv =>
          hz d hd ⟨h1, Nat.mod_eq_zero_of_dvd hdv⟩⟩, h2⟩
    by_cases hb : Bar (r i)
    · rw [if_pos hb, if_pos (e.1 hb)]
    · rw [if_neg hb, if_neg (fun h => hb (e.2 h))]
  · rw [if_neg h2, zero_mul, if_neg (fun hb : Bar (r i) => h2 hb.2)]

lemma pushG {c : Bench m ι} {S' : ι → ℕ} {x : ι → PrimeList} {r : ι → ℕ}
    (hx : c.Dry S' cartTy fun i => cartT (x i)) (hl : c.Grain S' fun i => (x i).l)
    (hlS : Small S' fun i => (x i).l) (hv : c.Grain S' fun i => (x i).vol) (hr : c.Grain S' r) :
    c.Dry S' cartTy fun i => cartT ((x i).pushQ (r i)) := by
  have l1 : c.Grain S' fun i => (x i).l + 1 := hl.add (Grain.wc 1)
  have arr : c.Dry S' (a w) fun i =>
      Tape.tab ((x i).l + 1) (fun j => if j = (x i).l then r i else (x i).q j) := by
    refine arrayG l1 (hlS.add (Small.const _ 1)) _ ?_
    have I := Instant.scan c (fun i => (x i).l + 1)
    have hj := chopG l1
    have f := Grain.cmp hj (hl.transfer I)
    have tp := (hx.snd.transfer I).look hj.dry
    refine (Dry.branch f.dry (hr.transfer I).dry tp).congr fun d => ?_
    have hd := d.hj
    by_cases e : d.j = (x d.i).l
    · simp [e]
    · have : d.j < (x d.i).l := by omega
      simp [e, this, cartT, Tape.look_tab]
  exact ((l1.dry.pair (hv.mul hr).dry).pair arr).congr fun i => rfl

lemma greedy_le (N : ℕ) : ∀ j, (greedyPrimes N j).l ≤ j := by
  intro j; induction j with
  | zero => exact le_rfl
  | succ j ih =>
    simp only [greedyPrimes]; split_ifs
    · exact Nat.succ_le_succ ih
    · omega

structure LenCtx (b : Bench m ι) (S n : ι→ℕ) : Prop where
  num : b.Nick n
  tidal : b.Nick S
  stack_eq : ∀ i, axisBudget (n i)=S i
  pos : ∀ i, 0<n i

namespace LenCtx
variable {n : ι→ℕ} {f : ι→κ}

lemma transfer {S n : κ→ℕ} (h : q.LenCtx S n) (g : b.Instant q f) :
    b.LenCtx (fun i => S (f i)) fun i => n (f i) :=
  ⟨h.num.transfer g, h.tidal.transfer g, fun _ => h.stack_eq _, fun _ => h.pos _⟩

lemma stackPow (h : b.LenCtx S n) : Small b.size fun i => 2^S i :=
  (h.num.small.mul (Small.const _ 4)).mono fun i => by
    rw [← h.stack_eq]; have := stack_pow (n i) (h.pos i); omega

lemma limitS (h : b.LenCtx S n) : Small S fun i => primeSearchLimit (n i) + 1 :=
  ((((Small.const S 16).mul ((Small.self S).add (Small.const S 4))).pow 2).add
    (Small.const S 1)).mono fun i => by
    show primeSearchBound (axisBudget (n i)) + 1 ≤ _; rw [h.stack_eq]; exact le_rfl

lemma powOrderS (h : b.LenCtx S n) : Small S fun i => 2^axisLogBound (n i) :=
  ((Small.const S 8).mul ((h.limitS).mono fun i => Nat.le_succ _)).mono fun i => by
    have := orderE_small (n i); omega

lemma orderS (h : b.LenCtx S n) : Small S fun i => axisLogBound (n i) :=
  h.powOrderS.mono fun i => Nat.lt_two_pow_self.le

lemma limitG (h : b.LenCtx S n) : b.Grain S fun i => primeSearchLimit (n i) := by
  have sG := h.tidal.grain S
  refine (((Grain.wc 16).mul (sG.add (Grain.wc 4))).mul
    ((Grain.wc 16).mul (sG.add (Grain.wc 4)))).congr fun i => ?_
  show _ = primeSearchBound (axisBudget (n i)); rw [h.stack_eq]; unfold primeSearchBound; ring

lemma orderG (h : b.LenCtx S n) : b.Grain S fun i => axisLogBound (n i) :=
  ((((Grain.wc 2).mul h.limitG).logtwo
    (((h.limitS).mono fun i => Nat.le_succ _).mul (Small.const S 2) |>.mono fun i =>
      (mul_comm _ _).le)).add (Grain.wc 2)).congr fun i => rfl

lemma powOrderG (h : b.LenCtx S n) : b.Grain S fun i => 2^axisLogBound (n i) :=
  Grain.twoPow h.orderG h.orderS (h.powOrderS.trans h.tidal.small)

lemma modulusAxes_lade (h : b.LenCtx S n) : b.Lade S fun i => modulusAxes (n i) := by
  have NG : b.Grain S fun i => 2 * n i := (Grain.wc 2).mul (h.num.grain S)
  set L : ι → ℕ := fun i => primeSearchLimit (n i) + 1
  have LG : b.Grain S L := h.limitG.add (Grain.wc 1)
  have LS : Small S L := h.limitS
  have topv : ∀ i j, (greedyPrimes (2 * n i) j).vol ≤ 2 * n i := fun i j =>
    (reap_baler (by have := h.pos i; omega) j).top
  let gx : ι → ℕ → T cartTy := fun i j => cartT (greedyPrimes (2 * n i) j)
  have odd : b.Dry S cartTy fun i => cartT (oddPart (n i)) := by
    refine cycleG LG LS gx ((((Dry.wc 0).pair (Dry.wc 1)).pair (arrayG (t := w) (Grain.wc 0) (Small.const S 0)
      (fun (_ : ι) (_ : ℕ) => (0:ℕ)) (Dry.wc 0))).congr fun i => rfl) ?_
    have st := Dry.token b L S gx
    have jG := strideG LG gx
    have jS : Small (fun d : During L => S d.i) During.j := (LS.reindex During.i).mono fun d => d.hj.le
    have vG : (b.climbs L cartTy gx).Grain (fun d => S d.i) fun d => (greedyPrimes (2 * n d.i) d.j).vol :=
      ⟨st.fst.snd, (NG.small.reindex During.i).mono fun d => topv _ _⟩
    refine (Dry.branch ((barG jG jS).mul (Grain.cmp (vG.mul jG) ((NG.transfer (Instant.climbs b L gx)).add
      (Grain.wc 1)))).dry st (pushG st ⟨st.fst.fst, ((LS.trans h.tidal.small).reindex During.i).mono
      fun d => (greedy_le _ _).trans d.hj.le⟩ (jS.mono fun d => greedy_le _ _) vG jG)).congr fun d => ?_
    show _ = cartT (if Bar d.j ∧ (greedyPrimes (2 * n d.i) d.j).vol * d.j ≤ 2 * n d.i then _ else _)
    by_cases hb1 : Bar d.j
    · by_cases hb : (greedyPrimes (2 * n d.i) d.j).vol * d.j ≤ 2 * n d.i
      · rw [if_pos (And.intro hb1 hb), if_neg (by simp [hb1]; omega)]
      · rw [if_neg (not_and_of_not_right _ hb), if_pos (by simp [hb1]; omega)] <;> rfl
    · rw [if_neg (not_and_of_not_left _ hb1), if_pos (by simp [hb1])] <;> rfl
  have spec := fun i => modulusAxes_spec (n i) (h.pos i)
  have ol : ∀ i, (oddPart (n i)).l < S i := fun i => h.stack_eq i ▸ (spec i).count
  have ovG : b.Grain S fun i => (oddPart (n i)).vol := ⟨odd.fst.snd, NG.small.mono fun i => topv i _⟩
  let tx : ι → ℕ → ℕ := fun i k => twoPartFill (2 * n i) (oddPart (n i)).vol k
  have tle : ∀ i k, twoPartFill (2 * n i) (oddPart (n i)).vol k ≤ 2^k := fun i k => by
    induction k with
    | zero => exact le_rfl
    | succ k ih =>
      show (if _ then _ else _) ≤ _; rw [pow_succ]; split_ifs
      · exact Nat.mul_le_mul_right 2 ih
      · omega
  have twoG : b.Grain S fun i => twoPart (n i) := by
    refine ⟨(cycleG (t := w) (h.tidal.grain S) (Small.self S) tx (Dry.wc 1) ?_).congr fun i => by
        show twoPartFill _ _ (S i) = twoPartFill _ _ (axisBudget (n i)); rw [h.stack_eq],
      h.stackPow.mono fun i => h.stack_eq i ▸ tle i _⟩
    have tok : (b.climbs S w tx).Grain (fun d => S d.i) fun d => tx d.i d.j :=
      ⟨Dry.token (t := w) b S S tx, (h.stackPow.reindex During.i).mono fun d =>
        (tle _ _).trans (Nat.pow_le_pow_right (by norm_num) d.hj.le)⟩
    have I := Instant.climbs (t := w) b S tx
    refine (Dry.branch (Grain.cmp ((ovG.transfer I).mul tok) (NG.transfer I)).dry tok.dry
      (tok.mul (Grain.wc 2)).dry).congr fun d => ?_
    show _ = if (oddPart (n d.i)).vol * tx d.i d.j < 2 * n d.i then tx d.i d.j * 2 else tx d.i d.j
    by_cases e : (oddPart (n d.i)).vol * tx d.i d.j < 2 * n d.i <;> simp [e]
  refine ⟨pushG odd ⟨odd.fst.fst, h.tidal.small.mono fun i => (ol i).le⟩ ((Small.self S).mono
    fun i => (ol i).le) ovG twoG, h.tidal.small.mono fun i => h.stack_eq i ▸ (spec i).count,
    (h.num.small.mul (Small.const _ 4)).mono fun i => by have := (spec i).upper; omega,
    (Small.self S).mono fun i => h.stack_eq i ▸ (spec i).count⟩

lemma portG (h : b.LenCtx S n) :
    b.Grain S fun i => if IsLargeLen (n i) then 0 else 1 :=
  (Grain.cmp (h.num.grain S) h.powOrderG).congr fun i => by
    by_cases c : n i < 2^axisLogBound (n i)
    · rw [if_pos c, if_neg (show ¬ IsLargeLen (n i) from fun e => by unfold IsLargeLen at e; omega)]
    · rw [if_neg c, if_pos (show IsLargeLen (n i) by unfold IsLargeLen; omega)]

lemma workModulus_grain (h : b.LenCtx S n) :
    b.Grain S fun i => workModulus (n i) := by
  have nG := h.num.grain S
  have big := ((((Grain.wc 2).mul nG).mul h.modulusAxes_lade.volL).mul h.powOrderG)
  refine ⟨(Dry.branch h.portG.dry big.dry nG.dry).congr fun i => ?_,
    (h.num.small.pow 3 |>.mul (Small.const _ 8)).mono fun i => by
      have := (receipt_bound (n i) (h.pos i)).2; omega⟩
  unfold workModulus largeWorkModulus
  by_cases e : IsLargeLen (n i) <;> simp [e]

end LenCtx

lemma Nick.axisBudget_moves (h : b.Nick N) (g : ∀ i, 0<N i) :
    b.Moves N w (fun i => axisBudget (N i)) ∧
    (b.extend w (fun i => axisBudget (N i))).LenCtx (fun i => axisBudget (N i)) N := by
  have hs : Small b.size fun i => axisBudget (N i) :=
    (h.small.mul (Small.const _ 4)).mono fun i => by have := stack_le (N i) (g i); omega
  have h2 : b.Nick fun i => 2 * N i := (Nick.wc 2).mul h
  have lm : b.Moves N w fun i => Nat.log 2 (2 * N i) :=
    (Nick.logM h2).weaken ⟨2, fun i => show 2 * N i + 1 ≤ 2 * (N i + 1) by omega⟩
  have mv : b.Moves N w fun i => axisBudget (N i) :=
    Can.wadd lm (Moves.wc 1) hs
  refine ⟨mv, ⟨h.transfer (Instant.extend b _), ⟨cherry b _, hs⟩, fun _ => rfl, g⟩⟩

lemma Nick.workModulus_moves (h : b.Nick N) (g : ∀ i,0<N i) :
    ∃ d : ℕ,b.Moves (fun i => N i + (axisBudget (N i)+2)^d) w fun i => workModulus (N i) := by
  obtain ⟨mv, ctx⟩ := h.axisBudget_moves g
  obtain ⟨d, hd⟩ := ctx.workModulus_grain.dry
  exact ⟨d, caseM (mv.weaken (Dom.of_le fun i => Nat.le_add_right _ _))
    (Can.mono hd fun i => Nat.le_add_left _ _)⟩

end Bench
end
end PowerSaving.RAM
end OAI
