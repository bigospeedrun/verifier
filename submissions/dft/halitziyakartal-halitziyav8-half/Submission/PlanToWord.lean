-- From a rational plan to an engine word: the unit structure `PlanUnit` (part 1) and the translation of
-- plans into role words with its correctness (part 2). Notices and credits: texts/credits.lean.
import Submission.WalshTemplate
import Submission.EngineMoves
set_option linter.all false

-- ===== begin part 1: the unit =====
section

/-! # Route B: a rational kernel-pass template as an engine unit

`PlanUnit t` packages what the plan-to-word translation must provide for a
rational candidate template `t` (`QCandidate`, this tree's own definition; the notion of a candidate
with a call rate follows OpenAI's `KernelPass` candidates, openai/math,
`OAI/Computability/NearSquareRoot/KernelPassSearch.lean`):
* a word on the bits `Fin t.arity × Fin 2` of one column letter,
* whose live roles (one per template row) receive the two-point kernel on all `2·arity` bits,
* whose recursive blocks are exactly `t.program.calls` blocks of rank 2 (one per `child` call).
From it `PlanUnit.engine` builds a `SlotEngine`, the input of `SlotEngine.RealisesRule.ripple_engine`. -/

namespace OAI.PowerSaving.RouteB
open Binary GenMove RoleKernel
open OAI.Computability.NearSquareRoot.KernelPass

noncomputable section

/-- Bits of one column letter of an arity-`A` template. -/
abbrev Bit (A : ℕ) := Fin A × Fin 2

/-- The output of the plan-to-word translation for a fixed candidate template. -/
structure PlanUnit (t : QCandidate) where
  ρ : Type
  [fρ : Fintype ρ]
  [dρ : DecidableEq ρ]
  e : Fin t.rows → ρ
  he : Function.Injective e
  tz : Fin (2 * t.arity) → Space (Bit t.arity)
  tind : LinearIndependent F tz
  wd : Script (Bit t.arity) ρ
  hw : RoleKernel.Drives e (fun _ => blockMat tz) wd
  hP : wd.Fits (2 * t.arity)
  hhist : wd.filterMap Move.rk? = List.replicate t.program.calls 2

attribute [instance] PlanUnit.fρ PlanUnit.dρ

end

end OAI.PowerSaving.RouteB
end
-- ===== end part 1 =====

-- ===== begin part 2: plans as role words =====
section

/-!
# Rational plans (OpenAI's binary normalized Walsh plans and others) as role words

`QPlan` (this tree's plan type, shaped after OpenAI's `KernelPass.Plan`, `NearSquareRoot/KernelPass.lean`,
with rational `mix` and `scale` data) is translated into a `Script` of this repository. Each plan node writes its own fresh roles (`Roles p`); inputs are only read.

The word of a plan is checked entrywise against the rational matrix `QPlan.eval`
(`rowSum` below); no separate bank semantics is used.
-/

namespace OAI.PowerSaving.RouteB
open OAI.Computability.NearSquareRoot.KernelPass Matrix Finset
noncomputable section

open Binary GenMove

/-! ## Coordinates -/

def toCol {A : ℕ} (v : Space (Bit A)) : Column A := fun a j => v (a, j)
def toSp {A : ℕ} (c : Column A) : Space (Bit A) := fun p => c p.1 p.2
def toSky {A f : ℕ} (u : Addr A f) : Sky (Bit A) f := fun k => toSp (u k)
def toAddr {A f : ℕ} (y : Sky (Bit A) f) : Addr A f := fun k => toCol (y k)

@[simp] lemma toCol_toSp {A : ℕ} (c : Column A) : toCol (toSp c) = c := rfl
@[simp] lemma toSp_toCol {A : ℕ} (v : Space (Bit A)) : toSp (toCol v) = v := rfl

def skyEquiv (A f : ℕ) : Addr A f ≃ Sky (Bit A) f :=
  ⟨toSky, toAddr, fun _ => rfl, fun _ => rfl⟩

@[simp] lemma skyEquiv_apply {A f : ℕ} (u : Addr A f) : skyEquiv A f u = toSky u := rfl
@[simp] lemma toSky_apply {A f : ℕ} (u : Addr A f) (k : Fin f) : toSky u k = toSp (u k) := rfl
@[simp] lemma toAddr_apply {A f : ℕ} (y : Sky (Bit A) f) (k : Fin f) : toAddr y k = toCol (y k) := rfl

/-! ## Plans read entrywise on role data

`rowSum M x inp b u` is entry `(b, u)` of the rational row matrix `M` applied to the complex
rows `inp` of the role data `x`. Each constructor of `QPlan.eval` (after OpenAI's `Plan.eval`, `KernelPass.lean`)
gets one evaluation lemma below. -/
section RowSum
variable {A : ℕ} {ρ : Type*}

def rowSum {f i o : ℕ} (M : RowMatrix A f i o) (x : Data (Bit A) ρ f) (inp : Fin i → ρ)
    (b : Fin o) (u : Addr A f) : ℂ :=
  ∑ c : Fin i × Addr A f, (M (b, u) c : ℂ) * x (inp c.1) (toSky c.2)

lemma rowSum_mix {f i o : ℕ} (M : Matrix (Fin o) (Fin i) ℚ) (x : Data (Bit A) ρ f)
    (inp : Fin i → ρ) (b : Fin o) (u : Addr A f) :
    rowSum ((QPlan.mix M).eval f) x inp b u = ∑ a, (M b a : ℂ) * x (inp a) (toSky u) := by
  unfold rowSum
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [eval_mix_apply, apply_ite (Rat.cast : ℚ → ℂ), Rat.cast_zero, ite_mul, zero_mul, sum_ite_eq', mem_univ, ↓reduceIte]

lemma rowSum_perm {f : ℕ} (π : Column A ≃+ Column A) (x : Data (Bit A) ρ f) (inp : Fin 1 → ρ)
    (b : Fin 1) (u : Addr A f) :
    rowSum ((QPlan.perm π).eval f) x inp b u = x (inp 0) (toSky (⇑π.symm ∘ u)) := by
  have key : ∀ v : Addr A f, (u = ⇑π ∘ v) ↔ (v = ⇑π.symm ∘ u) := by
    intro v
    constructor <;> rintro rfl <;> funext k <;> simp
  unfold rowSum
  rw [Fintype.sum_prod_type, Fin.sum_univ_one]
  simp only [eval_perm_apply, key, apply_ite (Rat.cast : ℚ → ℂ), Rat.cast_one, Rat.cast_zero, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma rowSum_scale {f q : ℕ} (test : Column A → Fin q → ZMod 2)
    (table : (Fin q → ZMod 2) → ℚ) (x : Data (Bit A) ρ f) (inp : Fin 1 → ρ)
    (b : Fin 1) (u : Addr A f) :
    rowSum ((QPlan.scale q test table).eval f) x inp b u =
      (table (∑ c, test (u c)) : ℂ) * x (inp 0) (toSky u) := by
  unfold rowSum
  rw [Fintype.sum_prod_type, Fin.sum_univ_one]
  simp only [Fin.isValue, eval_scale_apply, apply_ite (Rat.cast : ℚ → ℂ), Rat.cast_zero, ite_mul, zero_mul, sum_ite_eq', mem_univ, ↓reduceIte]

lemma rowSum_child {f : ℕ} (a : Fin A) (x : Data (Bit A) ρ f) (inp : Fin 1 → ρ)
    (b : Fin 1) (u : Addr A f) :
    rowSum ((QPlan.child a).eval f) x inp b u =
      ∑ v : Addr A f, (∏ c, (axisMat a (u c) (v c) : ℂ)) * x (inp 0) (toSky v) := by
  unfold rowSum
  rw [Fintype.sum_prod_type, Fin.sum_univ_one]
  simp only [Fin.isValue, eval_child_apply, colPow, piMat, Rat.cast_prod]

lemma rowSum_mul {f i j o : ℕ} (P : RowMatrix A f j o) (Q : RowMatrix A f i j)
    (x y : Data (Bit A) ρ f) (inp : Fin i → ρ) (mid : Fin j → ρ)
    (h : ∀ a v, y (mid a) (toSky v) = rowSum Q x inp a v) (b : Fin o) (u : Addr A f) :
    rowSum (P * Q) x inp b u = rowSum P y mid b u := by
  unfold rowSum
  simp only [h]
  unfold rowSum
  simp only [Matrix.mul_apply, Rat.cast_sum, Rat.cast_mul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

lemma rowSum_sum_left {f i j o w : ℕ} (P : RowMatrix A f i o) (Q : RowMatrix A f j w)
    (x : Data (Bit A) ρ f) (inp : Fin (i+j) → ρ) (b : Fin o) (u : Addr A f) :
    rowSum (directSum P Q) x inp (Fin.castAdd w b) u =
      rowSum P x (fun a => inp (Fin.castAdd j a)) b u := by
  unfold rowSum
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fin.sum_univ_add]
  simp only [directSum_ll, directSum_lr, Rat.cast_zero, zero_mul, sum_const_zero, add_zero]

lemma rowSum_sum_right {f i j o w : ℕ} (P : RowMatrix A f i o) (Q : RowMatrix A f j w)
    (x : Data (Bit A) ρ f) (inp : Fin (i+j) → ρ) (b : Fin w) (u : Addr A f) :
    rowSum (directSum P Q) x inp (Fin.natAdd o b) u =
      rowSum Q x (fun a => inp (Fin.natAdd i a)) b u := by
  unfold rowSum
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fin.sum_univ_add]
  simp only [directSum_rl, Rat.cast_zero, zero_mul, sum_const_zero, directSum_rr, zero_add]

/-- A correct rational plan (`QCorrect`, after OpenAI's `Correct`) acts row by row as the normalized Walsh product. -/
lemma rowSum_correct {f W : ℕ} {p : QPlan A W W} (ok : QCorrect p) (x : Data (Bit A) ρ f)
    (inp : Fin W → ρ) (b : Fin W) (u : Addr A f) :
    rowSum (p.eval f) x inp b u =
      ∑ v : Addr A f, (∏ c, ∏ j, (pairMat (u c j) (v c j) : ℂ)) * x (inp b) (toSky v) := by
  unfold rowSum
  rw [ok f, Fintype.sum_prod_type]
  simp only [target_apply, colPow, piMat, walshCol, apply_ite (Rat.cast : ℚ → ℂ), Rat.cast_prod, Rat.cast_zero, ite_mul, zero_mul, sum_ite_irrel, sum_const_zero, sum_ite_eq', mem_univ, ↓reduceIte]

end RowSum

/-! ## Role allocation -/
def Roles {A : ℕ} : {i o : ℕ} → QPlan A i o → Type
  | _, _, .mix (o := o) _ => Fin o
  | _, _, .perm _ => Unit
  | _, _, .scale q _ _ => Option (Fin q → ZMod 2)
  | _, _, .child _ => Unit
  | _, _, .seq p q => Roles p ⊕ Roles q
  | _, _, .parallel p q => Roles p ⊕ Roles q

instance rolesFintype {A : ℕ} : {i o : ℕ} → (p : QPlan A i o) → Fintype (Roles p)
  | _, _, .mix (o := o) _ => inferInstanceAs (Fintype (Fin o))
  | _, _, .perm _ => inferInstanceAs (Fintype Unit)
  | _, _, .scale q _ _ => inferInstanceAs (Fintype (Option (Fin q → ZMod 2)))
  | _, _, .child _ => inferInstanceAs (Fintype Unit)
  | _, _, .seq p q => @instFintypeSum _ _ (rolesFintype p) (rolesFintype q)
  | _, _, .parallel p q => @instFintypeSum _ _ (rolesFintype p) (rolesFintype q)

instance rolesDecEq {A : ℕ} : {i o : ℕ} → (p : QPlan A i o) → DecidableEq (Roles p)
  | _, _, .mix (o := o) _ => inferInstanceAs (DecidableEq (Fin o))
  | _, _, .perm _ => inferInstanceAs (DecidableEq Unit)
  | _, _, .scale q _ _ => inferInstanceAs (DecidableEq (Option (Fin q → ZMod 2)))
  | _, _, .child _ => inferInstanceAs (DecidableEq Unit)
  | _, _, .seq p q => @instDecidableEqSum _ _ (rolesDecEq p) (rolesDecEq q)
  | _, _, .parallel p q => @instDecidableEqSum _ _ (rolesDecEq p) (rolesDecEq q)

/-- The role holding each output row of a plan. -/
def outR {A : ℕ} : {i o : ℕ} → (p : QPlan A i o) → Fin o → Roles p
  | _, _, .mix _ => id
  | _, _, .perm _ => fun _ => ()
  | _, _, .scale _ _ _ => fun _ => none
  | _, _, .child _ => fun _ => ()
  | _, _, .seq p _ => fun b => Sum.inl (outR p b)
  | _, _, .parallel p q => Fin.addCases (fun b => Sum.inl (outR p b)) (fun b => Sum.inr (outR q b))

/-! ## Basic role matrices -/
section Mat
variable {ρ : Type*} [Fintype ρ] [DecidableEq ρ]

/-- Overwrite each output role with a combination of input roles; all other roles are kept. -/
def mixG {I O : Type*} [Fintype I] [Fintype O] (inp : I → ρ) (out : O → ρ) (c : O → I → ℚ) :
    Matrix ρ ρ ℚ :=
  fun r j => if ∃ b, out b = r then ∑ b, (if out b = r then ∑ a, (if inp a = j then c b a else 0) else 0)
    else if r = j then 1 else 0

variable {A : ℕ}

lemma localG_apply (f : ℕ) (G : Matrix ρ ρ ℚ) (x : Data (Bit A) ρ f) (r : ρ) (y : Sky (Bit A) f) :
    Move.act (.mix G 0) f x r y = ∑ j, (G r j : ℂ) * x j y := by
  simp only [Move.act, point, actPointG, Matrix.zero_apply, Rat.cast_zero, zero_mul, add_zero]

lemma mixG_out {I O : Type*} [Fintype I] [Fintype O] (inp : I → ρ) (out : O → ρ)
    (hout : Function.Injective out)
    (c : O → I → ℚ) (f : ℕ) (x : Data (Bit A) ρ f) (b : O) (y : Sky (Bit A) f) :
    Move.act (.mix (mixG inp out c) 0) f x (out b) y = ∑ a, (c b a : ℂ) * x (inp a) y := by
  rw [localG_apply]
  have hex : ∃ b', out b' = out b := ⟨b, rfl⟩
  have hrow : ∀ j, mixG inp out c (out b) j = ∑ a, if inp a = j then c b a else 0 := by
    intro j
    rw [mixG, if_pos hex, Finset.sum_eq_single b]
    · simp only [↓reduceIte]
    · intro b' _ hb; rw [if_neg (fun h => hb (hout h))]
    · simp only [mem_univ, not_true_eq_false, ↓reduceIte, IsEmpty.forall_iff]
  simp only [hrow, Rat.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [apply_ite (Rat.cast : ℚ → ℂ), Rat.cast_zero, ite_mul, zero_mul, sum_ite_eq, mem_univ, ↓reduceIte]

lemma mixG_keep {I O : Type*} [Fintype I] [Fintype O] (inp : I → ρ) (out : O → ρ)
    (c : O → I → ℚ) (f : ℕ)
    (x : Data (Bit A) ρ f) (r : ρ) (hr : ∀ b, out b ≠ r) :
    Move.act (.mix (mixG inp out c) 0) f x r = x r := by
  funext y
  rw [localG_apply]
  have hex : ¬ ∃ b, out b = r := fun ⟨b, hb⟩ => hr b hb
  simp only [mixG, if_neg hex]
  rw [Finset.sum_eq_single r]
  · simp only [↓reduceIte, Rat.cast_one, one_mul]
  · intro j _ hj; simp only [Ne.symm hj, ↓reduceIte, Rat.cast_zero, zero_mul]
  · simp only [mem_univ, not_true_eq_false, ↓reduceIte, Rat.cast_one, one_mul, IsEmpty.forall_iff]

lemma roleAct_self (f : ℕ) (l : ρ) (M : CMat (Bit A)) (x : Data (Bit A) ρ f) :
    roleAct f l M x l = letterwise f M (x l) := by simp only [roleAct, ↓reduceIte]

lemma roleAct_other (f : ℕ) (l r : ρ) (M : CMat (Bit A)) (x : Data (Bit A) ρ f) (h : r ≠ l) :
    roleAct f l M x r = x r := by simp only [roleAct, h, ↓reduceIte]

end Mat

/-! ## A column permutation as an additive permutation of the engine's space -/
def colPerm {A : ℕ} (π : Column A ≃+ Column A) : Space (Bit A) ≃+ Space (Bit A) where
  toFun v := toSp (π.symm (toCol v))
  invFun v := toSp (π (toCol v))
  left_inv v := by simp only [toCol_toSp, AddEquiv.apply_symm_apply, toSp_toCol]
  right_inv v := by simp only [toCol_toSp, AddEquiv.symm_apply_apply, toSp_toCol]
  map_add' x y := by
    show toSp (π.symm (toCol (x + y))) = toSp (π.symm (toCol x)) + toSp (π.symm (toCol y))
    rw [show toCol (x + y) = toCol x + toCol y from rfl, AddEquiv.map_add]; rfl

/-! ## Column identities (C kernel versus normalized Walsh factors) -/
section Ident
open Complex
noncomputable def pairEntry (y0 y1 x0 x1 : F) : ℂ :=
  (if y0 = x0 ∧ y1 = x1 then ca*ca else 0) + (if y0 = x0 ∧ y1 + 1 = x1 then ca*cb else 0) +
  (if y0 + 1 = x0 ∧ y1 = x1 then cb*ca else 0) + (if y0 + 1 = x0 ∧ y1 + 1 = x1 then cb*cb else 0)
lemma chi_dot_half (a b : F) :
    (((if a+b = 0 then 1/2 else -(1/2) : ℚ)) : ℂ) = 1/2 * (sign a * sign b) := by
  rw [← sign_add, sign]
  split_ifs <;> push_cast <;> ring

lemma littleC_split (y x : F) :
    (if y = x then ca else 0) + (if y + 1 = x then cb else 0) = littleC y x := by
  rcases bit_cases y with rfl|rfl <;> rcases bit_cases x with rfl|rfl <;>
    simp (config := {decide := true}) only [littleC, if_true, if_false, add_zero, zero_add]

lemma pairEntry_eq (y0 y1 x0 x1 : F) : pairEntry y0 y1 x0 x1 = littleC y0 x0 * littleC y1 x1 := by
  rw [← littleC_split, ← littleC_split, pairEntry, ← ite_zero_mul_ite_zero, ← ite_zero_mul_ite_zero,
    ← ite_zero_mul_ite_zero, ← ite_zero_mul_ite_zero, add_mul, mul_add, mul_add, ← add_assoc]

lemma littleC_phase (y x : F) : phaseI y * littleC y x * phaseI x = (1+I)/2 * sign (y*x) := by
  rcases bit_cases y with rfl|rfl <;> rcases bit_cases x with rfl|rfl <;>
    simp (config := {decide := true}) only [littleC, phaseI, sign, ca, cb, if_true, if_false,
      mul_zero, zero_mul, mul_one, one_mul]
  · linear_combination (-1/2 : ℂ) * I_mul_I
  · linear_combination (-1/2 : ℂ) * I_mul_I
  · linear_combination ((1+I)/2 : ℂ) * I_mul_I

lemma pairMat_entry (y0 y1 x0 x1 : F) :
    (((if y0*x0+y1*x1 = 0 then 1/2 else -(1/2) : ℚ)) : ℂ) =
      -I * (phaseI y0 * phaseI y1) * pairEntry y0 y1 x0 x1 * (phaseI x0 * phaseI x1) := by
  rw [chi_dot_half, pairEntry_eq]
  have h0 := littleC_phase y0 x0
  have h1 := littleC_phase y1 x1
  linear_combination (I * (phaseI y1 * littleC y1 x1 * phaseI x1)) * h0 +
    (I * ((1+I)/2) * sign (y0*x0)) * h1 + (sign (y0*x0) * sign (y1*x1) * (2+I)/4) * I_mul_I

open Matrix in
lemma dir_apply {α : Type*} [Fintype α] [DecidableEq α] (z Y W : Space α) :
    dir z Y W = (if Y = W then ca else 0) + (if Y + z = W then cb else 0) := by
  simp only [dir, Matrix.add_apply, Matrix.smul_apply, one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, shift]

open Matrix in
lemma dir_mul_dir {α : Type*} [Fintype α] [DecidableEq α] (z w Y X : Space α) :
    (dir z * dir w) Y X = (if Y = X then ca*ca else 0) + (if Y + w = X then ca*cb else 0) +
      (if Y + z = X then cb*ca else 0) + (if Y + (z + w) = X then cb*cb else 0) := by
  rw [mul_apply]
  simp only [dir_apply, add_mul, ite_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  simp only [mul_add, mul_ite, mul_zero, ← add_assoc]

section Pair
variable {A : ℕ}
def pairDirs (a : Fin A) : Fin 2 → Space (Bit A) := ![eu (a,0), eu (a,1)]

lemma add_eq_iff (Y X d : Space (Bit A)) (a : Fin A) (hd : ∀ b ≠ a, ∀ j, d (b,j) = 0) :
    Y + d = X ↔ ((∀ b ≠ a, ∀ j, X (b,j) = Y (b,j)) ∧ Y (a,0) + d (a,0) = X (a,0) ∧
      Y (a,1) + d (a,1) = X (a,1)) := by
  constructor
  · rintro rfl
    exact ⟨fun b hb j => by simp only [Pi.add_apply, hd b hb j, add_zero], rfl, rfl⟩
  · rintro ⟨h, h0, h1⟩
    funext ⟨b, j⟩
    by_cases hb : b = a
    · subst hb
      fin_cases j
      · exact h0
      · exact h1
    · simp only [Pi.add_apply, hd b hb j, add_zero, h b hb j]

lemma eu_off (a b : Fin A) (k j : Fin 2) (hb : b ≠ a) : eu (a,k) (b,j) = 0 := by
  simp only [eu, Prod.ext_iff, Ne.symm hb, false_and, ↓reduceIte]

lemma blockPair_apply (a : Fin A) (Y X : Space (Bit A)) :
    blockMat (pairDirs a) Y X = if (∀ b ≠ a, ∀ j, X (b,j) = Y (b,j)) then
      pairEntry (Y (a,0)) (Y (a,1)) (X (a,0)) (X (a,1)) else 0 := by
  have hb : blockMat (pairDirs a) = dir (eu (a,0)) * dir (eu (a,1)) := by
    rw [blockMat_eq_prod_ofFn, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero, List.prod_cons,
      List.prod_cons, List.prod_nil, Matrix.mul_one]; rfl
  rw [hb, dir_mul_dir]
  have e0 : ∀ b ≠ a, ∀ j, (eu (a,0) : Space (Bit A)) (b,j) = 0 := fun b h j => eu_off a b 0 j h
  have e1 : ∀ b ≠ a, ∀ j, (eu (a,1) : Space (Bit A)) (b,j) = 0 := fun b h j => eu_off a b 1 j h
  have e01 : ∀ b ≠ a, ∀ j, (eu (a,0) + eu (a,1) : Space (Bit A)) (b,j) = 0 := fun b h j => by
    simp only [Fin.isValue, Pi.add_apply, eu_off a b 0 j h, eu_off a b 1 j h, add_zero]
  have z0 : ∀ b ≠ a, ∀ j, (0 : Space (Bit A)) (b,j) = 0 := fun _ _ _ => rfl
  have i0 := add_eq_iff Y X 0 a z0
  have i1 := add_eq_iff Y X _ a e1
  have i2 := add_eq_iff Y X _ a e0
  have i3 := add_eq_iff Y X _ a e01
  rw [add_zero] at i0
  have v00 : (eu (a,0) : Space (Bit A)) (a,0) = 1 := by simp only [eu, Fin.isValue, ↓reduceIte]
  have v01 : (eu (a,0) : Space (Bit A)) (a,1) = 0 := by simp only [eu, Fin.isValue, Prod.ext_iff, zero_ne_one, and_false, ↓reduceIte]
  have v10 : (eu (a,1) : Space (Bit A)) (a,0) = 0 := by simp only [eu, Fin.isValue, Prod.ext_iff, one_ne_zero, and_false, ↓reduceIte]
  have v11 : (eu (a,1) : Space (Bit A)) (a,1) = 1 := by simp only [eu, Fin.isValue, ↓reduceIte]
  simp only [Pi.add_apply, Pi.zero_apply, v00, v01, v10, v11, add_zero] at i0 i1 i2 i3
  by_cases hag : ∀ b ≠ a, ∀ j, X (b,j) = Y (b,j)
  · have ht := iff_true_intro hag
    simp only [ht, true_and] at i0 i1 i2 i3
    simp only [i0, i1, i2, i3, ht, ite_true, pairEntry, zero_add]
  · have hf := iff_false_intro hag
    simp only [hf, false_and] at i0 i1 i2 i3
    simp only [i0, i1, i2, i3, hf, ite_false, add_zero]
end Pair

section Col
variable {A : ℕ}

lemma pairMat_cast (y x : Fin 2 → ZMod 2) :
    ((pairMat y x : ℚ) : ℂ) = (((if y 0 * x 0 + y 1 * x 1 = 0 then 1/2 else -(1/2) : ℚ)) : ℂ) := by
  rw [pairMat_apply]; unfold chi OAI.Computability.NearSquareRoot.KernelPass.dot; split_ifs <;> norm_num

lemma child_col (a : Fin A) (Y X : Space (Bit A)) :
    ((axisMat a (toCol Y) (toCol X) : ℚ) : ℂ) =
      (-I * (phaseI (Y (a,0)) * phaseI (Y (a,1)))) * blockMat (pairDirs a) Y X * (phaseI (X (a,0)) * phaseI (X (a,1))) := by
  rw [blockPair_apply]
  have hc : (∀ b ≠ a, toCol X b = toCol Y b) ↔ (∀ b ≠ a, ∀ j, X (b,j) = Y (b,j)) := by
    simp only [toCol, funext_iff]
  rw [axisMat, piMat_update]
  by_cases hag : ∀ b ≠ a, ∀ j, X (b,j) = Y (b,j)
  · rw [if_pos (hc.2 hag), if_pos hag, pairMat_cast, pairMat_entry]; simp only [toCol, Fin.isValue, neg_mul] <;> ring
  · rw [if_neg (fun h => hag (hc.1 h)), if_neg hag]; simp only [Rat.cast_zero, Fin.isValue, neg_mul, mul_zero, zero_mul]

lemma littleC_phase_cube (y x : F) : littleC y x = (1+I)/2 * sign (y*x) * (phaseI y ^ 3 * phaseI x ^ 3) := by
  rcases bit_cases y with rfl|rfl <;> rcases bit_cases x with rfl|rfl <;>
    simp (config := {decide := true}) only [littleC, phaseI, sign, ca, cb, if_true, if_false,
      mul_zero, zero_mul, mul_one, one_mul, one_pow]
  · linear_combination (-(I^2+I-1)/2 : ℂ) * I_mul_I
  · linear_combination (-(I^2+I-1)/2 : ℂ) * I_mul_I
  · linear_combination ((1+I)*(I^4-I^2+1)/2 : ℂ) * I_mul_I

lemma littleC_pair (y0 y1 x0 x1 : F) :
    littleC y0 x0 * littleC y1 x1 = I * (((if y0*x0+y1*x1 = 0 then 1/2 else -(1/2) : ℚ)) : ℂ) *
      (phaseI y0 ^ 3 * phaseI y1 ^ 3) * (phaseI x0 ^ 3 * phaseI x1 ^ 3) := by
  rw [chi_dot_half]
  have h0 := littleC_phase_cube y0 x0
  have h1 := littleC_phase_cube y1 x1
  linear_combination littleC y1 x1 * h0 + ((1+I)/2 * sign (y0*x0) * (phaseI y0 ^ 3 * phaseI x0 ^ 3)) * h1 +
    (sign (y0*x0) * sign (y1*x1) * (phaseI y0 ^ 3 * phaseI x0 ^ 3) * (phaseI y1 ^ 3 * phaseI x1 ^ 3) / 4) * I_mul_I

lemma rippleMat_col (Y X : Space (Bit A)) :
    rippleMat (Bit A) Y X = I ^ A * (∏ a, ((pairMat (toCol Y a) (toCol X a) : ℚ) : ℂ)) *
      (∏ β, phaseI (Y β) ^ 3) * (∏ β, phaseI (X β) ^ 3) := by
  simp only [rippleMat, OAI.PowerSaving.digitProd_apply, Fintype.prod_prod_type, Fin.prod_univ_two]
  simp only [littleC_pair, pairMat_cast, toCol, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  rfl

end Col
end Ident

/-! ## Words -/
section Words
open Complex
variable {A : ℕ} {ρ : Type*} [Fintype ρ] [DecidableEq ρ]

lemma matAct_apply' (f : ℕ) (M : CMat (Bit A)) (y : Sky (Bit A) f → ℂ) (b : Sky (Bit A) f) :
    letterwise f M y b = ∑ b', (∏ k, M (b k) (b' k)) * y b' :=
  letterwise_sum f M y b

def cpMove (src dst : ρ) : Move (Bit A) ρ :=
  .mix (mixG (fun _ : Unit => src) (fun _ : Unit => dst) (fun _ _ => 1)) 0

lemma cpMove_dst (src dst : ρ) (f : ℕ) (x : Data (Bit A) ρ f) :
    (cpMove src dst : Move (Bit A) ρ).act f x dst = x src := by
  funext y
  have := mixG_out (A := A) (fun _ : Unit => src) (fun _ : Unit => dst)
    (fun _ _ _ => Subsingleton.elim _ _) (fun _ _ => 1) f x () y
  simpa only [cpMove, univ_unique, PUnit.default_eq_unit, Rat.cast_one, one_mul, sum_const, card_singleton, one_smul] using this

lemma cpMove_keep (src dst : ρ) (f : ℕ) (x : Data (Bit A) ρ f) (r : ρ) (h : r ≠ dst) :
    (cpMove src dst : Move (Bit A) ρ).act f x r = x r :=
  mixG_keep _ _ _ f x r (fun _ => Ne.symm h)

lemma pairDirs_indep (a : Fin A) : LinearIndependent F (pairDirs a) := by
  unfold pairDirs
  rw [LinearIndependent.pair_iff]
  intro s t h
  have h0 := congrFun h (a,0)
  have h1 := congrFun h (a,1)
  simp only [Fin.isValue, Pi.add_apply, Pi.smul_apply, eu, ↓reduceIte, smul_eq_mul, mul_one,
    Prod.ext_iff, one_ne_zero, and_false, mul_zero, add_zero, Pi.zero_apply, zero_ne_one,
    zero_add] at h0 h1
  exact ⟨h0, h1⟩

def childMat (a : Fin A) : CMat (Bit A) :=
  ph 0 1 * (ph 0 1 * (ph 0 1 * (ph (eu (a,1)) 0 * (ph (eu (a,0)) 0 *
    (blockMat (pairDirs a) * (ph (eu (a,0)) 0 * ph (eu (a,1)) 0))))))
where
  /-- The diagonal matrix of an affine phase move. -/
  ph (z : Space (Bit A)) (c : F) : CMat (Bit A) := diagonal fun y => phaseI (dot z y + c)

lemma childMat_apply (a : Fin A) (Y X : Space (Bit A)) :
    childMat a Y X = ((axisMat a (toCol Y) (toCol X) : ℚ) : ℂ) := by
  rw [child_col]
  simp only [childMat, childMat.ph, diagonal_mul_diagonal, diagonal_mul, mul_diagonal, dot_eu_left,
    dot_zero_left, zero_add, add_zero]
  have hI : phaseI 1 = I := if_neg one_ne
  rw [hI]
  have h3 : I * (I * I) = -I := by rw [I_mul_I]; ring
  linear_combination (phaseI (Y (a, 1)) * (phaseI (Y (a, 0)) * (blockMat (pairDirs a) Y X *
    (phaseI (X (a, 0)) * phaseI (X (a, 1)))))) * h3

def childWord (l : ρ) (a : Fin A) : Script (Bit A) ρ :=
  [.phase l (eu (a,1)) 0, .phase l (eu (a,0)) 0, .kern l 2 (pairDirs a) (pairDirs_indep a),
   .phase l (eu (a,0)) 0, .phase l (eu (a,1)) 0, .phase l 0 1, .phase l 0 1, .phase l 0 1]

lemma childWord_walk (l : ρ) (a : Fin A) (f : ℕ) (x : Data (Bit A) ρ f) :
    Script.exec (childWord l a) f x = roleAct f l (childMat a) x := by
  simp only [childWord, exec_cons, exec_nil, Move.act, roleAct_mul, childMat, childMat.ph,
    Matrix.mul_assoc]

/-! ### `scale` -/
abbrev QV (q : ℕ) := Fin q → ZMod 2

def gtest {q : ℕ} (test : Column A → Fin q → ZMod 2) (u : QV q) (v : Space (Bit A)) : F :=
  ∑ j, u j * test (toCol v) j


lemma chi_cast (i : F) : ((chi i : ℚ) : ℂ) = sign i := by
  unfold chi sign; split <;> simp

def hat {q : ℕ} (table : QV q → ℚ) (u : QV q) : ℚ :=
  ((2:ℚ)^q)⁻¹ * ∑ s, table s * chi (∑ j, u j * s j)

def bphOne (l : ρ) (g : Space (Bit A) → F) : Script (Bit A) ρ := [.sgn l g]

def scaleWord {q : ℕ} (test : Column A → Fin q → ZMod 2) (table : QV q → ℚ)
    (inp0 : ρ) (emb : Option (QV q) → ρ) : Script (Bit A) ρ :=
  [cpMove inp0 (emb none),
    .mix (mixG (fun _ : Unit => emb none) (fun u : QV q => emb (some u)) (fun _ _ => 1)) 0] ++
  (((Finset.univ : Finset (QV q)).toList.flatMap fun u => bphOne (emb (some u)) (gtest test u)) ++
  [.mix (mixG (fun u : QV q => emb (some u)) (fun _ : Unit => emb none)
    (fun _ u => hat table u)) 0])

/-- Role-local words, one per distinct role, each acting on its own role. -/
lemma multi_walk {σ ρ : Type*} [Fintype ρ] [DecidableEq ρ] (e : σ → ρ) (he : Function.Injective e)
    (w : σ → Script (Bit A) ρ) (M : σ → CMat (Bit A))
    (hw : ∀ l f (x : Data (Bit A) ρ f), Script.exec (w l) f x = roleAct f (e l) (M l) x) (f : ℕ) :
    ∀ (L : List σ), L.Nodup → ∀ (x : Data (Bit A) ρ f),
      (∀ r, (∀ l ∈ L, e l ≠ r) → Script.exec (L.flatMap w) f x r = x r) ∧
      (∀ l ∈ L, Script.exec (L.flatMap w) f x (e l) = letterwise f (M l) (x (e l)))
  | [], _, x => ⟨fun _ _ => rfl, fun _ h => by simp only [List.not_mem_nil] at h⟩
  | v :: L, hn, x => by
    have hv : v ∉ L := (List.nodup_cons.1 hn).1
    obtain ⟨ih1, ih2⟩ := multi_walk e he w M hw f L (List.nodup_cons.1 hn).2 (roleAct f (e v) (M v) x)
    have hw' : Script.exec ((v :: L).flatMap w) f x = Script.exec (L.flatMap w) f (roleAct f (e v) (M v) x) := by
      rw [List.flatMap_cons, exec_append, hw]
    refine ⟨fun r hr => ?_, fun u hu => ?_⟩
    · rw [hw', ih1 r (fun u hu => hr u (List.mem_cons_of_mem _ hu))]
      have hne : r ≠ e v := fun h => hr v (by simp only [List.mem_cons, true_or]) h.symm
      simp only [roleAct, hne, ↓reduceIte]
    · rw [hw']
      rcases List.mem_cons.1 hu with rfl | hu
      · rw [ih1 (e u) (fun w' hw'' h => hv (he h ▸ hw''))]
        simp only [roleAct, ↓reduceIte]
      · rw [ih2 u hu]
        have hne : e u ≠ e v := fun h => hv (he h ▸ hu)
        simp only [roleAct, hne, ↓reduceIte]

lemma orth_sign {q : ℕ} (c : QV q) :
    ∑ u : QV q, sign (∑ j, u j * c j) = if c = 0 then (2:ℂ)^q else 0 := by
  simp only [sign_sum]
  rw [show (∑ u : QV q, ∏ j ∈ Finset.univ, sign (u j * c j)) =
      ∏ j : Fin q, ∑ v : ZMod 2, sign (v * c j) from by
    rw [Finset.prod_univ_sum]; simp]
  have h2 (z : ZMod 2) : ∑ v : ZMod 2, sign (v * z) = if z = 0 then 2 else 0 := by
    rw [sumF]
    rcases bit_cases z with rfl | rfl <;>
      simp (config := {decide := true}) only [sign, mul_zero, zero_mul, one_mul, if_true,
        if_false, one_add_one_eq_two, add_neg_cancel]
  simp only [h2]
  by_cases hc : c = 0
  · simp only [hc, Pi.zero_apply, ↓reduceIte, prod_const, card_univ, Fintype.card_fin]
  · rw [if_neg hc]
    obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
      by_contra h; push Not at h; exact hc (funext h)
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

lemma fourier {q : ℕ} (t : QV q → ℂ) (S : QV q) :
    ∑ u : QV q, (((2:ℂ)^q)⁻¹ * ∑ s, t s * sign (∑ j, u j * s j)) * sign (∑ j, u j * S j) = t S := by
  have hsplit (u s : QV q) : sign (∑ j, u j * s j) * sign (∑ j, u j * S j) =
      sign (∑ j, u j * (s + S) j) := by
    rw [← sign_add, ← Finset.sum_add_distrib]; congr 1
    refine Finset.sum_congr rfl fun j _ => ?_; simp only [Pi.add_apply, mul_add]
  simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc, hsplit]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, orth_sign]
  rw [Finset.sum_eq_single S]
  · have h0 : S + S = 0 := by funext j; simp only [Pi.add_apply, ← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul, Pi.zero_apply]
    rw [if_pos h0]; field_simp
  · intro s _ hs
    have : s + S ≠ 0 := fun h => hs (by
      funext j; have := congrFun h j; simp only [Pi.add_apply, Pi.zero_apply] at this
      rw [eq_neg_of_add_eq_zero_left this, ZMod.neg_eq_self_mod_two])
    simp only [this, ↓reduceIte, mul_zero]
  · simp only [mem_univ, not_true_eq_false, binary_cancel, ↓reduceIte, mul_eq_zero, pow_eq_zero_iff', OfNat.ofNat_ne_zero, ne_eq, false_and, or_false, IsEmpty.forall_iff]

end Words

/-! ## Translation and its semantics -/
section Translate
variable {A : ℕ} {ρ : Type*} [Fintype ρ] [DecidableEq ρ]

/-- Plan to role word: `inp` are the input rows, `emb` places the node's own roles. -/
def toWord : {i o : ℕ} → (p : QPlan A i o) → (Fin i → ρ) → (Roles p → ρ) → Script (Bit A) ρ
  | _, _, .mix M, inp, emb =>
      [.mix (mixG inp (fun b : Fin _ => emb b) (fun b a => M b a)) 0]
  | _, _, .perm π, inp, emb => [cpMove (inp 0) (emb ()), .perm (emb ()) (colPerm π)]
  | _, _, .scale _ test table, inp, emb => scaleWord test table (inp 0) emb
  | _, _, .child a, inp, emb => cpMove (inp 0) (emb ()) :: childWord (emb ()) a
  | _, _, .seq p q, inp, emb =>
      toWord q inp (fun s => emb (Sum.inr s)) ++
        toWord p (fun a => emb (Sum.inr (outR q a))) (fun s => emb (Sum.inl s))
  | _, _, .parallel p q, inp, emb =>
      toWord p (fun a => inp (Fin.castAdd _ a)) (fun s => emb (Sum.inl s)) ++
        toWord q (fun a => inp (Fin.natAdd _ a)) (fun s => emb (Sum.inr s))

/-- Every node leaves foreign roles alone and puts its output rows in its output roles. -/
def Realises {i o : ℕ} (p : QPlan A i o) (w : Script (Bit A) ρ) (inp : Fin i → ρ)
    (emb : Roles p → ρ) : Prop :=
  ∀ (f : ℕ) (x : Data (Bit A) ρ f),
    (∀ r, (∀ s, emb s ≠ r) → Script.exec w f x r = x r) ∧
    (∀ b u, Script.exec w f x (emb (outR p b)) (toSky u) = rowSum (p.eval f) x inp b u)

end Translate

section Semantics
open Complex
variable {A : ℕ} {ρ : Type*} [Fintype ρ] [DecidableEq ρ]

lemma mix_realises {i o : ℕ} (coeff : Matrix (Fin o) (Fin i) ℚ) (inp : Fin i → ρ)
    (emb : Roles (QPlan.mix (A := A) coeff) → ρ) (he : Function.Injective emb) :
    Realises (QPlan.mix coeff) (toWord (QPlan.mix coeff) inp emb) inp emb := by
  intro f x
  refine ⟨fun r hr => ?_, fun b u => ?_⟩
  · exact mixG_keep (A := A) inp (fun b : Fin o => emb b) _ f x r hr
  · rw [rowSum_mix]
    exact mixG_out (A := A) inp (fun b : Fin o => emb b) he _ f x b (toSky u)

lemma perm_realises (π : Column A ≃+ Column A) (inp : Fin 1 → ρ)
    (emb : Roles (QPlan.perm (A := A) π) → ρ) :
    Realises (QPlan.perm π) (toWord (QPlan.perm π) inp emb) inp emb := by
  intro f x
  have hw : Script.exec (toWord (QPlan.perm π) inp emb) f x =
      roleAct f (emb ()) (shuffleMat (colPerm π)) ((cpMove (inp 0) (emb ())).act f x) := rfl
  refine ⟨fun r hr => ?_, fun b u => ?_⟩
  · have hne : r ≠ emb () := fun h => hr () h.symm
    rw [hw, roleAct_other _ _ _ _ _ hne, cpMove_keep _ _ _ _ _ hne]
  · rw [hw, show outR (QPlan.perm (A := A) π) b = () from rfl, roleAct_self, matAct_perm,
      cpMove_dst, rowSum_perm]
    rfl

lemma child_realises (a : Fin A) (inp : Fin 1 → ρ) (emb : Roles (QPlan.child (A := A) a) → ρ) :
    Realises (QPlan.child a) (toWord (QPlan.child a) inp emb) inp emb := by
  intro f x
  have hw : Script.exec (toWord (QPlan.child a) inp emb) f x =
      roleAct f (emb ()) (childMat a) ((cpMove (inp 0) (emb ())).act f x) := by
    show Script.exec (cpMove (inp 0) (emb ()) :: childWord (emb ()) a) f x = _
    rw [exec_cons, childWord_walk]
  refine ⟨fun r hr => ?_, fun b u => ?_⟩
  · have hne : r ≠ emb () := fun h => hr () h.symm
    rw [hw, roleAct_other _ _ _ _ _ hne, cpMove_keep _ _ _ _ _ hne]
  · have hb : b = 0 := Subsingleton.elim _ _
    subst hb
    rw [hw, show outR (QPlan.child (A := A) a) 0 = () from rfl, roleAct_self, cpMove_dst,
      matAct_apply', rowSum_child, ← (skyEquiv A f).sum_comp]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [childMat_apply]
    rfl

lemma gtest_sum {q f : ℕ} (test : Column A → Fin q → ZMod 2) (u : QV q) (y : Addr A f) :
    ∑ k, gtest test u (toSky y k) = ∑ j, u j * (∑ c, test (y c)) j := by
  simp only [gtest, toSky, toCol_toSp, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

lemma scale_realises {q : ℕ} (test : Column A → Fin q → ZMod 2) (table : QV q → ℚ)
    (inp : Fin 1 → ρ) (emb : Roles (QPlan.scale (A := A) q test table) → ρ)
    (he : Function.Injective emb) :
    Realises (QPlan.scale q test table) (toWord (QPlan.scale q test table) inp emb) inp emb := by
  intro f x
  let emb' : Option (QV q) → ρ := emb
  let out := emb' none
  let scr : QV q → ρ := fun u => emb' (some u)
  have hscr : Function.Injective scr := fun u v h => Option.some_injective _ (he h)
  have hout : ∀ u, scr u ≠ out := fun u h => by have := he h; simp at this
  let cp : Move (Bit A) ρ := cpMove (inp 0) out
  let spread : Move (Bit A) ρ :=
    .mix (mixG (fun _ : Unit => out) (fun u : QV q => scr u) (fun _ _ => 1)) 0
  let comb : Move (Bit A) ρ :=
    .mix (mixG (fun u : QV q => scr u) (fun _ : Unit => out) (fun _ u => hat table u)) 0
  let L := (Finset.univ : Finset (QV q)).toList
  let gu := gtest (A := A) test
  let x2 := spread.act f (cp.act f x)
  let x3 := Script.exec (L.flatMap fun u => bphOne (scr u) (gu u)) f x2
  have hw : Script.exec (toWord (QPlan.scale q test table) inp emb) f x = comb.act f x3 := by
    show Script.exec (scaleWord test table (inp 0) emb) f x = _
    simp only [scaleWord, exec_append, exec_cons, exec_nil]; rfl
  obtain ⟨k3, v3⟩ := multi_walk scr hscr (fun u => bphOne (scr u) (gu u)) (fun u => diagonal fun y => sign (gu u y))
    (fun u f x => by simp only [bphOne, exec_cons, exec_nil, Move.act]) f L (Finset.nodup_toList _) x2
  have k2 : ∀ r, (∀ u, scr u ≠ r) → x2 r = cp.act f x r := fun r hr =>
    mixG_keep _ _ _ f _ r hr
  have v2 : ∀ u, x2 (scr u) = x (inp 0) := by
    intro u; funext y
    have := mixG_out (A := A) (fun _ : Unit => out) (fun u : QV q => scr u) hscr (fun _ _ => 1) f
      (cp.act f x) u y
    simp only [Finset.univ_unique, Finset.sum_singleton, Rat.cast_one, one_mul] at this
    rw [show x2 (scr u) y = _ from this, cpMove_dst]
  refine ⟨fun r hr => ?_, fun b u => ?_⟩
  · have hro : r ≠ out := fun h => hr none h.symm
    have hrs : ∀ u, scr u ≠ r := fun u h => hr (some u) h
    rw [hw, mixG_keep _ _ _ f _ r (fun _ => Ne.symm hro)]
    exact (k3 r (fun u _ => hrs u)).trans ((k2 r hrs).trans (cpMove_keep _ _ _ _ _ hro))
  · have hb : outR (QPlan.scale (A := A) q test table) b = none := rfl
    rw [hb, hw, rowSum_scale]
    have := mixG_out (A := A) (fun u : QV q => scr u) (fun _ : Unit => out)
      (fun _ _ _ => Subsingleton.elim _ _) (fun _ u => hat table u) f x3 () (toSky u)
    rw [show comb.act f x3 out (toSky u) = _ from this]
    have hv3 : ∀ v, x3 (scr v) = letterwise f (diagonal fun y => sign (gu v y)) (x (inp 0)) := fun v => by
      rw [← v2 v]; exact v3 v (Finset.mem_toList.2 (Finset.mem_univ _))
    have hsq (v : QV q) : (hat table v : ℂ) * x3 (scr v) (toSky u) =
        (((2:ℂ)^q)⁻¹ * ∑ s, (table s : ℂ) * sign (∑ j, v j * s j)) *
          sign (∑ j, v j * (∑ c, test (u c)) j) * x (inp 0) (toSky u) := by
      rw [hv3 v, matAct_bphase, ← sign_sum, gtest_sum]
      simp only [hat, Rat.cast_mul, Rat.cast_inv, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_sum,
        chi_cast]
      ring
    rw [Finset.sum_congr rfl (fun v _ => hsq v), ← Finset.sum_mul,
      fourier (fun s => (table s : ℂ))]

lemma seq_realises {i j o : ℕ} (p : QPlan A j o) (q : QPlan A i j) (inp : Fin i → ρ)
    (emb : Roles (QPlan.seq p q) → ρ)
    (hq : Realises q (toWord q inp (fun s => emb (Sum.inr s))) inp (fun s => emb (Sum.inr s)))
    (hp : Realises p (toWord p (fun a => emb (Sum.inr (outR q a))) (fun s => emb (Sum.inl s)))
      (fun a => emb (Sum.inr (outR q a))) (fun s => emb (Sum.inl s))) :
    Realises (QPlan.seq p q) (toWord (QPlan.seq p q) inp emb) inp emb := by
  intro f x
  have hw : Script.exec (toWord (QPlan.seq p q) inp emb) f x =
      Script.exec (toWord p (fun a => emb (Sum.inr (outR q a))) (fun s => emb (Sum.inl s))) f
        (Script.exec (toWord q inp (fun s => emb (Sum.inr s))) f x) :=
    exec_append f _ _ x
  obtain ⟨kq, vq⟩ := hq f x
  obtain ⟨kp, vp⟩ := hp f (Script.exec (toWord q inp (fun s => emb (Sum.inr s))) f x)
  refine ⟨fun r hr => ?_, fun b u => ?_⟩
  · rw [hw, kp r (fun s => hr _), kq r (fun s => hr _)]
  · rw [hw, show outR (QPlan.seq p q) b = Sum.inl (outR p b) from rfl, vp]
    exact (rowSum_mul (p.eval f) (q.eval f) x _ inp _ vq b u).symm

lemma parallel_realises {i j o u : ℕ} (p : QPlan A i o) (q : QPlan A j u) (inp : Fin (i+j) → ρ)
    (emb : Roles (QPlan.parallel p q) → ρ) (he : Function.Injective emb)
    (hd : ∀ a s, inp a ≠ emb s)
    (hp : Realises p (toWord p (fun a => inp (Fin.castAdd _ a)) (fun s => emb (Sum.inl s)))
      (fun a => inp (Fin.castAdd _ a)) (fun s => emb (Sum.inl s)))
    (hq : Realises q (toWord q (fun a => inp (Fin.natAdd _ a)) (fun s => emb (Sum.inr s)))
      (fun a => inp (Fin.natAdd _ a)) (fun s => emb (Sum.inr s))) :
    Realises (QPlan.parallel p q) (toWord (QPlan.parallel p q) inp emb) inp emb := by
  intro f x
  let y := Script.exec (toWord p (fun a => inp (Fin.castAdd _ a)) (fun s => emb (Sum.inl s))) f x
  have hw : Script.exec (toWord (QPlan.parallel p q) inp emb) f x =
      Script.exec (toWord q (fun a => inp (Fin.natAdd _ a)) (fun s => emb (Sum.inr s))) f y :=
    exec_append f _ _ x
  obtain ⟨kp, vp⟩ := hp f x
  obtain ⟨kq, vq⟩ := hq f y
  refine ⟨fun r hr => ?_, fun b v => ?_⟩
  · rw [hw]; exact (kq r (fun s => hr _)).trans (kp r (fun s => hr _))
  · change _ = rowSum (directSum (p.eval f) (q.eval f)) x inp b v
    rw [hw]
    refine Fin.addCases (fun b => ?_) (fun b => ?_) b
    · have ho : outR (QPlan.parallel p q) (Fin.castAdd u b) = Sum.inl (outR p b) := by
        show Fin.addCases (motive := fun _ => Roles (QPlan.parallel p q))
          (fun b => Sum.inl (outR p b)) (fun b => Sum.inr (outR q b)) (Fin.castAdd u b) = _
        exact Fin.addCases_left _
      rw [ho, rowSum_sum_left]
      exact (congrFun (kq _ (fun s h => Sum.inl_ne_inr (he h).symm)) _).trans (vp b v)
    · have ho : outR (QPlan.parallel p q) (Fin.natAdd o b) = Sum.inr (outR q b) := by
        show Fin.addCases (motive := fun _ => Roles (QPlan.parallel p q))
          (fun b => Sum.inl (outR p b)) (fun b => Sum.inr (outR q b)) (Fin.natAdd o b) = _
        exact Fin.addCases_right _
      rw [ho, vq, rowSum_sum_right]
      unfold rowSum
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [show y (inp (Fin.natAdd i c.1)) = x (inp (Fin.natAdd i c.1)) from
        kp _ (fun s => Ne.symm (hd _ _))]

/-- Main realisation lemma: the word of every plan computes its complex semantics. -/
theorem realise {i o : ℕ} (p : QPlan A i o) :
    ∀ (inp : Fin i → ρ) (emb : Roles p → ρ), Function.Injective emb → (∀ a s, inp a ≠ emb s) →
      Realises p (toWord p inp emb) inp emb := by
  induction p with
  | mix coeff => exact fun inp emb he _ => mix_realises coeff inp emb he
  | perm π => exact fun inp emb _ _ => perm_realises π inp emb
  | scale q test table => exact fun inp emb he _ => scale_realises test table inp emb he
  | child a => exact fun inp emb _ _ => child_realises a inp emb
  | seq p q ihp ihq =>
    intro inp emb he hd
    exact seq_realises p q inp emb
      (ihq inp _ (fun s t h => Sum.inr_injective (he h)) (fun a s => hd a _))
      (ihp _ _ (fun s t h => Sum.inl_injective (he h)) (fun a s h => Sum.inr_ne_inl (he h)))
  | parallel p q ihp ihq =>
    intro inp emb he hd
    exact parallel_realises p q inp emb he hd
      (ihp _ _ (fun s t h => Sum.inl_injective (he h)) (fun a s => hd _ _))
      (ihq _ _ (fun s t h => Sum.inr_injective (he h)) (fun a s => hd _ _))

/-- Only child calls carry a rank, each of rank 2. -/
theorem toWord_ranks {i o : ℕ} (p : QPlan A i o) (inp : Fin i → ρ) (emb : Roles p → ρ) :
    (toWord p inp emb).filterMap Move.rk? = List.replicate p.calls 2 := by
  induction p with
  | mix coeff => rfl
  | perm π => rfl
  | scale q test table =>
    show (scaleWord test table (inp 0) emb).filterMap Move.rk? = List.replicate 0 2
    simp only [scaleWord, List.filterMap_append, List.replicate_zero]
    have h : ((Finset.univ : Finset (QV q)).toList.flatMap fun u =>
        bphOne (A := A) (emb (some u)) (gtest test u)).filterMap Move.rk? = [] := by
      rw [List.filterMap_flatMap]
      exact List.flatMap_eq_nil_iff.2 fun _ _ => rfl
    rw [h]; rfl
  | child a => rfl
  | seq p q ihp ihq =>
    show (toWord q _ _ ++ toWord p _ _).filterMap Move.rk? = List.replicate (p.calls + q.calls) 2
    rw [List.filterMap_append, ihp, ihq, ← List.replicate_add, add_comm]
  | parallel p q ihp ihq =>
    show (toWord p _ _ ++ toWord q _ _).filterMap Move.rk? = List.replicate (p.calls + q.calls) 2
    rw [List.filterMap_append, ihp, ihq, List.replicate_add]

end Semantics

/-! ## The unit: phases, plan, copy back, phases -/
section Unit
open Complex
variable {A : ℕ}

def phWord {ρ : Type*} (r : ρ) (zs : List (Space (Bit A) × F)) : Script (Bit A) ρ :=
  zs.map fun t => .phase r t.1 t.2

def phVal (zs : List (Space (Bit A) × F)) (v : Space (Bit A)) : ℂ :=
  (zs.map fun t => phaseI (dot t.1 v + t.2)).prod

lemma phWord_walk {ρ : Type*} [Fintype ρ] [DecidableEq ρ] (r : ρ) (zs : List (Space (Bit A) × F))
    (f : ℕ) (x : Data (Bit A) ρ f) :
    Script.exec (phWord r zs) f x = roleAct f r (diagonal (phVal zs)) x := by
  induction zs generalizing x with
  | nil =>
    have h1 : diagonal (phVal (A := A) []) = 1 := by
      simp only [diagonal_eq_one]; rfl
    rw [h1]; funext j; simp only [phWord, List.map_nil, exec_nil, roleAct, matAct_one, ite_self]
  | cons t zs ih =>
    rw [phWord, List.map_cons, exec_cons, ← phWord, ih]
    simp only [Move.act, roleAct_mul, diagonal_mul_diagonal]
    congr 2; funext v; simp only [phVal, mul_comm, List.map_cons, List.prod_cons]

lemma phVal_append (a b : List (Space (Bit A) × F)) (v : Space (Bit A)) :
    phVal (a ++ b) v = phVal a v * phVal b v := by
  simp only [phVal, List.map_append, List.prod_append]

lemma phVal_flatMap {β : Type*} (L : List β) (g : β → List (Space (Bit A) × F)) (v : Space (Bit A)) :
    phVal (L.flatMap g) v = (L.map fun b => phVal (g b) v).prod := by
  induction L with
  | nil => simp only [phVal, List.flatMap_nil, List.map_nil, List.prod_nil]
  | cons b L ih => rw [List.flatMap_cons, phVal_append, ih]; simp only [List.map_cons, List.prod_cons]

def preZ : List (Space (Bit A) × F) :=
  (Finset.univ : Finset (Bit A)).toList.flatMap fun β => [(eu β, 0), (eu β, 0), (eu β, 0)]

def postZ : List (Space (Bit A) × F) := preZ ++ List.replicate A (0, 1)

lemma phVal_preZ (v : Space (Bit A)) : phVal preZ v = ∏ β, phaseI (v β) ^ 3 := by
  rw [preZ, phVal_flatMap, Finset.prod_map_toList]
  refine Finset.prod_congr rfl fun β _ => ?_
  simp only [phVal, List.map_cons, dot_eu_left, add_zero, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_three]

lemma phVal_postZ (v : Space (Bit A)) : phVal postZ v = (∏ β, phaseI (v β) ^ 3) * I ^ A := by
  rw [postZ, phVal_append, phVal_preZ]
  simp only [phVal, List.map_replicate, List.prod_replicate, dot_zero_left, zero_add, phaseI,
    if_neg one_ne]


/-- The full standard basis of the `2A` bits. -/
def fullBasis : Fin (Fintype.card (Bit A)) → Space (Bit A) :=
  fun i => eu ((Fintype.equivFin (Bit A)).symm i)

lemma fullBasis_indep : LinearIndependent F (fullBasis (A := A)) := by
  have h : fullBasis (A := A) = (Pi.basisFun F (Bit A)) ∘ (Fintype.equivFin (Bit A)).symm := by
    funext i; funext j
    simp only [fullBasis, eu, eq_comm, Function.comp_apply, Pi.basisFun_apply, Pi.single_apply]
  rw [h]
  exact (Pi.basisFun F (Bit A)).linearIndependent.comp _ (Equiv.injective _)

lemma blockMat_full : blockMat (fullBasis (A := A)) = rippleMat (Bit A) :=
  blockMat_units (Fintype.equivFin (Bit A)).symm

variable {W : ℕ}

def copyBack (p : QPlan A W W) : Move (Bit A) (Fin W ⊕ Roles p) :=
  .mix (mixG (fun a : Fin W => (Sum.inr (outR p a) : Fin W ⊕ Roles p)) Sum.inl
    (fun b a => if a = b then 1 else 0)) 0

/-- The unit word for a plan on `W` rows. -/
def unitWord (p : QPlan A W W) : Script (Bit A) (Fin W ⊕ Roles p) :=
  ((Finset.univ : Finset (Fin W)).toList.flatMap fun l => phWord (Sum.inl l) preZ) ++
  (toWord p Sum.inl Sum.inr ++
    (copyBack p :: ((Finset.univ : Finset (Fin W)).toList.flatMap fun l => phWord (Sum.inl l) postZ)))

theorem unit_live (p : QPlan A W W) (ok : QCorrect p) :
    RoleKernel.Drives (Sum.inl : Fin W → Fin W ⊕ Roles p)
      (fun _ => blockMat (fullBasis (A := A))) (unitWord p) := by
  refine ⟨fun f l => funext fun vv => ?_⟩
  obtain ⟨v, -⟩ := vv
  show Script.exec (unitWord p) f v (Sum.inl l) = letterwise f (blockMat fullBasis) (v (Sum.inl l))
  let L := (Finset.univ : Finset (Fin W)).toList
  have hL : L.Nodup := Finset.nodup_toList _
  have hlL : l ∈ L := Finset.mem_toList.2 (Finset.mem_univ _)
  have hpre := multi_walk (ρ := Fin W ⊕ Roles p) Sum.inl Sum.inl_injective
    (fun l => phWord (Sum.inl l) preZ) (fun _ => _) (fun l f x => phWord_walk (Sum.inl l) preZ f x) f L hL v
  let x1 := Script.exec (L.flatMap fun l => phWord (Sum.inl l) preZ) f v
  have hreal := realise p Sum.inl Sum.inr Sum.inr_injective (fun a s h => Sum.inl_ne_inr h) f x1
  let x2 := Script.exec (toWord p Sum.inl Sum.inr) f x1
  let x3 := (copyBack p).act f x2
  have hpost := multi_walk (ρ := Fin W ⊕ Roles p) Sum.inl Sum.inl_injective
    (fun l => phWord (Sum.inl l) postZ) (fun _ => _) (fun l f x => phWord_walk (Sum.inl l) postZ f x) f L hL x3
  have hw : Script.exec (unitWord p) f v = Script.exec (L.flatMap fun l => phWord (Sum.inl l) postZ) f x3 := by
    simp only [unitWord, exec_append, exec_cons]; rfl
  have h3 : x3 (Sum.inl l) = x2 (Sum.inr (outR p l)) := by
    funext y
    have := mixG_out (A := A) (fun a : Fin W => (Sum.inr (outR p a) : Fin W ⊕ Roles p)) Sum.inl
      Sum.inl_injective (fun b a => if a = b then 1 else 0) f x2 l y
    rw [show x3 (Sum.inl l) y = _ from this,
      Finset.sum_eq_single l (fun a _ ha => by simp only [ha, ↓reduceIte, Rat.cast_zero, zero_mul]) (by simp only [mem_univ, not_true_eq_false, ↓reduceIte, Rat.cast_one, one_mul, IsEmpty.forall_iff])]
    simp only [↓reduceIte, Rat.cast_one, one_mul]
  rw [hw, hpost.2 l hlL, h3, blockMat_full]
  funext b
  rw [matAct_diag, matAct_apply', ← (skyEquiv A f).sum_comp]
  have hb : b = toSky (toAddr b) := rfl
  rw [show x2 (Sum.inr (outR p l)) b = _ from hreal.2 l (toAddr b), rowSum_correct ok]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  have h1 : x1 (Sum.inl l) (toSky u) = (∏ k, phVal preZ (toSky u k)) * v (Sum.inl l) (toSky u) := by
    rw [show x1 (Sum.inl l) = _ from hpre.2 l hlL, matAct_diag]
  simp only [h1, skyEquiv_apply, phVal_postZ, phVal_preZ, rippleMat_col]
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp only [skyEquiv_apply, toSky_apply, toAddr_apply, toCol_toSp]
  ring

/-- Ranks of the unit word: one block of rank 2 per call. -/
theorem unitWord_ranks (p : QPlan A W W) :
    (unitWord p).filterMap Move.rk? = List.replicate p.calls 2 := by
  have hph : ∀ (zs : List (Space (Bit A) × F)),
      ((Finset.univ : Finset (Fin W)).toList.flatMap fun l =>
        phWord (ρ := Fin W ⊕ Roles p) (Sum.inl l) zs).filterMap Move.rk? = [] := by
    intro zs
    rw [List.filterMap_flatMap]
    exact List.flatMap_eq_nil_iff.2 fun _ _ => by
      rw [phWord, List.filterMap_map]; exact List.filterMap_eq_nil_iff.2 fun _ _ => rfl
  simp only [unitWord, List.filterMap_append, List.filterMap_cons, hph, toWord_ranks]
  simp only [Move.rk?, copyBack, List.append_nil, List.nil_append]

theorem unitWord_proper (p : QPlan A W W) {u : ℕ} (hu : 2 < u) : (unitWord p).Fits u := by
  intro r hr
  rw [unitWord_ranks, List.mem_replicate] at hr
  omega

lemma cardBit (A : ℕ) : Fintype.card (Bit A) = 2 * A := by
  simp only [Bit, Fintype.card_prod, Fintype.card_fin]; exact Nat.mul_comm _ _

end Unit

end
end OAI.PowerSaving.RouteB
end
-- ===== end part 2 =====
