-- The rational binary Walsh template family (`walshTemplate_above_half`), in parts marked
-- `===== begin KP.<part> =====` ... `===== end KP.<part> =====` (KP = kernel pass), each with its own
-- notices and credits; see texts/credits.lean.
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
set_option linter.all false

-- ===== begin KP.FreeFactor =====
section
/-! # The free-rectangle factorization, coordinate level (algebraic core)

In coordinates adapted to a free rectangle, a source address is `((h₁, h₂), (s₁, s₂))`
(`h` = coordinates along the summation space of the targets' routing vectors, `s` = the
residual, both halves) and a target address is `((p₁, p₂), (t₁, t₂))` (`p` = coordinates along
the orthogonal space). When the cross pairing has no `h`-`p` term (this is where the pairing-zero
hypothesis enters), the kernel phase is

`cT o + cS i + eH h₁ (bT t₂) + eH h₂ (bT t₁) + eP (bS s₂) p₁ + eP (bS s₁) p₂ + m (s, t)`.

`free_factor` shows that the matrix with that sign is `Tgt * (Mid * Src)`:
* `Src`: a diagonal sign `cS`, then the partial transform in `h` only (independent of the target
  and, if `cS` is, of the query);
* `Mid`: a signed partial permutation carrying the sign `m` (the query-dependent part);
* `Tgt`: the partial transform in `p` only, then a diagonal sign `cT`.
Unnormalized (entries `±1`, `0`); the powers of two are separate scalars.
`mid_src` gives the entries of `Mid * Src`; `phase_split` splits the phase into these parts.

Adapted in outline from OpenAI's `PrimeEndpointSplit` / `PrimeEndpointFactor`
(`primeCommonKernel_free_factor`); the statement here is coordinate-level and the proof is
this tree's. -/

namespace OAI.Computability.NearSquareRoot.KernelPass
open Finset

/-- The sign character of `F`. -/
def chi (a : ZMod 2) : ℚ := if a = 0 then 1 else -1

lemma chi_add (a b : ZMod 2) : chi (a + b) = chi a * chi b := by
  fin_cases a <;> fin_cases b <;> simp [chi] <;> decide

lemma chi_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) : chi (∑ c ∈ s, f c) = ∏ c ∈ s, chi (f c) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [chi, sum_empty, ↓reduceIte, prod_empty]
  | insert a s ha ih => rw [sum_insert ha, prod_insert ha, chi_add, ih]

end OAI.Computability.NearSquareRoot.KernelPass

namespace OAI.Computability.NearSquareRoot.KernelPass.Free
open Matrix Finset

variable {Hc Sc Pc Tc : Type*} [Fintype Hc] [Fintype Sc] [Fintype Pc] [Fintype Tc]
  [DecidableEq Hc] [DecidableEq Sc] [DecidableEq Pc] [DecidableEq Tc]

/-- Source side: sign `cS`, then the transform in the `h` coordinates of both halves. -/
def Src (eH : Hc → Hc → ZMod 2) (cS : (Hc × Hc) × (Sc × Sc) → ZMod 2) :
    Matrix ((Hc × Hc) × (Sc × Sc)) ((Hc × Hc) × (Sc × Sc)) ℚ :=
  fun m i => if m.2 = i.2 then chi (eH i.1.1 m.1.1 + eH i.1.2 m.1.2 + cS i) else 0

/-- Middle: a signed partial permutation between the two residual/frequency addresses. -/
def Mid (bS : Sc → Pc) (bT : Tc → Hc) (mm : Sc × Sc → Tc × Tc → ZMod 2) :
    Matrix ((Pc × Pc) × (Tc × Tc)) ((Hc × Hc) × (Sc × Sc)) ℚ :=
  fun n m => if m.1 = (bT n.2.2, bT n.2.1) ∧ n.1 = (bS m.2.2, bS m.2.1) then chi (mm m.2 n.2) else 0

/-- Target side: the transform in the `p` coordinates of both halves, then the sign `cT`. -/
def Tgt (eP : Pc → Pc → ZMod 2) (cT : (Pc × Pc) × (Tc × Tc) → ZMod 2) :
    Matrix ((Pc × Pc) × (Tc × Tc)) ((Pc × Pc) × (Tc × Tc)) ℚ :=
  fun o n => if o.2 = n.2 then chi (eP n.1.1 o.1.1 + eP n.1.2 o.1.2 + cT o) else 0

theorem mid_src (eH : Hc → Hc → ZMod 2) (cS : (Hc × Hc) × (Sc × Sc) → ZMod 2) (bS : Sc → Pc)
    (bT : Tc → Hc) (mm : Sc × Sc → Tc × Tc → ZMod 2) (n : (Pc × Pc) × (Tc × Tc))
    (i : (Hc × Hc) × (Sc × Sc)) :
    (Mid bS bT mm * Src eH cS) n i =
      if n.1 = (bS i.2.2, bS i.2.1) then
        chi (mm i.2 n.2 + eH i.1.1 (bT n.2.2) + eH i.1.2 (bT n.2.1) + cS i) else 0 := by
  rw [mul_apply, Finset.sum_eq_single ((bT n.2.2, bT n.2.1), i.2)]
  · simp only [Mid, Src, true_and, if_true]
    split_ifs with h1
    · rw [← chi_add]; congr 1; ring
    · simp only [mul_zero, zero_mul]
  · intro m _ hm
    simp only [Mid, Src]
    by_cases h2 : m.2 = i.2
    · by_cases h1 : m.1 = (bT n.2.2, bT n.2.1)
      · exact absurd (Prod.ext h1 h2 : m = ((bT n.2.2, bT n.2.1), i.2)) hm
      · rw [if_neg (fun h => h1 h.1), zero_mul]
    · rw [if_neg h2, mul_zero]
  · exact fun h => absurd (mem_univ _) h

/-- **Free factorization, coordinate level.** -/
theorem free_factor (eH : Hc → Hc → ZMod 2) (eP : Pc → Pc → ZMod 2)
    (cS : (Hc × Hc) × (Sc × Sc) → ZMod 2) (cT : (Pc × Pc) × (Tc × Tc) → ZMod 2) (bS : Sc → Pc)
    (bT : Tc → Hc) (mm : Sc × Sc → Tc × Tc → ZMod 2) (o : (Pc × Pc) × (Tc × Tc))
    (i : (Hc × Hc) × (Sc × Sc)) :
    (Tgt eP cT * (Mid bS bT mm * Src eH cS)) o i =
      chi (cT o + cS i + eH i.1.1 (bT o.2.2) + eH i.1.2 (bT o.2.1) +
        eP (bS i.2.2) o.1.1 + eP (bS i.2.1) o.1.2 + mm i.2 o.2) := by
  rw [mul_apply, Finset.sum_eq_single ((bS i.2.2, bS i.2.1), o.2)]
  · rw [mid_src]
    simp only [Tgt, if_true]
    rw [← chi_add]; congr 1; ring
  · intro n _ hn
    rw [mid_src]
    by_cases h2 : o.2 = n.2
    · by_cases h1 : n.1 = (bS i.2.2, bS i.2.1)
      · exact absurd (Prod.ext h1 h2.symm : n = ((bS i.2.2, bS i.2.1), o.2)) hn
      · rw [if_neg h1, mul_zero]
    · simp only [Tgt, if_neg h2, zero_mul]
  · exact fun h => absurd (mem_univ _) h

/-- **Cross-pairing split.** `β` is the (symmetric, biadditive) routing form. A source vector is
`ιH h + ιS s`, a target vector `ιP p + ιT t`. If the summation directions pair to zero
(`β (ιH h) (ιP p) = 0`: the pairing-zero hypothesis), and the remaining pairings are read in
the coordinates `eH`, `eP` through `bT`, `bS`, then the kernel phase
`β (a_i + a_o) (b_o + b_i)` has exactly the form factored by `free_factor`, with
`cS = β a_i b_i`, `cT = β a_o b_o` and `m = β (ιS s₁) (ιT t₂) + β (ιT t₁) (ιS s₂)`. -/
theorem phase_split {V : Type*} [AddCommGroup V] (β : V →+ V →+ ZMod 2)
    (hsymm : ∀ x y, β x y = β y x)
    (ιH : Hc → V) (ιS : Sc → V) (ιP : Pc → V) (ιT : Tc → V)
    (eH : Hc → Hc → ZMod 2) (eP : Pc → Pc → ZMod 2) (bS : Sc → Pc) (bT : Tc → Hc)
    (hHP : ∀ h p, β (ιH h) (ιP p) = 0)
    (hHT : ∀ h t, β (ιH h) (ιT t) = eH h (bT t))
    (hSP : ∀ s p, β (ιS s) (ιP p) = eP (bS s) p)
    (h₁ h₂ : Hc) (s₁ s₂ : Sc) (p₁ p₂ : Pc) (t₁ t₂ : Tc) :
    β ((ιH h₁ + ιS s₁) + (ιP p₁ + ιT t₁)) ((ιP p₂ + ιT t₂) + (ιH h₂ + ιS s₂)) =
      β (ιP p₁ + ιT t₁) (ιP p₂ + ιT t₂) + β (ιH h₁ + ιS s₁) (ιH h₂ + ιS s₂) +
        eH h₁ (bT t₂) + eH h₂ (bT t₁) + eP (bS s₂) p₁ + eP (bS s₁) p₂ +
        (β (ιS s₁) (ιT t₂) + β (ιT t₁) (ιS s₂)) := by
  have e1 : β (ιP p₁) (ιH h₂) = 0 := by rw [hsymm]; exact hHP _ _
  have e2 : β (ιT t₁) (ιH h₂) = eH h₂ (bT t₁) := by rw [hsymm]; exact hHT _ _
  have e3 : β (ιP p₁) (ιS s₂) = eP (bS s₂) p₁ := by rw [hsymm]; exact hSP _ _
  simp only [map_add, AddMonoidHom.add_apply, hHP, hHT, hSP, e1, e2, e3]
  ring

end OAI.Computability.NearSquareRoot.KernelPass.Free
end
-- ===== end KP.FreeFactor =====

-- ===== begin KP.Defs =====
section
/-! # Rational kernel-pass plans

A column carries two bits on each of `A` axes; an address is `h` columns. A plan is a finite
list of instructions on rows of data indexed by addresses: rational row mixes, axis additions,
diagonal scalings by a rational table of a column sum, the two-bit Walsh transform of one axis
(`child`, the only instruction that costs a call), composition and juxtaposition.
`QCorrect p` says `p` is the normalized Walsh transform of all `2·A·h` bits on every row, at
every width `h`; `QCandidate.Good` adds the strict call rate `calls / rows < arity ^ (num/den)`.

The semantics is compositional: each instruction is a row matrix tensored (`rowTensor`) with
an address matrix, a tensor power (`colPow`, `piMat`) of a column matrix (`axisMat`, `walshCol`)
where the instruction acts column by column; route B's engine reads it through the entry lemmas
`eval_*_apply`, `directSum_*`, `target_apply`. The six instructions follow
the shape of OpenAI's `KernelPass.Plan` (openai/math), with rational coefficients in place of
dyadic ones. -/

namespace OAI.Computability.NearSquareRoot.KernelPass
open Matrix Finset

/-- A column: two bits on every axis. -/
abbrev Column (A : ℕ) := Fin A → Fin 2 → ZMod 2
/-- An address: `h` columns. -/
abbrev Addr (A h : ℕ) := Fin h → Column A
/-- Matrices from `I` rows to `O` rows of data on addresses. -/
abbrev RowMatrix (A h I O : ℕ) := Matrix (Fin O × Addr A h) (Fin I × Addr A h) ℚ
/-- Matrices on one column. -/
abbrev ColMat (A : ℕ) := Matrix (Column A) (Column A) ℚ

/-- The tensor product of a family of square matrices, one per coordinate of a function space. -/
def piMat {ι K : Type*} [Fintype ι] (M : ι → Matrix K K ℚ) : Matrix (ι → K) (ι → K) ℚ :=
  fun y x => ∏ i, M i (y i) (x i)

/-- The dot product of two bit pairs. -/
def dot (u v : Fin 2 → ZMod 2) : ZMod 2 := u 0 * v 0 + u 1 * v 1

/-- The normalized Walsh matrix of one axis: the sign of the dot product of the two bit pairs, halved. -/
def pairMat : Matrix (Fin 2 → ZMod 2) (Fin 2 → ZMod 2) ℚ := fun u v => chi (dot u v) / 2

/-- The normalized Walsh matrix of a whole column. -/
def walshCol (A : ℕ) : ColMat A := piMat fun _ : Fin A => pairMat

/-- The Walsh matrix of axis `a` alone, the identity on the other axes. -/
def axisMat {A : ℕ} (a : Fin A) : ColMat A := piMat (Function.update (fun _ => 1) a pairMat)

/-- The same column matrix on each of the `h` columns of an address. -/
abbrev colPow {A : ℕ} (h : ℕ) (C : ColMat A) : Matrix (Addr A h) (Addr A h) ℚ := piMat fun _ : Fin h => C

/-- A row matrix `R` tensored with an address matrix `M`. -/
def rowTensor {A h i o : ℕ} (R : Matrix (Fin o) (Fin i) ℚ) (M : Matrix (Addr A h) (Addr A h) ℚ) :
    RowMatrix A h i o := kroneckerMap (· * ·) R M

/-- Row blocks: `Fin (n + m) × X` as the disjoint union of the two row ranges. -/
def rowSplit (n m : ℕ) (X : Type) : Fin (n + m) × X ≃ (Fin n × X) ⊕ (Fin m × X) :=
  (finSumFinEquiv.symm.prodCongr (Equiv.refl X)).trans (Equiv.sumProdDistrib _ _ _)

/-- Block-diagonal juxtaposition of two row matrices. -/
def directSum {i j o u : ℕ} {X : Type} (M : Matrix (Fin o × X) (Fin i × X) ℚ)
    (N : Matrix (Fin u × X) (Fin j × X) ℚ) : Matrix (Fin (o + u) × X) (Fin (i + j) × X) ℚ :=
  (fromBlocks M 0 0 N).submatrix (rowSplit o u X) (rowSplit i j X)

/-- Rational plans: row mixes, additive column permutations (`perm`; an axis `xor` is one of them), diagonal tables of a column sum, the Walsh transform
of one axis (`child`, the only paid instruction), composition and juxtaposition. -/
inductive QPlan (A : ℕ) : ℕ → ℕ → Type
  | mix {i o} (M : Matrix (Fin o) (Fin i) ℚ) : QPlan A i o
  | perm (π : Column A ≃+ Column A) : QPlan A 1 1
  | scale (q : ℕ) (test : Column A → Fin q → ZMod 2) (table : (Fin q → ZMod 2) → ℚ) : QPlan A 1 1
  | child (axis : Fin A) : QPlan A 1 1
  | seq {i j o} (p : QPlan A j o) (q : QPlan A i j) : QPlan A i o
  | parallel {i j o u} (p : QPlan A i o) (q : QPlan A j u) : QPlan A (i+j) (o+u)

variable {A : ℕ}

/-- Paid instructions. -/
def QPlan.calls {i o : ℕ} : QPlan A i o → ℕ
  | .child _ => 1
  | .seq p q | .parallel p q => p.calls + q.calls
  | _ => 0

/-- Compositional semantics at width `h`: every instruction is a row matrix tensored with an
address matrix; `seq` multiplies, `parallel` juxtaposes. -/
def QPlan.eval {i o : ℕ} (h : ℕ) : QPlan A i o → RowMatrix A h i o
  | .mix M => rowTensor M 1
  | .perm π => rowTensor 1 ((1 : Matrix (Addr A h) (Addr A h) ℚ).submatrix id (⇑π ∘ ·))
  | .scale _ test t => rowTensor 1 (diagonal fun x => t (∑ c, test (x c)))
  | .child a => rowTensor 1 (colPow h (axisMat a))
  | .seq p q => p.eval h * q.eval h
  | .parallel p q => directSum (p.eval h) (q.eval h)

/-- The Walsh transform of every column, on each of `W` rows. -/
def target (A W h : ℕ) : RowMatrix A h W W := rowTensor 1 (colPow h (walshCol A))

/-- Correct: the Walsh target at every width. -/
def QCorrect {W : ℕ} (p : QPlan A W W) : Prop := ∀ h, p.eval h = target A W h

/-- A template: arity, rows and a plan. -/
structure QCandidate where
  arity : ℕ
  rows : ℕ
  program : QPlan arity rows rows

/-- Arity at least 5, at least 2 rows, correct, and fewer than `rows · arity ^ (num/den)` calls. -/
def QCandidate.Good (num den : ℕ) (t : QCandidate) : Prop :=
  5 ≤ t.arity ∧ 2 ≤ t.rows ∧ QCorrect t.program ∧
    (t.program.calls : ℝ) < t.rows * (t.arity : ℝ) ^ ((num : ℝ) / den)

/-! Entries. -/

theorem rowTensor_apply {h i o : ℕ} (R : Matrix (Fin o) (Fin i) ℚ) (M : Matrix (Addr A h) (Addr A h) ℚ)
    (b : Fin o) (y : Addr A h) (a : Fin i) (x : Addr A h) :
    rowTensor R M (b, y) (a, x) = R b a * M y x := rfl

theorem eval_mix_apply {h i o : ℕ} (M : Matrix (Fin o) (Fin i) ℚ) (b y a x) :
    (QPlan.mix (A := A) M).eval h (b, y) (a, x) = if x = y then M b a else 0 := by
  simp only [QPlan.eval, rowTensor_apply, one_apply, mul_ite, mul_one, mul_zero, eq_comm]

theorem eval_perm_apply {h : ℕ} (π : Column A ≃+ Column A) (b y a x) :
    (QPlan.perm π).eval h (b, y) (a, x) = if y = ⇑π ∘ x then 1 else 0 := by
  simp only [QPlan.eval, Fin.fin_one_eq_zero b, Fin.isValue, Fin.fin_one_eq_zero a, rowTensor_apply, one_apply, ↓reduceIte, submatrix_apply, id_eq, mul_ite, mul_one, mul_zero]

theorem eval_scale_apply {h q : ℕ} (test : Column A → Fin q → ZMod 2) (t : (Fin q → ZMod 2) → ℚ) (b y a x) :
    (QPlan.scale q test t).eval h (b, y) (a, x) = if x = y then t (∑ c, test (x c)) else 0 := by
  simp only [QPlan.eval, rowTensor_apply, diagonal_apply, Fin.fin_one_eq_zero b, Fin.fin_one_eq_zero a, one_apply_eq,
    one_mul]
  by_cases e : x = y <;> simp [e, Ne.symm]

theorem eval_child_apply {h : ℕ} (c : Fin A) (b y a x) :
    (QPlan.child c).eval h (b, y) (a, x) = colPow h (axisMat c) y x := by
  simp only [QPlan.eval, Fin.fin_one_eq_zero b, Fin.isValue, Fin.fin_one_eq_zero a, rowTensor_apply, one_apply_eq, one_mul]

theorem target_apply (W h : ℕ) (b y a x) :
    target A W h (b, y) (a, x) = if a = b then colPow h (walshCol A) y x else 0 := by
  simp only [target, rowTensor_apply, one_apply, ite_mul, one_mul, zero_mul, eq_comm]

section
variable {i j o u : ℕ} {X : Type} (M : Matrix (Fin o × X) (Fin i × X) ℚ) (N : Matrix (Fin u × X) (Fin j × X) ℚ)
  (y x : X)
theorem directSum_ll (b : Fin o) (a : Fin i) : directSum M N (Fin.castAdd u b, y) (Fin.castAdd j a, x) = M (b, y) (a, x) := by
  simp only [directSum, rowSplit, Equiv.coe_trans, Equiv.prodCongr_apply, Equiv.coe_refl, submatrix_apply, Function.comp_apply, Prod.map_apply, finSumFinEquiv_symm_apply_castAdd, id_eq, Equiv.sumProdDistrib_apply_left, fromBlocks_apply₁₁]
theorem directSum_lr (b : Fin o) (a : Fin j) : directSum M N (Fin.castAdd u b, y) (Fin.natAdd i a, x) = 0 := by
  simp only [directSum, rowSplit, Equiv.coe_trans, Equiv.prodCongr_apply, Equiv.coe_refl, submatrix_apply, Function.comp_apply, Prod.map_apply, finSumFinEquiv_symm_apply_castAdd, id_eq, Equiv.sumProdDistrib_apply_left, finSumFinEquiv_symm_apply_natAdd, Equiv.sumProdDistrib_apply_right, fromBlocks_apply₁₂, Matrix.zero_apply]
theorem directSum_rl (b : Fin u) (a : Fin i) : directSum M N (Fin.natAdd o b, y) (Fin.castAdd j a, x) = 0 := by
  simp only [directSum, rowSplit, Equiv.coe_trans, Equiv.prodCongr_apply, Equiv.coe_refl, submatrix_apply, Function.comp_apply, Prod.map_apply, finSumFinEquiv_symm_apply_natAdd, id_eq, Equiv.sumProdDistrib_apply_right, finSumFinEquiv_symm_apply_castAdd, Equiv.sumProdDistrib_apply_left, fromBlocks_apply₂₁, Matrix.zero_apply]
theorem directSum_rr (b : Fin u) (a : Fin j) : directSum M N (Fin.natAdd o b, y) (Fin.natAdd i a, x) = N (b, y) (a, x) := by
  simp only [directSum, rowSplit, Equiv.coe_trans, Equiv.prodCongr_apply, Equiv.coe_refl, submatrix_apply, Function.comp_apply, Prod.map_apply, finSumFinEquiv_symm_apply_natAdd, id_eq, Equiv.sumProdDistrib_apply_right, fromBlocks_apply₂₂]
end

end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.Defs =====

-- ===== begin KP.Tensor =====
section
/-! # Tensor products of column matrices

`piMat M` is the product matrix of a family of matrices on the coordinates of a function
space. Single-row plans whose eval is a column-wise product are handled through `OneRow`. -/

namespace OAI.Computability.NearSquareRoot.KernelPass
open Matrix Finset

section
variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Fintype K] [DecidableEq K]

theorem piMat_mul (M N : ι → Matrix K K ℚ) : piMat M * piMat N = piMat fun i => M i * N i := by
  ext y x
  simp only [piMat, mul_apply, ← prod_mul_distrib]
  exact (Fintype.prod_sum fun i k => M i (y i) k * N i k (x i)).symm

theorem piMat_one : piMat (fun _ : ι => (1 : Matrix K K ℚ)) = 1 := by
  ext y x
  simp only [piMat, one_apply]
  by_cases h : y = x
  · simp only [h, ↓reduceIte, prod_const_one]
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 h
    rw [if_neg h]; exact prod_eq_zero (mem_univ i) (if_neg hi)

omit [Fintype K] in
theorem piMat_update (a : ι) (P : Matrix K K ℚ) (y x : ι → K) :
    piMat (Function.update (fun _ => 1) a P) y x =
      if ∀ b ≠ a, x b = y b then P (y a) (x a) else 0 := by
  simp only [piMat]
  rw [← mul_prod_erase _ _ (mem_univ a)]
  simp only [Function.update_self]
  split_ifs with h
  · rw [prod_eq_one, mul_one]
    intro b hb
    rw [Function.update_of_ne (ne_of_mem_erase hb), one_apply, if_pos (h b (ne_of_mem_erase hb)).symm]
  · push_neg at h
    obtain ⟨b, hb, hne⟩ := h
    rw [prod_eq_zero (mem_erase.2 ⟨hb, mem_univ b⟩), mul_zero]
    rw [Function.update_of_ne hb, one_apply, ite_eq_right_iff.2 fun e => absurd e.symm hne]
end

/-- A one-row matrix that is the `h`-th tensor power of a column matrix. -/
def OneRow {A h : ℕ} (M : RowMatrix A h 1 1) (C : ColMat A) : Prop :=
  ∀ y x, M (0, y) (0, x) = piMat (fun _ : Fin h => C) y x

theorem OneRow.mul {A h : ℕ} {M N : RowMatrix A h 1 1} {C D : ColMat A} (hM : OneRow M C)
    (hN : OneRow N D) : OneRow (M * N) (C * D) := by
  intro y x
  rw [← piMat_mul, mul_apply, mul_apply, Fintype.sum_prod_type, Fin.sum_univ_one]
  exact Finset.sum_congr rfl fun z _ => by rw [hM, hN]

theorem child_oneRow {A h : ℕ} (a : Fin A) : OneRow ((QPlan.child a).eval h) (axisMat a) :=
  fun y x => eval_child_apply a 0 y 0 x

end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.Tensor =====

-- ===== begin KP.Naive =====
section
/-! # The naive baseline plan

`child a` for every axis, on every row. It is `QCorrect` at every width and makes `A·W` calls,
rate `A = A^1`. -/

namespace OAI.Computability.NearSquareRoot.KernelPass
open Matrix Finset

/-- The identity one-row plan. -/
def idPlan (A : ℕ) : QPlan A 1 1 := .mix 1

theorem idPlan_oneRow {A h : ℕ} : OneRow ((idPlan A).eval h) 1 := by
  intro y x
  rw [piMat_one, idPlan, eval_mix_apply, one_apply, one_apply]; simp only [eq_comm, Fin.isValue, ↓reduceIte]

/-- Child calls on a list of axes, last first. -/
def chainPlan {A : ℕ} : List (Fin A) → QPlan A 1 1
  | [] => idPlan A
  | a :: l => .seq (.child a) (chainPlan l)

theorem chainPlan_calls {A : ℕ} (l : List (Fin A)) : (chainPlan l).calls = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [chainPlan, QPlan.calls, ih, add_comm, List.length_cons, Nat.add_left_cancel_iff]

theorem chainPlan_oneRow {A h : ℕ} (l : List (Fin A)) (hl : l.Nodup) :
    OneRow ((chainPlan l).eval h) (piMat fun b => if b ∈ l then pairMat else 1) := by
  induction l with
  | nil => simpa only [chainPlan, List.not_mem_nil, ↓reduceIte, piMat_one] using idPlan_oneRow
  | cons a l ih =>
    obtain ⟨ha, hl⟩ := List.nodup_cons.1 hl
    have := (child_oneRow (h := h) a).mul (ih hl)
    unfold axisMat at this
    rw [piMat_mul] at this
    have e : (piMat fun b => if b ∈ a :: l then pairMat else 1) =
        piMat fun b => Function.update (fun _ => 1) a pairMat b * if b ∈ l then pairMat else 1 := by
      congr 1; funext b
      by_cases hb : b = a
      · subst hb; simp only [List.mem_cons, ha, or_false, ↓reduceIte, Function.update_self, mul_one]
      · simp only [List.mem_cons, hb, false_or, ne_eq, not_false_eq_true, Function.update_of_ne, mul_ite, one_mul, mul_one]
    rw [e]; exact this

/-- All axes, one call each. -/
def rowPlan (A : ℕ) : QPlan A 1 1 := chainPlan (List.finRange A)

theorem rowPlan_oneRow {A h : ℕ} : OneRow ((rowPlan A).eval h) (walshCol A) := by
  show OneRow ((chainPlan _).eval h) _
  simpa only [walshCol, List.mem_finRange, ↓reduceIte] using chainPlan_oneRow (h := h) (List.finRange A) (List.nodup_finRange A)

end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.Naive =====

-- ===== begin KP.Query =====
section
/-! # The query identity as a plan

For two axes `i ≠ j` the quadratic query `Q x = x i · x j` (dot product of the two bit pairs)
has, conjugated by the full column Walsh transform,
`W · D_Q · W = D_Q · (H_i H_j ∘ swap_ij) · D_Q`: a chirp, the partial Walsh transform on the two
active axes composed with the free axis swap, and a chirp (`query_col`). `queryPlan i j` realises
the right side with two `child` calls (`queryPlan_oneRow`, `queryPlan_calls`). -/

namespace OAI.Computability.NearSquareRoot.KernelPass
open Matrix Finset

variable {A : ℕ}

/-- Two-bit dot product over `F`. -/


lemma sum_zmod2 (f : ZMod 2 → ℚ) : ∑ a, f a = f 0 + f 1 := by
  rw [show (univ : Finset (ZMod 2)) = {0, 1} from rfl, sum_pair (by decide)]

lemma sum_chi_mul (c : ZMod 2) : ∑ a : ZMod 2, chi (a * c) = if c = 0 then 2 else 0 := by
  rw [sum_zmod2]
  obtain rfl | rfl : c = 0 ∨ c = 1 := by revert c; decide
  · simp only [chi, mul_zero, ↓reduceIte]; norm_num
  · simp only [chi, mul_one, ↓reduceIte, one_ne_zero, add_neg_cancel]

lemma sum_chi_dot (v : Fin 2 → ZMod 2) :
    ∑ u : Fin 2 → ZMod 2, chi (dot u v) = if v = 0 then 4 else 0 := by
  have e : ∀ u : Fin 2 → ZMod 2, chi (dot u v) = ∏ k : Fin 2, chi (u k * v k) := by
    intro u; rw [Fin.prod_univ_two, dot, chi_add]
  simp only [e]
  rw [← Fintype.prod_sum (fun k a => chi (a * v k)), Fin.prod_univ_two, sum_chi_mul, sum_chi_mul]
  have hv : v = 0 ↔ v 0 = 0 ∧ v 1 = 0 := by
    constructor
    · rintro rfl; simp only [Pi.zero_apply, and_self]
    · rintro ⟨h0, h1⟩; ext k; fin_cases k <;> simp [h0, h1]
  by_cases h0 : v 0 = 0 <;> by_cases h1 : v 1 = 0 <;> simp [h0, h1, hv] <;> norm_num

lemma pairMat_apply (u v : Fin 2 → ZMod 2) : pairMat u v = chi (dot u v) / 2 := rfl

def sgn2 (u v : Fin 2 → ZMod 2) : ℚ := chi (dot u v)

def qc (i j : Fin A) (x : Column A) : ℚ := sgn2 (x i) (x j)

def permMat (f : Column A → Column A) : ColMat A := fun y x => if y = f x then 1 else 0

theorem permMat_mul (f g : Column A → Column A) : permMat f * permMat g = permMat (f ∘ g) := by
  ext y x
  rw [mul_apply, Finset.sum_eq_single (g x)] <;> simp +contextual [permMat]

def swapCol (i j : Fin A) (x : Column A) : Column A := fun a => x (Equiv.swap i j a)

theorem mul_permMat_apply (M : ColMat A) (f : Column A → Column A) (y x : Column A) :
    (M * permMat f) y x = M y (f x) := by
  rw [mul_apply, Finset.sum_eq_single (f x)] <;> simp +contextual [permMat]

theorem piMat_update2 {i j : Fin A} (hij : i ≠ j) (Mi Mj : Matrix (Fin 2 → ZMod 2) (Fin 2 → ZMod 2) ℚ)
    (y x : Column A) :
    piMat (Function.update (Function.update (fun _ => 1) i Mi) j Mj) y x =
      if ∀ b, b ≠ i → b ≠ j → x b = y b then Mi (y i) (x i) * Mj (y j) (x j) else 0 := by
  simp only [piMat]
  rw [← mul_prod_erase _ _ (mem_univ j), ← mul_prod_erase _ _ (mem_erase.2 ⟨hij, mem_univ i⟩)]
  simp only [Function.update_self, Function.update_of_ne hij]
  split_ifs with h
  · rw [prod_eq_one, mul_one, mul_comm]
    intro b hb
    have hbi : b ≠ i := ne_of_mem_erase hb
    have hbj : b ≠ j := ne_of_mem_erase (mem_of_mem_erase hb)
    rw [Function.update_of_ne hbj, Function.update_of_ne hbi, one_apply, if_pos (h b hbi hbj).symm]
  · push_neg at h
    obtain ⟨b, hbi, hbj, hne⟩ := h
    rw [prod_eq_zero (show b ∈ (univ.erase j).erase i by simp only [mem_erase, ne_eq, hbi, not_false_eq_true, hbj, mem_univ, and_self]), mul_zero, mul_zero]
    rw [Function.update_of_ne hbj, Function.update_of_ne hbi, one_apply,
      ite_eq_right_iff.2 fun e => absurd e.symm hne]

lemma dot_comm (a b : Fin 2 → ZMod 2) : dot a b = dot b a := by simp only [dot]; ring

lemma pairMat_mul_diag_mul (a b : Fin 2 → ZMod 2) (d : (Fin 2 → ZMod 2) → ℚ) :
    (pairMat * diagonal d * pairMat) a b = ∑ u, chi (dot a u) * d u * chi (dot u b) / 4 := by
  simp only [mul_apply, diagonal_apply, pairMat_apply, mul_ite, mul_zero, ite_mul, zero_mul,
    sum_ite_eq', mem_univ, if_true]
  refine sum_congr rfl fun u _ => by ring

lemma dot_add_right (a b c : Fin 2 → ZMod 2) : dot a (b + c) = dot a b + dot a c := by
  simp only [dot, Pi.add_apply]; ring

lemma add_eq_zero_iff' (a b : Fin 2 → ZMod 2) : a + b = 0 ↔ a = b := by
  constructor
  · intro h; ext k; have := congrFun h k; simp only [Pi.add_apply, Pi.zero_apply] at this
    exact (add_eq_zero_iff_eq_neg.1 this).trans (ZMod.neg_eq_self_mod_two _)
  · rintro rfl; ext k; simp only [Pi.add_apply, CharTwo.add_self_eq_zero, Pi.zero_apply]

/-- Two-bit identities of the two-bit Walsh matrix. -/
lemma pair_sq : pairMat * pairMat = 1 := by
  have := pairMat_mul_diag_mul (d := fun _ => 1)
  rw [diagonal_one, mul_one] at this
  ext a b
  rw [this]
  have key : ∀ u, chi (dot a u) * 1 * chi (dot u b) / 4 = chi (dot u (a + b)) * (1/4) := by
    intro u; rw [mul_one, ← chi_add, dot_comm a u, dot_add_right]; ring
  rw [sum_congr rfl fun u _ => key u, ← sum_mul, sum_chi_dot, one_apply]
  simp only [add_eq_zero_iff']
  split_ifs <;> norm_num

/-- The diagonal query as a sum of product diagonals. -/
def qTerm (i j : Fin A) (w : Fin 2 → ZMod 2) : Fin A → Matrix (Fin 2 → ZMod 2) (Fin 2 → ZMod 2) ℚ :=
  Function.update (Function.update (fun _ => 1) i (diagonal fun u => sgn2 u w)) j
    (diagonal fun u => if u = w then 1 else 0)

theorem diag_qc {i j : Fin A} (hij : i ≠ j) :
    diagonal (qc i j) = ∑ w, piMat (qTerm i j w) := by
  ext y x
  rw [Matrix.sum_apply]
  simp only [qTerm, piMat_update2 hij, diagonal_apply]
  by_cases e : y = x
  · subst e; simp only [↓reduceIte, qc, ne_eq, implies_true, mul_ite, mul_one, mul_zero, sum_ite_eq, mem_univ]
  · rw [if_neg e]; symm; refine sum_eq_zero fun w _ => ?_
    have hn : ¬ ((∀ b, b ≠ i → b ≠ j → x b = y b) ∧ y i = x i ∧ y j = x j) := by
      rintro ⟨h1, h2, h3⟩
      exact e (funext fun b => by
        by_cases hb : b = i
        · subst hb; exact h2
        · by_cases hb' : b = j
          · subst hb'; exact h3
          · exact (h1 b hb hb').symm)
    by_cases h1 : ∀ b, b ≠ i → b ≠ j → x b = y b
    · rw [if_pos h1]
      by_cases h2 : y i = x i
      · by_cases h3 : y j = x j
        · exact absurd ⟨h1, h2, h3⟩ hn
        · simp only [h3, ↓reduceIte, mul_zero]
      · simp only [h2, ↓reduceIte, mul_ite, mul_one, mul_zero, ite_self]
    · rw [if_neg h1]

theorem pDp (a b w : Fin 2 → ZMod 2) :
    (pairMat * diagonal (fun u => sgn2 u w) * pairMat) a b = if a + b = w then 1 else 0 := by
  rw [pairMat_mul_diag_mul]
  have key : ∀ u, chi (dot a u) * sgn2 u w * chi (dot u b) / 4 = chi (dot u (a + b + w)) * (1/4) := by
    intro u
    rw [sgn2, ← chi_add, ← chi_add, div_eq_mul_one_div]
    congr 2; simp only [dot, Pi.add_apply]; ring
  rw [sum_congr rfl fun u _ => key u, ← sum_mul, sum_chi_dot]
  simp only [add_eq_zero_iff']
  split_ifs <;> norm_num

theorem pEp (a b w : Fin 2 → ZMod 2) :
    (pairMat * diagonal (fun u => if u = w then (1 : ℚ) else 0) * pairMat) a b =
      chi (dot a w) * chi (dot w b) / 4 := by
  rw [pairMat_mul_diag_mul]
  simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul, ite_div, zero_div]
  rw [sum_ite_eq']; simp only [mem_univ, ↓reduceIte]

/-- The Walsh conjugate of the query `(-1)^{x_i·x_j}` is chirp · (partial Walsh on the two
active axes ∘ swap) · chirp, with identity on all spectator axes. -/
theorem query_col {i j : Fin A} (hij : i ≠ j) :
    walshCol A * diagonal (qc i j) * walshCol A =
      diagonal (qc i j) * (piMat (Function.update (Function.update (fun _ => 1) i pairMat) j pairMat) *
        permMat (swapCol i j)) * diagonal (qc i j) := by
  rw [diag_qc hij, mul_sum, sum_mul]
  simp only [walshCol, piMat_mul]
  have hfun : ∀ w, (fun a => pairMat * qTerm i j w a * pairMat) =
      Function.update (Function.update (fun _ => 1) i
        (pairMat * diagonal (fun u => sgn2 u w) * pairMat)) j
        (pairMat * diagonal (fun u => if u = w then 1 else 0) * pairMat) := by
    intro w; funext a
    by_cases ha : a = j
    · subst ha; simp only [qTerm, Function.update_self]
    · by_cases hb : a = i
      · subst hb; simp only [qTerm, Function.update_of_ne hij, Function.update_self]
      · simp only [qTerm, Function.update_of_ne ha, Function.update_of_ne hb, mul_one, pair_sq]
  simp only [hfun]
  rw [← diag_qc hij]
  ext y x
  rw [Matrix.sum_apply]
  simp only [piMat_update2 hij, pDp, pEp]
  rw [mul_diagonal, diagonal_mul, mul_permMat_apply, piMat_update2 hij]
  have hrest : (∀ b, b ≠ i → b ≠ j → swapCol i j x b = y b) ↔
      (∀ b, b ≠ i → b ≠ j → x b = y b) := by
    refine forall_congr' fun b => imp_congr_right fun hi => imp_congr_right fun hj => ?_
    rw [swapCol, Equiv.swap_apply_of_ne_of_ne hi hj]
  simp_rw [hrest]
  simp only [swapCol, Equiv.swap_apply_left, Equiv.swap_apply_right]
  split_ifs with h
  · simp only [ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ, if_true]
    simp only [qc, sgn2, pairMat_apply]
    have e : chi (dot (y j) (y i + x i)) * chi (dot (y i + x i) (x j)) =
        chi (dot (y i) (y j)) * chi (dot (y i) (x j)) * chi (dot (y j) (x i)) * chi (dot (x i) (x j)) := by
      simp only [← chi_add]; congr 1; simp only [dot, Pi.add_apply]; ring
    linear_combination (1/4 : ℚ) * e
  · simp only [sum_const_zero, mul_zero, zero_mul]

/-! ### The query plan -/


theorem piMat_diagonal' {ι K : Type*} [Fintype ι] [DecidableEq ι] [Fintype K] [DecidableEq K]
    (d : ι → K → ℚ) : piMat (fun i : ι => diagonal (d i)) = diagonal fun x => ∏ i, d i (x i) := by
  ext y x
  simp only [piMat, diagonal_apply]
  rw [prod_ite_zero]
  simp only [mem_univ, true_implies, funext_iff]

theorem piMat_diagonal {ι K : Type*} [Fintype ι] [DecidableEq ι] [Fintype K] [DecidableEq K]
    (d : K → ℚ) : piMat (fun _ : ι => diagonal d) = diagonal fun x => ∏ c, d (x c) :=
  piMat_diagonal' fun _ => d

theorem piMat_perm {ι K : Type*} [Fintype ι] [DecidableEq ι] [Fintype K] [DecidableEq K]
    (f : K → K) :
    piMat (fun _ : ι => (fun y x => if y = f x then 1 else 0 : Matrix K K ℚ)) =
      fun y x => if y = f ∘ x then 1 else 0 := by
  ext y x
  simp only [piMat]
  rw [prod_ite_zero]
  simp only [mem_univ, true_implies, funext_iff, Function.comp_apply, prod_const_one]

/-- The chirp `(-1)^{x_i·x_j}` on every column, as a `scale` move. -/
def chirp (i j : Fin A) : QPlan A 1 1 :=
  .scale 1 (fun x _ => dot (x i) (x j)) (fun s => if s 0 = 0 then 1 else -1)

theorem chirp_oneRow {h : ℕ} (i j : Fin A) : OneRow ((chirp i j).eval h) (diagonal (qc i j)) := by
  intro y x
  rw [piMat_diagonal, diagonal_apply]
  simp only [chirp]
  rw [eval_scale_apply, eq_comm]
  by_cases e : y = x
  · subst e
    simp only [if_true]
    have : (if (∑ c, fun _ : Fin 1 => dot (y c i) (y c j)) 0 = 0 then (1 : ℚ) else -1) =
        chi (∑ c, dot (y c i) (y c j)) := by
      rw [Finset.sum_apply]; rfl
    rw [this, chi_sum]; rfl
  · rw [if_neg e, if_neg (Ne.symm e)]

/-- A free move is any additive permutation of columns. -/
theorem perm_oneRow {h : ℕ} (π : Column A ≃+ Column A) : OneRow ((QPlan.perm π).eval h) (permMat π) := by
  intro y x
  rw [eval_perm_apply, show permMat (⇑π) = (fun y x => if y = π x then (1 : ℚ) else 0) from rfl,
    piMat_perm]

/-- The axis swap as an additive permutation of columns. -/
def swapAdd (i j : Fin A) : Column A ≃+ Column A where
  toFun := swapCol i j
  invFun := swapCol i j
  left_inv x := by funext a; simp only [swapCol, Equiv.swap_apply_self]
  right_inv x := by funext a; simp only [swapCol, Equiv.swap_apply_self]
  map_add' _ _ := rfl

/-- The free axis swap: one `perm` move. -/
def swapPlan (i j : Fin A) : QPlan A 1 1 := .perm (swapAdd i j)

theorem swapPlan_oneRow {h : ℕ} (i j : Fin A) :
    OneRow ((swapPlan i j).eval h) (permMat (swapCol i j)) := perm_oneRow _

/-- The query identity as a plan: chirp, two partial transforms, the free swap, chirp. Two calls. -/
def queryPlan (i j : Fin A) : QPlan A 1 1 :=
  .seq (chirp i j) (.seq (.child i) (.seq (.child j) (.seq (swapPlan i j) (chirp i j))))

theorem queryPlan_calls (i j : Fin A) : (queryPlan i j).calls = 2 := by
  simp only [queryPlan, chirp, Fin.isValue, swapPlan, QPlan.calls, add_zero, Nat.reduceAdd, zero_add]

theorem queryPlan_oneRow {h : ℕ} {i j : Fin A} (hij : i ≠ j) :
    OneRow ((queryPlan i j).eval h) (walshCol A * diagonal (qc i j) * walshCol A) := by
  have := (chirp_oneRow (h := h) i j).mul ((child_oneRow (h := h) i).mul
    ((child_oneRow (h := h) j).mul ((swapPlan_oneRow (h := h) i j).mul (chirp_oneRow i j))))
  have hU : axisMat i * axisMat j
      = piMat (Function.update (Function.update (fun _ => 1) i pairMat) j pairMat) := by
    rw [axisMat, axisMat, piMat_mul]; congr 1; funext a
    by_cases ha : a = j
    · subst ha; simp only [Function.update_of_ne (Ne.symm hij), Function.update_self, one_mul]
    · by_cases hb : a = i
      · subst hb; simp only [Function.update_self, Function.update_of_ne ha, mul_one]
      · simp only [Function.update_of_ne hb, Function.update_of_ne ha, mul_one]
  show OneRow ((chirp i j).eval h * ((QPlan.child i).eval h * ((QPlan.child j).eval h *
    ((swapPlan i j).eval h * (chirp i j).eval h)))) _
  rw [query_col hij]
  simp only [← Matrix.mul_assoc] at this ⊢
  rw [Matrix.mul_assoc (diagonal _) (axisMat _) (axisMat _), hU] at this
  exact this

end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.Query =====

-- ===== begin KP.Spec =====
section
/-! # The plan-level spectral interface (every combinator lands here)

`Wh` is the column Walsh transform on an address, `Kw` applies it on every row (`Kw_sq`).
`Fdr F` is frequency-diagonal (frequency `x` carries the matrix `F x`), and
`specR F = Kw · Fdr F · Kw`. Every plan combinator in KP is stated as `eval h = specR F`; they
compose by `specR_mul`.
`specR_const`: any column-independent move is `specR` of a constant (`qmix_specR` in KP.QPlan).
`rowBank` (one plan per row) is the basic bank of plans. -/

namespace OAI.Computability.NearSquareRoot.KernelPass
open Matrix Finset

variable {A : ℕ}

/-- Independent one-row plans, one per row. -/
def rowBank : (W : ℕ) → (Fin W → QPlan A 1 1) → QPlan A W W
  | 0, _ => .mix fun i => i.elim0
  | n + 1, p => .parallel (rowBank n fun r => p r.castSucc) (p (Fin.last n))

theorem rowBank_calls : ∀ (W : ℕ) (p : Fin W → QPlan A 1 1), (rowBank W p).calls = ∑ r, (p r).calls
  | 0, _ => by rw [Fin.sum_univ_zero]; rfl
  | n + 1, p => by
    rw [rowBank, QPlan.calls, rowBank_calls n, Fin.sum_univ_castSucc]

theorem rowBank_apply {h : ℕ} : ∀ (W : ℕ) (p : Fin W → QPlan A 1 1) (b a : Fin W) (y x : Addr A h),
    (rowBank W p).eval h (b, y) (a, x) = if a = b then (p b).eval h (0, y) (0, x) else 0
  | 0, _, b, _, _, _ => b.elim0
  | n + 1, p, b, a, y, x => by
    have ih := rowBank_apply (h := h) n (fun r => p r.castSucc)
    simp only [rowBank, QPlan.eval]
    refine Fin.addCases (fun b => ?_) (fun b => ?_) b <;>
      refine Fin.addCases (fun a => ?_) (fun a => ?_) a
    · rw [directSum_ll, ih]
      simp only [Fin.ext_iff, Fin.isValue, Fin.val_castAdd]; rfl
    · rw [directSum_lr, if_neg]; intro e; have := congrArg Fin.val e; simp only [Fin.val_natAdd, Fin.val_eq_zero, add_zero, Fin.val_castAdd] at this; omega
    · rw [directSum_rl, if_neg]; intro e; have := congrArg Fin.val e; simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.val_eq_zero, add_zero] at this; omega
    · rw [directSum_rr]
      have hb : (Fin.natAdd n b : Fin (n + 1)) = Fin.last n := by
        ext; simp only [Subsingleton.elim b 0, Fin.isValue, Fin.val_natAdd, Fin.val_eq_zero, add_zero, Fin.val_last]
      rw [Subsingleton.elim a b, if_pos rfl, hb, Subsingleton.elim b 0]

theorem walshCol_sq : walshCol A * walshCol A = 1 := by
  rw [walshCol, piMat_mul]; simp only [pair_sq]; exact piMat_one

/-- The column Walsh transform on a whole address. -/
def Wh (A h : ℕ) : Matrix (Addr A h) (Addr A h) ℚ := piMat fun _ : Fin h => walshCol A

theorem Wh_sq (A h : ℕ) : Wh A h * Wh A h = 1 := by
  rw [Wh, piMat_mul]; simp only [walshCol_sq]; exact piMat_one

/-- `Wh` on every one of `W` rows. -/
def Kw (A h W : ℕ) : RowMatrix A h W W := fun p q => if q.1 = p.1 then Wh A h p.2 q.2 else 0

/-- Rectangular frequency-diagonal matrices. -/
def Fdr {h o i : ℕ} (F : Addr A h → Matrix (Fin o) (Fin i) ℚ) :
    Matrix (Fin o × Addr A h) (Fin i × Addr A h) ℚ :=
  fun p q => if p.2 = q.2 then F q.2 p.1 q.1 else 0

def specR {h o i : ℕ} (F : Addr A h → Matrix (Fin o) (Fin i) ℚ) : RowMatrix A h i o :=
  Kw A h o * Fdr F * Kw A h i

theorem Kw_sq (A h W : ℕ) : Kw A h W * Kw A h W = 1 := by
  ext ⟨b, y⟩ ⟨a, x⟩
  have hW := congrFun (congrFun (Wh_sq A h) y) x
  rw [mul_apply] at hW
  rw [mul_apply, Fintype.sum_prod_type,
    Finset.sum_eq_single b (fun c _ hc => by simp only [Kw, hc, ↓reduceIte, mul_ite, zero_mul, mul_zero, ite_self, sum_const_zero]) (fun h => absurd (mem_univ _) h)]
  by_cases hab : a = b
  · subst hab; simp only [Kw, if_true]; rw [hW]; simp only [one_apply, Prod.mk.injEq, true_and]
  · simp only [Kw, ↓reduceIte, hab, mul_zero, sum_const_zero, one_apply, Prod.mk.injEq, Ne.symm hab, false_and]

theorem Fdr_mul {h o j i : ℕ} (F : Addr A h → Matrix (Fin o) (Fin j) ℚ)
    (G : Addr A h → Matrix (Fin j) (Fin i) ℚ) : Fdr F * Fdr G = Fdr fun x => F x * G x := by
  ext ⟨b, y⟩ ⟨a, x⟩
  rw [mul_apply, Fintype.sum_prod_type, Finset.sum_comm,
    Finset.sum_eq_single x (fun z _ hz => by simp only [Fdr, hz, ↓reduceIte, mul_zero, sum_const_zero]) (fun h => absurd (mem_univ _) h)]
  by_cases hyx : y = x
  · subst hyx; simp only [Fdr, ↓reduceIte, Matrix.mul_apply]
  · simp only [Fdr, hyx, ↓reduceIte, zero_mul, sum_const_zero]

theorem specR_mul {h o j i : ℕ} (F : Addr A h → Matrix (Fin o) (Fin j) ℚ)
    (G : Addr A h → Matrix (Fin j) (Fin i) ℚ) : specR F * specR G = specR fun x => F x * G x := by
  simp only [specR, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Kw A h j) (Kw A h j), Kw_sq, Matrix.one_mul, ← Matrix.mul_assoc (Fdr F),
    Fdr_mul]

/-- A column-independent row matrix `[x = y] · M b a` is `specR` of the constant `M`. -/
theorem specR_const {h o i : ℕ} (M : Matrix (Fin o) (Fin i) ℚ) (E : RowMatrix A h i o)
    (hE : ∀ b a y x, E (b, y) (a, x) = if x = y then M b a else 0) : E = specR fun _ => M := by
  have hc : Kw A h o * Fdr (fun _ => M) = Fdr (fun _ => M) * Kw A h i := by
    ext ⟨b, y⟩ ⟨a, x⟩
    rw [mul_apply, mul_apply, Fintype.sum_prod_type, Fintype.sum_prod_type,
      Finset.sum_eq_single b (fun c _ hc => by simp only [Kw, hc, ↓reduceIte, zero_mul, sum_const_zero]) (fun h => absurd (mem_univ _) h),
      Finset.sum_eq_single a (fun c _ hc => by simp only [Kw, Ne.symm hc, ↓reduceIte, mul_zero, sum_const_zero]) (fun h => absurd (mem_univ _) h)]
    simp only [Kw, Fdr, if_true, mul_ite, mul_zero, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq', Finset.sum_ite_eq]; simp only [mem_univ, ↓reduceIte, mul_comm]
  rw [specR, hc, Matrix.mul_assoc, Kw_sq, Matrix.mul_one]
  ext ⟨b, y⟩ ⟨a, x⟩
  rw [hE]; simp only [Fdr]; by_cases hxy : x = y
  · simp only [hxy, ↓reduceIte]
  · simp only [hxy, ↓reduceIte, Ne.symm hxy]

theorem spec_apply {h W : ℕ} (F : Addr A h → Matrix (Fin W) (Fin W) ℚ) (b a : Fin W)
    (y x : Addr A h) : specR F (b, y) (a, x) = ∑ z, Wh A h y z * F z b a * Wh A h z x := by
  simp only [specR, mul_apply, Fintype.sum_prod_type, Kw, Fdr, ite_mul, zero_mul, mul_ite, mul_zero,
    sum_ite_eq', sum_ite_eq, mem_univ, if_true, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [sum_ite_eq, mem_univ, ↓reduceIte]

end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.Spec =====

-- ===== begin KP.QPlan =====
section
/-! # Rational mixes in spectral form -/

namespace OAI.Computability.NearSquareRoot.KernelPass
open Matrix Finset

variable {A : ℕ}

/-- A rational mix is `specR` of a constant. -/
theorem qmix_specR {h i o : ℕ} (M : Matrix (Fin o) (Fin i) ℚ) :
    (QPlan.mix (A := A) M).eval h = specR fun _ => M :=
  specR_const M _ fun _ _ _ _ => eval_mix_apply M _ _ _ _

end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.QPlan =====

-- ===== begin KP.Small =====
section
/-! # Small shared definitions

The count of a 0/1 vector, digits from
signs, `(-1)^cnt = ∏ σ_j s_j`, and the fan matrices for sums and for pairwise routing. -/

namespace OAI.Computability.NearSquareRoot.KernelPass
open Matrix Finset

variable {m n : ℕ}

/-- The count of a `0/1` vector. -/
def cnt (x : Fin m → ℚ) : ℕ := (univ.filter fun j => x j = 1).card

/-- Digits from signs: `x_j = (1 - σ_j s_j)/2`. -/
def xs (σ s : Fin m → ℚ) : Fin m → ℚ := fun j => (1 - σ j * s j) / 2

lemma neg_one_pow_cnt {m : ℕ} {σ s : Fin m → ℚ} (hσ : ∀ j, σ j = 1 ∨ σ j = -1)
    (hs : ∀ j, s j = 1 ∨ s j = -1) : (-1 : ℚ) ^ cnt (xs σ s) = ∏ j, σ j * s j := by
  have : ∀ j, σ j * s j = if xs σ s j = 1 then -1 else 1 := by
    intro j; unfold xs
    rcases hσ j with h1 | h1 <;> rcases hs j with h2 | h2 <;> rw [h1, h2] <;> norm_num
  rw [Finset.prod_congr rfl fun j _ => this j, Finset.prod_ite, Finset.prod_const_one, mul_one,
    Finset.prod_const, cnt]

/-- Fan matrices for sums. -/
def sumIn (W : ℕ) (a b : ℚ) : Matrix (Fin (W + W)) (Fin W) ℚ :=
  fun r c => Fin.addCases (fun l => if l = c then a else 0) (fun l => if l = c then b else 0) r

def sumOut (W : ℕ) : Matrix (Fin W) (Fin (W + W)) ℚ :=
  fun c r => Fin.addCases (fun l => if c = l then 1 else 0) (fun l => if c = l then 1 else 0) r

def fanO (n : ℕ) : Matrix (Fin (n * n)) (Fin n) ℚ :=
  fun r s => if (finProdFinEquiv.symm r).2 = s then 1 else 0

def fanI (c : Fin n → Fin n → ℚ) : Matrix (Fin n) (Fin (n * n)) ℚ :=
  fun t r => if (finProdFinEquiv.symm r).1 = t then c t (finProdFinEquiv.symm r).2 else 0

end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.Small =====

-- ===== begin KP.QRouting =====
section
/-! # Routing over rational plans

The rectangle stage for `QPlan`, with rational weights.

* `QCharged`: a charged rectangle. Per query `j`: call-free per-label `inp j`, `out j`, and one
  common plan `com j` run once for the whole rectangle.
* `QFree`: a free rectangle. Per-label `src`, `tgt` (these carry the calls, once per incident
  label, for all queries together) and a call-free middle `mid j t s` per query and label pair.
* `routed`: the stage of a family of charged and free rectangles, with a coefficient `a t j`
  per target row and query.
* **`routed_eval`**: if every rectangle factors the kernels `H j t s` on its pairs and the
  rectangle weights sum to the identity on rows, then the stage is row-diagonal with block
  `Σ_j a t j • H j t t`.
* **`routed_calls`**: `calls ≤ d * (2 * n * inc + |J| * |C|)`.

Rows are any `Fin n`; for shift rows take rows = label × shift row and one copy of every
rectangle per shift row. The statement shape follows OpenAI's `block_pencil` and
`calls_pencil_le` (KernelPassRectBank / KernelPassRectBudget); the proofs are this tree's. -/

namespace OAI.Computability.NearSquareRoot.KernelPass
open Matrix Finset

variable {A : ℕ}

/-! ## Mixes, banks, blocks -/

theorem qeval_seq {h i j o : ℕ} (p : QPlan A j o) (q : QPlan A i j) :
    (QPlan.seq p q).eval h = p.eval h * q.eval h := rfl

theorem qmix_mul_apply {h i o k : ℕ} (M : Matrix (Fin o) (Fin i) ℚ) (X : RowMatrix A h k i)
    (b : Fin o) (y : Addr A h) (q : Fin k × Addr A h) :
    ((QPlan.mix (A := A) M).eval h * X) (b, y) q = ∑ c, M b c * X (c, y) q := by
  rw [mul_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [eval_mix_apply, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ y]; simp

theorem mul_qmix_apply {h i o k : ℕ} (M : Matrix (Fin o) (Fin i) ℚ) (X : RowMatrix A h o k)
    (p : Fin k × Addr A h) (a : Fin i) (x : Addr A h) :
    (X * (QPlan.mix (A := A) M).eval h) p (a, x) = ∑ c, X p (c, x) * M c a := by
  rw [mul_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [eval_mix_apply, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ x]; simp

/-- The block of a one-row rational plan. -/
def qBlk (h : ℕ) (P : QPlan A 1 1) : Matrix (Addr A h) (Addr A h) ℚ := fun y x => P.eval h (0, y) (0, x)

theorem rowBank_mul_apply {h n k : ℕ} (p : Fin n → QPlan A 1 1) (X : RowMatrix A h k n)
    (b : Fin n) (y : Addr A h) (q : Fin k × Addr A h) :
    ((rowBank n p).eval h * X) (b, y) q = ∑ y', qBlk h (p b) y y' * X (b, y') q := by
  rw [mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single b]
  · refine Finset.sum_congr rfl fun y' _ => ?_
    rw [rowBank_apply, if_pos rfl]; rfl
  · intro c _ hc
    refine Finset.sum_eq_zero fun y' _ => ?_
    rw [rowBank_apply, if_neg hc, zero_mul]
  · exact fun hu => absurd (Finset.mem_univ _) hu

theorem mul_rowBank_apply {h n k : ℕ} (p : Fin n → QPlan A 1 1) (X : RowMatrix A h n k)
    (q : Fin k × Addr A h) (a : Fin n) (x : Addr A h) :
    (X * (rowBank n p).eval h) q (a, x) = ∑ x', X q (a, x') * qBlk h (p a) x' x := by
  rw [mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single a]
  · refine Finset.sum_congr rfl fun x' _ => ?_
    rw [rowBank_apply, if_pos rfl]; rfl
  · intro c _ hc
    refine Finset.sum_eq_zero fun x' _ => ?_
    rw [rowBank_apply, if_neg (Ne.symm hc), mul_zero]
  · exact fun hu => absurd (Finset.mem_univ _) hu

theorem qBlk_qId (h : ℕ) : qBlk h (idPlan A) = 1 := by
  ext y x
  simp only [qBlk, idPlan, eval_mix_apply, one_apply]
  by_cases hyx : x = y
  · subst hyx; simp
  · simp [hyx, Ne.symm hyx]

/-! ## Sums of plans -/

variable {n : ℕ}

/-- `a • P + b • Q` for rational plans. -/
def qadd (a b : ℚ) (P Q : QPlan A n n) : QPlan A n n :=
  .seq (.mix (sumOut n)) (.seq (.parallel P Q) (.mix (sumIn n a b)))

theorem qadd_calls (a b : ℚ) (P Q : QPlan A n n) : (qadd a b P Q).calls = P.calls + Q.calls := by
  show 0 + ((P.calls + Q.calls) + 0) = _
  rw [zero_add, add_zero]

theorem qadd_eval {h : ℕ} (a b : ℚ) (P Q : QPlan A n n) :
    (qadd a b P Q).eval h = a • P.eval h + b • Q.eval h := by
  ext ⟨r, y⟩ ⟨c, x⟩
  simp only [qadd, qeval_seq]
  rw [qmix_mul_apply]
  simp only [mul_qmix_apply, Fin.sum_univ_add]
  simp only [QPlan.eval, directSum_ll, directSum_lr, directSum_rl, directSum_rr, sumOut, sumIn, Fin.addCases_left, Fin.addCases_right, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, ite_mul, one_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero, add_zero, zero_add]
  ring

def qZero (n : ℕ) : QPlan A n n := .mix 0

theorem qZero_eval {h : ℕ} : (qZero (A := A) n).eval h = 0 := by
  ext ⟨b, y⟩ ⟨a, x⟩; simp [qZero, eval_mix_apply]

def qSumL : List (QPlan A n n) → QPlan A n n
  | [] => qZero n
  | p :: ps => qadd 1 1 p (qSumL ps)

theorem qSumL_eval {h : ℕ} : ∀ l : List (QPlan A n n), (qSumL l).eval h = (l.map fun p => p.eval h).sum
  | [] => qZero_eval
  | p :: ps => by rw [qSumL, qadd_eval, qSumL_eval ps]; simp

theorem qSumL_calls : ∀ l : List (QPlan A n n), (qSumL l).calls = (l.map QPlan.calls).sum
  | [] => rfl
  | p :: ps => by rw [qSumL, qadd_calls, qSumL_calls ps]; simp

/-- The sum of a finite family of rational plans. -/
noncomputable def qSumF {ι : Type*} [Fintype ι] (P : ι → QPlan A n n) : QPlan A n n :=
  qSumL ((Finset.univ : Finset ι).toList.map P)

theorem qSumF_calls {ι : Type*} [Fintype ι] (P : ι → QPlan A n n) :
    (qSumF P).calls = ∑ k, (P k).calls := by
  rw [qSumF, qSumL_calls, List.map_map, Finset.sum_map_toList]; rfl

theorem qSumF_eval {ι : Type*} [Fintype ι] (h : ℕ) (P : ι → QPlan A n n) :
    (qSumF P).eval h = ∑ k, (P k).eval h := by
  rw [qSumF, qSumL_eval, List.map_map, Finset.sum_map_toList]; rfl

/-- A scalar multiple of a one-row plan. -/
def qSmul (a : ℚ) (P : QPlan A 1 1) : QPlan A 1 1 := .seq (.mix (a • 1)) P

theorem qSmul_calls (a : ℚ) (P : QPlan A 1 1) : (qSmul a P).calls = P.calls := by
  show 0 + P.calls = _
  rw [zero_add]

theorem qBlk_qSmul (h : ℕ) (a : ℚ) (P : QPlan A 1 1) : qBlk h (qSmul a P) = a • qBlk h P := by
  ext y x
  simp only [qBlk, qSmul, qeval_seq]
  rw [qmix_mul_apply]
  simp [Matrix.smul_apply]
  exact Or.inl rfl

/-- `Σ_j a j • P j` on one row. -/
noncomputable def qLin {J : Type*} [Fintype J] (a : J → ℚ) (P : J → QPlan A 1 1) : QPlan A 1 1 :=
  qSumF fun j => qSmul (a j) (P j)

theorem qLin_calls {J : Type*} [Fintype J] (a : J → ℚ) (P : J → QPlan A 1 1) :
    (qLin a P).calls = ∑ j, (P j).calls := by
  rw [qLin, qSumF_calls]; exact Finset.sum_congr rfl fun j _ => qSmul_calls _ _

theorem qBlk_qLin {J : Type*} [Fintype J] (h : ℕ) (a : J → ℚ) (P : J → QPlan A 1 1) :
    qBlk h (qLin a P) = ∑ j, a j • qBlk h (P j) := by
  ext y x
  simp only [qBlk, qLin, qSumF_eval, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := congrFun (congrFun (qBlk_qSmul h (a j) (P j)) y) x
  simpa [qBlk] using this

/-! ## The two kinds of rectangle plan -/

/-- Run `p r` on the rows of `S`, leave the other rows alone. -/
def qSide (S : Finset (Fin n)) (p : Fin n → QPlan A 1 1) : QPlan A n n :=
  rowBank n fun r => if r ∈ S then p r else idPlan _

theorem qSide_calls (S : Finset (Fin n)) (p : Fin n → QPlan A 1 1) :
    (qSide S p).calls = ∑ r ∈ S, (p r).calls := by
  rw [qSide, rowBank_calls]
  have e : ∀ r, (if r ∈ S then p r else idPlan _).calls = if r ∈ S then (p r).calls else 0 :=
    fun r => by split_ifs <;> rfl
  simp only [e]
  rw [← Finset.sum_filter]
  congr 1; ext r; simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- Source side, core, target side. -/
def qSandwich (S T : Finset (Fin n)) (src tgt : Fin n → QPlan A 1 1) (core : QPlan A n n) :
    QPlan A n n := .seq (qSide T tgt) (.seq core (qSide S src))

theorem qSandwich_calls (S T : Finset (Fin n)) (src tgt : Fin n → QPlan A 1 1) (core : QPlan A n n) :
    (qSandwich S T src tgt core).calls =
      ∑ t ∈ T, (tgt t).calls + core.calls + ∑ s ∈ S, (src s).calls := by
  simp only [qSandwich, QPlan.calls, qSide_calls]; ring

/-- Entry of a sandwich when both rows are on their sides. -/
theorem qSandwich_eval (h : ℕ) (S T : Finset (Fin n)) (src tgt : Fin n → QPlan A 1 1)
    (core : QPlan A n n) (t s : Fin n) (ht : t ∈ T) (hs : s ∈ S) (y x : Addr A h) :
    (qSandwich S T src tgt core).eval h (t, y) (s, x) =
      ∑ y', ∑ x', qBlk h (tgt t) y y' * core.eval h (t, y') (s, x') * qBlk h (src s) x' x := by
  simp only [qSandwich, qeval_seq, qSide]
  rw [rowBank_mul_apply, if_pos ht]
  refine Finset.sum_congr rfl fun y' _ => ?_
  rw [mul_rowBank_apply, if_pos hs, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x' _ => by ring

/-- Entry of a sandwich whose core vanishes between the two rows. -/
theorem qSandwich_eval_zero (h : ℕ) (S T : Finset (Fin n)) (src tgt : Fin n → QPlan A 1 1)
    (core : QPlan A n n) (t s : Fin n) (h0 : ∀ y' x', core.eval h (t, y') (s, x') = 0)
    (y x : Addr A h) : (qSandwich S T src tgt core).eval h (t, y) (s, x) = 0 := by
  simp only [qSandwich, qeval_seq, qSide]
  rw [rowBank_mul_apply]
  refine Finset.sum_eq_zero fun y' _ => ?_
  rw [mul_rowBank_apply]
  simp [h0]

/-- Gather the rows of `S`, run `com` once, scatter to the rows of `T` with weights `hamming`. -/
def qShare (S T : Finset (Fin n)) (hamming : Fin n → ℚ) (com : QPlan A 1 1) : QPlan A n n :=
  .seq (.mix (Matrix.of fun t _ => if t ∈ T then hamming t else 0))
    (.seq com (.mix (Matrix.of fun _ s => if s ∈ S then 1 else 0)))

theorem qShare_calls (S T : Finset (Fin n)) (hamming : Fin n → ℚ) (com : QPlan A 1 1) :
    (qShare S T hamming com).calls = com.calls := by
  show 0 + (com.calls + 0) = _
  rw [zero_add, add_zero]

theorem qShare_eval (h : ℕ) (S T : Finset (Fin n)) (hamming : Fin n → ℚ) (com : QPlan A 1 1)
    (t s : Fin n) (y x : Addr A h) :
    (qShare S T hamming com).eval h (t, y) (s, x) =
      if t ∈ T ∧ s ∈ S then hamming t * qBlk h com y x else 0 := by
  simp only [qShare, qeval_seq]
  rw [qmix_mul_apply, Fin.sum_univ_one, mul_qmix_apply, Fin.sum_univ_one]
  by_cases ht : t ∈ T <;> by_cases hs : s ∈ S <;> simp [ht, hs, qBlk]

/-- Route `c t s • (mdl t s)` from every row `s` to every row `t`. -/
def qPair (c : Fin n → Fin n → ℚ) (mdl : Fin n → Fin n → QPlan A 1 1) : QPlan A n n :=
  .seq (.mix (fanI c))
    (.seq (rowBank (n * n) fun r => mdl (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm r).2)
      (.mix (fanO n)))

theorem qPair_calls (c : Fin n → Fin n → ℚ) (mdl : Fin n → Fin n → QPlan A 1 1) :
    (qPair c mdl).calls = ∑ t, ∑ s, (mdl t s).calls := by
  simp only [qPair, QPlan.calls, rowBank_calls, zero_add, add_zero]
  rw [← Fintype.sum_prod_type', ← Equiv.sum_comp finProdFinEquiv]
  simp only [Equiv.symm_apply_apply]

theorem qPair_eval (h : ℕ) (c : Fin n → Fin n → ℚ) (mdl : Fin n → Fin n → QPlan A 1 1)
    (t s : Fin n) (y x : Addr A h) :
    (qPair c mdl).eval h (t, y) (s, x) = c t s * qBlk h (mdl t s) y x := by
  simp only [qPair, qeval_seq]
  rw [qmix_mul_apply, ← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type,
    Finset.sum_eq_single t, Finset.sum_eq_single s]
  · rw [mul_qmix_apply, Finset.sum_eq_single (finProdFinEquiv (t, s))]
    · rw [rowBank_apply, if_pos rfl]
      simp only [fanI, fanO, Equiv.symm_apply_apply, ↓reduceIte, mul_one, qBlk]
    · intro r _ hr; rw [rowBank_apply, if_neg hr, zero_mul]
    · simp only [mem_univ, not_true_eq_false, finProdFinEquiv_symm_apply, mul_eq_zero, IsEmpty.forall_iff]
  · intro s' _ hs'
    rw [mul_qmix_apply, Finset.sum_eq_single (finProdFinEquiv (t, s'))]
    · simp [fanO, hs']
    · intro r _ hr; rw [rowBank_apply, if_neg hr, zero_mul]
    · exact fun hu => absurd (Finset.mem_univ _) hu
  · exact fun hu => absurd (Finset.mem_univ _) hu
  · intro t' _ ht'
    refine Finset.sum_eq_zero fun s' _ => ?_
    simp [fanI, ht']
  · exact fun hu => absurd (Finset.mem_univ _) hu

/-! ## Rectangles and the routed stage -/

/-- A charged rectangle on `n` rows for queries `J`. -/
structure QCharged (A n : ℕ) (J : Type*) where
  S : Finset (Fin n)
  T : Finset (Fin n)
  w : ℚ
  inp : J → Fin n → QPlan A 1 1
  out : J → Fin n → QPlan A 1 1
  com : J → QPlan A 1 1

/-- A free rectangle on `n` rows for queries `J`. -/
structure QFree (A n : ℕ) (J : Type*) where
  S : Finset (Fin n)
  T : Finset (Fin n)
  w : ℚ
  src : Fin n → QPlan A 1 1
  tgt : Fin n → QPlan A 1 1
  mid : J → Fin n → Fin n → QPlan A 1 1

variable {J : Type*} [Fintype J]

/-- The plan of a charged rectangle for one query. -/
def QCharged.plan (r : QCharged A n J) (a : Fin n → J → ℚ) (j : J) : QPlan A n n :=
  qSandwich r.S r.T (r.inp j) (r.out j) (qShare r.S r.T (fun t => r.w * a t j) (r.com j))

/-- The plan of a free rectangle for all queries. -/
noncomputable def QFree.plan (r : QFree A n J) (a : Fin n → J → ℚ) : QPlan A n n :=
  qSandwich r.S r.T r.src r.tgt
    (qPair (fun t s => if t ∈ r.T ∧ s ∈ r.S then r.w else 0)
      (fun t s => qLin (a t) fun j => r.mid j t s))

omit [Fintype J] in
theorem QCharged.plan_eval (h : ℕ) (r : QCharged A n J) (a : Fin n → J → ℚ) (j : J)
    (K : Fin n → Fin n → Matrix (Addr A h) (Addr A h) ℚ)
    (hK : ∀ t s, t ∈ r.T → s ∈ r.S →
      qBlk h (r.out j t) * qBlk h (r.com j) * qBlk h (r.inp j s) = K t s)
    (t s : Fin n) (y x : Addr A h) :
    (r.plan a j).eval h (t, y) (s, x) =
      (if t ∈ r.T ∧ s ∈ r.S then r.w else 0) * (a t j * K t s y x) := by
  by_cases hts : t ∈ r.T ∧ s ∈ r.S
  · rw [QCharged.plan, qSandwich_eval h _ _ _ _ _ t s hts.1 hts.2, if_pos hts, ← hK t s hts.1 hts.2]
    simp only [qShare_eval, if_pos hts]
    rw [mul_apply]
    simp only [mul_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun y' _ => by ring
  · rw [if_neg hts, zero_mul]
    exact qSandwich_eval_zero h _ _ _ _ _ t s (fun y' x' => by rw [qShare_eval, if_neg hts]) y x

theorem QFree.plan_eval (h : ℕ) (r : QFree A n J) (a : Fin n → J → ℚ)
    (H : J → Fin n → Fin n → Matrix (Addr A h) (Addr A h) ℚ)
    (hH : ∀ j t s, t ∈ r.T → s ∈ r.S →
      qBlk h (r.tgt t) * qBlk h (r.mid j t s) * qBlk h (r.src s) = H j t s)
    (t s : Fin n) (y x : Addr A h) :
    (r.plan a).eval h (t, y) (s, x) =
      (if t ∈ r.T ∧ s ∈ r.S then r.w else 0) * (∑ j, a t j • H j t s) y x := by
  by_cases hts : t ∈ r.T ∧ s ∈ r.S
  · rw [QFree.plan, qSandwich_eval h _ _ _ _ _ t s hts.1 hts.2, if_pos hts]
    simp only [qPair_eval, if_pos hts, qBlk_qLin]
    have e : (∑ j, a t j • H j t s) =
        qBlk h (r.tgt t) * (∑ j, a t j • qBlk h (r.mid j t s)) * qBlk h (r.src s) := by
      rw [Matrix.mul_sum, Matrix.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.mul_smul, Matrix.smul_mul, hH j t s hts.1 hts.2]
    rw [e, mul_apply]
    simp only [mul_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun y' _ => by ring
  · rw [if_neg hts, zero_mul]
    exact qSandwich_eval_zero h _ _ _ _ _ t s (fun y' x' => by rw [qPair_eval, if_neg hts, zero_mul]) y x

variable {C F : Type*} [Fintype C] [Fintype F]

/-- The routed stage: every charged rectangle once per query, every free rectangle once. -/
noncomputable def routed (ch : C → QCharged A n J) (fr : F → QFree A n J) (a : Fin n → J → ℚ) :
    QPlan A n n :=
  qadd 1 1 (qSumF fun p : C × J => (ch p.1).plan a p.2) (qSumF fun f => (fr f).plan a)

/-- **Routed stage, correctness.** -/
theorem routed_eval (h : ℕ) (ch : C → QCharged A n J) (fr : F → QFree A n J) (a : Fin n → J → ℚ)
    (H : J → Fin n → Fin n → Matrix (Addr A h) (Addr A h) ℚ)
    (hch : ∀ c j t s, t ∈ (ch c).T → s ∈ (ch c).S →
      qBlk h ((ch c).out j t) * qBlk h ((ch c).com j) * qBlk h ((ch c).inp j s) = H j t s)
    (hfr : ∀ f j t s, t ∈ (fr f).T → s ∈ (fr f).S →
      qBlk h ((fr f).tgt t) * qBlk h ((fr f).mid j t s) * qBlk h ((fr f).src s) = H j t s)
    (hId : ∀ t s, (∑ c, if t ∈ (ch c).T ∧ s ∈ (ch c).S then (ch c).w else 0) +
      (∑ f, if t ∈ (fr f).T ∧ s ∈ (fr f).S then (fr f).w else 0) = if s = t then 1 else 0)
    (t s : Fin n) (y x : Addr A h) :
    (routed ch fr a).eval h (t, y) (s, x) = if s = t then (∑ j, a t j • H j t t) y x else 0 := by
  rw [routed, qadd_eval, one_smul, one_smul, qSumF_eval, qSumF_eval, Matrix.add_apply, Matrix.sum_apply, Matrix.sum_apply,
    Fintype.sum_prod_type]
  have e1 : (∑ c, ∑ j, ((ch c).plan a j).eval h (t, y) (s, x)) =
      (∑ c, if t ∈ (ch c).T ∧ s ∈ (ch c).S then (ch c).w else 0) * (∑ j, a t j • H j t s) y x := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [(ch c).plan_eval h a j (H j) (hch c j) t s y x, Matrix.smul_apply, smul_eq_mul]
  have e2 : (∑ f, ((fr f).plan a).eval h (t, y) (s, x)) =
      (∑ f, if t ∈ (fr f).T ∧ s ∈ (fr f).S then (fr f).w else 0) * (∑ j, a t j • H j t s) y x := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun f _ => (fr f).plan_eval h a H (hfr f) t s y x
  rw [e1, e2, ← add_mul, hId]
  by_cases hst : s = t
  · subst hst; rw [if_pos rfl, if_pos rfl, one_mul]
  · rw [if_neg hst, if_neg hst, zero_mul]

/-- **Routed stage, calls.** -/
theorem routed_calls (ch : C → QCharged A n J) (fr : F → QFree A n J) (a : Fin n → J → ℚ)
    (d inc : ℕ)
    (hci : ∀ c j s, ((ch c).inp j s).calls = 0) (hco : ∀ c j t, ((ch c).out j t).calls = 0)
    (hcc : ∀ c j, ((ch c).com j).calls ≤ d)
    (hfm : ∀ f j t s, ((fr f).mid j t s).calls = 0)
    (hfs : ∀ f s, ((fr f).src s).calls ≤ d) (hft : ∀ f t, ((fr f).tgt t).calls ≤ d)
    (hincS : ∀ s, (Finset.univ.filter fun f => s ∈ (fr f).S).card ≤ inc)
    (hincT : ∀ t, (Finset.univ.filter fun f => t ∈ (fr f).T).card ≤ inc) :
    (routed ch fr a).calls ≤ d * (2 * n * inc + Fintype.card J * Fintype.card C) := by
  rw [routed, qadd_calls, qSumF_calls, qSumF_calls]
  have side_le : ∀ (sd : F → Finset (Fin n)) (wk : F → Fin n → ℕ), (∀ f r, wk f r ≤ d) →
      (∀ r, (Finset.univ.filter fun f => r ∈ sd f).card ≤ inc) →
      (∑ f, ∑ r ∈ sd f, wk f r) ≤ d * (n * inc) := by
    intro sd wk hwk hi
    calc (∑ f, ∑ r ∈ sd f, wk f r) ≤ ∑ f, ∑ r ∈ sd f, d :=
          Finset.sum_le_sum fun f _ => Finset.sum_le_sum fun r _ => hwk f r
      _ = ∑ r : Fin n, ∑ f, if r ∈ sd f then d else 0 := by
          rw [Finset.sum_comm]; simp only [sum_const, smul_eq_mul, sum_ite_mem, univ_inter]
      _ ≤ ∑ _r : Fin n, d * inc := Finset.sum_le_sum fun r _ => by
          rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
          exact Nat.mul_le_mul_left d (hi r)
      _ = d * (n * inc) := by
          simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]; ring
  have hC : (∑ p : C × J, ((ch p.1).plan a p.2).calls) ≤ d * (Fintype.card J * Fintype.card C) := by
    calc (∑ p : C × J, ((ch p.1).plan a p.2).calls) ≤ ∑ _p : C × J, d :=
          Finset.sum_le_sum fun p _ => by
            simp only [QCharged.plan, qSandwich_calls, qShare_calls, hci, hco, Finset.sum_const_zero,
              zero_add, add_zero]
            exact hcc p.1 p.2
      _ = d * (Fintype.card J * Fintype.card C) := by
          simp only [sum_const, card_univ, Fintype.card_prod, smul_eq_mul]; ring
  have hF : (∑ f, ((fr f).plan a).calls) ≤ d * (n * inc) + d * (n * inc) := by
    have e : ∀ f, ((fr f).plan a).calls =
        ∑ t ∈ (fr f).T, ((fr f).tgt t).calls + ∑ s ∈ (fr f).S, ((fr f).src s).calls := by
      intro f
      simp only [QFree.plan, qSandwich_calls, qPair_calls, qLin_calls, hfm, sum_const_zero, add_zero, Nat.add_left_cancel_iff]
    simp only [e]
    rw [Finset.sum_add_distrib]
    exact Nat.add_le_add (side_le (fun f => (fr f).T) (fun f t => ((fr f).tgt t).calls) hft hincT)
      (side_le (fun f => (fr f).S) (fun f s => ((fr f).src s).calls) hfs hincS)
  calc _ ≤ d * (Fintype.card J * Fintype.card C) + (d * (n * inc) + d * (n * inc)) :=
        Nat.add_le_add hC hF
    _ = _ := by ring

end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.QRouting =====

-- ===== begin KP.Letter =====
section
/-! # Letters: the shared interface for the label-kernel parts

An axis carries two bits; a *letter* is one bit of every axis (`Bits A`). Every move of the
label kernel acts the same way on both letters of a column and on every column. Letter
matrices are kept *unnormalized* (entries `0, ±1`), because the one-bit Walsh matrix has the
irrational factor `1/√2`; the normalization is a power of `1/2` per column.
`Implements p M n` says: at every width `h`, the one-row rational plan `p` has block
`(1/2)^(n*h) • lift h M` (`n` = number of Walsh bits per letter).

The charged and free factorizations (KP.LabelKernel .. KP.ChargedPlan, KP.Free*) prove identities
between letter matrices; KP.LetterPlans proves `lift_mul`,
closure of `Implements` under `seq`, and supplies plans for `linMat` (one `perm` move), `signMat`
(one `scale`) and `walshU` (children). The notions follow OpenAI's `Bits`, `lift`,
`Implements` (NearSquareRoot); the definitions are restated for this tree. -/

namespace OAI.Computability.NearSquareRoot.KernelPass
open Matrix Finset

variable {A : ℕ}

/-- One bit of every axis. -/
abbrev Bits (A : ℕ) := Fin A → ZMod 2
/-- Letter matrices. -/
abbrev LMat (A : ℕ) := Matrix (Bits A) (Bits A) ℚ

/-- Letter `t` of a column. -/
def letterAt (c : Column A) (t : Fin 2) : Bits A := fun a => c a t

/-- The width-`h` matrix of a letter matrix: the same `M` on both letters of every column. -/
def lift (h : ℕ) (M : LMat A) : Matrix (Addr A h) (Addr A h) ℚ :=
  fun y x => ∏ c : Fin h, ∏ t : Fin 2, M (letterAt (y c) t) (letterAt (x c) t)

/-- `p` acts as the letter matrix `M`, with `n` normalized Walsh bits per letter. -/
def Implements (p : QPlan A 1 1) (M : LMat A) (n : ℕ) : Prop :=
  ∀ h, qBlk h p = ((1 / 2 : ℚ) ^ (n * h)) • lift h M

/-- The permutation letter matrix of a map of letters: `y = g x`. -/
def linMat (g : Bits A → Bits A) : LMat A := fun y x => if y = g x then 1 else 0

/-- The diagonal sign letter matrix of a letter function. -/
def signMat (φ : Bits A → ZMod 2) : LMat A := Matrix.diagonal fun x => chi (φ x)

/-- Unnormalized Walsh on the bits in `S`, identity on the other bits. As a plan it is one
`child` per axis of `S`, with `n = S.card`. -/
def walshU (S : Finset (Fin A)) : LMat A :=
  fun y x => if ∀ a, a ∉ S → y a = x a then chi (∑ a ∈ S, y a * x a) else 0

end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.Letter =====

-- ===== begin KP.FreeKernel =====
section
/-! # The free factorization of the label kernel on the active coordinates

For one query the active part of a letter is `(a, b) : Act u × Act u`: `a = (x_j, aux₁)` is the
distinguished bit and the `u` auxiliary bits of half 1, `b = (x_{k+j}, aux₂)` those of half 2.
The label kernel between a source label `v` and a target label `w` has the sign
`β (φv a_x + φw a_y) (ψw b_y + ψv b_x)`.

`free_kernel_entry`: given coordinates adapted to a free rectangle,
* source: `aux ≃ Hc × Sr` in each half (`A`, `A'`), with `φv (a₀, α) = ιH h + ιS (a₀, s)`,
* target: `aux ≃ Pc × Tr` in each half (`Bq`, `Bq'`), with `φw (a₀, α) = ιP p + ιT (a₀, t)`,
* `β (ιH h) (ιP p) = 0` and the two remaining pairings read through `bT`, `bS`,
the kernel is `Tgt * (Mid * Src)` in those coordinates. The source factor sums over the `h`
coordinates only and carries the auxiliary chirp only; it does not involve the distinguished
bits (`srcM_apply`), so it is independent of the query. The distinguished chirps sit in the
middle. `free_kernel` is the matrix form `kerAct = TgtM * MidM * SrcM` on `Act u × Act u`.

Statements and proofs are this tree's; the route (auxiliary slices, coset representatives in
the middle) follows OpenAI's `PrimeEndpointFactor` / `PrimeEndpointAuxiliary`. -/

namespace OAI.Computability.NearSquareRoot.KernelPass.Free
open Matrix Finset

/-- Auxiliary bits of one half. -/
abbrev Aux (u : ℕ) := Fin u → ZMod 2
/-- Active bits of one half: the distinguished bit and the auxiliary bits. -/
abbrev Act (u : ℕ) := ZMod 2 × Aux u

/-- The auxiliary chirp exponent. -/
def auxDot {u : ℕ} (α β : Aux u) : ZMod 2 := ∑ i, α i * β i

variable {u : ℕ} {Hc Sr Pc Tr : Type*}

/-- Source coordinates of the active part: `((h₁, h₂), ((x_j, s₁), (x_{k+j}, s₂)))`. -/
def srcCo (A A' : Aux u ≃ Hc × Sr) :
    Act u × Act u ≃ (Hc × Hc) × ((ZMod 2 × Sr) × (ZMod 2 × Sr)) where
  toFun x := (((A x.1.2).1, (A' x.2.2).1), ((x.1.1, (A x.1.2).2), (x.2.1, (A' x.2.2).2)))
  invFun i := ((i.2.1.1, A.symm (i.1.1, i.2.1.2)), (i.2.2.1, A'.symm (i.1.2, i.2.2.2)))
  left_inv x := by simp
  right_inv i := by simp

/-- The source sign: the auxiliary chirp, read in coordinates. -/
def srcSign (A A' : Aux u ≃ Hc × Sr) (i : (Hc × Hc) × ((ZMod 2 × Sr) × (ZMod 2 × Sr))) : ZMod 2 :=
  auxDot (A.symm (i.1.1, i.2.1.2)) (A'.symm (i.1.2, i.2.2.2))

lemma srcSign_co (A A' : Aux u ≃ Hc × Sr) (x : Act u × Act u) :
    srcSign A A' (srcCo A A' x) = auxDot x.1.2 x.2.2 := by
  simp [srcSign, srcCo]

/-- The middle sign: the pairing of the residual representatives and the two distinguished
chirps. -/
def midSign {V : Type*} [AddCommGroup V] (β : V →+ V →+ ZMod 2) (ιS : ZMod 2 × Sr → V)
    (ιT : ZMod 2 × Tr → V) (s : (ZMod 2 × Sr) × (ZMod 2 × Sr)) (t : (ZMod 2 × Tr) × (ZMod 2 × Tr)) :
    ZMod 2 :=
  β (ιS s.1) (ιT t.2) + β (ιT t.1) (ιS s.2) + s.1.1 * s.2.1 + t.1.1 * t.2.1

variable [Fintype Hc] [Fintype Sr] [Fintype Pc] [Fintype Tr]
  [DecidableEq Hc] [DecidableEq Sr] [DecidableEq Pc] [DecidableEq Tr]

/-- **Free factorization of the label kernel, entry form.** -/
theorem free_kernel_entry {V : Type*} [AddCommGroup V] (β : V →+ V →+ ZMod 2)
    (hsymm : ∀ x y, β x y = β y x)
    (φv ψv φw ψw : Act u → V)
    (ιH : Hc → V) (ιS : ZMod 2 × Sr → V) (ιP : Pc → V) (ιT : ZMod 2 × Tr → V)
    (A A' : Aux u ≃ Hc × Sr) (Bq Bq' : Aux u ≃ Pc × Tr)
    (hφv : ∀ a, φv a = ιH (A a.2).1 + ιS (a.1, (A a.2).2))
    (hψv : ∀ b, ψv b = ιH (A' b.2).1 + ιS (b.1, (A' b.2).2))
    (hφw : ∀ a, φw a = ιP (Bq a.2).1 + ιT (a.1, (Bq a.2).2))
    (hψw : ∀ b, ψw b = ιP (Bq' b.2).1 + ιT (b.1, (Bq' b.2).2))
    (hcv : ∀ a b, β (φv a) (ψv b) = a.1 * b.1 + auxDot a.2 b.2)
    (hcw : ∀ a b, β (φw a) (ψw b) = a.1 * b.1 + auxDot a.2 b.2)
    (eH : Hc → Hc → ZMod 2) (eP : Pc → Pc → ZMod 2)
    (bS : ZMod 2 × Sr → Pc) (bT : ZMod 2 × Tr → Hc)
    (hHP : ∀ h p, β (ιH h) (ιP p) = 0)
    (hHT : ∀ h t, β (ιH h) (ιT t) = eH h (bT t))
    (hSP : ∀ s p, β (ιS s) (ιP p) = eP (bS s) p)
    (y x : Act u × Act u) :
    chi (β (φv x.1 + φw y.1) (ψw y.2 + ψv x.2)) =
      (Tgt eP (srcSign Bq Bq') * (Mid bS bT (midSign β ιS ιT) * Src eH (srcSign A A')))
        (srcCo Bq Bq' y) (srcCo A A' x) := by
  rw [free_factor, srcSign_co, srcSign_co]
  congr 1
  have key := phase_split β hsymm ιH ιS ιP ιT eH eP bS bT hHP hHT hSP
    (A x.1.2).1 (A' x.2.2).1 (x.1.1, (A x.1.2).2) (x.2.1, (A' x.2.2).2)
    (Bq y.1.2).1 (Bq' y.2.2).1 (y.1.1, (Bq y.1.2).2) (y.2.1, (Bq' y.2.2).2)
  rw [← hφv, ← hψv, ← hφw, ← hψw, hcw, hcv] at key
  rw [key]
  simp only [srcCo, Equiv.coe_fn_mk, midSign]
  ring

/-- The kernel on the active coordinates (unnormalized). -/
def kerAct {V : Type*} [AddCommGroup V] (β : V →+ V →+ ZMod 2) (φv ψv φw ψw : Act u → V) :
    Matrix (Act u × Act u) (Act u × Act u) ℚ :=
  fun y x => chi (β (φv x.1 + φw y.1) (ψw y.2 + ψv x.2))

/-- The source factor on active coordinates. It depends on the source label only. -/
def srcM (A A' : Aux u ≃ Hc × Sr) (eH : Hc → Hc → ZMod 2) :
    Matrix (Act u × Act u) (Act u × Act u) ℚ :=
  (Src eH (srcSign A A')).submatrix (srcCo A A') (srcCo A A')

/-- The target factor on active coordinates. It depends on the target label only. -/
def tgtM (Bq Bq' : Aux u ≃ Pc × Tr) (eP : Pc → Pc → ZMod 2) :
    Matrix (Act u × Act u) (Act u × Act u) ℚ :=
  (Tgt eP (srcSign Bq Bq')).submatrix (srcCo Bq Bq') (srcCo Bq Bq')

/-- The middle factor on active coordinates: a signed partial permutation. -/
def midM {V : Type*} [AddCommGroup V] (β : V →+ V →+ ZMod 2) (ιS : ZMod 2 × Sr → V)
    (ιT : ZMod 2 × Tr → V) (A A' : Aux u ≃ Hc × Sr) (Bq Bq' : Aux u ≃ Pc × Tr)
    (bS : ZMod 2 × Sr → Pc) (bT : ZMod 2 × Tr → Hc) :
    Matrix (Act u × Act u) (Act u × Act u) ℚ :=
  (Mid bS bT (midSign β ιS ιT)).submatrix (srcCo Bq Bq') (srcCo A A')

/-- **Free factorization of the label kernel, matrix form.** -/
theorem free_kernel {V : Type*} [AddCommGroup V] (β : V →+ V →+ ZMod 2)
    (hsymm : ∀ x y, β x y = β y x)
    (φv ψv φw ψw : Act u → V)
    (ιH : Hc → V) (ιS : ZMod 2 × Sr → V) (ιP : Pc → V) (ιT : ZMod 2 × Tr → V)
    (A A' : Aux u ≃ Hc × Sr) (Bq Bq' : Aux u ≃ Pc × Tr)
    (hφv : ∀ a, φv a = ιH (A a.2).1 + ιS (a.1, (A a.2).2))
    (hψv : ∀ b, ψv b = ιH (A' b.2).1 + ιS (b.1, (A' b.2).2))
    (hφw : ∀ a, φw a = ιP (Bq a.2).1 + ιT (a.1, (Bq a.2).2))
    (hψw : ∀ b, ψw b = ιP (Bq' b.2).1 + ιT (b.1, (Bq' b.2).2))
    (hcv : ∀ a b, β (φv a) (ψv b) = a.1 * b.1 + auxDot a.2 b.2)
    (hcw : ∀ a b, β (φw a) (ψw b) = a.1 * b.1 + auxDot a.2 b.2)
    (eH : Hc → Hc → ZMod 2) (eP : Pc → Pc → ZMod 2)
    (bS : ZMod 2 × Sr → Pc) (bT : ZMod 2 × Tr → Hc)
    (hHP : ∀ h p, β (ιH h) (ιP p) = 0)
    (hHT : ∀ h t, β (ιH h) (ιT t) = eH h (bT t))
    (hSP : ∀ s p, β (ιS s) (ιP p) = eP (bS s) p) :
    kerAct β φv ψv φw ψw =
      tgtM Bq Bq' eP * (midM β ιS ιT A A' Bq Bq' bS bT * srcM A A' eH) := by
  ext y x
  rw [kerAct, free_kernel_entry β hsymm φv ψv φw ψw ιH ιS ιP ιT A A' Bq Bq' hφv hψv hφw hψw
    hcv hcw eH eP bS bT hHP hHT hSP y x, tgtM, midM, srcM,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  rfl

/-- The source factor touches auxiliary bits only: it is the identity on both distinguished
bits, and its entries do not depend on them. So it is the same matrix for every query. -/
theorem srcM_apply (A A' : Aux u ≃ Hc × Sr) (eH : Hc → Hc → ZMod 2) (y x : Act u × Act u) :
    srcM A A' eH y x =
      if y.1.1 = x.1.1 ∧ y.2.1 = x.2.1 ∧ (A y.1.2).2 = (A x.1.2).2 ∧ (A' y.2.2).2 = (A' x.2.2).2 then
        chi (eH (A x.1.2).1 (A y.1.2).1 + eH (A' x.2.2).1 (A' y.2.2).1 + auxDot x.1.2 x.2.2)
      else 0 := by
  simp only [srcM, Matrix.submatrix_apply, Src, srcSign_co]
  simp only [srcCo, Equiv.coe_fn_mk, Prod.mk.injEq]
  by_cases h : y.1.1 = x.1.1 ∧ y.2.1 = x.2.1 ∧ (A y.1.2).2 = (A x.1.2).2 ∧ (A' y.2.2).2 = (A' x.2.2).2
  · rw [if_pos h, if_pos ⟨⟨h.1, h.2.2.1⟩, h.2.1, h.2.2.2⟩]
  · rw [if_neg h, if_neg (fun hh => h ⟨hh.1.1, hh.2.1, hh.1.2, hh.2.2⟩)]

/-- The target factor touches auxiliary bits only. -/
theorem tgtM_apply (Bq Bq' : Aux u ≃ Pc × Tr) (eP : Pc → Pc → ZMod 2) (y x : Act u × Act u) :
    tgtM Bq Bq' eP y x =
      if y.1.1 = x.1.1 ∧ y.2.1 = x.2.1 ∧ (Bq y.1.2).2 = (Bq x.1.2).2 ∧ (Bq' y.2.2).2 = (Bq' x.2.2).2 then
        chi (eP (Bq x.1.2).1 (Bq y.1.2).1 + eP (Bq' x.2.2).1 (Bq' y.2.2).1 + auxDot y.1.2 y.2.2)
      else 0 := by
  simp only [tgtM, Matrix.submatrix_apply, Tgt, srcSign_co]
  simp only [srcCo, Equiv.coe_fn_mk, Prod.mk.injEq]
  by_cases h : y.1.1 = x.1.1 ∧ y.2.1 = x.2.1 ∧ (Bq y.1.2).2 = (Bq x.1.2).2 ∧ (Bq' y.2.2).2 = (Bq' x.2.2).2
  · rw [if_pos h, if_pos ⟨⟨h.1, h.2.2.1⟩, h.2.1, h.2.2.2⟩]
  · rw [if_neg h, if_neg (fun hh => h ⟨hh.1.1, hh.2.1, hh.1.2, hh.2.2⟩)]

end OAI.Computability.NearSquareRoot.KernelPass.Free
end
-- ===== end KP.FreeKernel =====

-- ===== begin KP.LabelKernel =====
section
/-! # The label kernel at letter level (shared by the charged and the free factorization)

Layout: `k = M + u` pairs, `A = 2 * (M + u)` axes, pair `p` is the axes `(p, k + p)`.
Pairs `< M` are distinguished, the last `u` are auxiliary. `V u = Fin (u+1) → ZMod 2`.
For a letter `x` and a query `j`: `act j x` is the active half-1 vector `(x_j, aux bits)`,
`act' j x` the half-2 one, `spect j x` the other distinguished bits.
A `Chart` is a dual pair `(phi, psi)` of matrices on `V u`: `psiᵀ * phi = 1`, so
`dotV (phi a) (psi b) = dotV a b`. `Uq j` is the unnormalized query letter matrix and
`U c j w v` the label kernel between labels `v` (source) and `w` (target) for a family of
charts `c`; `U_self`: `U c j v v = Uq j`.

Definitions follow OpenAI's (`transfer`, `queryChart`, `LabelCharts`),
restated for this tree. -/

namespace OAI.Computability.NearSquareRoot.KernelPass
open Matrix Finset

variable {M u : ℕ}

/-- The routing space. -/
abbrev V (u : ℕ) := Fin (u + 1) → ZMod 2

/-- The standard dot product on `V u`. -/
def dotV (a b : V u) : ZMod 2 := a ⬝ᵥ b

/-- Half-1 position of pair `p`. -/
def pos1 (p : Fin (M + u)) : Fin (2 * (M + u)) := ⟨p, by omega⟩
/-- Half-2 position of pair `p`. -/
def pos2 (p : Fin (M + u)) : Fin (2 * (M + u)) := ⟨M + u + p, by omega⟩
/-- Distinguished pair `j`. -/
def dpair (j : Fin M) : Fin (M + u) := Fin.castAdd u j
/-- Auxiliary pair `a`. -/
def apair (a : Fin u) : Fin (M + u) := Fin.natAdd M a

/-- Active half-1 vector of a letter for query `j`. -/
def act (j : Fin M) (x : Bits (2 * (M + u))) : V u :=
  Fin.cons (x (pos1 (dpair j))) fun a => x (pos1 (apair a))
/-- Active half-2 vector of a letter for query `j`. -/
def act' (j : Fin M) (x : Bits (2 * (M + u))) : V u :=
  Fin.cons (x (pos2 (dpair j))) fun a => x (pos2 (apair a))
/-- Spectator bits of a letter for query `j`. -/
def spect (j : Fin M) (x : Bits (2 * (M + u))) : {i : Fin M // i ≠ j} → ZMod 2 × ZMod 2 :=
  fun i => (x (pos1 (dpair (u := u) i.1)), x (pos2 (dpair (u := u) i.1)))

/-- The unnormalized query letter matrix. -/
def Uq (j : Fin M) : LMat (2 * (M + u)) := fun y x =>
  if spect j y = spect j x then chi (dotV (act j x + act j y) (act' j x + act' j y)) else 0

/-- A dual pair of charts on the routing space. -/
structure Chart (u : ℕ) where
  phi : Matrix (Fin (u + 1)) (Fin (u + 1)) (ZMod 2)
  psi : Matrix (Fin (u + 1)) (Fin (u + 1)) (ZMod 2)
  dual : psiᵀ * phi = 1

theorem Chart.dot (c : Chart u) (a b : V u) : dotV (c.phi *ᵥ a) (c.psi *ᵥ b) = dotV a b := by
  unfold dotV
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, c.dual,
    Matrix.one_mulVec]

variable {ι : Type*}

/-- The label kernel: query `j` from label `v` to label `w`, unnormalized, on one letter. -/
def U (c : ι → Chart u) (j : Fin M) (w v : ι) : LMat (2 * (M + u)) := fun y x =>
  if spect j y = spect j x then
    chi (dotV ((c v).phi *ᵥ act j x + (c w).phi *ᵥ act j y)
      ((c w).psi *ᵥ act' j y + (c v).psi *ᵥ act' j x)) else 0

/-- The diagonal blocks of the label kernel are the query. -/
theorem U_self (c : ι → Chart u) (j : Fin M) (v : ι) : U c j v v = Uq j := by
  funext y x
  simp only [U, Uq]
  split_ifs
  · rw [← Matrix.mulVec_add, ← Matrix.mulVec_add, (c v).dot, add_comm (act' j y)]
  · rfl

end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.LabelKernel =====

-- ===== begin KP.LabelChart =====
section
/-! # The chart map on letters and the charged form of the label kernel

`gl j c` applies the chart `c` to a letter: `phi` on the active half-1 vector of query `j`,
`psi` on the active half-2 vector, nothing on the spectators (`act_gl`, `act'_gl`, `spect_gl`).
**`U_eq_submatrix`**: `U c j w v = (Uq j).submatrix (gl j (c w)) (gl j (c v))`, for every pair
of labels — the charged factorization at letter level: relabel, common query, relabel.
Follows OpenAI's `transfer = rippleMat.submatrix chart chart`. -/

namespace OAI.Computability.NearSquareRoot.KernelPass
open Matrix Finset

variable {M u : ℕ}

lemma pos1_inj : Function.Injective (pos1 (M := M) (u := u)) := fun p q h => by
  have := congrArg Fin.val h; simp only [pos1] at this; exact Fin.ext this
lemma pos2_inj : Function.Injective (pos2 (M := M) (u := u)) := fun p q h => by
  have := congrArg Fin.val h; simp only [pos2] at this; exact Fin.ext (by omega)
lemma pos1_ne_pos2 (p q : Fin (M + u)) : pos1 p ≠ pos2 q := fun h => by
  have := congrArg Fin.val h; simp only [pos1, pos2] at this; omega
lemma dpair_ne_apair (j : Fin M) (a : Fin u) : dpair (u := u) j ≠ apair a := fun h => by
  have := congrArg Fin.val h; simp only [dpair, apair, Fin.val_castAdd, Fin.val_natAdd] at this; omega
lemma apair_inj : Function.Injective (apair (M := M) (u := u)) := fun a b h => by
  have := congrArg Fin.val h; simp only [apair, Fin.val_natAdd] at this; exact Fin.ext (by omega)
lemma dpair_inj : Function.Injective (dpair (M := M) (u := u)) :=
  Fin.castAdd_injective M u

/-- The chart `c` applied to a letter, for query `j`. -/
noncomputable def gl (j : Fin M) (c : Chart u) (x : Bits (2 * (M + u))) : Bits (2 * (M + u)) :=
  fun i =>
    if i = pos1 (dpair j) then (c.phi *ᵥ act j x) 0
    else if h : ∃ a : Fin u, i = pos1 (apair a) then (c.phi *ᵥ act j x) h.choose.succ
    else if i = pos2 (dpair j) then (c.psi *ᵥ act' j x) 0
    else if h : ∃ a : Fin u, i = pos2 (apair a) then (c.psi *ᵥ act' j x) h.choose.succ
    else x i

lemma gl_d1 (j : Fin M) (c : Chart u) (x : Bits (2 * (M + u))) :
    gl j c x (pos1 (dpair j)) = (c.phi *ᵥ act j x) 0 := by
  simp only [gl, if_true]

lemma gl_a1 (j : Fin M) (c : Chart u) (x : Bits (2 * (M + u))) (a : Fin u) :
    gl j c x (pos1 (apair a)) = (c.phi *ᵥ act j x) a.succ := by
  have h1 : pos1 (apair (M := M) a) ≠ pos1 (dpair j) := fun h =>
    dpair_ne_apair j a (pos1_inj h).symm
  have h2 : ∃ a' : Fin u, pos1 (apair (M := M) a) = pos1 (apair a') := ⟨a, rfl⟩
  have h3 : h2.choose = a := (apair_inj (pos1_inj h2.choose_spec)).symm
  simp only [gl, if_neg h1, dif_pos h2, h3]

lemma gl_d2 (j : Fin M) (c : Chart u) (x : Bits (2 * (M + u))) :
    gl j c x (pos2 (dpair j)) = (c.psi *ᵥ act' j x) 0 := by
  have h1 : pos2 (dpair (u := u) j) ≠ pos1 (dpair j) := (pos1_ne_pos2 _ _).symm
  have h2 : ¬ ∃ a : Fin u, pos2 (dpair (u := u) j) = pos1 (apair a) := fun ⟨a, h⟩ =>
    pos1_ne_pos2 _ _ h.symm
  simp only [gl, if_neg h1, dif_neg h2, if_true]

lemma gl_a2 (j : Fin M) (c : Chart u) (x : Bits (2 * (M + u))) (a : Fin u) :
    gl j c x (pos2 (apair a)) = (c.psi *ᵥ act' j x) a.succ := by
  have h1 : pos2 (apair (M := M) a) ≠ pos1 (dpair j) := (pos1_ne_pos2 _ _).symm
  have h2 : ¬ ∃ a' : Fin u, pos2 (apair (M := M) a) = pos1 (apair a') := fun ⟨a', h⟩ =>
    pos1_ne_pos2 _ _ h.symm
  have h3 : pos2 (apair (M := M) a) ≠ pos2 (dpair j) := fun h =>
    dpair_ne_apair j a (pos2_inj h).symm
  have h4 : ∃ a' : Fin u, pos2 (apair (M := M) a) = pos2 (apair a') := ⟨a, rfl⟩
  have h5 : h4.choose = a := (apair_inj (pos2_inj h4.choose_spec)).symm
  simp only [gl, if_neg h1, dif_neg h2, if_neg h3, dif_pos h4, h5]

lemma gl_s1 (j : Fin M) (c : Chart u) (x : Bits (2 * (M + u))) {i : Fin M} (hi : i ≠ j) :
    gl j c x (pos1 (dpair i)) = x (pos1 (dpair i)) := by
  have h1 : pos1 (dpair (u := u) i) ≠ pos1 (dpair j) := fun h => hi (dpair_inj (pos1_inj h))
  have h2 : ¬ ∃ a : Fin u, pos1 (dpair (u := u) i) = pos1 (apair a) := fun ⟨a, h⟩ =>
    dpair_ne_apair i a (pos1_inj h)
  have h3 : pos1 (dpair (u := u) i) ≠ pos2 (dpair j) := pos1_ne_pos2 _ _
  have h4 : ¬ ∃ a : Fin u, pos1 (dpair (u := u) i) = pos2 (apair a) := fun ⟨a, h⟩ =>
    pos1_ne_pos2 _ _ h
  simp only [gl, if_neg h1, dif_neg h2, if_neg h3, dif_neg h4]

lemma gl_s2 (j : Fin M) (c : Chart u) (x : Bits (2 * (M + u))) {i : Fin M} (hi : i ≠ j) :
    gl j c x (pos2 (dpair i)) = x (pos2 (dpair i)) := by
  have h1 : pos2 (dpair (u := u) i) ≠ pos1 (dpair j) := (pos1_ne_pos2 _ _).symm
  have h2 : ¬ ∃ a : Fin u, pos2 (dpair (u := u) i) = pos1 (apair a) := fun ⟨a, h⟩ =>
    pos1_ne_pos2 _ _ h.symm
  have h3 : pos2 (dpair (u := u) i) ≠ pos2 (dpair j) := fun h => hi (dpair_inj (pos2_inj h))
  have h4 : ¬ ∃ a : Fin u, pos2 (dpair (u := u) i) = pos2 (apair a) := fun ⟨a, h⟩ =>
    dpair_ne_apair i a (pos2_inj h)
  simp only [gl, if_neg h1, dif_neg h2, if_neg h3, dif_neg h4]

theorem act_gl (j : Fin M) (c : Chart u) (x : Bits (2 * (M + u))) :
    act j (gl j c x) = c.phi *ᵥ act j x := by
  funext i
  refine Fin.cases ?_ (fun a => ?_) i
  · simp only [act, Fin.cons_zero]; exact gl_d1 j c x
  · simp only [act, Fin.cons_succ]; exact gl_a1 j c x a

theorem act'_gl (j : Fin M) (c : Chart u) (x : Bits (2 * (M + u))) :
    act' j (gl j c x) = c.psi *ᵥ act' j x := by
  funext i
  refine Fin.cases ?_ (fun a => ?_) i
  · simp only [act', Fin.cons_zero]; exact gl_d2 j c x
  · simp only [act', Fin.cons_succ]; exact gl_a2 j c x a

theorem spect_gl (j : Fin M) (c : Chart u) (x : Bits (2 * (M + u))) :
    spect j (gl j c x) = spect j x := by
  funext i
  simp only [spect, gl_s1 j c x i.2, gl_s2 j c x i.2]

variable {ι : Type*}

/-- **Charged form of the label kernel (letter level).** Every cross block is the query in
the charts of its two labels. -/
theorem U_eq_submatrix (c : ι → Chart u) (j : Fin M) (w v : ι) :
    U c j w v = (Uq j).submatrix (gl j (c w)) (gl j (c v)) := by
  funext y x
  simp only [U, Uq, submatrix_apply, act_gl, act'_gl, spect_gl]
  split_ifs
  · rw [add_comm ((c w).psi *ᵥ act' j y)]
  · rfl

end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.LabelChart =====

-- ===== begin KP.ActLift =====
section
/-! # Letters as (spectators, active part), and the label kernel as an active kernel

`bitsE j` splits a letter into the spectator bits of query `j` and the active part
`(a, b) : Act u × Act u`. `actLift j K` is the letter matrix that is `K` on the active part and
the identity on the spectators; it is multiplicative (`actLift_mul`).
`U_eq_actLift`: the label kernel `U c j w v` is `actLift j` of the active kernel `kerAct` for
the dot product and the charts of `v`, `w`. `chart_dot` is the chart identity in the form
`free_kernel` takes. -/

namespace OAI.Computability.NearSquareRoot.KernelPass
open Matrix Finset
open Free

variable {M u : ℕ}

/-- Positions of a letter: half, then distinguished or auxiliary pair. -/
def idxE (M u : ℕ) : (Fin M ⊕ Fin u) ⊕ (Fin M ⊕ Fin u) ≃ Fin (2 * (M + u)) :=
  ((Equiv.sumCongr finSumFinEquiv finSumFinEquiv).trans finSumFinEquiv).trans
    (finCongr (two_mul (M + u)).symm)

lemma idxE_ll (i : Fin M) : idxE M u (.inl (.inl i)) = pos1 (dpair i) := by
  apply Fin.ext; simp [idxE, pos1, dpair]
lemma idxE_lr (a : Fin u) : idxE M u (.inl (.inr a)) = pos1 (apair a) := by
  apply Fin.ext; simp [idxE, pos1, apair]
lemma idxE_rl (i : Fin M) : idxE M u (.inr (.inl i)) = pos2 (dpair i) := by
  apply Fin.ext; simp [idxE, pos2, dpair]; omega
lemma idxE_rr (a : Fin u) : idxE M u (.inr (.inr a)) = pos2 (apair a) := by
  apply Fin.ext; simp [idxE, pos2, apair]; omega

/-- Spectator bits of query `j`: the other distinguished bits of both halves. -/
abbrev Spec (M : ℕ) (j : Fin M) := ({i : Fin M // i ≠ j} → ZMod 2) × ({i : Fin M // i ≠ j} → ZMod 2)

/-- A letter as spectators and active part. -/
def bitsE (j : Fin M) : Bits (2 * (M + u)) ≃ Spec M j × (Act u × Act u) where
  toFun x := ((fun i => x (pos1 (dpair i.1)), fun i => x (pos2 (dpair i.1))),
    ((x (pos1 (dpair j)), fun a => x (pos1 (apair a))),
     (x (pos2 (dpair j)), fun a => x (pos2 (apair a)))))
  invFun p := fun i =>
    match (idxE M u).symm i with
    | .inl (.inl i') => if h : i' = j then p.2.1.1 else p.1.1 ⟨i', h⟩
    | .inl (.inr a) => p.2.1.2 a
    | .inr (.inl i') => if h : i' = j then p.2.2.1 else p.1.2 ⟨i', h⟩
    | .inr (.inr a) => p.2.2.2 a
  left_inv x := by
    funext i
    obtain ⟨s, rfl⟩ := (idxE M u).surjective i
    dsimp only
    rw [Equiv.symm_apply_apply]
    rcases s with (i' | a) | (i' | a)
    · by_cases h : i' = j
      · subst h; simp [idxE_ll]
      · simp [h, idxE_ll]
    · simp [idxE_lr]
    · by_cases h : i' = j
      · subst h; simp [idxE_rl]
      · simp [h, idxE_rl]
    · simp [idxE_rr]
  right_inv p := by
    refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_))
    · funext i; simp only [← idxE_ll, Equiv.symm_apply_apply]; simp [i.2]
    · funext i; simp only [← idxE_rl, Equiv.symm_apply_apply]; simp [i.2]
    · simp only [← idxE_ll, Equiv.symm_apply_apply]; simp
    · funext a; simp only [← idxE_lr, Equiv.symm_apply_apply]
    · simp only [← idxE_rl, Equiv.symm_apply_apply]; simp
    · funext a; simp only [← idxE_rr, Equiv.symm_apply_apply]

/-- Identity on a passive coordinate, `K` on the other. -/
def zext {Z X : Type*} [DecidableEq Z] (K : Matrix X X ℚ) : Matrix (Z × X) (Z × X) ℚ :=
  fun p q => if p.1 = q.1 then K p.2 q.2 else 0

theorem zext_mul {Z X : Type*} [DecidableEq Z] [Fintype Z] [Fintype X] (K K' : Matrix X X ℚ) :
    zext (Z := Z) (K * K') = zext K * zext K' := by
  ext p q
  rw [mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single p.1]
  · simp only [zext, if_true, mul_apply]
    split_ifs <;> simp only [mul_zero, Finset.sum_const_zero]
  · intro z _ hz
    refine Finset.sum_eq_zero fun a _ => ?_
    simp [zext, Ne.symm hz]
  · exact fun hu => absurd (Finset.mem_univ _) hu

/-- The letter matrix that is `K` on the active part of query `j`, identity on the spectators. -/
def actLift (j : Fin M) (K : Matrix (Act u × Act u) (Act u × Act u) ℚ) : LMat (2 * (M + u)) :=
  (zext (Z := Spec M j) K).submatrix (bitsE j) (bitsE j)

theorem actLift_mul (j : Fin M) (K K' : Matrix (Act u × Act u) (Act u × Act u) ℚ) :
    actLift (M := M) j (K * K') = actLift j K * actLift j K' := by
  rw [actLift, zext_mul, actLift, actLift, Matrix.submatrix_mul_equiv]

theorem actLift_apply (j : Fin M) (K : Matrix (Act u × Act u) (Act u × Act u) ℚ)
    (y x : Bits (2 * (M + u))) :
    actLift j K y x = if (bitsE j y).1 = (bitsE j x).1 then K (bitsE j y).2 (bitsE j x).2 else 0 := rfl

/-- The dot product on the routing space as a biadditive map. -/
def dotHom (u : ℕ) : V u →+ V u →+ ZMod 2 :=
  AddMonoidHom.mk' (fun a => AddMonoidHom.mk' (fun b => a ⬝ᵥ b) (fun b c => dotProduct_add a b c))
    (fun a b => by ext c; simp [add_dotProduct])

@[simp] lemma dotHom_apply (a b : V u) : dotHom u a b = dotV a b := rfl

lemma dotHom_symm (a b : V u) : dotHom u a b = dotHom u b a := dotProduct_comm a b

/-- A chart half as a map on active coordinates. -/
def chartMap (P : Matrix (Fin (u + 1)) (Fin (u + 1)) (ZMod 2)) (a : Act u) : V u :=
  P *ᵥ (Fin.cons a.1 a.2 : V u)

/-- The chart identity in active coordinates. -/
theorem chart_dot (c : Chart u) (a b : Act u) :
    dotHom u (chartMap c.phi a) (chartMap c.psi b) = a.1 * b.1 + auxDot a.2 b.2 := by
  rw [dotHom_apply, chartMap, chartMap, c.dot, dotV, dotProduct, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, auxDot]

lemma spect_eq_iff (j : Fin M) (y x : Bits (2 * (M + u))) :
    spect j y = spect j x ↔ (bitsE j y).1 = (bitsE j x).1 := by
  constructor
  · intro h
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · exact congrArg Prod.fst (congrFun h i)
    · exact congrArg Prod.snd (congrFun h i)
  · intro h
    funext i
    exact Prod.ext (congrFun (congrArg Prod.fst h) i) (congrFun (congrArg Prod.snd h) i)

/-- **The label kernel is the active kernel of the charts, lifted to letters.** -/
theorem U_eq_actLift {ι : Type*} (c : ι → Chart u) (j : Fin M) (w v : ι) :
    U c j w v = actLift j (kerAct (dotHom u) (chartMap (c v).phi) (chartMap (c v).psi)
      (chartMap (c w).phi) (chartMap (c w).psi)) := by
  funext y x
  rw [actLift_apply]
  simp only [U, spect_eq_iff]
  split_ifs
  · rfl
  · rfl

end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.ActLift =====

-- ===== begin KP.ExplicitChart =====
section
/-! # An explicit pointed chart for a routing vector

For `d : V u` with `d 0 = 1` and `d · d = 1` (every routing vector of the Hamming labels has
this form), `chartOf d` is a chart with `phi e₀ = psi e₀ = d`:
* `phi` has columns `d` and `e_i + d_i e₀` (`i ≥ 1`), a basis of `d^⊥`;
* `psi` has columns `d` and `e_i + d_i d` (`i ≥ 1`), the dual basis.
`psiOf_phiOf`: `psi` is the dual basis of `phi`. Shared by the charged and the free factorization. -/

namespace OAI.Computability.NearSquareRoot.KernelPass
open Matrix Finset

variable {u : ℕ}

def phiOf (d : V u) : Matrix (Fin (u + 1)) (Fin (u + 1)) (ZMod 2) :=
  fun a i => if i = 0 then d a else (if a = i then 1 else 0) + (if a = 0 then d i else 0)

def psiOf (d : V u) : Matrix (Fin (u + 1)) (Fin (u + 1)) (ZMod 2) :=
  fun a i => if i = 0 then d a else (if a = i then 1 else 0) + d i * d a

theorem psiOf_phiOf (d : V u) (h0 : d 0 = 1) (hd : dotV d d = 1) :
    (psiOf d)ᵀ * phiOf d = 1 := by
  have hdd : (∑ a, d a * d a) = 1 := hd
  ext i k
  rw [mul_apply, one_apply]
  simp only [transpose_apply, psiOf, phiOf]
  by_cases hi : i = 0
  · by_cases hk : k = 0
    · subst hi; subst hk; simp only [↓reduceIte, hdd]
    · subst hi
      simp only [if_true, if_neg hk, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, h0, one_mul, if_neg (Ne.symm hk)]
      exact CharTwo.add_self_eq_zero _
  · by_cases hk : k = 0
    · subst hk
      simp only [if_neg hi, if_true, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, mul_assoc, ← Finset.mul_sum, hdd, mul_one, if_neg hi]
      exact CharTwo.add_self_eq_zero _
    · simp only [if_neg hi, if_neg hk, add_mul, mul_add, Finset.sum_add_distrib, ite_mul, mul_ite,
        one_mul, zero_mul, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ,
        if_true, h0, if_neg hi]
      have hi' : ¬ (0 : Fin (u + 1)) = i := fun h => hi h.symm
      by_cases hik : i = k
      · subst hik
        simp only [if_true, if_neg hi']
        rw [zero_add, add_assoc, CharTwo.add_self_eq_zero, add_zero]
      · simp only [if_neg hik, if_neg hi', if_neg (Ne.symm hik), zero_add]
        exact CharTwo.add_self_eq_zero _

/-- The explicit pointed chart of a routing vector. -/
def chartOf (d : V u) (h0 : d 0 = 1) (hd : dotV d d = 1) : Chart u :=
  ⟨phiOf d, psiOf d, psiOf_phiOf d h0 hd⟩

end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.ExplicitChart =====

-- ===== begin KP.FreeLetter =====
section
/-! # The free factorization of the label kernel on letters

`free_letter`: for charts `c v`, `c w` and coordinates adapted to a free rectangle (the
hypotheses of `Free.free_kernel`, with linear `ιH`, `ιP`, so that the two residual pairings
are read off automatically), the label kernel `U` factors on letters as

`U c j w v = TgtL * (MidL * SrcL)`,

with `SrcL = actLift j (srcM A A' dotI)` depending on the source chart data only and
`TgtL = actLift j (tgtM Bq Bq' dotI)` on the target chart data only.
`actLift_srcM`, `actLift_tgtM`: these two letter matrices do not depend on the query `j`:
they are the identity on every distinguished bit and act on the auxiliary bits only. -/

namespace OAI.Computability.NearSquareRoot.KernelPass
open Matrix Finset
open Free

variable {M u : ℕ}

/-- The dot product on coordinate vectors. -/
def dotI {I : Type*} [Fintype I] (h h' : I → ZMod 2) : ZMod 2 := ∑ a, h a * h' a

/-- Read a pairing against a linear family in its coordinates. -/
def readL {I X : Type*} [DecidableEq I] (f : (I → ZMod 2) →ₗ[ZMod 2] V u) (g : X → V u) (x : X) :
    I → ZMod 2 :=
  fun a => dotV (f fun k => if a = k then 1 else 0) (g x)

lemma dot_readL {I X : Type*} [Fintype I] [DecidableEq I] (f : (I → ZMod 2) →ₗ[ZMod 2] V u)
    (g : X → V u) (h : I → ZMod 2) (x : X) : dotV (f h) (g x) = dotI h (readL f g x) := by
  rw [LinearMap.pi_apply_eq_sum_univ f h, dotV, sum_dotProduct]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_dotProduct, smul_eq_mul]; rfl

variable {ι IH IP Sr Tr : Type*} [Fintype IH] [DecidableEq IH] [Fintype IP] [DecidableEq IP]
  [Fintype Sr] [DecidableEq Sr] [Fintype Tr] [DecidableEq Tr]

/-- **Free factorization of the label kernel on letters.** -/
theorem free_letter (c : ι → Chart u) (j : Fin M) (w v : ι)
    (ιH : (IH → ZMod 2) →ₗ[ZMod 2] V u) (ιS : ZMod 2 × Sr → V u)
    (ιP : (IP → ZMod 2) →ₗ[ZMod 2] V u) (ιT : ZMod 2 × Tr → V u)
    (A A' : Aux u ≃ (IH → ZMod 2) × Sr) (Bq Bq' : Aux u ≃ (IP → ZMod 2) × Tr)
    (hφv : ∀ a, chartMap (c v).phi a = ιH (A a.2).1 + ιS (a.1, (A a.2).2))
    (hψv : ∀ b, chartMap (c v).psi b = ιH (A' b.2).1 + ιS (b.1, (A' b.2).2))
    (hφw : ∀ a, chartMap (c w).phi a = ιP (Bq a.2).1 + ιT (a.1, (Bq a.2).2))
    (hψw : ∀ b, chartMap (c w).psi b = ιP (Bq' b.2).1 + ιT (b.1, (Bq' b.2).2))
    (hHP : ∀ h p, dotV (ιH h) (ιP p) = 0) :
    U c j w v = actLift j (tgtM Bq Bq' dotI) *
      (actLift j (midM (dotHom u) ιS ιT A A' Bq Bq' (readL ιP ιS) (readL ιH ιT)) *
        actLift j (srcM A A' dotI)) := by
  rw [U_eq_actLift, ← actLift_mul, ← actLift_mul]
  congr 1
  refine free_kernel (dotHom u) dotHom_symm _ _ _ _ ιH ιS ιP ιT A A' Bq Bq' hφv hψv hφw hψw
    (chart_dot (c v)) (chart_dot (c w)) dotI dotI (readL ιP ιS) (readL ιH ιT) hHP
    (fun h t => dot_readL ιH ιT h t) (fun s p => ?_)
  rw [dotHom_apply, dotV, dotProduct_comm]
  have := dot_readL ιP ιS p s
  rw [dotV] at this
  rw [this, dotI, dotI]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

/-- Auxiliary bits of half 1 and half 2 of a letter. -/
def aux1 (x : Bits (2 * (M + u))) : Aux u := fun a => x (pos1 (apair a))
def aux2 (x : Bits (2 * (M + u))) : Aux u := fun a => x (pos2 (apair a))

/-- All distinguished bits of two letters agree. -/
def DistEq (y x : Bits (2 * (M + u))) : Prop :=
  ∀ i : Fin M, y (pos1 (dpair i)) = x (pos1 (dpair i)) ∧ y (pos2 (dpair i)) = x (pos2 (dpair i))

instance (y x : Bits (2 * (M + u))) : Decidable (DistEq y x) := by unfold DistEq; infer_instance

lemma distEq_iff (j : Fin M) (y x : Bits (2 * (M + u))) :
    DistEq y x ↔ (bitsE j y).1 = (bitsE j x).1 ∧
      (bitsE j y).2.1.1 = (bitsE j x).2.1.1 ∧ (bitsE j y).2.2.1 = (bitsE j x).2.2.1 := by
  constructor
  · intro h
    exact ⟨Prod.ext (funext fun i => (h i.1).1) (funext fun i => (h i.1).2), (h j).1, (h j).2⟩
  · rintro ⟨hz, h1, h2⟩ i
    by_cases hi : i = j
    · subst hi; exact ⟨h1, h2⟩
    · exact ⟨congrFun (congrArg Prod.fst hz) ⟨i, hi⟩, congrFun (congrArg Prod.snd hz) ⟨i, hi⟩⟩

/-- The source letter matrix does not depend on the query: identity on every distinguished
bit, a transform of the auxiliary bits only. -/
theorem actLift_srcM {Hc : Type*} [Fintype Hc] [DecidableEq Hc] (j : Fin M)
    (A A' : Aux u ≃ Hc × Sr) (eH : Hc → Hc → ZMod 2) (y x : Bits (2 * (M + u))) :
    actLift j (srcM A A' eH) y x =
      if DistEq y x ∧ (A (aux1 y)).2 = (A (aux1 x)).2 ∧ (A' (aux2 y)).2 = (A' (aux2 x)).2 then
        chi (eH (A (aux1 x)).1 (A (aux1 y)).1 + eH (A' (aux2 x)).1 (A' (aux2 y)).1 +
          auxDot (aux1 x) (aux2 x))
      else 0 := by
  rw [actLift_apply]
  by_cases hz : (bitsE j y).1 = (bitsE j x).1
  · rw [if_pos hz, srcM_apply]
    split_ifs with hc hd hd
    · rfl
    · exact absurd ⟨(distEq_iff j y x).2 ⟨hz, hc.1, hc.2.1⟩, hc.2.2.1, hc.2.2.2⟩ hd
    · exact absurd ⟨((distEq_iff j y x).1 hd.1).2.1, ((distEq_iff j y x).1 hd.1).2.2, hd.2.1, hd.2.2⟩ hc
    · rfl
  · rw [if_neg hz, if_neg (fun h => hz ((distEq_iff j y x).1 h.1).1)]

/-- The target letter matrix does not depend on the query. -/
theorem actLift_tgtM {Pc : Type*} [Fintype Pc] [DecidableEq Pc] (j : Fin M)
    (Bq Bq' : Aux u ≃ Pc × Tr) (eP : Pc → Pc → ZMod 2) (y x : Bits (2 * (M + u))) :
    actLift j (tgtM Bq Bq' eP) y x =
      if DistEq y x ∧ (Bq (aux1 y)).2 = (Bq (aux1 x)).2 ∧ (Bq' (aux2 y)).2 = (Bq' (aux2 x)).2 then
        chi (eP (Bq (aux1 x)).1 (Bq (aux1 y)).1 + eP (Bq' (aux2 x)).1 (Bq' (aux2 y)).1 +
          auxDot (aux1 y) (aux2 y))
      else 0 := by
  rw [actLift_apply]
  by_cases hz : (bitsE j y).1 = (bitsE j x).1
  · rw [if_pos hz, tgtM_apply]
    split_ifs with hc hd hd
    · rfl
    · exact absurd ⟨(distEq_iff j y x).2 ⟨hz, hc.1, hc.2.1⟩, hc.2.2.1, hc.2.2.2⟩ hd
    · exact absurd ⟨((distEq_iff j y x).1 hd.1).2.1, ((distEq_iff j y x).1 hd.1).2.2, hd.2.1, hd.2.2⟩ hc
    · rfl
  · rw [if_neg hz, if_neg (fun h => hz ((distEq_iff j y x).1 h.1).1)]

end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.FreeLetter =====

-- ===== begin KP.FreeGeom =====
section
/-! # Explicit coordinates for a free rectangle

Routing vectors `d` with `d 0 = 1`, `d · d = 1` and their explicit charts `chartOf d`.
`g a = d a.succ` is the auxiliary part of `d`. A free rectangle is described by a set `Sp` of
auxiliary coordinates, a vector `n'` and a pivot `i0 ∈ Sp` with `n' i0 = 1`, such that
* every source `v` has `g_v = n'` on `Sp`;
* every target `w` has `g_w = 0` off `Sp` and `n' · g_w = 1`.
(For a cut rectangle of the Hamming labels: `Sp` = the letters allowed for the targets, `n'` =
the indicator of the common letters at the uncut positions.)

Then the summation space of the sources is the coordinate space of `Sp` (half 1), and that of
the targets is the coordinate space off `Sp` plus the line of `n'`. `free_geom` is the resulting
factorization of the label kernel, with every piece explicit:
`splitA`, `theta`, `splitB`, `extH`, `extS`, `extP`, `extT`. -/

namespace OAI.Computability.NearSquareRoot.KernelPass
open Matrix Finset
open Free

variable {u : ℕ}

/-! ## The explicit charts on active coordinates -/

/-- The auxiliary part of a routing vector. -/
def gOf (d : V u) : Aux u := fun a => d a.succ

lemma auxDot_add_smul (β g g' : Aux u) (c : ZMod 2) :
    auxDot (fun a => β a + c * g a) g' = auxDot β g' + c * auxDot g g' := by
  simp only [auxDot, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]

lemma gOf_self (d : V u) (h0 : d 0 = 1) (hd : dotV d d = 1) : auxDot (gOf d) (gOf d) = 0 := by
  have h : dotV d d = d 0 * d 0 + auxDot (gOf d) (gOf d) := by
    rw [dotV, dotProduct, Fin.sum_univ_succ]; rfl
  rw [h, h0] at hd
  linear_combination hd

theorem phiOf_mulVec (d : V u) (h0 : d 0 = 1) (a0 : ZMod 2) (α : Aux u) :
    phiOf d *ᵥ (Fin.cons a0 α : V u) =
      Fin.cons (a0 + auxDot α (gOf d)) (fun a => a0 * gOf d a + α a) := by
  funext i
  refine Fin.cases ?_ (fun b => ?_) i
  · simp only [mulVec, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, phiOf, if_true,
      h0, one_mul, Fin.succ_ne_zero, if_false, auxDot, gOf, zero_add]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [if_neg (Fin.succ_ne_zero a).symm, zero_add, mul_comm]
  · simp only [mulVec, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, phiOf, if_true,
      Fin.succ_ne_zero, if_false, gOf, add_zero, Fin.succ_inj, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ]
    rw [mul_comm]

theorem psiOf_mulVec (d : V u) (h0 : d 0 = 1) (b0 : ZMod 2) (β : Aux u) :
    psiOf d *ᵥ (Fin.cons b0 β : V u) =
      Fin.cons (b0 + auxDot β (gOf d))
        (fun a => b0 * gOf d a + (β a + auxDot β (gOf d) * gOf d a)) := by
  funext i
  refine Fin.cases ?_ (fun b => ?_) i
  · simp only [mulVec, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, psiOf, if_true,
      h0, one_mul, Fin.succ_ne_zero, if_false, auxDot, gOf, mul_one]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [if_neg (Fin.succ_ne_zero a).symm, zero_add, mul_comm]
  · simp only [mulVec, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, psiOf, if_true,
      Fin.succ_ne_zero, if_false, gOf, Fin.succ_inj, add_mul, ite_mul, one_mul, zero_mul,
      Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, auxDot]
    rw [mul_comm (d b.succ) b0, Finset.sum_mul]
    congr 2
    refine Finset.sum_congr rfl fun a _ => by ring

/-- The transvection that turns the second chart into the first on auxiliary bits. -/
def thetaFn (g : Aux u) (β : Aux u) : Aux u := fun a => β a + auxDot β g * g a

lemma auxDot_theta (g : Aux u) (hg : auxDot g g = 0) (β : Aux u) :
    auxDot (thetaFn g β) g = auxDot β g := by
  unfold thetaFn
  rw [auxDot_add_smul, hg, mul_zero, add_zero]

lemma thetaFn_invol (g : Aux u) (hg : auxDot g g = 0) : Function.Involutive (thetaFn g) := by
  intro β
  funext a
  show thetaFn g β a + auxDot (thetaFn g β) g * g a = β a
  rw [auxDot_theta g hg]
  show β a + auxDot β g * g a + auxDot β g * g a = β a
  linear_combination CharTwo.add_self_eq_zero (auxDot β g * g a)

/-- `thetaFn` as a permutation of the auxiliary bits. -/
def theta (g : Aux u) (hg : auxDot g g = 0) : Aux u ≃ Aux u :=
  (thetaFn_invol g hg).toPerm

theorem psi_eq_phi_theta (d : V u) (h0 : d 0 = 1) (hd : dotV d d = 1) (b : Act u) :
    chartMap (psiOf d) b = chartMap (phiOf d) (b.1, thetaFn (gOf d) b.2) := by
  rw [chartMap, chartMap, psiOf_mulVec d h0, phiOf_mulVec d h0, auxDot_theta _ (gOf_self d h0 hd)]
  rfl

/-! ## Linear pieces -/

/-- `α ↦ (0, α)` into the routing space. -/
def consL (u : ℕ) : Aux u →ₗ[ZMod 2] V u where
  toFun α := Fin.cons 0 α
  map_add' α β := by funext i; refine Fin.cases ?_ (fun b => ?_) i <;> simp
  map_smul' c α := by funext i; refine Fin.cases ?_ (fun b => ?_) i <;> simp

lemma cons_split (a0 : ZMod 2) (α β : Aux u) :
    (Fin.cons a0 (α + β) : V u) = Fin.cons 0 α + Fin.cons a0 β := by
  funext i; refine Fin.cases ?_ (fun b => ?_) i <;> simp

variable (Sp : Finset (Fin u))

/-- Extend coordinates on `Sp` by zero. -/
def extH : ({a : Fin u // a ∈ Sp} → ZMod 2) →ₗ[ZMod 2] Aux u where
  toFun h := fun a => if ha : a ∈ Sp then h ⟨a, ha⟩ else 0
  map_add' h h' := by funext a; by_cases ha : a ∈ Sp <;> simp [ha]
  map_smul' c h := by funext a; by_cases ha : a ∈ Sp <;> simp [ha]

/-- Extend coordinates off `Sp` by zero. -/
def extS (s : {a : Fin u // a ∉ Sp} → ZMod 2) : Aux u :=
  fun a => if ha : a ∈ Sp then 0 else s ⟨a, ha⟩

/-- Split the auxiliary bits into those in `Sp` and the others. -/
def splitA : Aux u ≃ ({a : Fin u // a ∈ Sp} → ZMod 2) × ({a : Fin u // a ∉ Sp} → ZMod 2) where
  toFun α := (fun a => α a.1, fun a => α a.1)
  invFun p := extH Sp p.1 + extS Sp p.2
  left_inv α := by
    funext a; by_cases ha : a ∈ Sp <;> simp [extH, extS, ha]
  right_inv p := by
    refine Prod.ext (funext fun a => ?_) (funext fun a => ?_)
    · simp [extH, extS, a.2]
    · simp [extH, extS, a.2]

lemma splitA_sum (α : Aux u) : α = extH Sp (splitA Sp α).1 + extS Sp (splitA Sp α).2 :=
  ((splitA Sp).symm_apply_apply α).symm

variable (n' : Aux u) (i0 : Fin u)

/-- Target summation coordinates: the bits off `Sp`, and one bit along `n'`. -/
def extP : (({a : Fin u // a ∉ Sp} ⊕ Unit) → ZMod 2) →ₗ[ZMod 2] Aux u where
  toFun p := fun a => if ha : a ∈ Sp then n' a * p (.inr ()) else p (.inl ⟨a, ha⟩)
  map_add' p p' := by funext a; by_cases ha : a ∈ Sp <;> simp [ha, mul_add]
  map_smul' c p := by funext a; by_cases ha : a ∈ Sp <;> simp [ha, mul_left_comm]

/-- Target residual coordinates: the bits of `Sp` other than the pivot. -/
def extT (t : {a : Fin u // a ∈ Sp ∧ a ≠ i0} → ZMod 2) : Aux u :=
  fun a => if ha : a ∈ Sp ∧ a ≠ i0 then t ⟨a, ha⟩ else 0

/-- Split the auxiliary bits for a target. -/
def splitB (hi0 : i0 ∈ Sp) (hn0 : n' i0 = 1) :
    Aux u ≃ (({a : Fin u // a ∉ Sp} ⊕ Unit) → ZMod 2) × ({a : Fin u // a ∈ Sp ∧ a ≠ i0} → ZMod 2) where
  toFun α := (Sum.elim (fun a => α a.1) (fun _ => α i0), fun a => α a.1 + n' a.1 * α i0)
  invFun p := extP Sp n' p.1 + extT Sp i0 p.2
  left_inv α := by
    funext a
    by_cases ha : a ∈ Sp
    · by_cases h : a = i0
      · subst h; simp [extP, extT, ha, hn0]
      · simp only [extP, extT, Pi.add_apply, LinearMap.coe_mk, AddHom.coe_mk, dif_pos ha,
          dif_pos (And.intro ha h), Sum.elim_inr]
        linear_combination CharTwo.add_self_eq_zero (n' a * α i0)
    · simp [extP, extT, ha]
  right_inv p := by
    refine Prod.ext (funext fun s => ?_) (funext fun a => ?_)
    · rcases s with a | ⟨⟩
      · simp [extP, extT, a.2]
      · simp [extP, extT, hi0, hn0]
    · simp only [extP, extT, Pi.add_apply, LinearMap.coe_mk, AddHom.coe_mk, dif_pos a.2.1,
        dif_pos a.2, dif_pos hi0, hn0, one_mul, ne_eq, not_true_eq_false, and_false, dif_neg,
        not_false_eq_true, add_zero]
      linear_combination CharTwo.add_self_eq_zero (n' a.1 * p.1 (.inr ()))

lemma splitB_sum (hi0 : i0 ∈ Sp) (hn0 : n' i0 = 1) (α : Aux u) :
    α = extP Sp n' (splitB Sp n' i0 hi0 hn0 α).1 + extT Sp i0 (splitB Sp n' i0 hi0 hn0 α).2 :=
  ((splitB Sp n' i0 hi0 hn0).symm_apply_apply α).symm

/-! ## The factorization -/

lemma dotV_cons (a b : ZMod 2) (α β : Aux u) :
    dotV (Fin.cons a α : V u) (Fin.cons b β) = a * b + auxDot α β := by
  rw [dotV, dotProduct, Fin.sum_univ_succ]; rfl

/-- Source summation directions: the coordinates of `Sp`, through the first chart. -/
def iotaH (d : V u) : ({a : Fin u // a ∈ Sp} → ZMod 2) →ₗ[ZMod 2] V u :=
  (Matrix.mulVecLin (phiOf d)).comp ((consL u).comp (extH Sp))

/-- Source residual: the distinguished bit and the coordinates off `Sp`. -/
def iotaS (d : V u) (p : ZMod 2 × ({a : Fin u // a ∉ Sp} → ZMod 2)) : V u :=
  phiOf d *ᵥ (Fin.cons p.1 (extS Sp p.2) : V u)

/-- Target summation directions. -/
def iotaP (d : V u) : (({a : Fin u // a ∉ Sp} ⊕ Unit) → ZMod 2) →ₗ[ZMod 2] V u :=
  (Matrix.mulVecLin (phiOf d)).comp ((consL u).comp (extP Sp n'))

/-- Target residual. -/
def iotaT (d : V u) (p : ZMod 2 × ({a : Fin u // a ∈ Sp ∧ a ≠ i0} → ZMod 2)) : V u :=
  phiOf d *ᵥ (Fin.cons p.1 (extT Sp i0 p.2) : V u)

lemma phi_split_src (d : V u) (a : Act u) :
    chartMap (phiOf d) a = iotaH Sp d (splitA Sp a.2).1 + iotaS Sp d (a.1, (splitA Sp a.2).2) := by
  have e := splitA_sum Sp a.2
  calc chartMap (phiOf d) a
      = phiOf d *ᵥ (Fin.cons a.1 (extH Sp (splitA Sp a.2).1 + extS Sp (splitA Sp a.2).2) : V u) := by
        rw [← e]; rfl
    _ = _ := by rw [cons_split, Matrix.mulVec_add]; rfl

lemma phi_split_tgt (hi0 : i0 ∈ Sp) (hn0 : n' i0 = 1) (d : V u) (a : Act u) :
    chartMap (phiOf d) a = iotaP Sp n' d (splitB Sp n' i0 hi0 hn0 a.2).1 +
      iotaT Sp i0 d (a.1, (splitB Sp n' i0 hi0 hn0 a.2).2) := by
  have e := splitB_sum Sp n' i0 hi0 hn0 a.2
  calc chartMap (phiOf d) a
      = phiOf d *ᵥ (Fin.cons a.1 (extP Sp n' (splitB Sp n' i0 hi0 hn0 a.2).1 +
          extT Sp i0 (splitB Sp n' i0 hi0 hn0 a.2).2) : V u) := by
        rw [← e]; rfl
    _ = _ := by rw [cons_split, Matrix.mulVec_add]; rfl

/-- The summation directions of sources and targets pair to zero. -/
theorem iotaH_iotaP (dv dw : V u) (h0v : dv 0 = 1) (h0w : dw 0 = 1)
    (hv : ∀ a ∈ Sp, gOf dv a = n' a) (hw0 : ∀ a, a ∉ Sp → gOf dw a = 0)
    (hw1 : auxDot n' (gOf dw) = 1)
    (h : {a : Fin u // a ∈ Sp} → ZMod 2) (p : ({a : Fin u // a ∉ Sp} ⊕ Unit) → ZMod 2) :
    dotV (iotaH Sp dv h) (iotaP Sp n' dw p) = 0 := by
  have e1 : auxDot (extH Sp h) (gOf dv) = auxDot (extH Sp h) n' := by
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : a ∈ Sp
    · rw [hv a ha]
    · simp [extH, ha]
  have e2 : auxDot (extP Sp n' p) (gOf dw) = p (.inr ()) := by
    have : auxDot (extP Sp n' p) (gOf dw) = p (.inr ()) * auxDot n' (gOf dw) := by
      rw [auxDot, auxDot, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      by_cases ha : a ∈ Sp
      · simp only [extP, LinearMap.coe_mk, AddHom.coe_mk, dif_pos ha]; ring
      · rw [hw0 a ha]; ring
    rw [this, hw1, mul_one]
  have e3 : auxDot (extH Sp h) (extP Sp n' p) = p (.inr ()) * auxDot (extH Sp h) n' := by
    rw [auxDot, auxDot, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : a ∈ Sp
    · simp only [extP, LinearMap.coe_mk, AddHom.coe_mk, dif_pos ha]; ring
    · simp [extH, ha]
  have hH : iotaH Sp dv h = phiOf dv *ᵥ (Fin.cons 0 (extH Sp h) : V u) := rfl
  have hP : iotaP Sp n' dw p = phiOf dw *ᵥ (Fin.cons 0 (extP Sp n' p) : V u) := rfl
  rw [hH, hP, phiOf_mulVec dv h0v, phiOf_mulVec dw h0w, dotV_cons]
  have e4 : auxDot (fun a => 0 * gOf dv a + extH Sp h a) (fun a => 0 * gOf dw a + extP Sp n' p a) =
      auxDot (extH Sp h) (extP Sp n' p) := by
    refine Finset.sum_congr rfl fun a _ => by ring
  rw [e4, e1, e2, e3]
  linear_combination CharTwo.add_self_eq_zero (auxDot (extH Sp h) n' * p (.inr ()))

variable {M : ℕ} {ι : Type*}

/-- **Free factorization of the label kernel in explicit coordinates.** For the explicit
charts of routing vectors `d i`, a source `v` and a target `w` of a rectangle described by
`(Sp, n', i0)`: `U = TgtL_w * (MidL * SrcL_v)`, where
* `SrcL_v` sums over the `Sp` coordinates of the auxiliary bits (half 2 after `theta`);
* `TgtL_w` sums over the coordinates off `Sp` and one more bit;
both independent of the query (`actLift_srcM`, `actLift_tgtM`). -/
theorem free_geom (d : ι → V u) (h0 : ∀ i, d i 0 = 1) (hd : ∀ i, dotV (d i) (d i) = 1)
    (j : Fin M) (w v : ι) (hi0 : i0 ∈ Sp) (hn0 : n' i0 = 1)
    (hv : ∀ a ∈ Sp, gOf (d v) a = n' a) (hw0 : ∀ a, a ∉ Sp → gOf (d w) a = 0)
    (hw1 : auxDot n' (gOf (d w)) = 1) :
    U (fun i => chartOf (d i) (h0 i) (hd i)) j w v =
      actLift j (tgtM (splitB Sp n' i0 hi0 hn0)
          ((theta (gOf (d w)) (gOf_self (d w) (h0 w) (hd w))).trans (splitB Sp n' i0 hi0 hn0)) dotI) *
        (actLift j (midM (dotHom u) (iotaS Sp (d v)) (iotaT Sp i0 (d w)) (splitA Sp)
            ((theta (gOf (d v)) (gOf_self (d v) (h0 v) (hd v))).trans (splitA Sp))
            (splitB Sp n' i0 hi0 hn0)
            ((theta (gOf (d w)) (gOf_self (d w) (h0 w) (hd w))).trans (splitB Sp n' i0 hi0 hn0))
            (readL (iotaP Sp n' (d w)) (iotaS Sp (d v)))
            (readL (iotaH Sp (d v)) (iotaT Sp i0 (d w)))) *
          actLift j (srcM (splitA Sp)
            ((theta (gOf (d v)) (gOf_self (d v) (h0 v) (hd v))).trans (splitA Sp)) dotI)) := by
  refine free_letter (fun i => chartOf (d i) (h0 i) (hd i)) j w v (iotaH Sp (d v)) (iotaS Sp (d v))
    (iotaP Sp n' (d w)) (iotaT Sp i0 (d w)) _ _ _ _ ?_ ?_ ?_ ?_ ?_
  · intro a; exact phi_split_src Sp (d v) a
  · intro b
    show chartMap (psiOf (d v)) b = _
    rw [psi_eq_phi_theta (d v) (h0 v) (hd v) b]
    exact phi_split_src Sp (d v) (b.1, thetaFn (gOf (d v)) b.2)
  · intro a; exact phi_split_tgt Sp n' i0 hi0 hn0 (d w) a
  · intro b
    show chartMap (psiOf (d w)) b = _
    rw [psi_eq_phi_theta (d w) (h0 w) (hd w) b]
    exact phi_split_tgt Sp n' i0 hi0 hn0 (d w) (b.1, thetaFn (gOf (d w)) b.2)
  · intro h p
    exact iotaH_iotaP Sp n' (d v) (d w) (h0 v) (h0 w) hv hw0 hw1 h p

end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.FreeGeom =====

-- ===== begin KP.LetterPlans =====
section
/-! # The letter toolbox

Plans for the letter matrices of chunk KP.Letter, each with `Implements`:

* `lift_mul`, `lift_one`, `Implements.seq` (matrices multiply, Walsh bit counts add);
* `implements_lin`: every additive bijection of `Bits A` is one call-free `perm` move
  (`linPlan`; `exists_letterLinPlan_equiv` for linear equivalences of `Bits A`);
* `signPlan φ`: one `scale` for the sign diagonal of any letter function (`implements_sign`);
* `exists_walshPlan S`: one `child` per axis of `S` for `walshU S`.

The statements follow OpenAI's `implements_xor`, `reindex_linear`, `signPass` and the child
lemmas (NearSquareRoot); proofs are written for this tree. -/

namespace OAI.Computability.NearSquareRoot.KernelPass
open Matrix Finset

variable {A : ℕ}

/-! ## `lift` is multiplicative -/

/-- An address is a family of letters indexed by (column, bit). -/
def liftE (A h : ℕ) : Addr A h ≃ (Fin h × Fin 2 → Bits A) where
  toFun y p a := y p.1 a p.2
  invFun z c a t := z (c, t) a
  left_inv _ := rfl
  right_inv _ := rfl

theorem lift_eq (h : ℕ) (M : LMat A) :
    lift h M = (piMat fun _ : Fin h × Fin 2 => M).submatrix (liftE A h) (liftE A h) := by
  ext y x
  simp only [lift, piMat, submatrix_apply, Fintype.prod_prod_type]
  rfl

theorem lift_mul (h : ℕ) (M N : LMat A) : lift h (M * N) = lift h M * lift h N := by
  rw [lift_eq, lift_eq, lift_eq, Matrix.submatrix_mul_equiv, piMat_mul]

theorem lift_one (h : ℕ) : lift h (1 : LMat A) = 1 := by
  rw [lift_eq, piMat_one, submatrix_one_equiv]

theorem qBlk_seq (h : ℕ) (p q : QPlan A 1 1) : qBlk h (.seq p q) = qBlk h p * qBlk h q := by
  ext y x
  simp only [qBlk, QPlan.eval, mul_apply, Fintype.sum_prod_type, Fin.sum_univ_one]

theorem Implements.seq {p q : QPlan A 1 1} {M N : LMat A} {m n : ℕ}
    (hp : Implements p M m) (hq : Implements q N n) : Implements (.seq p q) (M * N) (m + n) := by
  intro h
  rw [qBlk_seq, hp h, hq h, lift_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_add, add_mul]

theorem implements_qId : Implements (idPlan A) 1 0 := by
  intro h; rw [qBlk_qId, lift_one, zero_mul, pow_zero, one_smul]

theorem Implements.congr {p : QPlan A 1 1} {M N : LMat A} {m n : ℕ} (hp : Implements p M m)
    (hM : M = N) (hn : m = n) : Implements p N n := by subst hM; subst hn; exact hp

/-! ## Maps of letters -/

theorem lift_linMat (h : ℕ) (g : Bits A → Bits A) (y x : Addr A h) :
    lift h (linMat g) y x = if ∀ c t, letterAt (y c) t = g (letterAt (x c) t) then 1 else 0 := by
  simp only [lift, linMat]
  split_ifs with hh
  · exact prod_eq_one fun c _ => prod_eq_one fun t _ => if_pos (hh c t)
  · push_neg at hh
    obtain ⟨c, t, hct⟩ := hh
    exact prod_eq_zero (mem_univ c) (prod_eq_zero (mem_univ t) (if_neg hct))

lemma z2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by revert x; decide

/-- An additive bijection of letters, applied to both letters of a column. -/
def letterwise (e : Bits A ≃+ Bits A) : Column A ≃+ Column A where
  toFun c := fun a t => e (letterAt c t) a
  invFun c := fun a t => e.symm (letterAt c t) a
  left_inv c := by funext a t; exact congrFun (e.symm_apply_apply (letterAt c t)) a
  right_inv c := by funext a t; exact congrFun (e.apply_symm_apply (letterAt c t)) a
  map_add' c d := by
    funext a t
    have h : letterAt (c + d) t = letterAt c t + letterAt d t := rfl
    show e (letterAt (c + d) t) a = e (letterAt c t) a + e (letterAt d t) a
    rw [h]; exact congrFun (e.map_add' _ _) a

/-- The free move of an additive bijection of letters. -/
def linPlan (e : Bits A ≃+ Bits A) : QPlan A 1 1 := .perm (letterwise e)

/-- **Linear reindexing.** Every additive bijection of letters is one call-free `perm` move. -/
theorem implements_lin (e : Bits A ≃+ Bits A) : Implements (linPlan e) (linMat e) 0 := by
  intro h
  ext y x
  rw [zero_mul, pow_zero, one_smul, lift_linMat]
  simp only [qBlk, linPlan, eval_perm_apply]
  refine if_congr ⟨fun hh c t => ?_, fun hh => ?_⟩ rfl rfl
  · subst hh; rfl
  · funext c a t; exact congrFun (hh c t) a

/-- Linear reindexing by a linear equivalence of letters. -/
theorem exists_letterLinPlan_equiv (e : Bits A ≃ₗ[ZMod 2] Bits A) :
    ∃ p : QPlan A 1 1, p.calls = 0 ∧ Implements p (linMat e) 0 :=
  ⟨linPlan e.toAddEquiv, rfl, implements_lin e.toAddEquiv⟩

/-! ## Sign diagonals -/


theorem addr_eq_iff {h : ℕ} (y x : Addr A h) :
    (∀ c t, letterAt (y c) t = letterAt (x c) t) ↔ y = x :=
  ⟨fun hh => funext fun c => funext fun a => funext fun t => congrFun (hh c t) a,
    fun e _ _ => by rw [e]⟩

theorem lift_diagonal (h : ℕ) (d : Bits A → ℚ) :
    lift h (Matrix.diagonal d) = Matrix.diagonal fun x => ∏ c : Fin h, ∏ t : Fin 2, d (letterAt (x c) t) := by
  ext y x
  by_cases hyx : y = x
  · subst hyx; simp only [lift, diagonal_apply_eq, Fin.prod_univ_two, Fin.isValue]
  · rw [diagonal_apply, if_neg hyx]
    have : ¬ ∀ c t, letterAt (y c) t = letterAt (x c) t := fun hh => hyx ((addr_eq_iff y x).mp hh)
    push_neg at this
    obtain ⟨c, t, hct⟩ := this
    exact prod_eq_zero (mem_univ c) (prod_eq_zero (mem_univ t) (by rw [diagonal_apply, if_neg hct]))

/-- The sign diagonal `chi(φ(letter))` as one `scale` move. -/
def signPlan (φ : Bits A → ZMod 2) : QPlan A 1 1 :=
  .scale 1 (fun c _ => φ (letterAt c 0) + φ (letterAt c 1)) (fun s => chi (s 0))

theorem signPlan_calls (φ : Bits A → ZMod 2) : (signPlan φ).calls = 0 := rfl

theorem implements_sign (φ : Bits A → ZMod 2) : Implements (signPlan φ) (signMat φ) 0 := by
  intro h
  rw [zero_mul, pow_zero, one_smul, signMat, lift_diagonal]
  ext y x
  simp only [qBlk, signPlan, eval_scale_apply, diagonal_apply]
  by_cases hyx : y = x
  · subst hyx
    rw [if_pos rfl, if_pos rfl, Finset.sum_apply, chi_sum]
    refine prod_congr rfl fun c _ => ?_
    rw [Fin.prod_univ_two, chi_add]
  · rw [if_neg hyx, if_neg (Ne.symm hyx)]

/-! ## Walsh on a set of axes -/

theorem pairMat_chi (u v : Fin 2 → ZMod 2) :
    pairMat u v = (1 / 2 : ℚ) * (chi (u 0 * v 0) * chi (u 1 * v 1)) := by
  rw [← chi_add, pairMat_apply, dot]; ring

theorem walshU_single_apply (a : Fin A) (y x : Bits A) :
    walshU {a} y x = if ∀ b, b ≠ a → y b = x b then chi (y a * x a) else 0 := by
  simp only [walshU, Finset.mem_singleton, Finset.sum_singleton, ne_eq]

theorem axisMat_letters (a : Fin A) (yc xc : Column A) :
    axisMat a yc xc = (1 / 2 : ℚ) * ∏ t : Fin 2, walshU {a} (letterAt yc t) (letterAt xc t) := by
  rw [Fin.prod_univ_two, walshU_single_apply, walshU_single_apply, axisMat, piMat_update]
  have key : (∀ b ≠ a, xc b = yc b) ↔ (∀ b, b ≠ a → letterAt yc 0 b = letterAt xc 0 b) ∧
      (∀ b, b ≠ a → letterAt yc 1 b = letterAt xc 1 b) := by
    constructor
    · intro hh
      exact ⟨fun b hb => by simp [letterAt, hh b hb], fun b hb => by simp [letterAt, hh b hb]⟩
    · rintro ⟨h0, h1⟩ b hb
      funext t
      fin_cases t
      · exact (h0 b hb).symm
      · exact (h1 b hb).symm
  by_cases hc : ∀ b ≠ a, xc b = yc b
  · rw [if_pos hc, if_pos (key.mp hc).1, if_pos (key.mp hc).2, pairMat_chi]; rfl
  · rw [if_neg hc]
    by_cases h0 : ∀ b, b ≠ a → letterAt yc 0 b = letterAt xc 0 b
    · have h1 : ¬ ∀ b, b ≠ a → letterAt yc 1 b = letterAt xc 1 b := fun h1 => hc (key.mpr ⟨h0, h1⟩)
      rw [if_neg h1]; ring
    · rw [if_neg h0]; ring

theorem implements_child (a : Fin A) : Implements (QPlan.child a) (walshU {a}) 1 := by
  intro h
  ext y x
  simp only [qBlk, eval_child_apply, Matrix.smul_apply, smul_eq_mul, lift, one_mul, colPow, piMat]
  simp only [axisMat_letters]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem walshU_empty : walshU (∅ : Finset (Fin A)) = 1 := by
  ext y x
  simp only [walshU, Finset.notMem_empty, not_false_eq_true, forall_const, Finset.sum_empty, one_apply]
  by_cases hyx : y = x
  · subst hyx; simp [chi]
  · rw [if_neg hyx, if_neg (fun hh => hyx (funext hh))]

theorem walshU_insert (a : Fin A) (S : Finset (Fin A)) (ha : a ∉ S) :
    walshU (insert a S) = walshU {a} * walshU S := by
  ext y x
  rw [mul_apply]
  let z : Bits A := fun b => if b = a then x a else y b
  rw [Finset.sum_eq_single z]
  · rw [walshU_single_apply, if_pos (fun b hb => by simp [z, hb])]
    have hz : z a = x a := by simp [z]
    have hsum : (∑ b ∈ S, z b * x b) = ∑ b ∈ S, y b * x b :=
      Finset.sum_congr rfl fun b hb => by
        have : b ≠ a := fun e => ha (e ▸ hb)
        simp [z, this]
    simp only [walshU]
    by_cases hc : ∀ b, b ∉ insert a S → y b = x b
    · have hc' : ∀ b, b ∉ S → z b = x b := by
        intro b hb
        by_cases hba : b = a
        · subst hba; exact hz
        · have : z b = y b := by simp [z, hba]
          rw [this]; exact hc b (by simp [hba, hb])
      rw [if_pos hc, if_pos hc', Finset.sum_insert ha, chi_add, hz, hsum]
    · have hc' : ¬ ∀ b, b ∉ S → z b = x b := by
        intro hh; apply hc; intro b hb
        have hba : b ≠ a := fun e => hb (by simp [e])
        have hbS : b ∉ S := fun e => hb (by simp [e])
        have : z b = y b := by simp [z, hba]
        rw [← this]; exact hh b hbS
      rw [if_neg hc, if_neg hc', mul_zero]
  · intro z' _ hz'
    rw [walshU_single_apply]
    split_ifs with h1
    · have : walshU S z' x = 0 := by
        rw [walshU, if_neg]
        intro h2
        apply hz'
        funext b
        by_cases hba : b = a
        · subst hba; simp [z, h2 b ha]
        · simp [z, hba, (h1 b hba).symm]
      rw [this, mul_zero]
    · rw [zero_mul]
  · simp

/-- **Walsh on a set of axes**: one `child` per axis. -/
theorem exists_walshPlan (S : Finset (Fin A)) :
    ∃ p : QPlan A 1 1, p.calls = S.card ∧ Implements p (walshU S) S.card := by
  induction S using Finset.induction_on with
  | empty => exact ⟨idPlan _, rfl, implements_qId.congr walshU_empty.symm rfl⟩
  | insert a S ha ih =>
    obtain ⟨q, hq0, hq⟩ := ih
    refine ⟨.seq (.child a) q, ?_, ((implements_child a).seq hq).congr (walshU_insert a S ha).symm ?_⟩
    · show 1 + q.calls = _
      rw [hq0, Finset.card_insert_of_notMem ha, add_comm]
    · rw [Finset.card_insert_of_notMem ha, add_comm]

end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.LetterPlans =====

-- ===== begin KP.FreeReal =====
section
/-! # Plans for the free factorization: helpers and the source side

* `linMat` / `signMat` products entrywise; `linEquivOf`; `exists_walshConj` (Walsh on a set of
  axes in a linear chart: `S.card` calls); `exists_monoPlan` (signed linear permutation: 0 calls).
* `onAux f₁ f₂`: act on the auxiliary bits of the two halves, leave the distinguished bits.
* `walshU_aux`: Walsh on the auxiliary positions of a set `T` of auxiliary coordinates.
* `exists_srcPlan`: the source factor of `free_geom` is a plan with `2 * Sp.card` calls. -/

namespace OAI.Computability.NearSquareRoot.KernelPass
open Matrix Finset
open Free


section Generic
variable {A : ℕ}

theorem linMat_inv_mul {f f' : Bits A → Bits A} (h1 : ∀ x, f' (f x) = x) (h2 : ∀ x, f (f' x) = x)
    (K : LMat A) (y x : Bits A) : (linMat f' * K) y x = K (f y) x := by
  rw [mul_apply, Finset.sum_eq_single (f y)]
  · simp [linMat, h1]
  · intro z _ hz
    have : y ≠ f' z := fun e => hz (by rw [e, h2])
    simp [linMat, this]
  · simp

theorem linMat_symm_mul (e : Bits A ≃ Bits A) (K : LMat A) (y x : Bits A) :
    (linMat e.symm * K) y x = K (e y) x := linMat_inv_mul e.symm_apply_apply e.apply_symm_apply K y x

theorem mul_linMat (g : Bits A → Bits A) (K : LMat A) (y x : Bits A) :
    (K * linMat g) y x = K y (g x) := by
  rw [mul_apply, Finset.sum_eq_single (g x)]
  · simp [linMat]
  · intro z _ hz; simp [linMat, hz]
  · simp

theorem mul_signMat (φ : Bits A → ZMod 2) (K : LMat A) (y x : Bits A) :
    (K * signMat φ) y x = K y x * chi (φ x) := by
  rw [signMat, Matrix.mul_diagonal]

theorem signMat_mul (φ : Bits A → ZMod 2) (K : LMat A) (y x : Bits A) :
    (signMat φ * K) y x = chi (φ y) * K y x := by
  rw [signMat, Matrix.diagonal_mul]

/-- An additive bijection of letters as a linear equivalence. -/
def linEquivOf (f f' : Bits A → Bits A) (hadd : ∀ x y, f (x + y) = f x + f y)
    (h1 : Function.LeftInverse f' f) (h2 : Function.RightInverse f' f) :
    Bits A ≃ₗ[ZMod 2] Bits A where
  toFun := f
  invFun := f'
  left_inv := h1
  right_inv := h2
  map_add' := hadd
  map_smul' c x := by
    have f0 : f 0 = 0 := by
      have := hadd 0 0
      rw [add_zero] at this
      exact left_eq_add.mp this
    have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases hc c with rfl | rfl
    · simp [f0]
    · simp

/-- Walsh on the axes of `S` in a linear chart: `S.card` calls. -/
theorem exists_walshConj (e : Bits A ≃ₗ[ZMod 2] Bits A) (S : Finset (Fin A)) :
    ∃ p : QPlan A 1 1, p.calls = S.card ∧
      Implements p (linMat e.symm * (walshU S * linMat e)) S.card := by
  obtain ⟨pe, hpe0, hpe⟩ := exists_letterLinPlan_equiv e
  obtain ⟨pe', hpe'0, hpe'⟩ := exists_letterLinPlan_equiv e.symm
  obtain ⟨pw, hpw0, hpw⟩ := exists_walshPlan S
  refine ⟨.seq pe' (.seq pw pe), ?_, (hpe'.seq (hpw.seq hpe)).congr rfl (by omega)⟩
  show pe'.calls + (pw.calls + pe.calls) = _
  rw [hpe0, hpe'0, hpw0, zero_add, add_zero]

/-- A signed linear permutation of letters: 0 calls. -/
theorem exists_monoPlan (e : Bits A ≃ₗ[ZMod 2] Bits A) (φ : Bits A → ZMod 2) :
    ∃ p : QPlan A 1 1, p.calls = 0 ∧ Implements p (linMat e * signMat φ) 0 := by
  obtain ⟨pe, hpe0, hpe⟩ := exists_letterLinPlan_equiv e
  refine ⟨.seq pe (signPlan φ), ?_, (hpe.seq (implements_sign φ)).congr rfl rfl⟩
  show pe.calls + (signPlan φ).calls = _
  rw [hpe0, signPlan_calls]

end Generic

variable {M u : ℕ}

/-! ## Acting on the auxiliary bits -/

/-- Apply `f₁` to the auxiliary bits of half 1 and `f₂` to those of half 2. -/
def onAux (f₁ f₂ : Aux u → Aux u) (x : Bits (2 * (M + u))) : Bits (2 * (M + u)) := fun i =>
  match (idxE M u).symm i with
  | .inl (.inr a) => f₁ (aux1 x) a
  | .inr (.inr a) => f₂ (aux2 x) a
  | _ => x i

lemma onAux_a1 (f₁ f₂ : Aux u → Aux u) (x : Bits (2 * (M + u))) (a : Fin u) :
    onAux f₁ f₂ x (pos1 (apair a)) = f₁ (aux1 x) a := by
  simp only [onAux, ← idxE_lr, Equiv.symm_apply_apply]
lemma onAux_a2 (f₁ f₂ : Aux u → Aux u) (x : Bits (2 * (M + u))) (a : Fin u) :
    onAux f₁ f₂ x (pos2 (apair a)) = f₂ (aux2 x) a := by
  simp only [onAux, ← idxE_rr, Equiv.symm_apply_apply]
lemma onAux_d1 (f₁ f₂ : Aux u → Aux u) (x : Bits (2 * (M + u))) (i : Fin M) :
    onAux f₁ f₂ x (pos1 (dpair i)) = x (pos1 (dpair i)) := by
  simp only [onAux, ← idxE_ll, Equiv.symm_apply_apply]
lemma onAux_d2 (f₁ f₂ : Aux u → Aux u) (x : Bits (2 * (M + u))) (i : Fin M) :
    onAux f₁ f₂ x (pos2 (dpair i)) = x (pos2 (dpair i)) := by
  simp only [onAux, ← idxE_rl, Equiv.symm_apply_apply]

lemma aux1_onAux (f₁ f₂ : Aux u → Aux u) (x : Bits (2 * (M + u))) :
    aux1 (onAux f₁ f₂ x) = f₁ (aux1 x) := funext fun a => onAux_a1 f₁ f₂ x a
lemma aux2_onAux (f₁ f₂ : Aux u → Aux u) (x : Bits (2 * (M + u))) :
    aux2 (onAux f₁ f₂ x) = f₂ (aux2 x) := funext fun a => onAux_a2 f₁ f₂ x a

/-- Two letters agree when they agree at the four kinds of positions. -/
lemma bits_ext {y x : Bits (2 * (M + u))}
    (h1 : ∀ i : Fin M, y (pos1 (dpair i)) = x (pos1 (dpair i)))
    (h2 : ∀ i : Fin M, y (pos2 (dpair i)) = x (pos2 (dpair i)))
    (h3 : aux1 y = aux1 x) (h4 : aux2 y = aux2 x) : y = x := by
  funext i
  obtain ⟨s, rfl⟩ := (idxE M u).surjective i
  rcases s with (i' | a) | (i' | a)
  · rw [idxE_ll]; exact h1 i'
  · rw [idxE_lr]; exact congrFun h3 a
  · rw [idxE_rl]; exact h2 i'
  · rw [idxE_rr]; exact congrFun h4 a

lemma onAux_comp (f₁ f₂ g₁ g₂ : Aux u → Aux u) (x : Bits (2 * (M + u))) :
    onAux f₁ f₂ (onAux g₁ g₂ x) = onAux (f₁ ∘ g₁) (f₂ ∘ g₂) x := by
  apply bits_ext
  · intro i; rw [onAux_d1, onAux_d1, onAux_d1]
  · intro i; rw [onAux_d2, onAux_d2, onAux_d2]
  · rw [aux1_onAux, aux1_onAux, aux1_onAux]; rfl
  · rw [aux2_onAux, aux2_onAux, aux2_onAux]; rfl

lemma onAux_id (x : Bits (2 * (M + u))) : onAux id id x = x := by
  apply bits_ext
  · intro i; rw [onAux_d1]
  · intro i; rw [onAux_d2]
  · rw [aux1_onAux]; rfl
  · rw [aux2_onAux]; rfl

lemma onAux_add (f₁ f₂ : Aux u → Aux u) (h₁ : ∀ α β, f₁ (α + β) = f₁ α + f₁ β)
    (h₂ : ∀ α β, f₂ (α + β) = f₂ α + f₂ β) (x y : Bits (2 * (M + u))) :
    onAux f₁ f₂ (x + y) = onAux f₁ f₂ x + onAux f₁ f₂ y := by
  have e1 : aux1 (x + y) = aux1 x + aux1 y := rfl
  have e2 : aux2 (x + y) = aux2 x + aux2 y := rfl
  apply bits_ext
  · intro i; rw [Pi.add_apply, onAux_d1, onAux_d1, onAux_d1]; rfl
  · intro i; rw [Pi.add_apply, onAux_d2, onAux_d2, onAux_d2]; rfl
  · rw [aux1_onAux, e1, h₁]
    funext a
    show _ = onAux f₁ f₂ x (pos1 (apair a)) + onAux f₁ f₂ y (pos1 (apair a))
    rw [onAux_a1, onAux_a1]; rfl
  · rw [aux2_onAux, e2, h₂]
    funext a
    show _ = onAux f₁ f₂ x (pos2 (apair a)) + onAux f₁ f₂ y (pos2 (apair a))
    rw [onAux_a2, onAux_a2]; rfl

/-- `onAux` of additive bijections as a linear equivalence of letters. -/
def onAuxL (f₁ f₂ g₁ g₂ : Aux u → Aux u) (h₁ : ∀ α β, f₁ (α + β) = f₁ α + f₁ β)
    (h₂ : ∀ α β, f₂ (α + β) = f₂ α + f₂ β) (l₁ : Function.LeftInverse g₁ f₁)
    (l₂ : Function.LeftInverse g₂ f₂) (r₁ : Function.RightInverse g₁ f₁)
    (r₂ : Function.RightInverse g₂ f₂) : Bits (2 * (M + u)) ≃ₗ[ZMod 2] Bits (2 * (M + u)) :=
  linEquivOf (onAux f₁ f₂) (onAux g₁ g₂) (onAux_add f₁ f₂ h₁ h₂)
    (fun x => by
      rw [onAux_comp, show g₁ ∘ f₁ = id from funext l₁, show g₂ ∘ f₂ = id from funext l₂, onAux_id])
    (fun x => by
      rw [onAux_comp, show f₁ ∘ g₁ = id from funext r₁, show f₂ ∘ g₂ = id from funext r₂, onAux_id])

lemma distEq_onAux (f₁ f₂ : Aux u → Aux u) (y x : Bits (2 * (M + u))) :
    DistEq (onAux f₁ f₂ y) (onAux f₁ f₂ x) ↔ DistEq y x := by
  simp only [DistEq, onAux_d1, onAux_d2]

/-! ## Walsh on auxiliary positions -/

/-- The auxiliary positions (both halves) of a set of auxiliary coordinates. -/
def setAux (M : ℕ) (T : Finset (Fin u)) : Finset (Fin (2 * (M + u))) :=
  T.map ⟨fun a => pos1 (apair a), fun a b h => apair_inj (pos1_inj h)⟩ ∪
    T.map ⟨fun a => pos2 (apair a), fun a b h => apair_inj (pos2_inj h)⟩

lemma setAux_card (T : Finset (Fin u)) : (setAux M T).card = 2 * T.card := by
  rw [setAux, Finset.card_union_of_disjoint, Finset.card_map, Finset.card_map, two_mul]
  rw [Finset.disjoint_left]
  intro i h1 h2
  simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at h1 h2
  obtain ⟨a, _, rfl⟩ := h1
  obtain ⟨b, _, hb⟩ := h2
  exact pos1_ne_pos2 _ _ hb.symm

theorem walshU_aux (T : Finset (Fin u)) (y x : Bits (2 * (M + u))) :
    walshU (setAux M T) y x =
      if DistEq y x ∧ (∀ a, a ∉ T → aux1 y a = aux1 x a) ∧ (∀ a, a ∉ T → aux2 y a = aux2 x a) then
        chi ((∑ a ∈ T, aux1 y a * aux1 x a) + ∑ a ∈ T, aux2 y a * aux2 x a)
      else 0 := by
  have hdisj : Disjoint (T.map ⟨fun a => pos1 (apair (M := M) a), fun a b h => apair_inj (pos1_inj h)⟩)
      (T.map ⟨fun a => pos2 (apair (M := M) a), fun a b h => apair_inj (pos2_inj h)⟩) := by
    rw [Finset.disjoint_left]
    intro i h1 h2
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at h1 h2
    obtain ⟨a, _, rfl⟩ := h1
    obtain ⟨b, _, hb⟩ := h2
    exact pos1_ne_pos2 _ _ hb.symm
  have hsum : (∑ i ∈ setAux M T, y i * x i) =
      (∑ a ∈ T, aux1 y a * aux1 x a) + ∑ a ∈ T, aux2 y a * aux2 x a := by
    rw [setAux, Finset.sum_union hdisj, Finset.sum_map, Finset.sum_map]; rfl
  have hmem1 : ∀ a, pos1 (apair (M := M) a) ∈ setAux M T ↔ a ∈ T := by
    intro a
    simp only [setAux, Finset.mem_union, Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro (⟨b, hb, h⟩ | ⟨b, _, h⟩)
      · rwa [← apair_inj (pos1_inj h)]
      · exact absurd h.symm (pos1_ne_pos2 _ _)
    · intro ha; exact Or.inl ⟨a, ha, rfl⟩
  have hmem2 : ∀ a, pos2 (apair (M := M) a) ∈ setAux M T ↔ a ∈ T := by
    intro a
    simp only [setAux, Finset.mem_union, Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro (⟨b, _, h⟩ | ⟨b, hb, h⟩)
      · exact absurd h (pos1_ne_pos2 _ _)
      · rwa [← apair_inj (pos2_inj h)]
    · intro ha; exact Or.inr ⟨a, ha, rfl⟩
  have hd1 : ∀ i : Fin M, pos1 (dpair (u := u) i) ∉ setAux M T := by
    intro i h
    simp only [setAux, Finset.mem_union, Finset.mem_map, Function.Embedding.coeFn_mk] at h
    rcases h with ⟨b, _, h⟩ | ⟨b, _, h⟩
    · exact dpair_ne_apair i b (pos1_inj h).symm
    · exact pos1_ne_pos2 _ _ h.symm
  have hd2 : ∀ i : Fin M, pos2 (dpair (u := u) i) ∉ setAux M T := by
    intro i h
    simp only [setAux, Finset.mem_union, Finset.mem_map, Function.Embedding.coeFn_mk] at h
    rcases h with ⟨b, _, h⟩ | ⟨b, _, h⟩
    · exact pos1_ne_pos2 _ _ h
    · exact dpair_ne_apair i b (pos2_inj h).symm
  have hcond : (∀ i, i ∉ setAux M T → y i = x i) ↔
      (DistEq y x ∧ (∀ a, a ∉ T → aux1 y a = aux1 x a) ∧ (∀ a, a ∉ T → aux2 y a = aux2 x a)) := by
    constructor
    · intro h
      exact ⟨fun i => ⟨h _ (hd1 i), h _ (hd2 i)⟩,
        fun a ha => h _ (fun hh => ha ((hmem1 a).mp hh)),
        fun a ha => h _ (fun hh => ha ((hmem2 a).mp hh))⟩
    · rintro ⟨hD, h1, h2⟩ i hi
      obtain ⟨s, rfl⟩ := (idxE M u).surjective i
      rcases s with (i' | a) | (i' | a)
      · rw [idxE_ll]; exact (hD i').1
      · rw [idxE_lr] at hi ⊢; exact h1 a (fun ha => hi ((hmem1 a).mpr ha))
      · rw [idxE_rl]; exact (hD i').2
      · rw [idxE_rr] at hi ⊢; exact h2 a (fun ha => hi ((hmem2 a).mpr ha))
  simp only [walshU, hsum]
  by_cases hc : ∀ i, i ∉ setAux M T → y i = x i
  · rw [if_pos hc, if_pos (hcond.mp hc)]
  · rw [if_neg hc, if_neg (fun h => hc (hcond.mpr h))]

end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.FreeReal =====

-- ===== begin KP.FreeSrc =====
section
/-! # The source plan of the free factorization

`srcL_eq`: the source letter matrix of `free_geom` is
`linMat E⁻¹ * (walshU (setAux Sp) * linMat E) * signMat (auxiliary chirp)`, where `E` applies
`thetaFn g` to the auxiliary bits of half 2. `exists_srcPlan`: a plan with `2 * Sp.card`
calls implementing it, the same plan for every query. -/

namespace OAI.Computability.NearSquareRoot.KernelPass
open Matrix Finset
open Free

variable {M u : ℕ}

theorem linMat_lsymm_mul {A : ℕ} (e : Bits A ≃ₗ[ZMod 2] Bits A) (K : LMat A) (y x : Bits A) :
    (linMat e.symm * K) y x = K (e y) x := linMat_symm_mul e.toEquiv K y x

lemma theta_apply (g : Aux u) (hg : auxDot g g = 0) (β : Aux u) : theta g hg β = thetaFn g β := rfl

variable (Sp : Finset (Fin u))

lemma splitA_snd_eq_iff (α β : Aux u) :
    (splitA Sp α).2 = (splitA Sp β).2 ↔ ∀ a, a ∉ Sp → α a = β a := by
  constructor
  · intro h a ha; exact congrFun h ⟨a, ha⟩
  · intro h; funext a; exact h a.1 a.2

lemma dotI_splitA (α β : Aux u) :
    dotI (splitA Sp α).1 (splitA Sp β).1 = ∑ a ∈ Sp, α a * β a :=
  (Finset.sum_subtype Sp (fun _ => Iff.rfl) (fun a => α a * β a)).symm

/-- The chart of the source side: `thetaFn g` on the auxiliary bits of half 2. -/
def srcE (M : ℕ) (g : Aux u) (hg : auxDot g g = 0) :
    Bits (2 * (M + u)) ≃ₗ[ZMod 2] Bits (2 * (M + u)) :=
  onAuxL id (thetaFn g) id (thetaFn g) (fun _ _ => rfl)
    (fun α β => by
      funext a
      simp only [thetaFn, Pi.add_apply]
      have : auxDot (α + β) g = auxDot α g + auxDot β g := by
        simp only [auxDot, Pi.add_apply, add_mul, Finset.sum_add_distrib]
      rw [this]; ring)
    (fun _ => rfl) (thetaFn_invol g hg) (fun _ => rfl) (thetaFn_invol g hg)

/-- The auxiliary chirp of a letter. -/
def auxChirp (x : Bits (2 * (M + u))) : ZMod 2 := auxDot (aux1 x) (aux2 x)

theorem srcL_eq (g : Aux u) (hg : auxDot g g = 0) (j : Fin M) :
    actLift j (srcM (splitA Sp) ((theta g hg).trans (splitA Sp)) dotI) =
      (linMat (srcE M g hg).symm * (walshU (setAux M Sp) * linMat (srcE M g hg))) *
        signMat auxChirp := by
  ext y x
  rw [mul_signMat, linMat_lsymm_mul, mul_linMat, actLift_srcM, walshU_aux]
  have ey1 : aux1 (srcE M g hg y) = aux1 y := aux1_onAux id (thetaFn g) y
  have ex1 : aux1 (srcE M g hg x) = aux1 x := aux1_onAux id (thetaFn g) x
  have ey2 : aux2 (srcE M g hg y) = thetaFn g (aux2 y) := aux2_onAux id (thetaFn g) y
  have ex2 : aux2 (srcE M g hg x) = thetaFn g (aux2 x) := aux2_onAux id (thetaFn g) x
  have hD : DistEq (srcE M g hg y) (srcE M g hg x) ↔ DistEq y x := distEq_onAux id (thetaFn g) y x
  rw [ey1, ex1, ey2, ex2]
  simp only [Equiv.trans_apply, theta_apply, splitA_snd_eq_iff, dotI_splitA, hD]
  split_ifs with hc
  · rw [chi_add, auxChirp]
    exact congrArg (chi · * chi (auxDot (aux1 x) (aux2 x)))
      (congrArg₂ (· + ·) (Finset.sum_congr rfl fun a _ => mul_comm _ _)
        (Finset.sum_congr rfl fun a _ => mul_comm _ _))
  · rw [zero_mul]

/-- **The source plan**: `2 * Sp.card` calls, the same for every query. -/
theorem exists_srcPlan (g : Aux u) (hg : auxDot g g = 0) :
    ∃ p : QPlan (2 * (M + u)) 1 1, p.calls = 2 * Sp.card ∧ ∀ j : Fin M,
      Implements p (actLift j (srcM (splitA Sp) ((theta g hg).trans (splitA Sp)) dotI))
        (2 * Sp.card) := by
  obtain ⟨pw, hpw0, hpw⟩ := exists_walshConj (srcE M g hg) (setAux M Sp)
  refine ⟨.seq pw (signPlan auxChirp), ?_, fun j => ?_⟩
  · simp [QPlan.calls, hpw0, signPlan_calls, setAux_card]
  · exact (hpw.seq (implements_sign auxChirp)).congr (srcL_eq Sp g hg j).symm
      (by simp [setAux_card])

end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.FreeSrc =====

-- ===== begin KP.FreeTgt =====
section
/-! # The target plan of the free factorization

The target summation coordinates are the auxiliary coordinates off `Sp` and the pivot `i0`,
after the shear `shFn` (`α a ↦ α a + n' a * α i0` on `Sp \ {i0}`); half 2 goes through
`thetaFn g` first. `tgtL_eq`: the target letter matrix of `free_geom` is
`signMat (auxiliary chirp) * (linMat E⁻¹ * (walshU (setAux T) * linMat E))`, `T = insert i0 Spᶜ`.
`exists_tgtPlan`: a plan with `2 * ((u - Sp.card) + 1)` calls, the same for every query. -/

namespace OAI.Computability.NearSquareRoot.KernelPass
open Matrix Finset
open Free

variable {M u : ℕ} (Sp : Finset (Fin u)) (n' : Aux u) (i0 : Fin u)

/-- The shear of the target chart. -/
def shFn (α : Aux u) : Aux u := fun a => if a ∈ Sp ∧ a ≠ i0 then α a + n' a * α i0 else α a

lemma shFn_i0 (α : Aux u) : shFn Sp n' i0 α i0 = α i0 := by simp [shFn]

lemma shFn_invol : Function.Involutive (shFn Sp n' i0) := by
  intro α
  funext a
  by_cases ha : a ∈ Sp ∧ a ≠ i0
  · show shFn Sp n' i0 (shFn Sp n' i0 α) a = α a
    rw [shFn, if_pos ha, shFn_i0, shFn, if_pos ha]
    linear_combination CharTwo.add_self_eq_zero (n' a * α i0)
  · show shFn Sp n' i0 (shFn Sp n' i0 α) a = α a
    rw [shFn, if_neg ha, shFn, if_neg ha]

lemma shFn_add (α β : Aux u) : shFn Sp n' i0 (α + β) = shFn Sp n' i0 α + shFn Sp n' i0 β := by
  funext a
  by_cases ha : a ∈ Sp ∧ a ≠ i0
  · simp only [shFn, if_pos ha, Pi.add_apply]; ring
  · simp only [shFn, if_neg ha, Pi.add_apply]

lemma thetaFn_add (g : Aux u) (α β : Aux u) : thetaFn g (α + β) = thetaFn g α + thetaFn g β := by
  funext a
  simp only [thetaFn, Pi.add_apply]
  have : auxDot (α + β) g = auxDot α g + auxDot β g := by
    simp only [auxDot, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  rw [this]; ring

/-- The target summation coordinates. -/
def tgtSet : Finset (Fin u) := insert i0 Spᶜ

lemma not_mem_tgtSet (hi0 : i0 ∈ Sp) (a : Fin u) : a ∉ tgtSet Sp i0 ↔ a ∈ Sp ∧ a ≠ i0 := by
  simp only [tgtSet, Finset.mem_insert, Finset.mem_compl, not_or, not_not]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

lemma tgtSet_card (hi0 : i0 ∈ Sp) : (tgtSet Sp i0).card = (u - Sp.card) + 1 := by
  rw [tgtSet, Finset.card_insert_of_notMem (by simp [hi0]), Finset.card_compl, Fintype.card_fin]

variable (hi0 : i0 ∈ Sp) (hn0 : n' i0 = 1)

lemma splitB_snd_eq_iff (α β : Aux u) :
    (splitB Sp n' i0 hi0 hn0 α).2 = (splitB Sp n' i0 hi0 hn0 β).2 ↔
      ∀ a, a ∉ tgtSet Sp i0 → shFn Sp n' i0 α a = shFn Sp n' i0 β a := by
  constructor
  · intro h a ha
    have ha' := (not_mem_tgtSet Sp i0 hi0 a).mp ha
    have := congrFun h ⟨a, ha'⟩
    simp only [shFn, if_pos ha']
    exact this
  · intro h
    funext a
    have := h a.1 ((not_mem_tgtSet Sp i0 hi0 a.1).mpr a.2)
    simp only [shFn, if_pos a.2] at this
    exact this

lemma dotI_splitB (α β : Aux u) :
    dotI (splitB Sp n' i0 hi0 hn0 α).1 (splitB Sp n' i0 hi0 hn0 β).1 =
      ∑ a ∈ tgtSet Sp i0, shFn Sp n' i0 α a * shFn Sp n' i0 β a := by
  have hsh : ∀ γ : Aux u, ∀ a ∈ tgtSet Sp i0, shFn Sp n' i0 γ a = γ a := by
    intro γ a ha
    have : ¬ (a ∈ Sp ∧ a ≠ i0) := fun h => (not_mem_tgtSet Sp i0 hi0 a).mpr h ha
    simp only [shFn, if_neg this]
  rw [Finset.sum_congr rfl fun a ha => by rw [hsh α a ha, hsh β a ha]]
  rw [tgtSet, Finset.sum_insert (by simp [hi0]), dotI, Fintype.sum_sum_type]
  simp only [splitB, Equiv.coe_fn_mk, Sum.elim_inl, Sum.elim_inr, Finset.univ_unique,
    Finset.sum_singleton]
  rw [add_comm]
  congr 1
  exact (Finset.sum_subtype Spᶜ (fun a => by simp) (fun a => α a * β a)).symm

/-- The chart of the target side. -/
def tgtE (M : ℕ) (g : Aux u) (hg : auxDot g g = 0) :
    Bits (2 * (M + u)) ≃ₗ[ZMod 2] Bits (2 * (M + u)) :=
  onAuxL (shFn Sp n' i0) (shFn Sp n' i0 ∘ thetaFn g) (shFn Sp n' i0) (thetaFn g ∘ shFn Sp n' i0)
    (shFn_add Sp n' i0)
    (fun α β => by
      show shFn Sp n' i0 (thetaFn g (α + β)) = _
      rw [thetaFn_add, shFn_add]; rfl)
    (shFn_invol Sp n' i0)
    (fun α => by
      show thetaFn g (shFn Sp n' i0 (shFn Sp n' i0 (thetaFn g α))) = α
      rw [shFn_invol Sp n' i0, thetaFn_invol g hg])
    (shFn_invol Sp n' i0)
    (fun α => by
      show shFn Sp n' i0 (thetaFn g (thetaFn g (shFn Sp n' i0 α))) = α
      rw [thetaFn_invol g hg, shFn_invol Sp n' i0])

theorem tgtL_eq (g : Aux u) (hg : auxDot g g = 0) (j : Fin M) :
    actLift j (tgtM (splitB Sp n' i0 hi0 hn0) ((theta g hg).trans (splitB Sp n' i0 hi0 hn0)) dotI) =
      signMat auxChirp * (linMat (tgtE Sp n' i0 M g hg).symm *
        (walshU (setAux M (tgtSet Sp i0)) * linMat (tgtE Sp n' i0 M g hg))) := by
  ext y x
  rw [signMat_mul, linMat_lsymm_mul, mul_linMat, actLift_tgtM, walshU_aux]
  have ey1 : aux1 (tgtE Sp n' i0 M g hg y) = shFn Sp n' i0 (aux1 y) := aux1_onAux _ _ y
  have ex1 : aux1 (tgtE Sp n' i0 M g hg x) = shFn Sp n' i0 (aux1 x) := aux1_onAux _ _ x
  have ey2 : aux2 (tgtE Sp n' i0 M g hg y) = shFn Sp n' i0 (thetaFn g (aux2 y)) := aux2_onAux _ _ y
  have ex2 : aux2 (tgtE Sp n' i0 M g hg x) = shFn Sp n' i0 (thetaFn g (aux2 x)) := aux2_onAux _ _ x
  have hD : DistEq (tgtE Sp n' i0 M g hg y) (tgtE Sp n' i0 M g hg x) ↔ DistEq y x :=
    distEq_onAux _ _ y x
  rw [ey1, ex1, ey2, ex2]
  simp only [Equiv.trans_apply, theta_apply, splitB_snd_eq_iff, dotI_splitB, hD]
  split_ifs with hc
  · rw [chi_add, auxChirp, mul_comm]
    exact congrArg (chi (auxDot (aux1 y) (aux2 y)) * chi ·)
      (congrArg₂ (· + ·) (Finset.sum_congr rfl fun a _ => mul_comm _ _)
        (Finset.sum_congr rfl fun a _ => mul_comm _ _))
  · rw [mul_zero]

/-- **The target plan**: `2 * ((u - Sp.card) + 1)` calls, the same for every query. -/
theorem exists_tgtPlan (g : Aux u) (hg : auxDot g g = 0) :
    ∃ p : QPlan (2 * (M + u)) 1 1, p.calls = 2 * ((u - Sp.card) + 1) ∧ ∀ j : Fin M,
      Implements p (actLift j (tgtM (splitB Sp n' i0 hi0 hn0)
        ((theta g hg).trans (splitB Sp n' i0 hi0 hn0)) dotI)) (2 * ((u - Sp.card) + 1)) := by
  obtain ⟨pw, hpw0, hpw⟩ := exists_walshConj (tgtE Sp n' i0 M g hg) (setAux M (tgtSet Sp i0))
  refine ⟨.seq (signPlan auxChirp) pw, ?_, fun j => ?_⟩
  · simp [QPlan.calls, hpw0, signPlan_calls, setAux_card, tgtSet_card Sp i0 hi0]
  · exact ((implements_sign auxChirp).seq hpw).congr (tgtL_eq Sp n' i0 hi0 hn0 g hg j).symm
      (by simp [setAux_card, tgtSet_card Sp i0 hi0])

end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.FreeTgt =====

-- ===== begin KP.FreeMidBij =====
section
/-! # The two residual pairings of a free rectangle are bijections

`bT = readL (iotaH …) (iotaT …)` maps the target residual `(t₀, t)` to coordinates on `Sp`;
`bS = readL (iotaP …) (iotaS …)` maps the source residual `(s₀, s)` to the target summation
coordinates. Both are additive with trivial kernel between spaces of the same size, so they
are additive equivalences (`bTe`, `bSe`). This is what makes the middle factor a signed
linear permutation. -/

namespace OAI.Computability.NearSquareRoot.KernelPass
open Matrix Finset
open Free

variable {u : ℕ} (Sp : Finset (Fin u)) (n' : Aux u) (i0 : Fin u)

lemma cons_add (a b : ZMod 2) (α β : Aux u) :
    (Fin.cons (a + b) (α + β) : V u) = Fin.cons a α + Fin.cons b β := by
  funext i; refine Fin.cases ?_ (fun c => ?_) i <;> simp

lemma dotV_phi_cons (d : V u) (h0 : d 0 = 1) (a0 : ZMod 2) (α : Aux u) (yv : V u) :
    dotV (phiOf d *ᵥ (Fin.cons a0 α : V u)) yv =
      (a0 + auxDot α (gOf d)) * yv 0 + ∑ b, (a0 * gOf d b + α b) * yv b.succ := by
  rw [phiOf_mulVec d h0, dotV, dotProduct, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

lemma extS_add (s s' : {a : Fin u // a ∉ Sp} → ZMod 2) :
    extS Sp (s + s') = extS Sp s + extS Sp s' := by
  funext a; by_cases ha : a ∈ Sp <;> simp [extS, ha]

lemma extT_add (t t' : {a : Fin u // a ∈ Sp ∧ a ≠ i0} → ZMod 2) :
    extT Sp i0 (t + t') = extT Sp i0 t + extT Sp i0 t' := by
  funext a; by_cases ha : a ∈ Sp ∧ a ≠ i0 <;> simp [extT, ha]

lemma iotaS_add (d : V u) (p q : ZMod 2 × ({a : Fin u // a ∉ Sp} → ZMod 2)) :
    iotaS Sp d (p + q) = iotaS Sp d p + iotaS Sp d q := by
  simp only [iotaS, Prod.fst_add, Prod.snd_add, extS_add, cons_add, Matrix.mulVec_add]

lemma iotaT_add (d : V u) (p q : ZMod 2 × ({a : Fin u // a ∈ Sp ∧ a ≠ i0} → ZMod 2)) :
    iotaT Sp i0 d (p + q) = iotaT Sp i0 d p + iotaT Sp i0 d q := by
  simp only [iotaT, Prod.fst_add, Prod.snd_add, extT_add, cons_add, Matrix.mulVec_add]

lemma readL_add {I X : Type*} [DecidableEq I] [Add X] (f : (I → ZMod 2) →ₗ[ZMod 2] V u)
    (g : X → V u) (hg : ∀ x y, g (x + y) = g x + g y) (x y : X) :
    readL f g (x + y) = readL f g x + readL f g y := by
  funext a
  simp only [readL, hg, dotV, dotProduct_add, Pi.add_apply]

/-! ## Values of the pairings -/

lemma extH_basis (a : Fin u) (ha : a ∈ Sp) :
    extH Sp (fun k => if (⟨a, ha⟩ : {a : Fin u // a ∈ Sp}) = k then 1 else 0) =
      fun b => if a = b then 1 else 0 := by
  funext b
  by_cases hb : b ∈ Sp
  · simp [extH, hb, Subtype.ext_iff]
  · have : a ≠ b := fun h => hb (h ▸ ha)
    simp [extH, hb, this]

lemma extP_basis_inl (a : Fin u) (ha : a ∉ Sp) :
    extP Sp n' (fun k => if (Sum.inl ⟨a, ha⟩ : {a : Fin u // a ∉ Sp} ⊕ Unit) = k then 1 else 0) =
      fun b => if a = b then 1 else 0 := by
  funext b
  by_cases hb : b ∈ Sp
  · have : a ≠ b := fun h => ha (h ▸ hb)
    simp [extP, hb, this]
  · simp [extP, hb, Subtype.ext_iff]

lemma extP_basis_inr :
    extP Sp n' (fun k => if (Sum.inr () : {a : Fin u // a ∉ Sp} ⊕ Unit) = k then 1 else 0) =
      fun b => if b ∈ Sp then n' b else 0 := by
  funext b
  by_cases hb : b ∈ Sp <;> simp [extP, hb]

lemma auxDot_ind (a : Fin u) (g : Aux u) : auxDot (fun b => if a = b then 1 else 0) g = g a := by
  simp only [auxDot, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- The value of `bT`. -/
theorem bT_apply (dv dw : V u) (h0v : dv 0 = 1) (h0w : dw 0 = 1)
    (p : ZMod 2 × ({a : Fin u // a ∈ Sp ∧ a ≠ i0} → ZMod 2)) (a : Fin u) (ha : a ∈ Sp) :
    readL (iotaH Sp dv) (iotaT Sp i0 dw) p ⟨a, ha⟩ =
      gOf dv a * (p.1 + auxDot (extT Sp i0 p.2) (gOf dw)) +
        (p.1 * gOf dw a + extT Sp i0 p.2 a) := by
  have hH : iotaH Sp dv (fun k => if (⟨a, ha⟩ : {a : Fin u // a ∈ Sp}) = k then 1 else 0) =
      phiOf dv *ᵥ (Fin.cons 0 (fun b => if a = b then 1 else 0) : V u) := by
    show phiOf dv *ᵥ (Fin.cons 0 (extH Sp _) : V u) = _
    rw [extH_basis]
  rw [readL, hH, dotV_phi_cons dv h0v, auxDot_ind, iotaT, phiOf_mulVec dw h0w]
  simp only [Fin.cons_zero, Fin.cons_succ, zero_add, zero_mul, ite_mul, one_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- The value of `bS` at a coordinate off `Sp`. -/
theorem bS_apply_inl (dv dw : V u) (h0v : dv 0 = 1) (h0w : dw 0 = 1)
    (hw0 : ∀ a, a ∉ Sp → gOf dw a = 0)
    (p : ZMod 2 × ({a : Fin u // a ∉ Sp} → ZMod 2)) (a : Fin u) (ha : a ∉ Sp) :
    readL (iotaP Sp n' dw) (iotaS Sp dv) p (.inl ⟨a, ha⟩) = p.1 * gOf dv a + p.2 ⟨a, ha⟩ := by
  have hP : iotaP Sp n' dw (fun k => if (Sum.inl ⟨a, ha⟩ : {a : Fin u // a ∉ Sp} ⊕ Unit) = k
      then 1 else 0) = phiOf dw *ᵥ (Fin.cons 0 (fun b => if a = b then 1 else 0) : V u) := by
    show phiOf dw *ᵥ (Fin.cons 0 (extP Sp n' _) : V u) = _
    rw [extP_basis_inl]
  rw [readL, hP, dotV_phi_cons dw h0w, auxDot_ind, hw0 a ha, iotaS, phiOf_mulVec dv h0v]
  simp only [Fin.cons_zero, Fin.cons_succ, zero_add, zero_mul, ite_mul, one_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, extS, dif_neg ha]

/-- The value of `bS` at the coordinate along `n'`. -/
theorem bS_apply_inr (dv dw : V u) (h0v : dv 0 = 1) (h0w : dw 0 = 1)
    (hw0 : ∀ a, a ∉ Sp → gOf dw a = 0) (hw1 : auxDot n' (gOf dw) = 1)
    (p : ZMod 2 × ({a : Fin u // a ∉ Sp} → ZMod 2)) :
    readL (iotaP Sp n' dw) (iotaS Sp dv) p (.inr ()) =
      (p.1 + auxDot (extS Sp p.2) (gOf dv)) +
        ∑ b, (if b ∈ Sp then n' b else 0) * (p.1 * gOf dv b + extS Sp p.2 b) := by
  have hP : iotaP Sp n' dw (fun k => if (Sum.inr () : {a : Fin u // a ∉ Sp} ⊕ Unit) = k
      then 1 else 0) = phiOf dw *ᵥ (Fin.cons 0 (fun b => if b ∈ Sp then n' b else 0) : V u) := by
    show phiOf dw *ᵥ (Fin.cons 0 (extP Sp n' _) : V u) = _
    rw [extP_basis_inr]
  have hn : auxDot (fun b => if b ∈ Sp then n' b else 0) (gOf dw) = 1 := by
    rw [← hw1]
    refine Finset.sum_congr rfl fun b _ => ?_
    show (if b ∈ Sp then n' b else 0) * gOf dw b = n' b * gOf dw b
    by_cases hb : b ∈ Sp
    · rw [if_pos hb]
    · rw [if_neg hb, hw0 b hb]; ring
  rw [readL, hP, dotV_phi_cons dw h0w, hn, iotaS, phiOf_mulVec dv h0v]
  simp only [Fin.cons_zero, Fin.cons_succ, zero_add, zero_mul, one_mul]

/-! ## Trivial kernels -/

theorem bT_ker (dv dw : V u) (h0v : dv 0 = 1) (h0w : dw 0 = 1)
    (hv : ∀ a ∈ Sp, gOf dv a = n' a) (hw0 : ∀ a, a ∉ Sp → gOf dw a = 0)
    (hw1 : auxDot n' (gOf dw) = 1) (hgw : auxDot (gOf dw) (gOf dw) = 0)
    (hi0 : i0 ∈ Sp) (hn0 : n' i0 = 1)
    (p : ZMod 2 × ({a : Fin u // a ∈ Sp ∧ a ≠ i0} → ZMod 2))
    (hp : readL (iotaH Sp dv) (iotaT Sp i0 dw) p = 0) : p = 0 := by
  obtain ⟨t0, t⟩ := p
  obtain ⟨β, hβ⟩ : ∃ β, β = extT Sp i0 t := ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = auxDot β (gOf dw) := ⟨_, rfl⟩
  have hrow : ∀ a (_ : a ∈ Sp), n' a * (t0 + τ) + (t0 * gOf dw a + β a) = 0 := by
    intro a ha
    have := congrFun hp ⟨a, ha⟩
    rw [bT_apply Sp i0 dv dw h0v h0w _ a ha, hv a ha] at this
    rw [hτ, hβ]; exact this
  have hsum : (∑ a, gOf dw a * (n' a * (t0 + τ) + (t0 * gOf dw a + β a))) = 0 :=
    Finset.sum_eq_zero fun a _ => by
      by_cases ha : a ∈ Sp
      · rw [hrow a ha, mul_zero]
      · rw [hw0 a ha, zero_mul]
  have hexp : (∑ a, gOf dw a * (n' a * (t0 + τ) + (t0 * gOf dw a + β a))) =
      (t0 + τ) * auxDot n' (gOf dw) + t0 * auxDot (gOf dw) (gOf dw) + τ := by
    rw [hτ]
    simp only [auxDot, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [hexp, hw1, hgw] at hsum
  have ht0 : t0 = 0 := by linear_combination hsum - CharTwo.add_self_eq_zero τ
  have hβi0 : β i0 = 0 := by simp [hβ, extT]
  have hτ0 : τ = 0 := by
    have := hrow i0 hi0
    rw [hn0, ht0, hβi0] at this
    linear_combination this
  refine Prod.ext ht0 (funext fun a => ?_)
  have := hrow a.1 a.2.1
  rw [ht0, hτ0] at this
  have hb : β a.1 = t a := by simp [hβ, extT, a.2]
  rw [hb] at this
  show t a = 0
  linear_combination this

theorem bS_ker (dv dw : V u) (h0v : dv 0 = 1) (h0w : dw 0 = 1)
    (hv : ∀ a ∈ Sp, gOf dv a = n' a) (hw0 : ∀ a, a ∉ Sp → gOf dw a = 0)
    (hw1 : auxDot n' (gOf dw) = 1) (hgv : auxDot (gOf dv) (gOf dv) = 0)
    (p : ZMod 2 × ({a : Fin u // a ∉ Sp} → ZMod 2))
    (hp : readL (iotaP Sp n' dw) (iotaS Sp dv) p = 0) : p = 0 := by
  obtain ⟨s0, s⟩ := p
  have hrow : ∀ a (ha : a ∉ Sp), s0 * gOf dv a + s ⟨a, ha⟩ = 0 := by
    intro a ha
    have := congrFun hp (.inl ⟨a, ha⟩)
    rw [bS_apply_inl Sp n' dv dw h0v h0w hw0 _ a ha] at this
    exact this
  have hlast := congrFun hp (.inr ())
  rw [bS_apply_inr Sp n' dv dw h0v h0w hw0 hw1] at hlast
  rw [Pi.zero_apply] at hlast
  have hcl : auxDot (extS Sp s) (gOf dv) +
      ∑ b, (if b ∈ Sp then n' b else 0) * (s0 * gOf dv b + extS Sp s b) =
      s0 * auxDot (gOf dv) (gOf dv) := by
    rw [auxDot, auxDot, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : b ∈ Sp
    · have hσ : extS Sp s b = 0 := by simp [extS, hb]
      rw [if_pos hb, hσ, ← hv b hb]; ring
    · have hσ : extS Sp s b = s ⟨b, hb⟩ := by simp [extS, hb]
      have hs : s ⟨b, hb⟩ = s0 * gOf dv b := by
        linear_combination hrow b hb - CharTwo.add_self_eq_zero (s0 * gOf dv b)
      rw [if_neg hb, hσ, hs]; ring
  have hs0 : s0 = 0 := by
    have h1 : s0 + s0 * auxDot (gOf dv) (gOf dv) = 0 := by
      rw [← hcl]; linear_combination hlast
    rw [hgv, mul_zero, add_zero] at h1; exact h1
  refine Prod.ext hs0 (funext fun a => ?_)
  have := hrow a.1 a.2
  rw [hs0] at this
  show s a = 0
  linear_combination this

/-! ## The additive equivalences -/

/-- An additive map with trivial kernel between finite groups of the same size. -/
noncomputable def addEquivOfKer {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] [Fintype X]
    [Fintype Y] (f : X → Y) (hadd : ∀ x y, f (x + y) = f x + f y) (hker : ∀ x, f x = 0 → x = 0)
    (hcard : Fintype.card X = Fintype.card Y) : X ≃+ Y :=
  AddEquiv.ofBijective (AddMonoidHom.mk' f hadd)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨(injective_iff_map_eq_zero (AddMonoidHom.mk' f hadd)).mpr hker, hcard⟩)

lemma card_resT (hi0 : i0 ∈ Sp) :
    Fintype.card (ZMod 2 × ({a : Fin u // a ∈ Sp ∧ a ≠ i0} → ZMod 2)) =
      Fintype.card ({a : Fin u // a ∈ Sp} → ZMod 2) := by
  have h1 : Fintype.card {a : Fin u // a ∈ Sp ∧ a ≠ i0} = Sp.card - 1 := by
    rw [Fintype.card_subtype, ← Finset.card_erase_of_mem hi0]
    congr 1; ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_comm]
  have h2 : Fintype.card {a : Fin u // a ∈ Sp} = Sp.card := Fintype.card_coe Sp
  obtain ⟨k, hk⟩ : ∃ k, Sp.card = k + 1 :=
    ⟨Sp.card - 1, (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr ⟨i0, hi0⟩)).symm⟩
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, ZMod.card, h1, h2, hk,
    Nat.add_sub_cancel, pow_succ, mul_comm]

lemma card_resS :
    Fintype.card (ZMod 2 × ({a : Fin u // a ∉ Sp} → ZMod 2)) =
      Fintype.card (({a : Fin u // a ∉ Sp} ⊕ Unit) → ZMod 2) := by
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, ZMod.card, Fintype.card_sum,
    Fintype.card_unit, pow_succ, mul_comm]

/-- `bT` as an additive equivalence. -/
noncomputable def bTe (dv dw : V u) (h0v : dv 0 = 1) (h0w : dw 0 = 1)
    (hv : ∀ a ∈ Sp, gOf dv a = n' a) (hw0 : ∀ a, a ∉ Sp → gOf dw a = 0)
    (hw1 : auxDot n' (gOf dw) = 1) (hgw : auxDot (gOf dw) (gOf dw) = 0)
    (hi0 : i0 ∈ Sp) (hn0 : n' i0 = 1) :
    (ZMod 2 × ({a : Fin u // a ∈ Sp ∧ a ≠ i0} → ZMod 2)) ≃+ ({a : Fin u // a ∈ Sp} → ZMod 2) :=
  addEquivOfKer (readL (iotaH Sp dv) (iotaT Sp i0 dw))
    (readL_add _ _ (iotaT_add Sp i0 dw))
    (bT_ker Sp n' i0 dv dw h0v h0w hv hw0 hw1 hgw hi0 hn0) (card_resT Sp i0 hi0)

/-- `bS` as an additive equivalence. -/
noncomputable def bSe (dv dw : V u) (h0v : dv 0 = 1) (h0w : dw 0 = 1)
    (hv : ∀ a ∈ Sp, gOf dv a = n' a) (hw0 : ∀ a, a ∉ Sp → gOf dw a = 0)
    (hw1 : auxDot n' (gOf dw) = 1) (hgv : auxDot (gOf dv) (gOf dv) = 0) :
    (ZMod 2 × ({a : Fin u // a ∉ Sp} → ZMod 2)) ≃+ (({a : Fin u // a ∉ Sp} ⊕ Unit) → ZMod 2) :=
  addEquivOfKer (readL (iotaP Sp n' dw) (iotaS Sp dv))
    (readL_add _ _ (iotaS_add Sp dv))
    (bS_ker Sp n' dv dw h0v h0w hv hw0 hw1 hgv) (card_resS Sp)

end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.FreeMidBij =====

-- ===== begin KP.FreeMid =====
section
/-! # The middle plan of the free factorization, and the packaged statement

`midL_eq`: with additive coordinate maps and bijective residual pairings, the middle letter
matrix is `linMat G * signMat φ` for an additive bijection `G` of letters: a signed linear
permutation, hence a 0-call plan (`exists_midPlan`).

**`free_hfr`** is the result of the free factorization: for routing vectors `d` with `d v 0 = 1`,
`d v · d v = 1`, the explicit charts `chartOf (d v)`, and a rectangle described by
`(Sp, n', i0)`, there are plans `src`, `tgt` (at most `2 * (u + 1)` calls, independent of the
query) and `mid` (0 calls) with
`qBlk h (tgt t) * qBlk h (mid j t s) * qBlk h (src s) = (1/2)^(2 (u+1) h) • lift h (U c j t s)`
for all targets `t` and sources `s` of the rectangle: the hypothesis `hfr` of
`shift_stage_spec`. -/

namespace OAI.Computability.NearSquareRoot.KernelPass
open Matrix Finset
open Free

section Abstract
variable {Hc Sc Pc Tc : Type*} [Fintype Hc] [Fintype Sc] [Fintype Pc] [Fintype Tc]
  [DecidableEq Hc] [DecidableEq Sc] [DecidableEq Pc] [DecidableEq Tc]

/-- With bijective pairings the middle is a signed permutation, in closed form. -/
theorem mid_eq_iff (bS : Sc ≃ Pc) (bT : Tc ≃ Hc) (mm : Sc × Sc → Tc × Tc → ZMod 2)
    (n : (Pc × Pc) × (Tc × Tc)) (m : (Hc × Hc) × (Sc × Sc)) :
    Mid bS bT mm n m =
      if n = ((bS m.2.2, bS m.2.1), (bT.symm m.1.2, bT.symm m.1.1)) then chi (mm m.2 n.2) else 0 := by
  simp only [Mid]
  have key : (m.1 = (bT n.2.2, bT n.2.1) ∧ n.1 = (bS m.2.2, bS m.2.1)) ↔
      n = ((bS m.2.2, bS m.2.1), (bT.symm m.1.2, bT.symm m.1.1)) := by
    constructor
    · rintro ⟨h1, h2⟩
      refine Prod.ext h2 (Prod.ext ?_ ?_)
      · simp [h1]
      · simp [h1]
    · intro h
      rw [h]
      exact ⟨by simp, rfl⟩
  by_cases h : n = ((bS m.2.2, bS m.2.1), (bT.symm m.1.2, bT.symm m.1.1))
  · rw [if_pos h, if_pos (key.mpr h)]
  · rw [if_neg h, if_neg (fun hh => h (key.mp hh))]

variable [AddCommGroup Hc] [AddCommGroup Sc] [AddCommGroup Pc] [AddCommGroup Tc]

/-- The coordinate map of the middle. -/
def muE (bS : Sc ≃+ Pc) (bT : Tc ≃+ Hc) : (Hc × Hc) × (Sc × Sc) ≃+ (Pc × Pc) × (Tc × Tc) :=
  AddEquiv.mk'
    { toFun := fun m => ((bS m.2.2, bS m.2.1), (bT.symm m.1.2, bT.symm m.1.1))
      invFun := fun n => ((bT n.2.2, bT n.2.1), (bS.symm n.1.2, bS.symm n.1.1))
      left_inv := fun m => Prod.ext (Prod.ext (bT.apply_symm_apply _) (bT.apply_symm_apply _))
        (Prod.ext (bS.symm_apply_apply _) (bS.symm_apply_apply _))
      right_inv := fun n => Prod.ext (Prod.ext (bS.apply_symm_apply _) (bS.apply_symm_apply _))
        (Prod.ext (bT.symm_apply_apply _) (bT.symm_apply_apply _)) }
    (fun x y => Prod.ext (Prod.ext (bS.map_add' _ _) (bS.map_add' _ _))
      (Prod.ext (bT.symm.map_add' _ _) (bT.symm.map_add' _ _)))

end Abstract

variable {M u : ℕ}

/-- `bitsE` is additive. -/
def bitsA (j : Fin M) : Bits (2 * (M + u)) ≃+ Spec M j × (Act u × Act u) :=
  AddEquiv.mk' (bitsE j) (fun _ _ => rfl)

section Mid
variable {Hc Sr Pc Tr : Type*} [Fintype Hc] [Fintype Sr] [Fintype Pc] [Fintype Tr]
  [DecidableEq Hc] [DecidableEq Sr] [DecidableEq Pc] [DecidableEq Tr]
  [AddCommGroup Hc] [AddCommGroup Sr] [AddCommGroup Pc] [AddCommGroup Tr]

/-- `srcCo` of additive maps is additive. -/
def srcCoA (A A' : Aux u ≃ Hc × Sr) (hA : ∀ α β, A (α + β) = A α + A β)
    (hA' : ∀ α β, A' (α + β) = A' α + A' β) :
    Act u × Act u ≃+ (Hc × Hc) × ((ZMod 2 × Sr) × (ZMod 2 × Sr)) :=
  AddEquiv.mk' (srcCo A A') (fun x y => by
    simp only [srcCo, Equiv.coe_fn_mk, Prod.fst_add, Prod.snd_add, hA, hA']; rfl)

variable (j : Fin M) (A A' : Aux u ≃ Hc × Sr) (hA : ∀ α β, A (α + β) = A α + A β)
  (hA' : ∀ α β, A' (α + β) = A' α + A' β) (Bq Bq' : Aux u ≃ Pc × Tr)
  (hB : ∀ α β, Bq (α + β) = Bq α + Bq β) (hB' : ∀ α β, Bq' (α + β) = Bq' α + Bq' β)
  (bS : (ZMod 2 × Sr) ≃+ Pc) (bT : (ZMod 2 × Tr) ≃+ Hc)

/-- The letter map of the middle: an additive bijection. -/
def midG : Bits (2 * (M + u)) ≃+ Bits (2 * (M + u)) :=
  (bitsA j).trans ((AddEquiv.prodCongr (AddEquiv.refl _)
    ((srcCoA A A' hA hA').trans ((muE bS bT).trans (srcCoA Bq Bq' hB hB').symm))).trans
      (bitsA j).symm)

lemma bitsE_midG (x : Bits (2 * (M + u))) :
    bitsE j (midG j A A' hA hA' Bq Bq' hB hB' bS bT x) =
      ((bitsE j x).1, (srcCo Bq Bq').symm (muE bS bT (srcCo A A' (bitsE j x).2))) := by
  show bitsE j ((bitsE j).symm _) = _
  rw [Equiv.apply_symm_apply]
  rfl

theorem midL_eq {V' : Type*} [AddCommGroup V'] (β : V' →+ V' →+ ZMod 2)
    (ιS : ZMod 2 × Sr → V') (ιT : ZMod 2 × Tr → V') :
    actLift j (midM β ιS ιT A A' Bq Bq' bS bT) =
      linMat (midG j A A' hA hA' Bq Bq' hB hB' bS bT) *
        signMat (fun x => midSign β ιS ιT (srcCo A A' (bitsE j x).2).2
          (muE bS bT (srcCo A A' (bitsE j x).2)).2) := by
  ext y x
  rw [mul_signMat, actLift_apply]
  simp only [linMat, midM, Matrix.submatrix_apply]
  have hm := mid_eq_iff bS.toEquiv bT.toEquiv (midSign β ιS ιT) (srcCo Bq Bq' (bitsE j y).2)
    (srcCo A A' (bitsE j x).2)
  rw [show Mid (⇑bS) (⇑bT) (midSign β ιS ιT) ((srcCo Bq Bq') ((bitsE j) y).2)
    ((srcCo A A') ((bitsE j) x).2) = _ from hm]
  by_cases hy : y = midG j A A' hA hA' Bq Bq' hB hB' bS bT x
  · rw [if_pos hy, one_mul, hy, bitsE_midG]
    simp only [Equiv.apply_symm_apply, if_true]
    refine (if_pos ?_).trans rfl
    rfl
  · rw [if_neg hy, zero_mul]
    split_ifs with h1 h2
    · exfalso
      apply hy
      apply (bitsE j).injective
      rw [bitsE_midG]
      exact Prod.ext h1 ((Equiv.eq_symm_apply _).mpr h2)
    · rfl
    · rfl

end Mid

end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.FreeMid =====

-- ===== begin KP.FreeHfr =====
section
/-! # The free factorization as plans: the hypothesis `hfr`

`exists_midPlan`: the middle of `free_geom` is a 0-call plan.
**`free_hfr`**: for routing vectors `d` (`d v 0 = 1`, `d v · d v = 1`), the explicit charts
`chartOf (d v)`, sets `Ssrc`, `Stgt` of labels, and `(Sp, n', i0)` with
* `i0 ∈ Sp`, `n' i0 = 1`;
* sources: `d v a.succ = n' a` for `a ∈ Sp`;
* targets: `d w a.succ = 0` for `a ∉ Sp`, and `Σ_a n' a * d w a.succ = 1`;
there are plans `src`, `tgt` (at most `2 * (u + 1)` calls, independent of the query) and `mid`
(0 calls) with
`qBlk h (tgt t) * qBlk h (mid j t s) * qBlk h (src s) = (1/2)^(2 * (u + 1) * h) • lift h (U c j t s)`
for all `t ∈ Stgt`, `s ∈ Ssrc`, every width `h` and query `j`. -/

namespace OAI.Computability.NearSquareRoot.KernelPass
open Matrix Finset
open Free

variable {M u : ℕ} (Sp : Finset (Fin u)) (n' : Aux u) (i0 : Fin u)

lemma splitA_add (α β : Aux u) : splitA Sp (α + β) = splitA Sp α + splitA Sp β := rfl

lemma thetaSplitA_add (g : Aux u) (hg : auxDot g g = 0) (α β : Aux u) :
    ((theta g hg).trans (splitA Sp)) (α + β) =
      ((theta g hg).trans (splitA Sp)) α + ((theta g hg).trans (splitA Sp)) β := by
  show splitA Sp (thetaFn g (α + β)) = _
  rw [thetaFn_add]; rfl

lemma splitB_add (hi0 : i0 ∈ Sp) (hn0 : n' i0 = 1) (α β : Aux u) :
    splitB Sp n' i0 hi0 hn0 (α + β) = splitB Sp n' i0 hi0 hn0 α + splitB Sp n' i0 hi0 hn0 β := by
  refine Prod.ext (funext fun s => ?_) (funext fun a => ?_)
  · rcases s with a | ⟨⟩ <;> rfl
  · show (α + β) a.1 + n' a.1 * (α + β) i0 = (α a.1 + n' a.1 * α i0) + (β a.1 + n' a.1 * β i0)
    simp only [Pi.add_apply]; ring

lemma thetaSplitB_add (hi0 : i0 ∈ Sp) (hn0 : n' i0 = 1) (g : Aux u) (hg : auxDot g g = 0)
    (α β : Aux u) :
    ((theta g hg).trans (splitB Sp n' i0 hi0 hn0)) (α + β) =
      ((theta g hg).trans (splitB Sp n' i0 hi0 hn0)) α +
        ((theta g hg).trans (splitB Sp n' i0 hi0 hn0)) β := by
  show splitB Sp n' i0 hi0 hn0 (thetaFn g (α + β)) = _
  rw [thetaFn_add, splitB_add]; rfl

/-- **The middle plan**: 0 calls. -/
theorem exists_midPlan (dv dw : V u) (h0v : dv 0 = 1) (h0w : dw 0 = 1)
    (hdv : dotV dv dv = 1) (hdw : dotV dw dw = 1) (j : Fin M) (hi0 : i0 ∈ Sp) (hn0 : n' i0 = 1)
    (hv : ∀ a ∈ Sp, gOf dv a = n' a) (hw0 : ∀ a, a ∉ Sp → gOf dw a = 0)
    (hw1 : auxDot n' (gOf dw) = 1) :
    ∃ p : QPlan (2 * (M + u)) 1 1, p.calls = 0 ∧
      Implements p (actLift j (midM (dotHom u) (iotaS Sp dv) (iotaT Sp i0 dw) (splitA Sp)
        ((theta (gOf dv) (gOf_self dv h0v hdv)).trans (splitA Sp)) (splitB Sp n' i0 hi0 hn0)
        ((theta (gOf dw) (gOf_self dw h0w hdw)).trans (splitB Sp n' i0 hi0 hn0))
        (readL (iotaP Sp n' dw) (iotaS Sp dv)) (readL (iotaH Sp dv) (iotaT Sp i0 dw)))) 0 := by
  have key := midL_eq j (splitA Sp) ((theta (gOf dv) (gOf_self dv h0v hdv)).trans (splitA Sp))
    (splitA_add Sp) (thetaSplitA_add Sp _ _) (splitB Sp n' i0 hi0 hn0)
    ((theta (gOf dw) (gOf_self dw h0w hdw)).trans (splitB Sp n' i0 hi0 hn0))
    (splitB_add Sp n' i0 hi0 hn0) (thetaSplitB_add Sp n' i0 hi0 hn0 _ _)
    (bSe Sp n' dv dw h0v h0w hv hw0 hw1 (gOf_self dv h0v hdv))
    (bTe Sp n' i0 dv dw h0v h0w hv hw0 hw1 (gOf_self dw h0w hdw) hi0 hn0)
    (dotHom u) (iotaS Sp dv) (iotaT Sp i0 dw)
  obtain ⟨p, hp0, hp⟩ := exists_monoPlan
    (linEquivOf _ _ (AddEquiv.map_add' (midG j (splitA Sp)
      ((theta (gOf dv) (gOf_self dv h0v hdv)).trans (splitA Sp))
      (splitA_add Sp) (thetaSplitA_add Sp _ _) (splitB Sp n' i0 hi0 hn0)
      ((theta (gOf dw) (gOf_self dw h0w hdw)).trans (splitB Sp n' i0 hi0 hn0))
      (splitB_add Sp n' i0 hi0 hn0) (thetaSplitB_add Sp n' i0 hi0 hn0 _ _)
      (bSe Sp n' dv dw h0v h0w hv hw0 hw1 (gOf_self dv h0v hdv))
      (bTe Sp n' i0 dv dw h0v h0w hv hw0 hw1 (gOf_self dw h0w hdw) hi0 hn0)))
      (AddEquiv.symm_apply_apply _) (AddEquiv.apply_symm_apply _))
    (fun x => midSign (dotHom u) (iotaS Sp dv) (iotaT Sp i0 dw)
      (srcCo (splitA Sp) ((theta (gOf dv) (gOf_self dv h0v hdv)).trans (splitA Sp)) (bitsE j x).2).2
      (muE (bSe Sp n' dv dw h0v h0w hv hw0 hw1 (gOf_self dv h0v hdv))
        (bTe Sp n' i0 dv dw h0v h0w hv hw0 hw1 (gOf_self dw h0w hdw) hi0 hn0)
        (srcCo (splitA Sp) ((theta (gOf dv) (gOf_self dv h0v hdv)).trans (splitA Sp))
          (bitsE j x).2)).2)
  exact ⟨p, hp0, hp.congr key.symm rfl⟩

variable {ι : Type*}

/-- **The free factorization as plans (`hfr` of `shift_stage_spec`).** -/
theorem free_hfr (d : ι → V u) (h0 : ∀ i, d i 0 = 1) (hd : ∀ i, dotV (d i) (d i) = 1)
    (Ssrc Stgt : Set ι) (hi0 : i0 ∈ Sp) (hn0 : n' i0 = 1)
    (hsrc : ∀ v ∈ Ssrc, ∀ a ∈ Sp, d v a.succ = n' a)
    (htgt0 : ∀ w ∈ Stgt, ∀ a, a ∉ Sp → d w a.succ = 0)
    (htgt1 : ∀ w ∈ Stgt, (∑ a, n' a * d w a.succ) = 1) :
    ∃ (src tgt : ι → QPlan (2 * (M + u)) 1 1) (mid : Fin M → ι → ι → QPlan (2 * (M + u)) 1 1),
      (∀ s, (src s).calls ≤ 2 * (u + 1)) ∧ (∀ t, (tgt t).calls ≤ 2 * (u + 1)) ∧
      (∀ j t s, (mid j t s).calls = 0) ∧
      ∀ (h : ℕ) (j : Fin M) (t s : ι), t ∈ Stgt → s ∈ Ssrc →
        qBlk h (tgt t) * qBlk h (mid j t s) * qBlk h (src s) =
          ((1 / 2 : ℚ) ^ (2 * (u + 1) * h)) •
            lift h (U (fun i => chartOf (d i) (h0 i) (hd i)) j t s) := by
  classical
  have hSp : Sp.card ≤ u := (Finset.card_le_univ Sp).trans_eq (Fintype.card_fin u)
  have hS := fun s : ι => exists_srcPlan (M := M) Sp (gOf (d s)) (gOf_self (d s) (h0 s) (hd s))
  have hT := fun t : ι => exists_tgtPlan (M := M) Sp n' i0 hi0 hn0 (gOf (d t))
    (gOf_self (d t) (h0 t) (hd t))
  have hMid := fun (j : Fin M) (t s : ι) (ht : t ∈ Stgt) (hs : s ∈ Ssrc) =>
    exists_midPlan Sp n' i0 (d s) (d t) (h0 s) (h0 t) (hd s) (hd t) j hi0 hn0
      (hsrc s hs) (htgt0 t ht) (htgt1 t ht)
  refine ⟨fun s => (hS s).choose, fun t => (hT t).choose,
    fun j t s => if hh : t ∈ Stgt ∧ s ∈ Ssrc then (hMid j t s hh.1 hh.2).choose else idPlan _,
    fun s => ?_, fun t => ?_, fun j t s => ?_, fun h j t s ht hs => ?_⟩
  · rw [(hS s).choose_spec.1]; omega
  · rw [(hT t).choose_spec.1]; omega
  · dsimp only
    by_cases hh : t ∈ Stgt ∧ s ∈ Ssrc
    · rw [dif_pos hh]; exact (hMid j t s hh.1 hh.2).choose_spec.1
    · rw [dif_neg hh]; rfl
  · dsimp only
    rw [dif_pos ⟨ht, hs⟩]
    have hI := ((hT t).choose_spec.2 j).seq
      (((hMid j t s ht hs).choose_spec.2).seq ((hS s).choose_spec.2 j))
    have hU := free_geom Sp n' i0 d h0 hd j t s hi0 hn0 (hsrc s hs) (htgt0 t ht) (htgt1 t ht)
    have hI' := hI h
    rw [qBlk_seq, qBlk_seq, ← Matrix.mul_assoc, ← hU] at hI'
    have he : 2 * (u - Sp.card + 1) + (0 + 2 * Sp.card) = 2 * (u + 1) := by omega
    rw [hI', he]

end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.FreeHfr =====

-- ===== begin KP.Params =====
section
/-! # The parameter inequality

The template parameters at `ℓ = 2`, with `L = 4n`, `q = 2^b`, `N = q^L` labels, `m = 2q^(2n)+1`,
routing dimension `D = 2 + L·q` and arity `A = 2(m+D-1)`; the call bound `q^(n+5)` per row is
`calls_le` (chunk KP.ParamsQ). -/

namespace OAI.Computability.NearSquareRoot.KernelPass

section Budget
variable (n b : ℕ)

def pq : ℕ := 2 ^ b
def pL : ℕ := 4 * n
def pN : ℕ := pq b ^ pL n
def pm : ℕ := 2 * pq b ^ (2 * n) + 1
def pD : ℕ := 2 + pL n * pq b
def pA : ℕ := 2 * (pm n b + pD n b - 1)

end Budget

lemma sq_le_two_pow (k : ℕ) (hk : 5 ≤ k) : (k + 1) * k ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ]; have h5 := Nat.mul_le_mul_right k hk; nlinarith only [ih, h5, hk]

/-- A large `b`: every polynomial side condition holds at `b = 2^k`. -/
lemma exists_k (c : ℕ) : ∃ k, 5 ≤ k ∧ c * (k + 1) ≤ 2 ^ k :=
  ⟨max c 5, le_max_right _ _, (Nat.mul_le_mul_right _ (le_max_left c 5)).trans
    (by rw [mul_comm]; exact sq_le_two_pow _ (le_max_right _ _))⟩

end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.Params =====

-- ===== begin KP.FreqTable =====
section
/-! # The frequency-table compiler

Idea from OpenAI's KernelPassMatrixTable / KernelPassFrequency; construction and
proofs ours. A per-frequency matrix `M (e v)` on `n` rows that depends on the frequency `v` only
through the sign pattern `e v = spat test v = Σ_c test (v c) ∈ F^q` is a `QPlan`:
Walsh-convert the `n` rows (`n·A` calls), fan out to `n²` rows, `scale` row `(r,c)` by
`M (e v) r c`, fan in, convert back (`n·A` calls). The plan itself is `qfreqMat` (chunk KP.QFreq:
`qfreqMat_spec`, its eval is `specR (fun v => M (e v))`; `qfreqMat_calls = 2·n·A`); this chunk
holds its pieces (`spat`, the fan matrices `fanOutT`, `fanInT`, `fanT_freq`). -/

namespace OAI.Computability.NearSquareRoot.KernelPass
open Matrix Finset

variable {A : ℕ}

theorem target_eq_Kw (A W h : ℕ) : target A W h = Kw A h W := by
  ext ⟨b, y⟩ ⟨a, x⟩
  rw [target_apply]; rfl

theorem bank_rowPlan_eval (n h : ℕ) : (rowBank n fun _ => rowPlan A).eval h = Kw A h n := by
  ext ⟨b, y⟩ ⟨a, x⟩
  rw [rowBank_apply]
  simp only [Kw, Wh]
  split_ifs
  · exact rowPlan_oneRow y x
  · rfl

section
variable {q n : ℕ} (test : Column A → Fin q → ZMod 2)
  (M : (Fin q → ZMod 2) → Matrix (Fin n) (Fin n) ℚ)

/-- The sign pattern of a frequency. -/
def spat {h : ℕ} (v : Addr A h) : Fin q → ZMod 2 := ∑ c, test (v c)

def rI (u : Fin (n * n)) : Fin n := (finProdFinEquiv.symm u).1
def cI (u : Fin (n * n)) : Fin n := (finProdFinEquiv.symm u).2

/-- Fan out `n → n²`: row `(r,c)` copies row `c`. -/
def fanOutT : Matrix (Fin (n * n)) (Fin n) ℚ := fun u a => if cI u = a then 1 else 0
/-- Fan in `n² → n`: row `r` sums rows `(r,·)`. -/
def fanInT : Matrix (Fin n) (Fin (n * n)) ℚ := fun r u => if rI u = r then 1 else 0

theorem fanT_freq (N : Matrix (Fin n) (Fin n) ℚ) :
    fanInT * diagonal (fun u => N (rI u) (cI u)) * fanOutT = N := by
  ext r a
  rw [mul_apply]
  simp only [mul_diagonal, fanInT, fanOutT, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  simp only [rI, cI, Equiv.symm_apply_apply]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

end

end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.FreqTable =====

-- ===== begin KP.LinChart =====
section
/-! # Multi-pair queries and the Walsh column formula

`multiQuery`: the query on a list of disjoint axis pairs as a plan with `2·length` calls
(`multiQuery_calls`, `multiQuery_oneRow`: `W · diag(sign) · W`); `walshCol_apply`: the entries of
the Walsh column matrix. Linear maps as `perm` moves are in chunk KP.LetterPlans
(`exists_letterLinPlan_equiv`). -/

namespace OAI.Computability.NearSquareRoot.KernelPass
open Matrix Finset

variable {A : ℕ}


/-! ## The charged factorization -/

/-! ## The common plan of a query on several axis pairs -/

/-- The query plans of a list of axis pairs, in sequence. -/
def multiQuery : List (Fin A × Fin A) → QPlan A 1 1
  | [] => idPlan A
  | g :: l => .seq (queryPlan g.1 g.2) (multiQuery l)

/-- The sign of a list of axis pairs. -/
def multiSign (l : List (Fin A × Fin A)) (x : Column A) : ℚ := (l.map fun g => qc g.1 g.2 x).prod

theorem multiQuery_calls : ∀ l : List (Fin A × Fin A), (multiQuery l).calls = 2 * l.length
  | [] => rfl
  | g :: l => by
    rw [multiQuery, QPlan.calls, queryPlan_calls, multiQuery_calls l, List.length_cons]; ring

theorem multiQuery_oneRow {h : ℕ} : ∀ l : List (Fin A × Fin A), (∀ g ∈ l, g.1 ≠ g.2) →
    OneRow ((multiQuery l).eval h) (walshCol A * diagonal (multiSign l) * walshCol A)
  | [], _ => by
    have e : walshCol A * diagonal (multiSign ([] : List (Fin A × Fin A))) * walshCol A = 1 := by
      have : diagonal (multiSign ([] : List (Fin A × Fin A))) = (1 : ColMat A) := by
        ext y x; simp [multiSign, diagonal_apply, Matrix.one_apply]
      rw [this, Matrix.mul_one, walshCol_sq]
    rw [e]; exact idPlan_oneRow
  | g :: l, hl => by
    have h1 := queryPlan_oneRow (h := h) (hl g (List.mem_cons_self))
    have h2 := multiQuery_oneRow (h := h) l fun g' hg' => hl g' (List.mem_cons_of_mem _ hg')
    have e : walshCol A * diagonal (multiSign (g :: l)) * walshCol A =
        (walshCol A * diagonal (qc g.1 g.2) * walshCol A) *
          (walshCol A * diagonal (multiSign l) * walshCol A) := by
      have hd : diagonal (multiSign (g :: l)) =
          diagonal (qc g.1 g.2) * (diagonal (multiSign l) : ColMat A) := by
        rw [diagonal_mul_diagonal]; exact congrArg _ (funext fun x => by simp [multiSign])
      calc walshCol A * diagonal (multiSign (g :: l)) * walshCol A
          = walshCol A * diagonal (qc g.1 g.2) * (1 : ColMat A) * diagonal (multiSign l) * walshCol A := by
            rw [hd]; simp only [Matrix.mul_one, Matrix.mul_assoc]
        _ = _ := by rw [← walshCol_sq]; simp only [Matrix.mul_assoc]
    rw [e]
    exact h1.mul h2

theorem walshCol_apply (y x : Column A) :
    walshCol A y x = (1 / 2 : ℚ) ^ A * chi (∑ a, dot (y a) (x a)) := by
  simp only [walshCol, piMat, pairMat_apply]
  rw [chi_sum, Finset.prod_div_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, div_eq_mul_inv, mul_comm, one_mul,
    inv_pow]

end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.LinChart =====

-- ===== begin KP.Pairs =====
section
/-! # Many disjoint query pairs: from `W·D·W` back to the Walsh target

Arity `A = 2k`, axis `eA (t, p) = p + k·t` (`t : Fin 2`, `p : Fin k`): pair `p` is the two axes
`p` and `k + p`. `qtot x = ∏_p (-1)^{⟨x_p, x_{k+p}⟩}`. Zipping a column into `k` two-axis columns
(`zipE`), the two-axis identity `query_col` lifts by `piMat` to

`walshCol · diag(qtot) · walshCol = diag(qtot) · (walshCol · swapHalves) · diag(qtot)`
(`query_pairs`), hence `walshCol = diag(qtot) · (W·D·W) · diag(qtot) · swapHalves`
(`walsh_of_WDW`). Idea of the halves exchange after OpenAI's KernelBinaryQuerySigns;
proofs ours. `swapAllPlan k` (one `perm` move) realizes `swapHalves`. -/

namespace OAI.Computability.NearSquareRoot.KernelPass
open Matrix Finset

variable {k : ℕ}

/-- Axis `(t, p) ↦ p + k·t`. -/
abbrev eA (k : ℕ) : Fin 2 × Fin k ≃ Fin (2 * k) := finProdFinEquiv

/-- Zip a column into `k` two-axis columns. -/
def zipE (k : ℕ) : Column (2 * k) ≃ (Fin k → Column 2) where
  toFun x p t := x (eA k (t, p))
  invFun z a := z ((eA k).symm a).2 ((eA k).symm a).1
  left_inv x := by
    funext a
    show x (eA k (((eA k).symm a).1, ((eA k).symm a).2)) = x a
    rw [Prod.mk.eta, Equiv.apply_symm_apply]
  right_inv z := by funext p t; simp

lemma prod_zip (f : Fin (2 * k) → ℚ) : ∏ a, f a = ∏ p : Fin k, ∏ t : Fin 2, f (eA k (t, p)) := by
  rw [← (eA k).prod_comp, Fintype.prod_prod_type, Finset.prod_comm]

lemma walshCol_zip : walshCol (2 * k) = (piMat fun _ : Fin k => walshCol 2).submatrix (zipE k) (zipE k) := by
  ext y x
  simp only [walshCol, piMat, submatrix_apply]
  rw [prod_zip]; rfl

/-- The total query sign of a column. -/
def qtot (x : Column (2 * k)) : ℚ := ∏ p : Fin k, qc (eA k (0, p)) (eA k (1, p)) x

lemma diag_zip : diagonal (qtot (k := k)) =
    (piMat fun _ : Fin k => diagonal (qc (A := 2) 0 1)).submatrix (zipE k) (zipE k) := by
  rw [piMat_diagonal]
  ext y x
  simp only [diagonal_apply, submatrix_apply, (zipE k).injective.eq_iff]
  split_ifs
  · rfl
  · rfl

lemma update2_eq_walsh :
    piMat (Function.update (Function.update (fun _ => 1) (0 : Fin 2) pairMat) 1 pairMat) = walshCol 2 := by
  rw [walshCol]; congr 1; funext a; fin_cases a <;> simp

/-- Exchange the two halves: axis `p ↔ k + p`. -/
def partner (a : Fin (2 * k)) : Fin (2 * k) := eA k (((eA k).symm a).1 + 1, ((eA k).symm a).2)

def swapHalves (x : Column (2 * k)) : Column (2 * k) := fun a => x (partner a)

lemma swap01 (t : Fin 2) : Equiv.swap (0 : Fin 2) 1 t = t + 1 := by fin_cases t <;> decide

lemma perm_zip : (piMat fun _ : Fin k => permMat (A := 2) (swapCol 0 1)).submatrix (zipE k) (zipE k) =
    permMat (swapHalves (k := k)) := by
  rw [show (fun _ : Fin k => permMat (A := 2) (swapCol 0 1)) =
      fun _ => (fun y x => if y = swapCol 0 1 x then (1 : ℚ) else 0) from rfl, piMat_perm]
  ext y x
  show (if zipE k y = (fun p => swapCol 0 1 (zipE k x p)) then (1 : ℚ) else 0) =
    if y = swapHalves x then 1 else 0
  congr 1
  apply propext
  constructor
  · intro h; funext a
    have := congrFun (congrFun h ((eA k).symm a).2) ((eA k).symm a).1
    simp only [zipE, swapCol, swap01, Equiv.coe_fn_mk] at this
    rw [Prod.mk.eta, Equiv.apply_symm_apply] at this
    exact this
  · intro h; funext p t
    have := congrFun h (eA k (t, p))
    simp only [swapHalves, partner, Equiv.symm_apply_apply] at this
    simp only [zipE, swapCol, swap01, Equiv.coe_fn_mk]
    exact this

theorem query_pairs : walshCol (2 * k) * diagonal (qtot (k := k)) * walshCol (2 * k) =
    diagonal qtot * (walshCol (2 * k) * permMat (swapHalves (k := k))) * diagonal qtot := by
  have h2 := query_col (A := 2) (i := 0) (j := 1) (by decide)
  rw [update2_eq_walsh] at h2
  rw [walshCol_zip, diag_zip, ← perm_zip, submatrix_mul_equiv, submatrix_mul_equiv, submatrix_mul_equiv,
    submatrix_mul_equiv, submatrix_mul_equiv, piMat_mul, piMat_mul, piMat_mul, piMat_mul, piMat_mul]
  simp only [h2]

lemma qtot_sq_diag : diagonal (qtot (k := k)) * diagonal qtot = 1 := by
  rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext x
  rw [qtot, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun p _ => by simp only [qc, sgn2, chi]; split_ifs <;> norm_num

lemma partner_partner (a : Fin (2 * k)) : partner (partner a) = a := by
  simp only [partner, Equiv.symm_apply_apply]
  rw [add_assoc, show (1 : Fin 2) + 1 = 0 by decide, add_zero, Prod.mk.eta, Equiv.apply_symm_apply]

lemma swapHalves_perm_sq : permMat (swapHalves (k := k)) * permMat swapHalves = 1 := by
  rw [permMat_mul]
  have : swapHalves (k := k) ∘ swapHalves = id := by
    funext x a; simp [swapHalves, partner_partner]
  rw [this]; ext y x; simp [permMat, one_apply]

/-- The Walsh target from the query product. -/
theorem walsh_of_WDW : walshCol (2 * k) =
    diagonal qtot * (walshCol (2 * k) * diagonal (qtot (k := k)) * walshCol (2 * k)) * diagonal qtot *
      permMat swapHalves := by
  rw [query_pairs]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (diagonal qtot) (diagonal qtot), qtot_sq_diag, Matrix.one_mul,
    ← Matrix.mul_assoc (diagonal qtot) (diagonal qtot), qtot_sq_diag, Matrix.one_mul,
    swapHalves_perm_sq, Matrix.mul_one]

/-! ## The free moves: total chirp and halves exchange -/

/-- The chirp `(-1)^{Σ_p ⟨x_p, x_{k+p}⟩}`, one `scale` move. -/
def chirpAll (k : ℕ) : QPlan (2 * k) 1 1 :=
  .scale 1 (fun x _ => ∑ p : Fin k, dot (x (eA k (0, p))) (x (eA k (1, p))))
    (fun s => if s 0 = 0 then 1 else -1)

theorem chirpAll_oneRow {h : ℕ} : OneRow ((chirpAll k).eval h) (diagonal (qtot (k := k))) := by
  intro y x
  rw [piMat_diagonal, diagonal_apply]
  simp only [chirpAll]
  rw [eval_scale_apply, eq_comm]
  by_cases e : y = x
  · subst e
    simp only [if_true]
    have : (if (∑ c, fun _ : Fin 1 => ∑ p : Fin k, dot (y c (eA k (0, p))) (y c (eA k (1, p)))) 0 = 0
        then (1 : ℚ) else -1) = chi (∑ c, ∑ p : Fin k, dot (y c (eA k (0, p))) (y c (eA k (1, p)))) := by
      rw [Finset.sum_apply]; rfl
    rw [this, chi_sum]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [chi_sum]; rfl
  · rw [if_neg e, if_neg (Ne.symm e)]

/-- The halves exchange as an additive permutation of columns. -/
def swapHalvesAdd (k : ℕ) : Column (2 * k) ≃+ Column (2 * k) where
  toFun := swapHalves
  invFun := swapHalves
  left_inv x := by funext a; simp [swapHalves, partner_partner]
  right_inv x := by funext a; simp [swapHalves, partner_partner]
  map_add' _ _ := rfl

/-- The halves exchange: one free `perm` move. -/
def swapAllPlan (k : ℕ) : QPlan (2 * k) 1 1 := .perm (swapHalvesAdd k)

theorem swapAllPlan_oneRow {h : ℕ} : OneRow ((swapAllPlan k).eval h) (permMat (swapHalves (k := k))) :=
  perm_oneRow _

theorem swapAllPlan_calls : (swapAllPlan k).calls = 0 := rfl

end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.Pairs =====

-- ===== begin KP.KernelBridge =====
section
/-! # Bridge: the letter-level query kernel and the column-level spectral kernel

`sQ j` is the column sign of query `j` (distinguished pair `j` and every auxiliary pair), and
`colK j = W · diag (sQ j) · W` its column kernel. **`colK_apply`**: on a column,
`colK j y x = (1/2)^(2D) · ∏_t Uq j (letter t of y) (letter t of x)`, `D = u + 1`.
Hence `lift_Uq_spectral`: `(1/2)^(2D·h) • lift h (Uq j) = Wh · diag (∏_c sQ j) · Wh`, the diagonal
block of the label kernel in spectral form, and `prod_sQ`: for odd `M` the query signs multiply
to `qtot`. Statements follow OpenAI's `rational_query`, `sum_primeQueryExponent`;
proofs are written for this tree. -/

namespace OAI.Computability.NearSquareRoot.KernelPass
open Matrix Finset

variable {M u : ℕ}


lemma eA_zero (p : Fin (M + u)) : eA (M + u) (0, p) = pos1 p := by
  ext; simp [eA, pos1, finProdFinEquiv]
lemma eA_one (p : Fin (M + u)) : eA (M + u) (1, p) = pos2 p := by
  ext; simp [eA, pos2, finProdFinEquiv]; omega

/-- The sign of the pair `p` of a column. -/
def qp (p : Fin (M + u)) (x : Column (2 * (M + u))) : ℚ := qc (pos1 p) (pos2 p) x

lemma qc_zip (p : Fin (M + u)) (x : Column (2 * (M + u))) :
    qc (A := 2) 0 1 (zipE (M + u) x p) = qp p x := by
  show sgn2 (x (eA (M + u) (0, p))) (x (eA (M + u) (1, p))) = _
  rw [eA_zero, eA_one]; rfl

/-- Per-pair sign selector of query `j`: active on pair `j` and on the auxiliary pairs. -/
def dsel (j : Fin M) (p : Fin (M + u)) (z : Column 2) : ℚ :=
  Fin.addCases (fun i : Fin M => if i = j then qc 0 1 z else 1) (fun _ : Fin u => qc 0 1 z) p

/-- The column sign of query `j`. -/
def sQ (j : Fin M) (x : Column (2 * (M + u))) : ℚ := ∏ p, dsel j p (zipE (M + u) x p)

theorem sQ_eq (j : Fin M) (x : Column (2 * (M + u))) :
    sQ j x = qp (dpair j) x * ∏ a : Fin u, qp (apair a) x := by
  rw [sQ, Fin.prod_univ_add]
  congr 1
  · simp only [dsel, Fin.addCases_left]
    rw [Finset.prod_ite_eq' Finset.univ j (fun i => qc (A := 2) 0 1 (zipE (M + u) x (Fin.castAdd u i)))]
    simp only [Finset.mem_univ, if_true]
    exact qc_zip (dpair j) x
  · refine Finset.prod_congr rfl fun a _ => ?_
    simp only [dsel, Fin.addCases_right]
    exact qc_zip (apair a) x

lemma diag_sQ (j : Fin M) : diagonal (sQ (u := u) j) =
    (piMat fun p => diagonal (dsel j p)).submatrix (zipE (M + u)) (zipE (M + u)) := by
  rw [piMat_diagonal']
  ext y x
  simp only [diagonal_apply, submatrix_apply, (zipE (M + u)).injective.eq_iff]
  rfl

/-- The column kernel of query `j`. -/
def colK (j : Fin M) : ColMat (2 * (M + u)) :=
  walshCol (2 * (M + u)) * diagonal (sQ j) * walshCol (2 * (M + u))

/-- The two-axis query kernel. -/
def Kpair : ColMat 2 := walshCol 2 * diagonal (qc 0 1) * walshCol 2

theorem Kpair_apply (y x : Column 2) :
    Kpair y x = (1 / 4 : ℚ) * chi (dot (x 0 + y 0) (x 1 + y 1)) := by
  have h2 := query_col (A := 2) (i := 0) (j := 1) (by decide)
  rw [update2_eq_walsh] at h2
  rw [Kpair, h2, Matrix.mul_diagonal, Matrix.diagonal_mul, mul_permMat_apply, walshCol_apply,
    Fin.sum_univ_two]
  have e0 : swapCol (A := 2) 0 1 x 0 = x 1 := by simp [swapCol]
  have e1 : swapCol (A := 2) 0 1 x 1 = x 0 := by simp [swapCol]
  have hd : dot (x 0 + y 0) (x 1 + y 1) =
      dot (y 0) (y 1) + (dot (y 0) (x 1) + dot (y 1) (x 0)) + dot (x 0) (x 1) := by
    simp only [dot, Pi.add_apply]; ring
  rw [e0, e1, hd]
  simp only [qc, sgn2, chi_add]
  ring

lemma diag_one_col : diagonal (fun _ : Column 2 => (1 : ℚ)) = 1 := diagonal_one

lemma walsh_dsel_dist (j i : Fin M) : walshCol 2 * diagonal (dsel (u := u) j (Fin.castAdd u i)) * walshCol 2 =
    if i = j then Kpair else 1 := by
  by_cases hij : i = j
  · rw [if_pos hij]
    have : dsel (u := u) j (Fin.castAdd u i) = qc 0 1 := by
      funext z; simp only [dsel, Fin.addCases_left, if_pos hij]
    rw [this]; rfl
  · rw [if_neg hij]
    have : dsel (u := u) j (Fin.castAdd u i) = fun _ => 1 := by
      funext z; simp only [dsel, Fin.addCases_left, if_neg hij]
    rw [this, diag_one_col, Matrix.mul_one, walshCol_sq]

lemma walsh_dsel_aux (j : Fin M) (a : Fin u) :
    walshCol 2 * diagonal (dsel j (Fin.natAdd M a)) * walshCol 2 = Kpair := by
  have : dsel j (Fin.natAdd M a) = qc 0 1 := by
    funext z; simp only [dsel, Fin.addCases_right]
  rw [this]; rfl

/-- The column kernel as a product over the pairs. -/
theorem colK_prod (j : Fin M) (y x : Column (2 * (M + u))) :
    colK j y x =
      (∏ i : Fin M, (if i = j then Kpair else (1 : ColMat 2))
          (zipE (M + u) y (dpair i)) (zipE (M + u) x (dpair i))) *
        ∏ a : Fin u, Kpair (zipE (M + u) y (apair a)) (zipE (M + u) x (apair a)) := by
  have e : colK (u := u) j = (piMat fun p => walshCol 2 * diagonal (dsel j p) * walshCol 2).submatrix
      (zipE (M + u)) (zipE (M + u)) := by
    rw [colK, walshCol_zip, diag_sQ, submatrix_mul_equiv, submatrix_mul_equiv, piMat_mul, piMat_mul]
  rw [e, submatrix_apply, piMat, Fin.prod_univ_add]
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun i _ => ?_) (Finset.prod_congr rfl fun a _ => ?_)
  · rw [walsh_dsel_dist]; rfl
  · rw [walsh_dsel_aux]; rfl

/-! ## The bridge -/

lemma zip_zero (p : Fin (M + u)) (x : Column (2 * (M + u))) : zipE (M + u) x p 0 = x (pos1 p) := by
  show x (eA (M + u) (0, p)) = _; rw [eA_zero]
lemma zip_one (p : Fin (M + u)) (x : Column (2 * (M + u))) : zipE (M + u) x p 1 = x (pos2 p) := by
  show x (eA (M + u) (1, p)) = _; rw [eA_one]

/-- The product of the two half bits of pair `p` on the difference of two letters. -/
def pbit (p : Fin (M + u)) (x y : Bits (2 * (M + u))) : ZMod 2 :=
  (x (pos1 p) + y (pos1 p)) * (x (pos2 p) + y (pos2 p))

lemma dotV_act (j : Fin M) (x y : Bits (2 * (M + u))) :
    dotV (act j x + act j y) (act' j x + act' j y) =
      pbit (dpair j) x y + ∑ a : Fin u, pbit (apair a) x y := by
  simp only [dotV, dotProduct, Fin.sum_univ_succ, Pi.add_apply, act, act', Fin.cons_zero,
    Fin.cons_succ, pbit]

lemma dot_zip (p : Fin (M + u)) (x y : Column (2 * (M + u))) :
    dot (zipE (M + u) x p 0 + zipE (M + u) y p 0) (zipE (M + u) x p 1 + zipE (M + u) y p 1) =
      ∑ t : Fin 2, pbit p (letterAt x t) (letterAt y t) := by
  rw [zip_zero, zip_zero, zip_one, zip_one, Fin.sum_univ_two]
  simp only [dot, Pi.add_apply, pbit, letterAt]

lemma Kpair_zip (p : Fin (M + u)) (y x : Column (2 * (M + u))) :
    Kpair (zipE (M + u) y p) (zipE (M + u) x p) =
      (1 / 4 : ℚ) * ∏ t : Fin 2, chi (pbit p (letterAt x t) (letterAt y t)) := by
  rw [Kpair_apply, dot_zip, chi_sum]

/-- **Bridge.** The column kernel of query `j` is the letter kernel `Uq j` on both letters,
normalized by `(1/2)^(2D)`, `D = u + 1`. -/
theorem colK_apply (j : Fin M) (y x : Column (2 * (M + u))) :
    colK j y x = (1 / 2 : ℚ) ^ (2 * (u + 1)) * ∏ t : Fin 2, Uq j (letterAt y t) (letterAt x t) := by
  rw [colK_prod]
  by_cases S : ∀ i : Fin M, i ≠ j → zipE (M + u) y (dpair i) = zipE (M + u) x (dpair i)
  · have hfirst : (∏ i : Fin M, (if i = j then Kpair else (1 : ColMat 2))
        (zipE (M + u) y (dpair i)) (zipE (M + u) x (dpair i))) =
        Kpair (zipE (M + u) y (dpair j)) (zipE (M + u) x (dpair j)) := by
      rw [Finset.prod_eq_single j]
      · rw [if_pos rfl]
      · intro i _ hi; rw [if_neg hi, S i hi, Matrix.one_apply_eq]
      · exact fun hu => absurd (Finset.mem_univ _) hu
    have hspect : ∀ t, spect j (letterAt y t) = spect j (letterAt x t) := by
      intro t; funext i
      have h0 : y (pos1 (dpair i.1)) t = x (pos1 (dpair i.1)) t := by
        have := congrFun (congrFun (S i.1 i.2) 0) t
        rw [← eA_zero]; exact this
      have h1 : y (pos2 (dpair i.1)) t = x (pos2 (dpair i.1)) t := by
        have := congrFun (congrFun (S i.1 i.2) 1) t
        rw [← eA_one]; exact this
      simp only [spect, letterAt, h0, h1]
    rw [hfirst]
    simp only [Uq, if_pos (hspect _), Kpair_zip, dotV_act, chi_add, chi_sum]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, Finset.prod_comm (s := (Finset.univ : Finset (Fin 2)))]
    have hc : (1 / 2 : ℚ) ^ (2 * (u + 1)) = (1 / 4) * (1 / 4) ^ u := by
      rw [pow_mul, pow_succ]; norm_num; ring
    rw [hc]; ring
  · push_neg at S
    obtain ⟨i, hi, hne⟩ := S
    have hz : (∏ i : Fin M, (if i = j then Kpair else (1 : ColMat 2))
        (zipE (M + u) y (dpair i)) (zipE (M + u) x (dpair i))) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by rw [if_neg hi, Matrix.one_apply_ne hne])
    rw [hz, zero_mul]
    obtain ⟨a, t, hat⟩ : ∃ a t, zipE (M + u) y (dpair i) a t ≠ zipE (M + u) x (dpair i) a t := by
      by_contra hc; push_neg at hc
      exact hne (funext fun a => funext fun t => hc a t)
    have hsp : spect j (letterAt y t) ≠ spect j (letterAt x t) := by
      intro hh
      have h2 := congrFun hh ⟨i, hi⟩
      simp only [spect, letterAt, Prod.mk.injEq] at h2
      have ha : a = 0 ∨ a = 1 := by fin_cases a <;> simp
      rcases ha with rfl | rfl
      · apply hat; have := h2.1; rw [← eA_zero] at this; exact this
      · apply hat; have := h2.2; rw [← eA_one] at this; exact this
    rw [Finset.prod_eq_zero (Finset.mem_univ t) (by rw [Uq, if_neg hsp]), mul_zero]

/-- The width-`h` kernel of query `j`: the column kernel on every column. -/
theorem piMat_colK (h : ℕ) (j : Fin M) :
    piMat (fun _ : Fin h => colK (u := u) j) = ((1 / 2 : ℚ) ^ (2 * (u + 1) * h)) • lift h (Uq j) := by
  ext y x
  simp only [piMat, colK_apply, Matrix.smul_apply, lift, smul_eq_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]

/-- **Spectral form of the query block.** -/
theorem lift_Uq_spectral (h : ℕ) (j : Fin M) :
    ((1 / 2 : ℚ) ^ (2 * (u + 1) * h)) • lift h (Uq (u := u) j) =
      Wh (2 * (M + u)) h * diagonal (fun y => ∏ c, sQ j (y c)) * Wh (2 * (M + u)) h := by
  rw [← piMat_colK, Wh, ← piMat_diagonal (sQ (u := u) j), piMat_mul, piMat_mul]
  rfl

lemma qp_sq (p : Fin (M + u)) (x : Column (2 * (M + u))) : qp p x * qp p x = 1 := by
  simp only [qp, qc, sgn2, ← chi_add]
  have h : ∀ a : ZMod 2, a + a = 0 := by decide
  rw [h]; rfl

/-- **Product identity.** For an odd number of queries the query signs multiply to the total
sign `qtot` (every auxiliary pair is counted an odd number of times). -/
theorem prod_sQ (hM : Odd M) (x : Column (2 * (M + u))) : ∏ j : Fin M, sQ j x = qtot x := by
  simp only [sQ_eq]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hY : (∏ a : Fin u, qp (apair (M := M) a) x) * (∏ a : Fin u, qp (apair (M := M) a) x) = 1 := by
    rw [← Finset.prod_mul_distrib]; exact Finset.prod_eq_one fun a _ => qp_sq _ x
  have hpow : (∏ a : Fin u, qp (apair (M := M) a) x) ^ M = ∏ a : Fin u, qp (apair (M := M) a) x := by
    have gen : ∀ (Y : ℚ) (n : ℕ), Y * Y = 1 → Odd n → Y ^ n = Y := by
      intro Y n h ⟨r, hr⟩
      rw [hr, pow_succ, pow_mul, pow_two, h, one_pow, one_mul]
    exact gen _ M hY hM
  rw [hpow, qtot, Fin.prod_univ_add]
  congr 1
  · exact Finset.prod_congr rfl fun i _ => by rw [eA_zero, eA_one]; rfl
  · exact Finset.prod_congr rfl fun a _ => by rw [eA_zero, eA_one]; rfl

end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.KernelBridge =====

-- ===== begin KP.ChargedPlan =====
section
/-! # The charged factorization as rational plans

`comQ j` is the common plan of query `j`: `2D` calls (`D = u + 1`), and it implements the
letter kernel `Uq j` (`implements_comQ`, from the bridge `piMat_colK`). `glEquiv j c` is the
chart map as a linear equivalence of letters, so it is a call-free plan. **`charged_routed`**:
for every family of charts there are call-free `inp v`, `out w` with, at every width and for
every pair of labels,
`qBlk h (out w) * qBlk h (comQ j) * qBlk h (inp v) = (1/2)^(2D·h) • lift h (U c j w v)`.
This is the hypothesis `hch` of `routed_eval` (chunk KP.QRouting) for the kernel
`H h j w v := (1/2)^(2D·h) • lift h (U c j w v)`. Follows OpenAI's `rectangleData_factors`;
proofs are written for this tree. -/

namespace OAI.Computability.NearSquareRoot.KernelPass
open Matrix Finset

variable {M u : ℕ}

/-! ## The common plan -/

/-- The active axis pairs of query `j`. -/
def qPairs (j : Fin M) : List (Fin (2 * (M + u)) × Fin (2 * (M + u))) :=
  (pos1 (dpair j), pos2 (dpair j)) :: List.ofFn fun a : Fin u => (pos1 (apair a), pos2 (apair a))

lemma qPairs_ne (j : Fin M) : ∀ g ∈ qPairs (u := u) j, g.1 ≠ g.2 := by
  intro g hg
  rw [qPairs, List.mem_cons, List.mem_ofFn] at hg
  rcases hg with rfl | ⟨a, rfl⟩ <;> exact pos1_ne_pos2 _ _

lemma multiSign_qPairs (j : Fin M) : multiSign (qPairs (u := u) j) = sQ j := by
  funext x
  rw [multiSign, qPairs, List.map_cons, List.prod_cons, List.map_ofFn, List.prod_ofFn, sQ_eq]
  rfl

/-- The common plan of query `j`. -/
def comQ (j : Fin M) : QPlan (2 * (M + u)) 1 1 := (multiQuery (qPairs (u := u) j))

theorem comQ_calls (j : Fin M) : (comQ (u := u) j).calls = 2 * (u + 1) := by
  rw [comQ, multiQuery_calls, qPairs, List.length_cons, List.length_ofFn]

theorem implements_comQ (j : Fin M) : Implements (comQ (u := u) j) (Uq j) (2 * (u + 1)) := by
  intro h
  rw [← piMat_colK]
  ext y x
  have h1 := multiQuery_oneRow (h := h) (qPairs (u := u) j) (qPairs_ne j) y x
  rw [multiSign_qPairs] at h1
  simp only [qBlk, comQ]
  exact h1

/-! ## The chart map is a linear equivalence of letters -/

lemma act_add (j : Fin M) (x y : Bits (2 * (M + u))) : act j (x + y) = act j x + act j y := by
  funext i; refine Fin.cases ?_ (fun a => ?_) i <;> simp [act]
lemma act'_add (j : Fin M) (x y : Bits (2 * (M + u))) : act' j (x + y) = act' j x + act' j y := by
  funext i; refine Fin.cases ?_ (fun a => ?_) i <;> simp [act']
lemma act_smul (j : Fin M) (r : ZMod 2) (x : Bits (2 * (M + u))) : act j (r • x) = r • act j x := by
  funext i; refine Fin.cases ?_ (fun a => ?_) i <;> simp [act]
lemma act'_smul (j : Fin M) (r : ZMod 2) (x : Bits (2 * (M + u))) : act' j (r • x) = r • act' j x := by
  funext i; refine Fin.cases ?_ (fun a => ?_) i <;> simp [act']

/-- A letter is determined by its active vectors and its spectator bits. -/
theorem letter_ext (j : Fin M) {x y : Bits (2 * (M + u))} (h1 : act j x = act j y)
    (h2 : act' j x = act' j y) (h3 : spect j x = spect j y) : x = y := by
  have key : ∀ p : Fin (M + u), x (pos1 p) = y (pos1 p) ∧ x (pos2 p) = y (pos2 p) := by
    intro p
    refine Fin.addCases (fun i => ?_) (fun a => ?_) p
    · by_cases hij : i = j
      · subst hij
        have a1 := congrFun h1 0
        have a2 := congrFun h2 0
        simp only [act, act', Fin.cons_zero] at a1 a2
        exact ⟨a1, a2⟩
      · have a3 := congrFun h3 ⟨i, hij⟩
        simp only [spect, Prod.mk.injEq] at a3
        exact a3
    · have a1 := congrFun h1 a.succ
      have a2 := congrFun h2 a.succ
      simp only [act, act', Fin.cons_succ] at a1 a2
      exact ⟨a1, a2⟩
  funext i
  by_cases hi : i.val < M + u
  · have : i = pos1 ⟨i.val, hi⟩ := Fin.ext rfl
    rw [this]; exact (key _).1
  · have hlt : i.val - (M + u) < M + u := by have := i.2; omega
    have : i = pos2 ⟨i.val - (M + u), hlt⟩ := Fin.ext (by simp only [pos2]; omega)
    rw [this]; exact (key _).2

/-- The inverse chart. -/
def Chart.inv (c : Chart u) : Chart u :=
  ⟨c.psiᵀ, c.phiᵀ, by rw [Matrix.transpose_transpose]; exact mul_eq_one_comm.mp c.dual⟩

lemma Chart.dual' (c : Chart u) : c.phiᵀ * c.psi = 1 := by
  have := congrArg Matrix.transpose c.dual
  rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this

theorem gl_inv_gl (j : Fin M) (c : Chart u) (x : Bits (2 * (M + u))) : gl j c.inv (gl j c x) = x := by
  refine letter_ext j ?_ ?_ ?_
  · rw [act_gl, act_gl, Matrix.mulVec_mulVec]
    show (c.psiᵀ * c.phi) *ᵥ act j x = act j x
    rw [c.dual, Matrix.one_mulVec]
  · rw [act'_gl, act'_gl, Matrix.mulVec_mulVec]
    show (c.phiᵀ * c.psi) *ᵥ act' j x = act' j x
    rw [c.dual', Matrix.one_mulVec]
  · rw [spect_gl, spect_gl]

theorem gl_gl_inv (j : Fin M) (c : Chart u) (x : Bits (2 * (M + u))) : gl j c (gl j c.inv x) = x := by
  refine letter_ext j ?_ ?_ ?_
  · rw [act_gl, act_gl, Matrix.mulVec_mulVec]
    show (c.phi * c.psiᵀ) *ᵥ act j x = act j x
    rw [mul_eq_one_comm.mp c.dual, Matrix.one_mulVec]
  · rw [act'_gl, act'_gl, Matrix.mulVec_mulVec]
    show (c.psi * c.phiᵀ) *ᵥ act' j x = act' j x
    rw [mul_eq_one_comm.mp c.dual', Matrix.one_mulVec]
  · rw [spect_gl, spect_gl]

lemma spect_add (j : Fin M) (x y : Bits (2 * (M + u))) :
    spect j (x + y) = fun i => ((spect j x i).1 + (spect j y i).1, (spect j x i).2 + (spect j y i).2) := by
  funext i; simp [spect]

/-- The chart map as a linear equivalence of letters. -/
noncomputable def glEquiv (j : Fin M) (c : Chart u) :
    Bits (2 * (M + u)) ≃ₗ[ZMod 2] Bits (2 * (M + u)) where
  toFun := gl j c
  map_add' x y := by
    refine letter_ext j ?_ ?_ ?_
    · rw [act_gl, act_add, act_add, Matrix.mulVec_add, act_gl, act_gl]
    · rw [act'_gl, act'_add, act'_add, Matrix.mulVec_add, act'_gl, act'_gl]
    · rw [spect_gl, spect_add, spect_add, spect_gl, spect_gl]
  map_smul' r x := by
    refine letter_ext j ?_ ?_ ?_
    · rw [act_gl, act_smul, Matrix.mulVec_smul, RingHom.id_apply, act_smul, act_gl]
    · rw [act'_gl, act'_smul, Matrix.mulVec_smul, RingHom.id_apply, act'_smul, act'_gl]
    · rw [spect_gl]; funext i; simp [spect, gl_s1 j c x i.2, gl_s2 j c x i.2]
  invFun := gl j c.inv
  left_inv := gl_inv_gl j c
  right_inv := gl_gl_inv j c

/-! ## The factorization -/

variable {ι : Type*}

/-- Letter level: the label kernel is `relabel · query · relabel`. -/
theorem U_eq_linMat (c : ι → Chart u) (j : Fin M) (w v : ι) :
    U c j w v = linMat (gl j (c w).inv) * Uq j * linMat (gl j (c v)) := by
  rw [U_eq_submatrix]
  ext y x
  rw [mul_linMat, linMat_inv_mul (gl_inv_gl j (c w)) (gl_gl_inv j (c w))]
  rfl

/-- **Charged factorization, in the form `routed_eval` consumes.** -/
theorem charged_routed (c : ι → Chart u) (j : Fin M) :
    ∃ inp out : ι → QPlan (2 * (M + u)) 1 1, (∀ v, (inp v).calls = 0) ∧ (∀ w, (out w).calls = 0) ∧
      ∀ h w v, qBlk h (out w) * qBlk h (comQ j) * qBlk h (inp v) =
        ((1 / 2 : ℚ) ^ (2 * (u + 1) * h)) • lift h (U c j w v) := by
  have hi : ∀ v, ∃ p : QPlan (2 * (M + u)) 1 1, p.calls = 0 ∧
      Implements p (linMat (gl j (c v))) 0 := fun v => exists_letterLinPlan_equiv (glEquiv j (c v))
  have ho : ∀ w, ∃ p : QPlan (2 * (M + u)) 1 1, p.calls = 0 ∧
      Implements p (linMat (gl j (c w).inv)) 0 := fun w =>
    exists_letterLinPlan_equiv (glEquiv j (c w)).symm
  choose inp hi0 hi1 using hi
  choose out ho0 ho1 using ho
  refine ⟨inp, out, hi0, ho0, fun h w v => ?_⟩
  rw [ho1 w h, hi1 v h, implements_comQ j h, U_eq_linMat, lift_mul, lift_mul]
  simp only [zero_mul, pow_zero, one_smul, Matrix.mul_smul, Matrix.smul_mul]

/-! ## The seam for the Horner stage: test, diagonal blocks, product -/

/-- The test of query `j` on a column: its sign exponent. -/
def testQ (c : Column (2 * (M + u))) (j : Fin M) : ZMod 2 :=
  dot (c (pos1 (dpair j))) (c (pos2 (dpair j))) +
    ∑ a : Fin u, dot (c (pos1 (apair a))) (c (pos2 (apair a)))

theorem sQ_test (j : Fin M) (c : Column (2 * (M + u))) : sQ j c = chi (testQ c j) := by
  rw [sQ_eq, testQ, chi_add, chi_sum]; rfl

theorem prod_sQ_spat (h : ℕ) (v : Addr (2 * (M + u)) h) (j : Fin M) :
    (∏ c, sQ j (v c)) = chi (spat (testQ (M := M) (u := u)) v j) := by
  simp only [sQ_test]
  rw [spat, Finset.sum_apply, chi_sum]

/-- **Diagonal blocks (`hself`).** The diagonal block of the label kernel is
`Wh · diag (chi (pattern j)) · Wh`. -/
theorem label_self_spectral (c : ι → Chart u) (j : Fin M) (l : ι) (h : ℕ) :
    ((1 / 2 : ℚ) ^ (2 * (u + 1) * h)) • lift h (U c j l l) =
      Wh (2 * (M + u)) h * diagonal (fun v => chi (spat (testQ (M := M) (u := u)) v j)) *
        Wh (2 * (M + u)) h := by
  rw [U_self, lift_Uq_spectral]
  congr 2; congr 1; funext v; exact prod_sQ_spat h v j

/-- **Product (`hz`).** For odd `M` the total sign is the product of the query signs of the
pattern. -/
theorem qtot_spat (hM : Odd M) (h : ℕ) (v : Addr (2 * (M + u)) h) :
    (∏ c, qtot (v c)) = ∏ j : Fin M, chi (spat (testQ (M := M) (u := u)) v j) := by
  simp only [← prod_sQ_spat]
  rw [Finset.prod_comm]
  exact Finset.prod_congr rfl fun c _ => (prod_sQ hM (v c)).symm

end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.ChargedPlan =====

-- ===== begin KP.Horner =====
section
/-! # The univariate count predictor, over ℚ

With rational mixes the predictor is a univariate polynomial in the count:
`upred u D t = (-1)^u Σ_{h ≤ D} tprod (t - u) h`, `tprod τ h = ∏_{i<h} (-2)(τ - i)/(i + 1)`,
and `upred_exact`: `u ≤ n ≤ u + D → upred u D n = (-1)^n`. The Horner stages themselves are in
chunk KP.HornerStage (over any stage plan). No subsets, no clock/shift pencil, no cyclotomic ring. -/

namespace OAI.Computability.NearSquareRoot.KernelPass
open Matrix Finset

/-! ## Scalars -/

/-- The stage coefficient. -/
def cstep (τ : ℚ) (h : ℕ) : ℚ := (-2) * (τ - h) / (h + 1)

/-- `T_h = ∏_{i<h} c_i`. -/
def tprod (τ : ℚ) (h : ℕ) : ℚ := ∏ i ∈ range h, cstep τ i

theorem tprod_nat (n h : ℕ) : tprod n h = (-2) ^ h * (n.choose h : ℚ) := by
  induction h with
  | zero => simp [tprod]
  | succ h ih =>
    have hq : ((n.choose (h + 1) : ℕ) : ℚ) * (h + 1) = (n.choose h : ℚ) * ((n : ℚ) - h) := by
      by_cases hn : h ≤ n
      · have := Nat.choose_succ_right_eq n h
        rw [← Nat.cast_sub hn]; exact_mod_cast this
      · rw [Nat.choose_eq_zero_of_lt (by omega : n < h + 1), Nat.choose_eq_zero_of_lt (by omega : n < h)]
        simp
    have h1 : ((h : ℚ) + 1) ≠ 0 := by positivity
    have hq' : ((n.choose (h + 1) : ℕ) : ℚ) = (n.choose h : ℚ) * ((n : ℚ) - h) / (h + 1) := by
      rw [eq_div_iff h1]; exact hq
    unfold tprod at ih ⊢
    rw [prod_range_succ, ih, cstep, pow_succ, hq']
    ring

/-- The univariate predictor: `(-1)^u Σ_{h ≤ D} T_h(t - u)`. -/
def upred (u D : ℕ) (t : ℚ) : ℚ := (-1) ^ u * ∑ h ∈ range (D + 1), tprod (t - u) h

/-- Exactness on the window. -/
theorem upred_exact (u D n : ℕ) (hlo : u ≤ n) (hhi : n ≤ u + D) : upred u D n = (-1) ^ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hlo
  have hk : k ≤ D := by omega
  have hc : ((u + k : ℕ) : ℚ) - u = (k : ℕ) := by push_cast; ring
  unfold upred
  rw [hc]
  simp only [tprod_nat]
  have hsum : ∑ h ∈ range (D + 1), (-2 : ℚ) ^ h * (k.choose h : ℚ) = (-1) ^ k := by
    have h2 := add_pow (-2 : ℚ) 1 k
    rw [show (-2 : ℚ) + 1 = -1 by norm_num] at h2
    simp only [one_pow, mul_one] at h2
    rw [h2]
    symm
    refine sum_subset (range_mono (by omega)) fun i _ hi => ?_
    rw [Nat.choose_eq_zero_of_lt (by simpa only [mem_range, Order.lt_add_one_iff, not_le] using hi)]
    simp only [CharP.cast_eq_zero, mul_zero]
  rw [hsum, pow_add]

/-! ## The stage and the chain as rational plans -/

variable {A : ℕ}

/-- The shifted count minus `u`, as a rational function of the signs. -/
def tauQ {m : ℕ} (σ s : Fin m → ℚ) (u : ℕ) : ℚ := ∑ k, (1 - σ k * s k) / 2 - u

end OAI.Computability.NearSquareRoot.KernelPass

namespace OAI.Computability.NearSquareRoot.KernelPass
open Matrix Finset

variable {A : ℕ}

/-- On `±1` shifts and signs the rational count is the natural count of `cnt`. -/
theorem sum_xs_eq_cnt {m : ℕ} {σ s : Fin m → ℚ} (hσ : ∀ j, σ j = 1 ∨ σ j = -1)
    (hs : ∀ j, s j = 1 ∨ s j = -1) : ∑ k, (1 - σ k * s k) / 2 = (cnt (xs σ s) : ℚ) := by
  have h01 : ∀ j, (1 - σ j * s j) / 2 = if xs σ s j = 1 then 1 else 0 := by
    intro j; unfold xs
    rcases hσ j with h1 | h1 <;> rcases hs j with h2 | h2 <;> rw [h1, h2] <;> norm_num
  rw [sum_congr rfl fun j _ => h01 j, cnt, Finset.sum_boole]

end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.Horner =====

-- ===== begin KP.Repair =====
section
/-! # Vandermonde checks for the repair

`repairCheck ρ s` (`H t u = ρ u ^ t`) and `tableMat L d = Lᵀ · diag(d) · L`. Adapted from OpenAI's
PrimeRepairVandermonde.lean (`repairCheck`, `repairCheck_leftInverse`); proofs written for this
tree. The left inverse used here is `intNodes_leftInverse` (chunk KP.RepairQ: integer nodes, any
`j ≤ s` columns have a left inverse). The rational template repairs by division (chunk KP.RepairQ),
so no Hermite filter is needed. -/

namespace OAI.Computability.NearSquareRoot.KernelPass
open Matrix
open scoped BigOperators

variable {R : Type*} [CommRing R]

/-- Vandermonde checks `H t u = ρ u ^ t`. -/
def repairCheck {W : ℕ} (ρ : Fin W → R) (s : ℕ) : Matrix (Fin s) (Fin W) R := fun t u => ρ u ^ t.val

/-- The table matrix `Lᵀ · diag(d) · L` on the `s` check rows. -/
def tableMat {j s : ℕ} (L : Matrix (Fin j) (Fin s) R) (d : Fin j → R) : Matrix (Fin s) (Fin s) R :=
  Lᵀ * diagonal d * L

end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.Repair =====

-- ===== begin KP.RepairQ =====
section
/-! # Division repair over a field, and integer check nodes

Over a field the Hermite filter is not needed: the table divides by `p - z` on the exceptional
rows (`0⁻¹ = 0` covers exceptional rows that happen to predict correctly).
`division_repair_mat`: `P - (P - z)·Hᵀ·T·H·(P - z) = z` with `T = Lᵀ diag((p - z)⁻¹) L`.
No condition on `z`.
`intNodes_leftInverse`: over ℚ the nodes `0, 1, …, W-1` work; no cyclotomic nodes. -/

namespace OAI.Computability.NearSquareRoot.KernelPass
open Matrix

/-- **Division repair**: `P - (P - z)·Hᵀ·T·H·(P - z) = z` for `P = diag p`, `T = Lᵀ diag((p - z)⁻¹) L`. -/
theorem division_repair_mat {W s j : ℕ} (z : ℚ) (p : Fin W → ℚ) (H : Matrix (Fin s) (Fin W) ℚ)
    (e : Fin j ↪ Fin W) (L : Matrix (Fin j) (Fin s) ℚ) (hL : L * H.submatrix id e = 1)
    (hsupp : ∀ i ∉ Set.range e, p i = z) :
    diagonal p - (diagonal p - z • 1) * (Hᵀ * tableMat L (fun k => (p (e k) - z)⁻¹) * H) *
      (diagonal p - z • 1) = z • (1 : Matrix (Fin W) (Fin W) ℚ) := by
  have hd : diagonal p - z • (1 : Matrix (Fin W) (Fin W) ℚ) = diagonal fun i => p i - z := by
    ext i k; by_cases hik : i = k <;> simp [hik]
  let Sel : Matrix (Fin j) (Fin W) ℚ := of fun k i => if i = e k then p i - z else 0
  have hsel : ∀ i i', (Selᵀ * diagonal (fun k => (p (e k) - z)⁻¹) * Sel) i i' =
      if i = i' then p i - z else 0 := by
    intro i i'
    rw [mul_apply]
    simp only [mul_diagonal, transpose_apply, Sel, of_apply]
    by_cases hi : i ∈ Set.range e
    · obtain ⟨k, rfl⟩ := hi
      rw [Finset.sum_eq_single k (fun k' _ hk' => by simp [e.injective.ne (Ne.symm hk')])
        (fun hu => absurd (Finset.mem_univ _) hu)]
      by_cases hk : e k = i'
      · subst hk
        rcases eq_or_ne (p (e k) - z) 0 with h0 | h0
        · simp [h0]
        · simp only [if_true]; field_simp
      · simp [Ne.symm hk, hk]
    · have hn : ∀ k, (i = e k) = False := fun k => eq_false fun h => hi ⟨k, h.symm⟩
      simp only [hn, if_false, zero_mul, Finset.sum_const_zero]
      split_ifs with h
      · rw [hsupp i hi, sub_self]
      · rfl
  have hLH : L * H * diagonal (fun i => p i - z) = Sel := by
    ext k i
    simp only [mul_diagonal, Sel, of_apply]
    by_cases hi : i ∈ Set.range e
    · obtain ⟨k', rfl⟩ := hi
      have h1 : (L * H) k (e k') = (1 : Matrix (Fin j) (Fin j) ℚ) k k' := congrFun (congrFun hL k) k'
      rw [h1, one_apply]
      simp [e.injective.eq_iff, eq_comm]
    · have hn : ∀ k, (i = e k) = False := fun k => eq_false fun h => hi ⟨k, h.symm⟩
      simp [hsupp i hi, hn]
  rw [hd, tableMat, show diagonal (fun i => p i - z) * (Hᵀ * (Lᵀ * diagonal (fun k => (p (e k) - z)⁻¹) * L) * H) *
      diagonal (fun i => p i - z) = (L * H * diagonal (fun i => p i - z))ᵀ *
        diagonal (fun k => (p (e k) - z)⁻¹) * (L * H * diagonal (fun i => p i - z)) by
    simp only [transpose_mul, diagonal_transpose, Matrix.mul_assoc], hLH]
  ext i i'
  rw [Matrix.sub_apply, hsel]
  by_cases h : i = i' <;> simp [h]

/-- Integer nodes: over ℚ any `j ≤ s` columns of the Vandermonde checks at `0, …, W-1` have a
left inverse. -/
theorem intNodes_leftInverse {W s j : ℕ} (hjs : j ≤ s) (e : Fin j ↪ Fin W) :
    ∃ L : Matrix (Fin j) (Fin s) ℚ,
      L * (repairCheck (fun u : Fin W => ((u : ℕ) : ℚ)) s).submatrix id e = 1 := by
  set V := (vandermonde fun k => ((e k : ℕ) : ℚ))ᵀ
  have hV : IsUnit V.det := by
    rw [det_transpose]
    exact isUnit_iff_ne_zero.2 (det_vandermonde_ne_zero_iff.2 fun a b h => e.injective (Fin.ext (by exact_mod_cast h)))
  refine ⟨V⁻¹ * of fun (t : Fin j) (t' : Fin s) => if (t : ℕ) = t' then (1 : ℚ) else 0, ?_⟩
  rw [Matrix.mul_assoc, show (of fun (t : Fin j) (t' : Fin s) => if (t : ℕ) = t' then (1 : ℚ) else 0) *
    (repairCheck (fun u : Fin W => ((u : ℕ) : ℚ)) s).submatrix id e = V from ?_, nonsing_inv_mul _ hV]
  ext t k
  rw [mul_apply, Finset.sum_eq_single ⟨t, t.2.trans_le hjs⟩]
  · simp +contextual only [of_apply, ↓reduceIte, submatrix_apply, repairCheck, id_eq, one_mul,
      vandermonde, transpose_apply, V]
  · simp +contextual only [Finset.mem_univ, ne_eq, Fin.ext_iff, eq_comm, of_apply, ↓reduceIte,
      submatrix_apply, repairCheck, id_eq, zero_mul, implies_true, imp_self]
  · exact fun hu => absurd (Finset.mem_univ _) hu

end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.RepairQ =====

-- ===== begin KP.QTemplate =====
section
/-! # A correct rational template from any predictor bank

`template k W out` is `chirps ∘ out ∘ chirps ∘ swaps` on `W` rows. If `out` has spectrum
`z v = ∏_c qtot (v c)` on every row, the template is `QCorrect` (`template_correct`), and its
calls are those of `out` (`template_calls`).

`repairOut Pb Ta Tz H` is the division repair as a plan:
`P − P·U·P + P·V + V·P − U` with `U = Hᵀ·T·H`, `V = z·U`, which equals
`P − (P − z)·U·(P − z)` when `z² = 1`. `repairOut_spec`: if `Pb` has spectrum `diag (p v)`,
the tables have spectra `T v` and `z v • T v`, and the per-frequency repair identity holds,
then `repairOut` has spectrum `z v • 1`. `division_repair_mat` supplies that identity. Calls: `5·Pb + 2·Ta + 2·Tz` (`repairOut_calls`).

Everything is generic in how `Pb` is computed, so a routed (shared) predictor bank can replace
an unshared one without touching this file. -/

namespace OAI.Computability.NearSquareRoot.KernelPass
open Matrix Finset

variable {A : ℕ}

/-! ## Linear combinations of rational plans -/

theorem Fdr_add_smul {h o i : ℕ} (a b : ℚ) (F G : Addr A h → Matrix (Fin o) (Fin i) ℚ) :
    Fdr (fun v => a • F v + b • G v) = a • Fdr F + b • Fdr G := by
  ext ⟨r, y⟩ ⟨c, x⟩
  simp only [Fdr, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp

theorem specR_add_smul {h o i : ℕ} (a b : ℚ) (F G : Addr A h → Matrix (Fin o) (Fin i) ℚ) :
    specR (fun v => a • F v + b • G v) = a • specR F + b • specR G := by
  simp only [specR, Fdr_add_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]

/-! ## The same column matrix on every row -/

/-- `M` on each of `W` rows. -/
def rowsOf {h : ℕ} (W : ℕ) (M : Matrix (Addr A h) (Addr A h) ℚ) : RowMatrix A h W W :=
  fun p q => if q.1 = p.1 then M p.2 q.2 else 0

theorem Kw_eq_rowsOf (h W : ℕ) : Kw A h W = rowsOf W (Wh A h) := rfl

theorem rowsOf_mul {h W : ℕ} (M N : Matrix (Addr A h) (Addr A h) ℚ) :
    rowsOf W M * rowsOf W N = rowsOf W (M * N) := by
  ext ⟨b, y⟩ ⟨a, x⟩
  rw [mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single b]
  · simp only [rowsOf, if_true]
    by_cases hab : a = b
    · simp [hab, mul_apply]
    · simp [hab]
  · intro c _ hc
    simp [rowsOf, hc]
  · exact fun hu => absurd (Finset.mem_univ _) hu

theorem Fdr_scalar {h W : ℕ} (z : Addr A h → ℚ) :
    Fdr (fun v => z v • (1 : Matrix (Fin W) (Fin W) ℚ)) = rowsOf W (diagonal z) := by
  ext ⟨b, y⟩ ⟨a, x⟩
  simp only [Fdr, rowsOf, Matrix.smul_apply, one_apply, diagonal_apply, smul_eq_mul]
  by_cases hyx : y = x <;> by_cases hab : b = a
  · subst hyx; subst hab; simp
  · simp [hyx, hab, Ne.symm hab]
  · subst hab; simp [hyx]
  · simp [hyx, hab, Ne.symm hab]

theorem spec_scalar {h W : ℕ} (z : Addr A h → ℚ) :
    specR (fun v => z v • (1 : Matrix (Fin W) (Fin W) ℚ)) = rowsOf W (Wh A h * diagonal z * Wh A h) := by
  rw [specR, Fdr_scalar, Kw_eq_rowsOf, rowsOf_mul, rowsOf_mul]

theorem rowBank_const {h : ℕ} (W : ℕ) (p : QPlan A 1 1) (C : ColMat A) (hp : OneRow (p.eval h) C) :
    (rowBank W fun _ => p).eval h = rowsOf W (piMat fun _ : Fin h => C) := by
  ext ⟨b, y⟩ ⟨a, x⟩
  rw [rowBank_apply]
  simp only [rowsOf]
  split_ifs
  · exact hp y x
  · rfl

/-! ## The template -/

/-- `chirps ∘ out ∘ chirps ∘ swaps` on `W` rows of arity `2k`. -/
def template (k W : ℕ) (out : QPlan (2 * k) W W) : QPlan (2 * k) W W :=
  .seq (rowBank W fun _ => chirpAll k)
    (.seq out (.seq (rowBank W fun _ => chirpAll k) (rowBank W fun _ => swapAllPlan k)))

theorem template_calls (k W : ℕ) (out : QPlan (2 * k) W W) : (template k W out).calls = out.calls := by
  have hc : (chirpAll k).calls = 0 := rfl
  simp only [template, QPlan.calls, rowBank_calls, swapAllPlan_calls, hc, Finset.sum_const_zero,
    zero_add, add_zero]

/-- **Template correctness.** A plan whose spectrum is the query-sign product on every row
becomes the Walsh target after free chirps and swaps. -/
theorem template_correct (k W : ℕ) (out : QPlan (2 * k) W W)
    (hout : ∀ h, out.eval h = specR fun v : Addr (2 * k) h =>
      (∏ c, qtot (v c)) • (1 : Matrix (Fin W) (Fin W) ℚ)) :
    QCorrect (template k W out) := by
  intro h
  simp only [template, qeval_seq]
  rw [hout h, spec_scalar, rowBank_const W _ _ chirpAll_oneRow, rowBank_const W _ _ swapAllPlan_oneRow,
    rowsOf_mul, rowsOf_mul, rowsOf_mul, target_eq_Kw, Kw_eq_rowsOf]
  congr 1
  rw [Wh, ← piMat_diagonal (ι := Fin h) (qtot (k := k)), piMat_mul, piMat_mul, piMat_mul, piMat_mul,
    piMat_mul]
  congr 1
  funext _
  conv_rhs => rw [walsh_of_WDW (k := k)]
  simp only [Matrix.mul_assoc]

/-! ## The division repair as a plan -/

/-- `Hᵀ · T · H` with the table plan `Tb` on the check rows. -/
def checkLoop {W s : ℕ} (H : Matrix (Fin s) (Fin W) ℚ) (Tb : QPlan A s s) : QPlan A W W :=
  .seq (.mix Hᵀ) (.seq Tb (.mix H))

/-- `P − P·U·P + P·V + V·P − U`. -/
def repairOut {W s : ℕ} (Pb : QPlan A W W) (Ta Tz : QPlan A s s) (H : Matrix (Fin s) (Fin W) ℚ) :
    QPlan A W W :=
  qadd 1 1 Pb (qadd (-1) 1 (.seq Pb (.seq (checkLoop H Ta) Pb))
    (qadd 1 1 (.seq Pb (checkLoop H Tz)) (qadd 1 (-1) (.seq (checkLoop H Tz) Pb) (checkLoop H Ta))))

theorem repairOut_calls {W s : ℕ} (Pb : QPlan A W W) (Ta Tz : QPlan A s s)
    (H : Matrix (Fin s) (Fin W) ℚ) :
    (repairOut Pb Ta Tz H).calls = 5 * Pb.calls + 2 * Ta.calls + 2 * Tz.calls := by
  simp only [repairOut, qadd_calls, checkLoop, QPlan.calls]; ring

theorem checkLoop_spec {h W s : ℕ} (H : Matrix (Fin s) (Fin W) ℚ) (Tb : QPlan A s s)
    (T : Addr A h → Matrix (Fin s) (Fin s) ℚ) (hT : Tb.eval h = specR T) :
    (checkLoop H Tb).eval h = specR fun v => Hᵀ * T v * H := by
  simp only [checkLoop, qeval_seq]
  rw [qmix_specR, qmix_specR, hT, specR_mul, specR_mul]
  congr 1; funext v; rw [Matrix.mul_assoc]

theorem repair_alg {n : Type*} [Fintype n] [DecidableEq n] (P U V : Matrix n n ℚ) (z : ℚ)
    (hz : z * z = 1) (hV : V = z • U) :
    (1 : ℚ) • P + (1 : ℚ) • ((-1 : ℚ) • (P * (U * P)) + (1 : ℚ) • ((1 : ℚ) • (P * V) +
      (1 : ℚ) • ((1 : ℚ) • (V * P) + (-1 : ℚ) • U))) = P - (P - z • 1) * U * (P - z • 1) := by
  subst hV
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, smul_sub, smul_smul, hz, one_smul, neg_smul, Matrix.mul_assoc, one_mul]
  abel

/-- **Repair plan.** Given the predictor bank, the two table plans and the per-frequency repair
identity, the output has spectrum `z v` on every row. -/
theorem repairOut_spec {h W s : ℕ} (Pb : QPlan A W W) (Ta Tz : QPlan A s s)
    (H : Matrix (Fin s) (Fin W) ℚ) (p : Addr A h → Fin W → ℚ) (z : Addr A h → ℚ)
    (T : Addr A h → Matrix (Fin s) (Fin s) ℚ)
    (hPb : Pb.eval h = specR fun v => diagonal (p v)) (hTa : Ta.eval h = specR T)
    (hTz : Tz.eval h = specR fun v => z v • T v) (hz : ∀ v, z v * z v = 1)
    (hrep : ∀ v, diagonal (p v) - (diagonal (p v) - z v • 1) * (Hᵀ * T v * H) *
      (diagonal (p v) - z v • 1) = z v • (1 : Matrix (Fin W) (Fin W) ℚ)) :
    (repairOut Pb Ta Tz H).eval h = specR fun v => z v • (1 : Matrix (Fin W) (Fin W) ℚ) := by
  have hU := checkLoop_spec H Ta T hTa
  have hV := checkLoop_spec H Tz (fun v => z v • T v) hTz
  simp only [repairOut, qadd_eval, qeval_seq, hU, hV, hPb]
  simp only [specR_mul, ← specR_add_smul]
  congr 1; funext v
  rw [← hrep v]
  exact repair_alg _ _ _ _ (hz v) (by simp only [Matrix.mul_smul, Matrix.smul_mul])

end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.QTemplate =====

-- ===== begin KP.QAssembly =====
section
/-! # Assembly: predictor bank + tables ⇒ a correct rational template

`qtot_mul_self`, `zprod_mul_self`: the pair-sign product `qtot` and its product over the columns
of an address square to 1. The row bank `rowBank` is in chunk KP.Spec, the Horner bank `hornerBankS`
in chunk KP.HornerTemplate. -/

namespace OAI.Computability.NearSquareRoot.KernelPass
open Matrix Finset

variable {A : ℕ}

lemma qtot_mul_self {k : ℕ} (x : Column (2 * k)) : qtot x * qtot x = 1 := by
  rw [qtot, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun p _ => by simp only [qc, sgn2, chi]; split_ifs <;> norm_num

lemma zprod_mul_self {k h : ℕ} (v : Addr (2 * k) h) :
    (∏ c, qtot (v c)) * (∏ c, qtot (v c)) = 1 := by
  rw [← Finset.prod_mul_distrib]; exact Finset.prod_eq_one fun c _ => qtot_mul_self _


end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.QAssembly =====

-- ===== begin KP.QFreq =====
section
/-! # Rational frequency tables

`qfreqMat test M` applies, per frequency `v`, the rational matrix `M (spat test v)`; it is the
rational frequency-table plan (pieces in chunk KP.FreqTable); `horner_template` uses it
for the repair tables. -/

namespace OAI.Computability.NearSquareRoot.KernelPass
open Matrix Finset

variable {A : ℕ}

theorem qmix_Fdr {h i o : ℕ} (M : Matrix (Fin o) (Fin i) ℚ) :
    (QPlan.mix (A := A) M).eval h = Fdr fun _ => M := by
  ext ⟨b, y⟩ ⟨a, x⟩
  simp only [eval_mix_apply, Fdr]; by_cases hxy : x = y
  · simp [hxy]
  · simp [hxy, Ne.symm hxy]

section
variable {q n : ℕ} (test : Column A → Fin q → ZMod 2)
  (M : (Fin q → ZMod 2) → Matrix (Fin n) (Fin n) ℚ)

/-- Row `(r,c)` scales by `M e r c`. -/
def qentryScale (u : Fin (n * n)) : QPlan A 1 1 :=
  .scale q test fun e => M e (rI u) (cI u)

theorem qscaleBank_eval {h : ℕ} :
    (rowBank (n * n) (qentryScale test M)).eval h =
      Fdr fun v : Addr A h => diagonal fun u => M (spat test v) (rI u) (cI u) := by
  ext ⟨b, y⟩ ⟨a, x⟩
  rw [rowBank_apply]
  simp only [qentryScale, eval_scale_apply, Fdr, diagonal_apply, spat]
  by_cases hab : a = b
  · subst hab; by_cases hxy : x = y
    · subst hxy; simp
    · simp [hxy, Ne.symm hxy]
  · simp [hab, Ne.symm hab]

/-- Per frequency, the rational matrix `M (spat test v)`. -/
def qfreqMat : QPlan A n n :=
  .seq (rowBank n fun _ => rowPlan A) (.seq (.mix fanInT)
    (.seq (rowBank (n * n) (qentryScale test M)) (.seq (.mix fanOutT) (rowBank n fun _ => rowPlan A))))

theorem qfreqMat_calls : (qfreqMat test M).calls = 2 * (n * A) := by
  simp only [qfreqMat, QPlan.calls, rowBank_calls, qentryScale, rowPlan, chainPlan_calls,
    List.length_finRange, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    Finset.sum_const_zero, zero_add, add_zero]
  ring

theorem qfreqMat_spec {h : ℕ} :
    (qfreqMat test M).eval h = specR fun v : Addr A h => M (spat test v) := by
  simp only [qfreqMat, qeval_seq]
  rw [bank_rowPlan_eval, qmix_Fdr, qscaleBank_eval, qmix_Fdr]
  have e : (Fdr fun _ : Addr A h => (fanInT : Matrix (Fin n) (Fin (n * n)) ℚ)) *
      (Fdr fun v : Addr A h => diagonal fun u => M (spat test v) (rI u) (cI u)) *
      (Fdr fun _ : Addr A h => (fanOutT : Matrix (Fin (n * n)) (Fin n) ℚ)) =
      Fdr fun v : Addr A h => M (spat test v) := by
    rw [Fdr_mul, Fdr_mul]; congr 1; funext v; exact fanT_freq _
  rw [show (specR fun v : Addr A h => M (spat test v)) = Kw A h n * ((Fdr fun _ : Addr A h =>
      (fanInT : Matrix (Fin n) (Fin (n * n)) ℚ)) *
      (Fdr fun v : Addr A h => diagonal fun u => M (spat test v) (rI u) (cI u)) *
      (Fdr fun _ : Addr A h => (fanOutT : Matrix (Fin (n * n)) (Fin n) ℚ))) * Kw A h n by
    rw [e]; rfl]
  simp only [Matrix.mul_assoc]
end

end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.QFreq =====

-- ===== begin KP.HornerStage =====
section
/-! # Horner predictor over a shared stage, and the shift-row routed stage

* `hornerPb m u D Sg`: the univariate predictor on all rows at once, from any *stage* plan
  `Sg` whose spectrum on row `r` is `Σ_k σ r k · s_k(v)`. It uses `Sg` exactly `D` times
  (`hornerPb_calls`) and has spectrum `upred u D (Σ_k (1 - σ r k · s_k(v))/2)` on row `r`
  (`hornerPb_spec`). The routed stage below is the `Sg` used.
* `liftCh`, `liftFr`: label-level rectangles copied to every shift row (rows = label × shift).
  `shift_eval`, `shift_calls`, `shift_stage_spec`: the routed plan on `N·R` rows is a stage in
  the above sense, with calls `≤ d·(2·(N·R)·inc + |J|·(|C|·R))`. -/

namespace OAI.Computability.NearSquareRoot.KernelPass
open Matrix Finset

variable {A n : ℕ}

/-! ## Scalar Horner -/

def aStep (m u h : ℕ) : ℚ := (-2) * ((m : ℚ) / 2 - u - h) / (h + 1)
def bStep (h : ℕ) : ℚ := 1 / (h + 1)

theorem cstep_affine {m : ℕ} (σ s : Fin m → ℚ) (u h : ℕ) :
    cstep (tauQ σ s u) h = aStep m u h + bStep h * ∑ k, σ k * s k := by
  have h1 : ((h : ℚ) + 1) ≠ 0 := by positivity
  have e2 : ∑ k : Fin m, (1 - σ k * s k) / 2 = (m : ℚ) / 2 - (∑ k : Fin m, σ k * s k) * (1 / 2) := by
    calc _ = ∑ k : Fin m, ((1 / 2 : ℚ) - σ k * s k * (1 / 2)) := sum_congr rfl fun k _ => by ring
      _ = _ := by rw [sum_sub_distrib, ← Finset.sum_mul]; simp; ring
  unfold cstep tauQ aStep bStep
  rw [e2]; field_simp; ring

/-- `Σ_{h ≤ k} ∏_{l < h} c (i + l)` by Horner's rule. -/
def hq (c : ℕ → ℚ) : ℕ → ℕ → ℚ
  | _, 0 => 1
  | i, k + 1 => 1 + c i * hq c (i + 1) k

theorem hq_eq (c : ℕ → ℚ) : ∀ k i, hq c i k = ∑ h ∈ range (k + 1), ∏ l ∈ range h, c (i + l)
  | 0, i => by simp [hq]
  | k + 1, i => by
    rw [hq, hq_eq c k (i + 1), sum_range_succ' _ (k + 1), prod_range_zero, add_comm, mul_sum]
    congr 1
    refine sum_congr rfl fun h _ => ?_
    rw [prod_range_succ', Nat.add_zero, mul_comm]
    congr 1
    exact prod_congr rfl fun l _ => by rw [Nat.add_assoc, Nat.add_comm 1 l]

theorem hq_upred {m : ℕ} (σ s : Fin m → ℚ) (u D : ℕ) :
    (-1 : ℚ) ^ u * hq (fun l => aStep m u l + bStep l * ∑ k, σ k * s k) 0 D =
      upred u D (∑ k, (1 - σ k * s k) / 2) := by
  rw [hq_eq, upred]
  congr 1
  refine sum_congr rfl fun h _ => ?_
  rw [tprod]
  refine prod_congr rfl fun l _ => ?_
  rw [Nat.zero_add, ← cstep_affine]; rfl

/-! ## The predictor bank over a stage plan -/

theorem spec_diag_mul {h : ℕ} (f g : Addr A h → Fin n → ℚ) :
    specR (fun v => diagonal (f v)) * specR (fun v => diagonal (g v)) =
      specR fun v => diagonal fun r => f v r * g v r := by
  rw [specR_mul]; congr 1; funext v
  show diagonal (f v) * diagonal (g v) = _
  rw [diagonal_mul_diagonal]

theorem diag_affine (a b : ℚ) (d : Fin n → ℚ) :
    a • (1 : Matrix (Fin n) (Fin n) ℚ) + b • diagonal d = diagonal fun r => a + b * d r := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

/-- `a + b·Σ` on every row, for a stage `Sg` with spectrum `Σ`. -/
def stepPlan (a b : ℚ) (Sg : QPlan A n n) : QPlan A n n := qadd a b (.mix 1) Sg

theorem stepPlan_spec {h : ℕ} (a b : ℚ) (Sg : QPlan A n n) (c : Addr A h → Fin n → ℚ)
    (hSg : Sg.eval h = specR fun v => diagonal (c v)) :
    (stepPlan a b Sg).eval h = specR fun v => diagonal fun r => a + b * c v r := by
  rw [stepPlan, qadd_eval, qmix_specR, hSg, ← specR_add_smul]
  congr 1; funext v; exact diag_affine a b (c v)

/-- Horner stages `i, …, i+k-1` on every row. -/
def hornerP (m u : ℕ) (Sg : QPlan A n n) : ℕ → ℕ → QPlan A n n
  | _, 0 => .mix 1
  | i, k + 1 => qadd 1 1 (.mix 1) (.seq (stepPlan (aStep m u i) (bStep i) Sg) (hornerP m u Sg (i + 1) k))

theorem hornerP_calls (m u : ℕ) (Sg : QPlan A n n) : ∀ k i, (hornerP m u Sg i k).calls = k * Sg.calls
  | 0, _ => by rw [zero_mul]; rfl
  | k + 1, i => by
    rw [hornerP, qadd_calls]
    simp only [QPlan.calls, stepPlan, qadd_calls, hornerP_calls m u Sg k (i + 1)]
    ring

theorem hornerP_spec {h : ℕ} (m u : ℕ) (Sg : QPlan A n n) (c : Addr A h → Fin n → ℚ)
    (hSg : Sg.eval h = specR fun v => diagonal (c v)) : ∀ k i,
    (hornerP m u Sg i k).eval h =
      specR fun v => diagonal fun r => hq (fun l => aStep m u l + bStep l * c v r) i k
  | 0, i => by
    rw [hornerP, qmix_specR]; congr 1
  | k + 1, i => by
    rw [hornerP, qadd_eval, qmix_specR, qeval_seq, stepPlan_spec _ _ Sg c hSg,
      hornerP_spec m u Sg c hSg k (i + 1), spec_diag_mul,
      ← specR_add_smul]
    congr 1; funext v
    rw [diag_affine]
    congr 1; funext r
    simp [hq]

/-- The predictor bank: `D` Horner stages over the stage plan, then the sign `(-1)^u`. -/
def hornerPb (m u D : ℕ) (Sg : QPlan A n n) : QPlan A n n :=
  .seq (.mix (((-1 : ℚ) ^ u) • (1 : Matrix (Fin n) (Fin n) ℚ))) (hornerP m u Sg 0 D)

theorem hornerPb_calls (m u D : ℕ) (Sg : QPlan A n n) : (hornerPb m u D Sg).calls = D * Sg.calls := by
  rw [hornerPb, QPlan.calls, hornerP_calls]; exact zero_add _

/-- **Predictor from a stage.** If the stage has spectrum `Σ_k σ r k · s v k` on row `r`, the
bank has spectrum `upred u D (Σ_k (1 - σ r k · s v k)/2)` on row `r`. -/
theorem hornerPb_spec {h m : ℕ} (u D : ℕ) (Sg : QPlan A n n) (σ : Fin n → Fin m → ℚ)
    (s : Addr A h → Fin m → ℚ)
    (hSg : Sg.eval h = specR fun v => diagonal fun r => ∑ k, σ r k * s v k) :
    (hornerPb m u D Sg).eval h =
      specR fun v => diagonal fun r => upred u D (∑ k, (1 - σ r k * s v k) / 2) := by
  rw [hornerPb, qeval_seq, qmix_specR, hornerP_spec m u Sg _ hSg D 0, specR_mul]
  congr 1; funext v
  rw [smul_mul_assoc, Matrix.one_mul]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.smul_apply, diagonal_apply_eq, smul_eq_mul]
    exact hq_upred (σ i) (s v) u D
  · simp [hij]

end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.HornerStage =====

-- ===== begin KP.ShiftRows =====
section
/-! # The routed stage on label × shift rows

Rows are `Fin (N * R)`, read as (label, shift row) through `finProdFinEquiv`. Every label-level
rectangle is copied once per shift row. `shift_eval`: the routed plan is label- and
shift-diagonal with block `Σ_j a t j • Hl j λ λ`. `shift_calls`: the bound of `routed_calls`
with `|C|·R` charged rectangles and unchanged incidence. `shift_stage_spec`: if the diagonal
kernels are the queries, the routed plan is a stage for `hornerPb`. -/

namespace OAI.Computability.NearSquareRoot.KernelPass
open Matrix Finset

variable {A N R : ℕ} {J : Type*} [Fintype J]

/-- Label of a row. -/
def lab (t : Fin (N * R)) : Fin N := (finProdFinEquiv.symm t).1
/-- Shift row of a row. -/
def shf (t : Fin (N * R)) : Fin R := (finProdFinEquiv.symm t).2

lemma lab_shf_ext {t s : Fin (N * R)} (h1 : lab s = lab t) (h2 : shf s = shf t) : s = t := by
  apply finProdFinEquiv.symm.injective
  exact Prod.ext h1 h2

/-- A set of labels at one shift row. -/
def liftSet (S : Finset (Fin N)) (ρ : Fin R) : Finset (Fin (N * R)) :=
  Finset.univ.filter fun t => lab t ∈ S ∧ shf t = ρ

lemma mem_liftSet {S : Finset (Fin N)} {ρ : Fin R} {t : Fin (N * R)} :
    t ∈ liftSet S ρ ↔ lab t ∈ S ∧ shf t = ρ := by
  rw [liftSet, Finset.mem_filter]; exact and_iff_right (Finset.mem_univ _)

/-- A charged rectangle at shift row `ρ`. -/
def liftCh (c : QCharged A N J) (ρ : Fin R) : QCharged A (N * R) J where
  S := liftSet c.S ρ
  T := liftSet c.T ρ
  w := c.w
  inp := fun j t => c.inp j (lab t)
  out := fun j t => c.out j (lab t)
  com := c.com

/-- A free rectangle at shift row `ρ`. -/
def liftFr (f : QFree A N J) (ρ : Fin R) : QFree A (N * R) J where
  S := liftSet f.S ρ
  T := liftSet f.T ρ
  w := f.w
  src := fun t => f.src (lab t)
  tgt := fun t => f.tgt (lab t)
  mid := fun j t s => f.mid j (lab t) (lab s)

lemma sum_shift (P Q : Prop) [Decidable P] [Decidable Q] (a b : Fin R) (w : ℚ) :
    (∑ ρ : Fin R, if (P ∧ a = ρ) ∧ (Q ∧ b = ρ) then w else 0) =
      if a = b then (if P ∧ Q then w else 0) else 0 := by
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl, Finset.sum_eq_single a]
    · by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]
    · intro ρ _ hρ; rw [if_neg]; intro hh; exact hρ hh.1.2.symm
    · simp
  · rw [if_neg hab]
    refine Finset.sum_eq_zero fun ρ _ => ?_
    rw [if_neg]; intro hh; exact hab (hh.1.2.trans hh.2.2.symm)

variable {C F : Type*} [Fintype C] [Fintype F]

/-- **Routed stage on label × shift rows, correctness.** -/
theorem shift_eval (h : ℕ) (ch : C → QCharged A N J) (fr : F → QFree A N J)
    (a : Fin (N * R) → J → ℚ) (Hl : J → Fin N → Fin N → Matrix (Addr A h) (Addr A h) ℚ)
    (hch : ∀ c j t s, t ∈ (ch c).T → s ∈ (ch c).S →
      qBlk h ((ch c).out j t) * qBlk h ((ch c).com j) * qBlk h ((ch c).inp j s) = Hl j t s)
    (hfr : ∀ f j t s, t ∈ (fr f).T → s ∈ (fr f).S →
      qBlk h ((fr f).tgt t) * qBlk h ((fr f).mid j t s) * qBlk h ((fr f).src s) = Hl j t s)
    (hId : ∀ t s, (∑ c, if t ∈ (ch c).T ∧ s ∈ (ch c).S then (ch c).w else 0) +
      (∑ f, if t ∈ (fr f).T ∧ s ∈ (fr f).S then (fr f).w else 0) = if s = t then 1 else 0)
    (t s : Fin (N * R)) (y x : Addr A h) :
    (routed (fun p : C × Fin R => liftCh (ch p.1) p.2) (fun p : F × Fin R => liftFr (fr p.1) p.2)
      a).eval h (t, y) (s, x) =
      if s = t then (∑ j, a t j • Hl j (lab t) (lab t)) y x else 0 := by
  refine routed_eval h _ _ a (fun j t s => Hl j (lab t) (lab s)) ?_ ?_ ?_ t s y x
  · intro p j t s ht hs
    exact hch p.1 j _ _ (mem_liftSet.mp ht).1 (mem_liftSet.mp hs).1
  · intro p j t s ht hs
    exact hfr p.1 j _ _ (mem_liftSet.mp ht).1 (mem_liftSet.mp hs).1
  · intro t s
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    have e1 : ∀ c : C, (∑ ρ : Fin R, if t ∈ (liftCh (ch c) ρ).T ∧ s ∈ (liftCh (ch c) ρ).S then
        (liftCh (ch c) ρ).w else 0) =
        if shf t = shf s then (if lab t ∈ (ch c).T ∧ lab s ∈ (ch c).S then (ch c).w else 0) else 0 := by
      intro c
      rw [← sum_shift]
      exact Finset.sum_congr rfl fun ρ _ => by
        simp only [liftCh, mem_liftSet]
    have e2 : ∀ f : F, (∑ ρ : Fin R, if t ∈ (liftFr (fr f) ρ).T ∧ s ∈ (liftFr (fr f) ρ).S then
        (liftFr (fr f) ρ).w else 0) =
        if shf t = shf s then (if lab t ∈ (fr f).T ∧ lab s ∈ (fr f).S then (fr f).w else 0) else 0 := by
      intro f
      rw [← sum_shift]
      exact Finset.sum_congr rfl fun ρ _ => by
        simp only [liftFr, mem_liftSet]
    simp only [e1, e2]
    by_cases hsh : shf t = shf s
    · simp only [if_pos hsh]
      rw [hId (lab t) (lab s)]
      by_cases hst : s = t
      · subst hst; simp only [↓reduceIte]
      · rw [if_neg hst, if_neg]
        intro hl; exact hst (lab_shf_ext hl hsh.symm)
    · simp only [if_neg hsh, Finset.sum_const_zero, add_zero]
      rw [if_neg]; intro hst; exact hsh (by rw [hst])

/-- **Routed stage on label × shift rows, calls.** -/
theorem shift_calls (ch : C → QCharged A N J) (fr : F → QFree A N J) (a : Fin (N * R) → J → ℚ)
    (d inc : ℕ)
    (hci : ∀ c j s, ((ch c).inp j s).calls = 0) (hco : ∀ c j t, ((ch c).out j t).calls = 0)
    (hcc : ∀ c j, ((ch c).com j).calls ≤ d)
    (hfm : ∀ f j t s, ((fr f).mid j t s).calls = 0)
    (hfs : ∀ f s, ((fr f).src s).calls ≤ d) (hft : ∀ f t, ((fr f).tgt t).calls ≤ d)
    (hincS : ∀ s, (Finset.univ.filter fun f => s ∈ (fr f).S).card ≤ inc)
    (hincT : ∀ t, (Finset.univ.filter fun f => t ∈ (fr f).T).card ≤ inc) :
    (routed (fun p : C × Fin R => liftCh (ch p.1) p.2) (fun p : F × Fin R => liftFr (fr p.1) p.2)
      a).calls ≤ d * (2 * (N * R) * inc + Fintype.card J * (Fintype.card C * R)) := by
  have key : ∀ (sd : F → Finset (Fin N)) (r : Fin (N * R)),
      (Finset.univ.filter fun f => lab r ∈ sd f).card ≤ inc →
      (Finset.univ.filter fun p : F × Fin R => r ∈ liftSet (sd p.1) p.2).card ≤ inc := by
    intro sd r hr
    refine le_trans (Finset.card_le_card_of_injOn (fun p => p.1) ?_ ?_) hr
    · intro p hp
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, mem_liftSet] at hp ⊢
      exact hp.1
    · intro p hp p' hp' hpp
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, mem_liftSet] at hp hp'
      exact Prod.ext hpp (hp.2.symm.trans hp'.2)
  have := routed_calls (fun p : C × Fin R => liftCh (ch p.1) p.2)
    (fun p : F × Fin R => liftFr (fr p.1) p.2) a d inc
    (fun p j s => hci p.1 j _) (fun p j t => hco p.1 j _) (fun p j => hcc p.1 j)
    (fun p j t s => hfm p.1 j _ _) (fun p s => hfs p.1 _) (fun p t => hft p.1 _)
    (fun s => key (fun f => (fr f).S) s (hincS _)) (fun t => key (fun f => (fr f).T) t (hincT _))
  simpa only [ge_iff_le, Fintype.card_prod, Fintype.card_fin] using this

lemma wdw_apply {h : ℕ} (d : Addr A h → ℚ) (y x : Addr A h) :
    (Wh A h * diagonal d * Wh A h) y x = ∑ z, Wh A h y z * d z * Wh A h z x := by
  rw [Matrix.mul_apply]
  exact Finset.sum_congr rfl fun z _ => by rw [Matrix.mul_diagonal]

/-- **The routed plan is a Horner stage.** If every diagonal kernel `Hl j λ λ` is the query
`Wh · diag(sgn · j) · Wh`, the routed plan has spectrum `Σ_j a r j · sgn v j` on row `r`. -/
theorem shift_stage_spec (h : ℕ) (ch : C → QCharged A N J) (fr : F → QFree A N J)
    (a : Fin (N * R) → J → ℚ) (Hl : J → Fin N → Fin N → Matrix (Addr A h) (Addr A h) ℚ)
    (sgn : Addr A h → J → ℚ)
    (hch : ∀ c j t s, t ∈ (ch c).T → s ∈ (ch c).S →
      qBlk h ((ch c).out j t) * qBlk h ((ch c).com j) * qBlk h ((ch c).inp j s) = Hl j t s)
    (hfr : ∀ f j t s, t ∈ (fr f).T → s ∈ (fr f).S →
      qBlk h ((fr f).tgt t) * qBlk h ((fr f).mid j t s) * qBlk h ((fr f).src s) = Hl j t s)
    (hId : ∀ t s, (∑ c, if t ∈ (ch c).T ∧ s ∈ (ch c).S then (ch c).w else 0) +
      (∑ f, if t ∈ (fr f).T ∧ s ∈ (fr f).S then (fr f).w else 0) = if s = t then 1 else 0)
    (hself : ∀ j l, Hl j l l = Wh A h * diagonal (fun v => sgn v j) * Wh A h) :
    (routed (fun p : C × Fin R => liftCh (ch p.1) p.2) (fun p : F × Fin R => liftFr (fr p.1) p.2)
      a).eval h = specR fun v => diagonal fun r => ∑ j, a r j * sgn v j := by
  ext ⟨t, y⟩ ⟨s, x⟩
  rw [shift_eval h ch fr a Hl hch hfr hId, spec_apply]
  by_cases hst : s = t
  · subst hst
    rw [if_pos rfl, Matrix.sum_apply]
    simp only [Matrix.smul_apply, hself, smul_eq_mul, diagonal_apply_eq, wdw_apply,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun j _ => by ring
  · rw [if_neg hst]
    symm
    refine Finset.sum_eq_zero fun z _ => ?_
    rw [diagonal_apply_ne _ (Ne.symm hst)]; ring

end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.ShiftRows =====

-- ===== begin KP.HornerTemplate =====
section
/-! # The template from a stage

`horner_template`: from any stage plan `Sg` with spectrum `Σ_j σ r j · chi (κ_j)` on row `r`
(`κ` the sign pattern of the frequency), shifts `σ = ±1`, the product identity for `qtot`, and
a bound `s` on the number of rows whose shifted count leaves the window `[u, u + D]`, the
pattern template with integer check nodes is correct and costs
`5 · D · Sg.calls + 8 · s · (2k)` calls. -/

namespace OAI.Computability.NearSquareRoot.KernelPass
open Matrix Finset

/-- A sign is `±1`. -/
lemma chi_pm (a : ZMod 2) : chi a = 1 ∨ chi a = -1 := by unfold chi; split_ifs <;> simp

section
variable {k W m : ℕ} (test : Column (2 * k) → Fin m → ZMod 2) (σ : Fin W → Fin m → ℚ) (u D : ℕ)

/-- The row sign `∏_j σ r j`. -/
def csg (r : Fin W) : ℚ := ∏ j, σ r j

/-- The predictor value of row `r` at pattern `κ`. -/
def pOfH (κ : Fin m → ZMod 2) (r : Fin W) : ℚ :=
  csg σ r * upred u D (∑ j, (1 - σ r j * chi (κ j)) / 2)

/-- The query-sign product at pattern `κ`. -/
def zOfH (κ : Fin m → ZMod 2) : ℚ := ∏ j, chi (κ j)

/-- Row `r` is in the window at pattern `κ`. -/
def InWin (κ : Fin m → ZMod 2) (r : Fin W) : Prop :=
  u ≤ cnt (xs (σ r) fun j => chi (κ j)) ∧ cnt (xs (σ r) fun j => chi (κ j)) ≤ u + D

instance (κ : Fin m → ZMod 2) (r : Fin W) : Decidable (InWin σ u D κ r) := by
  unfold InWin; infer_instance

theorem pOfH_window (hσ : ∀ r j, σ r j = 1 ∨ σ r j = -1) (κ : Fin m → ZMod 2) (r : Fin W)
    (hw : InWin σ u D κ r) : pOfH σ u D κ r = zOfH κ := by
  have hs : ∀ j, chi (κ j) = 1 ∨ chi (κ j) = -1 := fun j => chi_pm _
  rw [pOfH, sum_xs_eq_cnt (hσ r) hs, upred_exact u D _ hw.1 hw.2, neg_one_pow_cnt (hσ r) hs, csg,
    ← Finset.prod_mul_distrib, zOfH]
  refine Finset.prod_congr rfl fun j _ => ?_
  rcases hσ r j with h1 | h1 <;> rw [h1] <;> ring

/-- The predictor bank with the row signs. -/
def hornerBankS (Sg : QPlan (2 * k) W W) : QPlan (2 * k) W W :=
  .seq (.mix (diagonal (csg σ))) (hornerPb m u D Sg)

theorem hornerBankS_calls (Sg : QPlan (2 * k) W W) : (hornerBankS σ u D Sg).calls = D * Sg.calls := by
  rw [hornerBankS, QPlan.calls, hornerPb_calls]; exact zero_add _

theorem hornerBankS_spec (Sg : QPlan (2 * k) W W) (h : ℕ)
    (hSg : Sg.eval h = specR fun v : Addr (2 * k) h =>
      diagonal fun r => ∑ j, σ r j * chi (spat test v j)) :
    (hornerBankS σ u D Sg).eval h =
      specR fun v : Addr (2 * k) h => diagonal (pOfH σ u D (spat test v)) := by
  rw [hornerBankS, qeval_seq, qmix_specR,
    hornerPb_spec u D Sg σ (fun v j => chi (spat test v j)) hSg, specR_mul]
  congr 1; funext v
  rw [diagonal_mul_diagonal]; rfl

/-- **Template from a stage.** -/
theorem horner_template (s : ℕ) (Sg : QPlan (2 * k) W W)
    (hσ : ∀ r j, σ r j = 1 ∨ σ r j = -1)
    (hSg : ∀ h, Sg.eval h = specR fun v : Addr (2 * k) h =>
      diagonal fun r => ∑ j, σ r j * chi (spat test v j))
    (hz : ∀ h (v : Addr (2 * k) h), (∏ c, qtot (v c)) = zOfH (spat test v))
    (hcount : ∀ κ : Fin m → ZMod 2, (Finset.univ.filter fun r => ¬ InWin σ u D κ r).card ≤ s) :
    ∃ t : QPlan (2 * k) W W, QCorrect t ∧ t.calls = 5 * (D * Sg.calls) + 8 * (s * (2 * k)) := by
  have hfix : ∀ κ : Fin m → ZMod 2, ∃ (j : ℕ) (e : Fin j ↪ Fin W) (L : Matrix (Fin j) (Fin s) ℚ),
      L * (repairCheck (fun i : Fin W => ((i : ℕ) : ℚ)) s).submatrix id e = 1 ∧
        ∀ i ∉ Set.range e, pOfH σ u D κ i = zOfH κ := by
    intro κ
    let E := Finset.univ.filter fun r => ¬ InWin σ u D κ r
    obtain ⟨L, hL⟩ := intNodes_leftInverse (W := W) (hcount κ) (E.orderEmbOfFin rfl).toEmbedding
    refine ⟨E.card, _, L, hL, fun i hi => pOfH_window σ u D hσ κ i ?_⟩
    by_contra hn
    apply hi
    have : i ∈ Set.range (E.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩
    exact this
  choose j e L hL hsupp using hfix
  let T := fun κ => tableMat (L κ) fun k' => (pOfH σ u D κ (e κ k') - zOfH κ)⁻¹
  refine ⟨template k W (repairOut (hornerBankS σ u D Sg) (qfreqMat test T)
    (qfreqMat test fun κ => zOfH κ • T κ) (repairCheck (fun i : Fin W => ((i : ℕ) : ℚ)) s)),
    template_correct k W _ fun h => ?_, ?_⟩
  · rw [show (fun v : Addr (2 * k) h => (∏ c, qtot (v c)) • (1 : Matrix (Fin W) (Fin W) ℚ)) =
      fun v => zOfH (spat test v) • 1 from funext fun v => by rw [hz h v]]
    exact repairOut_spec _ _ _ _ (fun v => pOfH σ u D (spat test v)) (fun v => zOfH (spat test v))
      (fun v => T (spat test v)) (hornerBankS_spec test σ u D Sg h (hSg h)) (qfreqMat_spec test _)
      (qfreqMat_spec test _) (fun v => by rw [← hz h v]; exact zprod_mul_self v)
      (fun v => division_repair_mat _ _ _ (e _) (L _) (hL _) (hsupp _))
  · rw [template_calls, repairOut_calls, qfreqMat_calls, qfreqMat_calls, hornerBankS_calls]; ring

end

end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.HornerTemplate =====

-- ===== begin KP.Window =====
section
/-! # The window count on `F^m`

An elementary two-sided Chernoff count for the Hamming weight on the cube `F^m`, `F = ZMod 2`:
outside a window of half-width `t` around `m/2` there are at most `2·2^m·exp(-t²/m)` points
(`window_count`). With `m·log(4m³) ≤ t²` this is at most a `1/(2m³)` fraction
(`window_fraction`). Only `e^x ≤ 1 + x + x²` (`|x| ≤ 1`) and Markov's inequality are used. -/

open Finset Real

namespace OAI.Computability.NearSquareRoot.KernelPass

/-- Hamming weight. -/
def hamming {m : ℕ} (x : Fin m → ZMod 2) : ℕ := (univ.filter fun i => x i = 1).card

lemma hamming_sub (m : ℕ) (x : Fin m → ZMod 2) :
    (hamming x : ℝ) - m / 2 = ∑ i, ((if x i = 1 then 1 else 0 : ℝ) - 1 / 2) := by
  rw [sum_sub_distrib, sum_boole, hamming]; simp; ring

lemma sum_exp_hamming (m : ℕ) (μ : ℝ) :
    ∑ x : Fin m → ZMod 2, exp (μ * ((hamming x : ℝ) - m / 2)) = (exp (μ / 2) + exp (-(μ / 2))) ^ m := by
  simp_rw [hamming_sub, mul_sum, exp_sum]
  rw [← Fintype.prod_sum (fun (_ : Fin m) (b : ZMod 2) => exp (μ * ((if b = 1 then 1 else 0 : ℝ) - 1/2)))]
  rw [prod_const, card_univ, Fintype.card_fin]
  congr 1
  rw [show (univ : Finset (ZMod 2)) = {0, 1} from rfl, sum_pair (by decide)]
  simp only [show (0 : ZMod 2) ≠ 1 by decide, if_false, if_true]
  ring_nf

/-- `cosh x ≤ exp x²` for `|x| ≤ 1`, from `|e^x - 1 - x| ≤ x²`. -/
lemma cosh_le (x : ℝ) (hx : |x| ≤ 1) : exp x + exp (-x) ≤ 2 * exp (x ^ 2) := by
  have h1 := abs_le.1 (abs_exp_sub_one_sub_id_le hx)
  have h2 := abs_le.1 (abs_exp_sub_one_sub_id_le (x := -x) (by rwa [abs_neg]))
  have h3 := add_one_le_exp (x ^ 2)
  nlinarith

lemma one_side (m : ℕ) (hm : 0 < m) (t : ℝ) (ht0 : 0 ≤ t) (htm : t ≤ m) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    ((univ.filter fun x : Fin m → ZMod 2 => t ≤ s * ((hamming x : ℝ) - m / 2)).card : ℝ) ≤
      2 ^ m * exp (-(t ^ 2 / m)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  set μ := s * (2 * t / m) with hμ
  have hμ2 : |μ / 2| ≤ 1 := by
    have ht' : t / m ≤ 1 := (div_le_one hm').2 htm
    have hs1 : |s| = 1 := by
      rcases hs with rfl | rfl
      exacts [abs_one, by rw [abs_neg, abs_one]]
    have : |μ / 2| = t / m := by
      rw [show μ / 2 = s * (t / m) by rw [hμ]; ring, abs_mul, hs1, one_mul,
        abs_of_nonneg (div_nonneg ht0 hm'.le)]
    rw [this]; exact ht'
  have hsq : s ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
  have mark : ((univ.filter fun x : Fin m → ZMod 2 => t ≤ s * ((hamming x : ℝ) - m / 2)).card : ℝ) *
      exp (2 * t ^ 2 / m) ≤ ∑ x : Fin m → ZMod 2, exp (μ * ((hamming x : ℝ) - m / 2)) := by
    rw [card_eq_sum_ones, Nat.cast_sum, sum_mul, ← sum_filter_add_sum_filter_not univ
      (fun x : Fin m → ZMod 2 => t ≤ s * ((hamming x : ℝ) - m / 2))]
    refine le_add_of_le_of_nonneg (sum_le_sum fun x hx => ?_) (sum_nonneg fun _ _ => (exp_pos _).le)
    rw [mem_filter] at hx
    rw [Nat.cast_one, one_mul, exp_le_exp, hμ]
    have := mul_le_mul_of_nonneg_left hx.2 (show 0 ≤ 2 * t / m by positivity)
    calc 2 * t ^ 2 / m = 2 * t / m * t := by ring
      _ ≤ 2 * t / m * (s * ((hamming x : ℝ) - m / 2)) := this
      _ = _ := by ring
  rw [sum_exp_hamming] at mark
  have hc := cosh_le (μ / 2) hμ2
  have hb : (exp (μ / 2) + exp (-(μ / 2))) ^ m ≤ (2 * exp ((μ / 2) ^ 2)) ^ m :=
    pow_le_pow_left₀ (by positivity) hc m
  have he : (2 * exp ((μ / 2) ^ 2)) ^ m * exp (-(2 * t ^ 2 / m)) = 2 ^ m * exp (-(t ^ 2 / m)) := by
    rw [mul_pow, ← exp_nat_mul, mul_assoc, ← exp_add]
    congr 2
    rw [hμ]; field_simp; linear_combination t ^ 2 * hsq
  calc _ = (((univ.filter fun x : Fin m → ZMod 2 => t ≤ s * ((hamming x : ℝ) - m / 2)).card : ℝ) *
        exp (2 * t ^ 2 / m)) * exp (-(2 * t ^ 2 / m)) := by
          rw [mul_assoc, ← exp_add, add_neg_cancel, exp_zero, mul_one]
    _ ≤ (2 * exp ((μ / 2) ^ 2)) ^ m * exp (-(2 * t ^ 2 / m)) :=
        mul_le_mul_of_nonneg_right (mark.trans hb) (exp_pos _).le
    _ = _ := he

/-- The two-sided window count. -/
theorem window_count (m : ℕ) (hm : 0 < m) (t : ℝ) (ht0 : 0 ≤ t) (htm : t ≤ m) :
    ((univ.filter fun x : Fin m → ZMod 2 => t ≤ |(hamming x : ℝ) - m / 2|).card : ℝ) ≤
      2 * 2 ^ m * exp (-(t ^ 2 / m)) := by
  have e : (univ.filter fun x : Fin m → ZMod 2 => t ≤ |(hamming x : ℝ) - m / 2|) =
      (univ.filter fun x => t ≤ 1 * ((hamming x : ℝ) - m / 2)) ∪
        (univ.filter fun x => t ≤ -1 * ((hamming x : ℝ) - m / 2)) := by
    ext x; simp only [mem_filter, mem_univ, true_and, mem_union, one_mul, neg_one_mul, le_abs]
  rw [e]
  calc _ ≤ ((univ.filter fun x : Fin m → ZMod 2 => t ≤ 1 * ((hamming x : ℝ) - m / 2)).card : ℝ) +
        (univ.filter fun x : Fin m → ZMod 2 => t ≤ -1 * ((hamming x : ℝ) - m / 2)).card := by
        exact_mod_cast card_union_le _ _
    _ ≤ _ := by
      exact (add_le_add (one_side m hm t ht0 htm 1 (Or.inl rfl))
        (one_side m hm t ht0 htm (-1) (Or.inr rfl))).trans_eq (by ring)

/-- The exceptional fraction is at most `1/(2m³)` once `m·log(4m³) ≤ t²`. -/
theorem window_fraction (m : ℕ) (hm : 0 < m) (t : ℝ) (ht0 : 0 ≤ t) (htm : t ≤ m)
    (ht : m * log (4 * m ^ 3) ≤ t ^ 2) :
    ((univ.filter fun x : Fin m → ZMod 2 => t ≤ |(hamming x : ℝ) - m / 2|).card : ℝ) ≤
      2 ^ m / (2 * m ^ 3) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  refine (window_count m hm t ht0 htm).trans ?_
  have : exp (-(t ^ 2 / m)) ≤ 1 / (4 * m ^ 3) := by
    rw [← exp_log (show (0 : ℝ) < 1 / (4 * m ^ 3) by positivity), exp_le_exp, one_div, log_inv,
      neg_le_neg_iff, le_div_iff₀ hm']
    linarith
  calc 2 * 2 ^ m * exp (-(t ^ 2 / m)) ≤ 2 * 2 ^ m * (1 / (4 * m ^ 3)) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := by field_simp; ring

end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.Window =====

-- ===== begin KP.Order =====
section
/-! # The pencil order: `P(m) = ⌊√(32·m·(log₂ m + 1))⌋`

`pencilOrder_sq_le`: `P(m)² ≤ 32·m·(log₂ m + 1)`. `pencilOrder_window` shows this order is wide enough for the window count (chunk KP.Window):
`m · log(4m³) ≤ P(m)²`, the side condition of `window_fraction`. -/

namespace OAI.Computability.NearSquareRoot.KernelPass
open Real

/-- The pencil order: `⌊√(32·m·(log₂ m + 1))⌋`. -/
def pencilOrder (m : ℕ) : ℕ := Nat.sqrt (32 * m * (Nat.log 2 m + 1))

theorem pencilOrder_sq_le (m : ℕ) : pencilOrder m ^ 2 ≤ 32 * m * (Nat.log 2 m + 1) := by
  exact Nat.sqrt_le' _

/-- `8·m·(log₂ m + 1) ≤ P(m)²` for `m ≥ 1`. -/
lemma eight_le_pencilOrder_sq (m : ℕ) (hm : 0 < m) :
    8 * (m * (Nat.log 2 m + 1)) ≤ pencilOrder m ^ 2 := by
  set Y := m * (Nat.log 2 m + 1)
  have hY : 1 ≤ Y := Nat.one_le_iff_ne_zero.2 (by positivity)
  have h := Nat.lt_succ_sqrt' (32 * m * (Nat.log 2 m + 1))
  have e : 32 * m * (Nat.log 2 m + 1) = 32 * Y := by ring
  rw [e] at h
  unfold pencilOrder; rw [e]
  set P := Nat.sqrt (32 * Y)
  by_contra hc; push Not at hc
  have h2 : (2 * P) ^ 2 < (P + 1) ^ 2 := by
    calc (2 * P) ^ 2 = 4 * P ^ 2 := by ring
      _ < 32 * Y := by omega
      _ < (P + 1) ^ 2 := h
  have h3 := (Nat.pow_lt_pow_iff_left (by norm_num)).1 h2
  have hP0 : P = 0 := by omega
  rw [hP0, Nat.succ_eq_add_one, zero_add, one_pow] at h
  omega

/-- The window side condition: `m · log(4m³) ≤ P(m)²`. -/
theorem pencilOrder_window (m : ℕ) (hm : 0 < m) :
    (m : ℝ) * log (4 * m ^ 3) ≤ (pencilOrder m : ℝ) ^ 2 := by
  set L := Nat.log 2 m
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hlt : (m : ℝ) < 2 ^ (L + 1) := by exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) m
  have hlogm : log m < (L + 1) * log 2 := by
    have := Real.log_lt_log hm' hlt
    rwa [Real.log_pow, Nat.cast_add, Nat.cast_one] at this
  have hl2 : log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)]
  have hl2' : 0 < log 2 := Real.log_pos (by norm_num)
  have hlog : log (4 * m ^ 3) ≤ 8 * (L + 1) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow,
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg _
    have hL2 := mul_le_mul_of_nonneg_left hl2 (show (0 : ℝ) ≤ L + 1 by linarith only [hL])
    push_cast
    linarith only [hL2, hlogm, hl2, hL]
  have h4 : ((8 * (m * (L + 1)) : ℕ) : ℝ) ≤ (pencilOrder m : ℝ) ^ 2 := by
    exact_mod_cast eight_le_pencilOrder_sq m hm
  push_cast at h4
  calc (m : ℝ) * log (4 * m ^ 3) ≤ m * (8 * (L + 1)) := by gcongr
    _ ≤ _ := by linarith only [h4]

end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.Order =====

-- ===== begin KP.ParamsQ =====
section
/-! # Parameters for the rational template

`params_rate_side`: parameters `n b` with the side facts the assembly needs and
`q^(n+5) < A^θ`. `window_params`: for `m ≥ 2048` the window `u = m/2 - p`, `D = 2p`, `t = p`
with `p = pencilOrder m` meets the hypotheses of `shift_count`. `calls_le`: the routed Horner
template costs at most `q^(n+5)` calls per row. -/

namespace OAI.Computability.NearSquareRoot.KernelPass
open Real

/-- The rate condition the `walshTemplate_above_half` budget needs: a stage count `n` with `n + 5 < 2nθ`
(the budget is `pq^(n+5)` rows-normalised, against `pA ≥ pq^(2n)`). The 1/2 comes from this
call budget (`calls_le`: at most `q^(n+5)` calls per row, against arity `A ≥ q^(2n)`), not from
the true call rate of the template: a lower wall needs a smaller budget per row. -/
def RateOK (θ : ℝ) : Prop := ∃ n : ℕ, (n : ℝ) + 5 < 2 * n * θ

/-- **The one-half wall of `walshTemplate_above_half`**: the rate condition holds at every exponent above one half (and only there,
since `n + 5 < 2nθ` forces `θ > 1/2`). This is the one place the Walsh templates use `1/2`. -/
theorem rateOK_of_half {θ : ℝ} (hθ : 1 / 2 < θ) : RateOK θ := by
  obtain ⟨n, hn⟩ := exists_nat_gt (5 / (2 * θ - 1))
  exact ⟨n, by have h := (div_lt_iff₀ (by linarith : (0 : ℝ) < 2 * θ - 1)).1 hn; nlinarith⟩

theorem params_rate_side (θ : ℝ) (hθ : RateOK θ) : ∃ n b, 1 ≤ n ∧ 384 ≤ pq b ∧ 4 * n + 2 ≤ pq b ∧
    (1 + b) ^ pL n ≤ pq b ∧ 2 * n * b + 3 ≤ pq b ∧ (pq b : ℝ) ^ (n + 5) < (pA n b : ℝ) ^ θ := by
  obtain ⟨n, hn'⟩ := hθ
  have hθ0 : (0 : ℝ) < θ := by
    by_contra h
    have : 2 * (n : ℝ) * θ ≤ 0 := mul_nonpos_iff.mpr (Or.inl ⟨by positivity, not_lt.mp h⟩)
    linarith [n.cast_nonneg (α := ℝ)]
  have n1 : 1 ≤ n := by
    by_contra h
    have : n = 0 := by omega
    subst this; norm_num at hn'
  obtain ⟨k, hk5, hk⟩ := exists_k (4 * n + 464 + 2 * n)
  set b := 2 ^ k with hb
  have hbq : b ≤ pq b := (Nat.lt_two_pow_self).le
  have big : (4 * n + 464 + 2 * n) * (k + 1) ≤ b := hk
  have h1 : (1 + b) ^ pL n ≤ pq b := by
    calc (1 + b) ^ pL n ≤ (2 ^ (k + 1)) ^ (4 * n) := by
          simp only [pL]; gcongr; rw [hb, pow_succ]; have := Nat.one_le_two_pow (n := k); omega
      _ = 2 ^ ((k + 1) * (4 * n)) := by rw [← pow_mul]
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num)
          ((Nat.mul_le_mul_left (k + 1) (show 4 * n ≤ 4 * n + 464 + 2 * n by omega)).trans
            (by rw [mul_comm]; exact big))
  have hcb : 4 * n + 464 + 2 * n ≤ b := le_trans (Nat.le_mul_of_pos_right _ (by omega)) big
  have h4 : 2 * n * b + 3 ≤ pq b := by
    have hA1 := Nat.mul_le_mul_right b (show 2 * n + 1 ≤ b by omega)
    rw [add_mul, one_mul] at hA1
    have hbb : b * b ≤ 2 ^ b := (Nat.mul_le_mul_right b (by omega : b ≤ b + 1)).trans (sq_le_two_pow b (by omega))
    have : 2 * n * b + 3 ≤ b * b := by omega
    exact this.trans hbb
  have hA : (pq b : ℝ) ^ (2 * n) ≤ pA n b := by
    have : pq b ^ (2 * n) ≤ pA n b := by simp only [pA, pm]; omega
    exact_mod_cast this
  refine ⟨n, b, n1, by omega, by omega, h1, h4, ?_⟩
  have hq1 : (1 : ℝ) < pq b := by exact_mod_cast (show 1 < pq b by omega)
  calc (pq b : ℝ) ^ (n + 5) < (pq b : ℝ) ^ (2 * n * θ) := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_lt_rpow_of_exponent_lt hq1 (by push_cast; exact hn')
    _ ≤ (pA n b : ℝ) ^ θ := by
        rw [show (2 * n * θ : ℝ) = ((2 * n : ℕ) : ℝ) * θ by push_cast; ring, Real.rpow_mul (by positivity),
          Real.rpow_natCast]
        exact Real.rpow_le_rpow (by positivity) hA hθ0.le

lemma log_bound : ∀ l : ℕ, 11 ≤ l → 128 * (l + 1) ≤ 2 ^ l := by
  intro l hl
  induction l, hl using Nat.le_induction with
  | base => norm_num
  | succ l hl ih => rw [pow_succ]; omega

lemma log_le_self (m : ℕ) (hm : 2048 ≤ m) : 128 * (Nat.log 2 m + 1) ≤ m := by
  have h11 : 11 ≤ Nat.log 2 m := by
    have : 2 ^ 11 ≤ m := by norm_num; exact hm
    exact (Nat.le_log_iff_pow_le (by norm_num) (by omega)).mpr this
  exact (log_bound _ h11).trans (Nat.pow_log_le_self 2 (by omega))

theorem two_pencilOrder_le (m : ℕ) (hm : 2048 ≤ m) : 2 * pencilOrder m ≤ m := by
  have h1 := pencilOrder_sq_le m
  have h2 := log_le_self m hm
  have h3 : (2 * pencilOrder m) ^ 2 ≤ m ^ 2 :=
    calc (2 * pencilOrder m) ^ 2 = 4 * pencilOrder m ^ 2 := by ring
      _ ≤ 4 * (32 * m * (Nat.log 2 m + 1)) := Nat.mul_le_mul_left 4 h1
      _ = m * (128 * (Nat.log 2 m + 1)) := by ring
      _ ≤ m * m := Nat.mul_le_mul_left m h2
      _ = m ^ 2 := (sq m).symm
  exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h3

/-- The window `u = m/2 - p`, `D = 2p`, `t = p`. -/
theorem window_params (m : ℕ) (hm : 2048 ≤ m) :
    (0 : ℝ) ≤ pencilOrder m ∧ (pencilOrder m : ℝ) ≤ m ∧
      (m : ℝ) * log (4 * m ^ 3) ≤ (pencilOrder m : ℝ) ^ 2 ∧
      ((m / 2 - pencilOrder m : ℕ) : ℝ) ≤ m / 2 - pencilOrder m + 1 ∧
      (m : ℝ) / 2 + pencilOrder m ≤ (m / 2 - pencilOrder m : ℕ) + (2 * pencilOrder m : ℕ) + 1 := by
  have h2 := two_pencilOrder_le m hm
  have hp : pencilOrder m ≤ m / 2 := by omega
  have hc : ((m / 2 - pencilOrder m : ℕ) : ℝ) = ((m / 2 : ℕ) : ℝ) - pencilOrder m := Nat.cast_sub hp
  have hd1 : ((m / 2 : ℕ) : ℝ) ≤ (m : ℝ) / 2 := Nat.cast_div_le
  have hd2 : (m : ℝ) / 2 ≤ ((m / 2 : ℕ) : ℝ) + 1 / 2 := by
    have : m ≤ 2 * (m / 2) + 1 := by omega
    have : (m : ℝ) ≤ 2 * ((m / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast this
    linarith only [this]
  refine ⟨by positivity, ?_, pencilOrder_window m (by omega), ?_, ?_⟩
  · have : pencilOrder m ≤ m := by omega
    exact_mod_cast this
  · rw [hc]; linarith only [hd1]
  · rw [hc]; push_cast; linarith only [hd2]

/-- `A ≤ 2 m³` for the arity and query count of `Params.lean`. -/
theorem pA_le (n b : ℕ) (hn : 1 ≤ n) (h2 : 4 * n + 2 ≤ pq b) : pA n b ≤ 2 * pm n b ^ 3 := by
  have hq : 2 ≤ pq b := by omega
  have hqq : pq b ^ 2 ≤ pq b ^ (2 * n) := Nat.pow_le_pow_right (by omega) (by omega)
  have hLq : pL n * pq b ≤ pq b ^ 2 := by
    rw [sq]; exact Nat.mul_le_mul_right _ (by simp only [pL]; omega)
  have hm : pq b ^ 2 ≤ pm n b := by simp only [pm]; omega
  have hm2 : 2 ≤ pm n b := by
    have hsq : 2 * 2 ≤ pq b ^ 2 := by rw [sq]; exact Nat.mul_le_mul hq hq
    omega
  have hA : pA n b ≤ 2 * (3 * pm n b) := by simp only [pA, pD]; omega
  have h6 : 4 * pm n b ≤ pm n b ^ 3 := by
    rw [show pm n b ^ 3 = (pm n b * pm n b) * pm n b by ring]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul hm2 hm2 : 2 * 2 ≤ pm n b * pm n b)
  omega

/-- The routed Horner template's calls: at most `q^(n+5)` per row. -/
theorem calls_le (n b R Sg s cC : ℕ) (h1 : (1 + b) ^ pL n ≤ pq b) (h2 : 4 * n + 2 ≤ pq b)
    (h3 : 384 ≤ pq b) (h4 : 2 * n * b + 3 ≤ pq b)
    (hSg : Sg ≤ 2 * pD n b * (2 * (pN n b * R) * (1 + b) ^ pL n + pm n b * (cC * R)))
    (hC : cC ≤ 2 ^ pL n * pq b ^ (2 * n)) (hs : s * pA n b ≤ pN n b * R) :
    5 * (2 * pencilOrder (pm n b) * Sg) + 8 * (s * pA n b) ≤ pq b ^ (n + 5) * (pN n b * R) := by
  set q := pq b with hq
  have hN : pN n b = q ^ (4 * n) := rfl
  have hm : pm n b ≤ 3 * q ^ (2 * n) := by
    have := Nat.one_le_pow (2 * n) q (by omega); simp only [pm, ← hq]; omega
  have hlog : Nat.log 2 (pm n b) + 1 ≤ 2 * n * b + 3 := by
    have : pm n b < 2 ^ (2 * n * b + 2) := by
      calc pm n b ≤ 3 * q ^ (2 * n) := hm
        _ < 4 * q ^ (2 * n) := by have := Nat.one_le_pow (2 * n) q (by omega); omega
        _ = 2 ^ (2 * n * b + 2) := by rw [hq, pq, ← pow_mul, pow_add]; ring
    have hl := Nat.log_lt_of_lt_pow (b := 2) (by simp [pm] : pm n b ≠ 0) this; omega
  have hP : 2 * pencilOrder (pm n b) ≤ q ^ (n + 1) := by
    have h := pencilOrder_sq_le (pm n b)
    have : (2 * pencilOrder (pm n b)) ^ 2 ≤ (q ^ (n + 1)) ^ 2 := by
      calc (2 * pencilOrder (pm n b)) ^ 2 ≤ 128 * pm n b * (Nat.log 2 (pm n b) + 1) := by
            rw [mul_pow]; exact (Nat.mul_le_mul_left _ h).trans_eq (by ring)
        _ ≤ 128 * (3 * q ^ (2 * n)) * q := Nat.mul_le_mul (Nat.mul_le_mul_left _ hm) (hlog.trans h4)
        _ ≤ q * q ^ (2 * n) * q := by rw [← mul_assoc]; gcongr; omega
        _ = (q ^ (n + 1)) ^ 2 := by ring
    exact (Nat.pow_le_pow_iff_left (by norm_num)).1 this
  have hD : pD n b ≤ q ^ 2 := by
    have e := Nat.mul_le_mul_left q h2
    have e2 : q * (4 * n + 2) = 4 * n * q + 2 * q := by ring
    have e3 : q ^ 2 = q * q := pow_two q
    simp only [pD, pL, ← hq]
    omega
  have hb1 : 2 ≤ 1 + b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · simp [hq, pq, h] at h3
    · omega
  have hL : 2 ^ pL n ≤ q := (Nat.pow_le_pow_left hb1 _).trans h1
  have hC' : cC ≤ q * q ^ (2 * n) := hC.trans (Nat.mul_le_mul_right _ hL)
  have hSg' : Sg ≤ 10 * q ^ (4 * n + 3) * R := by
    calc Sg ≤ 2 * pD n b * (2 * (pN n b * R) * (1 + b) ^ pL n + pm n b * (cC * R)) := hSg
      _ ≤ 2 * q ^ 2 * (2 * (q ^ (4 * n) * R) * q + 3 * q ^ (2 * n) * (q * q ^ (2 * n) * R)) := by
          rw [hN]; gcongr
      _ = 10 * q ^ (4 * n + 3) * R := by ring
  rw [hN] at hs ⊢
  have hs' : s * pA n b ≤ q ^ (5 * n + 4) * R :=
    hs.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by positivity) (by omega)))
  calc 5 * (2 * pencilOrder (pm n b) * Sg) + 8 * (s * pA n b)
      ≤ 5 * (q ^ (n + 1) * (10 * q ^ (4 * n + 3) * R)) + 8 * (q ^ (5 * n + 4) * R) :=
        Nat.add_le_add (by gcongr) (Nat.mul_le_mul_left _ hs')
    _ = 58 * q ^ (5 * n + 4) * R := by ring
    _ ≤ q * q ^ (5 * n + 4) * R := by gcongr; omega
    _ = q ^ (n + 5) * (q ^ (4 * n) * R) := by ring

end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.ParamsQ =====

-- ===== begin KP.ShiftCount =====
section
/-! # The exceptional-row count for shift rows

Rows carry shifts `β r ∈ F^m` with `σ r j = chi (β r j)`, every shift used by at most `N` rows
(for label × shift rows: exactly the `N` labels). `shift_count`: for a window `[u, u + D]` that
contains `(m/2 - t, m/2 + t)`, with `m · log(4m³) ≤ t²`, at most `N · ⌊2^m / (2m³)⌋` rows are
outside the window at any pattern. This is the `hcount` of `horner_template`. -/

namespace OAI.Computability.NearSquareRoot.KernelPass
open Matrix Finset Real

variable {W m : ℕ}

lemma xs_sgZ (a c : ZMod 2) : (1 - chi a * chi c) / 2 = 1 ↔ a + c = 1 := by
  rcases z2_cases a with rfl | rfl <;> rcases z2_cases c with rfl | rfl <;>
    simp only [chi, ↓reduceIte, one_ne_zero, zero_ne_one, mul_one, mul_neg, neg_neg, sub_self,
      sub_neg_eq_add, add_self_div_two, zero_div, zero_add, add_zero, add_eq_left] <;>
    first | norm_num | decide

theorem cnt_eq_hamming (b κ : Fin m → ZMod 2) :
    cnt (xs (fun j => chi (b j)) fun j => chi (κ j)) = hamming (b + κ) := by
  unfold cnt hamming
  congr 1
  refine Finset.filter_congr fun j _ => ?_
  exact xs_sgZ (b j) (κ j)

theorem shift_count (β : Fin W → Fin m → ZMod 2) (N u D : ℕ)
    (hfib : ∀ γ, (Finset.univ.filter fun r => β r = γ).card ≤ N)
    (hm : 0 < m) (t : ℝ) (ht0 : 0 ≤ t) (htm : t ≤ m) (ht : m * log (4 * m ^ 3) ≤ t ^ 2)
    (hu1 : (u : ℝ) ≤ m / 2 - t + 1) (hu2 : (m : ℝ) / 2 + t ≤ u + D + 1) (κ : Fin m → ZMod 2) :
    (Finset.univ.filter fun r => ¬ InWin (fun r j => chi (β r j)) u D κ r).card ≤
      N * ⌊(2 : ℝ) ^ m / (2 * m ^ 3)⌋₊ := by
  classical
  let Q : (Fin m → ZMod 2) → Prop := fun δ => ¬ (u ≤ hamming δ ∧ hamming δ ≤ u + D)
  let E := Finset.univ.filter fun r => ¬ InWin (fun r j => chi (β r j)) u D κ r
  have hE : ∀ r, r ∈ E ↔ Q (β r + κ) := by
    intro r
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and, InWin, Q, cnt_eq_hamming]
  -- fibers
  have h1 : E.card ≤ N * (E.image β).card := by
    refine Finset.card_le_mul_card_image E N fun γ _ => ?_
    exact le_trans (Finset.card_le_card fun r hr => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢; exact hr.2) (hfib γ)
  -- translate by κ
  have h2 : (E.image β).card ≤ (Finset.univ.filter Q).card := by
    refine Finset.card_le_card_of_injOn (fun γ => γ + κ) ?_ ?_
    · intro γ hγ
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hγ)
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      exact (hE r).mp hr
    · intro γ _ γ' _ hh
      exact add_right_cancel hh
  -- outside the window means far from the mean
  have h3 : (Finset.univ.filter Q).card ≤
      (Finset.univ.filter fun x : Fin m → ZMod 2 => t ≤ |(hamming x : ℝ) - m / 2|).card := by
    refine Finset.card_le_card fun δ hδ => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Q, not_and_or, not_le] at hδ ⊢
    rcases hδ with hlt | hgt
    · have : (hamming δ : ℝ) + 1 ≤ u := by exact_mod_cast hlt
      rw [le_abs]; right; linarith only [this, hu1]
    · have : (u : ℝ) + D + 1 ≤ hamming δ := by exact_mod_cast hgt
      rw [le_abs]; left; linarith only [this, hu2]
  have h4 : (Finset.univ.filter Q).card ≤ ⌊(2 : ℝ) ^ m / (2 * m ^ 3)⌋₊ := by
    apply Nat.le_floor
    refine le_trans ?_ (window_fraction m hm t ht0 htm ht)
    exact_mod_cast h3
  calc E.card ≤ N * (E.image β).card := h1
    _ ≤ N * ⌊(2 : ℝ) ^ m / (2 * m ^ 3)⌋₊ := Nat.mul_le_mul_left N (h2.trans h4)

end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.ShiftCount =====

-- ===== begin KP.Assembly =====
section
/-! # Assembly: a correct template from routed rectangles

`template_of_routing`: for `M ≥ 2048` odd queries, `u` auxiliary pairs and `N` labels, any
charged/free rectangle families on the labels that factor a kernel `Hl` whose diagonal blocks are
the queries, with rectangle weights summing to the identity, give a `QCorrect` template on
`N · 2^M` rows (all shifts) of arity `2(M+u)`. Its calls are
`5·(2p·Sg) + 8·(s·2(M+u))` with `p = pencilOrder M`, `s = N·⌊2^M/(2M³)⌋` and stage calls
`Sg ≤ d·(2·N·2^M·inc + M·|C|·2^M)`.

This file only composes: `shift_stage_spec`, `shift_calls` (routing on label × shift rows),
`horner_template` (predictor and repair), `shift_count`, `window_params` (window),
`qtot_spat` (product identity). -/

namespace OAI.Computability.NearSquareRoot.KernelPass
open Matrix Finset

/-- All shifts: `Fin (2^M) ≃ (Fin M → ZMod 2)`. -/
noncomputable def shiftEquiv (M : ℕ) : Fin (2 ^ M) ≃ (Fin M → ZMod 2) :=
  (Fintype.equivFinOfCardEq (by simp [ZMod.card])).symm

theorem template_of_routing {M u N : ℕ} (hM : 2048 ≤ M) (hodd : Odd M)
    {C F : Type} [Fintype C] [Fintype F]
    (ch : C → QCharged (2 * (M + u)) N (Fin M)) (fr : F → QFree (2 * (M + u)) N (Fin M))
    (Hl : ∀ h : ℕ, Fin M → Fin N → Fin N → Matrix (Addr (2 * (M + u)) h) (Addr (2 * (M + u)) h) ℚ)
    (hch : ∀ h c j t s, t ∈ (ch c).T → s ∈ (ch c).S →
      qBlk h ((ch c).out j t) * qBlk h ((ch c).com j) * qBlk h ((ch c).inp j s) = Hl h j t s)
    (hfr : ∀ h f j t s, t ∈ (fr f).T → s ∈ (fr f).S →
      qBlk h ((fr f).tgt t) * qBlk h ((fr f).mid j t s) * qBlk h ((fr f).src s) = Hl h j t s)
    (hId : ∀ t s, (∑ c, if t ∈ (ch c).T ∧ s ∈ (ch c).S then (ch c).w else 0) +
      (∑ f, if t ∈ (fr f).T ∧ s ∈ (fr f).S then (fr f).w else 0) = if s = t then 1 else 0)
    (hself : ∀ h j l, Hl h j l l = Wh (2 * (M + u)) h *
      diagonal (fun v => chi (spat (testQ (M := M) (u := u)) v j)) * Wh (2 * (M + u)) h)
    (d inc : ℕ)
    (hci : ∀ c j s, ((ch c).inp j s).calls = 0) (hco : ∀ c j t, ((ch c).out j t).calls = 0)
    (hcc : ∀ c j, ((ch c).com j).calls ≤ d)
    (hfm : ∀ f j t s, ((fr f).mid j t s).calls = 0)
    (hfs : ∀ f s, ((fr f).src s).calls ≤ d) (hft : ∀ f t, ((fr f).tgt t).calls ≤ d)
    (hincS : ∀ s, (Finset.univ.filter fun f => s ∈ (fr f).S).card ≤ inc)
    (hincT : ∀ t, (Finset.univ.filter fun f => t ∈ (fr f).T).card ≤ inc) :
    ∃ (t : QPlan (2 * (M + u)) (N * 2 ^ M) (N * 2 ^ M)) (Sg : ℕ), QCorrect t ∧
      t.calls = 5 * (2 * pencilOrder M * Sg) +
        8 * (N * ⌊(2 : ℝ) ^ M / (2 * (M : ℝ) ^ 3)⌋₊ * (2 * (M + u))) ∧
      Sg ≤ d * (2 * (N * 2 ^ M) * inc + M * (Fintype.card C * 2 ^ M)) := by
  obtain ⟨ht0, htm, ht, hu1, hu2⟩ := window_params M hM
  let β : Fin (N * 2 ^ M) → Fin M → ZMod 2 := fun r => shiftEquiv M (shf r)
  let σ : Fin (N * 2 ^ M) → Fin M → ℚ := fun r j => chi (β r j)
  let Sg := routed (fun p : C × Fin (2 ^ M) => liftCh (ch p.1) p.2)
    (fun p : F × Fin (2 ^ M) => liftFr (fr p.1) p.2) σ
  have hSg : ∀ h, Sg.eval h = specR fun v : Addr (2 * (M + u)) h =>
      diagonal fun r => ∑ j, σ r j * chi (spat (testQ (M := M) (u := u)) v j) := fun h =>
    shift_stage_spec h ch fr σ (Hl h) (fun v j => chi (spat (testQ (M := M) (u := u)) v j))
      (hch h) (hfr h) hId (hself h)
  have hz : ∀ h (v : Addr (2 * (M + u)) h),
      (∏ c, qtot (v c)) = zOfH (spat (testQ (M := M) (u := u)) v) := fun h v => qtot_spat hodd h v
  have hfib : ∀ γ, (Finset.univ.filter fun r => β r = γ).card ≤ N := by
    intro γ
    have : (Finset.univ.filter fun r => β r = γ).card ≤ (Finset.univ : Finset (Fin N)).card := by
      refine Finset.card_le_card_of_injOn lab (fun _ _ => Finset.mem_univ _) ?_
      intro r hr r' hr' hl
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hr hr'
      have hs : shf r' = shf r := (shiftEquiv M).injective (hr'.trans hr.symm)
      exact (lab_shf_ext hl.symm hs).symm
    simpa only [ge_iff_le, card_univ, Fintype.card_fin] using this
  have hcount := shift_count β N (M / 2 - pencilOrder M) (2 * pencilOrder M) hfib (by omega)
    (pencilOrder M) ht0 htm ht hu1 (by exact_mod_cast hu2)
  obtain ⟨t, ht1, ht2⟩ := horner_template (testQ (M := M) (u := u)) σ (M / 2 - pencilOrder M)
    (2 * pencilOrder M) (N * ⌊(2 : ℝ) ^ M / (2 * (M : ℝ) ^ 3)⌋₊) Sg (fun r j => chi_pm _) hSg hz hcount
  refine ⟨t, Sg.calls, ht1, ht2, ?_⟩
  have := shift_calls (R := 2 ^ M) ch fr σ d inc hci hco hcc hfm hfs hft hincS hincT
  simpa only [ge_iff_le, Fintype.card_fin] using this

end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.Assembly =====

-- ===== begin KP.AssemblyRate =====
section
/-! # Assembly: parameters of the query count

`pm_large`, `pm_odd`: the query count `pm n b` is large and odd. -/

namespace OAI.Computability.NearSquareRoot.KernelPass
open Matrix Finset

lemma pm_large (n b : ℕ) (hn : 1 ≤ n) (hq : 80 ≤ pq b) : 2048 ≤ pm n b := by
  have h1 : pq b ^ 2 ≤ pq b ^ (2 * n) := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : 80 ^ 2 ≤ pq b ^ 2 := Nat.pow_le_pow_left hq 2
  simp only [pm]; omega

lemma pm_odd (n b : ℕ) : Odd (pm n b) := ⟨pq b ^ (2 * n), rfl⟩

end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.AssemblyRate =====

-- ===== begin KP.HammingWeights =====
section
/-! # Weights of the charged rectangles on Hamming labels (pair level)

Labels are words `Fin L → α`. A charged rectangle is a set `S` of positions with a prescribed
letter at each (`ρ : S → α`); it contains the pair `(u, v)` when both words carry `ρ` on `S`.
With weight `a |S|` on rectangles of at most `t` positions, the total weight through `(u, v)`
depends only on the number `k` of agreeing positions: it is `Σ_j C(k, j) · a_j` (`charged_sum`).
If that function is `1` at `k = L` and `0` whenever `L - k` is positive and even, and the unique
free rectangle of a pair at odd distance carries minus the charged weight, the weights sum to
the identity matrix on labels (`weight_identity`).

The counting idea (rectangles through a pair ↔ `j`-subsets of the agreement set) follows
OpenAI's `PrimeRectangleCharged`; statements and proofs are written for this tree. -/

namespace OAI.Computability.NearSquareRoot.KernelPass
open Finset

variable {α : Type*} [Fintype α] [DecidableEq α] {L : ℕ}

/-- Positions where two words agree. -/
def agree (u v : Fin L → α) : Finset (Fin L) := Finset.univ.filter fun i => u i = v i

/-- Charged rectangles: a set of positions and a letter at each. -/
abbrev ChRect (α : Type*) (L : ℕ) := (S : Finset (Fin L)) × (S → α)

/-- Both words carry the recorded letters. -/
def ChRect.has (R : ChRect α L) (u v : Fin L → α) : Prop := ∀ i : R.1, u i = R.2 i ∧ v i = R.2 i

instance (R : ChRect α L) (u v : Fin L → α) : Decidable (R.has u v) := by
  unfold ChRect.has; infer_instance

theorem sum_has (S : Finset (Fin L)) (u v : Fin L → α) :
    (∑ ρ : S → α, if ChRect.has ⟨S, ρ⟩ u v then (1 : ℚ) else 0) = if S ⊆ agree u v then 1 else 0 := by
  by_cases hS : S ⊆ agree u v
  · rw [if_pos hS, Finset.sum_eq_single (fun i : S => u i)]
    · rw [if_pos]
      intro i
      have := hS i.2
      simp only [agree, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact ⟨rfl, this.symm⟩
    · intro ρ _ hρ
      rw [if_neg]
      intro hh
      exact hρ (funext fun i => ((hh i).1).symm)
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg hS]
    refine Finset.sum_eq_zero fun ρ _ => ?_
    rw [if_neg]
    intro hh
    apply hS
    intro i hi
    have := hh ⟨i, hi⟩
    simp only [agree, Finset.mem_filter, Finset.mem_univ, true_and]
    exact this.1.trans this.2.symm

/-- Total charged weight through a pair: a function of the number of agreements only. -/
theorem charged_sum (g : ℕ → ℚ) (u v : Fin L → α) :
    (∑ R : ChRect α L, if R.has u v then g R.1.card else 0) =
      ∑ j ∈ Finset.range ((agree u v).card + 1), ((agree u v).card.choose j : ℚ) * g j := by
  rw [Fintype.sum_sigma]
  have e : ∀ S : Finset (Fin L), (∑ ρ : S → α, if ChRect.has ⟨S, ρ⟩ u v then g S.card else 0) =
      if S ⊆ agree u v then g S.card else 0 := by
    intro S
    have := sum_has S u v
    calc (∑ ρ : S → α, if ChRect.has ⟨S, ρ⟩ u v then g S.card else 0)
        = (∑ ρ : S → α, if ChRect.has ⟨S, ρ⟩ u v then (1 : ℚ) else 0) * g S.card := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun ρ _ => by split_ifs <;> simp
      _ = _ := by rw [this]; split_ifs <;> simp
  simp only [e]
  rw [← Finset.sum_filter]
  have hf : (Finset.univ.filter fun S : Finset (Fin L) => S ⊆ agree u v) = (agree u v).powerset := by
    ext S; simp
  rw [hf, Finset.sum_powerset_apply_card (fun j => g j)]
  exact Finset.sum_congr rfl fun j _ => by rw [nsmul_eq_mul]

/-- **Weight identity (pair level).** `P k` is the charged weight at `k` agreements. If `P L = 1`
and `P k = 0` at every positive even distance `L - k`, then charged weights plus the free weight
`-P k` at odd distances give the identity matrix on labels. -/
theorem weight_identity (g P : ℕ → ℚ)
    (hP : ∀ k ≤ L, (∑ j ∈ Finset.range (k + 1), (k.choose j : ℚ) * g j) = P k)
    (h1 : P L = 1) (h0 : ∀ k < L, Even (L - k) → P k = 0) (u v : Fin L → α) :
    (∑ R : ChRect α L, if R.has u v then g R.1.card else 0) +
      (if Odd (L - (agree u v).card) then -P (agree u v).card else 0) = if u = v then 1 else 0 := by
  have hk : (agree u v).card ≤ L := by
    simpa using Finset.card_le_univ (agree u v)
  rw [charged_sum, hP _ hk]
  by_cases huv : u = v
  · subst huv
    have : (agree u u).card = L := by simp [agree]
    rw [this, h1]; simp
  · have hlt : (agree u v).card < L := by
      refine lt_of_le_of_ne hk fun hc => huv ?_
      have hall : agree u v = Finset.univ := by
        apply Finset.eq_univ_of_card; simpa using hc
      funext i
      have := Finset.mem_univ i
      rw [← hall] at this
      simpa [agree] using this
    rw [if_neg huv]
    by_cases ho : Odd (L - (agree u v).card)
    · rw [if_pos ho]; ring
    · rw [if_neg ho, h0 _ hlt (Nat.not_odd_iff_even.mp ho)]; simp

end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.HammingWeights =====

-- ===== begin KP.ChCount =====
section
/-! # Number of charged rectangles on at most `t` positions: at most `2^L · q^t`. -/

namespace OAI.Computability.NearSquareRoot.KernelPass
open Finset

variable {α : Type*} [Fintype α] [DecidableEq α] {L : ℕ}

theorem card_chRect_le (t : ℕ) (hq : 0 < Fintype.card α) :
    (Finset.univ.filter fun R : ChRect α L => R.1.card ≤ t).card ≤ 2 ^ L * Fintype.card α ^ t := by
  rw [Finset.card_filter, Fintype.sum_sigma]
  calc (∑ S : Finset (Fin L), ∑ _ρ : S → α, if S.card ≤ t then 1 else 0)
      ≤ ∑ _S : Finset (Fin L), Fintype.card α ^ t := Finset.sum_le_sum fun S _ => by
        by_cases h : S.card ≤ t
        · simp only [if_pos h, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
            Fintype.card_pi, Finset.prod_const, Fintype.card_coe]
          exact Nat.pow_le_pow_right hq h
        · simp only [if_neg h, Finset.sum_const_zero]; exact Nat.zero_le _
    _ = 2 ^ L * Fintype.card α ^ t := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin, smul_eq_mul]

end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.ChCount =====

-- ===== begin KP.CutRect =====
section
/-! # Free cut rectangles on bit-letter labels

Letters are `b`-bit strings, labels are words of `L` letters. A cut rectangle records, at each
position, either the whole common letter (`none`) or a cut bit `c`: the common prefix below `c`
and the source bit at `c` (the target has the opposite bit there). The record is stored as a
truncated letter, so a rectangle is a pair `(cut pattern, records)`.

* `cut_sum`: every ordered pair `(u, v)` lies in exactly one cut rectangle, and its number of
  cut positions is the Hamming distance (stated as a sum over all rectangles).
* `card_src`, `card_tgt`: every label lies in exactly `(b+1)^L` source sides and target sides.
* `label_identity`: charged weights plus the weight `-P (L - cuts)` on cut rectangles with an
  odd number of cuts sum to the identity matrix on labels (from `weight_identity`).

The first-disagreement idea follows OpenAI's `PrimeBitLetter` / `PrimeBitRectangles`;
definitions, statements and proofs are written for this tree. -/

namespace OAI.Computability.NearSquareRoot.KernelPass
open Finset

abbrev Letter (b : ℕ) := Fin b → Bool

variable {b L : ℕ}

/-- The source record of a letter at a cut. -/
def trunc : Option (Fin b) → Letter b → Letter b
  | none, a => a
  | some c, a => fun k => if k ≤ c then a k else false

/-- The target record of a letter at a cut: the bit at the cut is flipped. -/
def truncF : Option (Fin b) → Letter b → Letter b
  | none, a => a
  | some c, a => fun k => if k < c then a k else if k = c then !a k else false

theorem match_some (c : Fin b) (a a' : Letter b) :
    trunc (some c) a = truncF (some c) a' ↔ (∀ k, k < c → a k = a' k) ∧ a c = !a' c := by
  constructor
  · intro h
    refine ⟨fun k hk => ?_, ?_⟩
    · have := congrFun h k
      simpa [trunc, truncF, hk, hk.le] using this
    · have := congrFun h c
      simpa [trunc, truncF] using this
  · rintro ⟨h1, h2⟩
    funext k
    simp only [trunc, truncF]
    rcases lt_trichotomy k c with hk | hk | hk
    · simp [hk, hk.le, h1 k hk]
    · subst hk; simp [h2]
    · simp [not_le.2 hk, not_lt.2 hk.le, hk.ne']

/-- Two letters match at one cut at most. -/
theorem match_unique (a a' : Letter b) (c c' : Option (Fin b))
    (h : trunc c a = truncF c a') (h' : trunc c' a = truncF c' a') : c = c' := by
  cases c with
  | none =>
    cases c' with
    | none => rfl
    | some d =>
      have e : a = a' := h
      have := ((match_some d a a').mp h').2
      rw [e] at this; cases hh : a' d <;> simp [hh] at this
  | some d =>
    cases c' with
    | none =>
      have e : a = a' := h'
      have := ((match_some d a a').mp h).2
      rw [e] at this; cases hh : a' d <;> simp [hh] at this
    | some d' =>
      obtain ⟨p1, q1⟩ := (match_some d a a').mp h
      obtain ⟨p2, q2⟩ := (match_some d' a a').mp h'
      rcases lt_trichotomy d d' with hd | hd | hd
      · have := p2 d hd; rw [q1] at this; cases hh : a' d <;> simp [hh] at this
      · rw [hd]
      · have := p1 d' hd; rw [q2] at this; cases hh : a' d' <;> simp [hh] at this

/-- Two letters match at some cut: nowhere if equal, else at the first differing bit. -/
theorem match_exists (a a' : Letter b) : ∃ c : Option (Fin b), trunc c a = truncF c a' := by
  by_cases e : a = a'
  · exact ⟨none, e⟩
  · have hex : ∃ n : ℕ, ∃ hn : n < b, a ⟨n, hn⟩ ≠ a' ⟨n, hn⟩ := by
      by_contra hc
      push_neg at hc
      exact e (funext fun k => hc k.1 k.2)
    classical
    obtain ⟨hn, hne⟩ := Nat.find_spec hex
    refine ⟨some ⟨Nat.find hex, hn⟩, (match_some _ a a').mpr ⟨fun k hk => ?_, ?_⟩⟩
    · by_contra hk'
      exact Nat.find_min hex (show k.1 < Nat.find hex from hk) ⟨k.2, hk'⟩
    · exact Bool.eq_not_of_ne hne

/-- The cut at which two letters match. -/
noncomputable def cutOf (a a' : Letter b) : Option (Fin b) := Classical.choose (match_exists a a')

theorem cutOf_spec (a a' : Letter b) : trunc (cutOf a a') a = truncF (cutOf a a') a' :=
  Classical.choose_spec (match_exists a a')

theorem cutOf_eq_none (a a' : Letter b) : cutOf a a' = none ↔ a = a' := by
  constructor
  · intro h; have := cutOf_spec a a'; rw [h] at this; exact this
  · intro h; exact match_unique a a' _ _ (cutOf_spec a a') h

/-- A cut rectangle: the cut pattern and the record at each position. -/
abbrev CutRect (L b : ℕ) := (Fin L → Option (Fin b)) × (Fin L → Letter b)

namespace CutRect

/-- The source side. -/
def src (R : CutRect L b) (u : Fin L → Letter b) : Prop := ∀ i, R.2 i = trunc (R.1 i) (u i)
/-- The target side. -/
def tgt (R : CutRect L b) (v : Fin L → Letter b) : Prop := ∀ i, R.2 i = truncF (R.1 i) (v i)
/-- The number of cut positions. -/
def cuts (R : CutRect L b) : ℕ := (Finset.univ.filter fun i => R.1 i ≠ none).card

instance (R : CutRect L b) (u : Fin L → Letter b) : Decidable (R.src u) := by
  unfold src; infer_instance
instance (R : CutRect L b) (v : Fin L → Letter b) : Decidable (R.tgt v) := by
  unfold tgt; infer_instance

end CutRect

/-- Hamming distance of two labels. -/
def hdist (u v : Fin L → Letter b) : ℕ := (Finset.univ.filter fun i => u i ≠ v i).card

theorem agree_add_hdist (u v : Fin L → Letter b) : (agree u v).card + hdist u v = L := by
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin L)))
    (fun i => u i = v i)
  simpa [agree, hdist] using this

/-- The rectangle of an ordered pair. -/
noncomputable def rectOf (u v : Fin L → Letter b) : CutRect L b :=
  (fun i => cutOf (u i) (v i), fun i => trunc (cutOf (u i) (v i)) (u i))

theorem rectOf_cuts (u v : Fin L → Letter b) : (rectOf u v).cuts = hdist u v := by
  unfold CutRect.cuts hdist rectOf
  congr 1; ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, cutOf_eq_none]

theorem mem_iff_rectOf (R : CutRect L b) (u v : Fin L → Letter b) :
    R.src u ∧ R.tgt v ↔ R = rectOf u v := by
  constructor
  · rintro ⟨hs, ht⟩
    have hc : R.1 = fun i => cutOf (u i) (v i) := funext fun i =>
      match_unique (u i) (v i) _ _ ((hs i).symm.trans (ht i)) (cutOf_spec (u i) (v i))
    refine Prod.ext hc (funext fun i => ?_)
    rw [hs i, hc]; rfl
  · rintro rfl
    exact ⟨fun i => rfl, fun i => cutOf_spec (u i) (v i)⟩

/-- **Every ordered pair lies in exactly one cut rectangle, with `hdist` cuts.** -/
theorem cut_sum (f : ℕ → ℚ) (u v : Fin L → Letter b) :
    (∑ R : CutRect L b, if R.src u ∧ R.tgt v then f R.cuts else 0) = f (hdist u v) := by
  rw [Finset.sum_eq_single (rectOf u v)]
  · rw [if_pos ((mem_iff_rectOf _ u v).mpr rfl), rectOf_cuts]
  · intro R _ hR
    rw [if_neg fun h => hR ((mem_iff_rectOf R u v).mp h)]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Every label lies in the source side of exactly `(b+1)^L` cut rectangles. -/
theorem card_src (u : Fin L → Letter b) :
    (Finset.univ.filter fun R : CutRect L b => R.src u).card = (b + 1) ^ L := by
  have : (Finset.univ.filter fun R : CutRect L b => R.src u) =
      (Finset.univ : Finset (Fin L → Option (Fin b))).image
        (fun c => ((c, fun i => trunc (c i) (u i)) : CutRect L b)) := by
    ext R
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h; exact ⟨R.1, Prod.ext rfl (funext fun i => (h i).symm)⟩
    · rintro ⟨c, rfl⟩; exact fun i => rfl
  rw [this, Finset.card_image_of_injective _ (fun c c' h => (Prod.ext_iff.mp h).1)]
  simp [Fintype.card_pi, Fintype.card_option]

/-- Every label lies in the target side of exactly `(b+1)^L` cut rectangles. -/
theorem card_tgt (v : Fin L → Letter b) :
    (Finset.univ.filter fun R : CutRect L b => R.tgt v).card = (b + 1) ^ L := by
  have : (Finset.univ.filter fun R : CutRect L b => R.tgt v) =
      (Finset.univ : Finset (Fin L → Option (Fin b))).image
        (fun c => ((c, fun i => truncF (c i) (v i)) : CutRect L b)) := by
    ext R
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h; exact ⟨R.1, Prod.ext rfl (funext fun i => (h i).symm)⟩
    · rintro ⟨c, rfl⟩; exact fun i => rfl
  rw [this, Finset.card_image_of_injective _ (fun c c' h => (Prod.ext_iff.mp h).1)]
  simp [Fintype.card_pi, Fintype.card_option]

/-- **Weight identity on labels.** Charged rectangles with weight `g |S|`, and cut rectangles
with an odd number `c` of cuts with weight `-P (L - c)`, sum to the identity matrix. Cut
rectangles with an even number of cuts are not used. -/
theorem label_identity (g P : ℕ → ℚ)
    (hP : ∀ k ≤ L, (∑ j ∈ Finset.range (k + 1), (k.choose j : ℚ) * g j) = P k)
    (h1 : P L = 1) (h0 : ∀ k < L, Even (L - k) → P k = 0) (u v : Fin L → Letter b) :
    (∑ R : ChRect (Letter b) L, if R.has u v then g R.1.card else 0) +
      (∑ R : CutRect L b, if R.src u ∧ R.tgt v then
        (if Odd R.cuts then -P (L - R.cuts) else 0) else 0) = if u = v then 1 else 0 := by
  rw [cut_sum (fun c => if Odd c then -P (L - c) else 0) u v]
  have hd := agree_add_hdist u v
  have e1 : L - hdist u v = (agree u v).card := by omega
  have e2 : hdist u v = L - (agree u v).card := by omega
  rw [e1, e2]
  exact weight_identity g P hP h1 h0 u v

end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.CutRect =====

-- ===== begin KP.Interp =====
section
/-! # Interpolation coefficients for the charged rectangles (rational)

For `L = 2t` the charged weights `gch t j` (zero for `j > t`) satisfy
`Σ_j C(k, j) · gch t j = Pch t k` with `Pch t k = ∏_{l<t} (k - 2l) / ∏_{l<t} 2(t - l)`,
so `Pch t (2t) = 1` and `Pch t (2e) = 0` for `e < t`. The proof is by the rule
`(k - c) · C(k, j) = (j+1) · C(k, j+1) + (j - c) · C(k, j)`; no interpolation matrix is
inverted. `label_identity_even` is the resulting weight identity on labels of even length.
Rational coefficients (QPlan). -/

namespace OAI.Computability.NearSquareRoot.KernelPass
open Finset

/-- Coefficients of `k ↦ (k - c) · f k` in the binomial basis, from those of `f`. -/
def mulLin (c : ℚ) (g : ℕ → ℚ) : ℕ → ℚ :=
  fun j => (j - c) * g j + (if j = 0 then 0 else (j : ℚ) * g (j - 1))

lemma choose_mul_succ (k i : ℕ) : (k.choose (i + 1) : ℚ) * (i + 1) = k.choose i * (k - i) := by
  by_cases h : i ≤ k
  · have := Nat.choose_succ_right_eq k i
    have h2 : ((k - i : ℕ) : ℚ) = k - i := Nat.cast_sub h
    rw [← h2]; exact_mod_cast this
  · push_neg at h
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt h]; simp

theorem sum_mulLin (c : ℚ) (g : ℕ → ℚ) (n k : ℕ) (hg : ∀ j, n ≤ j → g j = 0) :
    (∑ j ∈ range (n + 1), (k.choose j : ℚ) * mulLin c g j) =
      (k - c) * ∑ j ∈ range n, (k.choose j : ℚ) * g j := by
  simp only [mulLin, mul_add, sum_add_distrib]
  rw [sum_range_succ (fun j => (k.choose j : ℚ) * ((j - c) * g j)), hg n le_rfl,
    sum_range_succ' (fun j => (k.choose j : ℚ) * (if j = 0 then 0 else (j : ℚ) * g (j - 1)))]
  simp only [mul_zero, add_zero, if_true, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
  rw [mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  have := choose_mul_succ k j
  push_cast
  linear_combination (g j) * this

lemma mulLin_supp (c : ℚ) (g : ℕ → ℚ) (n : ℕ) (hg : ∀ j, n ≤ j → g j = 0) :
    ∀ j, n + 1 ≤ j → mulLin c g j = 0 := by
  intro j hj
  have h1 : g j = 0 := hg j (by omega)
  have h2 : g (j - 1) = 0 := hg (j - 1) (by omega)
  have h3 : j ≠ 0 := by omega
  simp [mulLin, h1, h2, h3]

/-- Binomial-basis coefficients of `k ↦ ∏_{l<i} (k - 2l)`. -/
def Gint : ℕ → ℕ → ℚ
  | 0 => fun j => if j = 0 then 1 else 0
  | i + 1 => mulLin (2 * i) (Gint i)

lemma Gint_supp : ∀ i j, i + 1 ≤ j → Gint i j = 0
  | 0, j, hj => by simp [Gint]; omega
  | i + 1, j, hj => mulLin_supp _ _ (i + 1) (Gint_supp i) j hj

theorem Gint_sum : ∀ i k : ℕ, (∑ j ∈ range (i + 1), (k.choose j : ℚ) * Gint i j) =
    ∏ l ∈ range i, ((k : ℚ) - 2 * l)
  | 0, k => by simp [Gint]
  | i + 1, k => by
    rw [Gint, sum_mulLin _ _ (i + 1) k (Gint_supp i), Gint_sum i k, prod_range_succ]; ring

/-- The normalizing constant `∏_{l<t} 2(t - l)`. -/
def denCh (t : ℕ) : ℚ := ∏ l ∈ range t, (2 * ((t : ℚ) - l))

lemma denCh_ne (t : ℕ) : denCh t ≠ 0 := by
  refine prod_ne_zero_iff.mpr fun l hl => ?_
  have : (l : ℚ) < t := by exact_mod_cast mem_range.mp hl
  intro h; linarith

/-- The charged weight of a rectangle on `j` positions. -/
def gch (t j : ℕ) : ℚ := Gint t j / denCh t
/-- The total charged weight at `k` agreements. -/
def Pch (t k : ℕ) : ℚ := (∏ l ∈ range t, ((k : ℚ) - 2 * l)) / denCh t

lemma gch_supp (t j : ℕ) (hj : t < j) : gch t j = 0 := by
  rw [gch, Gint_supp t j hj, zero_div]

theorem gch_sum (t k : ℕ) : (∑ j ∈ range (k + 1), (k.choose j : ℚ) * gch t j) = Pch t k := by
  have e1 : (∑ j ∈ range (k + 1), (k.choose j : ℚ) * gch t j) =
      ∑ j ∈ range (k + t + 1), (k.choose j : ℚ) * gch t j := by
    refine sum_subset (range_subset_range.mpr (by omega)) fun j _ hj => ?_
    rw [mem_range] at hj
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  have e2 : (∑ j ∈ range (t + 1), (k.choose j : ℚ) * gch t j) =
      ∑ j ∈ range (k + t + 1), (k.choose j : ℚ) * gch t j := by
    refine sum_subset (range_subset_range.mpr (by omega)) fun j _ hj => ?_
    rw [mem_range] at hj
    rw [gch_supp t j (by omega), mul_zero]
  rw [e1, ← e2, Pch, ← Gint_sum t k, div_eq_mul_inv, Finset.sum_mul]
  exact sum_congr rfl fun j _ => by rw [gch, div_eq_mul_inv, mul_assoc]

theorem Pch_top (t : ℕ) : Pch t (2 * t) = 1 := by
  rw [Pch, div_eq_one_iff_eq (denCh_ne t), denCh]
  exact prod_congr rfl fun l _ => by push_cast; ring

theorem Pch_even (t e : ℕ) (he : e < t) : Pch t (2 * e) = 0 := by
  rw [Pch, prod_eq_zero (mem_range.mpr he) (by push_cast; ring), zero_div]

end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.Interp =====

-- ===== begin KP.CutRectEven =====
section
/-! # The label weight identity at even length, with the explicit rational weights

`label_identity` instantiated with the charged weights `gch t` and totals `Pch t` of
chunk KP.Interp: no hypothesis is left. This is the `hId` input of the routing stage for
Hamming labels of length `L = 2t`. -/

namespace OAI.Computability.NearSquareRoot.KernelPass
open Finset

variable {b : ℕ}

theorem label_identity_even (t : ℕ) (u v : Fin (2 * t) → Letter b) :
    (∑ R : ChRect (Letter b) (2 * t), if R.has u v then gch t R.1.card else 0) +
      (∑ R : CutRect (2 * t) b, if R.src u ∧ R.tgt v then
        (if Odd R.cuts then -Pch t (2 * t - R.cuts) else 0) else 0) = if u = v then 1 else 0 := by
  refine label_identity (gch t) (Pch t) (fun k _ => gch_sum t k) (Pch_top t) (fun k hk hev => ?_) u v
  obtain ⟨r, hr⟩ := hev
  have he : k = 2 * (t - r) := by omega
  rw [he]
  exact Pch_even t (t - r) (by omega)

end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.CutRectEven =====

-- ===== begin KP.LabelVec =====
section
/-! # Routing vectors of labels, and the free hypotheses for odd-cut rectangles

Auxiliary coordinates are indexed by `Option (Fin L × Letter b)` through an equivalence `e`
with `Fin u`: one spare coordinate (`none`, always 0) and one coordinate per (position,
letter). The routing vector `dLab e v` has the constant `1` at coordinate 0 and `[v i = l]`
at `(i, l)`. For a cut rectangle with an odd number of cuts and `L` even, the set `SpLab`,
the vector `nLab` and a pivot satisfy the hypotheses of the free factorization
(`free_geom`): `src_cond`, `tgt_zero`, `tgt_one`, `exists_pivot`. -/

namespace OAI.Computability.NearSquareRoot.KernelPass
open Finset
open Free

variable {L b u : ℕ} (e : Option (Fin L × Letter b) ≃ Fin u)

/-- Auxiliary coordinates of a label, on the option index. -/
def gLabO (v : Fin L → Letter b) : Option (Fin L × Letter b) → ZMod 2
  | none => 0
  | some (i, l) => if v i = l then 1 else 0

/-- Auxiliary coordinates of a label. -/
def gLab (v : Fin L → Letter b) : Aux u := fun a => gLabO v (e.symm a)

/-- The routing vector of a label. -/
def dLab (v : Fin L → Letter b) : V u := Fin.cons 1 (gLab e v)

lemma dLab_zero (v : Fin L → Letter b) : dLab e v 0 = 1 := rfl

lemma gOf_dLab (v : Fin L → Letter b) : gOf (dLab e v) = gLab e v := by
  funext a; simp [gOf, dLab]

lemma sum_aux (f : Option (Fin L × Letter b) → ZMod 2) :
    (∑ a : Fin u, f (e.symm a)) = ∑ i : Fin L, ∑ l : Letter b, f (some (i, l)) + f none := by
  rw [Equiv.sum_comp e.symm f, Fintype.sum_option, Fintype.sum_prod_type, add_comm]

lemma auxDot_gLab_self (hL : Even L) (v : Fin L → Letter b) :
    auxDot (gLab e v) (gLab e v) = 0 := by
  unfold auxDot gLab
  rw [sum_aux e (fun o => gLabO v o * gLabO v o)]
  simp only [gLabO, mul_zero, add_zero, ite_mul, one_mul, zero_mul]
  have : ∀ i : Fin L, (∑ l : Letter b, if v i = l then (if v i = l then (1 : ZMod 2) else 0) else 0) = 1 := by
    intro i
    rw [Finset.sum_eq_single (v i)]
    · simp
    · intro l _ hl; rw [if_neg (Ne.symm hl)]
    · simp
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  exact (ZMod.natCast_eq_zero_iff_even).mpr hL

lemma dotV_dLab_self (hL : Even L) (v : Fin L → Letter b) : dotV (dLab e v) (dLab e v) = 1 := by
  have h := auxDot_gLab_self e hL v
  unfold auxDot at h
  simp only [dotV, dotProduct, Fin.sum_univ_succ, dLab, Fin.cons_zero, Fin.cons_succ, mul_one, h,
    add_zero]

/-! ## A cut rectangle -/

variable (R : CutRect L b)

/-- Letters allowed for the targets of `R`, on the option index. -/
def allowO : Option (Fin L × Letter b) → Prop
  | none => False
  | some (i, l) => truncF (R.1 i) l = R.2 i

/-- The common letter at uncut positions, on the option index. -/
def nO : Option (Fin L × Letter b) → ZMod 2
  | none => 0
  | some (i, l) => if R.1 i = none ∧ l = R.2 i then 1 else 0

open Classical in
/-- The summation coordinates of `R`. -/
noncomputable def SpLab : Finset (Fin u) := Finset.univ.filter fun a => allowO R (e.symm a)

/-- The vector `n'` of `R`. -/
def nLab : Aux u := fun a => nO R (e.symm a)

lemma src_O {v : Fin L → Letter b} (hs : R.src v) :
    ∀ o, allowO R o → gLabO v o = nO R o := by
  intro o ho
  match o, ho with
  | some (i, l), ho =>
    have hsi := hs i
    simp only [allowO] at ho
    simp only [gLabO, nO]
    cases hc : R.1 i with
    | none =>
      rw [hc] at hsi ho
      have h1 : v i = R.2 i := hsi.symm
      have h2 : l = R.2 i := ho
      simp [h1, h2]
    | some c =>
      rw [hc] at hsi ho
      have hm := (match_some c (v i) l).mp (hsi.symm.trans ho.symm)
      have hne : v i ≠ l := by
        intro h; have := hm.2; rw [h] at this; cases hl : l c <;> simp [hl] at this
      simp [hne]

lemma src_cond {v : Fin L → Letter b} (hs : R.src v) :
    ∀ a ∈ SpLab e R, gLab e v a = nLab e R a := by
  intro a ha
  have : allowO R (e.symm a) := by simpa [SpLab] using ha
  exact src_O R hs _ this

lemma tgt_O {w : Fin L → Letter b} (ht : R.tgt w) :
    ∀ o, ¬ allowO R o → gLabO w o = 0 := by
  intro o ho
  match o, ho with
  | none, _ => rfl
  | some (i, l), ho =>
    simp only [allowO] at ho
    simp only [gLabO]
    rw [if_neg]
    intro h
    exact ho (by rw [← h]; exact (ht i).symm)

lemma tgt_zero {w : Fin L → Letter b} (ht : R.tgt w) :
    ∀ a, a ∉ SpLab e R → gLab e w a = 0 := by
  intro a ha
  have : ¬ allowO R (e.symm a) := by simpa [SpLab] using ha
  exact tgt_O R ht _ this

lemma uncut_add_cuts : (Finset.univ.filter fun i => R.1 i = none).card + R.cuts = L := by
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin L)))
    (fun i => R.1 i = none)
  simpa [CutRect.cuts] using this

lemma tgt_one {w : Fin L → Letter b} (ht : R.tgt w) (hodd : Odd R.cuts) (hL : Even L) :
    auxDot (nLab e R) (gLab e w) = 1 := by
  unfold auxDot nLab gLab
  rw [sum_aux e (fun o => nO R o * gLabO w o)]
  simp only [nO, gLabO, zero_mul, add_zero]
  have hin : ∀ i : Fin L, (∑ l : Letter b, (if R.1 i = none ∧ l = R.2 i then (1 : ZMod 2) else 0) *
      (if w i = l then 1 else 0)) = if R.1 i = none then 1 else 0 := by
    intro i
    by_cases hc : R.1 i = none
    · have hw : R.2 i = w i := by have := ht i; rw [hc] at this; exact this
      rw [if_pos hc, Finset.sum_eq_single (R.2 i)]
      · simp [hc, hw]
      · intro l _ hl; simp [hl]
      · simp
    · simp [hc]
  simp only [hin]
  rw [Finset.sum_boole]
  have h := uncut_add_cuts R
  have hoddU : Odd (Finset.univ.filter fun i => R.1 i = none).card := by
    rcases hodd with ⟨r, hr⟩; rcases hL with ⟨s, hs⟩
    exact ⟨s - r - 1, by omega⟩
  exact (ZMod.natCast_eq_one_iff_odd).mpr hoddU

lemma exists_pivot (hodd : Odd R.cuts) (hL : Even L) :
    ∃ i0, i0 ∈ SpLab e R ∧ nLab e R i0 = 1 := by
  have h := uncut_add_cuts R
  have hpos : 0 < (Finset.univ.filter fun i => R.1 i = none).card := by
    rcases hodd with ⟨r, hr⟩; rcases hL with ⟨s, hs⟩; omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  have hc : R.1 i = none := by simpa using hi
  refine ⟨e (some (i, R.2 i)), ?_, ?_⟩
  · have hal : allowO R (some (i, R.2 i)) := by
      show truncF (R.1 i) (R.2 i) = R.2 i; rw [hc]; rfl
    simpa [SpLab] using hal
  · simp [nLab, nO, hc]

end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.LabelVec =====

-- ===== begin KP.RoutingFinal =====
section
/-! # `walshTemplate_above_half` at the rate condition (the assembly)

`templates_of_rate`: labels `Fin (4n) → Letter b` with routing vectors `dLab`, charged rectangles on at
most `2n` positions (`charged_routed`), free odd-cut rectangles (`free_hfr`), weights from
`label_identity_even`; `template_of_routing` and the budget give a Good candidate. -/

namespace OAI.Computability.NearSquareRoot.KernelPass
open Matrix Finset
open Free

lemma has_split {α : Type*} {L : ℕ} (R : ChRect α L) (u v : Fin L → α) :
    R.has u v ↔ R.has u u ∧ R.has v v := by
  unfold ChRect.has
  constructor
  · intro h; exact ⟨fun i => ⟨(h i).1, (h i).1⟩, fun i => ⟨(h i).2, (h i).2⟩⟩
  · intro h i; exact ⟨(h.1 i).1, (h.2 i).1⟩

lemma sum_subtype_ite {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] (g : α → ℚ)
    (hz : ∀ x, ¬ p x → g x = 0) : (∑ x : {x // p x}, g x.1) = ∑ x, g x := by
  rw [← Finset.sum_subtype (Finset.univ.filter p) (fun x => by simp) g, Finset.sum_filter]
  exact Finset.sum_congr rfl fun x _ => by by_cases h : p x <;> simp [h, hz]

theorem templates_of_rate (num den : ℕ) (hθ : RateOK ((num : ℝ) / den)) : ∃ t : QCandidate, t.Good num den := by
  classical
  obtain ⟨n, b, hn, hq, h4', h1, h4, hrate⟩ := params_rate_side ((num : ℝ) / den) hθ
  have hL : Even (2 * (2 * n)) := ⟨2 * n, by ring⟩
  have hcardL : Fintype.card (Letter b) = 2 ^ b := by
    simp only [Letter, Fintype.card_pi, Fintype.card_bool, prod_const, card_univ, Fintype.card_fin]
  have hu : Fintype.card (Option (Fin (2 * (2 * n)) × Letter b)) = pD n b - 1 := by
    rw [Fintype.card_option, Fintype.card_prod, Fintype.card_fin, hcardL]
    simp only [pD, pL, pq]
    have : 2 * (2 * n) * 2 ^ b = 4 * n * 2 ^ b := by ring
    omega
  have hN : Fintype.card (Fin (2 * (2 * n)) → Letter b) = pN n b := by
    rw [Fintype.card_fun, hcardL, Fintype.card_fin]
    simp only [pN, pL, pq]
    congr 1; ring
  have hD1 : 1 ≤ pD n b := Nat.le_add_right_of_le (by norm_num)
  have hu1 : pD n b - 1 + 1 = pD n b := Nat.sub_add_cancel hD1
  let eA := Fintype.equivFinOfCardEq hu
  let eL := Fintype.equivFinOfCardEq hN
  let d : (Fin (2 * (2 * n)) → Letter b) → V (pD n b - 1) := fun v => dLab eA v
  have h0 : ∀ v, d v 0 = 1 := fun v => dLab_zero eA v
  have hd : ∀ v, dotV (d v) (d v) = 1 := fun v => dotV_dLab_self eA hL v
  let c : (Fin (2 * (2 * n)) → Letter b) → Chart (pD n b - 1) := fun v => chartOf (d v) (h0 v) (hd v)
  -- charged plans
  have hcr := fun j : Fin (pm n b) => charged_routed (M := pm n b) c j
  choose cinp cout hci hco hcf using hcr
  -- free plans
  have hfree : ∀ f : {R : CutRect (2 * (2 * n)) b // Odd R.cuts},
      ∃ (src tgt : (Fin (2 * (2 * n)) → Letter b) → QPlan (2 * (pm n b + (pD n b - 1))) 1 1)
        (mid : Fin (pm n b) → (Fin (2 * (2 * n)) → Letter b) → (Fin (2 * (2 * n)) → Letter b) →
          QPlan (2 * (pm n b + (pD n b - 1))) 1 1),
        (∀ v, (src v).calls ≤ 2 * (pD n b - 1 + 1)) ∧ (∀ w, (tgt w).calls ≤ 2 * (pD n b - 1 + 1)) ∧
        (∀ j t s, (mid j t s).calls = 0) ∧
        ∀ h j t s, f.1.tgt t → f.1.src s →
          qBlk h (tgt t) * qBlk h (mid j t s) * qBlk h (src s) =
            ((1 / 2 : ℚ) ^ (2 * (pD n b - 1 + 1) * h)) • lift h (U c j t s) := by
    intro f
    obtain ⟨i0, hi0, hn0⟩ := exists_pivot eA f.1 f.2 hL
    exact free_hfr (M := pm n b) (SpLab eA f.1) (nLab eA f.1) i0 d h0 hd {v | f.1.src v} {w | f.1.tgt w}
      hi0 hn0 (fun v hv a ha => by
        change gOf (d v) a = _; rw [gOf_dLab]; exact src_cond eA f.1 hv a ha)
      (fun w hw a ha => by change gOf (d w) a = _; rw [gOf_dLab]; exact tgt_zero eA f.1 hw a ha)
      (fun w hw => by change auxDot _ (gOf (d w)) = _; rw [gOf_dLab]; exact tgt_one eA f.1 hw f.2 hL)
  choose fsrc ftgt fmid hfs hft hfm hff using hfree
  let ch : {R : ChRect (Letter b) (2 * (2 * n)) // R.1.card ≤ 2 * n} →
      QCharged (2 * (pm n b + (pD n b - 1))) (pN n b) (Fin (pm n b)) := fun R =>
    { S := Finset.univ.filter fun s => R.1.has (eL.symm s) (eL.symm s)
      T := Finset.univ.filter fun t => R.1.has (eL.symm t) (eL.symm t)
      w := gch (2 * n) R.1.1.card
      inp := fun j s => cinp j (eL.symm s)
      out := fun j t => cout j (eL.symm t)
      com := fun j => comQ j }
  let fr : {R : CutRect (2 * (2 * n)) b // Odd R.cuts} →
      QFree (2 * (pm n b + (pD n b - 1))) (pN n b) (Fin (pm n b)) := fun f =>
    { S := Finset.univ.filter fun s => f.1.src (eL.symm s)
      T := Finset.univ.filter fun t => f.1.tgt (eL.symm t)
      w := -Pch (2 * n) (2 * (2 * n) - f.1.cuts)
      src := fun s => fsrc f (eL.symm s)
      tgt := fun t => ftgt f (eL.symm t)
      mid := fun j t s => fmid f j (eL.symm t) (eL.symm s) }
  have hC : Fintype.card {R : ChRect (Letter b) (2 * (2 * n)) // R.1.card ≤ 2 * n} ≤
      2 ^ pL n * pq b ^ (2 * n) := by
    rw [Fintype.card_subtype]
    have hq0 : 0 < Fintype.card (Letter b) := by rw [hcardL]; positivity
    refine (card_chRect_le (L := 2 * (2 * n)) (α := Letter b) (2 * n) hq0).trans (le_of_eq ?_)
    rw [hcardL]; simp only [pL, pq]; congr 2; ring
  have hM := pm_large n b hn (by omega)
  refine (fun H => ?_) (template_of_routing hM (pm_odd n b) ch fr
    (fun h j t s => ((1 / 2 : ℚ) ^ (2 * (pD n b - 1 + 1) * h)) • lift h (U c j (eL.symm t) (eL.symm s)))
    ?_ ?_ ?_ ?_ (2 * pD n b) ((1 + b) ^ pL n) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  obtain ⟨t, Sg, ht1, ht2, ht3⟩ := H
  have hAeq : 2 * (pm n b + (pD n b - 1)) = pA n b := by rw [pA, Nat.add_sub_assoc hD1]
  set f := ⌊(2 : ℝ) ^ pm n b / (2 * (pm n b : ℝ) ^ 3)⌋₊ with hf
  have hfl : f * (2 * pm n b ^ 3) ≤ 2 ^ pm n b := by
    have hpos : (0 : ℝ) < 2 * (pm n b : ℝ) ^ 3 := by
      have : (0 : ℝ) < pm n b := by exact_mod_cast (by omega : 0 < pm n b)
      positivity
    have h1 : (f : ℝ) ≤ (2 : ℝ) ^ pm n b / (2 * (pm n b : ℝ) ^ 3) := Nat.floor_le (by positivity)
    have h2 : (f : ℝ) * (2 * (pm n b : ℝ) ^ 3) ≤ (2 : ℝ) ^ pm n b := (le_div_iff₀ hpos).mp h1
    exact_mod_cast h2
  have hs : pN n b * f * pA n b ≤ pN n b * 2 ^ pm n b := by
    have := pA_le n b hn h4'
    calc pN n b * f * pA n b ≤ pN n b * f * (2 * pm n b ^ 3) := Nat.mul_le_mul_left _ this
      _ = pN n b * (f * (2 * pm n b ^ 3)) := by ring
      _ ≤ pN n b * 2 ^ pm n b := Nat.mul_le_mul_left _ hfl
  have hcalls := calls_le n b (2 ^ pm n b) Sg (pN n b * f) _ h1 h4' hq h4 ht3 hC hs
  rw [← hAeq, ← ht2] at hcalls
  have h2 : 2 ≤ pq b ^ pL n := le_trans (by omega) (Nat.le_self_pow (by simp [pL]; omega) _)
  have hrate2 : (pq b : ℝ) ^ (n + 5) < ((2 * (pm n b + (pD n b - 1)) : ℕ) : ℝ) ^ ((num : ℝ) / den) := by
    rw [hAeq]; exact hrate
  have hR : (0 : ℝ) < (pN n b * 2 ^ pm n b : ℕ) :=
    Nat.cast_pos.2 (Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos b)) (Nat.two_pow_pos _))
  refine ⟨⟨_, _, t⟩, ?_, ?_, ht1, ?_⟩
  · show 5 ≤ 2 * (pm n b + (pD n b - 1)); have := Nat.one_le_pow (2 * n) (pq b) (by omega); simp only [pm, pD]; omega
  · exact le_trans h2 (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (by positivity)))
  · refine lt_of_le_of_lt (b := (pq b : ℝ) ^ (n + 5) * (pN n b * 2 ^ pm n b : ℕ)) (by exact_mod_cast hcalls) ?_
    rw [mul_comm]; exact mul_lt_mul_of_pos_left hrate2 hR
  · intro h R j t s _ _
    exact hcf j h (eL.symm t) (eL.symm s)
  · intro h f j t s ht hs
    have ht' : f.1.tgt (eL.symm t) := (Finset.mem_filter.1 ht).2
    have hs' : f.1.src (eL.symm s) := (Finset.mem_filter.1 hs).2
    exact hff f h j _ _ ht' hs'
  · intro t s
    have key := label_identity_even (b := b) (2 * n) (eL.symm s) (eL.symm t)
    have e1 : (∑ R : {R : ChRect (Letter b) (2 * (2 * n)) // R.1.card ≤ 2 * n},
        if t ∈ (ch R).T ∧ s ∈ (ch R).S then (ch R).w else 0) =
        ∑ R : ChRect (Letter b) (2 * (2 * n)),
          if R.has (eL.symm s) (eL.symm t) then gch (2 * n) R.1.card else 0 := by
      rw [← sum_subtype_ite (fun R : ChRect (Letter b) (2 * (2 * n)) => R.1.card ≤ 2 * n)
        (fun R => if R.has (eL.symm s) (eL.symm t) then gch (2 * n) R.1.card else 0)
        (fun R hR => by rw [gch_supp (2 * n) R.1.card (by omega)]; simp)]
      refine Finset.sum_congr rfl fun R _ => ?_
      have hiff : (t ∈ (ch R).T ∧ s ∈ (ch R).S) ↔ R.1.has (eL.symm s) (eL.symm t) := by
        rw [has_split R.1 (eL.symm s) (eL.symm t)]
        simp only [ch, Finset.mem_filter, Finset.mem_univ, true_and]
        exact and_comm
      simp only [hiff]
      rfl
    have e2 : (∑ f : {R : CutRect (2 * (2 * n)) b // Odd R.cuts},
        if t ∈ (fr f).T ∧ s ∈ (fr f).S then (fr f).w else 0) =
        ∑ R : CutRect (2 * (2 * n)) b, if R.src (eL.symm s) ∧ R.tgt (eL.symm t) then
          (if Odd R.cuts then -Pch (2 * n) (2 * (2 * n) - R.cuts) else 0) else 0 := by
      rw [← sum_subtype_ite (fun R : CutRect (2 * (2 * n)) b => Odd R.cuts)
        (fun R => if R.src (eL.symm s) ∧ R.tgt (eL.symm t) then
          (if Odd R.cuts then -Pch (2 * n) (2 * (2 * n) - R.cuts) else 0) else 0)
        (fun R hR => by simp only [hR, ↓reduceIte, ite_self])]
      refine Finset.sum_congr rfl fun f _ => ?_
      have hiff : (t ∈ (fr f).T ∧ s ∈ (fr f).S) ↔ (f.1.src (eL.symm s) ∧ f.1.tgt (eL.symm t)) := by
        simp only [fr, Finset.mem_filter, Finset.mem_univ, true_and]
        exact and_comm
      simp only [hiff, if_pos f.2]
      rfl
    rw [e1, e2, key]
    by_cases hst : s = t
    · subst hst; simp only [↓reduceIte]
    · rw [if_neg hst, if_neg (fun h => hst (eL.symm.injective h))]
  · intro h j l
    exact label_self_spectral c j (eL.symm l) h
  · intro R j s; exact hci j _
  · intro R j t; exact hco j _
  · intro R j
    show (comQ j).calls ≤ 2 * pD n b
    rw [comQ_calls, hu1]
  · intro f j t s; exact hfm f j _ _
  · intro f s; exact (hfs f _).trans (by rw [hu1])
  · intro f t; exact (hft f _).trans (by rw [hu1])
  · intro s
    calc (Finset.univ.filter fun f : {R : CutRect (2 * (2 * n)) b // Odd R.cuts} => s ∈ (fr f).S).card
        ≤ (Finset.univ.filter fun R : CutRect (2 * (2 * n)) b => R.src (eL.symm s)).card :=
          Finset.card_le_card_of_injOn Subtype.val (fun f hf => Finset.mem_filter.2 ⟨Finset.mem_univ _,
            (Finset.mem_filter.1 (Finset.mem_filter.1 hf).2).2⟩)
            (Subtype.val_injective.injOn)
      _ = (b + 1) ^ (2 * (2 * n)) := card_src _
      _ ≤ (1 + b) ^ pL n := le_of_eq (by simp only [pL]; rw [add_comm]; congr 1; ring)
  · intro t
    calc (Finset.univ.filter fun f : {R : CutRect (2 * (2 * n)) b // Odd R.cuts} => t ∈ (fr f).T).card
        ≤ (Finset.univ.filter fun R : CutRect (2 * (2 * n)) b => R.tgt (eL.symm t)).card :=
          Finset.card_le_card_of_injOn Subtype.val (fun f hf => Finset.mem_filter.2 ⟨Finset.mem_univ _,
            (Finset.mem_filter.1 (Finset.mem_filter.1 hf).2).2⟩)
            (Subtype.val_injective.injOn)
      _ = (b + 1) ^ (2 * (2 * n)) := card_tgt _
      _ ≤ (1 + b) ^ pL n := le_of_eq (by simp only [pL]; rw [add_comm]; congr 1; ring)

end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.RoutingFinal =====

-- ===== begin KP.AboveHalf =====
section
/-! # Walsh templates above one half for rational plans: a Good candidate for every exponent above 1/2 -/

namespace OAI.Computability.NearSquareRoot.KernelPass

/-- **Walsh templates above one half (rational plans).** For every rational exponent above 1/2 there is a Good candidate. -/
theorem walshTemplate_above_half : ∀ num den : ℕ, (1 : ℝ) / 2 < num / den → ∃ t : QCandidate, t.Good num den :=
  fun num den h => templates_of_rate num den (rateOK_of_half h)

end OAI.Computability.NearSquareRoot.KernelPass
end
-- ===== end KP.AboveHalf =====
