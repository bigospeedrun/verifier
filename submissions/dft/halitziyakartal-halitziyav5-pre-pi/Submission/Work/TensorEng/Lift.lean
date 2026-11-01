import Submission.Work.TensorEng.Basic

/-!
# T1, part 2: lifting blocks, address permutations and phases; the column-count transport

* `dop_insert`, `dop_list_prod`, `trp_list_prod` : operators on several digits, products of lists;
* `dirs_perm`, `blockMat_eq_dirs` : a block is the product of its directional factors, in any order;
* `digitProd_trp` : at column count `f` the transport is digitwise.

-- changed for the tensor-power extension (30103/10000000); see Submission.lean
-/

namespace TensorEng
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.GF Matrix Finset

noncomputable section

section Lift
variable {α β J : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype J] [DecidableEq J]

/-! ### several digits -/

lemma dop_insert {d : J} {D : Finset J} (hd : d ∉ D) (A : CMat α) :
    dop (insert d D) A = dop {d} A * dop D A := by
  unfold dop
  rw [digitProd_mul]
  congr 1
  funext j
  by_cases h : j = d
  · subst h
    simp [hd]
  · simp [h]

lemma dop_list_prod (D : Finset J) (Ms : List (CMat α)) :
    dop D Ms.prod = (Ms.map (dop D)).prod := by
  induction Ms with
  | nil => simp [dop_one]
  | cons M Ms ih => rw [List.prod_cons, ← dop_mul, ih, List.map_cons, List.prod_cons]

lemma trp_list_prod {γ δ : Type*} [Fintype γ] [Fintype δ] [DecidableEq γ] [DecidableEq δ] (E : γ ≃ δ)
    (Ms : List (Matrix γ γ ℂ)) : trp E Ms.prod = (Ms.map (trp E)).prod := by
  induction Ms with
  | nil => simp [trp_one]
  | cons M Ms ih => rw [List.prod_cons, trp_mul, ih, List.map_cons, List.prod_cons]

/-- Blocks (products of directional factors) are invariant under permutation of the directions. -/
lemma dirs_perm {γ : Type*} [Fintype γ] [DecidableEq γ] {L L' : List (Space γ)} (h : L.Perm L') :
    (L.map dir).prod = (L'.map dir).prod := by
  rw [prod_dir_wrap, prod_dir_wrap]
  congr 1
  funext x
  exact (h.map _).prod_eq

lemma blockMat_eq_dirs {γ : Type*} [Fintype γ] [DecidableEq γ] {r : ℕ} (z : Fin r → Space γ) :
    blockMat z = ((List.ofFn z).map dir).prod := by
  unfold blockMat
  rw [List.map_ofFn]
  rfl

/-! ### the column-count transport -/

/-- At column count `f`, the transport is digitwise. -/
lemma digitProd_trp {γ δ : Type*} [Fintype γ] [Fintype δ] (E : γ ≃ δ) (f : ℕ) (M : Matrix γ γ ℂ) :
    digitProd (fun _ : Fin f => trp E M) = trp (Equiv.piCongrRight fun _ : Fin f => E) (digitProd fun _ : Fin f => M) := by
  ext x y
  simp only [digitProd_apply, trp_apply]
  rfl

end Lift

end

end TensorEng
