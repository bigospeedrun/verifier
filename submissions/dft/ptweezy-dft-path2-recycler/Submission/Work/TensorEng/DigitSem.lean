import Submission.Work.TensorEng.Lift

/-!
# T1, part 3: the semantics of a word on an arbitrary digit type, with spectator digits

`gwalkI P w x`: the word `w` acting on data whose digit index is any finite type `I`; every letter acts by its
role matrix on the ACTIVE digits (`P i`) and by the identity on the others (spectators).

* `gwalkI_true` : with `I = Fin f` and every digit active this is the leader's `gwalk f`;
* `gwalkI_reidx` : relabelling the digits along an equivalence commutes with the semantics;
* `gwalkI_slice` : with digits `A ⊕ S` and active `A`, the semantics acts slice by slice of the spectators;
* `certI` : a mixed certificate `GLiveKernelM e (blockMat ∘ tz) w` gives the same statement with spectators:
  every live role ends at `blockMat (tz l)` on its active digits, the identity on its spectator digits.

-- changed for the tensor-power extension (30103/10000000); see Submission.lean
-/

namespace TensorEng
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.GF OAI.PowerSaving.MX Matrix Finset

noncomputable section

section DigitSem
variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

/-- Data whose digit index is a finite type `I`. -/
abbrev DataI (α ρ I : Type*) := ρ → (I → Space α) → ℂ

/-- `A` on the active digits, the identity on the others. -/
def dopI {I : Type*} [Fintype I] [DecidableEq I] (P : I → Prop) [DecidablePred P] (A : CMat α) :
    Matrix (I → Space α) (I → Space α) ℂ :=
  digitProd (fun i => if P i then A else (1 : CMat α))

/-- One letter on data with digit index `I` and active digits `P`. -/
def actI {I : Type*} [Fintype I] [DecidableEq I] (P : I → Prop) [DecidablePred P] :
    GMove α ρ → DataI α ρ I → DataI α ρ I
  | .old (.localM g), x => fun r y => ∑ j, (g r j : ℂ) * x j y
  | mv, x => fun r => dopI P (rmat mv r) *ᵥ x r

/-- The semantics of a word on data with digit index `I` and active digits `P`. -/
def gwalkI {I : Type*} [Fintype I] [DecidableEq I] (P : I → Prop) [DecidablePred P] (w : GWord α ρ)
    (x : DataI α ρ I) : DataI α ρ I :=
  w.foldl (fun y mv => actI P mv y) x

section Basic
variable {I : Type*} [Fintype I] [DecidableEq I] (P : I → Prop) [DecidablePred P]

@[simp] lemma gwalkI_nil (x : DataI α ρ I) : gwalkI P ([] : GWord α ρ) x = x := rfl

lemma gwalkI_cons (mv : GMove α ρ) (w : GWord α ρ) (x : DataI α ρ I) :
    gwalkI P (mv :: w) x = gwalkI P w (actI P mv x) := rfl

lemma gwalkI_append (w w' : GWord α ρ) (x : DataI α ρ I) :
    gwalkI P (w ++ w') x = gwalkI P w' (gwalkI P w x) := by
  simp [gwalkI, List.foldl_append]

lemma actI_local (mv : GMove α ρ) (h : IsLocal mv) (x : DataI α ρ I) (r : ρ) :
    actI P mv x r = dopI P (rmat mv r) *ᵥ x r := by
  cases mv with
  | old mv =>
    cases mv with
    | localM g => exact h.elim
    | shift l z => rfl
    | block l rk z ind => rfl
  | perm l G => rfl
  | phase l z c => rfl

end Basic

/-! ### agreement with the leader's semantics -/

lemma dopI_true (f : ℕ) (A : CMat α) : dopI (fun _ : Fin f => True) A = digitProd (fun _ : Fin f => A) := by
  unfold dopI
  simp only [if_true]

lemma actI_true (f : ℕ) (mv : GMove α ρ) (x : Data α ρ f) :
    actI (fun _ : Fin f => True) mv x = mv.act f x := by
  by_cases h : IsLocal mv
  · funext r
    rw [actI_local _ mv h, act_local f mv h x r, dopI_true]
    all_goals rfl
  · cases mv with
    | old mv =>
      cases mv with
      | localM g =>
        funext r y
        rfl
      | shift l z => exact absurd trivial h
      | block l rk z ind => exact absurd trivial h
    | perm l G => exact absurd trivial h
    | phase l z c => exact absurd trivial h

lemma gwalkI_true (f : ℕ) (w : GWord α ρ) (x : Data α ρ f) :
    gwalkI (fun _ : Fin f => True) w x = gwalk f w x := by
  induction w generalizing x with
  | nil => rfl
  | cons mv w ih => rw [gwalkI_cons, gwalk_cons, actI_true, ih]

/-! ### relabelling the digits -/

section Reidx
variable {I I' : Type*} [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I']

/-- Data relabelled along `e : I ≃ I'`. -/
def reidx (e : I ≃ I') (x : DataI α ρ I') : DataI α ρ I := fun r y => x r (y ∘ e.symm)

lemma dopI_reidx (e : I ≃ I') (P' : I' → Prop) [DecidablePred P'] (A : CMat α) (v : (I' → Space α) → ℂ)
    (y : I → Space α) :
    (dopI (fun i => P' (e i)) A *ᵥ fun y' => v (y' ∘ e.symm)) y = (dopI P' A *ᵥ v) (y ∘ e.symm) := by
  simp only [mulVec, dotProduct, dopI, digitProd_apply]
  -- reindex the summation variable along `y' ↦ y' ∘ e.symm`
  refine Fintype.sum_equiv (Equiv.arrowCongr e (Equiv.refl (Space α))) _ _ (fun y' => ?_)
  congr 1
  rw [← Equiv.prod_comp e]
  apply Finset.prod_congr rfl
  intro i _
  simp [Equiv.arrowCongr_apply, Function.comp]

lemma actI_reidx (e : I ≃ I') (P' : I' → Prop) [DecidablePred P'] (mv : GMove α ρ) (x : DataI α ρ I') :
    actI (fun i => P' (e i)) mv (reidx e x) = reidx e (actI P' mv x) := by
  by_cases h : IsLocal mv
  · funext r y
    show actI (fun i => P' (e i)) mv (reidx e x) r y = actI P' mv x r (y ∘ e.symm)
    rw [actI_local _ mv h, actI_local _ mv h]
    exact dopI_reidx e P' (rmat mv r) (x r) y
  · cases mv with
    | old mv =>
      cases mv with
      | localM g => rfl
      | shift l z => exact absurd trivial h
      | block l rk z ind => exact absurd trivial h
    | perm l G => exact absurd trivial h
    | phase l z c => exact absurd trivial h

lemma gwalkI_reidx (e : I ≃ I') (P' : I' → Prop) [DecidablePred P'] (w : GWord α ρ) (x : DataI α ρ I') :
    gwalkI (fun i => P' (e i)) w (reidx e x) = reidx e (gwalkI P' w x) := by
  induction w generalizing x with
  | nil => rfl
  | cons mv w ih => rw [gwalkI_cons, gwalkI_cons, actI_reidx, ih]

end Reidx

/-! ### spectator digits -/

section Slice
variable {A S : Type*} [Fintype A] [DecidableEq A] [Fintype S] [DecidableEq S]

/-- Active digits of `A ⊕ S`: the left ones. -/
def isL : A ⊕ S → Prop := fun i => i.isLeft = true

instance : DecidablePred (isL (A := A) (S := S)) := fun i => by unfold isL; infer_instance

@[simp] lemma ite_isL_inl {β : Type*} (a : A) (t f : β) :
    (if isL (A := A) (S := S) (Sum.inl a) then t else f) = t := if_pos rfl

@[simp] lemma ite_isL_inr {β : Type*} (s : S) (t f : β) :
    (if isL (A := A) (S := S) (Sum.inr s) then t else f) = f := if_neg (fun h => Bool.false_ne_true h)

/-- The slice of data at a fixed value `s` of the spectator digits. -/
def slice (x : DataI α ρ (A ⊕ S)) (s : S → Space α) : DataI α ρ A := fun r a => x r (Sum.elim a s)

lemma dopI_slice (M : CMat α) (v : ((A ⊕ S) → Space α) → ℂ) (a : A → Space α) (s : S → Space α) :
    (dopI isL M *ᵥ v) (Sum.elim a s)
      = (digitProd (fun _ : A => M) *ᵥ fun a' => v (Sum.elim a' s)) a := by
  have he : ∀ (x : A → Space α) (y : S → Space α),
      (Equiv.sumArrowEquivProdArrow A S (Space α)).symm (x, y) = Sum.elim x y := fun _ _ => rfl
  simp only [mulVec, dotProduct, dopI, digitProd_apply]
  rw [← (Equiv.sumArrowEquivProdArrow A S (Space α)).symm.sum_comp, Fintype.sum_prod_type]
  simp only [he, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, ite_isL_inl, ite_isL_inr, Matrix.one_apply]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_eq_single s]
  · simp
  · intro y _ hy
    rw [OAI.PowerSaving.prod_delta s y, if_neg (fun h => hy h.symm)]
    simp
  · intro h; exact absurd (Finset.mem_univ s) h

lemma actI_slice (mv : GMove α ρ) (x : DataI α ρ (A ⊕ S)) (s : S → Space α) :
    slice (actI isL mv x) s = actI (fun _ : A => True) mv (slice x s) := by
  by_cases h : IsLocal mv
  · funext r a
    simp only [slice]
    rw [actI_local _ mv h, actI_local _ mv h, dopI_slice]
    unfold dopI
    simp only [ite_true]
    all_goals rfl
  · cases mv with
    | old mv =>
      cases mv with
      | localM g => rfl
      | shift l z => exact absurd trivial h
      | block l rk z ind => exact absurd trivial h
    | perm l G => exact absurd trivial h
    | phase l z c => exact absurd trivial h

lemma gwalkI_slice (w : GWord α ρ) (x : DataI α ρ (A ⊕ S)) (s : S → Space α) :
    slice (gwalkI isL w x) s = gwalkI (fun _ : A => True) w (slice x s) := by
  induction w generalizing x with
  | nil => rfl
  | cons mv w ih => rw [gwalkI_cons, gwalkI_cons, ih, actI_slice]

end Slice

/-! ### the certificate with spectators -/

section Cert
variable {σ : Type*} {A S : Type*} [Fintype A] [DecidableEq A] [Fintype S] [DecidableEq S]

/-- All digits active, any finite digit type: the certificate (by relabelling to `Fin (card A)`). -/
theorem certI_all {e : σ → ρ} {tr : σ → ℕ} {tz : ∀ l, Fin (tr l) → Space α} {w : GWord α ρ}
    (hw : GLiveKernelM e (fun l => blockMat (tz l)) w) (x : DataI α ρ A)
    (hx : ∀ r, (∀ l, e l ≠ r) → x r = 0) (l : σ) :
    gwalkI (fun _ : A => True) w x (e l) = digitProd (fun _ : A => blockMat (tz l)) *ᵥ x (e l) := by
  set eA : A ≃ Fin (Fintype.card A) := Fintype.equivFin A
  -- the data on `Fin n` digits whose relabelling is `x`
  set x' : Data α ρ (Fintype.card A) := fun r y => x r (y ∘ eA) with hx'
  have hrx : reidx eA x' = x := by
    funext r y
    simp only [reidx, hx']
    congr 1
    funext i
    simp
  have hx'0 : ∀ r, (∀ l, e l ≠ r) → x' r = 0 := by
    intro r hr
    funext y
    simp only [hx', hx r hr, Pi.zero_apply]
  have key := gwalkI_reidx eA (fun _ : Fin (Fintype.card A) => True) w x'
  rw [hrx] at key
  have key' : gwalkI (fun _ : A => True) w x = reidx eA (gwalkI (fun _ : Fin (Fintype.card A) => True) w x') :=
    key
  rw [key']
  funext y
  simp only [reidx]
  rw [gwalkI_true, hw _ x' hx'0 l]
  -- `matAct` on `Fin n` relabelled back to `A`
  have h2 := dopI_reidx eA (fun _ : Fin (Fintype.card A) => True) (blockMat (tz l)) (x' (e l)) y
  have h3 : (fun y' : A → Space α => x' (e l) (y' ∘ eA.symm)) = x (e l) := by
    funext y'
    simp only [hx']
    congr 1
    funext i
    simp
  rw [h3] at h2
  unfold dopI at h2
  simp only [if_true] at h2
  rw [h2]
  all_goals rfl

/-- **The certificate with spectator digits.** -/
theorem certI {e : σ → ρ} {tr : σ → ℕ} {tz : ∀ l, Fin (tr l) → Space α} {w : GWord α ρ}
    (hw : GLiveKernelM e (fun l => blockMat (tz l)) w) (x : DataI α ρ (A ⊕ S))
    (hx : ∀ r, (∀ l, e l ≠ r) → x r = 0) (l : σ) :
    gwalkI isL w x (e l) = dopI isL (blockMat (tz l)) *ᵥ x (e l) := by
  funext y
  have hy : y = Sum.elim (fun a => y (Sum.inl a)) (fun s => y (Sum.inr s)) := by
    funext i
    cases i <;> rfl
  rw [hy]
  have h1 : gwalkI isL w x (e l) (Sum.elim (fun a => y (Sum.inl a)) (fun s => y (Sum.inr s)))
      = gwalkI (fun _ : A => True) w (slice x (fun s => y (Sum.inr s))) (e l) (fun a => y (Sum.inl a)) :=
    congr_fun (congr_fun (gwalkI_slice w x (fun s => y (Sum.inr s))) (e l)) (fun a => y (Sum.inl a))
  have h0 : ∀ r, (∀ l, e l ≠ r) → slice x (fun s => y (Sum.inr s)) r = 0 := by
    intro r hr
    funext a
    simp only [slice, hx r hr, Pi.zero_apply]
  rw [h1, certI_all hw (slice x (fun s => y (Sum.inr s))) h0 l, dopI_slice]
  all_goals rfl

end Cert

end DigitSem

end

end TensorEng
