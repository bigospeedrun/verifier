import Submission.Work.TensorEng.Transport
import Submission.Work.GFrame.Engine.Over

/-!
# T1, part 5: the tensor product of two certified words

A certified unit `CU α ρ σ` is a word `wd` on labels `α`, roles `ρ`, with live roles `e : σ → ρ` and a mixed
certificate `GLiveKernelM e (fun l => blockMat (tz l)) wd` (the field `hw` of the leader's `Eng`).

For units `U` (labels `α`) and `V` (labels `β`) the product word `prodWord U V` on labels `α × β` has roles
`(ρ × σ') ⊕ (Fin |U.wd| × ρ')`:

* every letter of `U` except a block is lifted, for every live role `l'` of `V`, through the digit map `ER V l'`
  (digits = a basis of `Space β` starting with `V.tz l'`) onto the roles `(·, l')` (`pieceL`);
* a block of `U` at position `q` (role `r`, directions `z`) is replaced by ONE INVOCATION of `V`'s word, lifted
  through the digit map `EL z` (digits = a basis of `Space α` starting with `z`), with `V`'s live roles placed on
  `(r, ·)` and `V`'s scratch roles on the fresh copy `(q, ·)` (`pieceV`).

`prod_cert`: the product word has the mixed certificate with live roles `σ × σ'` and targets the blocks of the
Kronecker families `tz l ⊗ tz' l'` (`tzP`, ranks `tr' l' * tr l`).
`rk_prodWord`: its paid ranks are the products `k * k'` of a paid rank of `U` and a paid rank of `V`.

-- changed for the tensor-power extension (30103/10000000); see Submission.lean
-/

namespace TensorEng
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.GF OAI.PowerSaving.MX Matrix Finset

noncomputable section

/-! ### digit maps of a splitting -/

section DigitMaps
variable {α β γ D : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
  [Fintype D] [DecidableEq D]

lemma T_zero (T : Space D ≃ Space β) (hT : ∀ u v, T (u + v) = T u + T v) : T 0 = 0 := by
  have h := hT 0 0
  rw [add_zero] at h
  have h2 : T 0 + T 0 = 0 := binary_cancel _
  rw [h2] at h
  exact h

lemma T_smul (T : Space D ≃ Space β) (hT : ∀ u v, T (u + v) = T u + T v) (a : F) (u : Space D) :
    T (a • u) = a • T u := by
  rcases bit_cases a with rfl | rfl
  · rw [zero_smul, zero_smul, T_zero T hT]
  · rw [one_smul, one_smul]

lemma slice_single (d : D) (y : Space γ) (c : γ) :
    (fun d2 => (Pi.single d y : D → Space γ) d2 c) = y c • (eu d : Space D) := by
  funext d2
  by_cases h : d2 = d
  · subst h
    simp [eu]
  · simp [eu, Pi.single_apply, h, Ne.symm h]

/-- The additive bijection `Space (Fin r ⊕ Fin m) ≃ Space α` of a splitting (block coordinates first). -/
def splitT {r m : ℕ} (S : Split α (Fin m) (Fin r)) : Space (Fin r ⊕ Fin m) ≃ Space α where
  toFun v := S.e.symm (fun k => v (Sum.inr k), fun i => v (Sum.inl i))
  invFun x := Sum.elim (S.e x).2 (S.e x).1
  left_inv v := by
    simp only [Equiv.apply_symm_apply]
    funext d
    cases d <;> rfl
  right_inv x := S.e.symm_apply_apply x

lemma splitT_add {r m : ℕ} (S : Split α (Fin m) (Fin r)) (u v : Space (Fin r ⊕ Fin m)) :
    splitT S (u + v) = splitT S u + splitT S v := by
  show S.e.symm _ = S.e.symm _ + S.e.symm _
  rw [← S.symm_add]
  all_goals rfl

lemma splitT_eu {r m : ℕ} (S : Split α (Fin m) (Fin r)) (i : Fin r) :
    splitT S (eu (Sum.inl i)) = S.e.symm (0, eu i) := by
  show S.e.symm _ = _
  congr 1
  refine Prod.ext ?_ ?_
  · funext k
    simp [eu]
  · funext j
    simp [eu]

/-- Right digit map: the digits index a basis of `Space β` (through `T`), digit values in `Space γ`. -/
def EdR (γ : Type*) [Fintype γ] (T : Space D ≃ Space β) : (D → Space γ) ≃ Space (γ × β) where
  toFun y p := T (fun d => y d p.1) p.2
  invFun v d c := T.symm (fun b => v (c, b)) d
  left_inv y := by
    funext d c
    show T.symm (T (fun d' => y d' c)) d = y d c
    rw [Equiv.symm_apply_apply]
  right_inv v := by
    funext p
    show T (T.symm (fun b => v (p.1, b))) p.2 = v p
    rw [Equiv.apply_symm_apply]

lemma EdR_apply (T : Space D ≃ Space β) (y : D → Space γ) (p : γ × β) :
    EdR γ T y p = T (fun d => y d p.1) p.2 := rfl

lemma EdR_add (T : Space D ≃ Space β) (hT : ∀ u v, T (u + v) = T u + T v) (y y' : D → Space γ) :
    EdR γ T (y + y') = EdR γ T y + EdR γ T y' := by
  funext p
  exact congr_fun (hT (fun d => y d p.1) (fun d => y' d p.1)) p.2

lemma EdR_single (T : Space D ≃ Space β) (hT : ∀ u v, T (u + v) = T u + T v) (d : D) (y : Space γ) :
    EdR γ T (Pi.single d y) = kron y (T (eu d)) := by
  funext p
  show T (fun d2 => (Pi.single d y : D → Space γ) d2 p.1) p.2 = y p.1 * T (eu d) p.2
  rw [slice_single, T_smul T hT]
  all_goals rfl

/-- Left digit map: the digits index a basis of `Space α` (through `T`), digit values in `Space γ`. -/
def EdL (γ : Type*) [Fintype γ] (T : Space D ≃ Space α) : (D → Space γ) ≃ Space (α × γ) where
  toFun y p := T (fun d => y d p.2) p.1
  invFun v d c := T.symm (fun a => v (a, c)) d
  left_inv y := by
    funext d c
    show T.symm (T (fun d' => y d' c)) d = y d c
    rw [Equiv.symm_apply_apply]
  right_inv v := by
    funext p
    show T (T.symm (fun a => v (a, p.2))) p.1 = v p
    rw [Equiv.apply_symm_apply]

lemma EdL_add (T : Space D ≃ Space α) (hT : ∀ u v, T (u + v) = T u + T v) (y y' : D → Space γ) :
    EdL γ T (y + y') = EdL γ T y + EdL γ T y' := by
  funext p
  exact congr_fun (hT (fun d => y d p.2) (fun d => y' d p.2)) p.1

lemma EdL_single (T : Space D ≃ Space α) (hT : ∀ u v, T (u + v) = T u + T v) (d : D) (y : Space γ) :
    EdL γ T (Pi.single d y) = kron (T (eu d)) y := by
  funext p
  show T (fun d2 => (Pi.single d y : D → Space γ) d2 p.2) p.1 = T (eu d) p.1 * y p.2
  rw [slice_single, T_smul T hT]
  show y p.2 * T (eu d) p.1 = T (eu d) p.1 * y p.2
  ring

end DigitMaps

/-! ### certified units -/

/-- A certified unit: a word whose live roles end at blocks (the certificate field `hw` of the leader's `Eng`). -/
structure CU (α ρ σ : Type*) [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] where
  e : σ → ρ
  he : Function.Injective e
  tr : σ → ℕ
  tz : ∀ l, Fin (tr l) → Space α
  tind : ∀ l, LinearIndependent F (tz l)
  wd : GWord α ρ
  hw : GLiveKernelM e (fun l => blockMat (tz l)) wd

namespace CU
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] (U : CU α ρ σ)

/-- The live role behind a role, if any. -/
def liveOf (r : ρ) : Option σ :=
  @dite _ (∃ l, U.e l = r) (Classical.propDecidable _) (fun h => some h.choose) (fun _ => none)

lemma liveOf_e (l : σ) : U.liveOf (U.e l) = some l := by
  have h : ∃ l', U.e l' = U.e l := ⟨l, rfl⟩
  unfold liveOf
  rw [dif_pos h]
  exact congrArg some (U.he h.choose_spec)

lemma liveOf_some {r : ρ} {l : σ} (h : U.liveOf r = some l) : U.e l = r := by
  unfold liveOf at h
  by_cases h' : ∃ l', U.e l' = r
  · rw [dif_pos h'] at h
    obtain rfl := Option.some.inj h
    exact h'.choose_spec
  · rw [dif_neg h'] at h
    cases h

lemma liveOf_none {r : ρ} (h : U.liveOf r = none) (l : σ) : U.e l ≠ r := by
  intro hl
  have h1 := U.liveOf_e l
  rw [hl, h] at h1
  cases h1

end CU

/-! ### the product -/

section Product
variable {α β ρ ρ' σ σ' : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype ρ] [DecidableEq ρ] [Fintype ρ'] [DecidableEq ρ'] [Fintype σ] [DecidableEq σ]
  [Fintype σ'] [DecidableEq σ']

/-- Roles of the product: `V`'s live roles for every role of `U`, and `N` fresh copies of `V`'s roles. -/
abbrev RW (ρ σ' ρ' : Type*) (N : ℕ) := (ρ × σ') ⊕ (Fin N × ρ')

/-- `U`'s roles placed on the copy of `V`'s live role `l'`. -/
def embL (N : ℕ) (l' : σ') : ρ ↪ RW ρ σ' ρ' N :=
  ⟨fun r => Sum.inl (r, l'), fun a b h => (Prod.mk.inj (Sum.inl.inj h)).1⟩

/-- `V`'s roles placed for an invocation at position `q` on `U`'s role `r`. -/
def embVf (V : CU β ρ' σ') (N : ℕ) (q : Fin N) (r : ρ) (r' : ρ') : RW ρ σ' ρ' N :=
  (V.liveOf r').elim (Sum.inr (q, r')) (fun l' => Sum.inl (r, l'))

lemma embVf_live (V : CU β ρ' σ') (N : ℕ) (q : Fin N) (r : ρ) (l' : σ') :
    embVf V N q r (V.e l') = Sum.inl (r, l') := by
  simp [embVf, V.liveOf_e l']

lemma embVf_dead (V : CU β ρ' σ') (N : ℕ) (q : Fin N) (r : ρ) {r' : ρ'} (h : V.liveOf r' = none) :
    embVf V N q r r' = Sum.inr (q, r') := by
  simp [embVf, h]

lemma embVf_inj (V : CU β ρ' σ') (N : ℕ) (q : Fin N) (r : ρ) :
    Function.Injective (embVf V N q r) := by
  intro a b h
  cases ha : V.liveOf a with
  | none =>
    cases hb : V.liveOf b with
    | none =>
      rw [embVf_dead V N q r ha, embVf_dead V N q r hb] at h
      exact (Prod.mk.inj (Sum.inr.inj h)).2
    | some lb =>
      rw [embVf_dead V N q r ha, ← V.liveOf_some hb, embVf_live] at h
      cases h
  | some la =>
    cases hb : V.liveOf b with
    | none =>
      rw [← V.liveOf_some ha, embVf_live, embVf_dead V N q r hb] at h
      cases h
    | some lb =>
      rw [← V.liveOf_some ha, ← V.liveOf_some hb, embVf_live, embVf_live] at h
      rw [← V.liveOf_some ha, ← V.liveOf_some hb, (Prod.mk.inj (Sum.inl.inj h)).2]

def embV (V : CU β ρ' σ') (N : ℕ) (q : Fin N) (r : ρ) : ρ' ↪ RW ρ σ' ρ' N :=
  ⟨embVf V N q r, embVf_inj V N q r⟩

lemma embV_out_inl (V : CU β ρ' σ') (N : ℕ) (q : Fin N) {r r2 : ρ} (h : r2 ≠ r) (l' : σ') :
    (Sum.inl (r2, l') : RW ρ σ' ρ' N) ∉ covered (embV V N q r) := by
  rw [cover_iff]
  rintro ⟨r', hr'⟩
  change embVf V N q r r' = _ at hr'
  cases hl : V.liveOf r' with
  | none =>
    rw [embVf_dead V N q r hl] at hr'
    cases hr'
  | some l2 =>
    rw [← V.liveOf_some hl, embVf_live] at hr'
    exact h (Prod.mk.inj (Sum.inl.inj hr')).1.symm

lemma embV_out_inr (V : CU β ρ' σ') (N : ℕ) {q q2 : Fin N} (h : q2 ≠ q) (r : ρ) (r' : ρ') :
    (Sum.inr (q2, r') : RW ρ σ' ρ' N) ∉ covered (embV V N q r) := by
  rw [cover_iff]
  rintro ⟨r1, hr1⟩
  change embVf V N q r r1 = _ at hr1
  cases hl : V.liveOf r1 with
  | none =>
    rw [embVf_dead V N q r hl] at hr1
    exact h (Prod.mk.inj (Sum.inr.inj hr1)).1.symm
  | some l2 =>
    rw [← V.liveOf_some hl, embVf_live] at hr1
    cases hr1

lemma embL_out_inl (N : ℕ) {l' l2 : σ'} (h : l2 ≠ l') (r : ρ) :
    (Sum.inl (r, l2) : RW ρ σ' ρ' N) ∉ covered (embL N l') := by
  rw [cover_iff]
  rintro ⟨r1, hr1⟩
  change Sum.inl (r1, l') = _ at hr1
  exact h (Prod.mk.inj (Sum.inl.inj hr1)).2.symm

lemma embL_out_inr (N : ℕ) (l' : σ') (p : Fin N × ρ') :
    (Sum.inr p : RW ρ σ' ρ' N) ∉ covered (embL (ρ := ρ) N l') := by
  rw [cover_iff]
  rintro ⟨r1, hr1⟩
  change Sum.inl (r1, l') = _ at hr1
  cases hr1

/-! #### the digit maps of the product -/

/-- The splitting of `Space β` adapted to `V`'s target on live role `l'`. -/
def SR (V : CU β ρ' σ') (l' : σ') : Split β (Fin (Fintype.card β - V.tr l')) (Fin (V.tr l')) :=
  Classical.choose (exists_split (V.tz l') (V.tind l'))

lemma SR_spec (V : CU β ρ' σ') (l' : σ') (i : Fin (V.tr l')) : (SR V l').e.symm (0, eu i) = V.tz l' i :=
  Classical.choose_spec (exists_split (V.tz l') (V.tind l')) i

/-- The digit map of `V`'s live role `l'`: digits = a basis of `Space β` starting with `V.tz l'`. -/
def ER (V : CU β ρ' σ') (l' : σ') :
    ((Fin (V.tr l') ⊕ Fin (Fintype.card β - V.tr l')) → Space α) ≃ Space (α × β) :=
  EdR α (splitT (SR V l'))

lemma ER_add (V : CU β ρ' σ') (l' : σ') (y y' : (Fin (V.tr l') ⊕ Fin (Fintype.card β - V.tr l')) → Space α) :
    ER V l' (y + y') = ER V l' y + ER V l' y' :=
  EdR_add _ (splitT_add _) y y'

lemma ER_single (V : CU β ρ' σ') (l' : σ') (j : Fin (V.tr l')) (y : Space α) :
    ER V l' (Pi.single (Sum.inl j) y) = kron y (V.tz l' j) := by
  rw [ER, EdR_single _ (splitT_add _), splitT_eu, SR_spec]

/-- The splitting of `Space α` adapted to a block family of `U`. -/
def SL {k : ℕ} (z : Fin k → Space α) (ind : LinearIndependent F z) : Split α (Fin (Fintype.card α - k)) (Fin k) :=
  Classical.choose (exists_split z ind)

lemma SL_spec {k : ℕ} (z : Fin k → Space α) (ind : LinearIndependent F z) (i : Fin k) :
    (SL z ind).e.symm (0, eu i) = z i :=
  Classical.choose_spec (exists_split z ind) i

/-- The digit map of a block of `U`: digits = a basis of `Space α` starting with the block directions. -/
def EL {k : ℕ} (z : Fin k → Space α) (ind : LinearIndependent F z) :
    ((Fin k ⊕ Fin (Fintype.card α - k)) → Space β) ≃ Space (α × β) :=
  EdL β (splitT (SL z ind))

lemma EL_add {k : ℕ} (z : Fin k → Space α) (ind : LinearIndependent F z)
    (y y' : (Fin k ⊕ Fin (Fintype.card α - k)) → Space β) :
    EL (β := β) z ind (y + y') = EL z ind y + EL z ind y' :=
  EdL_add _ (splitT_add _) y y'

lemma EL_single {k : ℕ} (z : Fin k → Space α) (ind : LinearIndependent F z) (i : Fin k) (y : Space β) :
    EL z ind (Pi.single (Sum.inl i) y) = kron (z i) y := by
  rw [EL, EdL_single _ (splitT_add _), splitT_eu, SL_spec]

/-- **The Kronecker identity**: the invocation of `V` on a block `z` of `U` ends, on `V`'s live role `l'`, at the
same block as `z` lifted along `V`'s target `tz l'`. -/
lemma kron_swap (V : CU β ρ' σ') {k : ℕ} (z : Fin k → Space α) (ind : LinearIndependent F z) (l' : σ') :
    blockMat (liftFam (EL (β := β) z ind) (V.tz l')) = blockMat (liftFam (ER (α := α) V l') z) := by
  apply blockMat_congr
  intro x
  rw [bph_liftFam, bph_liftFam, Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro j _
  apply Finset.prod_congr rfl
  intro i _
  rw [EL_single, ER_single]

/-! #### the product word -/

/-- The lifted copies of a letter of `U`, one on the roles `(·, l')` for every live role `l'` of `V`. -/
def pieceL (V : CU β ρ' σ') (N : ℕ) (mv : GMove α ρ) : GWord (α × β) (RW ρ σ' ρ' N) :=
  ((Finset.univ : Finset σ').toList).flatMap fun l' =>
    (liftLab (ER (α := α) V l') (ER_add V l') mv).map (GMove.over (embL N l'))

/-- The invocation of `V` replacing a block of `U` (role `r`, directions `z`) at position `q`. -/
def pieceV (V : CU β ρ' σ') (N : ℕ) (q : Fin N) (r : ρ) {k : ℕ} (z : Fin k → Space α)
    (ind : LinearIndependent F z) : GWord (α × β) (RW ρ σ' ρ' N) :=
  (liftWord (EL (β := β) z ind) (EL_add z ind) V.wd).map (GMove.over (embV V N q r))

/-- The piece of the product word for the letter `mv` of `U` at position `q`. -/
def piece (V : CU β ρ' σ') (N : ℕ) (q : Fin N) : GMove α ρ → GWord (α × β) (RW ρ σ' ρ' N)
  | .old (.block r _ z ind) => pieceV V N q r z ind
  | mv => pieceL V N mv

/-- The product word along a list of (position, letter) pairs. -/
def wordL (V : CU β ρ' σ') (N : ℕ) (ps : List (Fin N × GMove α ρ)) : GWord (α × β) (RW ρ σ' ρ' N) :=
  ps.flatMap fun p => piece V N p.1 p.2

/-- The letters of a word with their positions. -/
def pairs (w : GWord α ρ) : List (Fin w.length × GMove α ρ) :=
  (List.finRange w.length).map fun q => (q, w.get q)

lemma pairs_fst (w : GWord α ρ) : (pairs w).map Prod.fst = List.finRange w.length := by
  simp [pairs, List.map_map, Function.comp_def]

lemma pairs_snd (w : GWord α ρ) : (pairs w).map Prod.snd = w := by
  simp only [pairs, List.map_map, Function.comp_def]
  exact List.map_get_finRange w

/-- **The tensor product of two certified words.** -/
def prodWord (U : CU α ρ σ) (V : CU β ρ' σ') : GWord (α × β) (RW ρ σ' ρ' U.wd.length) :=
  wordL V U.wd.length (pairs U.wd)

/-- The data of the copy `l'`, read through the digit map of `l'`. -/
def pullR (V : CU β ρ' σ') (N f : ℕ) (l' : σ') (X : Data (α × β) (RW ρ σ' ρ' N) f) :
    DataI α ρ ((Fin f × Fin (V.tr l')) ⊕ (Fin f × Fin (Fintype.card β - V.tr l'))) :=
  pull (ER V l') f (X ∘ embL N l')

/-! #### the invariant -/

lemma gwalk_flatMap_embL (N f : ℕ) (Ls : List σ') (hLs : Ls.Nodup) (g : σ' → GWord (α × β) ρ)
    (X : Data (α × β) (RW ρ σ' ρ' N) f) (l' : σ') :
    (gwalk f (Ls.flatMap fun l2 => (g l2).map (GMove.over (embL N l2))) X) ∘ embL N l'
      = if l' ∈ Ls then gwalk f (g l') (X ∘ embL N l') else X ∘ embL N l' := by
  induction Ls generalizing X with
  | nil => simp
  | cons l2 Ls ih =>
    rw [List.nodup_cons] at hLs
    rw [List.flatMap_cons, gwalk_append, ih hLs.2]
    have hstep : (gwalk f ((g l2).map (GMove.over (embL N l2))) X) ∘ embL N l'
        = if l' = l2 then gwalk f (g l2) (X ∘ embL N l2) else X ∘ embL N l' := by
      by_cases h : l' = l2
      · subst h
        rw [if_pos rfl]
        exact gwalk_over (embL N l') (g l') f X
      · rw [if_neg h]
        funext r
        exact gwalk_out (embL N l2) (g l2) f X (embL_out_inl N h r)
    rw [hstep]
    by_cases h : l' = l2
    · subst h
      simp [hLs.1]
    · simp [h]

lemma gwalk_pieceL_inr (V : CU β ρ' σ') (N f : ℕ) (mv : GMove α ρ) (X : Data (α × β) (RW ρ σ' ρ' N) f)
    (p : Fin N × ρ') : gwalk f (pieceL V N mv) X (Sum.inr p) = X (Sum.inr p) := by
  unfold pieceL
  generalize ((Finset.univ : Finset σ').toList) = Ls
  induction Ls generalizing X with
  | nil => rfl
  | cons l2 Ls ih =>
    rw [List.flatMap_cons, gwalk_append, ih]
    exact gwalk_out (embL N l2) _ f X (embL_out_inr N l2 p)

lemma pieceL_pull (V : CU β ρ' σ') (N f : ℕ) (mv : GMove α ρ) (X : Data (α × β) (RW ρ σ' ρ' N) f)
    (l' : σ') : pullR V N f l' (gwalk f (pieceL V N mv) X) = actI isL mv (pullR V N f l' X) := by
  unfold pullR pieceL
  rw [gwalk_flatMap_embL N f _ (Finset.nodup_toList _) _ X l',
    if_pos (Finset.mem_toList.2 (Finset.mem_univ l'))]
  exact pull_gwalk_liftLab (ER V l') (ER_add V l') f mv (X ∘ embL N l')

/-- Inside an invocation: `V`'s certificate, with spectators, through the lift. -/
lemma pieceV_live (V : CU β ρ' σ') (N f : ℕ) (q : Fin N) (r : ρ) {k : ℕ} (z : Fin k → Space α)
    (ind : LinearIndependent F z) (X : Data (α × β) (RW ρ σ' ρ' N) f) (hX : ∀ r', X (Sum.inr (q, r')) = 0)
    (l' : σ') :
    gwalk f (pieceV V N q r z ind) X (Sum.inl (r, l'))
      = matAct f (blockMat (liftFam (EL (β := β) z ind) (V.tz l'))) (X (Sum.inl (r, l'))) := by
  have hE := EL_add (β := β) z ind
  -- through the role embedding
  have h1 : gwalk f (pieceV V N q r z ind) X (Sum.inl (r, l'))
      = gwalk f (liftWord (EL (β := β) z ind) hE V.wd) (X ∘ embV V N q r) (V.e l') := by
    have h := congr_fun (gwalk_over (embV V N q r) (liftWord (EL (β := β) z ind) hE V.wd) f X) (V.e l')
    rw [Function.comp_apply] at h
    rw [← h]
    show _ = gwalk f _ X (embVf V N q r (V.e l'))
    rw [embVf_live]
    all_goals rfl
  rw [h1]
  -- `V`'s scratch roles are fresh
  have hY0 : ∀ r', (∀ l, V.e l ≠ r') → pull (EL (β := β) z ind) f (X ∘ embV V N q r) r' = 0 := by
    intro r' hr'
    have hn : V.liveOf r' = none := by
      cases h : V.liveOf r' with
      | none => rfl
      | some l => exact absurd (V.liveOf_some h) (hr' l)
    funext y
    show X (embVf V N q r r') _ = 0
    simp only [embVf_dead V N q r hn, hX, Pi.zero_apply]
  have h3 := certI V.hw (pull (EL (β := β) z ind) f (X ∘ embV V N q r)) hY0 l'
  rw [← pull_gwalk_liftWord (EL (β := β) z ind) hE f V.wd (X ∘ embV V N q r)] at h3
  have hYl : (X ∘ embV V N q r) (V.e l') = X (Sum.inl (r, l')) := by
    show X (embVf V N q r (V.e l')) = _
    rw [embVf_live]
  have h5 : pull (EL (β := β) z ind) f (X ∘ embV V N q r) (V.e l')
      = fun y => X (Sum.inl (r, l')) (PhiE (EL (β := β) z ind) f y) := by
    funext y
    show (X ∘ embV V N q r) (V.e l') _ = _
    rw [hYl]
  rw [h5] at h3
  apply push_eq (EL (β := β) z ind) f
  have h4 := pull_matAct (EL (β := β) z ind) f (blockMat (V.tz l')) (X (Sum.inl (r, l')))
  rw [trp_dopI_blockMat _ hE] at h4
  rw [h4]
  exact h3

lemma pieceV_pull (V : CU β ρ' σ') (N f : ℕ) (q : Fin N) (r : ρ) {k : ℕ} (z : Fin k → Space α)
    (ind : LinearIndependent F z) (X : Data (α × β) (RW ρ σ' ρ' N) f) (hX : ∀ r', X (Sum.inr (q, r')) = 0)
    (l' : σ') :
    pullR V N f l' (gwalk f (pieceV V N q r z ind) X)
      = actI isL (GMove.old (.block r k z ind)) (pullR V N f l' X) := by
  funext r2
  rw [actI_local _ (GMove.old (.block r k z ind)) trivial]
  simp only [rmat]
  by_cases h : r2 = r
  · subst h
    rw [if_pos rfl]
    show (fun y => gwalk f (pieceV V N q r2 z ind) X (Sum.inl (r2, l')) (PhiE (ER V l') f y)) = _
    rw [pieceV_live V N f q r2 z ind X hX l', kron_swap V z ind l',
      ← trp_dopI_blockMat (ER V l') (ER_add V l') z]
    exact pull_matAct (ER V l') f (blockMat z) (X (Sum.inl (r2, l')))
  · rw [if_neg h, dopI_one, one_mulVec]
    show (fun y => gwalk f ((liftWord (EL (β := β) z ind) (EL_add z ind) V.wd).map (GMove.over (embV V N q r))) X
      (Sum.inl (r2, l')) (PhiE (ER V l') f y)) = _
    rw [gwalk_out (embV V N q r) _ f X (embV_out_inl V N q h l')]
    all_goals rfl

lemma piece_pull (V : CU β ρ' σ') (N f : ℕ) (q : Fin N) (mv : GMove α ρ) (X : Data (α × β) (RW ρ σ' ρ' N) f)
    (hX : ∀ r', X (Sum.inr (q, r')) = 0) (l' : σ') :
    pullR V N f l' (gwalk f (piece V N q mv) X) = actI isL mv (pullR V N f l' X) := by
  cases mv with
  | old mv =>
    cases mv with
    | localM g => exact pieceL_pull V N f (.old (.localM g)) X l'
    | shift l z => exact pieceL_pull V N f (.old (.shift l z)) X l'
    | block r k z ind => exact pieceV_pull V N f q r z ind X hX l'
  | perm l G => exact pieceL_pull V N f (.perm l G) X l'
  | phase l z c => exact pieceL_pull V N f (.phase l z c) X l'

lemma piece_out (V : CU β ρ' σ') (N f : ℕ) {q q2 : Fin N} (h : q2 ≠ q) (mv : GMove α ρ)
    (X : Data (α × β) (RW ρ σ' ρ' N) f) (r' : ρ') :
    gwalk f (piece V N q mv) X (Sum.inr (q2, r')) = X (Sum.inr (q2, r')) := by
  cases mv with
  | old mv =>
    cases mv with
    | localM g => exact gwalk_pieceL_inr V N f (.old (.localM g)) X _
    | shift l z => exact gwalk_pieceL_inr V N f (.old (.shift l z)) X _
    | block r k z ind => exact gwalk_out (embV V N q r) _ f X (embV_out_inr V N h r r')
  | perm l G => exact gwalk_pieceL_inr V N f (.perm l G) X _
  | phase l z c => exact gwalk_pieceL_inr V N f (.phase l z c) X _

/-- **The invariant**: every copy `l'`, read through its digit map, runs `U`'s word with spectators. -/
theorem wordL_pull (V : CU β ρ' σ') (N f : ℕ) (l' : σ') (ps : List (Fin N × GMove α ρ))
    (hps : (ps.map Prod.fst).Nodup) (X : Data (α × β) (RW ρ σ' ρ' N) f)
    (hX : ∀ q ∈ ps.map Prod.fst, ∀ r', X (Sum.inr (q, r')) = 0) :
    pullR V N f l' (gwalk f (wordL V N ps) X) = gwalkI isL (ps.map Prod.snd) (pullR V N f l' X) := by
  induction ps generalizing X with
  | nil => rfl
  | cons p ps ih =>
    rw [List.map_cons, List.nodup_cons] at hps
    have hX1 : ∀ r', X (Sum.inr (p.1, r')) = 0 := hX p.1 (by simp)
    have hX2 : ∀ q ∈ ps.map Prod.fst, ∀ r', gwalk f (piece V N p.1 p.2) X (Sum.inr (q, r')) = 0 := by
      intro q hq r'
      have hne : q ≠ p.1 := fun h => hps.1 (h ▸ hq)
      rw [piece_out V N f hne p.2 X r']
      exact hX q (by simp [hq]) r'
    show pullR V N f l' (gwalk f (piece V N p.1 p.2 ++ wordL V N ps) X) = _
    rw [gwalk_append, ih hps.2 _ hX2, piece_pull V N f p.1 p.2 X hX1 l', List.map_cons, gwalkI_cons]

/-- The targets of the product: `tz l ⊗ tz' l'` (as the lift of `tz l` along the digit map of `l'`). -/
def tzP (U : CU α ρ σ) (V : CU β ρ' σ') (ll : σ × σ') :
    Fin (Fintype.card (Fin (V.tr ll.2)) * U.tr ll.1) → Space (α × β) :=
  liftFam (ER (α := α) V ll.2) (U.tz ll.1)

lemma tzP_ind (U : CU α ρ σ) (V : CU β ρ' σ') (ll : σ × σ') : LinearIndependent F (tzP U V ll) :=
  liftFam_ind _ (ER_add V ll.2) _ (U.tind ll.1)

/-- **T1: the tensor product of two certified words is a certified word.** -/
theorem prod_cert (U : CU α ρ σ) (V : CU β ρ' σ') :
    GLiveKernelM (fun ll : σ × σ' => (Sum.inl (U.e ll.1, ll.2) : RW ρ σ' ρ' U.wd.length))
      (fun ll => blockMat (tzP U V ll)) (prodWord U V) := by
  intro f X hX ll
  obtain ⟨l, l'⟩ := ll
  have hps : ((pairs U.wd).map Prod.fst).Nodup := by
    rw [pairs_fst]
    exact List.nodup_finRange _
  have hX0 : ∀ q ∈ (pairs U.wd).map Prod.fst, ∀ r', X (Sum.inr (q, r')) = 0 := by
    intro q _ r'
    apply hX
    intro ll h
    cases h
  have hinv := wordL_pull V U.wd.length f l' (pairs U.wd) hps X hX0
  rw [pairs_snd] at hinv
  -- `U`'s certificate with spectators
  have hU0 : ∀ r, (∀ l0, U.e l0 ≠ r) → pullR V U.wd.length f l' X r = 0 := by
    intro r hr
    have h0 : X (Sum.inl (r, l')) = 0 := by
      apply hX
      intro ll h
      simp only [Sum.inl.injEq, Prod.mk.injEq] at h
      exact hr ll.1 h.1
    funext y
    show X (Sum.inl (r, l')) _ = 0
    simp only [h0, Pi.zero_apply]
  have h3 := certI U.hw (pullR V U.wd.length f l' X) hU0 l
  rw [← hinv] at h3
  show gwalk f (prodWord U V) X (Sum.inl (U.e l, l'))
    = matAct f (blockMat (tzP U V (l, l'))) (X (Sum.inl (U.e l, l')))
  apply push_eq (ER (α := α) V l') f
  have h4 := pull_matAct (ER (α := α) V l') f (blockMat (U.tz l)) (X (Sum.inl (U.e l, l')))
  rw [trp_dopI_blockMat _ (ER_add V l')] at h4
  rw [show tzP U V (l, l') = liftFam (ER (α := α) V l') (U.tz l) from rfl, h4]
  exact h3

/-! #### paid ranks -/

lemma rk_over {γ ρ0 ρ1 : Type*} [Fintype γ] [DecidableEq γ] [Fintype ρ0] [DecidableEq ρ0] [Fintype ρ1]
    [DecidableEq ρ1] (e : ρ0 ↪ ρ1) (mv : GMove γ ρ0) : (mv.over e).rk? = mv.rk? := by
  cases mv with
  | old mv => cases mv <;> rfl
  | perm l G => rfl
  | phase l z c => rfl

lemma filterMap_rk_map_over {γ ρ0 ρ1 : Type*} [Fintype γ] [DecidableEq γ] [Fintype ρ0] [DecidableEq ρ0]
    [Fintype ρ1] [DecidableEq ρ1] (e : ρ0 ↪ ρ1) (w : GWord γ ρ0) :
    (w.map (GMove.over e)).filterMap GMove.rk? = w.filterMap GMove.rk? := by
  rw [List.filterMap_map]
  congr 1
  funext mv
  exact rk_over e mv

lemma rk_pieceL (V : CU β ρ' σ') (N : ℕ) (mv : GMove α ρ) (h : mv.rk? = none) :
    (pieceL V N mv).filterMap GMove.rk? = [] := by
  unfold pieceL
  generalize ((Finset.univ : Finset σ').toList) = Ls
  induction Ls with
  | nil => rfl
  | cons l2 Ls ih =>
    rw [List.flatMap_cons, List.filterMap_append, ih, filterMap_rk_map_over, rk_liftLab, h]
    all_goals rfl

lemma rk_pieceV (V : CU β ρ' σ') (N : ℕ) (q : Fin N) (r : ρ) {k : ℕ} (z : Fin k → Space α)
    (ind : LinearIndependent F z) :
    (pieceV V N q r z ind).filterMap GMove.rk? = (V.wd.filterMap GMove.rk?).map (k * ·) := by
  unfold pieceV
  rw [filterMap_rk_map_over, rk_liftWord, Fintype.card_fin]

lemma rk_piece (V : CU β ρ' σ') (N : ℕ) (q : Fin N) (mv : GMove α ρ) :
    (piece V N q mv).filterMap GMove.rk?
      = (mv.rk?.toList).flatMap fun k => (V.wd.filterMap GMove.rk?).map (k * ·) := by
  cases mv with
  | old mv =>
    cases mv with
    | localM g => exact rk_pieceL V N _ rfl
    | shift l z => exact rk_pieceL V N _ rfl
    | block r k z ind =>
      show (pieceV V N q r z ind).filterMap GMove.rk?
        = [k].flatMap fun k => (V.wd.filterMap GMove.rk?).map (k * ·)
      rw [rk_pieceV]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  | perm l G => exact rk_pieceL V N _ rfl
  | phase l z c => exact rk_pieceL V N _ rfl

theorem rk_wordL (V : CU β ρ' σ') (N : ℕ) (ps : List (Fin N × GMove α ρ)) :
    (wordL V N ps).filterMap GMove.rk?
      = ((ps.map Prod.snd).filterMap GMove.rk?).flatMap fun k => (V.wd.filterMap GMove.rk?).map (k * ·) := by
  unfold wordL
  rw [List.filterMap_flatMap]
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rw [List.flatMap_cons, ih, rk_piece, List.map_cons]
    cases h : p.2.rk? with
    | none => rw [List.filterMap_cons_none h]; all_goals rfl
    | some k =>
      rw [List.filterMap_cons_some h]
      simp only [Option.toList_some, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- **The paid ranks of the product are the products of the paid ranks.** -/
theorem rk_prodWord (U : CU α ρ σ) (V : CU β ρ' σ') :
    (prodWord U V).filterMap GMove.rk?
      = (U.wd.filterMap GMove.rk?).flatMap fun k => (V.wd.filterMap GMove.rk?).map (k * ·) := by
  rw [prodWord, rk_wordL, pairs_snd]

theorem prod_rk_mem (U : CU α ρ σ) (V : CU β ρ' σ') {m : ℕ} (h : m ∈ (prodWord U V).filterMap GMove.rk?) :
    ∃ k ∈ U.wd.filterMap GMove.rk?, ∃ k' ∈ V.wd.filterMap GMove.rk?, m = k * k' := by
  rw [rk_prodWord, List.mem_flatMap] at h
  obtain ⟨k, hk, hm⟩ := h
  rw [List.mem_map] at hm
  obtain ⟨k', hk', rfl⟩ := hm
  exact ⟨k, hk, k', hk', rfl⟩

end Product

end

end TensorEng
