import Submission.Work.TensorEng.DigitSem

/-!
# T1, part 4: lifting a word to a product label space

Fix an additive bijection `E : ((A ⊕ S) → Space γ) ≃ Space δ` (a digit map: `A` = active digits, `S` = spectator
digits).  Every letter of a word on labels `γ` is lifted to letters on labels `δ` (`liftLab`), so that the lifted
word, read through the column-count digit map `PhiE E f`, is the original word with spectators (`gwalkI isL`):

  `pull_gwalk_liftWord : pull E f (gwalk f (liftWord E hE w) x) = gwalkI isL w (pull E f x)`.

A block of rank `rk` lifts to ONE block of rank `|A| * rk` along the vectors `E (single (inl a) (z i))`
(`trp_dopI_blockMat`, `liftFam`, `liftFam_ind`); shifts and address permutations lift to one letter, a phase to
`|A|` phases, `localM` to itself.  The paid ranks of the lifted word are those of the word times `|A|`
(`rk_liftWord`).

-- changed for the tensor-power extension (30103/10000000); see Submission.lean
-/

namespace TensorEng
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.GF OAI.PowerSaving.MX Matrix Finset

noncomputable section

section Transport
variable {γ δ ρ : Type*} [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ] [Fintype ρ] [DecidableEq ρ]
variable {A S : Type*} [Fintype A] [DecidableEq A] [Fintype S] [DecidableEq S]

/-! ### the column-count digit map -/

/-- `(Fin f × A) ⊕ (Fin f × S)` digits regrouped column by column. -/
def colDist (f : ℕ) : ((Fin f × A) ⊕ (Fin f × S) → Space γ) ≃ (Fin f → (A ⊕ S) → Space γ) where
  toFun y k d := Sum.elim (fun a => y (Sum.inl (k, a))) (fun s => y (Sum.inr (k, s))) d
  invFun u d' := Sum.elim (fun p => u p.1 (Sum.inl p.2)) (fun p => u p.1 (Sum.inr p.2)) d'
  left_inv y := by
    funext d'
    cases d' <;> rfl
  right_inv u := by
    funext k d
    cases d <;> rfl

lemma colDist_symm_inl (f : ℕ) (u : Fin f → (A ⊕ S) → Space γ) (p : Fin f × A) :
    (colDist f).symm u (Sum.inl p) = u p.1 (Sum.inl p.2) := rfl

lemma colDist_symm_inr (f : ℕ) (u : Fin f → (A ⊕ S) → Space γ) (p : Fin f × S) :
    (colDist f).symm u (Sum.inr p) = u p.1 (Sum.inr p.2) := rfl

/-- The digit map at column count `f`. -/
def PhiE (E : ((A ⊕ S) → Space γ) ≃ Space δ) (f : ℕ) :
    ((Fin f × A) ⊕ (Fin f × S) → Space γ) ≃ (Fin f → Space δ) :=
  (colDist f).trans (Equiv.piCongrRight fun _ => E)

/-- Data pulled back along the digit map. -/
def pull (E : ((A ⊕ S) → Space γ) ≃ Space δ) (f : ℕ) (x : Data δ ρ f) :
    DataI γ ρ ((Fin f × A) ⊕ (Fin f × S)) :=
  fun r y => x r (PhiE E f y)

lemma trp_trans {X Y Z : Type*} (e : X ≃ Y) (e' : Y ≃ Z) (M : Matrix X X ℂ) :
    trp e' (trp e M) = trp (e.trans e') M := rfl

/-- One column of `dopI isL M`, repeated over `f` columns, is `dopI isL M` on the regrouped digits. -/
lemma digitProd_col (f : ℕ) (M : CMat γ) :
    digitProd (fun _ : Fin f => dopI (isL (A := A) (S := S)) M) = trp (colDist f) (dopI isL M) := by
  ext u u'
  rw [trp_apply]
  simp only [digitProd_apply, dopI, Fintype.prod_sum_type, ite_isL_inl, ite_isL_inr, colDist_symm_inl,
    colDist_symm_inr]
  rw [Finset.prod_mul_distrib, Fintype.prod_prod_type, Fintype.prod_prod_type]

/-- **The transport identity at column count `f`.** -/
lemma matAct_trp (E : ((A ⊕ S) → Space γ) ≃ Space δ) (f : ℕ) (M : CMat γ) (v : Sky δ f → ℂ) :
    matAct f (trp E (dopI isL M)) v = trp (PhiE E f) (dopI isL M) *ᵥ v := by
  unfold matAct
  rw [digitProd_trp, digitProd_col, trp_trans]
  all_goals rfl

lemma pull_matAct (E : ((A ⊕ S) → Space γ) ≃ Space δ) (f : ℕ) (M : CMat γ) (v : Sky δ f → ℂ) :
    (fun y => matAct f (trp E (dopI isL M)) v (PhiE E f y)) = dopI isL M *ᵥ (fun y => v (PhiE E f y)) := by
  funext y
  rw [matAct_trp, trp_mulVec]
  simp only [Function.comp_apply, Equiv.symm_apply_apply]
  rfl

/-- Functions agreeing after the digit map agree. -/
lemma push_eq (E : ((A ⊕ S) → Space γ) ≃ Space δ) (f : ℕ) {u v : Sky δ f → ℂ}
    (h : (fun y => u (PhiE E f y)) = (fun y => v (PhiE E f y))) : u = v := by
  funext s
  have h1 := congr_fun h ((PhiE E f).symm s)
  simp only [Equiv.apply_symm_apply] at h1
  exact h1

lemma dopI_one {I : Type*} [Fintype I] [DecidableEq I] (P : I → Prop) [DecidablePred P] :
    dopI P (1 : CMat γ) = 1 := by
  unfold dopI
  simp only [ite_self]
  exact digitProd_one

/-! ### the active digits as a finset (to reuse `trp_dop_*`) -/

/-- The active digits of `A ⊕ S`. -/
def Lset : Finset (A ⊕ S) := Finset.univ.filter (fun d => d.isLeft = true)

lemma dopI_eq_dop (M : CMat γ) : dopI (isL (A := A) (S := S)) M = dop Lset M := by
  unfold dopI dop
  congr 1
  funext d
  cases d with
  | inl a => rw [ite_isL_inl, if_pos (by simp [Lset])]
  | inr s => rw [ite_isL_inr, if_neg (by simp [Lset])]

lemma Lset_eq : (Lset : Finset (A ⊕ S)) = (((Finset.univ : Finset A).toList).map Sum.inl).toFinset := by
  ext d
  cases d with
  | inl a => simp [Lset]
  | inr s => simp [Lset]

lemma nodup_inl_list : ((((Finset.univ : Finset A).toList).map (Sum.inl : A → A ⊕ S))).Nodup :=
  (Finset.nodup_toList _).map Sum.inl_injective

lemma dopI_list_prod (Ms : List (CMat γ)) :
    dopI (isL (A := A) (S := S)) Ms.prod = (Ms.map (dopI isL)).prod := by
  have h : (dopI (isL (A := A) (S := S)) : CMat γ → _) = dop Lset := funext dopI_eq_dop
  rw [h, dop_list_prod]

lemma trp_dopI_ite (E : ((A ⊕ S) → Space γ) ≃ Space δ) {j l : ρ} (M : CMat γ) :
    trp E (dopI isL (if j = l then M else 1)) = if j = l then trp E (dopI isL M) else 1 := by
  split_ifs
  · rfl
  · rw [dopI_one, trp_one]

/-! ### shifts -/

lemma trp_shift (E : ((A ⊕ S) → Space γ) ≃ Space δ) (hE : ∀ y y', E (y + y') = E y + E y') (z : Space γ) :
    trp E (dopI isL (Binary.shift z)) = Binary.shift (E (fun d => if d.isLeft then z else 0)) := by
  rw [dopI_eq_dop, trp_dop_shift E hE]
  congr 2
  funext d
  simp [Lset]

/-! ### blocks -/

lemma trp_dop_dir_list {D : Type*} [Fintype D] [DecidableEq D] (E : (D → Space γ) ≃ Space δ)
    (hE : ∀ y y', E (y + y') = E y + E y') (Dl : List D) (hDl : Dl.Nodup) (y : Space γ) :
    trp E (dop Dl.toFinset (dir y)) = (Dl.map fun d => dir (E (Pi.single d y))).prod := by
  induction Dl with
  | nil =>
    simp only [List.toFinset_nil, List.map_nil, List.prod_nil]
    have h0 : dop (∅ : Finset D) (dir y) = 1 := by
      unfold dop
      simp only [Finset.notMem_empty, if_false]
      exact digitProd_one
    rw [h0, trp_one]
  | cons d Dl ih =>
    rw [List.nodup_cons] at hDl
    have hd : d ∉ Dl.toFinset := by simpa using hDl.1
    rw [List.toFinset_cons, dop_insert hd, trp_mul, ih hDl.2, trp_dop_dir_single E hE, List.map_cons,
      List.prod_cons]

lemma trp_dopI_dir (E : ((A ⊕ S) → Space γ) ≃ Space δ) (hE : ∀ y y', E (y + y') = E y + E y')
    (y : Space γ) :
    trp E (dopI isL (dir y))
      = (((Finset.univ : Finset A).toList).map fun a => dir (E (Pi.single (Sum.inl a) y))).prod := by
  rw [dopI_eq_dop, Lset_eq, trp_dop_dir_list E hE _ nodup_inl_list, List.map_map]
  all_goals rfl

/-- A block on the active digits is the product of the directional factors of the lifted directions. -/
lemma trp_dopI_blockMat_list (E : ((A ⊕ S) → Space γ) ≃ Space δ) (hE : ∀ y y', E (y + y') = E y + E y')
    {r : ℕ} (z : Fin r → Space γ) :
    trp E (dopI isL (blockMat z))
      = ((List.ofFn z).map fun y =>
          (((Finset.univ : Finset A).toList).map fun a => dir (E (Pi.single (Sum.inl a) y))).prod).prod := by
  rw [blockMat_eq_dirs, dopI_list_prod, trp_list_prod, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro y _
  exact trp_dopI_dir E hE y

/-- The enumeration of the active digits. -/
def eA (A : Type*) [Fintype A] : Fin (Fintype.card A) ≃ A := (Fintype.equivFin A).symm

/-- **The lifted block family**: `E (single (inl a) (z i))`, indexed by `Fin (card A * r)`. -/
def liftFam (E : ((A ⊕ S) → Space γ) ≃ Space δ) {r : ℕ} (z : Fin r → Space γ) :
    Fin (Fintype.card A * r) → Space δ :=
  fun i => E (Pi.single (Sum.inl (eA A (finProdFinEquiv.symm i).1)) (z (finProdFinEquiv.symm i).2))

lemma prod_liftFam (E : ((A ⊕ S) → Space γ) ≃ Space δ) {r : ℕ} (z : Fin r → Space γ) (g : Space δ → ℂ) :
    ∏ i, g (liftFam E z i) = ∏ a : A, ∏ j : Fin r, g (E (Pi.single (Sum.inl a) (z j))) := by
  rw [← Equiv.prod_comp finProdFinEquiv, Fintype.prod_prod_type]
  simp only [liftFam, Equiv.symm_apply_apply]
  exact Fintype.prod_equiv (eA A) _ _ (fun _ => rfl)

lemma bph_liftFam (E : ((A ⊕ S) → Space γ) ≃ Space δ) {r : ℕ} (z : Fin r → Space γ) (x : Space δ) :
    bph (liftFam E z) x = ∏ a : A, ∏ j : Fin r, tint (dot (E (Pi.single (Sum.inl a) (z j))) x) :=
  prod_liftFam E z (fun v => tint (dot v x))

/-- **A block on the active digits transports to ONE block**, of rank `|A| * r`. -/
theorem trp_dopI_blockMat (E : ((A ⊕ S) → Space γ) ≃ Space δ) (hE : ∀ y y', E (y + y') = E y + E y')
    {r : ℕ} (z : Fin r → Space γ) :
    trp E (dopI isL (blockMat z)) = blockMat (liftFam E z) := by
  rw [trp_dopI_blockMat_list E hE z, blockMat_eq_wrap]
  -- every factor is a `wrap`
  have hw : ∀ y : Space γ, (((Finset.univ : Finset A).toList).map fun a => dir (E (Pi.single (Sum.inl a) y))).prod
      = wrap (fun x => ∏ a : A, tint (dot (E (Pi.single (Sum.inl a) y)) x)) := by
    intro y
    have h1 : (((Finset.univ : Finset A).toList).map fun a => dir (E (Pi.single (Sum.inl a) y)))
        = ((((Finset.univ : Finset A).toList).map fun a => E (Pi.single (Sum.inl a) y))).map dir := by
      rw [List.map_map]; all_goals rfl
    rw [h1, prod_dir_wrap]
    congr 1
    funext x
    rw [List.map_map]
    exact Finset.prod_map_toList _ _
  have hlist : ((List.ofFn z).map fun y =>
        (((Finset.univ : Finset A).toList).map fun a => dir (E (Pi.single (Sum.inl a) y))).prod)
      = (List.ofFn z).map fun y => wrap (fun x => ∏ a : A, tint (dot (E (Pi.single (Sum.inl a) y)) x)) :=
    List.map_congr_left (fun y _ => hw y)
  rw [hlist]
  -- a product of wraps is the wrap of the product
  have hprod : ∀ L : List (Space γ), (L.map fun y => wrap (fun x => ∏ a : A,
      tint (dot (E (Pi.single (Sum.inl a) y)) x))).prod
      = wrap (fun x => (L.map fun y => ∏ a : A, tint (dot (E (Pi.single (Sum.inl a) y)) x)).prod) := by
    intro L
    induction L with
    | nil => simp [wrap_one]
    | cons y L ih => rw [List.map_cons, List.prod_cons, ih, wrap_mul]; all_goals rfl
  rw [hprod]
  congr 1
  funext x
  rw [bph_liftFam, List.map_ofFn, List.prod_ofFn, Finset.prod_comm]
  all_goals rfl

/-- The lifted family is linearly independent. -/
theorem liftFam_ind (E : ((A ⊕ S) → Space γ) ≃ Space δ) (hE : ∀ y y', E (y + y') = E y + E y') {r : ℕ}
    (z : Fin r → Space γ) (hz : LinearIndependent F z) : LinearIndependent F (liftFam E z) := by
  -- the family of `single (inl a) (z j)` is independent
  have h1 : LinearIndependent F
      (fun p : A × Fin r => (Pi.single (Sum.inl p.1) (z p.2) : (A ⊕ S) → Space γ)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc p
    have h2 := congr_fun hc (Sum.inl p.1)
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] at h2
    rw [Fintype.sum_prod_type, Finset.sum_eq_single p.1] at h2
    · simp only [Pi.single_eq_same] at h2
      exact Fintype.linearIndependent_iff.1 hz (fun j => c (p.1, j)) h2 p.2
    · intro a _ ha
      apply Finset.sum_eq_zero
      intro j _
      have hne : (Sum.inl p.1 : A ⊕ S) ≠ Sum.inl a := fun h => ha (Sum.inl_injective h).symm
      rw [Pi.single_eq_of_ne hne, smul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  -- `E` is an injective `F`-linear map
  let Φ : ((A ⊕ S) → Space γ) →ₗ[F] Space δ := (AddMonoidHom.mk' E hE).toZModLinearMap 2
  have hΦ : LinearMap.ker Φ = ⊥ := LinearMap.ker_eq_bot.mpr E.injective
  let ι : Fin (Fintype.card A * r) ≃ A × Fin r :=
    finProdFinEquiv.symm.trans (Equiv.prodCongr (eA A) (Equiv.refl _))
  have h4 := (h1.map' Φ hΦ).comp ι ι.injective
  have h5 : liftFam E z
      = (Φ ∘ fun p : A × Fin r => (Pi.single (Sum.inl p.1) (z p.2) : (A ⊕ S) → Space γ)) ∘ ι := by
    funext i
    rfl
  rw [h5]
  exact h4

/-! ### address permutations -/

/-- `G` on the active digits, the identity on the spectators. -/
def applyL (G : APerm γ) : ((A ⊕ S) → Space γ) ≃ ((A ⊕ S) → Space γ) :=
  Equiv.piCongrRight (fun d => if d.isLeft then G.π else Equiv.refl (Space γ))

lemma applyL_apply (G : APerm γ) (y : (A ⊕ S) → Space γ) (d : A ⊕ S) :
    applyL G y d = if d.isLeft then G.π (y d) else y d := by
  show (if d.isLeft then G.π else Equiv.refl (Space γ)) (y d) = _
  split_ifs <;> rfl

/-- The lifted address permutation. -/
def liftAPerm (E : ((A ⊕ S) → Space γ) ≃ Space δ) (hE : ∀ y y', E (y + y') = E y + E y') (G : APerm γ) :
    APerm δ where
  π := (E.symm.trans (applyL G)).trans E
  add := by
    intro x y
    simp only [Equiv.trans_apply]
    have hs : E.symm (x + y) = E.symm x + E.symm y := by
      apply E.injective
      rw [hE, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    have ha : applyL G (E.symm x + E.symm y) = applyL G (E.symm x) + applyL G (E.symm y) := by
      funext d
      simp only [applyL_apply, Pi.add_apply]
      split_ifs
      · exact G.add _ _
      · rfl
    rw [hs, ha, hE]

lemma trp_perm (E : ((A ⊕ S) → Space γ) ≃ Space δ) (hE : ∀ y y', E (y + y') = E y + E y') (G : APerm γ) :
    trp E (dopI isL (permMat G)) = permMat (liftAPerm E hE G) := by
  ext x y
  rw [trp_apply]
  simp only [dopI, digitProd_apply]
  have h1 : ∀ d, (if isL d then permMat G else (1 : CMat γ)) (E.symm x d) (E.symm y d)
      = if applyL G (E.symm x) d = E.symm y d then (1:ℂ) else 0 := by
    intro d
    rw [applyL_apply]
    cases d with
    | inl a =>
      rw [ite_isL_inl]
      simp [permMat]
    | inr s =>
      rw [ite_isL_inr]
      simp [Matrix.one_apply]
  rw [Finset.prod_congr rfl (fun d _ => h1 d), OAI.PowerSaving.prod_delta]
  have h2 : (applyL G (E.symm x) = E.symm y) ↔ (E (applyL G (E.symm x)) = y) := by
    constructor
    · intro h; rw [h, Equiv.apply_symm_apply]
    · intro h; rw [← h, Equiv.symm_apply_apply]
  show _ = (if E (applyL G (E.symm x)) = y then (1:ℂ) else 0)
  by_cases h : E (applyL G (E.symm x)) = y
  · rw [if_pos (h2.2 h), if_pos h]
  · rw [if_neg (fun h' => h (h2.1 h')), if_neg h]

/-! ### phases -/

/-- The vector representing the functional `x ↦ dot z ((E.symm x) (inl a))`. -/
def zrep (E : ((A ⊕ S) → Space γ) ≃ Space δ) (z : Space γ) (a : A) : Space δ :=
  fun p => dot z (E.symm (eu p) (Sum.inl a))

lemma eu_sum (x : Space δ) : x = ∑ p, x p • (eu p : Space δ) := by
  funext q
  simp [eu, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- `E.symm` is additive, hence `F`-linear. -/
lemma symm_lin (E : ((A ⊕ S) → Space γ) ≃ Space δ) (hE : ∀ y y', E (y + y') = E y + E y') (x : Space δ) :
    E.symm x = ∑ p, x p • E.symm (eu p) := by
  let φ : Space δ →+ ((A ⊕ S) → Space γ) := AddMonoidHom.mk' E.symm (fun u v => by
      apply E.injective
      rw [hE, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply])
  have h := map_sum (φ.toZModLinearMap 2) (fun p => x p • (eu p : Space δ)) Finset.univ
  simp only [map_smul] at h
  rw [← eu_sum x] at h
  exact h

lemma dot_zrep (E : ((A ⊕ S) → Space γ) ≃ Space δ) (hE : ∀ y y', E (y + y') = E y + E y')
    (z : Space γ) (a : A) (x : Space δ) :
    dot (zrep E z a) x = dot z (E.symm x (Sum.inl a)) := by
  rw [symm_lin E hE x, Finset.sum_apply, dot_sum]
  show ∑ p, zrep E z a p * x p = _
  apply Finset.sum_congr rfl
  intro p _
  rw [Pi.smul_apply, dot_smul_right]
  simp only [zrep]
  ring

lemma trp_phase (E : ((A ⊕ S) → Space γ) ≃ Space δ) (hE : ∀ y y', E (y + y') = E y + E y') (z : Space γ)
    (c : F) :
    trp E (dopI isL (phaseMat z c)) = Matrix.diagonal (fun x => ∏ a : A, tint (dot (zrep E z a) x + c)) := by
  ext x y
  rw [trp_apply]
  simp only [dopI, digitProd_apply, phaseMat, Matrix.diagonal_apply, Fintype.prod_sum_type, ite_isL_inl,
    ite_isL_inr, Matrix.one_apply]
  by_cases hxy : x = y
  · subst hxy
    simp only [eq_self_iff_true, ↓reduceIte, Finset.prod_const_one, mul_one]
    apply Finset.prod_congr rfl
    intro a _
    rw [dot_zrep E hE]
  · rw [if_neg hxy]
    have hne : E.symm x ≠ E.symm y := fun h => hxy (E.symm.injective h)
    obtain ⟨d, hd⟩ := Function.ne_iff.1 hne
    cases d with
    | inl a =>
      rw [Finset.prod_eq_zero (Finset.mem_univ a) (by rw [if_neg hd]), zero_mul]
    | inr s =>
      rw [Finset.prod_eq_zero (Finset.mem_univ s) (by rw [if_neg hd]), mul_zero]

/-- The role product of a list of phases on one role. -/
lemma roleProd_phases (l : ρ) (c : F) (La : List A) (zz : A → Space δ) (j : ρ) :
    roleProd (La.map fun a => (GMove.phase l (zz a) c : GMove δ ρ)) j
      = if j = l then Matrix.diagonal (fun x => (La.map fun a => tint (dot (zz a) x + c)).prod) else 1 := by
  induction La with
  | nil => by_cases hj : j = l <;> simp [hj]
  | cons a La ih =>
    rw [List.map_cons, roleProd_cons, ih]
    by_cases hj : j = l
    · simp only [hj, if_true, rmat, phaseMat, diagonal_mul_diagonal, List.map_cons, List.prod_cons]
      congr 1
      funext x
      ring
    · simp only [hj, if_false, rmat, mul_one]

/-! ### the lift of a letter and of a word -/

/-- **The lift of one letter.** -/
def liftLab (E : ((A ⊕ S) → Space γ) ≃ Space δ) (hE : ∀ y y', E (y + y') = E y + E y') :
    GMove γ ρ → GWord δ ρ
  | .old (.localM g) => [.old (.localM g)]
  | .old (.shift l z) => [.old (.shift l (E (fun d => if d.isLeft then z else 0)))]
  | .old (.block l rk z ind) =>
      [.old (.block l (Fintype.card A * rk) (liftFam E z) (liftFam_ind E hE z ind))]
  | .perm l G => [.perm l (liftAPerm E hE G)]
  | .phase l z c => ((Finset.univ : Finset A).toList).map fun a => .phase l (zrep E z a) c

lemma liftLab_local (E : ((A ⊕ S) → Space γ) ≃ Space δ) (hE : ∀ y y', E (y + y') = E y + E y')
    (mv : GMove γ ρ) (h : IsLocal mv) : RoleLocal (liftLab E hE mv) := by
  intro m hm
  cases mv with
  | old mv =>
    cases mv with
    | localM g => exact h.elim
    | shift l z =>
      simp only [liftLab, List.mem_singleton] at hm
      subst hm; trivial
    | block l rk z ind =>
      simp only [liftLab, List.mem_singleton] at hm
      subst hm; trivial
  | perm l G =>
    simp only [liftLab, List.mem_singleton] at hm
    subst hm; trivial
  | phase l z c =>
    simp only [liftLab, List.mem_map] at hm
    obtain ⟨a, _, rfl⟩ := hm
    trivial

lemma roleProd_liftLab (E : ((A ⊕ S) → Space γ) ≃ Space δ) (hE : ∀ y y', E (y + y') = E y + E y')
    (mv : GMove γ ρ) (h : IsLocal mv) (j : ρ) :
    roleProd (liftLab E hE mv) j = trp E (dopI isL (rmat mv j)) := by
  cases mv with
  | old mv =>
    cases mv with
    | localM g => exact h.elim
    | shift l z =>
      show roleProd [] j * rmat _ j = _
      rw [roleProd_nil, one_mul]
      simp only [rmat]
      rw [trp_dopI_ite, trp_shift E hE]
    | block l rk z ind =>
      show roleProd [] j * rmat _ j = _
      rw [roleProd_nil, one_mul]
      simp only [rmat]
      rw [trp_dopI_ite, trp_dopI_blockMat E hE]
  | perm l G =>
    show roleProd [] j * rmat _ j = _
    rw [roleProd_nil, one_mul]
    simp only [rmat]
    rw [trp_dopI_ite, trp_perm E hE]
  | phase l z c =>
    show roleProd (((Finset.univ : Finset A).toList).map fun a => GMove.phase l (zrep E z a) c) j = _
    rw [roleProd_phases]
    simp only [rmat]
    rw [trp_dopI_ite, trp_phase E hE]
    congr 2
    funext x
    exact Finset.prod_map_toList _ _

/-- **One lifted letter is the letter with spectators.** -/
theorem pull_gwalk_liftLab (E : ((A ⊕ S) → Space γ) ≃ Space δ) (hE : ∀ y y', E (y + y') = E y + E y')
    (f : ℕ) (mv : GMove γ ρ) (x : Data δ ρ f) :
    pull E f (gwalk f (liftLab E hE mv) x) = actI isL mv (pull E f x) := by
  by_cases h : IsLocal mv
  · funext r
    rw [actI_local _ mv h]
    show (fun y => gwalk f (liftLab E hE mv) x r (PhiE E f y)) = _
    rw [gwalk_local f _ (liftLab_local E hE mv h) x r, roleProd_liftLab E hE mv h r]
    exact pull_matAct E f (rmat mv r) (x r)
  · cases mv with
    | old mv =>
      cases mv with
      | localM g => funext r y; rfl
      | shift l z => exact absurd trivial h
      | block l rk z ind => exact absurd trivial h
    | perm l G => exact absurd trivial h
    | phase l z c => exact absurd trivial h

/-- The lift of a word. -/
def liftWord (E : ((A ⊕ S) → Space γ) ≃ Space δ) (hE : ∀ y y', E (y + y') = E y + E y')
    (w : GWord γ ρ) : GWord δ ρ :=
  w.flatMap (liftLab E hE)

/-- **The lifted word is the word with spectators.** -/
theorem pull_gwalk_liftWord (E : ((A ⊕ S) → Space γ) ≃ Space δ) (hE : ∀ y y', E (y + y') = E y + E y')
    (f : ℕ) (w : GWord γ ρ) (x : Data δ ρ f) :
    pull E f (gwalk f (liftWord E hE w) x) = gwalkI isL w (pull E f x) := by
  induction w generalizing x with
  | nil => rfl
  | cons mv w ih =>
    rw [liftWord, List.flatMap_cons, gwalk_append, gwalkI_cons, ← pull_gwalk_liftLab E hE f mv x]
    exact ih _

/-! ### paid ranks -/

lemma filterMap_rk_phases (l : ρ) (c : F) (La : List A) (zz : A → Space δ) :
    (La.map fun a => (GMove.phase l (zz a) c : GMove δ ρ)).filterMap GMove.rk? = [] := by
  induction La with
  | nil => rfl
  | cons a La ih => exact ih

lemma rk_liftLab (E : ((A ⊕ S) → Space γ) ≃ Space δ) (hE : ∀ y y', E (y + y') = E y + E y')
    (mv : GMove γ ρ) :
    (liftLab E hE mv).filterMap GMove.rk? = (mv.rk?.map (Fintype.card A * ·)).toList := by
  cases mv with
  | old mv =>
    cases mv with
    | localM g => rfl
    | shift l z => rfl
    | block l rk z ind => rfl
  | perm l G => rfl
  | phase l z c => exact filterMap_rk_phases l c _ _

/-- **The paid ranks of a lifted word are the paid ranks times `|A|`.** -/
theorem rk_liftWord (E : ((A ⊕ S) → Space γ) ≃ Space δ) (hE : ∀ y y', E (y + y') = E y + E y')
    (w : GWord γ ρ) :
    (liftWord E hE w).filterMap GMove.rk? = (w.filterMap GMove.rk?).map (Fintype.card A * ·) := by
  induction w with
  | nil => rfl
  | cons mv w ih =>
    simp only [liftWord] at ih ⊢
    rw [List.flatMap_cons, List.filterMap_append, ih, rk_liftLab]
    cases h : mv.rk? with
    | none => rw [List.filterMap_cons_none h]; all_goals rfl
    | some k => rw [List.filterMap_cons_some h]; all_goals rfl

end Transport

end

end TensorEng
