import Submission.Work.TensorEng.Power

/-!
# O4: splitting the paid blocks and completing the targets of a certified unit

* `splitBlk J l rk z ind` : a block of rank `rk > J` becomes blocks of `J` directions and a last block of at most
  `J` (`gwalk_splitBlk`: same action); `splitW J w` splits every block of a word (`GLiveKernelM.splitW`:
  certificates are kept); its paid ranks are `splitAll J` of the paid ranks (`ranks_splitW`).
* `CU.pad L` : every live role with target rank `K < L` gets ONE extra block of `L - K` directions extending its
  target family (`padExt`), appended at the end of the word; the new targets are the extended families of rank
  `max K L` (`CU.pad`, certificate by `GLiveKernelM.append_local`).  The extra paid ranks are `comp L`.

`BU.strict J L A = split J (pad L A)` has paid ranks `splitAll J (ranks + comp L tgts)` and targets `padT L tgts`:
for `A.pow n` these are `strictP` and `strictT` of `TensorProto.Strictify` (`ranks_strict_pow`, `tgts_strict_pow`).

-- changed for the tensor-power extension (30103/10000000); see Submission.lean
-/

namespace TensorEng
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.GF OAI.PowerSaving.MX Matrix Finset
open TensorProto (tens tpow pieces splitAll padT comp strictT strictP)

noncomputable section

section Split
variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

/-- The phase of a block splits after its first `J` directions. -/
lemma bph_split {rk J : ℕ} (h : J ≤ rk) (z : Fin rk → Space α) (x : Space α) :
    bph z x = bph (fun i : Fin J => z (Fin.castLE h i)) x
      * bph (fun j : Fin (rk - J) => z ⟨J + j.1, by have := j.2; omega⟩) x := by
  unfold bph
  have e : J + (rk - J) = rk := by omega
  rw [← Fintype.prod_equiv (finCongr e) (fun i => tint (dot (z (Fin.cast e i)) x))
    (fun i => tint (dot (z i) x)) (fun i => rfl), Fin.prod_univ_add]
  rfl

/-- A block split into blocks of `J` directions and a last block of at most `J` directions. -/
def splitBlk (J : ℕ) (l : ρ) (rk : ℕ) (z : Fin rk → Space α) (ind : LinearIndependent F z) : GWord α ρ :=
  if h : 0 < J ∧ J < rk then
    GMove.old (.block l J (fun i => z (Fin.castLE h.2.le i)) (ind.comp _ (Fin.castLE_injective h.2.le))) ::
      splitBlk J l (rk - J) (fun j => z ⟨J + j.1, by have := j.2; omega⟩)
        (ind.comp (fun j : Fin (rk - J) => (⟨J + j.1, by have := j.2; omega⟩ : Fin rk))
          (fun a b hab => Fin.ext (by simp only [Fin.mk.injEq] at hab; omega)))
  else [GMove.old (.block l rk z ind)]
termination_by rk
decreasing_by omega

lemma gwalk_splitBlk (J : ℕ) (l : ρ) (f : ℕ) (rk : ℕ) :
    ∀ (z : Fin rk → Space α) (ind : LinearIndependent F z) (x : Data α ρ f),
      gwalk f (splitBlk J l rk z ind) x = roleAct f l (blockMat z) x := by
  induction rk using Nat.strong_induction_on with
  | _ rk ih =>
    intro z ind x
    rw [splitBlk]
    split_ifs with h
    · rw [gwalk_cons, ih (rk - J) (by omega)]
      change roleAct f l (blockMat _) (roleAct f l (blockMat _) x) = _
      rw [roleAct_mul]
      congr 1
      rw [blockMat_eq_wrap, blockMat_eq_wrap, blockMat_eq_wrap, wrap_mul]
      congr 1
      funext y
      rw [bph_split h.2.le z y, mul_comm]
    · rfl

/-- The pieces of a rank: `J, …, J` and a last piece of at most `J`. -/
def piecesL (J : ℕ) (rk : ℕ) : List ℕ :=
  if h : 0 < J ∧ J < rk then J :: piecesL J (rk - J) else [rk]
termination_by rk
decreasing_by omega

lemma rk_splitBlk (J : ℕ) (l : ρ) (rk : ℕ) :
    ∀ (z : Fin rk → Space α) (ind : LinearIndependent F z),
      (splitBlk J l rk z ind).filterMap GMove.rk? = piecesL J rk := by
  induction rk using Nat.strong_induction_on with
  | _ rk ih =>
    intro z ind
    rw [splitBlk, piecesL]
    split_ifs with h
    · exact congrArg (J :: ·) (ih (rk - J) (by omega) _ _)
    · rfl

/-- The pieces as a multiset are `TensorProto.pieces`. -/
lemma pieces_eq_rep {J S : ℕ} (hJ : 0 < J) (hS : 0 < S) :
    pieces J S = Multiset.replicate (S / J) J + (if S % J = 0 then 0 else {S % J}) := by
  unfold pieces
  by_cases h1 : S ≤ J
  · rw [if_pos h1]
    rcases Nat.lt_or_ge S J with hlt | hge
    · have h2 : S % J ≠ 0 := by rw [Nat.mod_eq_of_lt hlt]; omega
      rw [if_neg h2, Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt]
      simp
    · have hSJ : S = J := le_antisymm h1 hge
      subst hSJ
      rw [Nat.div_self hS, Nat.mod_self, if_pos rfl]
      simp
  · rw [if_neg h1]

lemma piecesL_eq (J : ℕ) (hJ : 0 < J) (R : ℕ) (hR : 0 < R) :
    ((piecesL J R : List ℕ) : Multiset ℕ) = pieces J R := by
  induction R using Nat.strong_induction_on with
  | _ R ih =>
    rw [piecesL]
    by_cases h : J < R
    · rw [dif_pos ⟨hJ, h⟩, ← Multiset.cons_coe, ih (R - J) (by omega) (by omega),
        pieces_eq_rep hJ (by omega : 0 < R - J), pieces_eq_rep hJ hR,
        Nat.div_eq_sub_div hJ h.le, Nat.mod_eq_sub_mod h.le, Multiset.replicate_succ, Multiset.cons_add]
    · rw [dif_neg (fun h' => h h'.2)]
      unfold pieces
      rw [if_pos (by omega)]
      all_goals rfl

/-- Split every block of a word. -/
def splitLet (J : ℕ) : GMove α ρ → GWord α ρ
  | .old (.block l rk z ind) => splitBlk J l rk z ind
  | mv => [mv]

def splitW (J : ℕ) (w : GWord α ρ) : GWord α ρ := w.flatMap (splitLet J)

lemma gwalk_splitLet (J f : ℕ) (mv : GMove α ρ) (x : Data α ρ f) :
    gwalk f (splitLet J mv) x = mv.act f x := by
  cases mv with
  | old mv =>
    cases mv with
    | localM g => rfl
    | shift l z => rfl
    | block l rk z ind => exact gwalk_splitBlk J l f rk z ind x
  | perm l G => rfl
  | phase l z c => rfl

theorem gwalk_splitW (J f : ℕ) (w : GWord α ρ) (x : Data α ρ f) :
    gwalk f (splitW J w) x = gwalk f w x := by
  induction w generalizing x with
  | nil => rfl
  | cons mv w ih =>
    rw [splitW, List.flatMap_cons, gwalk_append, gwalk_splitLet, gwalk_cons, ← ih]
    all_goals rfl

theorem GLiveKernelM.splitW {σ : Type*} {e : σ → ρ} {T : σ → CMat α} {w : GWord α ρ} (J : ℕ)
    (h : GLiveKernelM e T w) : GLiveKernelM e T (splitW J w) :=
  h.of_gwalk (fun f x => (gwalk_splitW J f w x).symm)

lemma rk_splitLet (J : ℕ) (mv : GMove α ρ) :
    (splitLet J mv).filterMap GMove.rk? = (mv.rk?.toList).flatMap (piecesL J) := by
  cases mv with
  | old mv =>
    cases mv with
    | localM g => rfl
    | shift l z => rfl
    | block l rk z ind =>
      show (splitBlk J l rk z ind).filterMap GMove.rk? = [rk].flatMap (piecesL J)
      rw [rk_splitBlk]
      simp
  | perm l G => rfl
  | phase l z c => rfl

theorem rk_splitW (J : ℕ) (w : GWord α ρ) :
    (splitW J w).filterMap GMove.rk? = (w.filterMap GMove.rk?).flatMap (piecesL J) := by
  induction w with
  | nil => rfl
  | cons mv w ih =>
    simp only [splitW] at ih ⊢
    rw [List.flatMap_cons, List.filterMap_append, ih, rk_splitLet]
    cases h : mv.rk? with
    | none => rw [List.filterMap_cons_none h]; all_goals rfl
    | some k =>
      rw [List.filterMap_cons_some h]
      simp only [Option.toList_some, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The paid ranks after the split, as a multiset. -/
theorem ranks_splitW (J : ℕ) (hJ : 0 < J) (w : GWord α ρ) (hpos : ∀ r ∈ w.filterMap GMove.rk?, 0 < r) :
    (((splitW J w).filterMap GMove.rk? : List ℕ) : Multiset ℕ)
      = splitAll J ((w.filterMap GMove.rk? : List ℕ) : Multiset ℕ) := by
  rw [rk_splitW]
  unfold splitAll
  rw [← Multiset.coe_bind]
  apply Multiset.bind_congr
  intro R hR
  exact piecesL_eq J hJ R (hpos R (Multiset.mem_coe.1 hR))

end Split

/-! ### completion of the targets -/

section Pad
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] [Fintype σ] [DecidableEq σ]

/-- An additive bijection preserves linear independence. -/
lemma indep_map_add {X Y ι : Type*} [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y]
    (T : X ≃ Y) (hT : ∀ u v, T (u + v) = T u + T v) {v : ι → X} (hv : LinearIndependent F v) :
    LinearIndependent F (T ∘ v) := by
  let Φ : X →ₗ[F] Y := (AddMonoidHom.mk' T hT).toZModLinearMap 2
  have hΦ : LinearMap.ker Φ = ⊥ := LinearMap.ker_eq_bot.mpr T.injective
  exact hv.map' Φ hΦ

/-- The standard vectors of `Space κ × Space (Fin r)`: first the block coordinates, then the rest. -/
def stdPair {κ : Type*} [Fintype κ] [DecidableEq κ] {r n : ℕ} (hn : n ≤ Fintype.card κ) :
    Fin (r + n) → Space κ × Space (Fin r) :=
  Fin.append (fun i : Fin r => ((0 : Space κ), (eu i : Space (Fin r))))
    (fun j : Fin n => ((eu ((Fintype.equivFin κ).symm (Fin.castLE hn j)) : Space κ), (0 : Space (Fin r))))

lemma stdPair_ind {κ : Type*} [Fintype κ] [DecidableEq κ] {r n : ℕ} (hn : n ≤ Fintype.card κ) :
    LinearIndependent F (stdPair (r := r) hn) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc k
  -- the two components of the vanishing combination
  have h1 := congr_arg Prod.snd hc
  have h2 := congr_arg Prod.fst hc
  simp only [Fin.sum_univ_add, stdPair, Fin.append_left, Fin.append_right, Prod.fst_add, Prod.snd_add,
    Prod.snd_sum, Prod.fst_sum, Prod.smul_snd, Prod.smul_fst, Prod.snd_zero, Prod.fst_zero, smul_zero,
    Finset.sum_const_zero, zero_add, add_zero] at h1 h2
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · have := congr_fun h1 i
    simp only [Finset.sum_apply, Pi.smul_apply, eu, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, Pi.zero_apply] at this
    exact this
  · have := congr_fun h2 ((Fintype.equivFin κ).symm (Fin.castLE hn j))
    simp only [Finset.sum_apply, Pi.smul_apply, eu, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Pi.zero_apply] at this
    rw [Finset.sum_eq_single j] at this
    · simpa using this
    · intro b _ hb
      rw [if_neg]
      intro h
      apply hb
      have := (Fintype.equivFin κ).symm.injective h
      exact Fin.castLE_injective hn this
    · intro h; exact absurd (Finset.mem_univ j) h

namespace CU
variable (U : CU α ρ σ)

/-- The splitting adapted to the target of live role `l`. -/
def St (l : σ) : Split α (Fin (Fintype.card α - U.tr l)) (Fin (U.tr l)) :=
  Classical.choose (exists_split (U.tz l) (U.tind l))

lemma St_spec (l : σ) (i : Fin (U.tr l)) : (U.St l).e.symm (0, eu i) = U.tz l i :=
  Classical.choose_spec (exists_split (U.tz l) (U.tind l)) i

/-- The target of live role `l`, completed to rank `max (tr l) L` (needs `L ≤ card α`). -/
def padFam (L : ℕ) (hL : L ≤ Fintype.card α) (l : σ) : Fin (U.tr l + (L - U.tr l)) → Space α :=
  fun k => (U.St l).e.symm (stdPair (r := U.tr l) (n := L - U.tr l) (by rw [Fintype.card_fin]; omega) k)

lemma padFam_ind (L : ℕ) (hL : L ≤ Fintype.card α) (l : σ) : LinearIndependent F (U.padFam L hL l) :=
  indep_map_add (U.St l).e.symm (U.St l).symm_add (stdPair_ind _)

lemma padFam_left (L : ℕ) (hL : L ≤ Fintype.card α) (l : σ) (i : Fin (U.tr l)) :
    U.padFam L hL l (Fin.castAdd _ i) = U.tz l i := by
  unfold padFam stdPair
  rw [Fin.append_left, St_spec]

/-- The extra directions of live role `l`. -/
def padExt (L : ℕ) (hL : L ≤ Fintype.card α) (l : σ) : Fin (L - U.tr l) → Space α :=
  fun j => U.padFam L hL l (Fin.natAdd _ j)

lemma padExt_ind (L : ℕ) (hL : L ≤ Fintype.card α) (l : σ) : LinearIndependent F (U.padExt L hL l) :=
  (U.padFam_ind L hL l).comp _ (Fin.natAdd_injective _ _)

/-- The completion letter of live role `l`. -/
def padLetter (L : ℕ) (hL : L ≤ Fintype.card α) (l : σ) : GMove α ρ :=
  GMove.old (BMove.block (U.e l) (L - U.tr l) (U.padExt L hL l) (U.padExt_ind L hL l))

/-- The live roles whose target is below `L`, each once. -/
def lowList (L : ℕ) : List σ := ((Finset.univ : Finset σ).filter fun l => U.tr l < L).toList

/-- The completion word. -/
def padWord (L : ℕ) (hL : L ≤ Fintype.card α) : GWord α ρ := (U.lowList L).map (U.padLetter L hL)

lemma blockMat_padFam (L : ℕ) (hL : L ≤ Fintype.card α) (l : σ) :
    blockMat (U.padFam L hL l) = blockMat (U.padExt L hL l) * blockMat (U.tz l) := by
  have h1 : (fun i : Fin (U.tr l) => U.padFam L hL l (Fin.castAdd (L - U.tr l) i)) = U.tz l :=
    funext (U.padFam_left L hL l)
  have h2 : (fun j : Fin (L - U.tr l) => U.padFam L hL l (Fin.natAdd (U.tr l) j)) = U.padExt L hL l := rfl
  rw [split_block, blockMat_comm, h1, h2]

/-- **The completed unit.** -/
def pad (L : ℕ) (hL : L ≤ Fintype.card α) : CU α ρ σ where
  e := U.e
  he := U.he
  tr := fun l => U.tr l + (L - U.tr l)
  tz := U.padFam L hL
  tind := U.padFam_ind L hL
  wd := U.wd ++ U.padWord L hL
  hw := by
    have hloc : RoleLocal (U.padWord L hL) := by
      intro mv hmv
      obtain ⟨l, _, rfl⟩ := List.mem_map.mp hmv
      trivial
    have h := U.hw.append_local (U.padWord L hL) hloc
    refine h.congr (fun l => ?_)
    have hm : OnRole U.e (U.padLetter L hL) (fun l => blockMat (U.padExt L hL l)) :=
      fun l => ⟨trivial, fun j => rfl⟩
    rw [padWord, roleProd_map_e U.he hm (U.lowList L) (Finset.nodup_toList _) l, blockMat_padFam]
    split_ifs with hl
    · rfl
    · -- `tr l ≥ L`: no extra directions
      have h0 : L - U.tr l = 0 := by
        have : ¬ U.tr l < L := fun h' => hl (by simp [lowList, h'])
        omega
      rw [one_mul]
      have : blockMat (U.padExt L hL l) = 1 := by
        unfold blockMat
        have hn : ∀ (n : ℕ) (g : Fin n → Space α), n = 0 → (List.ofFn fun i => dir (g i)).prod = 1 := by
          intro n g hn; subst hn; simp
        exact hn _ _ h0
      rw [this, one_mul]

end CU

end Pad

end

end TensorEng
