--might be  containing modified Apache-2.0 codes pieces from one or several sources; notices and credits: Credits.lean
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Ripple.RoleMoves

namespace OAI.PowerSaving.TensorMoment

open Multiset

noncomputable section

def mom (t : ℝ) (s : Multiset ℕ) : ℝ := (s.map fun r : ℕ => (r : ℝ) ^ t).sum

@[simp] lemma mom_zero (t : ℝ) : mom t 0 = 0 := by simp [mom]

@[simp] lemma mom_singleton (t : ℝ) (r : ℕ) : mom t {r} = (r : ℝ) ^ t := by simp [mom]

lemma mom_add (t : ℝ) (s s' : Multiset ℕ) : mom t (s + s') = mom t s + mom t s' := by simp [mom]

lemma mom_replicate (t : ℝ) (n r : ℕ) : mom t (Multiset.replicate n r) = (n : ℝ) * (r : ℝ) ^ t := by simp [mom]

lemma mom_nonneg (t : ℝ) (s : Multiset ℕ) : 0 ≤ mom t s := sum_nonneg fun _ h => by obtain ⟨r, -, rfl⟩ := mem_map.1 h; positivity

private lemma mom_bind (t : ℝ) (s : Multiset ℕ) (f : ℕ → Multiset ℕ) :
    mom t (s.bind f) = (s.map fun a => mom t (f a)).sum := by
  rw [mom, map_bind, sum_bind]; rfl

def tens (A B : Multiset ℕ) : Multiset ℕ := A.bind fun a => B.map fun b => a * b

lemma mom_tens (t : ℝ) (A B : Multiset ℕ) : mom t (tens A B) = mom t A * mom t B := by
  rw [tens, mom_bind]
  simp [mom, Real.mul_rpow, sum_map_mul_left, sum_map_mul_right]

lemma card_tens (A B : Multiset ℕ) : card (tens A B) = card A * card B := by simp [tens, card_bind]

def tpow (A : Multiset ℕ) : ℕ → Multiset ℕ
  | 0 => {1}
  | v + 1 => tens (tpow A v) A

lemma mom_tpow (t : ℝ) (A : Multiset ℕ) (v : ℕ) : mom t (tpow A v) = mom t A ^ v := by
  induction v <;> simp [tpow, mom_tens, pow_succ, *]

lemma card_tpow (A : Multiset ℕ) (v : ℕ) : card (tpow A v) = card A ^ v := by
  induction v <;> simp [tpow, card_tens, pow_succ, *]

lemma pow_mem_tpow {A : Multiset ℕ} {a : ℕ} (ha : a ∈ A) (v : ℕ) : a ^ v ∈ tpow A v := by
  induction v with
  | zero => simp [tpow]
  | succ v ih => simp only [tpow, tens, mem_bind, mem_map, pow_succ]; exact ⟨_, ih, a, ha, rfl⟩

def pieces (J R : ℕ) : Multiset ℕ :=
  if R ≤ J then {R} else Multiset.replicate (R / J) J + (if R % J = 0 then 0 else {R % J})

def splitAll (J : ℕ) (P : Multiset ℕ) : Multiset ℕ := P.bind (pieces J)

private lemma mem_pieces {J R x : ℕ} (hJ : 0 < J) (hx : x ∈ pieces J R) : (1 ≤ R → 1 ≤ x) ∧ x ≤ J := by
  have := Nat.mod_lt R hJ
  unfold pieces at hx; split_ifs at hx <;> simp [mem_replicate] at hx <;> omega

lemma splitAll_pos {J : ℕ} (hJ : 0 < J) {P : Multiset ℕ} (hP : ∀ R ∈ P, 1 ≤ R) :
    ∀ x ∈ splitAll J P, 1 ≤ x := by
  simp only [splitAll, mem_bind]
  rintro x ⟨R, hR, hx⟩
  exact (mem_pieces hJ hx).1 (hP R hR)

private lemma mom_pieces {J R : ℕ} {t : ℝ} (hJ : 0 < J) (ht0 : 0 ≤ t) :
    mom t (pieces J R) ≤ ((R / J * J + J : ℕ) : ℝ) * (J : ℝ) ^ (t - 1) := by
  have hJ' : (0 : ℝ) < J := Nat.cast_pos.2 hJ
  have e : (J : ℝ) ^ t = J * J ^ (t - 1) := by rw [Real.rpow_sub_one hJ'.ne']; field_simp
  have hr : ∀ r ≤ J, (r : ℝ) ^ t ≤ J ^ t := fun r h => Real.rpow_le_rpow (by positivity) (by exact_mod_cast h) ht0
  have := hr _ (Nat.mod_lt R hJ).le
  have : 0 ≤ ((R / J : ℕ) : ℝ) * J * J ^ (t - 1) := by positivity
  push_cast; unfold pieces; split_ifs with h
  · simp only [mom_singleton]; linarith [hr R h]
  all_goals simp only [mom_add, mom_replicate, mom_singleton, add_zero]; linarith [Real.rpow_nonneg hJ'.le t, congrArg (((R / J : ℕ) : ℝ) * ·) e]

lemma mom_splitAll_le {J : ℕ} {t u : ℝ} (hJ : 0 < J) (ht0 : 0 ≤ t) (hu : 0 ≤ u) (hσ : 1 ≤ t + u)
    (P : Multiset ℕ) :
    mom t (splitAll J P) ≤ mom t P + 2 * (J : ℝ) ^ (-u) * mom (t + u) P := by
  rw [splitAll, mom_bind]
  refine (sum_map_le_sum_map _ (fun R : ℕ => (R : ℝ) ^ t + 2 * (J : ℝ) ^ (-u) * (R : ℝ) ^ (t + u))
    fun R _ => ?_).trans_eq (by simp [mom, sum_map_add, sum_map_mul_left])
  have hJ' : (0 : ℝ) < J := Nat.cast_pos.2 hJ
  by_cases hJR : R ≤ J
  · simp only [pieces, hJR, if_true, mom_singleton]; linarith [(by positivity : 0 ≤ (J : ℝ) ^ (-u) * (R : ℝ) ^ (t + u))]
  have hR : (J : ℝ) ≤ R := by exact_mod_cast (by omega : J ≤ R)
  have hq : ((R / J * J + J : ℕ) : ℝ) ≤ 2 * R := by
    have := Nat.div_mul_le_self R J; exact_mod_cast (by omega : R / J * J + J ≤ 2 * R)
  have : (R : ℝ) * J ^ (t - 1) ≤ J ^ (-u) * R ^ (t + u) :=
    calc (R : ℝ) * J ^ (t - 1) = J ^ (-u) * (J ^ (t + u - 1) * R) := by rw [← mul_assoc, ← Real.rpow_add hJ']; ring_nf
      _ ≤ J ^ (-u) * (R ^ (t + u - 1) * R) := by gcongr
      _ = _ := by rw [← Real.rpow_add_one (hJ'.trans_le hR).ne']; ring_nf
  linarith [@mom_pieces J R t hJ ht0, mul_le_mul_of_nonneg_right hq (Real.rpow_nonneg hJ'.le (t - 1)),
    Real.rpow_nonneg (Nat.cast_nonneg R) t]

lemma mom_pieces_big {J R : ℕ} {t : ℝ} (hJ : 0 < J) (hRJ : J < R) (ht0 : 0 ≤ t) :
    mom t (pieces J R) ≤ (R : ℝ) * (J : ℝ) ^ (t - 1) + (J : ℝ) ^ t := by
  have hJ' : (0 : ℝ) < J := Nat.cast_pos.2 hJ
  have hq : ((R / J * J + J : ℕ) : ℝ) ≤ R + J := by exact_mod_cast (by have := Nat.div_mul_le_self R J; omega : R / J * J + J ≤ R + J)
  have e : (J : ℝ) ^ t = J * J ^ (t - 1) := by rw [Real.rpow_sub_one hJ'.ne']; field_simp
  linarith [@mom_pieces J R t hJ ht0, mul_le_mul_of_nonneg_right hq (Real.rpow_nonneg hJ'.le (t - 1))]

lemma mom_pieces_two {J R : ℕ} {t : ℝ} (hJ : 0 < J) (hRJ : J < R) (ht0 : 0 ≤ t) :
    mom t (pieces J R) ≤ 2 * (R : ℝ) * (J : ℝ) ^ (t - 1) := by
  have hJ' : (0 : ℝ) < J := Nat.cast_pos.2 hJ
  have e : (J : ℝ) ^ t = J * J ^ (t - 1) := by rw [Real.rpow_sub_one hJ'.ne']; field_simp
  linarith [mom_pieces_big hJ hRJ ht0, mul_le_mul_of_nonneg_right (by exact_mod_cast hRJ.le : (J : ℝ) ≤ R) (Real.rpow_nonneg hJ'.le (t - 1))]

lemma mom_pieces_tail {J R : ℕ} {t u : ℝ} (hJ : 0 < J) (ht0 : 0 ≤ t) (hu : 0 ≤ u) (hσ : 1 ≤ t + u) :
    mom t (pieces J R) ≤ (R : ℝ) ^ t + 2 * (J : ℝ) ^ (-u) * (R : ℝ) ^ (t + u) := by
  simpa [splitAll] using mom_splitAll_le hJ ht0 hu hσ {R}

def padT (L : ℕ) (T : Multiset ℕ) : Multiset ℕ := T.map fun K => max K L

def comp (L : ℕ) (T : Multiset ℕ) : Multiset ℕ := T.bind fun K => if K < L then {L - K} else 0

lemma mem_padT {L K : ℕ} {T : Multiset ℕ} (hK : K ∈ T) (h : K ≤ L) : L ∈ padT L T := mem_map.2 ⟨K, hK, Nat.max_eq_right h⟩

lemma mom_le_mom_padT {t : ℝ} (ht0 : 0 ≤ t) (L : ℕ) (T : Multiset ℕ) : mom t T ≤ mom t (padT L T) := by
  simp only [mom, padT, map_map, Function.comp_def]
  exact sum_map_le_sum_map _ _ fun K _ =>
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast le_max_left K L) ht0

lemma comp_pos {L : ℕ} {T : Multiset ℕ} : ∀ x ∈ comp L T, 1 ≤ x := by
  simp only [comp, mem_bind]
  rintro x ⟨K, -, hx⟩
  split_ifs at hx <;> simp at hx; omega

lemma mom_split_comp_le {J L : ℕ} {t : ℝ} (hJ : 0 < J) (hJL : J ≤ L) (ht0 : 0 ≤ t) (T : Multiset ℕ) :
    mom t (splitAll J (comp L T)) ≤ (card T : ℝ) * (2 * (L : ℝ) * (J : ℝ) ^ (t - 1)) := by
  rw [splitAll, comp, bind_assoc, mom_bind]
  refine (sum_le_card_nsmul _ (2 * (L : ℝ) * (J : ℝ) ^ (t - 1)) fun y hy => ?_).trans_eq (by simp)
  obtain ⟨K, -, rfl⟩ := mem_map.1 hy
  have hJ' : (0 : ℝ) < J := by exact_mod_cast hJ
  split_ifs with hK
  · rw [singleton_bind]
    have hq : ((((L - K) / J * J + J : ℕ)) : ℝ) ≤ 2 * L := by
      have := Nat.div_mul_le_self (L - K) J; exact_mod_cast (by omega : (L - K) / J * J + J ≤ 2 * L)
    linarith [@mom_pieces J (L - K) t hJ ht0, mul_le_mul_of_nonneg_right hq (Real.rpow_nonneg hJ'.le (t - 1))]
  · simp only [zero_bind, mom_zero]; positivity

def strictT (T : Multiset ℕ) (v L : ℕ) : Multiset ℕ := padT L (tpow T v)

def strictP (T P : Multiset ℕ) (v J L : ℕ) : Multiset ℕ := splitAll J (tpow P v + comp L (tpow T v))

lemma strictP_le {T P : Multiset ℕ} {v J L : ℕ} (hJ : 0 < J) : ∀ x ∈ strictP T P v J L, x ≤ J := by
  simp only [strictP, splitAll, mem_bind]
  rintro x ⟨R, -, hx⟩
  exact (mem_pieces hJ hx).2

theorem strictify_mom {T P : Multiset ℕ} {v J L : ℕ} {t u : ℝ}
    (hJ : 0 < J) (hJL : J ≤ L) (ht0 : 0 ≤ t) (hu : 0 ≤ u) (hσ : 1 ≤ t + u)
    (h : mom t P ^ v + 2 * (J : ℝ) ^ (-u) * mom (t + u) P ^ v
          + (card T : ℝ) ^ v * (2 * (L : ℝ) * (J : ℝ) ^ (t - 1)) ≤ mom t T ^ v) :
    mom t (strictP T P v J L) ≤ mom t (strictT T v L) := by
  have h1 := mom_splitAll_le hJ ht0 hu hσ (tpow P v)
  have h2 := mom_split_comp_le hJ hJL ht0 (tpow T v)
  have h3 := mom_le_mom_padT ht0 L (tpow T v)
  rw [mom_tpow, mom_tpow] at h1; rw [card_tpow, Nat.cast_pow] at h2; rw [mom_tpow] at h3
  rw [strictP, strictT, splitAll, add_bind, mom_add]
  rw [splitAll] at h1 h2
  linarith

theorem strictify {T P : Multiset ℕ} {v c b : ℕ} {t u : ℝ}
    (hc : 0 < c) (hcb : c ≤ b) (ht0 : 0 ≤ t) (hu : 0 ≤ u) (hσ : 1 ≤ t + u) (hT : 0 < mom t T)
    (h : (mom t P / mom t T) ^ v + 2 * (mom (t + u) P / ((c : ℝ) ^ u * mom t T)) ^ v
          + 2 * ((card T : ℝ) * b / ((c : ℝ) ^ (1 - t) * mom t T)) ^ v ≤ 1) :
    mom t (strictP T P v (c ^ v) (b ^ v)) ≤ mom t (strictT T v (b ^ v)) := by
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have e : ∀ y : ℝ, ((c ^ v : ℕ) : ℝ) ^ (-y) = (((c : ℝ) ^ y) ^ v)⁻¹ := fun y => by
    rw [Real.rpow_neg (by positivity), Nat.cast_pow, Real.rpow_pow_comm hc'.le]
  refine strictify_mom (pow_pos hc v) (Nat.pow_le_pow_left hcb v) ht0 hu hσ ?_
  rw [e, show t - 1 = -(1 - t) by ring, e]; push_cast
  rw [div_pow, div_pow, div_pow, mul_pow, mul_pow, mul_pow] at h
  have := pow_pos hT v
  have := pow_pos (Real.rpow_pos_of_pos hc' u) v
  have := pow_pos (Real.rpow_pos_of_pos hc' (1 - t)) v
  field_simp at h ⊢
  linarith

end

end OAI.PowerSaving.TensorMoment

namespace OAI
namespace PowerSaving
noncomputable def envelope (z : ℝ) (k : ℕ) : ℕ := ⌈((k : ℝ) + 1) ^ z⌉₊
lemma envelope_pos (z : ℝ) (k : ℕ) : 1 ≤ envelope z k := Nat.one_le_ceil_iff.2 (Real.rpow_pos_of_pos (by positivity) z)
lemma envelope_mono (z : ℝ) (hz : 0 ≤ z) {a b : ℕ} (h : a ≤ b) : envelope z a ≤ envelope z b := by
  unfold envelope; gcongr
namespace RAM
variable {ρ : Type*} [Fintype ρ] [DecidableEq ρ]

lemma sum_castInd_mul (a : ρ) (x : ρ → ℂ) : ∑ j, ((if a = j then (1:ℚ) else 0 : ℚ) : ℂ) * x j = x a := by
  simp only [apply_ite (fun q : ℚ => (q : ℂ)), Rat.cast_one, Rat.cast_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

lemma sum_ind_right (a : ρ) (x : ρ → ℂ) : ∑ j, ((if a = j then (1:ℚ) else 0 : ℚ) : ℂ) * x j = x a :=
  sum_castInd_mul a x
end RAM
end PowerSaving
end OAI

namespace OAI.PowerSaving.Histogram
def histFn (l : List (ℕ × ℕ)) (r : ℕ) : ℕ :=
  ((l.filter fun b => b.1 = r).map Prod.snd).sum
lemma histFn_cons (b : ℕ × ℕ) (l : List (ℕ × ℕ)) (r : ℕ) :
    histFn (b::l) r = (if b.1 = r then b.2 else 0) + histFn l r := by
  unfold histFn
  by_cases h : b.1 = r <;> simp [List.filter_cons, h]
end OAI.PowerSaving.Histogram

namespace OAI
namespace PowerSaving.Binary
open Matrix Finset
noncomputable section
variable {α β γ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ]
structure Split (α β γ : Type*) where
  e : Space α ≃ Space β × Space γ
  add : ∀ x y, e (x + y) = e x + e y
namespace Split
variable (S : Split α β γ)
lemma symm_add (p q : Space β × Space γ) :
    S.e.symm (p + q) = S.e.symm p + S.e.symm q := S.e.injective (by simp [S.add])
def lift (M : CMat γ) : CMat α :=
  fun x y => if (S.e x).1 = (S.e y).1 then M (S.e x).2 (S.e y).2 else 0
lemma lift_one : S.lift (1 : CMat γ) = 1 := by
  ext x y; simp only [lift, one_apply, ← S.e.injective.eq_iff, Prod.ext_iff]; split_ifs <;> simp_all
lemma lift_mul (M N : CMat γ) : S.lift (M * N) = S.lift M * S.lift N := by
  ext x y; simp only [lift, mul_apply]; rw [← S.e.symm.sum_comp, Fintype.sum_prod_type]
  simp [ite_mul, mul_ite]
lemma lift_shift (c : Space γ) : S.lift (shift c) = shift (S.e.symm (0, c)) := by
  ext; simp [lift, shift, ← S.e.injective.eq_iff, S.add, Prod.ext_iff, ite_and]
lemma lift_dir (c : Space γ) : S.lift (dir c) = dir (S.e.symm (0, c)) := by
  have h (a b : ℂ) (M N : CMat γ) : S.lift (a • M + b • N) = a • S.lift M + b • S.lift N := by
    ext; simp only [lift, Matrix.add_apply, Matrix.smul_apply]; split_ifs <;> simp
  rw [dir, dir, h, lift_one, lift_shift]
lemma lift_list_prod (L : List (CMat γ)) : S.lift L.prod = (L.map S.lift).prod := by
  induction L <;> simp [*, lift_one, lift_mul]
end Split
def blockMat {r : ℕ} (z : Fin r → Space α) : CMat α := (List.ofFn fun i => dir (z i)).prod
lemma blockMat_wrap {r : ℕ} (z : Fin r → Space α) :
    blockMat z = wrap fun x => ∏ i, tint (dot (z i) x) := by
  induction r with
  | zero => simp [blockMat, wrap_one]
  | succ r ih =>
    simp only [blockMat, List.ofFn_succ, List.prod_cons] at ih ⊢
    rw [ih, dir_phase, wrap_mul]; simp only [Fin.prod_univ_succ]
theorem blockMat_eq_lift {r : ℕ} (S : Split α β (Fin r)) (z : Fin r → Space α)
    (hz : ∀ i, S.e.symm (0, eu i) = z i) : blockMat z = S.lift (kernel (Fin r)) := by
  rw [show kernel (Fin r) = blockMat eu by rw [blockMat_wrap, ← wrap_lum]; congr 1; funext x; simp [lum],
    blockMat, blockMat, S.lift_list_prod, List.map_ofFn]
  simp [Function.comp_def, S.lift_dir, hz]
section Exists
lemma extend {r : ℕ} (z : Fin r → Space α) (hz : LinearIndependent F z) :
    ∀ k, k ≤ Fintype.card α - r → ∃ w : Fin k → Space α, LinearIndependent F (Fin.append z w)
  | 0, _ => ⟨Fin.elim0, by rw [Fin.append_right_nil _ _ rfl]; exact hz.comp _ (Fin.cast_injective _)⟩
  | k+1, hk => by
    obtain ⟨w, hw⟩ := extend z hz k (by omega)
    obtain ⟨v, hv⟩ : ∃ v, v ∉ Submodule.span F (Set.range (Fin.append z w)) := by
      by_contra! H
      have := Fintype.card_le_of_surjective _ fun v => (Submodule.mem_span_range_iff_exists_fun F).1 (H v)
      simp [Nat.pow_le_pow_iff_right] at this; omega
    exact ⟨Fin.snoc w v, by rw [Fin.append_snoc]; exact linearIndependent_finSnoc.2 ⟨hw, hv⟩⟩
theorem exists_split {r : ℕ} (z : Fin r → Space α) (hz : LinearIndependent F z) :
    ∃ S : Split α (Fin (Fintype.card α - r)) (Fin r), ∀ i, S.e.symm (0, eu i) = z i := by
  obtain ⟨w, hw⟩ := extend z hz _ le_rfl
  let φ : Space (Fin (Fintype.card α - r)) × Space (Fin r) →+ Space α :=
    AddMonoidHom.mk' (fun p => ∑ i, p.2 i • z i + ∑ j, p.1 j • w j) fun p q => by
      simp [add_smul, sum_add_distrib, add_add_add_comm]
  have inj : Function.Injective φ := (injective_iff_map_eq_zero φ).2 fun p hp => by
    have := Fintype.linearIndependent_iff.1 hw (Fin.append p.2 p.1) (by simpa [φ, Fin.sum_univ_add] using hp)
    exact Prod.ext (funext fun j => by simpa using this (Fin.natAdd _ j))
      (funext fun j => by simpa using this (Fin.castAdd _ j))
  have c := Fintype.card_le_of_injective φ inj
  simp [← pow_add, Nat.pow_le_pow_iff_right] at c
  let A := AddEquiv.ofBijective φ ((Fintype.bijective_iff_injective_and_card φ).2 ⟨inj, by simp [← pow_add]; omega⟩)
  exact ⟨⟨A.symm.toEquiv, A.symm.map_add⟩, fun i => show φ (0, eu i) = z i by simp [φ, eu]⟩
end Exists
lemma flat_len (r f : ℕ) : (Layout.std r).n*f+0 = r*f := rfl
def flat (r f : ℕ) : Sky (Fin r) f ≃ Bits (r*f) where
  toFun y := serial (Layout.std r) 0 f (flat_len r f) (default, y)
  invFun b := ((serial (Layout.std r) 0 f (flat_len r f)).symm b).2
  left_inv y := by simp
  right_inv b := by
    have h0 : ((default : Bits 0), ((serial (Layout.std r) 0 f (flat_len r f)).symm b).2)
        = (serial (Layout.std r) 0 f (flat_len r f)).symm b := Prod.ext (Subsingleton.elim _ _) rfl
    simp only [h0, Equiv.apply_symm_apply]
variable {r : ℕ}
def Split.sky (S : Split α β γ) (f : ℕ) : Sky α f ≃ Sky β f × Sky γ f where
  toFun x := (fun k => (S.e (x k)).1, fun k => (S.e (x k)).2)
  invFun x k := S.e.symm (x.1 k, x.2 k)
  left_inv x := by simp
  right_inv x := by apply Prod.ext <;> funext k <;> simp
def Split.peel (S : Split α β (Fin r)) (r' f : ℕ) :
    Grid α r' f ≃ Grid β r' f × Bits (r*f) where
  toFun x := ((x.1,(S.sky f x.2).1), flat r f (S.sky f x.2).2)
  invFun p := (p.1.1,(S.sky f).symm (p.1.2,(flat r f).symm p.2))
  left_inv x := by simp
  right_inv p := by simp
theorem Split.product (S : Split α β (Fin r)) (f : ℕ) (x y : Sky α f) :
    digitProd (fun _ : Fin f => S.lift (kernel (Fin r))) x y =
    if (S.sky f x).1=(S.sky f y).1 then
      kernel (Fin (r*f)) (flat r f (S.sky f x).2) (flat r f (S.sky f y).2) else 0 := by
  have key (u v : Sky (Fin r) f) :
      kernel (Fin (r*f)) (flat r f u) (flat r f v) = ∏ j, kernel (Fin r) (u j) (v j) := by
    show kernel _ (serial (Layout.std r) 0 f (flat_len r f) (default, u))
      (serial (Layout.std r) 0 f (flat_len r f) (default, v)) = _
    rw [kernel_serial]; simp [kernel]
  rw [key, digitProd_apply]; simp only [Split.lift]
  exact prod_ite_eqs (fun j => (S.e (x j)).1) (fun j => (S.e (y j)).1) _
end
end PowerSaving.Binary
namespace PowerSaving.RAM
open Binary Ty Finset
noncomputable section
universe U
variable {ι : Type U}
namespace BitCtx
variable {m : Bool} {B f : ι → ℕ} {s t : Ty} {x : ι → T s}
variable (g : BitCtx m B f s x)
include g
lemma powerB (rk : ℕ) : Knows m B s x (fun i => 2^(rk * f i)) :=
  (Can.wpow_fixed rk g.power g.bound).cong (fun _ => rfl) fun i => by rw [← pow_mul, mul_comm]
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

lemma body_lin (X : Layout α) (L : Space α → F) (hL : ∀ p q, L (p+q) = L p + L q)
    (v : ∀ i, Sky α (f i)) (h : Knows m B s x fun i => (bodyOrder X (f i)).loc (v i)) :
    Knows m B s x fun i => (bits (f i)).loc fun l => L (v i l) := by
  have hs (c : F) (y : Space α) : L (c • y) = c * L y := by
    rcases bit_cases c with rfl | rfl <;> simp [show L 0 = 0 by simpa using hL 0 0]
  have key (d : Finset α) : Knows m B s x fun i => (bits (f i)).loc fun l => ∑ a ∈ d, v i l a * L (eu a) := by
    induction d using Finset.induction with
    | empty => simpa [bits_loc] using Can.wc (m := m) (B := B) (x := x) (W := fun _ => 0) 0
    | insert a d ha ih =>
      simp only [Finset.sum_insert ha]
      rcases bit_cases (L (eu a)) with e | e <;> simp only [e, mul_zero, zero_add, mul_one]
      exacts [ih, g.addr_xor (fun i => (_, _)) (g.body_get X v a h) ih]
  refine (key univ).cong (fun _ => rfl) fun i => congrArg _ (funext fun l => ?_)
  conv_rhs => rw [pi_eq_sum_univ (v i l)]
  exact ((map_sum (AddMonoidHom.mk' L hL) _ _).trans (Finset.sum_congr rfl fun a _ => hs _ _)).symm
variable (X : Layout α) (r : ℕ) {rk : ℕ}
lemma from_gridB (S : Split α β (Fin rk)) (X' : Layout β)
    (v : ∀ i, Grid α r (f i))
    (h : Knows m B s x (fun i => (book X r (f i)).loc (v i))) :
    Knows m B s x (fun i => (book X' r (f i)).loc (S.peel r (f i) (v i)).1) ∧
    Knows m B s x (fun i => (bits (rk * f i)).loc (S.peel r (f i) (v i)).2) := by
  obtain ⟨h1, h2⟩ := g.grid_fetch X r h
  have H (L : Space α → F) (hL) := g.body_lin X L hL _ h2
  exact ⟨g.grid_combine X' r h1 (g.body_set X' _ fun j => H (fun y => (S.e y).1 j) fun p q => by simp [S.add]),
    (g.grid_combine (Layout.std rk) 0 (v := fun i => (default, _)) (by simpa [bits_loc] using Can.wc 0)
      (g.body_set _ _ fun j => H (fun y => (S.e y).2 j) fun p q => by simp [S.add])).cong (fun _ => rfl)
      fun i => (serial_code _ _ _ (flat_len rk (f i)) _).symm⟩
lemma to_gridB (S : Split α β (Fin rk)) (X' : Layout β)
    (u : ∀ i, Grid β r (f i) × Bits (rk * f i))
    (h : Knows m B s x (fun i => (book X' r (f i)).loc (u i).1))
    (k : Knows m B s x (fun i => (bits (rk * f i)).loc (u i).2)) :
    Knows m B s x (fun i => (book X r (f i)).loc ((S.peel r (f i)).symm (u i))) := by
  have lin (P Q : Space β × Space (Fin rk)) (j : α) : S.e.symm (P + Q) j = S.e.symm P j + S.e.symm Q j := by
    rw [S.symm_add]; rfl
  obtain ⟨h1, h2⟩ := g.grid_fetch X' r h
  have k2 := (g.grid_fetch (Layout.std rk) 0 (v := fun i => (default, (flat rk (f i)).symm (u i).2))
    (k.cong (fun _ => rfl) fun i => (congrArg _ ((flat rk (f i)).apply_symm_apply _)).symm.trans
      (serial_code _ _ _ (flat_len rk (f i)) _))).2
  refine g.grid_combine X r h1 (g.body_set X _ fun j => (g.addr_xor (fun i => (_, _))
    (g.body_lin X' (fun y => S.e.symm (y, 0) j) (fun p q => by simpa using lin (p, 0) (q, 0) j) _ h2)
    (g.body_lin _ (fun y => S.e.symm (0, y) j) (fun p q => by simpa using lin (0, p) (0, q) j) _ k2)).cong
    (fun _ => rfl) fun i => congrArg _ (funext fun l => (lin ((u i).1.2 l, 0)
      (0, (flat rk (f i)).symm (u i).2 l) j).symm.trans (by simp [Split.peel, Split.sky])))
end BitCtx
end
end PowerSaving.RAM
namespace PowerSaving.Binary
open Matrix Finset
noncomputable section
variable {α ρ σ : Type*}
  [Fintype σ] [DecidableEq σ]
inductive BMove (α ρ : Type*)
  | localM (g : Matrix ρ ρ ℚ)
  | shift (l : ρ) (z : Space α)
  | block (l : ρ) (rk : ℕ) (z : Fin rk → Space α) (ind : LinearIndependent F z)
abbrev BWord (α ρ : Type*) := List (BMove α ρ)
namespace BMove
def flat : BMove α ρ → PWord α ρ
  | localM g => [Move.localM g]
  | shift l z => [Move.shift l z]
  | block l _ z ind => List.ofFn fun i => Move.dir l (z i) (ind.ne_zero i)
def rk? : BMove α ρ → Option ℕ
  | localM _ => none
  | shift _ _ => none
  | block _ k _ _ => some k
def Proper (u : ℕ) : BMove α ρ → Prop
  | localM _ => True
  | shift _ _ => True
  | block _ k _ _ => 1 ≤ k ∧ k < u
end BMove
namespace BWord
def flat (w : BWord α ρ) : PWord α ρ := (w.map BMove.flat).flatten
@[simp] lemma flat_nil : flat ([] : BWord α ρ) = [] := rfl
@[simp] lemma flat_cons (mv : BMove α ρ) (w : BWord α ρ) : flat (mv :: w) = mv.flat ++ flat w := rfl
def hist (w : BWord α ρ) (r : ℕ) : ℕ := w.countP fun mv => decide (mv.rk? = some r)
@[simp] lemma hist_nil (r : ℕ) : hist ([] : BWord α ρ) r = 0 := rfl
lemma hist_cons (mv : BMove α ρ) (w : BWord α ρ) (r : ℕ) :
    hist (mv :: w) r = hist w r + if mv.rk? = some r then 1 else 0 := by
  simp [hist, List.countP_cons]
def Proper (u : ℕ) (w : BWord α ρ) : Prop := ∀ mv ∈ w, mv.Proper u
lemma Proper.append {u : ℕ} {w w' : BWord α ρ} (h : Proper u w) (h' : Proper u w') :
    Proper u (w ++ w') := fun mv hm => (List.mem_append.1 hm).elim (h mv) (h' mv)
end BWord
def BMove.costR (φ : ℕ → ℝ) (mv : BMove α ρ) : ℝ :=
  match mv.rk? with
  | none => 0
  | some k => φ k
def BWord.costR (φ : ℕ → ℝ) (w : BWord α ρ) : ℝ := (w.map (BMove.costR φ)).sum
@[simp] lemma BWord.costR_nil (φ : ℕ → ℝ) : BWord.costR φ ([] : BWord α ρ) = 0 := rfl
lemma BWord.costR_cons (φ : ℕ → ℝ) (mv : BMove α ρ) (w : BWord α ρ) :
    BWord.costR φ (mv :: w) = mv.costR φ + BWord.costR φ w := by
  simp [BWord.costR]
variable [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
def BMove.act (f : ℕ) : BMove α ρ → Data α ρ f → Data α ρ f
  | .localM g => point f (actPoint g)
  | .shift l z => roleAct f l (Binary.shift z)
  | .block l _ z _ => roleAct f l (blockMat z)
def BMove.over (e : ρ ↪ σ) : BMove α ρ → BMove α σ
  | .localM M => .localM (wide e M)
  | .shift r z => .shift (e r) z
  | .block r rk z ind => .block (e r) rk z ind
end
end PowerSaving.Binary
namespace PowerSaving.RAM
open Binary
noncomputable section
variable {α ρ : Type*} [Fintype α] [DecidableEq α]
def ferryM [DecidableEq ρ] (r f : ℕ) (l : ρ) (N : CMat α) (v : Grain α ρ r f) :
    Grain α ρ r f :=
  fun x => roleAct f l N (fun i j => v (i,x.2.1,j)) x.1 x.2.2
end
end PowerSaving.RAM
namespace PowerSaving.Binary
open Matrix Finset Complex
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]
lemma dot_sum_left {β : Type*} (s : Finset β) (g : β → Space α) (x : Space α) :
    dot (∑ j ∈ s, g j) x = ∑ j ∈ s, dot (g j) x := by simp [dot_symm _ x, dot_sum]
open Classical in
def eps (z : Space α) : F := if lum z = I then 0 else 1
namespace OBase
variable (A : OBase α)
def fam (d : Finset α) : Fin d.card → Space α := fun i => A.v (d.equivFin.symm i).1
lemma fam_indep (d : Finset α) : LinearIndependent F (A.fam d) :=
  Fintype.linearIndependent_iff.2 fun c hc i => by
    simpa [dot_sum_left, fam, A.rows] using congrArg (dot · (A.fam d i)) hc
lemma blockMat_fam (d : Finset α) :
    blockMat (A.fam d) = wrap (fun x => ∏ i ∈ d, tint (dot (A.v i) x)) := by
  rw [blockMat_wrap]; congr 1; funext x
  exact (d.equivFin.symm.prod_comp fun i : d => tint (dot (A.v i) x)).trans
    (d.prod_coe_sort (fun i => tint (dot (A.v i) x)))
def corr (d : Finset α) : Space α := ∑ i ∈ d, eps (A.v i) • A.v i
def deltas (d : Finset α) : CMat α := wrap (fun x => ∏ i ∈ d, lum (dot (A.v i) x • A.v i))
lemma frame_union (c d : Finset α) (h : Disjoint c d) :
    frame A (c ∪ d) = A.deltas d * frame A c := by
  induction d using Finset.induction with
  | empty => simp [deltas, wrap_one]
  | insert a d ha ih =>
    rw [Finset.disjoint_insert_right] at h
    rw [union_insert, frame_ins _ _ _ (by simp [ha, h.1]), ih h.2, ← mul_assoc, delta, deltas, deltas,
      wrap_mul]
    simp only [prod_insert ha]
lemma deltas_eq (d : Finset α) : A.deltas d = shift (A.corr d) * blockMat (A.fam d) := by
  rw [shift_phase, blockMat_fam, wrap_mul, deltas]; congr 1; funext x
  simp only [corr, dot_sum_left, dot_smul_left, sign_sum, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  rcases bit_cases (dot (A.v i) x) with e | e <;> simp only [e]
  · simp [tint, sign]
  · rcases lum_of_unit _ (A.self i) with e | e <;> simp [eps, e, sign, tint]
end OBase
end
end PowerSaving.Binary
namespace PowerSaving
lemma envelope_le (z : ℝ) (hz1 : z ≤ 1) (k : ℕ) : envelope z k ≤ k+1 :=
  Nat.ceil_le.2 (by simpa using Real.rpow_le_rpow_of_exponent_le (by simp : (1:ℝ) ≤ k+1) hz1)
lemma envelope_real (z : ℝ) (hz : 0 ≤ z) (k : ℕ) : (envelope z k:ℝ) ≤ 2*((k:ℝ)+1)^z :=
  (Nat.ceil_lt_add_one (by positivity)).le.trans
    (by linarith [Real.one_le_rpow (by simp : (1:ℝ) ≤ k+1) hz])
namespace RAM
lemma sum_map_getD {β M : Type*} [AddCommMonoid M] (L : List β) (z : β) (g : β → M) :
    (L.map g).sum = ∑ j ∈ Finset.range L.length, g (L.getD j z) := by
  induction L with
  | nil => simp
  | cons a L ih => rw [List.map_cons, List.sum_cons, ih, List.length_cons, Finset.sum_range_succ']; simp [add_comm]
end RAM
end PowerSaving
namespace PowerSaving.Binary
open Matrix Finset
noncomputable section
variable {α ρ : Type*}
def listCost (φ : ℕ → ℝ) (l : List (ℕ × ℕ)) : ℝ := (l.map fun b => (b.2 : ℝ) * φ b.1).sum
lemma listCost_cons (φ : ℕ → ℝ) (b : ℕ × ℕ) (l : List (ℕ × ℕ)) :
    listCost φ (b :: l) = (b.2:ℝ) * φ b.1 + listCost φ l := by simp [listCost]
lemma BWord.costR_ind (w : BWord α ρ) (r : ℕ) :
    w.costR (fun q => if q = r then 1 else 0) = (w.hist r : ℝ) := by
  induction w with
  | nil => simp
  | cons mv w ih =>
    rw [BWord.costR_cons, ih, BWord.hist_cons]
    rcases mv with _ | _ | ⟨_, k, _, _⟩
    · simp [BMove.costR, BMove.rk?]
    · simp [BMove.costR, BMove.rk?]
    · by_cases hk : k = r <;> simp [BMove.costR, BMove.rk?, hk, add_comm]
lemma listCost_ind (l : List (ℕ × ℕ)) (r : ℕ) :
    listCost (fun q => if q = r then 1 else 0) l = (Histogram.histFn l r : ℝ) := by
  induction l with
  | nil => simp [listCost, Histogram.histFn]
  | cons b l ih => rw [listCost_cons, ih, Histogram.histFn_cons]; by_cases h : b.1 = r <;> simp [h]
end
end PowerSaving.Binary
end OAI

namespace OAI
namespace PowerSaving.GenMove
open Binary Matrix Finset
noncomputable section
variable {α ρ : Type*}
structure APerm (α : Type*) where
  π : Space α ≃ Space α
  add : ∀ x y, π (x + y) = π x + π y
inductive GMove (α ρ : Type*)
  | old (mv : BMove α ρ)
  | perm (l : ρ) (G : APerm α)
  | phase (l : ρ) (z : Space α) (c : F)
  | localG (gr gi : Matrix ρ ρ ℚ)
abbrev GWord (α ρ : Type*) := List (GMove α ρ)
namespace GMove
def shadow : GMove α ρ → BMove α ρ
  | .old mv => mv
  | _ => .localM 0
def rk? (mv : GMove α ρ) : Option ℕ := mv.shadow.rk?
def costR (φ : ℕ → ℝ) (mv : GMove α ρ) : ℝ := mv.shadow.costR φ
def Proper (u : ℕ) (mv : GMove α ρ) : Prop := mv.shadow.Proper u
lemma proper_iff (mv : GMove α ρ) (u : ℕ) :
    mv.Proper u ↔ ∀ r, mv.rk? = some r → 1 ≤ r ∧ r < u := by
  unfold Proper rk?
  cases mv.shadow <;> simp [BMove.Proper, BMove.rk?]
end GMove
namespace GWord
def shadow (w : GWord α ρ) : BWord α ρ := w.map GMove.shadow
def costR (φ : ℕ → ℝ) (w : GWord α ρ) : ℝ := (w.map (GMove.costR φ)).sum
def Proper (u : ℕ) (w : GWord α ρ) : Prop := ∀ mv ∈ w, mv.Proper u
def hist (w : GWord α ρ) (r : ℕ) : ℕ := w.shadow.hist r
@[simp] lemma shadow_cons (mv : GMove α ρ) (w : GWord α ρ) :
    shadow (mv :: w) = mv.shadow :: shadow w := rfl
lemma costR_shadow (φ : ℕ → ℝ) (w : GWord α ρ) : costR φ w = BWord.costR φ w.shadow := by
  rw [costR, BWord.costR, shadow, List.map_map]; rfl
lemma costR_append (φ) (w w' : GWord α ρ) : costR φ (w ++ w') = costR φ w + costR φ w' := by
  simp [costR]
lemma Proper.append {u} {w w' : GWord α ρ} (h : Proper u w) (h' : Proper u w') :
    Proper u (w ++ w') := fun mv hm => (List.mem_append.1 hm).elim (h mv) (h' mv)
lemma proper_nil (u : ℕ) : Proper u ([] : GWord α ρ) := fun _ h => by cases h
lemma Proper.head {u} {mv : GMove α ρ} {w} (h : Proper u (mv :: w)) : mv.Proper u := h mv (by simp)
lemma Proper.tail {u} {mv : GMove α ρ} {w} (h : Proper u (mv :: w)) : Proper u w :=
  fun m hm => h m (List.mem_cons_of_mem _ hm)
end GWord
variable [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
def permMat (G : APerm α) : CMat α := fun x y => if G.π x = y then 1 else 0
def phaseMat (z : Space α) (c : F) : CMat α := Matrix.diagonal fun x => tint (dot z x + c)
def actPointG (gr gi : Matrix ρ ρ ℚ) (x : ρ → ℂ) (r : ρ) : ℂ :=
  ∑ j, ((gr r j : ℂ) + (gi r j : ℂ) * Complex.I) * x j
def GMove.act (f : ℕ) : GMove α ρ → Data α ρ f → Data α ρ f
  | .old mv => mv.act f
  | .perm l G => roleAct f l (permMat G)
  | .phase l z c => roleAct f l (phaseMat z c)
  | .localG gr gi => point f (actPointG gr gi)
def gwalk (f : ℕ) (w : GWord α ρ) (x : Data α ρ f) : Data α ρ f :=
  w.foldl (fun y mv => mv.act f y) x
@[simp] lemma gwalk_nil (f) (x : Data α ρ f) : gwalk f ([] : GWord α ρ) x = x := rfl
lemma gwalk_cons (f) (mv : GMove α ρ) (p : GWord α ρ) (x : Data α ρ f) :
    gwalk f (mv :: p) x = gwalk f p (mv.act f x) := rfl
lemma gwalk_append (f) (p q : GWord α ρ) (x : Data α ρ f) :
    gwalk f (p ++ q) x = gwalk f q (gwalk f p x) := by
  simp only [gwalk, List.foldl_append]
def GStep (l : ρ) (M N : CMat α) (c : (ℕ → ℝ) → ℝ) : Prop :=
  ∃ (w : GWord α ρ) (U : CMat α), w.Proper (Fintype.card α) ∧ (∀ φ, w.costR φ = c φ) ∧
    U * M = N ∧ ∀ (f : ℕ) (x : Data α ρ f), gwalk f w x = roleAct f l U x
omit [Fintype ρ] [DecidableEq ρ] in
lemma mulVec_apply' {n : Type*} [Fintype n] (M : Matrix n n ℂ) (y : n → ℂ) (b : n) :
    (M *ᵥ y) b = ∑ b', M b b' * y b' := rfl
omit [Fintype ρ] [DecidableEq ρ] in
lemma matAct_perm (f : ℕ) (G : APerm α) (y : Sky α f → ℂ) (b : Sky α f) :
    matAct f (permMat G) y b = y (fun k => G.π (b k)) := by
  rw [matAct, mulVec_apply']
  simp only [digitProd_apply, permMat]
  simp [prod_delta]
omit [Fintype ρ] [DecidableEq ρ] in
lemma matAct_phase (f : ℕ) (z : Space α) (c : F) (y : Sky α f → ℂ) (b : Sky α f) :
    matAct f (phaseMat z c) y b = (∏ k, tint (dot z (b k) + c)) * y b := by
  rw [matAct, phaseMat, digitProd_diagonal, Matrix.mulVec_diagonal]
end
end PowerSaving.GenMove
namespace PowerSaving.RAM
open Binary Ty Finset GenMove
noncomputable section
universe U V
variable {ι : Type U}
lemma can_ite {m : Bool} {B : ι → ℕ} {s t : Ty} {x : ι → T s} {n W : ι → ℕ} {a b : ι → T t}
    (hn : Can m B s w x n W) (ha : Can m B s t x a W) (hb : Can m B s t x b W) :
    Can m B s t x (fun i => if n i = 0 then a i else b i) W :=
  Can.testz hn ((ha.reindex Subtype.val).cong (fun _ => rfl) fun i => (if_pos i.2).symm)
    ((hb.reindex Subtype.val).cong (fun _ => rfl) fun i => (if_neg i.2).symm)
structure GRig {α ρ : Type*} (m : Bool) (B f : ι → ℕ) (s : Ty) (x : ι → T s)
    (cl : Paint) (X : Layout α) (R : Layout ρ) (r : ℕ) (v : ∀ i, Grain α ρ r (f i)) : Prop where
  rig : RoleTapeCtx m B f s x cl X R r v
  lumT : Has m B s (a sc) x fun i => (bits (f i)).tape (fun y : Bits (f i) => lum y)
section
variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
variable {m : Bool} {B f : ι → ℕ} {s t : Ty} {x : ι → T s}
    {cl : Paint} {X : Layout α} {R : Layout ρ} {r : ℕ} {v : ∀ i, Grain α ρ r (f i)}
lemma RoleTapeCtx.ferry_perm (h : RoleTapeCtx m B f s x cl X R r v) (l : ρ) (G : APerm α)
    (q : ∀ i, Beach α ρ r (f i))
    (g : Knows m B s x fun i => (fleet X R r (f i)).loc (q i)) :
    Has m B s (c cl) x fun i => ferryM r (f i) l (permMat G) (v i) (q i) := by
  obtain ⟨h1, h2⟩ := h.addrs q g
  obtain ⟨g1, g2⟩ := h.gear.grid_fetch X r h2
  have hnew := h.read (fun i => ((q i).1, (q i).2.1, fun k => G.π ((q i).2.2 k))) h1
    (h.gear.grid_combine X r g1 (h.gear.body_set X _ fun a =>
      h.gear.body_lin X (fun y => G.π y a) (fun p p' => by simp [G.add]) _ g2))
  refine (can_ite (Can.eqbit h1 (Can.wc (R.loc l))) hnew (h.read q h1 h2)).cong
    (fun _ => rfl) (fun i => ?_)
  by_cases hl : (q i).1 = l
  · simp [hl, ferryM, roleAct, matAct_perm]
  · have hne : R.loc (q i).1 ≠ R.loc l := fun e => hl (R.inj e)
    simp [hne, hl, ferryM, roleAct]
lemma GRig.ferry_phase (h : GRig m B f s x cl X R r v) (l : ρ) (z : Space α) (c' : F)
    (q : ∀ i, Beach α ρ r (f i))
    (g : Knows m B s x fun i => (fleet X R r (f i)).loc (q i)) :
    Has m B s (c cl) x fun i => ferryM r (f i) l (phaseMat z c') (v i) (q i) := by
  have hr := h.rig
  obtain ⟨h1, h2⟩ := hr.addrs q g
  have hw0 := hr.gear.body_lin X (dot z) (dot_add_right z) _ (hr.gear.grid_fetch X r h2).2
  have hc : Knows m B s x (fun i => (bits (f i)).loc (fun _ => c')) := by
    rcases bit_cases c' with rfl | rfl
    · exact (Can.wc 0).cong (fun _ => rfl) (fun i => by simp [bits_loc])
    · exact (Can.minus hr.gear.power (Can.wc 1) hr.gear.bound).cong (fun _ => rfl)
        (fun i => by show 2 ^ f i - 1 = (bits (f i)).loc (fun _ => 1); rw [← bits_lit]; simp)
  have hlum := Can.fetch h.lumT (hr.gear.addr_xor
    (fun i => ((fun l => dot z ((q i).2.2 l)), fun _ => c')) hw0 hc)
  have hnew := Can.mul hlum (hr.read (fun i => ((q i).1, (q i).2.1, (q i).2.2)) h1 h2)
  refine (can_ite (Can.eqbit h1 (Can.wc (R.loc l))) hnew (hr.read q h1 h2)).cong
    (fun _ => rfl) (fun i => ?_)
  by_cases hl : (q i).1 = l
  · simp [hl, ferryM, roleAct, matAct_phase, lum]
  · have hne : R.loc (q i).1 ≠ R.loc l := fun e => hl (R.inj e)
    simp [hne, hl, ferryM, roleAct]
end
end
end PowerSaving.RAM
end OAI
namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset GenMove
noncomputable section
section
universe U
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
variable {ι : Type U}
variable {m : Bool} {f : ι → ℕ} {s : Ty} {x : ι → T s}
    {cl : Paint} {X : Layout α} {R : Layout ρ} {r : ℕ} {v : ∀ i, Grain α ρ r (f i)}
    {b : Bank (hatch cl) ι}
def gferry (r f : ℕ) (mv : GMove α ρ) (v : Grain α ρ r f) : Grain α ρ r f :=
  fun x => mv.act f (fun i j => v (i,x.2.1,j)) x.1 x.2.2
def gcoast (r f : ℕ) (w : GWord α ρ) (v : Grain α ρ r f) : Grain α ρ r f :=
  fun x => gwalk f w (fun i j => v (i,x.2.1,j)) x.1 x.2.2
section
variable {B : ι → ℕ}
lemma RoleTapeCtx.ferry_pointG (h : RoleTapeCtx m B f s x cl X R r v) (gr gi : Matrix ρ ρ ℚ)
    (q : ∀ i, Beach α ρ r (f i))
    (g : Knows m B s x fun i => (fleet X R r (f i)).loc (q i)) :
    Has m B s (c cl) x fun i => gferry r (f i) (.localG gr gi) (v i) (q i) :=
  (Can.add (h.ferry_point gr q g) (Can.mul h.imag (h.ferry_point gi q g))).cong (fun _ => rfl)
    (fun i => by
      simp only [applyMove, gferry, GMove.act, Move.go, point, actPoint, actPointG, add_mul,
        Finset.sum_add_distrib, Finset.mul_sum]
      congr 1; exact Finset.sum_congr rfl fun j _ => by ring)
end
end
end
end PowerSaving.RAM
namespace PowerSaving.GenMove
open Binary Matrix Finset
noncomputable section
variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
inductive Free : CMat α → Prop
  | one : Free 1
  | perm (G : APerm α) : Free (permMat G)
  | phase (z : Space α) (c : F) : Free (phaseMat z c)
  | shift (z : Space α) : Free (Binary.shift z)
  | mul {A B : CMat α} : Free A → Free B → Free (A * B)
theorem GStep.refl (l : ρ) (M : CMat α) : GStep l M M (fun _ => 0) :=
  ⟨[], 1, GWord.proper_nil _, fun φ => by simp [GWord.costR], one_mul M,
    fun f x => by funext j; simp [roleAct]⟩
theorem GStep.cast {l : ρ} {M N : CMat α} {c c'} (a : GStep l M N c) (h : ∀ φ, c φ = c' φ) :
    GStep l M N c' :=
  let ⟨w, U, hp, hc, hU, hw⟩ := a
  ⟨w, U, hp, fun φ => (hc φ).trans (h φ), hU, hw⟩
theorem GStep.trans {l : ρ} {M N K : CMat α} {c c'} (a : GStep l M N c) (b : GStep l N K c') :
    GStep l M K (fun φ => c φ + c' φ) := by
  obtain ⟨w, U, hp, hc, hU, hw⟩ := a
  obtain ⟨w', U', hp', hc', hU', hw'⟩ := b
  exact ⟨w ++ w', U' * U, hp.append hp', fun φ => by rw [GWord.costR_append, hc, hc'],
    by rw [mul_assoc, hU, hU'], fun f x => by rw [gwalk_append, hw, hw', roleAct_mul]⟩

lemma gstep_single (l : ρ) (M : CMat α) (mv : GMove α ρ) (U : CMat α) {c : (ℕ → ℝ) → ℝ}
    (hp : mv.Proper (Fintype.card α)) (hc : ∀ φ, mv.costR φ = c φ)
    (hU : ∀ f (x : Data α ρ f), mv.act f x = roleAct f l U x) : GStep l M (U * M) c :=
  ⟨[mv], U, fun m hm => (List.mem_singleton.1 hm) ▸ hp, fun φ => by simp [GWord.costR, hc],
    rfl, fun f x => by simp [gwalk, hU]⟩
theorem gstep_free {A : CMat α} (h : Free A) (l : ρ) (M : CMat α) :
    GStep l M (A * M) (fun _ => 0) := by
  induction h generalizing M with
  | one => simpa using GStep.refl l M
  | perm G => exact gstep_single l M (.perm l G) _ trivial (fun _ => rfl) (fun _ _ => rfl)
  | phase z c => exact gstep_single l M (.phase l z c) _ trivial (fun _ => rfl) (fun _ _ => rfl)
  | shift z => exact gstep_single l M (.old (.shift l z)) _ trivial (fun _ => rfl) (fun _ _ => rfl)
  | @mul A₁ B₁ _ _ ihA ihB =>
    have := ((ihB M).trans (ihA (B₁ * M))).cast (c' := fun _ => 0) (fun _ => add_zero 0)
    rwa [← mul_assoc] at this
theorem gstep_block (l : ρ) (M : CMat α) {rk : ℕ} (z : Fin rk → Space α) (ind : LinearIndependent F z)
    (h1 : 1 ≤ rk) (h2 : rk < Fintype.card α) : GStep l M (blockMat z * M) (fun φ => φ rk) :=
  gstep_single l M (.old (.block l rk z ind)) _ ⟨h1, h2⟩ (fun _ => rfl) (fun _ _ => rfl)
theorem gstep_of_factor (l : ρ) (M : CMat α) {rk : ℕ} (z : Fin rk → Space α) (ind : LinearIndependent F z)
    {A B : CMat α} (hA : Free A) (hB : Free B) (h1 : 1 ≤ rk) (h2 : rk < Fintype.card α) :
    GStep l M (A * blockMat z * B * M) (fun φ => φ rk) := by
  have := (((gstep_free hB l M).trans (gstep_block l (B * M) z ind h1 h2)).trans
    (gstep_free hA l _)).cast (c' := fun φ => φ rk) (fun φ => by simp)
  simpa only [mul_assoc] using this
lemma _root_.OAI.PowerSaving.Binary.OBase.xup_small (A : OBase α) (l : ρ) (c d : Finset α) (h : Disjoint c d)
    (h1 : 1 ≤ d.card) (h2 : d.card < Fintype.card α) :
    GStep l (frame A c) (frame A (c ∪ d)) (fun φ => φ d.card) := by
  have := GenMove.gstep_of_factor l (frame A c) (A.fam d) (A.fam_indep d)
    (GenMove.Free.shift (A.corr d)) GenMove.Free.one h1 h2
  rwa [mul_one, ← A.deltas_eq, ← A.frame_union c d h] at this
lemma add_fun_eq_dot (f : Space α → F) (hf : ∀ x y, f (x + y) = f x + f y) (x : Space α) :
    f x = dot (fun j => f (eu j)) x := by
  have hs (c : F) (y : Space α) : f (c • y) = c * f y := by
    rcases bit_cases c with rfl | rfl <;> simp [show f 0 = 0 by simpa using hf 0 0]
  conv_lhs => rw [pi_eq_sum_univ x]
  exact (map_sum (AddMonoidHom.mk' f hf) _ _).trans
    (Finset.sum_congr rfl fun a _ => (hs _ _).trans (mul_comm _ _))
end
end PowerSaving.GenMove
end OAI
namespace OAI
namespace PowerSaving.GenMove
open Binary Matrix Finset
noncomputable section
variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
def GRoute (S T : ρ → CMat α) (g : (ρ→ℂ) → (ρ→ℂ)) (c : (ℕ → ℝ) → ℝ) : Prop :=
  ∃ w : GWord α ρ, w.Proper (Fintype.card α) ∧ (∀ φ, w.costR φ = c φ) ∧
    ∀ (f : ℕ) (x : Data α ρ f), gwalk f w (multiAct f S x) = multiAct f T (point f g x)
namespace GRoute
theorem refl {S : ρ → CMat α} : GRoute S S id (fun _ => 0) :=
  ⟨[], GWord.proper_nil _, fun φ => by simp [GWord.costR], fun _ _ => rfl⟩
theorem cast {S T : ρ → CMat α} {g c c'} (h : GRoute S T g c) (hc : ∀ φ, c φ = c' φ) :
    GRoute S T g c' :=
  let ⟨w, hp, hw, hr⟩ := h
  ⟨w, hp, fun φ => (hw φ).trans (hc φ), hr⟩
theorem trans {S T U : ρ → CMat α} {g h c c'} (a : GRoute S T g c) (b : GRoute T U h c') :
    GRoute S U (h ∘ g) (fun φ => c φ + c' φ) := by
  obtain ⟨w, hp, hc, hw⟩ := a
  obtain ⟨w', hp', hc', hw'⟩ := b
  exact ⟨w ++ w', hp.append hp', fun φ => by rw [GWord.costR_append, hc, hc'],
    fun f x => by rw [gwalk_append, hw, hw']; rfl⟩
theorem gate (g : Matrix ρ ρ ℚ) (S T : ρ → CMat α) (cond : ∀ i j, g i j ≠ 0 → T i = S j) :
    GRoute S T (actPoint g) (fun _ => 0) := by
  refine ⟨[.old (.localM g)], fun m hm => by rw [List.mem_singleton.1 hm]; trivial,
    fun φ => by simp [GWord.costR, GMove.costR, GMove.shadow, BMove.costR, BMove.rk?],
    fun f x => ?_⟩
  funext r b
  simp only [gwalk, List.foldl_cons, List.foldl_nil, GMove.act, BMove.act, point, multiAct,
    actPoint, matAct, mulVec_apply', Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases hg : g r j = 0
  · simp [hg]
  · rw [cond r j hg]; ring
theorem on_role (S : ρ → CMat α) (l : ρ) (N : CMat α) {c : (ℕ → ℝ) → ℝ}
    (h : GStep l (S l) N c) : GRoute S (Function.update S l N) id c := by
  obtain ⟨w, U, hp, hc, hU, hw⟩ := h
  refine ⟨w, hp, hc, fun f x => ?_⟩
  rw [hw]; funext j
  simp only [roleAct, multiAct, Function.update_apply, point, id_eq]
  split_ifs with hj
  · subst hj; rw [matAct_mul, hU]; rfl
  · rfl
end GRoute
end
end PowerSaving.GenMove
namespace PowerSaving
namespace RAM
open Binary Matrix Finset
noncomputable section
variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
theorem multiAct_mulR (f : ℕ) (S D : ρ → CMat α) (x : Data α ρ f) :
    multiAct f (fun r => S r * D r) x = multiAct f S (multiAct f D x) := by
  funext r; simp only [multiAct, matAct_mul]
end
end RAM
end PowerSaving
namespace PowerSaving.GenMove
open Binary Matrix Finset
noncomputable section
section
variable {τ : Type*} [Fintype τ] [DecidableEq τ]
lemma actPointG_eq (M N : Matrix τ τ ℚ) (y : τ → ℂ) (r : τ) :
    actPointG M N y r = actPoint M y r + Complex.I * actPoint N y r := by
  simp only [actPointG, actPoint, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1; exact Finset.sum_congr rfl fun j _ => by ring
lemma actPoint_sub (M N : Matrix τ τ ℚ) (y : τ → ℂ) (r : τ) :
    actPoint (M - N) y r = actPoint M y r - actPoint N y r := by
  simp only [actPoint, Matrix.sub_apply, Rat.cast_sub, sub_mul, Finset.sum_sub_distrib]
end
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] [Fintype σ]
  [DecidableEq σ]
def GMove.over (e : ρ ↪ σ) : GMove α ρ → GMove α σ
  | .old m => .old (m.over e)
  | .perm l G => .perm (e l) G
  | .phase l z c => .phase (e l) z c
  | .localG gr gi => .localG (wide e gr) (wide e gi - wide e 0)
lemma act_over (e : ρ ↪ σ) (mv : GMove α ρ) (f : ℕ) (x : Data α σ f) :
    (mv.over e).act f x ∘ e = mv.act f (x ∘ e) := by
  funext i b
  cases mv with
  | old m =>
    cases m with
    | localM M => exact wide_in e M i (fun r => x r b)
    | shift r z => simp [GMove.over, BMove.over, GMove.act, BMove.act, roleAct, e.injective.eq_iff]
    | block r k z ind =>
      simp [GMove.over, BMove.over, GMove.act, BMove.act, roleAct, e.injective.eq_iff]
  | perm r G => simp [GMove.over, GMove.act, roleAct, e.injective.eq_iff]
  | phase r z c => simp [GMove.over, GMove.act, roleAct, e.injective.eq_iff]
  | localG gr gi =>
    show actPointG (wide e gr) (wide e gi - wide e 0) (fun r => x r b) (e i) =
      actPointG gr gi (fun r => x (e r) b) i
    rw [actPointG_eq, actPointG_eq, actPoint_sub, wide_in, wide_in, wide_in]
    simp [actPoint]
lemma act_out (e : ρ ↪ σ) (mv : GMove α ρ) (f : ℕ) (x : Data α σ f) {i : σ}
    (hi : i ∉ covered e) : (mv.over e).act f x i = x i := by
  have hne : ∀ r, i ≠ e r := fun r h' => hi ((cover_iff e i).2 ⟨r, h'.symm⟩)
  funext b
  cases mv with
  | old m =>
    cases m with
    | localM M => exact wide_out e M (fun r => x r b) hi
    | shift r z => simp [GMove.over, BMove.over, GMove.act, BMove.act, roleAct, hne]
    | block r k z ind => simp [GMove.over, BMove.over, GMove.act, BMove.act, roleAct, hne]
  | perm r G => simp [GMove.over, GMove.act, roleAct, hne]
  | phase r z c => simp [GMove.over, GMove.act, roleAct, hne]
  | localG gr gi =>
    show actPointG (wide e gr) (wide e gi - wide e 0) (fun r => x r b) i = x i b
    rw [actPointG_eq, actPoint_sub, wide_out _ _ _ hi, wide_out _ _ _ hi, wide_out _ _ _ hi]
    simp
theorem gwalk_over (e : ρ ↪ σ) (p : GWord α ρ) (f : ℕ) (x : Data α σ f) :
    gwalk f (p.map (GMove.over e)) x ∘ e = gwalk f p (x ∘ e) := by
  induction p generalizing x with
  | nil => rfl
  | cons mv p ih => rw [List.map_cons, gwalk_cons, gwalk_cons, ih, act_over]
theorem gwalk_out (e : ρ ↪ σ) (p : GWord α ρ) (f : ℕ) (x : Data α σ f) {i : σ} (h : i ∉ covered e) :
    gwalk f (p.map (GMove.over e)) x i = x i := by
  induction p generalizing x with
  | nil => rfl
  | cons mv p ih => rw [List.map_cons, gwalk_cons, ih, act_out e mv f x h]
lemma over_proper (e : ρ ↪ σ) (mv : GMove α ρ) (u : ℕ) : (mv.over e).Proper u ↔ mv.Proper u := by
  rcases mv with ((_|_|_)|_|_|_) <;> exact Iff.rfl
lemma over_costR (e : ρ ↪ σ) (mv : GMove α ρ) (φ : ℕ → ℝ) : (mv.over e).costR φ = mv.costR φ := by
  rcases mv with ((_|_|_)|_|_|_) <;> rfl
lemma proper_map (e : ρ ↪ σ) {u : ℕ} {w : GWord α ρ} (h : w.Proper u) :
    GWord.Proper u (w.map (GMove.over e)) := fun mv hm => by
  obtain ⟨m0, hm0, rfl⟩ := List.mem_map.1 hm
  exact (over_proper e m0 u).2 (h m0 hm0)
lemma costR_map (e : ρ ↪ σ) (w : GWord α ρ) (φ : ℕ → ℝ) :
    GWord.costR φ (w.map (GMove.over e)) = w.costR φ := by
  simp [GWord.costR, Function.comp_def, over_costR]
theorem GRoute.parallel {J : Type*} [Fintype J] [DecidableEq J] (e : J → ρ ↪ σ)
    (dis : ∀ i j, i ≠ j → ∀ r ∈ covered (e i), r ∉ covered (e j))
    {S T : σ → CMat α} {d : J → (ℕ → ℝ) → ℝ} {g : (σ→ℂ)→(σ→ℂ)} {h : J → (ρ→ℂ) → (ρ→ℂ)}
    (q : ∀ i, GRoute (S ∘ e i) (T ∘ e i) (h i) (d i))
    (hin : ∀ i x, (g x) ∘ e i = h i (x ∘ e i)) (hout : ∀ x r, (∀ i, r∉covered (e i)) → g x r=x r)
    (he : ∀ r, (∀ i, r∉covered (e i)) → S r=T r) : GRoute S T g (fun φ => ∑ i, d i φ) := by
  choose wd hwp hwc hww using q
  have key : ∀ s : Finset J, ∃ w : GWord α σ, w.Proper (Fintype.card α) ∧
      (∀ φ, w.costR φ = ∑ i ∈ s, d i φ) ∧ ∀ f (y : Data α σ f),
      (∀ i ∈ s, gwalk f w y ∘ e i = gwalk f (wd i) (y ∘ e i)) ∧
      (∀ r, (∀ i ∈ s, r ∉ covered (e i)) → gwalk f w y r = y r) := by
    intro s
    refine Finset.induction_on s ⟨[], GWord.proper_nil _, fun φ => by simp [GWord.costR],
      fun f y => ⟨by simp, fun r _ => rfl⟩⟩ ?_
    rintro j s hj ⟨w, hp, hc, hw⟩
    refine ⟨(wd j).map (GMove.over (e j)) ++ w, (proper_map _ (hwp j)).append hp, fun φ => ?_,
      fun f y => ⟨fun i hi => ?_, fun r hr => ?_⟩⟩
    · rw [GWord.costR_append, costR_map, hwc, hc, Finset.sum_insert hj]
    · rw [gwalk_append]
      rcases Finset.mem_insert.1 hi with hij | hi
      · rw [hij]; funext k
        have hk : ∀ i' ∈ s, e j k ∉ covered (e i') := fun i' hi' =>
          dis j i' (fun h' => hj (h' ▸ hi')) _ ((cover_iff _ _).2 ⟨k, rfl⟩)
        rw [Function.comp_apply, (hw f _).2 _ hk]
        exact congrFun (gwalk_over (e j) (wd j) f y) k
      · rw [(hw f _).1 i hi]; congr 1; funext k
        exact gwalk_out (e j) (wd j) f y
          (dis i j (fun h' => hj (h' ▸ hi)) _ ((cover_iff _ _).2 ⟨k, rfl⟩))
    · rw [gwalk_append, (hw f _).2 r (fun i hi => hr i (Finset.mem_insert_of_mem hi))]
      exact gwalk_out _ _ _ _ (hr j (Finset.mem_insert_self j s))
  obtain ⟨w, hp, hc, hw⟩ := key Finset.univ
  refine ⟨w, hp, hc, fun f x => funext fun r => ?_⟩
  by_cases hr : ∃ i, r ∈ covered (e i)
  · obtain ⟨i, hi⟩ := hr
    obtain ⟨k, rfl⟩ := (cover_iff _ _).1 hi
    have h1 := congrFun ((hw f (multiAct f S x)).1 i (Finset.mem_univ _)) k
    rw [Function.comp_apply] at h1
    rw [h1]
    refine (congrFun (hww i f (x ∘ e i)) k).trans ?_
    show matAct f (T (e i k)) _ = matAct f (T (e i k)) _
    congr 1; funext b; exact (congrFun (hin i (fun r => x r b)) k).symm
  · push_neg at hr
    rw [(hw f _).2 r (fun i _ => hr i)]
    show matAct f (S r) (x r) = matAct f (T r) (point f g x r)
    rw [he r hr]; congr 1; funext b; exact (hout (fun r => x r b) r hr).symm
theorem GRoute.lift (e : ρ ↪ σ) {S T : σ → CMat α} {g : (σ→ℂ) → (σ→ℂ)} {h : (ρ→ℂ) → (ρ→ℂ)}
    {c : (ℕ → ℝ) → ℝ} (q : GRoute (S ∘ e) (T ∘ e) h c)
    (hin : ∀ x, (g x) ∘ e = h (x ∘ e)) (hout : ∀ x i, i∉covered e → g x i=x i)
    (he : ∀ i, i ∉ covered e → S i = T i) : GRoute S T g c :=
  (GRoute.parallel (J := Unit) (fun _ => e) (fun i j hij => absurd (Subsingleton.elim i j) hij)
    (d := fun _ => c) (fun _ => q) (fun _ x => hin x) (fun x r hr => hout x r (hr ()))
    (fun r hr => he r (hr ()))).cast (fun φ => by simp)
end
end PowerSaving.GenMove
end OAI
namespace OAI
namespace PowerSaving.LiveKernel
open Binary GenMove Matrix Finset
noncomputable section
section Mats
variable {α : Type*} [Fintype α] [DecidableEq α]
def bph {r : ℕ} (z : Fin r → Space α) (x : Space α) : ℂ := ∏ i, tint (dot (z i) x)
lemma blockMat_eq_wrap {r : ℕ} (z : Fin r → Space α) : blockMat z = wrap (bph z) :=
  blockMat_wrap z
lemma blockMat_congr {r r' : ℕ} (z : Fin r → Space α) (z' : Fin r' → Space α)
    (h : ∀ x, bph z x = bph z' x) : blockMat z = blockMat z' := by
  rw [blockMat_eq_wrap, blockMat_eq_wrap]; congr 1; funext x; exact h x
lemma blockMat_comm {r r' : ℕ} (z : Fin r → Space α) (z' : Fin r' → Space α) :
    blockMat z * blockMat z' = blockMat z' * blockMat z := by
  rw [blockMat_eq_wrap, blockMat_eq_wrap]; exact wrap_comm _ _
theorem split_block {a b : ℕ} (z : Fin (a+b) → Space α) :
    blockMat z = blockMat (fun i : Fin a => z (Fin.castAdd b i)) *
      blockMat (fun j : Fin b => z (Fin.natAdd a j)) := by
  rw [blockMat_eq_wrap, blockMat_eq_wrap, blockMat_eq_wrap, wrap_mul]
  congr 1; funext x; exact Fin.prod_univ_add (fun i => tint (dot (z i) x))
end Mats
section Words
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
def GLiveKernelM (e : σ → ρ) (T : σ → CMat α) (w : GWord α ρ) : Prop :=
  ∀ f (v : Data α ρ f), (∀ s, (∀ l, e l ≠ s) → v s = 0) →
    ∀ l, gwalk f w v (e l) = matAct f (T l) (v (e l))
theorem GLiveKernelM.congr {e : σ → ρ} {T T' : σ → CMat α} {w : GWord α ρ}
    (h : GLiveKernelM e T w) (hT : ∀ l, T l = T' l) : GLiveKernelM e T' w :=
  fun f v hv l => by rw [← hT]; exact h f v hv l
theorem GLiveKernelM.of_gwalk {e : σ → ρ} {T : σ → CMat α} {w w' : GWord α ρ}
    (h : GLiveKernelM e T w) (hw : ∀ f (x : Data α ρ f), gwalk f w x = gwalk f w' x) :
    GLiveKernelM e T w' :=
  fun f v hv l => by rw [← hw]; exact h f v hv l
noncomputable def rmat : GMove α ρ → ρ → CMat α
  | .old (.shift r z), j => if j = r then Binary.shift z else 1
  | .old (.block r _ z _), j => if j = r then blockMat z else 1
  | .perm r P, j => if j = r then permMat P else 1
  | .phase r z c, j => if j = r then phaseMat z c else 1
  | .old (.localM _), _ => 1
  | .localG _ _, _ => 1
def IsLocal : GMove α ρ → Prop
  | .old (.localM _) => False
  | .localG _ _ => False
  | _ => True
def RoleLocal (w : GWord α ρ) : Prop := ∀ mv ∈ w, IsLocal mv
noncomputable def roleProd : GWord α ρ → ρ → CMat α
  | [], _ => 1
  | mv :: rest, j => roleProd rest j * rmat mv j
@[simp] lemma roleProd_nil (j : ρ) : roleProd ([] : GWord α ρ) j = 1 := rfl
lemma roleProd_cons (mv : GMove α ρ) (w : GWord α ρ) (j : ρ) :
    roleProd (mv :: w) j = roleProd w j * rmat mv j := rfl
lemma act_local (f : ℕ) (mv : GMove α ρ) (h : IsLocal mv) (x : Data α ρ f) (j : ρ) :
    mv.act f x j = matAct f (rmat mv j) (x j) := by
  rcases mv with ((g|⟨r, z⟩|⟨r, k, z, ind⟩)|⟨r, P⟩|⟨r, z, c⟩|⟨gr, gi⟩)
  · exact False.elim h
  all_goals first
    | exact False.elim h
    | (simp only [GMove.act, BMove.act, roleAct, rmat]; split_ifs <;> simp)
theorem gwalk_local (f : ℕ) (w : GWord α ρ) (hw : RoleLocal w) (x : Data α ρ f) (j : ρ) :
    gwalk f w x j = matAct f (roleProd w j) (x j) := by
  induction w generalizing x with
  | nil => simp
  | cons mv w ih =>
    rw [gwalk_cons, ih (fun m hm => hw m (List.mem_cons_of_mem _ hm)),
      act_local f mv (hw mv (by simp)), matAct_mul, roleProd_cons]
theorem GLiveKernelM.append_local {e : σ → ρ} {T : σ → CMat α} {w : GWord α ρ}
    (h : GLiveKernelM e T w) (t : GWord α ρ) (ht : RoleLocal t) :
    GLiveKernelM e (fun l => roleProd t (e l) * T l) (w ++ t) := by
  intro f v hv l
  rw [gwalk_append, gwalk_local f t ht, h f v hv l, matAct_mul]
def OnRole (e : σ → ρ) (mk : σ → GMove α ρ) (M : σ → CMat α) : Prop :=
  ∀ l, IsLocal (mk l) ∧ ∀ j, rmat (mk l) j = if j = e l then M l else 1
lemma roleProd_map_e [DecidableEq σ] {e : σ → ρ} (he : Function.Injective e)
    {mk : σ → GMove α ρ} {M : σ → CMat α} (hm : OnRole e mk M) (L : List σ) (hL : L.Nodup) (l : σ) :
    roleProd (L.map mk) (e l) = if l ∈ L then M l else 1 := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.nodup_cons] at hL
    rw [List.map_cons, roleProd_cons, ih hL.2, (hm a).2 (e l)]
    by_cases hla : l = a
    · subst hla; simp [hL.1]
    · simp [hla, he.ne hla]
end Words
end
end PowerSaving.LiveKernel
end OAI

namespace OAI
namespace PowerSaving
namespace StageBox
noncomputable section
open Binary Matrix Finset RAM
section Single
variable {H : Type} [Fintype H] [DecidableEq H]
def tt (z : Space H) : Matrix H H F := fun i j => z i * z j
lemma mat_empty (A : OBase H) : A.mat ∅ = 0 := by ext i j; simp [OBase.mat]
lemma mat_single (A : OBase H) (k : H) : A.mat {k} = tt (A.v k) := by
  ext i j; simp [OBase.mat, tt]
lemma mat_compl_single (A : OBase H) (k : H) : A.mat (univ \ {k}) = 1 + tt (A.v k) := by
  have h2 : ∀ a b : F, a - b = a + b := by decide
  rw [A.mat_sub univ {k} (subset_univ _), OBase.mat_univ, mat_single]
  ext i j; simp only [Matrix.sub_apply, Matrix.add_apply, h2]
lemma exists_base_one (z : Space H) (hz : dot z z = 1) (p : H) (hp : z p = 0) :
    ∃ (A : OBase H) (k : H), A.v k = z :=
  ⟨_, p, OBase.adapt_pivot (OBase.canonical H) p z hz (by simp [OBase.canonical, hp])⟩
end Single
def frameM {α : Type*} [Fintype α] [DecidableEq α] (M : Matrix α α F) : CMat α :=
  wrap fun x => lum (M *ᵥ x)
lemma frame_eq {α : Type*} [Fintype α] [DecidableEq α] (A : OBase α) (s : Finset α) :
    frame A s = frameM (A.mat s) := by
  have h : ∀ x, A.proj s x = A.mat s *ᵥ x := fun x => funext fun i => by rw [A.proj_apply]; rfl
  simp only [frame, frameM, h]
section Ap
variable {A B C : Type*} [Fintype B] [Fintype C]
def ap (M : Matrix A B ℚ) (u : B → ℂ) : A → ℂ := fun i => ∑ j, (M i j : ℂ) * u j
end Ap
section Box
variable (T Sl C : Type)
abbrev Box := (T ⊕ T) ⊕ (Sl ⊕ C)
variable {T Sl C}
def bX (t : T) : Box T Sl C := .inl (.inl t)
def bY (t : T) : Box T Sl C := .inl (.inr t)
def bS (q : Sl) : Box T Sl C := .inr (.inl q)
def bC (c : C) : Box T Sl C := .inr (.inr c)
def stamp {β : Type*} (x y : T → β) (s : Sl → β) (c : C → β) : Box T Sl C → β :=
  Sum.elim (Sum.elim x y) (Sum.elim s c)
end Box
end
end StageBox
namespace RankCost
noncomputable section
open Binary Matrix Finset RAM StageBox
def bcost (φ : ℕ → ℝ) (q : ℕ) : ℝ := if q = 0 then 0 else φ q
def rcost (φ : ℕ → ℝ) (l : List ℕ) : ℝ := (l.map (bcost φ)).sum
lemma bcost_zero (φ : ℕ → ℝ) : bcost φ 0 = 0 := by simp [bcost]
lemma bcost_pos (φ : ℕ → ℝ) {q : ℕ} (h : q ≠ 0) : bcost φ q = φ q := by simp [bcost, h]
lemma rcost_nil (φ : ℕ → ℝ) : rcost φ [] = 0 := by simp [rcost]
lemma rcost_cons (φ : ℕ → ℝ) (a : ℕ) (l : List ℕ) : rcost φ (a :: l) = bcost φ a + rcost φ l := by
  simp [rcost]
lemma rcost_append (φ : ℕ → ℝ) (l l' : List ℕ) : rcost φ (l ++ l') = rcost φ l + rcost φ l' := by
  simp [rcost]
lemma rcost_single (φ : ℕ → ℝ) (a : ℕ) : rcost φ [a] = bcost φ a := by simp [rcost]
structure XMap (H α : Type) [Fintype H] [DecidableEq H] [Fintype α] [DecidableEq α] where
  Φ : Matrix H H F → CMat α
end
end RankCost
end PowerSaving
end OAI
