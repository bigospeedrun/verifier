--might be  containing modified Apache-2.0 codes pieces from one or several sources; notices and credits: Credits.lean
import Submission.Engine.Moves

namespace OAI
namespace PowerSaving.GenMove
open Binary Matrix Finset Complex
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

def apId (α : Type*) : APerm α where
  π := Equiv.refl _
  add _ _ := rfl
def apInv (G : APerm α) : APerm α where
  π := G.π.symm
  add x y := G.π.injective (by simp only [Equiv.apply_symm_apply, G.add])
def apComp (G H : APerm α) : APerm α where
  π := G.π.trans H.π
  add x y := by simp only [Equiv.trans_apply, G.add, H.add]

def mkAP (f : Space α → Space α) (hf : ∀ x y, f (x + y) = f x + f y) (hk : ∀ x, f x = 0 → x = 0) :
    APerm α where
  π := Equiv.ofBijective f (Finite.injective_iff_bijective.mp fun x y h => by
    have := hk (x + y) (by rw [hf, h, binary_cancel])
    calc x = x + y + y := by rw [add_assoc, binary_cancel, add_zero]
      _ = y := by rw [this, zero_add])
  add := hf

lemma APerm.map_zero' (G : APerm α) : G.π 0 = 0 := by simpa using G.add 0 0

lemma F_add_self : ∀ a : F, a + a = 0 := by decide
lemma F_eq_add : ∀ a b : F, a = a + b ↔ b = 0 := by decide
lemma sgn0 : sign 0 = 1 := rfl
lemma sgn1 : sign 1 = -1 := rfl

lemma inv_cancel_left {A B : CMat α} (h : A * B = 1) (M : CMat α) : A * (B * M) = M := by
  rw [← Matrix.mul_assoc, h, Matrix.one_mul]

lemma permMat_mul_apply (G : APerm α) (M : CMat α) (x y : Space α) :
    (permMat G * M) x y = M (G.π x) y := by
  simp [Matrix.mul_apply, permMat]

lemma permMat_inv_mul (G : APerm α) : permMat (apInv G) * permMat G = 1 := by
  ext x y
  rw [permMat_mul_apply]
  simp [permMat, apInv, Matrix.one_apply]

lemma lum_inv (y : Space α) : (lum y)⁻¹ = lum y * lum y * lum y := by
  refine (eq_inv_of_mul_eq_one_left ?_).symm
  have h1 := lum_sq y
  have h2 := sign_sq (dot y y)
  linear_combination (lum y * lum y + sign (dot y y)) * h1 + h2

lemma free_lum_comp (q : Space α → Space α) (hq : ∀ x y, q (x + y) = q x + q y) :
    Free (diagonal fun x => lum (q x)) := by
  suffices h : ∀ s : Finset α, Free (diagonal fun x => ∏ i ∈ s, tint (q x i)) from h univ
  intro s
  refine Finset.induction_on s ?_ ?_
  · simpa using (Free.one : Free (1 : CMat α))
  · intro a s ha ih
    have e : (diagonal fun x => ∏ i ∈ insert a s, tint (q x i)) =
        phaseMat (fun j => q (eu j) a) 0 * diagonal fun x => ∏ i ∈ s, tint (q x i) := by
      rw [phaseMat, Matrix.diagonal_mul_diagonal]
      congr 1
      funext x
      have h := add_fun_eq_dot (fun x => q x a) (fun x y => by simp only [hq, Pi.add_apply]) x
      rw [Finset.prod_insert ha, add_zero, ← h]
    rw [e]
    exact (Free.phase _ _).mul ih

theorem free_inv {A : CMat α} (h : Free A) : ∃ A', Free A' ∧ A' * A = 1 ∧ A * A' = 1 := by
  induction h with
  | one => exact ⟨1, .one, Matrix.one_mul 1, Matrix.one_mul 1⟩
  | perm G => exact ⟨_, .perm (apInv G), permMat_inv_mul G, permMat_inv_mul (apInv G)⟩
  | phase z c =>
    refine ⟨_, ((Free.phase z c).mul (.phase z c)).mul (.phase z c), ?_, ?_⟩
    all_goals
      simp only [phaseMat, Matrix.diagonal_mul_diagonal]
      rw [← Matrix.diagonal_one]
      congr 1
      funext x
      have h1 := tint_sq (dot z x + c)
      have h2 := sign_sq (dot z x + c)
      linear_combination (tint (dot z x + c) * tint (dot z x + c) + sign (dot z x + c)) * h1 + h2
  | shift z => exact ⟨_, .shift z, shift_sq z, shift_sq z⟩
  | mul _ _ ihA ihB =>
    obtain ⟨A', hA', eA, eA'⟩ := ihA
    obtain ⟨B', hB', eB, eB'⟩ := ihB
    exact ⟨B' * A', hB'.mul hA', by rw [Matrix.mul_assoc, inv_cancel_left eA, eB],
      by rw [Matrix.mul_assoc, inv_cancel_left eB', eA']⟩

lemma free_scalar (n : ℕ) : Free (I ^ n • (1 : CMat α)) := by
  have hph : phaseMat (0 : Space α) 1 = I • 1 := by
    ext x y
    by_cases h : x = y <;> simp [phaseMat, Matrix.diagonal_apply, Matrix.one_apply, h, dot, tint, one_ne]
  induction n with
  | zero => simpa using (Free.one : Free (1 : CMat α))
  | succ n ih =>
    have e : I ^ (n + 1) • (1 : CMat α) = phaseMat 0 1 * (I ^ n • 1) := by
      rw [hph, Matrix.smul_mul, Matrix.one_mul, smul_smul, pow_succ']
    rw [e]
    exact (Free.phase 0 1).mul ih

def coordFrame (s : Finset α) : CMat α := wrap fun x => ∏ k ∈ s, tint (x k)
def phasedPerm (G : APerm α) : CMat α := fun x y => if G.π x = y then lum x / lum y else 0
def coreFrame (G : APerm α) (s : Finset α) : CMat α := phasedPerm G * coordFrame s * phasedPerm (apInv G)
def InSub (G : APerm α) (s : Finset α) (x : Space α) : Prop := ∀ k, k ∉ s → G.π x k = 0
instance (G : APerm α) (s : Finset α) (x : Space α) : Decidable (InSub G s x) := by
  unfold InSub; infer_instance

lemma insub_zero (G : APerm α) (s : Finset α) : InSub G s 0 := fun k _ => by
  rw [APerm.map_zero']; rfl

theorem free_kg (G : APerm α) : Free (phasedPerm G) := by
  have hD := free_lum_comp (α := α) id fun _ _ => rfl
  have e : phasedPerm G = diagonal (fun x => lum (id x)) * permMat G *
      (diagonal (fun x => lum (id x)) * diagonal (fun x => lum (id x)) * diagonal (fun x => lum (id x))) := by
    ext x y
    simp only [phasedPerm, permMat, id, Matrix.diagonal_mul_diagonal, Matrix.mul_diagonal,
      Matrix.diagonal_mul]
    split_ifs with h
    · rw [div_eq_mul_inv, lum_inv]; ring
    · simp
  rw [e]
  exact (hD.mul (.perm G)).mul ((hD.mul hD).mul hD)

lemma kg_comp {G H K : APerm α} (h : ∀ x, K.π x = H.π (G.π x)) :
    phasedPerm G * phasedPerm H = phasedPerm K := by
  ext x z
  simp only [phasedPerm, Matrix.mul_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte, h]
  split_ifs
  · have := lum_nonzero (G.π x)
    field_simp
  · simp

lemma kg_id : phasedPerm (apId α) = 1 := by
  ext x y
  by_cases h : x = y <;> simp [phasedPerm, apId, Matrix.one_apply, h, lum_nonzero]

lemma kg_mul_inv (G : APerm α) : phasedPerm G * phasedPerm (apInv G) = 1 := by
  rw [kg_comp (K := apId α) fun x => by simp [apId, apInv], kg_id]

lemma kg_inv_mul (G : APerm α) : phasedPerm (apInv G) * phasedPerm G = 1 := kg_mul_inv (apInv G)

lemma conj_apply (G : APerm α) (M : CMat α) (x y : Space α) :
    (phasedPerm G * M * phasedPerm (apInv G)) x y =
      lum x / lum (G.π x) * M (G.π x) (G.π y) * (lum (G.π y) / lum y) := by
  have h1 : ∀ b, (phasedPerm G * M) x b = lum x / lum (G.π x) * M (G.π x) b := fun b => by
    simp [Matrix.mul_apply, phasedPerm]
  rw [Matrix.mul_apply]
  simp [h1, phasedPerm, apInv, Equiv.symm_apply_eq]

lemma pk_empty : coordFrame (∅ : Finset α) = 1 := by
  simp only [coordFrame, Finset.prod_empty]; exact wrap_one

lemma pk_union (s t : Finset α) (h : Disjoint s t) : coordFrame (s ∪ t) = coordFrame s * coordFrame t := by
  simp only [coordFrame, wrap_mul, Finset.prod_union h]

lemma pk_sdiff {s t : Finset α} (h : s ⊆ t) : coordFrame t = coordFrame (t \ s) * coordFrame s := by
  rw [← pk_union _ _ Finset.sdiff_disjoint, Finset.sdiff_union_of_subset h]

lemma pk_eq_blockMat (d : Finset α) : coordFrame d = blockMat ((OBase.canonical α).fam d) := by
  rw [OBase.blockMat_fam, coordFrame]
  congr 1
  funext x
  exact Finset.prod_congr rfl fun i _ => by rw [show (OBase.canonical α).v i = eu i from rfl, dot_eu_left]

theorem core_nested (G : APerm α) {s t : Finset α} (h : s ⊆ t) :
    coreFrame G t = phasedPerm G * blockMat ((OBase.canonical α).fam (t \ s)) * phasedPerm (apInv G) * coreFrame G s := by
  rw [← pk_eq_blockMat, coreFrame, coreFrame, pk_sdiff h]
  simp only [Matrix.mul_assoc, inv_cancel_left (kg_inv_mul G)]

lemma core_insert (G : APerm α) {i : α} {s : Finset α} (hi : i ∉ s) :
    coreFrame G (insert i s) = phasedPerm G * dir (eu i) * phasedPerm (apInv G) * coreFrame G s := by
  have e : insert i s \ s = {i} := by
    ext k; by_cases hk : k = i <;> simp [hk, hi]
  have hd : coordFrame {i} = dir (eu i) := by
    rw [dir_phase, coordFrame]
    congr 1
    funext x
    rw [Finset.prod_singleton, dot_eu_left]
  rw [core_nested G (Finset.subset_insert i s), ← pk_eq_blockMat, e, hd]

lemma little_entry (i j : F) : littleC i j = ca / tint (i + j) := by
  have h : ca / I = cb := by
    rw [div_eq_iff Complex.I_ne_zero]
    simp only [ca, cb]
    linear_combination (1 / 2 : ℂ) * Complex.I_sq
  rcases bit_cases i with rfl | rfl <;> rcases bit_cases j with rfl | rfl <;>
    simp (config := { decide := true }) only [littleC, tint, ↓reduceIte, div_one] <;> exact h.symm

lemma pk_digit (s : Finset α) :
    coordFrame s = digitProd fun k => if k ∈ s then littleC else (1 : Matrix F F ℂ) := by
  refine wrap_of _ _ ?_
  have hd : (diagonal fun x : Space α => ∏ k ∈ s, tint (x k)) =
      digitProd fun k => diagonal (if k ∈ s then tint else fun _ => 1) := by
    rw [digitProd_diagonal]
    congr 1
    funext x
    simp only [ite_apply]
    rw [Finset.prod_ite_mem, Finset.univ_inter]
  rw [wal, hd, digitProd_mul, digitProd_mul]
  congr 1
  funext k
  split_ifs
  · exact little_phase
  · rw [Matrix.one_mul, Matrix.diagonal_one, Matrix.mul_one]

lemma pk_apply (s : Finset α) (a b : Space α) :
    coordFrame s a b = if (∀ k, k ∉ s → a k = b k) then ca ^ s.card / lum (a + b) else 0 := by
  rw [pk_digit, digitProd_apply]
  split_ifs with h
  · rw [show ca ^ s.card / lum (a + b) = ∏ k, (if k ∈ s then ca else 1) / tint (a k + b k) by
      rw [Finset.prod_div_distrib, Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]; rfl]
    refine Finset.prod_congr rfl fun k _ => ?_
    split_ifs with hk
    · exact little_entry _ _
    · rw [h k hk, Matrix.one_apply_eq, F_add_self]; simp [tint]
  · obtain ⟨k, hk, hab⟩ : ∃ k, k ∉ s ∧ a k ≠ b k := by push_neg at h; exact h
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by rw [if_neg hk, Matrix.one_apply_ne hab])

lemma card_insub (G : APerm α) (s : Finset α) : Fintype.card {x // InSub G s x} = 2 ^ s.card := by
  let e : {y : Space α // ∀ k, k ∉ s → y k = 0} ≃ (s → F) :=
    { toFun := fun y k => y.1 k
      invFun := fun c => ⟨fun k => if h : k ∈ s then c ⟨k, h⟩ else 0, fun k hk => dif_neg hk⟩
      left_inv := fun y => Subtype.ext (funext fun k => by by_cases h : k ∈ s <;> simp [h, y.2 k])
      right_inv := fun c => funext fun k => dif_pos k.2 }
  rw [Fintype.card_congr (G.π.subtypeEquiv fun x => Iff.rfl :
    {x // InSub G s x} ≃ {y : Space α // ∀ k, k ∉ s → y k = 0}), Fintype.card_congr e]
  simp

theorem same_card {G G' : APerm α} {s s' : Finset α}
    (h : ∀ x, InSub G s x ↔ InSub G' s' x) : s.card = s'.card := by
  have := Fintype.card_congr (Equiv.subtypeEquivRight h)
  rw [card_insub, card_insub] at this
  exact Nat.pow_right_injective le_rfl this

lemma insub_iff_of_card {G G' : APerm α} {s s' : Finset α} (h : ∀ x, InSub G s x → InSub G' s' x)
    (hc : s.card = s'.card) (x : Space α) : InSub G s x ↔ InSub G' s' x := by
  have hsub : univ.filter (InSub G s) ⊆ univ.filter (InSub G' s') := fun y hy => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢; exact h y hy
  have heq := Finset.eq_of_subset_of_card_le hsub (by
    rw [← Fintype.card_subtype, ← Fintype.card_subtype, card_insub, card_insub, hc])
  refine ⟨h x, fun hx => ?_⟩
  have : x ∈ univ.filter (InSub G' s') := by simp [hx]
  rw [← heq] at this
  simpa using this

def coordPerm (A : OBase α) : APerm α where
  π := { toFun := fun x k => dot (A.v k) x
         invFun := fun c => ∑ k, c k • A.v k
         left_inv := by
           intro x
           show ∑ k, dot (A.v k) x • A.v k = x
           exact A.proj_univ x
         right_inv := by
           intro c
           funext j
           show dot (A.v j) (∑ k, c k • A.v k) = c j
           rw [dot_sum]
           simp [A.rows] }
  add := by
    intro x y
    funext k
    show dot (A.v k) (x + y) = dot (A.v k) x + dot (A.v k) y
    exact dot_add_right _ _ _

def pmap (H : APerm α) (s : Finset α) (x : Space α) : Space α :=
  fun k => if k ∈ s then dot (H.π x) (H.π (eu k)) else x k

lemma rep_aux (H : APerm α) (s s' : Finset α) (hH : ∀ y, (∀ k, k ∉ s → y k = 0) ↔ InSub H s' y) :
    ∃ M, Free M ∧ coreFrame H s' = M * coordFrame s := by
  have hp_add : ∀ x y, pmap H s (x + y) = pmap H s x + pmap H s y := by
    intro x y; funext k; by_cases hk : k ∈ s <;> simp [pmap, hk, H.add]
  have key : ∀ x u, (∀ k, k ∉ s → u k = 0) → dot (pmap H s x) u = dot (H.π x) (H.π u) := by
    intro x u hu
    have e := add_fun_eq_dot (fun u => dot (H.π x) (H.π u)) (fun a b => by simp [H.add]) u
    rw [e]
    show ∑ i, pmap H s x i * u i = ∑ i, dot (H.π x) (H.π (eu i)) * u i
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j ∈ s
    · simp [pmap, hj]
    · simp [hu j hj]
  have hk0 : ∀ x, pmap H s x = 0 → x = 0 := by
    intro x hx
    have hs : ∀ k, k ∉ s → x k = 0 := fun k hk => by simpa [pmap, hk] using congrFun hx k
    apply H.π.injective
    rw [APerm.map_zero']
    funext j
    by_cases hj : j ∈ s'
    · obtain ⟨v, hv'⟩ : ∃ v, H.π v = eu j := ⟨_, H.π.apply_symm_apply _⟩
      have hv : ∀ k, k ∉ s → v k = 0 := (hH v).2 fun k hk => by
        rw [hv']; show (if j = k then (1 : F) else 0) = 0; exact if_neg fun e => hk (by simpa [e] using hj)
      rw [Pi.zero_apply, ← dot_eu_left (H.π x) j, dot_symm, ← hv', ← key x v hv, hx]
      simp [dot]
    · exact (hH x).1 hs j hj
  have hcard := same_card (G := apId α) (G' := H) hH
  refine ⟨diagonal (fun x => lum (pmap H s x + x)) * permMat (mkAP (pmap H s) hp_add hk0),
    (free_lum_comp _ fun x y => by simp only [hp_add]; abel).mul (.perm _), ?_⟩
  ext x y
  rw [coreFrame, conj_apply, Matrix.mul_assoc, Matrix.diagonal_mul, permMat_mul_apply, pk_apply, pk_apply]
  obtain ⟨u, rfl⟩ : ∃ u, y = x + u := ⟨x + y, by rw [← add_assoc, binary_cancel, zero_add]⟩
  have hc1 : (∀ k, k ∉ s' → H.π x k = H.π (x + u) k) ↔ ∀ k, k ∉ s → u k = 0 := by
    rw [H.add]; simp only [Pi.add_apply, F_eq_add]; exact (hH u).symm
  have hc2 : (∀ k, k ∉ s → (mkAP (pmap H s) hp_add hk0).π x k = (x + u) k) ↔ ∀ k, k ∉ s → u k = 0 :=
    forall_congr' fun k => imp_congr_right fun hk => by
      rw [show (mkAP (pmap H s) hp_add hk0).π x k = x k from if_neg hk, Pi.add_apply, F_eq_add]
  by_cases hu : ∀ k, k ∉ s → u k = 0
  · rw [if_pos (hc1.2 hu), if_pos (hc2.2 hu), H.add, ← add_assoc (H.π x), binary_cancel, zero_add,
      ← hcard, show (mkAP (pmap H s) hp_add hk0).π x = pmap H s x from rfl, ← add_assoc (pmap H s x) x u,
      lum_add (pmap H s x + x) u, lum_add (H.π x) (H.π u), lum_add x u, dot_add_left, sign_add, key x u hu]
    have hT : sign (dot x u) ≠ 0 := left_ne_zero_of_mul_eq_one (sign_sq _)
    rcases bit_cases (dot (H.π x) (H.π u)) with h | h <;> rw [h] <;> simp only [sgn0, sgn1] <;>
      field_simp [lum_nonzero] <;> ring
  · rw [if_neg (mt hc1.1 hu), if_neg (mt hc2.1 hu)]; simp

theorem repChange_core (G G' : APerm α) (s s' : Finset α) (h : ∀ x, InSub G s x ↔ InSub G' s' x) :
    ∃ N : CMat α, Free N ∧ coreFrame G' s' = N * coreFrame G s := by
  have hK : ∀ y, (∀ k, k ∉ s → y k = 0) ↔ InSub (apComp (apInv G) G') s' y := fun y => by
    have := h (G.π.symm y)
    simp only [InSub, Equiv.apply_symm_apply] at this
    exact this
  obtain ⟨M, hM, hKe⟩ := rep_aux _ s s' hK
  refine ⟨phasedPerm G * M * phasedPerm (apInv G), ((free_kg G).mul hM).mul (free_kg _), ?_⟩
  calc coreFrame G' s' = phasedPerm G * coreFrame (apComp (apInv G) G') s' * phasedPerm (apInv G) := by
        simp only [coreFrame]
        rw [← kg_comp (G := G) (H := apComp (apInv G) G') (K := G') fun x => by simp [apComp, apInv],
          ← kg_comp (G := apInv (apComp (apInv G) G')) (H := apInv G) (K := apInv G') fun x => by
            simp [apComp, apInv]]
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hKe]; simp only [coreFrame, Matrix.mul_assoc, inv_cancel_left (kg_inv_mul G)]

theorem flag (t : Finset α) : ∀ W : Space α → Prop, W 0 → (∀ x y, W x → W y → W (x + y)) →
    (∀ y, W y → ∀ k, k ∉ t → y k = 0) →
    ∃ (L : APerm α) (s : Finset α), s ⊆ t ∧ (∀ y k, k ∉ t → L.π y k = y k) ∧ ∀ y, InSub L s y ↔ W y := by
  refine Finset.induction_on t ?_ ?_
  · intro W h0 _ hW
    refine ⟨apId α, ∅, subset_rfl, fun _ _ _ => rfl, fun y => ⟨fun hy => ?_,
      fun hy k _ => hW y hy k (Finset.notMem_empty k)⟩⟩
    have : y = 0 := funext fun k => hy k (Finset.notMem_empty k)
    rw [this]; exact h0
  intro a t ha ih W h0 hadd hW
  obtain ⟨L, s, hs, hL, hLW⟩ := ih (fun y => W y ∧ y a = 0) ⟨h0, rfl⟩
    (fun x y hx hy => ⟨hadd x y hx.1 hy.1, by rw [Pi.add_apply, hx.2, hy.2, add_zero]⟩)
    (fun y hy k hk => by
      by_cases hka : k = a
      · rw [hka]; exact hy.2
      · exact hW y hy.1 k (by simp [hka, hk]))
  by_cases hp : ∃ p, W p ∧ p a = 1
  · obtain ⟨p, hpW, hpa⟩ := hp
    have hLa : ∀ y, L.π y a = y a := fun y => hL y a ha
    have hpk : ∀ k, k ∉ insert a t → p k = 0 := hW p hpW
    let f : Space α → Space α := fun y => L.π (y + y a • p) + y a • eu a
    have hf : ∀ x y, f (x + y) = f x + f y := by
      intro x y
      simp only [f, Pi.add_apply, add_smul]
      rw [show x + y + (x a • p + y a • p) = (x + x a • p) + (y + y a • p) by abel, L.add]
      abel
    have hfa : ∀ y, f y a = y a := fun y => by simp [f, hLa, hpa, eu, F_add_self]
    have hk : ∀ y, f y = 0 → y = 0 := by
      intro y hy
      have h1 : y a = 0 := by rw [← hfa y, hy]; rfl
      have h2 : L.π y = 0 := by simpa [f, h1] using hy
      exact L.π.injective (h2.trans (APerm.map_zero' L).symm)
    have hfy : ∀ y k, k ≠ a → f y k = L.π (y + y a • p) k := fun y k hk => by
      simp [f, eu, Ne.symm hk]
    refine ⟨mkAP f hf hk, insert a s, Finset.insert_subset_insert a hs, fun y k hk' => ?_, fun y => ?_⟩
    · have hka : k ≠ a := fun e => hk' (e ▸ Finset.mem_insert_self a t)
      have hkt : k ∉ t := fun e => hk' (Finset.mem_insert_of_mem e)
      show f y k = y k
      rw [hfy y k hka, hL _ k hkt, Pi.add_apply, Pi.smul_apply, hpk k hk', smul_zero, add_zero]
    · have hza : (y + y a • p) a = 0 := by simp [hpa, F_add_self]
      have hWz : W (y + y a • p) ↔ W y := by
        rcases bit_cases (y a) with h | h
        · rw [h, zero_smul, add_zero]
        · rw [h, one_smul]
          exact ⟨fun hw => by simpa [add_assoc] using hadd _ _ hw hpW, fun hw => hadd _ _ hw hpW⟩
      rw [← hWz]
      refine Iff.trans ?_ ((hLW (y + y a • p)).trans (and_iff_left hza))
      show (∀ k, k ∉ insert a s → f y k = 0) ↔ ∀ k, k ∉ s → L.π (y + y a • p) k = 0
      constructor
      · intro h k hk
        by_cases hka : k = a
        · rw [hka, hLa]; exact hza
        · rw [← hfy y k hka]; exact h k (by simp [hka, hk])
      · intro h k hk
        have hka : k ≠ a := fun e => hk (e ▸ Finset.mem_insert_self a s)
        rw [hfy y k hka]; exact h k fun e => hk (Finset.mem_insert_of_mem e)
  · push_neg at hp
    have hWa : ∀ y, W y → y a = 0 := fun y hy => (bit_cases (y a)).resolve_right (hp y hy)
    exact ⟨L, s, hs.trans (Finset.subset_insert a t), fun y k hk => hL y k fun e => hk (Finset.mem_insert_of_mem e),
      fun y => (hLW y).trans ⟨fun h => h.1, fun h => ⟨h, hWa y h⟩⟩⟩

theorem exists_common_base (G G' : APerm α) (s t : Finset α)
    (h : ∀ x, InSub G s x → InSub G' t x) :
    ∃ (G₀ : APerm α) (s₀ t₀ : Finset α), s₀ ⊆ t₀ ∧ (∀ x, InSub G s x ↔ InSub G₀ s₀ x) ∧
      (∀ x, InSub G₀ t₀ x ↔ InSub G' t x) := by
  obtain ⟨L, s₀, hs, hL, hW⟩ := flag t (fun y => InSub G s ((apInv G').π y))
    (fun k _ => by simp [APerm.map_zero'])
    (fun x y hx hy k hk => by simp [(apInv G').add, G.add, hx k hk, hy k hk])
    (fun y hy k hk => by simpa [apInv] using h _ hy k hk)
  refine ⟨apComp G' L, s₀, t, hs, fun x => Iff.trans ?_ (hW (G'.π x)).symm, fun x => ?_⟩
  · exact iff_of_eq (congrArg (InSub G s) (G'.π.symm_apply_apply x)).symm
  show (∀ k, k ∉ t → L.π (G'.π x) k = 0) ↔ ∀ k, k ∉ t → G'.π x k = 0
  exact forall_congr' fun k => imp_congr_right fun hk => by rw [hL _ k hk]

lemma lum_eu (i : α) : lum (eu i) = I := by
  simp only [lum, eu]
  rw [Finset.prod_eq_single i (fun b _ hb => by simp [tint, Ne.symm hb]) (by simp)]
  simp [tint, one_ne]

lemma conj_shift (A : OBase α) (i : α) :
    phasedPerm (coordPerm A) * shift (eu i) * phasedPerm (apInv (coordPerm A)) =
      (I / lum (A.v i)) • shift (A.v i) := by
  have hv : (coordPerm A).π (A.v i) = eu i := funext fun k => by
    show dot (A.v k) (A.v i) = eu i k
    rw [A.rows, eu]
    by_cases h : k = i
    · subst h; simp
    · simp [h, Ne.symm h]
  ext x y
  rw [conj_apply, Matrix.smul_apply]
  simp only [shift, smul_eq_mul]
  have hc : ((coordPerm A).π x + eu i = (coordPerm A).π y) ↔ (x + A.v i = y) := by
    rw [← hv, ← (coordPerm A).add, (coordPerm A).π.apply_eq_iff_eq]
  by_cases h : x + A.v i = y
  · subst h
    rw [if_pos (hc.2 rfl), if_pos rfl, (coordPerm A).add, hv, lum_add ((coordPerm A).π x) (eu i),
      lum_add x (A.v i), lum_eu, show dot ((coordPerm A).π x) (eu i) = dot x (A.v i) by
        rw [dot_symm, dot_eu_left, dot_symm]; rfl]
    have hT : sign (dot x (A.v i)) ≠ 0 := left_ne_zero_of_mul_eq_one (sign_sq _)
    field_simp [lum_nonzero] <;> ring
  · rw [if_neg (mt hc.1 h), if_neg h]; simp

theorem frame_eq_coreFrame (A : OBase α) (s : Finset α) :
    ∃ n : ℕ, frame A s = I ^ n • coreFrame (coordPerm A) s := by
  refine Finset.induction_on s ⟨0, ?_⟩ ?_
  · rw [frame_zero, coreFrame, pk_empty, Matrix.mul_one, kg_mul_inv, pow_zero, one_smul]
  rintro i s hi ⟨n, hn⟩
  have hc : phasedPerm (coordPerm A) * dir (eu i) * phasedPerm (apInv (coordPerm A)) =
      ca • 1 + (cb * (I / lum (A.v i))) • shift (A.v i) := by
    rw [dir, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.smul_mul, Matrix.mul_one, kg_mul_inv, conj_shift, smul_smul]
  obtain ⟨m, hm⟩ : ∃ m : ℕ, delta (A.v i) =
      I ^ m • (phasedPerm (coordPerm A) * dir (eu i) * phasedPerm (apInv (coordPerm A))) := by
    rcases lum_of_unit _ (A.self i) with h | h
    · refine ⟨0, ?_⟩
      rw [pow_zero, one_smul, hc, h, div_self Complex.I_ne_zero, mul_one, delta_pos _ h, dir]
    · refine ⟨3, ?_⟩
      have e1 : I ^ 3 * ca = cb := by
        simp only [ca, cb]; linear_combination ((I + I ^ 2 - 1) / 2) * Complex.I_sq
      have e2 : I ^ 3 * (cb * (I / -I)) = ca := by
        rw [div_neg, div_self Complex.I_ne_zero]
        simp only [ca, cb]; linear_combination ((I ^ 2 - 1 - I) / 2) * Complex.I_sq
      rw [hc, h, delta_neg _ h, dir, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one,
        shift_sq, smul_add, smul_smul, smul_smul, e1, e2, add_comm]
  refine ⟨m + n, ?_⟩
  rw [frame_ins A s i hi, hm, hn, core_insert _ hi, Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_add]

theorem frame_core (A : OBase α) (s : Finset α) :
    (∃ N, Free N ∧ frame A s = N * coreFrame (coordPerm A) s) ∧
      ∃ N, Free N ∧ coreFrame (coordPerm A) s = N * frame A s := by
  obtain ⟨n, hn⟩ := frame_eq_coreFrame A s
  have h1 : frame A s = (I ^ n • 1) * coreFrame (coordPerm A) s := by rw [hn, Matrix.smul_mul, Matrix.one_mul]
  obtain ⟨N', hN', h2, -⟩ := free_inv (free_scalar (α := α) n)
  exact ⟨⟨_, free_scalar n, h1⟩, N', hN', by rw [h1, ← Matrix.mul_assoc, h2, Matrix.one_mul]⟩

end
end PowerSaving.GenMove
end OAI

namespace OAI
namespace PowerSaving.GenMove
open Binary Matrix Finset RAM RankCost
noncomputable section
variable {α : Type} [Fintype α] [DecidableEq α]

inductive FrameMove : CMat α → CMat α → List ℕ → Prop
  | free {M A : CMat α} : GenMove.Free A → FrameMove M (A * M) []
  | block {M : CMat α} {r : ℕ} (z : Fin r → Space α) : LinearIndependent F z → 1 ≤ r →
      r < Fintype.card α → FrameMove M (blockMat z * M) [r]
  | trans {M N L : CMat α} {a b : List ℕ} : FrameMove M N a → FrameMove N L b → FrameMove M L (a ++ b)
  | zero {M N : CMat α} {a : List ℕ} : FrameMove M N a → FrameMove M N (0 :: a)

namespace FrameMove
variable {M N L : CMat α} {rs : List ℕ}

theorem refl (M : CMat α) : FrameMove M M [] := by simpa using FrameMove.free (M := M) Free.one

theorem step {ρ : Type} [Fintype ρ] [DecidableEq ρ] (h : FrameMove M N rs) (l : ρ) :
    GStep l M N (fun φ => rcost φ rs) := by
  induction h with
  | free hA => exact (gstep_free hA l _).cast fun φ => (rcost_nil φ).symm
  | block z ind h1 h2 =>
    exact (gstep_block l _ z ind h1 h2).cast fun φ => by rw [rcost_single, bcost_pos _ (by omega)]
  | trans _ _ ia ib => exact (ia.trans ib).cast fun φ => (rcost_append φ _ _).symm
  | zero _ ia => exact ia.cast fun φ => by rw [rcost_cons, bcost_zero, zero_add]
end FrameMove

def Reach (M N : CMat α) (c : (ℕ → ℝ) → ℝ) : Prop :=
  ∀ (ρ : Type) [Fintype ρ] [DecidableEq ρ] (l : ρ), GStep l M N c

theorem FrameMove.reach {M N : CMat α} {rs : List ℕ}
    (h : FrameMove M N rs) : Reach M N (fun φ => rcost φ rs) := fun _ _ _ l => h.step l

structure SubspaceLabel (α : Type) : Type where
   G : APerm α
   s : Finset α

namespace SubspaceLabel
def rep (U : SubspaceLabel α) : CMat α := GenMove.coreFrame U.G U.s
def Mem (U : SubspaceLabel α) (x : Space α) : Prop := GenMove.InSub U.G U.s x
def dim (U : SubspaceLabel α) : ℕ := Finset.card U.s
end SubspaceLabel

def indv (d : Finset α) : Space α := d.sum eu

lemma pk_sq (d : Finset α) : coordFrame d * coordFrame d = shift (indv d) := by
  rw [coordFrame, wrap_mul, shift_phase]
  congr 1
  funext x
  rw [← Finset.prod_mul_distrib]
  simp only [tint_sq]
  rw [← sign_sum, indv, dot_sum_left]
  simp [dot_eu_left]

def RepChange (α : Type) [Fintype α] [DecidableEq α] : Prop :=
  ∀ (G G' : APerm α) (s s' : Finset α), (∀ x, InSub G s x ↔ InSub G' s' x) →
    ∃ N : CMat α, GenMove.Free N ∧ coreFrame G' s' = N * coreFrame G s

theorem repChange (α : Type) [Fintype α] [DecidableEq α] : RepChange α := repChange_core

inductive LabelMove (m : ℕ) : SubspaceLabel α → SubspaceLabel α → List ℕ → Prop
  | stay (U : SubspaceLabel α) : LabelMove m U U []
  | up (G : APerm α) {s t : Finset α} : s ⊆ t → 1 ≤ (t \ s).card → (t \ s).card < m →
      LabelMove m ⟨G, s⟩ ⟨G, t⟩ [(t \ s).card]
  | down (G : APerm α) {s t : Finset α} : s ⊆ t → 1 ≤ (t \ s).card → (t \ s).card < m →
      LabelMove m ⟨G, t⟩ ⟨G, s⟩ [(t \ s).card]
  | rebase {U V : SubspaceLabel α} : (∀ x, U.Mem x ↔ V.Mem x) → LabelMove m U V []
  | trans {U V W : SubspaceLabel α} {a b : List ℕ} : LabelMove m U V a → LabelMove m V W b → LabelMove m U W (a ++ b)

theorem LabelMove.fmv (hR : RepChange α) {U V : SubspaceLabel α} {rs : List ℕ}
    (h : LabelMove (Fintype.card α) U V rs) :
    FrameMove U.rep V.rep rs := by
  induction h with
  | stay U => exact FrameMove.refl _
  | @up G s t hs h1 h2 =>
    have e : (⟨G, t⟩ : SubspaceLabel α).rep = phasedPerm G * (blockMat ((OBase.canonical α).fam (t \ s)) *
        (phasedPerm (apInv G) * (⟨G, s⟩ : SubspaceLabel α).rep)) := by
      simp only [SubspaceLabel.rep, core_nested G hs, Matrix.mul_assoc]
    have := ((FrameMove.free (M := (⟨G, s⟩ : SubspaceLabel α).rep) (free_kg (apInv G))).trans
      (FrameMove.block _ ((OBase.canonical α).fam_indep _) h1 h2)).trans (FrameMove.free (free_kg G))
    rw [e]; exact this
  | @down G s t hs h1 h2 =>
    have e : (⟨G, s⟩ : SubspaceLabel α).rep = phasedPerm G * (shift (indv (t \ s)) *
        (blockMat ((OBase.canonical α).fam (t \ s)) * (phasedPerm (apInv G) * (⟨G, t⟩ : SubspaceLabel α).rep))) := by
      simp only [SubspaceLabel.rep]
      rw [core_nested G hs, ← pk_eq_blockMat]
      simp only [Matrix.mul_assoc]
      rw [inv_cancel_left (kg_inv_mul G), ← Matrix.mul_assoc (coordFrame _) (coordFrame _), pk_sq,
        inv_cancel_left (shift_sq _), inv_cancel_left (kg_mul_inv G)]
    have := (((FrameMove.free (M := (⟨G, t⟩ : SubspaceLabel α).rep) (free_kg (apInv G))).trans
      (FrameMove.block _ ((OBase.canonical α).fam_indep _) h1 h2)).trans
      (FrameMove.free (Free.shift (indv (t \ s))))).trans (FrameMove.free (free_kg G))
    rw [e]; exact this
  | @rebase U V h =>
    obtain ⟨N, hN, he⟩ := hR U.G V.G U.s V.s h
    simp only [SubspaceLabel.rep]
    rw [he]
    exact .free hN
  | trans _ _ ia ib => exact ia.trans ib

structure LabelLift (H α : Type) [Fintype H] [DecidableEq H]
    [Fintype α] [DecidableEq α] where
  liftG : APerm H → APerm α
  liftS : Finset H → Finset α
  mono : ∀ {s t : Finset H}, s ⊆ t → liftS s ⊆ liftS t
  card : ∀ {s t : Finset H}, s ⊆ t → (liftS t \ liftS s).card = (t \ s).card
  sub : ∀ {G G' : APerm H} {s s' : Finset H}, (∀ x, InSub G s x ↔ InSub G' s' x) → ∀ y, InSub (liftG G) (liftS s) y ↔ InSub (liftG G') (liftS s') y

namespace LabelLift
variable {H : Type} [Fintype H] [DecidableEq H] (X : LabelLift H α)

def lab (U : SubspaceLabel H) : SubspaceLabel α := { G := X.liftG U.G, s := X.liftS U.s }
def Φ (U : SubspaceLabel H) : CMat α := SubspaceLabel.rep (X.lab U)

theorem lmv {m : ℕ} {U V : SubspaceLabel H} {rs : List ℕ} (h : LabelMove m U V rs) :
    LabelMove m (X.lab U) (X.lab V) rs := by
  induction h with
  | stay U => exact .stay _
  | up G hs h1 h2 =>
    rw [← X.card hs] at h1 h2 ⊢; exact .up _ (X.mono hs) h1 h2
  | down G hs h1 h2 =>
    rw [← X.card hs] at h1 h2 ⊢; exact .down _ (X.mono hs) h1 h2
  | @rebase U V h => exact .rebase (X.sub (G := U.G) (s := U.s) (G' := V.G) (s' := V.s) h)
  | trans _ _ ia ib => exact ia.trans ib

theorem fmv {U V : SubspaceLabel H} {rs : List ℕ} (h : LabelMove (Fintype.card α) U V rs) :
    FrameMove (X.Φ U) (X.Φ V) rs := (X.lmv h).fmv (repChange α)
end LabelLift

theorem LabelMove.symm {m : ℕ} {U V : SubspaceLabel α} {rs : List ℕ} (h : LabelMove m U V rs) :
    LabelMove m V U rs.reverse := by
  induction h with
  | stay U => exact .stay U
  | up G hs h1 h2 => exact .down G hs h1 h2
  | down G hs h1 h2 => exact .up G hs h1 h2
  | rebase h => exact .rebase fun x => (h x).symm
  | trans _ _ ia ib => rw [List.reverse_append]; exact ib.trans ia

theorem LabelMove.of_sub {m : ℕ} (U V : SubspaceLabel α) (h : ∀ x, U.Mem x → V.Mem x)
    (h1 : U.dim < V.dim) (h2 : V.dim - U.dim < m) : LabelMove m U V [V.dim - U.dim] := by
  obtain ⟨G₀, s₀, t₀, hst, h1', h2'⟩ := exists_common_base U.G V.G U.s V.s h
  have c1 := same_card h1'
  have c2 := same_card h2'
  have hr : (t₀ \ s₀).card = V.dim - U.dim := by
    rw [card_sdiff_of_subset hst]; simp only [SubspaceLabel.dim]; omega
  rw [← hr] at h2 ⊢
  have := (LabelMove.rebase (m := m) (U := U) (V := ⟨G₀, s₀⟩) h1').trans
    ((LabelMove.up G₀ hst (by rw [hr]; omega) h2).trans (LabelMove.rebase (U := ⟨G₀, t₀⟩) (V := V) h2'))
  exact this

theorem LabelMove.of_sup {m : ℕ} (U V : SubspaceLabel α) (h : ∀ x, U.Mem x → V.Mem x)
    (h1 : U.dim < V.dim) (h2 : V.dim - U.dim < m) : LabelMove m V U [V.dim - U.dim] :=
  (LabelMove.of_sub U V h h1 h2).symm

end
end PowerSaving.GenMove
end OAI

namespace OAI
namespace PowerSaving
namespace CoordPerm
open Binary Matrix Finset GenMove
noncomputable section
variable {α : Type} [Fintype α] [DecidableEq α]

def cperm (τ : Equiv.Perm α) : APerm α where
  π :=
    { toFun := fun x k => x (τ k)
      invFun := fun x k => x (τ.symm k)
      left_inv := fun x => funext fun k => by simp
      right_inv := fun x => funext fun k => by simp }
  add _ _ := rfl

lemma free_cperm (τ : Equiv.Perm α) : Free (permMat (cperm τ)) := .perm _

lemma mul_permMat_apply (M : CMat α) (G : APerm α) (x y : Space α) :
    (M * permMat G) x y = M x (G.π.symm y) := by
  simp [Matrix.mul_apply, permMat, Equiv.apply_eq_iff_eq_symm_apply]

theorem pk_cperm (τ : Equiv.Perm α) (s : Finset α) :
    permMat (cperm τ) * coordFrame s = coordFrame (s.map τ.toEmbedding) * permMat (cperm τ) := by
  ext x y
  rw [permMat_mul_apply, mul_permMat_apply, pk_apply, pk_apply, Finset.card_map]
  have hc : (∀ k, k ∉ s → (cperm τ).π x k = y k) ↔
      ∀ k, k ∉ s.map τ.toEmbedding → x k = (cperm τ).π.symm y k := by
    simp only [Finset.mem_map_equiv]
    exact ⟨fun h k hk => by simpa [cperm] using h (τ.symm k) hk,
      fun h k hk => by simpa [cperm] using h (τ k) (by simpa using hk)⟩
  have hl : lum ((cperm τ).π x + y) = lum (x + (cperm τ).π.symm y) := by
    unfold lum
    rw [← Equiv.prod_comp τ (fun k => tint ((x + (cperm τ).π.symm y) k))]
    congr 1; funext k; simp [cperm]
  by_cases h : ∀ k, k ∉ s → (cperm τ).π x k = y k
  · rw [if_pos h, if_pos (hc.1 h), hl]
  · rw [if_neg h, if_neg (mt hc.2 h)]
end
end CoordPerm
end PowerSaving
end OAI
