import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
-- changed for the tensor-power extension (30103/10000000); see Submission.lean

/-!
# Strictification of a mixed unit: tensor power, target completion, paid splitting (inventory level)

Prototype (tensor-theory hunt, 21 Oct 2026) of the moment side of the construction of
CrocSwap/integer-mult-bounds PR4416 `TENSOR.md` §§1–3 (product, completion, splitting) and its
higher-moment tail (PR4433 §2).  Mathlib only.

A unit is seen through its two rank inventories (multisets of natural numbers):
`T` = target ranks of its productive (live) roles, `P` = ranks of its paid jobs.

* `mom t s = ∑_{r ∈ s} r^t`, `tens A B` = all products `a*b` (the chronological product multiplies
  target ranks and paid ranks), `tpow A v` = `v`-fold product;
* `mom_tens`, `mom_tpow` : **moments multiply**: `mom t (tpow A v) = (mom t A)^v`;
* `pieces J R`, `splitAll J` : a job of rank `R > J` becomes jobs `J,…,J, R mod J` on disjoint axes;
* `padT L`, `comp L` : a target `K < L` is completed to `L` by an extra paid job of rank `L - K`;
* `mom_splitAll_le` : split charge `≤ mom t P + 2 J^(-u) mom (t+u) P` whenever `t + u ≥ 1`;
* `mom_split_comp_le` : all completions together cost `≤ |T| · 2 L J^(t-1)`;
* `strictify_mom` / `strictify` : the completed, split `v`-fold product has `t`-moment surplus as soon as
  `α^v + 2γ^v + 2δ^v ≤ 1` (`α = P_t/T_t`, `γ = P_(t+u)/(c^u T_t)`, `δ = |T| b/(c^(1-t) T_t)`), and it is
  separated: every paid rank `≤ c^v < b^v ≤` every target rank.
-/

namespace TensorProto

open Multiset

noncomputable section

/-! ## moments of rank inventories -/

/-- `t`-moment of a multiset of ranks. -/
def mom (t : ℝ) (s : Multiset ℕ) : ℝ := (s.map fun r : ℕ => (r : ℝ) ^ t).sum

@[simp] lemma mom_zero (t : ℝ) : mom t 0 = 0 := by simp [mom]

@[simp] lemma mom_singleton (t : ℝ) (r : ℕ) : mom t {r} = (r : ℝ) ^ t := by simp [mom]

lemma mom_add (t : ℝ) (s s' : Multiset ℕ) : mom t (s + s') = mom t s + mom t s' := by
  simp [mom, Multiset.map_add, Multiset.sum_add]

lemma mom_replicate (t : ℝ) (n r : ℕ) : mom t (Multiset.replicate n r) = (n : ℝ) * (r : ℝ) ^ t := by
  simp [mom, Multiset.map_replicate, Multiset.sum_replicate, nsmul_eq_mul]

lemma mom_bind (t : ℝ) (s : Multiset ℕ) (f : ℕ → Multiset ℕ) :
    mom t (s.bind f) = (s.map fun r => mom t (f r)).sum := by
  simp only [mom, Multiset.map_bind, Multiset.sum_bind]

lemma mom_nonneg (t : ℝ) (s : Multiset ℕ) : 0 ≤ mom t s :=
  Multiset.sum_nonneg (fun x hx => by
    obtain ⟨r, -, rfl⟩ := Multiset.mem_map.1 hx
    exact Real.rpow_nonneg (Nat.cast_nonneg r) t)

/-- rank-one moment = rank mass -/
lemma mom_one (s : Multiset ℕ) : mom 1 s = ((s.sum : ℕ) : ℝ) := by
  unfold mom
  simp only [Real.rpow_one]
  rw [Nat.cast_multiset_sum]

/-! ## the chronological product: ranks multiply, so moments multiply -/

/-- All products `a * b`, `a ∈ A`, `b ∈ B` (with multiplicity). -/
def tens (A B : Multiset ℕ) : Multiset ℕ := A.bind fun a => B.map fun b => a * b

lemma mom_tens (t : ℝ) (A B : Multiset ℕ) : mom t (tens A B) = mom t A * mom t B := by
  unfold tens
  rw [mom_bind]
  have h : ∀ a : ℕ, mom t (B.map fun b => a * b) = (a : ℝ) ^ t * mom t B := by
    intro a
    unfold mom
    rw [Multiset.map_map, ← Multiset.sum_map_mul_left]
    congr 1
    apply Multiset.map_congr rfl
    intro b _
    simp only [Function.comp_apply, Nat.cast_mul]
    exact Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)
  simp_rw [h]
  unfold mom
  rw [Multiset.sum_map_mul_right]

lemma card_tens (A B : Multiset ℕ) : card (tens A B) = card A * card B := by
  unfold tens
  rw [Multiset.card_bind]
  have h : (A.map (card ∘ fun a => B.map fun b => a * b)) = A.map fun _ => card B := by
    apply Multiset.map_congr rfl
    intro a _
    simp
  rw [h, Multiset.map_const', Multiset.sum_replicate, smul_eq_mul]

lemma mem_tens {A B : Multiset ℕ} {x : ℕ} (hx : x ∈ tens A B) : ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  unfold tens at hx
  obtain ⟨a, ha, hb⟩ := Multiset.mem_bind.1 hx
  obtain ⟨b, hb', rfl⟩ := Multiset.mem_map.1 hb
  exact ⟨a, ha, b, hb', rfl⟩

lemma mul_mem_tens {A B : Multiset ℕ} {a b : ℕ} (ha : a ∈ A) (hb : b ∈ B) : a * b ∈ tens A B := by
  unfold tens
  exact Multiset.mem_bind.2 ⟨a, ha, Multiset.mem_map.2 ⟨b, hb, rfl⟩⟩

/-- The `v`-fold chronological product. -/
def tpow (A : Multiset ℕ) : ℕ → Multiset ℕ
  | 0 => {1}
  | v + 1 => tens (tpow A v) A

/-- **Moments multiply** along the tensor power. -/
lemma mom_tpow (t : ℝ) (A : Multiset ℕ) (v : ℕ) : mom t (tpow A v) = mom t A ^ v := by
  induction v with
  | zero => simp [tpow]
  | succ v ih => rw [tpow, mom_tens, ih, pow_succ]

lemma card_tpow (A : Multiset ℕ) (v : ℕ) : card (tpow A v) = card A ^ v := by
  induction v with
  | zero => simp [tpow]
  | succ v ih => rw [tpow, card_tens, ih, pow_succ]

lemma tpow_bounds {A : Multiset ℕ} {lo hi : ℕ} (h : ∀ x ∈ A, lo ≤ x ∧ x ≤ hi) (v : ℕ) :
    ∀ x ∈ tpow A v, lo ^ v ≤ x ∧ x ≤ hi ^ v := by
  induction v with
  | zero =>
    intro x hx
    simp only [tpow, Multiset.mem_singleton] at hx
    subst hx; simp
  | succ v ih =>
    intro x hx
    rw [tpow] at hx
    obtain ⟨y, hy, a, ha, rfl⟩ := mem_tens hx
    obtain ⟨h1, h2⟩ := ih y hy
    obtain ⟨h3, h4⟩ := h a ha
    exact ⟨by rw [pow_succ]; exact Nat.mul_le_mul h1 h3, by rw [pow_succ]; exact Nat.mul_le_mul h2 h4⟩

lemma pow_mem_tpow {A : Multiset ℕ} {a : ℕ} (ha : a ∈ A) (v : ℕ) : a ^ v ∈ tpow A v := by
  induction v with
  | zero => simp [tpow]
  | succ v ih => rw [tpow, pow_succ]; exact mul_mem_tens ih ha

/-! ## splitting a paid job on disjoint axes -/

/-- A job of rank `R` split at `J`: itself if `R ≤ J`, else `R / J` jobs of rank `J` and the remainder. -/
def pieces (J R : ℕ) : Multiset ℕ :=
  if R ≤ J then {R} else Multiset.replicate (R / J) J + (if R % J = 0 then 0 else {R % J})

/-- Split every job of `P` at `J`. -/
def splitAll (J : ℕ) (P : Multiset ℕ) : Multiset ℕ := P.bind (pieces J)

lemma pieces_le {J R : ℕ} (hJ : 0 < J) : ∀ x ∈ pieces J R, x ≤ J := by
  intro x hx
  unfold pieces at hx
  split_ifs at hx with h1 h2
  · rw [Multiset.mem_singleton] at hx; omega
  · rw [add_zero] at hx
    exact le_of_eq (Multiset.eq_of_mem_replicate hx)
  · rcases Multiset.mem_add.1 hx with hx | hx
    · exact le_of_eq (Multiset.eq_of_mem_replicate hx)
    · rw [Multiset.mem_singleton] at hx
      have := Nat.mod_lt R hJ
      omega

lemma pieces_pos {J R : ℕ} (hJ : 0 < J) (hR : 1 ≤ R) : ∀ x ∈ pieces J R, 1 ≤ x := by
  intro x hx
  unfold pieces at hx
  split_ifs at hx with h1 h2
  · rw [Multiset.mem_singleton] at hx; omega
  · rw [add_zero] at hx
    rw [Multiset.eq_of_mem_replicate hx]; omega
  · rcases Multiset.mem_add.1 hx with hx | hx
    · rw [Multiset.eq_of_mem_replicate hx]; omega
    · rw [Multiset.mem_singleton] at hx; omega

/-- Splitting preserves rank mass (rank-one surplus is unchanged). -/
lemma sum_pieces {J R : ℕ} : (pieces J R).sum = R := by
  unfold pieces
  split_ifs with h1 h2
  · simp
  · simp only [add_zero, Multiset.sum_replicate, smul_eq_mul]
    have := Nat.div_add_mod R J
    rw [h2] at this
    linarith [mul_comm (R / J) J]
  · simp only [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul, Multiset.sum_singleton]
    have := Nat.div_add_mod R J
    linarith [mul_comm (R / J) J]

lemma splitAll_le {J : ℕ} (hJ : 0 < J) (P : Multiset ℕ) : ∀ x ∈ splitAll J P, x ≤ J := by
  intro x hx
  obtain ⟨R, -, hR⟩ := Multiset.mem_bind.1 hx
  exact pieces_le hJ x hR

lemma splitAll_pos {J : ℕ} (hJ : 0 < J) {P : Multiset ℕ} (hP : ∀ R ∈ P, 1 ≤ R) :
    ∀ x ∈ splitAll J P, 1 ≤ x := by
  intro x hx
  obtain ⟨R, hRP, hR⟩ := Multiset.mem_bind.1 hx
  exact pieces_pos hJ (hP R hRP) x hR

lemma rpow_eq_mul_rpow_sub_one {J : ℝ} (hJ : 0 < J) (t : ℝ) : J ^ t = J * J ^ (t - 1) := by
  have h : J ^ ((1 : ℝ) + (t - 1)) = J ^ (1 : ℝ) * J ^ (t - 1) := Real.rpow_add hJ 1 (t - 1)
  rw [Real.rpow_one] at h
  rw [← h]
  congr 1
  ring

/-- Charge of a split job of rank `R > J`: `⌊R/J⌋ J^t + (R mod J)^t ≤ R J^(t-1) + J^t`. -/
lemma mom_pieces_big {J R : ℕ} {t : ℝ} (hJ : 0 < J) (hRJ : J < R) (ht0 : 0 ≤ t) :
    mom t (pieces J R) ≤ (R : ℝ) * (J : ℝ) ^ (t - 1) + (J : ℝ) ^ t := by
  have hR : ¬ R ≤ J := by omega
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  unfold pieces
  rw [if_neg hR, mom_add, mom_replicate]
  have h2 : mom t (if R % J = 0 then 0 else {R % J}) ≤ (J : ℝ) ^ t := by
    split_ifs
    · rw [mom_zero]; exact Real.rpow_nonneg hJr.le t
    · rw [mom_singleton]
      exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast (Nat.mod_lt R hJ).le) ht0
  have h3 : ((R / J : ℕ) : ℝ) * (J : ℝ) ^ t ≤ (R : ℝ) * (J : ℝ) ^ (t - 1) := by
    rw [rpow_eq_mul_rpow_sub_one hJr t, ← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hJr.le _)
    exact_mod_cast Nat.div_mul_le_self R J
  linarith

/-- The same, as `≤ 2 R J^(t-1)` (`= 2 R J^(-C)` at `t = 1 - C`). -/
lemma mom_pieces_two {J R : ℕ} {t : ℝ} (hJ : 0 < J) (hRJ : J < R) (ht0 : 0 ≤ t) :
    mom t (pieces J R) ≤ 2 * (R : ℝ) * (J : ℝ) ^ (t - 1) := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have h1 := mom_pieces_big hJ hRJ ht0
  have h2 : (J : ℝ) ^ t ≤ (R : ℝ) * (J : ℝ) ^ (t - 1) := by
    rw [rpow_eq_mul_rpow_sub_one hJr t]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hRJ.le) (Real.rpow_nonneg hJr.le _)
  linarith

/-- **Higher-moment tail** (PR4433 §2): for `t + u ≥ 1`, every job's split charge is at most
`R^t + 2 J^(-u) R^(t+u)`. -/
lemma mom_pieces_tail {J R : ℕ} {t u : ℝ} (hJ : 0 < J) (ht0 : 0 ≤ t) (hu : 0 ≤ u) (hσ : 1 ≤ t + u) :
    mom t (pieces J R) ≤ (R : ℝ) ^ t + 2 * (J : ℝ) ^ (-u) * (R : ℝ) ^ (t + u) := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hnn : 0 ≤ 2 * (J : ℝ) ^ (-u) * (R : ℝ) ^ (t + u) := by positivity
  by_cases hRJ : R ≤ J
  · unfold pieces
    rw [if_pos hRJ, mom_singleton]
    linarith
  · push_neg at hRJ
    have hRr : (0 : ℝ) < R := by exact_mod_cast (lt_trans hJ hRJ)
    have h1 := mom_pieces_two hJ hRJ ht0
    -- `R J^(t-1) ≤ J^(-u) R^(t+u)`, from `J^(t+u-1) ≤ R^(t+u-1)`
    have h2 : (J : ℝ) ^ (t + u - 1) ≤ (R : ℝ) ^ (t + u - 1) :=
      Real.rpow_le_rpow hJr.le (by exact_mod_cast hRJ.le) (by linarith)
    have e1 : (J : ℝ) ^ (t - 1) = (J : ℝ) ^ (-u) * (J : ℝ) ^ (t + u - 1) := by
      rw [← Real.rpow_add hJr]; congr 1; ring
    have e2 : (R : ℝ) ^ (t + u) = (R : ℝ) * (R : ℝ) ^ (t + u - 1) := rpow_eq_mul_rpow_sub_one hRr _
    have h3 : (R : ℝ) * (J : ℝ) ^ (t - 1) ≤ (J : ℝ) ^ (-u) * (R : ℝ) ^ (t + u) := by
      rw [e1, e2]
      have hJu : 0 ≤ (J : ℝ) ^ (-u) := Real.rpow_nonneg hJr.le _
      calc (R : ℝ) * ((J : ℝ) ^ (-u) * (J : ℝ) ^ (t + u - 1))
          = (J : ℝ) ^ (-u) * ((R : ℝ) * (J : ℝ) ^ (t + u - 1)) := by ring
        _ ≤ (J : ℝ) ^ (-u) * ((R : ℝ) * (R : ℝ) ^ (t + u - 1)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hRr.le) hJu
    have h4 : 0 ≤ (R : ℝ) ^ t := Real.rpow_nonneg hRr.le t
    linarith

/-- Split charge of a whole inventory: `mom t (split P) ≤ mom t P + 2 J^(-u) mom (t+u) P`. -/
lemma mom_splitAll_le {J : ℕ} {t u : ℝ} (hJ : 0 < J) (ht0 : 0 ≤ t) (hu : 0 ≤ u) (hσ : 1 ≤ t + u)
    (P : Multiset ℕ) :
    mom t (splitAll J P) ≤ mom t P + 2 * (J : ℝ) ^ (-u) * mom (t + u) P := by
  unfold splitAll
  rw [mom_bind]
  have h := Multiset.sum_map_le_sum_map (s := P) (fun R => mom t (pieces J R))
    (fun R => (R : ℝ) ^ t + 2 * (J : ℝ) ^ (-u) * (R : ℝ) ^ (t + u))
    (fun R _ => mom_pieces_tail hJ ht0 hu hσ)
  refine h.trans (le_of_eq ?_)
  rw [Multiset.sum_map_add, Multiset.sum_map_mul_left]
  rfl

/-! ## completion of small targets -/

/-- Targets after completion to `L`. -/
def padT (L : ℕ) (T : Multiset ℕ) : Multiset ℕ := T.map fun K => max K L

/-- The paid completion jobs: rank `L - K` for every target `K < L`. -/
def comp (L : ℕ) (T : Multiset ℕ) : Multiset ℕ := T.bind fun K => if K < L then {L - K} else 0

lemma padT_ge {L : ℕ} {T : Multiset ℕ} : ∀ x ∈ padT L T, L ≤ x := by
  intro x hx
  obtain ⟨K, -, rfl⟩ := Multiset.mem_map.1 hx
  exact le_max_right K L

lemma padT_le {L m : ℕ} {T : Multiset ℕ} (hL : L ≤ m) (hT : ∀ x ∈ T, x ≤ m) : ∀ x ∈ padT L T, x ≤ m := by
  intro x hx
  obtain ⟨K, hK, rfl⟩ := Multiset.mem_map.1 hx
  exact max_le (hT K hK) hL

lemma mem_padT {L K : ℕ} {T : Multiset ℕ} (hK : K ∈ T) (h : K ≤ L) : L ∈ padT L T :=
  Multiset.mem_map.2 ⟨K, hK, max_eq_right h⟩

lemma card_padT (L : ℕ) (T : Multiset ℕ) : card (padT L T) = card T := by simp [padT]

/-- Completion only raises the target moment. -/
lemma mom_le_mom_padT {t : ℝ} (ht0 : 0 ≤ t) (L : ℕ) (T : Multiset ℕ) : mom t T ≤ mom t (padT L T) := by
  unfold padT mom
  rw [Multiset.map_map]
  apply Multiset.sum_map_le_sum_map
  intro K _
  simp only [Function.comp_apply]
  exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast le_max_left K L) ht0

lemma comp_pos {L : ℕ} {T : Multiset ℕ} : ∀ x ∈ comp L T, 1 ≤ x := by
  intro x hx
  obtain ⟨K, -, hK⟩ := Multiset.mem_bind.1 hx
  split_ifs at hK with h
  · rw [Multiset.mem_singleton] at hK; omega
  · simp at hK

/-- Completion adds equal rank mass to targets and paid jobs (rank-one surplus unchanged). -/
lemma sum_padT_eq (L : ℕ) (T : Multiset ℕ) : (padT L T).sum = T.sum + (comp L T).sum := by
  unfold padT comp
  rw [Multiset.sum_bind]
  induction T using Multiset.induction_on with
  | empty => simp
  | cons K T ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, ih]
    split_ifs with h
    · simp only [Multiset.sum_singleton]; rw [max_eq_right h.le]; omega
    · simp only [Multiset.sum_zero]; rw [max_eq_left (not_lt.1 h)]; omega

/-- All completion jobs, split at `J ≤ L`, cost at most `|T| · 2 L J^(t-1)` (each `< 2 L J^(-C)`). -/
lemma mom_split_comp_le {J L : ℕ} {t : ℝ} (hJ : 0 < J) (hJL : J ≤ L) (ht0 : 0 ≤ t) (T : Multiset ℕ) :
    mom t (splitAll J (comp L T)) ≤ (card T : ℝ) * (2 * (L : ℝ) * (J : ℝ) ^ (t - 1)) := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hJLr : (J : ℝ) ≤ L := by exact_mod_cast hJL
  have hJ1 : 0 ≤ (J : ℝ) ^ (t - 1) := Real.rpow_nonneg hJr.le _
  unfold splitAll comp
  rw [Multiset.bind_assoc, mom_bind]
  have hb : ∀ K ∈ T, mom t ((if K < L then ({L - K} : Multiset ℕ) else 0).bind (pieces J))
      ≤ 2 * (L : ℝ) * (J : ℝ) ^ (t - 1) := by
    intro K _
    split_ifs with h
    · rw [Multiset.singleton_bind]
      by_cases hD : L - K ≤ J
      · unfold pieces
        rw [if_pos hD, mom_singleton]
        have h1 : ((L - K : ℕ) : ℝ) ^ t ≤ (J : ℝ) ^ t :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hD) ht0
        have h2 : (J : ℝ) ^ t ≤ (L : ℝ) * (J : ℝ) ^ (t - 1) := by
          rw [rpow_eq_mul_rpow_sub_one hJr t]
          exact mul_le_mul_of_nonneg_right hJLr hJ1
        have h3 : 0 ≤ (L : ℝ) * (J : ℝ) ^ (t - 1) := mul_nonneg (Nat.cast_nonneg _) hJ1
        linarith
      · push_neg at hD
        have h1 := mom_pieces_big hJ hD ht0
        have hDL : ((L - K : ℕ) : ℝ) ≤ L := by exact_mod_cast Nat.sub_le L K
        have h2 : (J : ℝ) ^ t ≤ (L : ℝ) * (J : ℝ) ^ (t - 1) := by
          rw [rpow_eq_mul_rpow_sub_one hJr t]
          exact mul_le_mul_of_nonneg_right hJLr hJ1
        have h3 : ((L - K : ℕ) : ℝ) * (J : ℝ) ^ (t - 1) ≤ (L : ℝ) * (J : ℝ) ^ (t - 1) :=
          mul_le_mul_of_nonneg_right hDL hJ1
        linarith
    · rw [Multiset.zero_bind, mom_zero]
      positivity
  have h := Multiset.sum_map_le_sum_map _ (fun _ => 2 * (L : ℝ) * (J : ℝ) ^ (t - 1)) hb
  refine h.trans (le_of_eq ?_)
  rw [Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul]

/-! ## the strictified unit -/

/-- Targets of the completed `v`-fold product. -/
def strictT (T : Multiset ℕ) (v L : ℕ) : Multiset ℕ := padT L (tpow T v)

/-- Paid jobs of the completed `v`-fold product, every job (product jobs and completions) split at `J`. -/
def strictP (T P : Multiset ℕ) (v J L : ℕ) : Multiset ℕ := splitAll J (tpow P v + comp L (tpow T v))

lemma strictP_le {T P : Multiset ℕ} {v J L : ℕ} (hJ : 0 < J) : ∀ x ∈ strictP T P v J L, x ≤ J :=
  splitAll_le hJ _

lemma strictT_ge {T : Multiset ℕ} {v L : ℕ} : ∀ x ∈ strictT T v L, L ≤ x := padT_ge

/-- **Strictification, moment form.** If
`P_t^v + 2 J^(-u) P_(t+u)^v + |T|^v · 2 L J^(t-1) ≤ T_t^v` then the completed split product has
`t`-moment surplus. -/
theorem strictify_mom {T P : Multiset ℕ} {v J L : ℕ} {t u : ℝ}
    (hJ : 0 < J) (hJL : J ≤ L) (ht0 : 0 ≤ t) (hu : 0 ≤ u) (hσ : 1 ≤ t + u)
    (h : mom t P ^ v + 2 * (J : ℝ) ^ (-u) * mom (t + u) P ^ v
          + (card T : ℝ) ^ v * (2 * (L : ℝ) * (J : ℝ) ^ (t - 1)) ≤ mom t T ^ v) :
    mom t (strictP T P v J L) ≤ mom t (strictT T v L) := by
  unfold strictP strictT splitAll
  rw [Multiset.add_bind, mom_add]
  have h1 := mom_splitAll_le hJ ht0 hu hσ (tpow P v)
  have h2 := mom_split_comp_le hJ hJL ht0 (tpow T v)
  have h3 := mom_le_mom_padT ht0 L (tpow T v)
  rw [mom_tpow, mom_tpow] at h1
  rw [card_tpow, Nat.cast_pow] at h2
  rw [mom_tpow] at h3
  unfold splitAll at h1 h2
  linarith

lemma natpow_rpow (x : ℝ) (hx : 0 ≤ x) (a : ℝ) (v : ℕ) : (x ^ v) ^ a = (x ^ a) ^ v :=
  (Real.rpow_pow_comm hx a v).symm

/-- **Strictification** (TENSOR.md §3 / PR4433 §2, with cutoff `J = c^v` and floor `L = b^v`):
`α^v + 2 γ^v + 2 δ^v ≤ 1` gives the `t`-moment surplus of the completed, split `v`-fold product. -/
theorem strictify {T P : Multiset ℕ} {v c b : ℕ} {t u : ℝ}
    (hc : 0 < c) (hcb : c ≤ b) (ht0 : 0 ≤ t) (hu : 0 ≤ u) (hσ : 1 ≤ t + u) (hT : 0 < mom t T)
    (h : (mom t P / mom t T) ^ v + 2 * (mom (t + u) P / ((c : ℝ) ^ u * mom t T)) ^ v
          + 2 * ((card T : ℝ) * b / ((c : ℝ) ^ (1 - t) * mom t T)) ^ v ≤ 1) :
    mom t (strictP T P v (c ^ v) (b ^ v)) ≤ mom t (strictT T v (b ^ v)) := by
  have hcr : (0 : ℝ) < c := by exact_mod_cast hc
  have hcu : (0 : ℝ) < (c : ℝ) ^ u := Real.rpow_pos_of_pos hcr u
  have hct : (0 : ℝ) < (c : ℝ) ^ (1 - t) := Real.rpow_pos_of_pos hcr _
  apply strictify_mom (pow_pos hc v) (Nat.pow_le_pow_left hcb v) ht0 hu hσ
  have hTv : 0 < mom t T ^ v := pow_pos hT v
  have eJ : ((c ^ v : ℕ) : ℝ) = (c : ℝ) ^ v := by push_cast; ring
  have eL : ((b ^ v : ℕ) : ℝ) = (b : ℝ) ^ v := by push_cast; ring
  have e1 : ((c : ℝ) ^ v) ^ (-u) = (((c : ℝ) ^ u) ^ v)⁻¹ := by
    rw [natpow_rpow _ hcr.le, Real.rpow_neg hcr.le, inv_pow]
  have e2 : ((c : ℝ) ^ v) ^ (t - 1) = (((c : ℝ) ^ (1 - t)) ^ v)⁻¹ := by
    rw [natpow_rpow _ hcr.le, show t - 1 = -(1 - t) by ring, Real.rpow_neg hcr.le, inv_pow]
  rw [eJ, eL, e1, e2]
  have key : (mom t P / mom t T) ^ v + 2 * (mom (t + u) P / ((c : ℝ) ^ u * mom t T)) ^ v
      + 2 * ((card T : ℝ) * b / ((c : ℝ) ^ (1 - t) * mom t T)) ^ v
      = (mom t P ^ v + 2 * (((c : ℝ) ^ u) ^ v)⁻¹ * mom (t + u) P ^ v
        + (card T : ℝ) ^ v * (2 * (b : ℝ) ^ v * (((c : ℝ) ^ (1 - t)) ^ v)⁻¹)) / mom t T ^ v := by
    simp only [div_pow, mul_pow]
    ring
  rw [key, div_le_one hTv] at h
  exact h

/-- Separation of the strictified unit: every paid rank `≤ c^v < b^v ≤` every target rank. -/
theorem strictify_sep {T P : Multiset ℕ} {v c b : ℕ} (hv : 1 ≤ v) (hc : 0 < c) (hcb : c < b) :
    (∀ x ∈ strictP T P v (c ^ v) (b ^ v), x ≤ c ^ v) ∧ (∀ x ∈ strictT T v (b ^ v), b ^ v ≤ x)
      ∧ c ^ v < b ^ v :=
  ⟨strictP_le (pow_pos hc v), strictT_ge, Nat.pow_lt_pow_left hcb (by omega)⟩

/-- The rank-one surplus is preserved exactly: `(targets) - (paid) = T_1^v - P_1^v`. -/
theorem strictify_mass (T P : Multiset ℕ) (v J L : ℕ) :
    ((strictT T v L).sum : ℤ) - (strictP T P v J L).sum = (tpow T v).sum - (tpow P v).sum := by
  unfold strictT strictP splitAll
  rw [Multiset.add_bind, Multiset.sum_add, Multiset.sum_bind, Multiset.sum_bind, sum_padT_eq]
  have h1 : ∀ s : Multiset ℕ, (s.map fun R => (pieces J R).sum) = s := by
    intro s; simp [sum_pieces]
  rw [h1, h1]
  push_cast
  ring

end

end TensorProto
