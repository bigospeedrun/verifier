import Submission.Work.MixedCost.TopMain
import Submission.Work.MixedCost.Match
import Submission.Work.MixedCost.Bill

/-!
# Mixed engine, top body part 6: the bridge from the program's counts to the job model

(agent e-r3cost, round wht45/lever, 19 Oct 2026.)  For a `Rule` `R` whose types, ranks and arrays are
those of the engine `E` (`BridgeHyp`):

* `topG_eq`        the root height is `R.G n`;
* `NUc_eq`         unit counts are `R.unitsC`;
* `card_srcBelow_eq`  the subtree consumption is `card (R.srcBelow ..)`;
* `topN_eq`        **vectors per tree copy = `R.Nsrc n`**.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset GF MXR
noncomputable section

namespace Eng
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ] (E : Eng α ρ σ)

/-- The rule `R` is the engine's: same axes, ranks of the block letters, targets of the live roles. -/
structure BridgeHyp (R : MX.Rule) (typ : ℕ → Fin R.K) (kmin : ℕ) : Prop where
  hm : R.m = E.mx
  hP : R.P = E.nB
  hrk : ∀ j : Fin R.P, R.rk j = E.rkI j
  htq : ∀ x, x < E.W → E.tq x = R.kr (typ x)
  hW : ∀ k, ((range E.W).filter (fun x => typ x = k)).card = R.Wk k
  hkmin : R.kmin = kmin

variable {E} {R : MX.Rule} {typ : ℕ → Fin R.K} {kmin : ℕ}

lemma BridgeHyp.topG_eq (H : E.BridgeHyp R typ kmin) (n : ℕ) : E.topG kmin n = R.G n := by
  unfold topG MX.Rule.G; rw [H.hm, H.hkmin]

lemma BridgeHyp.NUc_eq (H : E.BridgeHyp R typ kmin) (n h μ : ℕ) : E.NUc n h μ = R.unitsC n h μ := by
  have := R.NU_eq_unitsC typ E.W_pos (tq := E.tq) H.htq H.hW n h μ
  rw [← this, H.hm]

lemma BridgeHyp.W_eq (H : E.BridgeHyp R typ kmin) : R.W = E.W := by
  unfold MX.Rule.W
  simp_rw [← H.hW]
  rw [← Finset.card_eq_sum_card_fiberwise (f := typ) (s := range E.W) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  simp

lemma srcU_iff (H : E.BridgeHyp R typ kmin) (n h μ r sc x : ℕ) (hs : sc < E.W^h) (hx : x < E.W) :
    E.srcU n h μ r (x + E.W * sc) ↔
      (inRS E.W E.tq R.m n h (μ * r) sc ∧ n < R.m * (μ * MXR.colS E.W E.tq (h + 1) (x + E.W * sc))) := by
  have hW := E.W_pos
  have hdiv : (x + E.W * sc) / E.W = sc := by
    rw [Nat.add_mul_div_left _ _ hW, Nat.div_eq_of_lt hx, zero_add]
  have hlt : x + E.W * sc < E.W^(h+1) := by
    have h1 : x + E.W * sc < E.W + E.W * sc := Nat.add_lt_add_right hx _
    have h2 : E.W + E.W * sc = E.W * (sc + 1) := by ring
    have h3 : E.W * (sc + 1) ≤ E.W * E.W^h := Nat.mul_le_mul_left _ hs
    have h4 : E.W * E.W^h = E.W^(h+1) := by ring
    omega
  unfold srcU inRS
  rw [hdiv, H.hm]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, Nat.lt_of_not_le (fun h3 => h2 ⟨hlt, h3⟩)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun h3 => Nat.not_le.mpr h2 h3.2⟩

/-- The program's count of a child's source slots is Flow's `card srcMS`. -/
lemma count_srcU_eq (H : E.BridgeHyp R typ kmin) (n h μ r : ℕ) :
    Nat.count (E.srcU n h μ r) (E.W^h * E.W) = Multiset.card (R.srcMS n h (μ * r) μ) := by
  rw [← R.card_srcMS_eq typ E.W_pos (tq := E.tq) H.htq H.hW n h (μ * r) μ]
  rw [Nat.count_eq_card_filter_range, Finset.card_filter, MX.sum_range_mul_split]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun sc hsc => ?_)
  have hs := Finset.mem_range.1 hsc
  rw [Finset.card_filter]
  by_cases hin : inRS E.W E.tq R.m n h (μ * r) sc
  · rw [if_pos hin]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    have key := srcU_iff H n h μ r sc x hs (Finset.mem_range.1 hx)
    by_cases hk : E.srcU n h μ r (x + E.W * sc)
    · rw [if_pos hk, if_pos (key.1 hk).2]
    · rw [if_neg hk, if_neg (fun h2 => hk (key.2 ⟨hin, h2⟩))]
  · rw [if_neg hin]
    refine Finset.sum_eq_zero (fun x hx => ?_)
    have key := srcU_iff H n h μ r sc x hs (Finset.mem_range.1 hx)
    rw [if_neg (fun hk => hin (key.1 hk).1)]

/-- **The subtree consumption is `card srcBelow`.** -/
theorem BridgeHyp.card_srcBelow_eq (H : E.BridgeHyp R typ kmin) (n : ℕ) :
    ∀ h μ, Multiset.card (R.srcBelow n h μ) = E.cons n h μ := by
  intro h
  induction h with
  | zero => intro μ; simp [MX.Rule.srcBelow, cons_zero]
  | succ h ih =>
    intro μ
    rw [cons_succ_idx]
    simp only [MX.Rule.srcBelow, Multiset.card_sum, Multiset.card_add]
    rw [← Fin.sum_univ_eq_sum_range (fun j => Nat.count (E.srcU n h μ (E.rkI j)) (E.W^h * E.W) +
      E.cons n h (μ * E.rkI j)) E.nB]
    have hP := H.hP
    refine Fintype.sum_equiv (finCongr hP) _ _ (fun j => ?_)
    rw [ih, ← count_srcU_eq H, H.hrk j]
    rfl

/-- **Vectors per tree copy = `Nsrc`.** -/
theorem BridgeHyp.topN_eq (H : E.BridgeHyp R typ kmin) (n : ℕ) : E.topN kmin n = R.Nsrc n := by
  unfold topN topNU0 MX.Rule.Nsrc MX.Rule.srcT
  rw [Multiset.card_add, R.card_inMS, ← H.topG_eq n, H.card_srcBelow_eq n, H.NUc_eq]
  congr 1
  unfold MX.Rule.unitsC
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [← Finset.mul_sum, ← H.W_eq]
  rfl


/-! ### The multisets of sizes -/

/-- Summing over the units of a class (by `Nat.nth`) is summing over its region codes. -/
lemma sum_units {M : Type*} [AddCommMonoid M] (n h μ : ℕ) (g : ℕ → M) :
    ∑ p ∈ Finset.range (E.NUc n h μ), g (E.Uc n h μ p) =
      ∑ sc ∈ (Finset.range (E.W^h)).filter (inRS E.W E.tq E.mx n h μ), g sc := by
  refine Finset.sum_bij (fun p _ => E.Uc n h μ p) ?_ ?_ ?_ ?_
  · intro p hp
    have hU := U_spec (Finset.mem_range.1 hp)
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨hU.2.1, hU.1⟩
  · intro p1 hp1 p2 hp2 heq
    have e1 := PC_U (Finset.mem_range.1 hp1)
    have e2 := PC_U (Finset.mem_range.1 hp2)
    rw [← e1, ← e2]; exact congrArg _ heq
  · intro sc hsc
    simp only [Finset.mem_filter, Finset.mem_range] at hsc
    exact ⟨E.PCc n h μ sc, Finset.mem_range.2 (PC_lt hsc.2), U_PC hsc.2⟩
  · intro p _; rfl

lemma coe_map_range_split (N : ℕ) (f : ℕ → ℕ) :
    ((List.range (N * E.W)).map f : Multiset ℕ) = ∑ p ∈ Finset.range N, ∑ a ∈ Finset.range E.W, {f (a + E.W * p)} := by
  have : ((List.range (N * E.W)).map f : Multiset ℕ) = ∑ t ∈ Finset.range (N * E.W), {f t} := by
    induction (N * E.W) with
    | zero => simp
    | succ M ih => rw [List.range_succ, List.map_append, ← Multiset.coe_add, ih, Finset.sum_range_succ]; simp
  rw [this, MX.sum_range_mul_split]

/-- **The sizes of a class's own slots are `inMS`.** -/
theorem BridgeHyp.own_sizes (H : E.BridgeHyp R typ kmin) (n h μ : ℕ) :
    ((List.range (E.NUc n h μ * E.W)).map (E.slotSize n h μ) : Multiset ℕ) = R.inMS n h μ := by
  rw [coe_map_range_split]
  have hW := E.W_pos
  have e1 : ∀ p a, a < E.W → E.slotSize n h μ (a + E.W * p) = E.tq a * E.cUc n h μ p := by
    intro p a ha
    unfold slotSize
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha, Nat.add_mul_div_left _ _ hW, Nat.div_eq_of_lt ha, zero_add]
  have e2 : ∀ p ∈ Finset.range (E.NUc n h μ), ∑ a ∈ Finset.range E.W, ({E.slotSize n h μ (a + E.W * p)} : Multiset ℕ) =
      (fun sc => ∑ a ∈ Finset.range E.W, ({E.tq a * (μ * MXR.colS E.W E.tq h sc)} : Multiset ℕ)) (E.Uc n h μ p) := by
    intro p _
    refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [e1 p a (Finset.mem_range.1 ha)]; rfl
  rw [Finset.sum_congr rfl e2, sum_units (E := E) n h μ
    (fun sc => ∑ a ∈ Finset.range E.W, ({E.tq a * (μ * MXR.colS E.W E.tq h sc)} : Multiset ℕ))]
  -- to a sum over all codes of a function of the type point
  let F : R.Pt → Multiset ℕ := fun b => if R.m * μ * R.col b ≤ n then
      ∑ k, R.Wk k • ({μ * R.kr k * R.col b} : Multiset ℕ) else 0
  have e3 : ∑ sc ∈ (Finset.range (E.W^h)).filter (inRS E.W E.tq E.mx n h μ),
      ∑ a ∈ Finset.range E.W, ({E.tq a * (μ * MXR.colS E.W E.tq h sc)} : Multiset ℕ) =
      ∑ sc ∈ Finset.range (E.W^h), F (R.cntS typ E.W h sc) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun sc hsc => ?_)
    have hs := Finset.mem_range.1 hsc
    have hcol := R.colS_eq_col typ hW H.htq h sc
    simp only [F, inRS, hs, true_and, hcol, H.hm, mul_assoc]
    split_ifs with hc
    · rw [Finset.sum_congr rfl (fun a ha => by rw [H.htq a (Finset.mem_range.1 ha)])]
      rw [R.sum_roles_by_type typ H.hW (fun k => ({R.kr k * (μ * R.col (R.cntS typ E.W h sc))} : Multiset ℕ))]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      congr 2; ring
    · rfl
  rw [e3, R.sum_codes typ H.hW h F]
  unfold MX.Rule.inMS MX.Rule.pts
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp only [F]
  split_ifs with hb
  · rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [smul_smul, mul_comm]
  · simp


lemma coe_filterMap_range (N : ℕ) (P : ℕ → Prop) [DecidablePred P] (f : ℕ → ℕ) :
    (((List.range N).filterMap (fun t => if P t then some (f t) else none)) : Multiset ℕ) =
      ∑ t ∈ Finset.range N, (if P t then ({f t} : Multiset ℕ) else 0) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.filterMap_append, ← Multiset.coe_add, ih, Finset.sum_range_succ]
    by_cases hp : P N <;> simp [hp]

lemma Gs_eq (H : E.BridgeHyp R typ kmin) (n h μ r sc : ℕ) (hs : sc < E.W^h) :
    ∑ a ∈ Finset.range E.W, (if ¬ inRS E.W E.tq E.mx n (h+1) μ (a + E.W * sc) then
      ({E.tq a * (μ * r * MXR.colS E.W E.tq h sc)} : Multiset ℕ) else 0) =
    ∑ k, R.Wk k • (if n < R.m * μ * R.col (R.cntS typ E.W h sc + R.e k) then
      ({μ * r * R.kr k * R.col (R.cntS typ E.W h sc)} : Multiset ℕ) else 0) := by
  have hW := E.W_pos
  have hcol := R.colS_eq_col typ hW H.htq h sc
  have e4 : ∀ a ∈ Finset.range E.W, (if ¬ inRS E.W E.tq E.mx n (h+1) μ (a + E.W * sc) then
      ({E.tq a * (μ * r * MXR.colS E.W E.tq h sc)} : Multiset ℕ) else 0) =
      (fun k => if n < R.m * μ * R.col (R.cntS typ E.W h sc + R.e k) then
        ({μ * r * R.kr k * R.col (R.cntS typ E.W h sc)} : Multiset ℕ) else 0) (typ a) := by
    intro a ha
    have ha' := Finset.mem_range.1 ha
    have hlt : a + E.W * sc < E.W^(h+1) := by
      have h1 : a + E.W * sc < E.W + E.W * sc := Nat.add_lt_add_right ha' _
      have h2 : E.W + E.W * sc = E.W * (sc + 1) := by ring
      have h3 : E.W * (sc + 1) ≤ E.W * E.W^h := Nat.mul_le_mul_left _ hs
      have h4 : E.W * E.W^h = E.W^(h+1) := by ring
      omega
    have hc1 : MXR.colS E.W E.tq (h+1) (a + E.W * sc) = R.kr (typ a) * R.col (R.cntS typ E.W h sc) := by
      rw [MXR.colS_cons _ _ _ _ _ ha', H.htq a ha', hcol]
    have hc2 : R.col (R.cntS typ E.W h sc + R.e (typ a)) = R.kr (typ a) * R.col (R.cntS typ E.W h sc) :=
      R.col_add_e _ _
    have hiff : ¬ inRS E.W E.tq E.mx n (h+1) μ (a + E.W * sc) ↔
        n < R.m * μ * R.col (R.cntS typ E.W h sc + R.e (typ a)) := by
      unfold inRS
      rw [hc1, hc2, ← H.hm]
      constructor
      · intro h1; by_contra h2; push_neg at h2; exact h1 ⟨hlt, by rw [← mul_assoc]; exact h2⟩
      · intro h1 h2; have := h2.2; rw [← mul_assoc] at this; omega
    have hval : E.tq a * (μ * r * MXR.colS E.W E.tq h sc) = μ * r * R.kr (typ a) * R.col (R.cntS typ E.W h sc) := by
      rw [H.htq a ha', hcol]; ring
    show _ = if n < R.m * μ * R.col (R.cntS typ E.W h sc + R.e (typ a)) then
        ({μ * r * R.kr (typ a) * R.col (R.cntS typ E.W h sc)} : Multiset ℕ) else 0
    by_cases hc : n < R.m * μ * R.col (R.cntS typ E.W h sc + R.e (typ a))
    · rw [if_pos (hiff.2 hc), if_pos hc, hval]
    · rw [if_neg (fun h1 => hc (hiff.1 h1)), if_neg hc]
  rw [Finset.sum_congr rfl e4, R.sum_roles_by_type typ H.hW (fun k =>
    if n < R.m * μ * R.col (R.cntS typ E.W h sc + R.e k) then
      ({μ * r * R.kr k * R.col (R.cntS typ E.W h sc)} : Multiset ℕ) else 0)]

/-- **The sizes of a child's source slots are `srcMS`.** -/
theorem BridgeHyp.ownSrc_sizes (H : E.BridgeHyp R typ kmin) (n h μ r : ℕ) :
    ((E.ownSrc n h μ r) : Multiset ℕ) = R.srcMS n h (μ * r) μ := by
  have hW := E.W_pos
  unfold ownSrc
  rw [coe_filterMap_range, MX.sum_range_mul_split]
  let Gs : ℕ → Multiset ℕ := fun sc => ∑ a ∈ Finset.range E.W,
    (if ¬ inRS E.W E.tq E.mx n (h+1) μ (a + E.W * sc) then
      ({E.tq a * (μ * r * MXR.colS E.W E.tq h sc)} : Multiset ℕ) else 0)
  have e2 : ∀ p ∈ Finset.range (E.NUc n h (μ * r)), ∑ a ∈ Finset.range E.W,
      (if E.srcP n h μ r (a + E.W * p) then ({E.slotSize n h (μ * r) (a + E.W * p)} : Multiset ℕ) else 0) =
      Gs (E.Uc n h (μ * r) p) := by
    intro p hp
    refine Finset.sum_congr rfl (fun a ha => ?_)
    have ha' := Finset.mem_range.1 ha
    have hp' := Finset.mem_range.1 hp
    have hmod : (a + E.W * p) % E.W = a := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha']
    have hdiv : (a + E.W * p) / E.W = p := by rw [Nat.add_mul_div_left _ _ hW, Nat.div_eq_of_lt ha', zero_add]
    have hlt : a + E.W * p < E.NUc n h (μ * r) * E.W := by
      calc a + E.W * p < E.W + E.W * p := Nat.add_lt_add_right ha' _
        _ = (p + 1) * E.W := by ring
        _ ≤ E.NUc n h (μ * r) * E.W := Nat.mul_le_mul_right _ hp'
    have hpar : E.parCode n h μ r (a + E.W * p) = a + E.W * E.Uc n h (μ * r) p := by
      unfold parCode; rw [hmod, hdiv]
    have hsrc : E.srcP n h μ r (a + E.W * p) ↔ ¬ inRS E.W E.tq E.mx n (h+1) μ (a + E.W * E.Uc n h (μ * r) p) := by
      unfold srcP; rw [hpar]; exact ⟨fun h1 => h1.2, fun h1 => ⟨hlt, h1⟩⟩
    have hsz : E.slotSize n h (μ * r) (a + E.W * p) = E.tq a * (μ * r * MXR.colS E.W E.tq h (E.Uc n h (μ * r) p)) := by
      unfold slotSize; rw [hmod, hdiv]; rfl
    show _ = if ¬ inRS E.W E.tq E.mx n (h+1) μ (a + E.W * E.Uc n h (μ * r) p) then
      ({E.tq a * (μ * r * MXR.colS E.W E.tq h (E.Uc n h (μ * r) p))} : Multiset ℕ) else 0
    by_cases hc : E.srcP n h μ r (a + E.W * p)
    · rw [if_pos hc, if_pos (hsrc.1 hc), hsz]
    · rw [if_neg hc, if_neg (fun h1 => hc (hsrc.2 h1))]
  rw [Finset.sum_congr rfl e2, sum_units (E := E) n h (μ * r) Gs]
  let F : R.Pt → Multiset ℕ := fun b => if R.m * (μ * r) * R.col b ≤ n then
      ∑ k, R.Wk k • (if n < R.m * μ * R.col (b + R.e k) then ({μ * r * R.kr k * R.col b} : Multiset ℕ) else 0)
      else 0
  have e3 : ∑ sc ∈ (Finset.range (E.W^h)).filter (inRS E.W E.tq E.mx n h (μ * r)), Gs sc =
      ∑ sc ∈ Finset.range (E.W^h), F (R.cntS typ E.W h sc) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun sc hsc => ?_)
    have hs := Finset.mem_range.1 hsc
    have hcol := R.colS_eq_col typ hW H.htq h sc
    have hreg : inRS E.W E.tq E.mx n h (μ * r) sc ↔ R.m * (μ * r) * R.col (R.cntS typ E.W h sc) ≤ n := by
      have e : R.m * (μ * r * R.col (R.cntS typ E.W h sc)) = R.m * (μ * r) * R.col (R.cntS typ E.W h sc) := by ring
      unfold inRS; rw [hcol, ← H.hm, e]; exact ⟨fun h1 => h1.2, fun h1 => ⟨hs, h1⟩⟩
    show _ = if R.m * (μ * r) * R.col (R.cntS typ E.W h sc) ≤ n then _ else 0
    by_cases hc : R.m * (μ * r) * R.col (R.cntS typ E.W h sc) ≤ n
    · rw [if_pos (hreg.2 hc), if_pos hc]
      exact Gs_eq H n h μ r sc hs
    · rw [if_neg (fun h1 => hc (hreg.1 h1)), if_neg hc]
  rw [e3, R.sum_codes typ H.hW h F]
  unfold MX.Rule.srcMS MX.Rule.pts
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp only [F]
  split_ifs with hb
  · rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    split_ifs <;> simp [smul_smul, mul_comm]
  · simp


lemma coe_flatMap {β γ : Type*} (L : List β) (f : β → List γ) :
    ((L.flatMap f : List γ) : Multiset γ) = (L.map (fun x => ((f x : List γ) : Multiset γ))).sum := by
  induction L with
  | nil => simp
  | cons a L ih => rw [List.flatMap_cons, ← Multiset.coe_add, ih, List.map_cons, List.sum_cons]

lemma sum_map_getD' {β M : Type*} [AddCommMonoid M] (L : List β) (z : β) (g : β → M) :
    (L.map g).sum = ∑ j ∈ Finset.range L.length, g (L.getD j z) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.sum_cons, ih, List.length_cons, Finset.sum_range_succ']
    simp [add_comm]

/-- **The consumed sizes of a subtree are `srcBelow`.** -/
theorem BridgeHyp.srcSizes_eq (H : E.BridgeHyp R typ kmin) (n : ℕ) :
    ∀ h μ, ((E.srcSizes n h μ : List ℕ) : Multiset ℕ) = R.srcBelow n h μ := by
  intro h
  induction h with
  | zero => intro μ; simp [srcSizes, MX.Rule.srcBelow]
  | succ h ih =>
    intro μ
    simp only [srcSizes, MX.Rule.srcBelow]
    rw [coe_flatMap, sum_map_getD' _ 0]
    rw [← Fin.sum_univ_eq_sum_range (fun j => (((E.ownSrc n h μ ((blockRanks E.wd).getD j 0) ++
      E.srcSizes n h (μ * (blockRanks E.wd).getD j 0)) : List ℕ) : Multiset ℕ)) (blockRanks E.wd).length]
    refine (Fintype.sum_equiv (finCongr H.hP) _ _ (fun j => ?_)).symm
    rw [← Multiset.coe_add, ih, H.ownSrc_sizes, H.hrk j]
    rfl

lemma map_getD_range {β : Type*} (L : List β) (z : β) : (List.range L.length).map (fun k => L.getD k z) = L := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp [List.getElem?_eq_getElem h2]

/-- **The sizes of one tree copy's vectors are the sources `srcT`.** -/
theorem BridgeHyp.topSz_eq (H : E.BridgeHyp R typ kmin) (n : ℕ) :
    (((List.range (E.topN kmin n)).map (E.topSz kmin n) : List ℕ) : Multiset ℕ) = R.srcT n := by
  unfold topN MX.Rule.srcT
  rw [List.range_add, List.map_append, ← Multiset.coe_add, ← H.topG_eq n]
  congr 1
  · rw [show (List.range (E.topNU0 kmin n * E.W)).map (E.topSz kmin n) =
        (List.range (E.NUc n (E.topG kmin n) 1 * E.W)).map (E.slotSize n (E.topG kmin n) 1) from
      List.map_congr_left (fun j hj => by
        unfold topSz; rw [if_pos (List.mem_range.1 hj)])]
    exact H.own_sizes n _ 1
  · rw [List.map_map]
    rw [show (List.range (E.cons n (E.topG kmin n) 1)).map (E.topSz kmin n ∘ (E.topNU0 kmin n * E.W + ·)) =
        (List.range (E.srcSizes n (E.topG kmin n) 1).length).map (fun k => (E.srcSizes n (E.topG kmin n) 1).getD k 0) from
      List.map_congr_left (fun k hk => by
        simp only [Function.comp, topSz]
        rw [if_neg (by omega), Nat.add_sub_cancel_left]; rfl)]
    rw [map_getD_range, H.srcSizes_eq]


/-- **The calls of a top job have exactly the shapes the bill charges** (`kidsS`). -/
theorem BridgeHyp.kidsTop_shape (H : E.BridgeHyp R typ kmin) (sh : MDesc → MX.Shape)
    (hsh1 : ∀ n B v, sh (MDesc.top n B v) = MX.Shape.top n B)
    (hsh2 : ∀ n h μ o BS J sup, sh (MDesc.cls n h μ o BS J sup) = MX.Shape.cls n h μ)
    (n0 n B : ℕ) (v : ℕ → Bits n → ℂ) :
    (((E.kidsTop kmin n0 n B v).map sh : List MX.Shape) : Multiset MX.Shape) = R.kidsS n0 (MX.Shape.top n B) := by
  unfold kidsTop
  simp only [MX.Rule.kidsS]
  rw [H.topN_eq n]
  by_cases hc : n0 ≤ n ∧ R.Nsrc n ≤ B
  · rw [if_pos hc, if_pos hc]
    rw [List.map_flatMap, coe_flatMap, ← H.topN_eq n]
    have e1 : ∀ t, (((E.topRoot kmin n B v t :: (List.range (E.topN kmin n)).map (E.topRest kmin n v t)).map sh :
        List MX.Shape) : Multiset MX.Shape) =
        {MX.Shape.cls n (R.G n) 1} + (R.srcT n).map (fun s => MX.Shape.top (n - s) (2 ^ s)) := by
      intro t
      rw [List.map_cons, List.map_map, ← Multiset.cons_coe, Multiset.singleton_add]
      congr 1
      · unfold topRoot; rw [hsh2, H.topG_eq]
      · rw [← H.topSz_eq n, Multiset.map_coe, List.map_map]
        congr 1
        refine List.map_congr_left (fun j _ => ?_)
        simp only [Function.comp]
        unfold topRest; rw [hsh1]
    simp_rw [e1]
    rw [List.map_const', List.sum_replicate, List.length_range, nsmul_add, Multiset.nsmul_singleton]
    unfold MX.Rule.restMS
    rfl
  · rw [if_neg hc, if_neg hc]
    rfl

end Eng

end
end PowerSaving.RAM
end OAI

#print axioms OAI.PowerSaving.RAM.Eng.BridgeHyp.topN_eq
#print axioms OAI.PowerSaving.RAM.Eng.BridgeHyp.own_sizes
#print axioms OAI.PowerSaving.RAM.Eng.BridgeHyp.ownSrc_sizes
#print axioms OAI.PowerSaving.RAM.Eng.BridgeHyp.topSz_eq
#print axioms OAI.PowerSaving.RAM.Eng.BridgeHyp.kidsTop_shape
