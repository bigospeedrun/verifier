import Submission.Work.TensorEng.Strict
import Submission.Work.Mixed.Bridge.CoreK
import Submission.Work.MixedCost.EngineFinal

/-!
# The strictified tensor power as an engine of Theorem 1G, and its engine theorem

For a bundled certified unit `A` (paid ranks `P = A.ranks`, target ranks `T = A.tgts`), the `(n+1)`-fold tensor
power, completed to `L` and split at `J < L` (`Strict.lean`), is an `Eng` (the leader's engine data) whose paid
ranks are `strictP T P (n+1) J L` and whose live target ranks are `strictT T (n+1) L`.  With the moment fact
`mom z1 (strictP …) ≤ mom z1 (strictT …)` (`TensorProto.strictify`), p3-port's `bundle_ofList` (K-target rule)
and the leader's `Eng.engine_seam_final` give OpenAI's `hills_program` shape at every `zE ∈ (z1, 1]`:
`tensor_engine`.

-- changed for the tensor-power extension (30103/10000000); see Submission.lean
-/

namespace TensorEng
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.GF OAI.PowerSaving.MX OAI.PowerSaving.RAM
open OAI.PowerSaving.RAM.Ty Matrix Finset
open TensorProto (mom tens tpow pieces splitAll padT comp strictT strictP)

noncomputable section

/-! ### histogram lists of multisets -/

section Hist

/-- The histogram list `(rank, count)` of a multiset of ranks (distinct ranks). -/
def histL (s : Multiset ℕ) : List (ℕ × ℕ) := s.toFinset.toList.map fun r => (r, s.count r)

lemma histL_fst (s : Multiset ℕ) : (histL s).map Prod.fst = s.toFinset.toList := by
  simp [histL, List.map_map, Function.comp_def]

lemma histL_nodup (s : Multiset ℕ) : ((histL s).map Prod.fst).Nodup := by
  rw [histL_fst]; exact Finset.nodup_toList _

lemma mem_histL_fst {s : Multiset ℕ} {r : ℕ} : r ∈ (histL s).map Prod.fst ↔ r ∈ s := by
  rw [histL_fst]; simp

lemma mem_histL {s : Multiset ℕ} {b : ℕ × ℕ} (hb : b ∈ histL s) : b.1 ∈ s ∧ b.2 = s.count b.1 := by
  unfold histL at hb
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hb
  exact ⟨Multiset.mem_toFinset.1 (Finset.mem_toList.1 hr), rfl⟩

lemma histL_mem {s : Multiset ℕ} {r : ℕ} (hr : r ∈ s) : (r, s.count r) ∈ histL s :=
  List.mem_map.2 ⟨r, Finset.mem_toList.2 (Multiset.mem_toFinset.2 hr), rfl⟩

lemma histFn_eq_sum (l : List (ℕ × ℕ)) (r : ℕ) :
    BlockAccounting.histFn l r = (l.map fun b => if b.1 = r then b.2 else 0).sum := by
  unfold BlockAccounting.histFn
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [List.filter_cons]
    by_cases h : b.1 = r
    · simp [h, ih]
    · simp [h, ih]

lemma histFn_histL (s : Multiset ℕ) (r : ℕ) : BlockAccounting.histFn (histL s) r = s.count r := by
  rw [histFn_eq_sum, histL, List.map_map]
  rw [show ((fun b : ℕ × ℕ => if b.1 = r then b.2 else 0) ∘ fun r' => (r', s.count r'))
      = fun r' => if r' = r then s.count r' else 0 from rfl]
  rw [Finset.sum_map_toList, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [Multiset.mem_toFinset] at h
    exact (Multiset.count_eq_zero.2 h).symm

lemma moment_histL (m : ℕ) (z : ℝ) (s : Multiset ℕ) :
    BlockAccounting.moment m z (histL s) = mom z s / (m : ℝ) ^ z := by
  unfold BlockAccounting.moment histL TensorProto.mom
  rw [List.map_map, Finset.sum_map_toList, Finset.sum_multiset_map_count, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r _
  simp only [Function.comp_apply, nsmul_eq_mul]
  rw [Real.div_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  ring

lemma card_filter_tr {σ : Type*} [Fintype σ] [DecidableEq σ] (tr : σ → ℕ) (r : ℕ) :
    (Finset.univ.filter fun l : σ => tr l = r).card = ((Finset.univ : Finset σ).val.map tr).count r := by
  rw [Multiset.count_map]
  show Multiset.card (Finset.univ.filter fun l : σ => tr l = r).val = _
  rw [Finset.filter_val]
  congr 1
  apply Multiset.filter_congr
  intro l _
  exact eq_comm

lemma hist_eq_count {α ρ : Type*} (w : GWord α ρ) (r : ℕ) :
    GWord.hist w r = (w.filterMap GMove.rk?).count r := by
  induction w with
  | nil => rfl
  | cons mv w ih =>
    unfold GWord.hist at ih ⊢
    rw [GWord.shadow_cons, BWord.hist_cons, ih]
    cases h : mv.rk? with
    | none =>
      rw [List.filterMap_cons_none h]
      have h' : mv.shadow.rk? = none := h
      simp [h']
    | some k =>
      rw [List.filterMap_cons_some h, List.count_cons]
      have h' : mv.shadow.rk? = some k := h
      simp [h']

end Hist

/-! ### the strictified power as an engine -/

section Engine

lemma map_filter_eq_bind {β : Type*} (s : Multiset β) (p : β → Prop) [DecidablePred p] (f : β → ℕ) :
    (s.filter p).map f = s.bind (fun l => if p l then {f l} else 0) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.filter_cons, Multiset.cons_bind, Multiset.map_add, ih]
    split_ifs <;> simp

lemma rk_padWord {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] [Fintype σ]
    [DecidableEq σ] (U : CU α ρ σ) (L : ℕ) (hL : L ≤ Fintype.card α) :
    (U.padWord L hL).filterMap GMove.rk? = (U.lowList L).map fun l => L - U.tr l := by
  unfold CU.padWord
  induction U.lowList L with
  | nil => rfl
  | cons l ls ih => exact congrArg ((L - U.tr l) :: ·) ih

/-- Ranks of the completion word. -/
lemma ranks_padWord {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] [Fintype σ]
    [DecidableEq σ] (U : CU α ρ σ) (L : ℕ) (hL : L ≤ Fintype.card α) :
    (((U.padWord L hL).filterMap GMove.rk? : List ℕ) : Multiset ℕ)
      = comp L ((Finset.univ : Finset σ).val.map U.tr) := by
  rw [rk_padWord]
  unfold TensorProto.comp CU.lowList
  rw [Multiset.bind_map, ← Multiset.map_coe, Finset.coe_toList, Finset.filter_val, map_filter_eq_bind]

lemma proper_of_rk {α ρ : Type*} {u : ℕ} (mv : GMove α ρ) (h : ∀ r, mv.rk? = some r → 1 ≤ r ∧ r < u) :
    mv.Proper u := by
  cases mv with
  | old mv =>
    cases mv with
    | localM g => trivial
    | shift l z => trivial
    | block l rk z ind => exact h rk rfl
  | perm l G => trivial
  | phase l z c => trivial

namespace BU
variable (A : BU)

/-- The completed (to `L`), split (at `J`) `(n+1)`-fold power, as a certified unit. -/
def strictCU (n J L : ℕ) (hL : L ≤ Fintype.card (A.pow n).α) :
    CU (A.pow n).α (A.pow n).ρ (A.pow n).σ :=
  { (A.pow n).u.pad L hL with
    wd := splitW J ((A.pow n).u.pad L hL).wd
    hw := GLiveKernelM.splitW J ((A.pow n).u.pad L hL).hw }

lemma strictCU_ranks (n J L : ℕ) (hL : L ≤ Fintype.card (A.pow n).α) (hJ : 0 < J) (hR : A.RanksOK) :
    (((A.strictCU n J L hL).wd.filterMap GMove.rk? : List ℕ) : Multiset ℕ)
      = strictP A.tgts A.ranks (n + 1) J L := by
  have hpos : ∀ r ∈ ((A.pow n).u.wd ++ (A.pow n).u.padWord L hL).filterMap GMove.rk?, 0 < r := by
    intro r hr
    rw [List.filterMap_append, List.mem_append] at hr
    rcases hr with hr | hr
    · exact (BU.ranksOK_pow hR n r hr).1
    · rw [rk_padWord] at hr
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hr
      have : (A.pow n).u.tr l < L := by simpa [CU.lowList] using hl
      omega
  show ((((splitW J ((A.pow n).u.wd ++ (A.pow n).u.padWord L hL)).filterMap GMove.rk?) : List ℕ)
    : Multiset ℕ) = _
  rw [ranks_splitW J hJ _ hpos]
  unfold strictP
  rw [List.filterMap_append, ← Multiset.coe_add, ranks_padWord]
  have e1 : (((A.pow n).u.wd.filterMap GMove.rk? : List ℕ) : Multiset ℕ) = tpow A.ranks (n + 1) :=
    BU.ranks_pow A n
  have e2 : (Finset.univ : Finset (A.pow n).σ).val.map (A.pow n).u.tr = tpow A.tgts (n + 1) :=
    BU.tgts_pow A n
  rw [e1, e2]

lemma strictCU_tgts (n J L : ℕ) (hL : L ≤ Fintype.card (A.pow n).α) :
    (Finset.univ : Finset (A.pow n).σ).val.map (A.strictCU n J L hL).tr = strictT A.tgts (n + 1) L := by
  unfold strictT padT
  rw [← BU.tgts_pow A n]
  show _ = Multiset.map _ (Multiset.map (A.pow n).u.tr _)
  rw [Multiset.map_map]
  congr 1
  funext l
  show (A.pow n).u.tr l + (L - (A.pow n).u.tr l) = max ((A.pow n).u.tr l) L
  rcases le_total ((A.pow n).u.tr l) L with h | h
  · rw [max_eq_right h]; omega
  · rw [max_eq_left h]; omega

lemma strictCU_rk_le (n J L : ℕ) (hL : L ≤ Fintype.card (A.pow n).α) (hJ : 0 < J) (hR : A.RanksOK)
    (hT : A.TgtsOK) {mv : GMove (A.pow n).α (A.pow n).ρ} (hmv : mv ∈ (A.strictCU n J L hL).wd) {r : ℕ}
    (hr : mv.rk? = some r) : 1 ≤ r ∧ r ≤ J := by
  have hm : r ∈ strictP A.tgts A.ranks (n + 1) J L := by
    rw [← strictCU_ranks A n J L hL hJ hR]
    exact Multiset.mem_coe.2 (List.mem_filterMap.2 ⟨mv, hmv, hr⟩)
  refine ⟨TensorProto.splitAll_pos hJ (fun R hR' => ?_) r hm, TensorProto.strictP_le hJ r hm⟩
  rcases Multiset.mem_add.1 hR' with h | h
  · have hb := TensorProto.tpow_bounds (lo := 1) (hi := Fintype.card A.α)
      (fun x hx => ⟨(hR x (Multiset.mem_coe.1 hx)).1, (hR x (Multiset.mem_coe.1 hx)).2.le⟩) (n + 1) R h
    simpa using hb.1
  · exact TensorProto.comp_pos R h

/-- **The strictified power as the leader's engine data.** -/
def strictEng (n J L : ℕ) (hL : L ≤ Fintype.card (A.pow n).α) (hJ : 0 < J) (hJL : J < L) (hR : A.RanksOK)
    (hT : A.TgtsOK) (hσ : 0 < Fintype.card (A.pow n).σ) (h3 : 3 ≤ Fintype.card (A.pow n).α) :
    Eng (A.pow n).α (A.pow n).ρ (A.pow n).σ where
  X := Layout.someLayout _
  R := Layout.someLayout _
  Q := Layout.someLayout _
  e := (A.strictCU n J L hL).e
  he := (A.strictCU n J L hL).he
  tr := (A.strictCU n J L hL).tr
  tz := (A.strictCU n J L hL).tz
  tind := (A.strictCU n J L hL).tind
  tr_le := fun l => by
    rw [← Layout.card]
    have := (BU.tgtsOK_pow hT n l).2
    show (A.pow n).u.tr l + (L - (A.pow n).u.tr l) ≤ _
    omega
  tr_pos := fun l => by
    have := (BU.tgtsOK_pow hT n l).1
    show 1 ≤ (A.pow n).u.tr l + (L - (A.pow n).u.tr l)
    omega
  wd := (A.strictCU n J L hL).wd
  hP := fun mv hmv => proper_of_rk mv (fun r hr => by
    rw [← Layout.card]
    have := strictCU_rk_le A n J L hL hJ hR hT hmv hr
    exact ⟨this.1, by omega⟩)
  sep := fun mv hmv r hr l => by
    have := strictCU_rk_le A n J L hL hJ hR hT hmv hr
    show r < (A.pow n).u.tr l + (L - (A.pow n).u.tr l)
    omega
  W_pos := by rw [← Layout.card]; exact hσ
  three := by rw [← Layout.card]; exact h3
  hw := (A.strictCU n J L hL).hw

universe u

/-- **THE TENSOR ENGINE THEOREM**: the strictified `(n+1)`-fold power of a certified unit, with the moment fact of
the strictified inventories at `z1`, gives OpenAI's `hills_program` shape at every `zE ∈ (z1, 1]`. -/
theorem tensor_engine (n J L : ℕ) (hL : L ≤ Fintype.card (A.pow n).α) (hJ : 0 < J) (hJL : J < L)
    (hR : A.RanksOK) (hT : A.TgtsOK) (hσ : 0 < Fintype.card (A.pow n).σ)
    (h3 : 3 ≤ Fintype.card (A.pow n).α) (hatt : L ∈ strictT A.tgts (n + 1) L) {z1 zE : ℝ}
    (hmom : mom z1 (strictP A.tgts A.ranks (n + 1) J L) ≤ mom z1 (strictT A.tgts (n + 1) L))
    (hz1 : 0 < z1) (h12 : z1 < zE) (hzE : zE ≤ 1) (m : Bool) (cl : Paint) {ι : Type u} (k : ι → ℕ)
    (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2 ^ k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2 ^ k i * envelope zE (k i)) := by
  let E := A.strictEng n J L hL hJ hJL hR hT hσ h3
  set Tg := strictT A.tgts (n + 1) L with hTg
  set Pd := strictP A.tgts A.ranks (n + 1) J L with hPd
  have hTgE : (Finset.univ : Finset (A.pow n).σ).val.map E.tr = Tg := strictCU_tgts A n J L hL
  have hPdE : ((E.wd.filterMap GMove.rk? : List ℕ) : Multiset ℕ) = Pd := strictCU_ranks A n J L hL hJ hR
  have hpos : 0 < (histL Tg).length := by
    have h1 : (L, Tg.count L) ∈ histL Tg := histL_mem hatt
    exact List.length_pos_of_mem h1
  have htrv : ∀ l, E.tr l ∈ (histL Tg).map Prod.fst := by
    intro l
    rw [mem_histL_fst, ← hTgE]
    exact Multiset.mem_map.2 ⟨l, Finset.mem_univ_val l, rfl⟩
  have htrc : ∀ k : Fin (histL Tg).length,
      (Finset.univ.filter fun l => E.tr l = ((histL Tg)[k.1]).1).card = 1 * ((histL Tg)[k.1]).2 := by
    intro k
    have hk := mem_histL (List.getElem_mem k.2)
    rw [one_mul, hk.2, card_filter_tr, hTgE]
  have hhist : ∀ r, E.wd.hist r = 1 * BlockAccounting.histFn (histL Pd) r := by
    intro r
    rw [one_mul, histFn_histL, ← hPdE, hist_eq_count, Multiset.coe_count]
  have hpaid : ∀ b ∈ histL Pd, b.1 ≤ J := fun b hb =>
    TensorProto.strictP_le hJ b.1 (mem_histL hb).1
  have hwr : ∀ mv ∈ E.wd, ∀ r, mv.rk? = some r → r ≤ J := fun mv hmv r hr =>
    (strictCU_rk_le A n J L hL hJ hR hT hmv hr).2
  have htg : ∀ b ∈ histL Tg, L ≤ b.1 ∧ b.1 ≤ Fintype.card (A.pow n).α := by
    intro b hb
    have h1 := (mem_histL hb).1
    refine ⟨TensorProto.strictT_ge b.1 h1, ?_⟩
    rw [← hTgE] at h1
    obtain ⟨l, _, hl⟩ := Multiset.mem_map.1 h1
    rw [← hl, Layout.card E.X]
    exact E.tr_le l
  have h2 : 2 ≤ L := by omega
  have hatt' : ∃ b ∈ histL Tg, b.1 = L ∧ 1 ≤ 1 * b.2 := by
    refine ⟨(L, Tg.count L), histL_mem hatt, rfl, ?_⟩
    rw [one_mul]
    exact Multiset.count_pos.2 hatt
  have hmom' : BlockAccounting.moment (Fintype.card (A.pow n).α) z1 (histL Pd)
      ≤ BlockAccounting.moment (Fintype.card (A.pow n).α) z1 (histL Tg) := by
    rw [moment_histL, moment_histL]
    apply div_le_div_of_nonneg_right hmom
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  obtain ⟨R, typ, hB, hRate⟩ := PB.bundle_ofList E (histL Tg) (histL Pd) 1 hpos (histL_nodup Tg) htrv htrc
    hhist hpaid hwr hJL htg h2 hatt' hmom'
  exact E.engine_seam_final hB E.mx le_rfl hRate hz1 h12 hzE m cl k v

end BU

end Engine

end

end TensorEng
