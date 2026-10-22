import Submission.Work.TensorEng.EngOf
import Submission.Work.TensorProto.P16A8ZRate

/-!
# The engine theorem of the 7760-fold tensor power of the raw p16a8 unit on S2979Z (#4470 provider)

`p16a8` is the query-thinned 16-pair controller (prefix `a = 8`: 18 full native calls, 15 rank-one thin queries per
port) on the S2979B provider and the 18-stage geometry with 145 label coordinates.  Per gauge copy its raw unit has
live target ranks `P16A8Z.TP16A8Z` = 4:504 7:126 8:846 9:5868 17:448 25:448 33:448 41:448 49:448 57:448
65:448 73:224 145:224 and paid ranks `P16A8Z.PP16A8Z` = 1:41946 2:6984 3:8892 4:2646 5:648 8:144 16:448 24:448 32:448
40:448 48:448 56:448 64:448 72:224 (raw root `0.0030201659…`).

Any bundled certified unit with `G` copies of these inventories gives OpenAI's `hills_program` shape at every
`zE ∈ (1 - 4719/1562500, 1]` (`4719/1562500 = 302016/10^8`) (`p16a8z_engine_G`): the unit is tensored 7760 times,
completed to `21^7760` and split at `20^7760` (`BU.tensor_engine`), with the moment fact `P16A8Z.strict`.
`p16a8z_engine_of_rawG` takes the RAW certificate (word, live roles, block targets) in the same shape as
`k4f_engine_of_rawG`.

The helper lemmas live in `TensorEng.P16A8ZE`, so this module can be imported together with the other engines.

-- changed for the tensor-power extension (30103/10000000); see Submission.lean
-/

namespace TensorEng
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.GF OAI.PowerSaving.MX OAI.PowerSaving.RAM
open OAI.PowerSaving.RAM.Ty Matrix Finset
open TensorProto (mom tens tpow padT strictT strictP)

noncomputable section

namespace P16A8ZE

lemma card_σ_pow (A : BU) (n : ℕ) : Fintype.card (A.pow n).σ = Fintype.card A.σ ^ (n + 1) := by
  induction n with
  | zero =>
    show Fintype.card A.σ = Fintype.card A.σ ^ (0 + 1)
    rw [zero_add, pow_one]
  | succ n ih =>
    show Fintype.card ((A.pow n).σ × A.σ) = _
    rw [Fintype.card_prod, ih]
    ring

lemma mem_ofHist_of {l : List (ℕ × ℕ)} {b : ℕ × ℕ} (hb : b ∈ l) (h : 0 < b.2) :
    b.1 ∈ TensorProto.P16A8Z.ofHist l := by
  induction l with
  | nil => simp at hb
  | cons a l ih =>
    have e : TensorProto.P16A8Z.ofHist (a :: l) = Multiset.replicate a.2 a.1 + TensorProto.P16A8Z.ofHist l := by
      simp [TensorProto.P16A8Z.ofHist]
    rw [e, Multiset.mem_add]
    rcases List.mem_cons.1 hb with h' | h'
    · subst h'; exact Or.inl (Multiset.mem_replicate.2 ⟨by omega, rfl⟩)
    · exact Or.inr (ih h')

/-- Multiplicities of a histogram multiset. -/
lemma count_ofHist (l : List (ℕ × ℕ)) (r : ℕ) :
    (TensorProto.P16A8Z.ofHist l).count r = BlockAccounting.histFn l r := by
  induction l with
  | nil => simp [TensorProto.P16A8Z.ofHist, BlockAccounting.histFn]
  | cons b l ih =>
    have e : TensorProto.P16A8Z.ofHist (b :: l) = Multiset.replicate b.2 b.1 + TensorProto.P16A8Z.ofHist l := by
      simp [TensorProto.P16A8Z.ofHist]
    rw [e, Multiset.count_add, ih, Multiset.count_replicate]
    unfold BlockAccounting.histFn
    rw [List.filter_cons]
    by_cases h : b.1 = r
    · subst h; simp
    · simp [h]

/-- Paid ranks of a proper word are `≥ 1` and `< u`. -/
lemma rk_bounds_of_proper {α ρ : Type*} {u : ℕ} {w : GWord α ρ} (hP : w.Proper u) {r : ℕ}
    (hr : r ∈ w.filterMap GMove.rk?) : 1 ≤ r ∧ r < u := by
  obtain ⟨mv, hmv, hmr⟩ := List.mem_filterMap.1 hr
  have h := hP mv hmv
  cases mv with
  | old mv =>
    cases mv with
    | localM g => cases hmr
    | shift l z => cases hmr
    | block l rk z ind =>
      have e : rk = r := Option.some.inj hmr
      subst e
      exact h
  | perm l G => cases hmr
  | phase l z c => cases hmr

/-! ### `G` copies of the unit: the strictified inventories scale by `G ^ v`, and so do their moments. -/

lemma bind_nsmul_left (k : ℕ) (s : Multiset ℕ) (f : ℕ → Multiset ℕ) : (k • s).bind f = k • s.bind f := by
  induction k with
  | zero => simp
  | succ k ih => rw [succ_nsmul, Multiset.add_bind, ih, succ_nsmul]

lemma bind_nsmul_right (k : ℕ) (s : Multiset ℕ) (f : ℕ → Multiset ℕ) :
    s.bind (fun a => k • f a) = k • s.bind f := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => rw [Multiset.cons_bind, Multiset.cons_bind, ih, nsmul_add]

lemma tens_nsmul (k k' : ℕ) (A B : Multiset ℕ) : tens (k • A) (k' • B) = (k * k') • tens A B := by
  unfold TensorProto.tens
  rw [bind_nsmul_left]
  have h : (fun a => Multiset.map (fun b => a * b) (k' • B)) = fun a => k' • Multiset.map (fun b => a * b) B := by
    funext a
    rw [Multiset.map_nsmul]
  rw [h, bind_nsmul_right, smul_smul]

lemma tpow_nsmul (k : ℕ) (A : Multiset ℕ) (v : ℕ) : tpow (k • A) v = (k ^ v) • tpow A v := by
  induction v with
  | zero => simp [TensorProto.tpow]
  | succ v ih =>
    show tens (tpow (k • A) v) (k • A) = (k ^ (v + 1)) • tens (tpow A v) A
    rw [ih, tens_nsmul, pow_succ]

lemma strictP_nsmul (k : ℕ) (T P : Multiset ℕ) (v J L : ℕ) :
    strictP (k • T) (k • P) v J L = (k ^ v) • strictP T P v J L := by
  unfold TensorProto.strictP TensorProto.splitAll TensorProto.comp
  rw [tpow_nsmul, tpow_nsmul, bind_nsmul_left, ← nsmul_add, bind_nsmul_left]

lemma strictT_nsmul (k : ℕ) (T : Multiset ℕ) (v L : ℕ) :
    strictT (k • T) v L = (k ^ v) • strictT T v L := by
  unfold TensorProto.strictT TensorProto.padT
  rw [tpow_nsmul, Multiset.map_nsmul]

lemma mom_nsmul (t : ℝ) (k : ℕ) (s : Multiset ℕ) : mom t (k • s) = k * mom t s := by
  unfold TensorProto.mom
  rw [Multiset.map_nsmul, Multiset.sum_nsmul, nsmul_eq_mul]

/-- The paid ranks of a unit from its word histogram, `G` copies. -/
lemma ranks_eq_of_histG (A : BU) (l : List (ℕ × ℕ)) (G : ℕ)
    (h : ∀ r, GWord.hist A.u.wd r = G * BlockAccounting.histFn l r) :
    A.ranks = G • TensorProto.P16A8Z.ofHist l := by
  ext r
  rw [Multiset.count_nsmul, count_ofHist, ← h, hist_eq_count]
  exact Multiset.coe_count r _

/-- The target ranks of a unit from the counts of its live roles, `G` copies. -/
lemma tgts_eq_of_cardG (A : BU) (l : List (ℕ × ℕ)) (G : ℕ)
    (h : ∀ r, (Finset.univ.filter fun s : A.σ => A.u.tr s = r).card = G * BlockAccounting.histFn l r) :
    A.tgts = G • TensorProto.P16A8Z.ofHist l := by
  ext r
  rw [Multiset.count_nsmul, count_ofHist, ← h, card_filter_tr]
  all_goals rfl

end P16A8ZE

universe u

/-- The tensor engine of `G` copies of the raw p16a8 unit on S2979Z (#4470 provider), the power `n + 1 = 7760` kept symbolic (no huge numerals
are ever evaluated). -/
theorem p16a8z_engine_G_v (A : BU) (G : ℕ) (hG : 1 ≤ G) (n : ℕ) (hn : n + 1 = 7760)
    (hPr : A.ranks = G • TensorProto.P16A8Z.ofHist TensorProto.P16A8Z.PP16A8Z)
    (hTg : A.tgts = G • TensorProto.P16A8Z.ofHist TensorProto.P16A8Z.TP16A8Z) (hR : A.RanksOK) (hT : A.TgtsOK)
    (hα : Fintype.card A.α = 145) (hσ : 0 < Fintype.card A.σ) {zE : ℝ}
    (h12 : 1 - (4719 : ℝ) / 1562500 < zE) (hzE : zE ≤ 1) (m : Bool) (cl : Paint) {ι : Type u} (k : ι → ℕ)
    (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2 ^ k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2 ^ k i * envelope zE (k i)) := by
  have hmom0 := TensorProto.P16A8Z.strict
  rw [← hn] at hmom0
  have hGv : (0 : ℝ) ≤ ((G ^ (n + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hmom : mom (1 - ((4719:ℝ)/1562500)) (strictP A.tgts A.ranks (n + 1) (20 ^ (n + 1)) (21 ^ (n + 1)))
      ≤ mom (1 - ((4719:ℝ)/1562500)) (strictT A.tgts (n + 1) (21 ^ (n + 1))) := by
    rw [hPr, hTg, P16A8ZE.strictP_nsmul, P16A8ZE.strictT_nsmul, P16A8ZE.mom_nsmul, P16A8ZE.mom_nsmul]
    exact mul_le_mul_of_nonneg_left hmom0 hGv
  have hL : 21 ^ (n + 1) ≤ Fintype.card (A.pow n).α := by
    rw [BU.card_pow, hα]
    exact Nat.pow_le_pow_left (by norm_num) (n + 1)
  have hJ : 0 < 20 ^ (n + 1) := pow_pos (by norm_num) (n + 1)
  have hJL : 20 ^ (n + 1) < 21 ^ (n + 1) := Nat.pow_lt_pow_left (by norm_num) (Nat.succ_ne_zero n)
  have hσ' : 0 < Fintype.card (A.pow n).σ := by
    rw [P16A8ZE.card_σ_pow]
    exact pow_pos hσ _
  have h3 : 3 ≤ Fintype.card (A.pow n).α := by
    rw [BU.card_pow, hα]
    exact le_trans (by norm_num) (Nat.le_self_pow (Nat.succ_ne_zero n) 145)
  have hatt : 21 ^ (n + 1) ∈ strictT A.tgts (n + 1) (21 ^ (n + 1)) := by
    rw [hTg, P16A8ZE.strictT_nsmul, Multiset.mem_nsmul_of_ne_zero (pow_ne_zero _ (by omega))]
    have h4 : 4 ∈ TensorProto.P16A8Z.ofHist TensorProto.P16A8Z.TP16A8Z :=
      P16A8ZE.mem_ofHist_of (b := (4, 504)) (by decide) (by norm_num)
    exact TensorProto.mem_padT (TensorProto.pow_mem_tpow h4 (n + 1))
      (Nat.pow_le_pow_left (by norm_num) (n + 1))
  exact A.tensor_engine n (20 ^ (n + 1)) (21 ^ (n + 1)) hL hJ hJL hR hT hσ' h3 hatt hmom
    (by norm_num) h12 hzE m cl k v

/-- **The tensor engine of `G` copies of the raw p16a8 unit on S2979Z (#4470 provider)**, saving `4719/1562500 = 0.00302016` at the rate point
(7760 factors). -/
theorem p16a8z_engine_G (A : BU) (G : ℕ) (hG : 1 ≤ G)
    (hPr : A.ranks = G • TensorProto.P16A8Z.ofHist TensorProto.P16A8Z.PP16A8Z)
    (hTg : A.tgts = G • TensorProto.P16A8Z.ofHist TensorProto.P16A8Z.TP16A8Z) (hR : A.RanksOK) (hT : A.TgtsOK)
    (hα : Fintype.card A.α = 145) (hσ : 0 < Fintype.card A.σ) {zE : ℝ}
    (h12 : 1 - (4719 : ℝ) / 1562500 < zE) (hzE : zE ≤ 1) (m : Bool) (cl : Paint) {ι : Type u} (k : ι → ℕ)
    (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2 ^ k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2 ^ k i * envelope zE (k i)) :=
  p16a8z_engine_G_v A G hG 7759 rfl hPr hTg hR hT hα hσ h12 hzE m cl k v

/-- **The tensor engine from a RAW certificate of `G` copies of the p16a8 unit** (the shape of p3-port's
`rawCert_exists` / `k4f_engine_of_rawG`): a word on 145 label coordinates with block targets whose live target ranks
and paid ranks are `G` copies of the raw p16a8 inventories. -/
theorem p16a8z_engine_of_rawG {α ρ σ : Type} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] [Fintype σ]
    [DecidableEq σ] (e : σ → ρ) (tr : σ → ℕ) (tz : ∀ l, Fin (tr l) → Space α) (wd : GWord α ρ) (G : ℕ)
    (he : Function.Injective e) (hind : ∀ l, LinearIndependent F (tz l)) (hP : wd.Proper (Fintype.card α))
    (hw : GLiveKernelM e (fun l => blockMat (tz l)) wd) (hG : 1 ≤ G) (hα : Fintype.card α = 145)
    (htr : ∀ l, 1 ≤ tr l ∧ tr l ≤ 145)
    (hcnt : ∀ r, (Finset.univ.filter fun l => tr l = r).card = G * BlockAccounting.histFn TensorProto.P16A8Z.TP16A8Z r)
    (hhist : ∀ r, wd.hist r = G * BlockAccounting.histFn TensorProto.P16A8Z.PP16A8Z r) {zE : ℝ}
    (h12 : 1 - (4719 : ℝ) / 1562500 < zE) (hzE : zE ≤ 1) (m : Bool) (cl : Paint) {ι : Type u} (k : ι → ℕ)
    (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2 ^ k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2 ^ k i * envelope zE (k i)) := by
  let A : BU := ⟨α, ρ, σ, ⟨e, he, tr, tz, hind, wd, hw⟩⟩
  have hR : A.RanksOK := fun r hr => P16A8ZE.rk_bounds_of_proper hP hr
  have hT : A.TgtsOK := fun l => ⟨(htr l).1, by show tr l ≤ Fintype.card α; rw [hα]; exact (htr l).2⟩
  have hσ : 0 < Fintype.card σ := by
    have h1 := Finset.card_le_univ (Finset.univ.filter fun l : σ => tr l = 145)
    rw [hcnt 145, show BlockAccounting.histFn TensorProto.P16A8Z.TP16A8Z 145 = 224 from rfl] at h1
    omega
  exact p16a8z_engine_G A G hG (P16A8ZE.ranks_eq_of_histG A _ G hhist) (P16A8ZE.tgts_eq_of_cardG A _ G hcnt) hR hT hα
    hσ h12 hzE m cl k v

end

end TensorEng
