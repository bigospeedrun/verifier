import Submission.Work.Mixed.Bound
import Submission.Work.BlockAccounting.Moment
-- changed for the tensor-power extension (30103/10000000); see Submission.lean

/-!
# The K-target rule of a mixed unit, its rate fact in moment form, and the type map of its bridge

p3-port draft (21 Oct 2026).  `Work.Mixed.TwoTarget` instantiates the general rule of Theorem 1G
(`Work.Mixed.Flow`'s `Rule`, general in `K`) at `K = 2`.  The productive-helper unit of the p3 port has six target
ranks (helpers 6, 7, 8, 9; main fields 25, 57).  This file gives the rule for ANY list of targets:

* `Rule.ofList m tg P rk kmin rmax …`  the rule with targets `tg = [(kr_0, W_0), …]` (`K = tg.length`) and paid
  rounds `rk` in word order, separated (`rmax < kmin`);
* `Rule.ofList_rateQ`      `moment m z paid ≤ moment m z tg`, with `histFn paid` the histogram of `rk`, gives the rate
  hypothesis `RateQ z 1` (through `rateQ_of_normalized`, the moment shape of the generated rate files);
* `Rule.ofList_allotM_bound`  R2 for this rule: `allotM n0 n ≤ C 2^n (n+1)^z` above the rate exponent;
* `typeOf`, `typeOf_spec`, `card_typeOf`  the combinatorial core of the bridge (`Eng.BridgeHyp`'s `htq` and `hW`): a
  target-rank function `tq` on `range W` with values among the DISTINCT ranks of `tg`, rank `tg[k].1` taken exactly
  `tg[k].2` times, has the type map "index of `tq x` in `tg`";
* `rkList`, `card_rkList`  the paid rounds of a `(rank, count)` list in list order, with histogram `histFn`.

Mathlib only (plus the Mathlib-only modules it imports).  No `sorry`.
-/

namespace OAI.PowerSaving.MX
open Finset BlockAccounting

namespace Rule

/-- **The K-target rule**: targets `tg` (one `(rank, count)` entry per target type), paid rounds `rk` (word order),
every paid rank in `[1, rmax]`, every target rank in `[kmin, m]`, `rmax < kmin` (separation, hypothesis (S)). -/
def ofList (m : ℕ) (tg : List (ℕ × ℕ)) (P : ℕ) (rk : Fin P → ℕ) (kmin rmax : ℕ)
    (hrk1 : ∀ j, 1 ≤ rk j) (hrk : ∀ j, rk j ≤ rmax) (hsep : rmax < kmin)
    (htg : ∀ b ∈ tg, kmin ≤ b.1 ∧ b.1 ≤ m) (h2 : 2 ≤ kmin)
    (hatt : ∃ b ∈ tg, b.1 = kmin ∧ 1 ≤ b.2) : Rule where
  K := tg.length
  kr := fun k => tg[k.1].1
  Wk := fun k => tg[k.1].2
  m := m
  P := P
  rk := rk
  kmin := kmin
  rmax := rmax
  kmin_le := fun k => (htg _ (List.getElem_mem k.2)).1
  kr_le := fun k => (htg _ (List.getElem_mem k.2)).2
  rk_pos := hrk1
  rk_le := hrk
  sep := hsep
  two_le_kmin := h2
  kmin_att := by
    obtain ⟨b, hb, hb1, hb2⟩ := hatt
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    exact ⟨⟨i, hi⟩, hb1, hb2⟩

/-- The right side of the normalised rate fact of `ofList` is the moment of the target list. -/
lemma ofList_rhs (m : ℕ) (tg : List (ℕ × ℕ)) (z : ℝ) :
    ∑ k : Fin tg.length, ((tg[k.1].2 : ℕ) : ℝ) * (((tg[k.1].1 : ℕ) : ℝ) / m) ^ z = moment m z tg := by
  unfold moment
  exact Fin.sum_univ_fun_getElem tg (fun b => (b.2 : ℝ) * ((b.1 : ℝ) / (m : ℝ)) ^ z)

/-- **The rate fact of the K-target rule from its moment form.** -/
theorem ofList_rateQ {m : ℕ} {tg : List (ℕ × ℕ)} {P : ℕ} {rk : Fin P → ℕ} {kmin rmax : ℕ}
    (hrk1 : ∀ j, 1 ≤ rk j) (hrk : ∀ j, rk j ≤ rmax) (hsep : rmax < kmin)
    (htg : ∀ b ∈ tg, kmin ≤ b.1 ∧ b.1 ≤ m) (h2 : 2 ≤ kmin) (hatt : ∃ b ∈ tg, b.1 = kmin ∧ 1 ≤ b.2)
    {paid : List (ℕ × ℕ)} (hpaid : ∀ b ∈ paid, b.1 ≤ rmax)
    (hcnt : ∀ r, (Finset.univ.filter fun j => rk j = r).card = histFn paid r) {z : ℝ}
    (h : moment m z paid ≤ moment m z tg) :
    (ofList m tg P rk kmin rmax hrk1 hrk hsep htg h2 hatt).RateQ z 1 := by
  set R := ofList m tg P rk kmin rmax hrk1 hrk hsep htg h2 hatt with hR
  apply rateQ_of_normalized
  have hl : ∑ j, ((R.rk j : ℝ) / R.m) ^ z = moment m z paid := by
    rw [R.sum_rk_hist (fun r => ((r : ℝ) / R.m) ^ z)]
    have hc : ∀ r, ((Finset.univ.filter fun j => R.rk j = r).card : ℝ) = (histFn paid r : ℝ) := by
      intro r; exact_mod_cast hcnt r
    simp_rw [hc]
    exact sum_histFn paid (fun r => ((r : ℝ) / (m : ℝ)) ^ z) (Finset.range (rmax + 1))
      (fun b hb => Finset.mem_range.mpr (Nat.lt_succ_of_le (hpaid b hb)))
  have hr : ∑ k, (R.Wk k : ℝ) * ((R.kr k : ℝ) / R.m) ^ z = moment m z tg := ofList_rhs m tg z
  rw [hl, hr]
  exact h

/-- **R2 for the K-target rule**: the moment form of the rate fact at `z1 > 0` gives, for every `z ∈ (z1, 1]` and every
threshold `n0 ≥ m`, `allotM n0 n ≤ C 2^n (n+1)^z`. -/
theorem ofList_allotM_bound {m : ℕ} {tg : List (ℕ × ℕ)} {P : ℕ} {rk : Fin P → ℕ} {kmin rmax : ℕ}
    (hrk1 : ∀ j, 1 ≤ rk j) (hrk : ∀ j, rk j ≤ rmax) (hsep : rmax < kmin)
    (htg : ∀ b ∈ tg, kmin ≤ b.1 ∧ b.1 ≤ m) (h2 : 2 ≤ kmin) (hatt : ∃ b ∈ tg, b.1 = kmin ∧ 1 ≤ b.2)
    {paid : List (ℕ × ℕ)} (hpaid : ∀ b ∈ paid, b.1 ≤ rmax)
    (hcnt : ∀ r, (Finset.univ.filter fun j => rk j = r).card = histFn paid r) {z1 z : ℝ}
    (h : moment m z1 paid ≤ moment m z1 tg) (hz1 : 0 < z1) (h12 : z1 < z) (hz : z ≤ 1)
    {n0 : ℕ} (hn0 : m ≤ n0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ((ofList m tg P rk kmin rmax hrk1 hrk hsep htg h2 hatt).allotM n0 n : ℝ)
      ≤ C * 2 ^ n * ((n : ℝ) + 1) ^ z :=
  (ofList m tg P rk kmin rmax hrk1 hrk hsep htg h2 hatt).allotM_bound
    (ofList_rateQ hrk1 hrk hsep htg h2 hatt hpaid hcnt h) hz1 h12 hz hn0

end Rule

/-! ### `G` gauge copies of a unit -/

/-- `G` copies of a `(rank, count)` list (the word of a network is `G` gauge copies of one unit). -/
def scaleL (G : ℕ) (l : List (ℕ × ℕ)) : List (ℕ × ℕ) := l.map fun b => (b.1, G * b.2)

lemma histFn_scaleL (G : ℕ) (l : List (ℕ × ℕ)) (r : ℕ) : histFn (scaleL G l) r = G * histFn l r := by
  induction l with
  | nil => simp [scaleL, histFn_nil]
  | cons b l ih =>
    obtain ⟨r0, n0⟩ := b
    have e : scaleL G ((r0, n0) :: l) = (r0, G * n0) :: scaleL G l := rfl
    rw [e, histFn_cons, histFn_cons, ih]
    dsimp only
    split_ifs <;> ring

lemma moment_scaleL (m G : ℕ) (l : List (ℕ × ℕ)) (z : ℝ) :
    moment m z (scaleL G l) = (G : ℝ) * moment m z l := by
  induction l with
  | nil => simp [scaleL, moment]
  | cons b l ih =>
    obtain ⟨r0, n0⟩ := b
    have e : scaleL G ((r0, n0) :: l) = (r0, G * n0) :: scaleL G l := rfl
    rw [e, moment_cons, moment_cons, ih]
    unfold T
    push_cast
    ring

/-- The moment fact of one unit gives the moment fact of `G` copies. -/
lemma moment_scaleL_le {m G : ℕ} {paid tg : List (ℕ × ℕ)} {z : ℝ} (h : moment m z paid ≤ moment m z tg) :
    moment m z (scaleL G paid) ≤ moment m z (scaleL G tg) := by
  rw [moment_scaleL, moment_scaleL]
  exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg G)

lemma mem_scaleL {G : ℕ} {l : List (ℕ × ℕ)} {b : ℕ × ℕ} (hb : b ∈ scaleL G l) : ∃ c ∈ l, b = (c.1, G * c.2) := by
  unfold scaleL at hb
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
  exact ⟨c, hc, rfl⟩

/-! ### The type map of the bridge -/

section Types

/-- The type of a target rank: the index of the first entry of `tg` with that rank (`0` if there is none). -/
def typeOf (tg : List (ℕ × ℕ)) (hpos : 0 < tg.length) (tq : ℕ → ℕ) (x : ℕ) : Fin tg.length :=
  if h : tg.findIdx (fun b => b.1 = tq x) < tg.length then ⟨_, h⟩ else ⟨0, hpos⟩

lemma typeOf_eq (tg : List (ℕ × ℕ)) (hpos : 0 < tg.length) (tq : ℕ → ℕ) (x : ℕ)
    (hlt : tg.findIdx (fun b => b.1 = tq x) < tg.length) :
    typeOf tg hpos tq x = ⟨tg.findIdx (fun b => b.1 = tq x), hlt⟩ := by
  unfold typeOf
  simp [hlt]

lemma typeOf_spec (tg : List (ℕ × ℕ)) (hpos : 0 < tg.length) (tq : ℕ → ℕ) (x : ℕ)
    (hx : tq x ∈ tg.map Prod.fst) : tq x = (tg[(typeOf tg hpos tq x).1]'(typeOf tg hpos tq x).2).1 := by
  obtain ⟨b, hb, hbx⟩ := List.mem_map.mp hx
  have hlt : tg.findIdx (fun b => b.1 = tq x) < tg.length :=
    List.findIdx_lt_length_of_exists ⟨b, hb, by simp [hbx]⟩
  rw [typeOf_eq tg hpos tq x hlt]
  have h := List.findIdx_getElem (w := hlt)
  simp only [decide_eq_true_eq] at h
  exact h.symm

/-- With DISTINCT ranks, the type of the rank of entry `k` is `k`. -/
lemma typeOf_getElem (tg : List (ℕ × ℕ)) (hpos : 0 < tg.length) (hnd : (tg.map Prod.fst).Nodup)
    (tq : ℕ → ℕ) (x : ℕ) (k : Fin tg.length) (hk : tq x = (tg[k.1]'k.2).1) : typeOf tg hpos tq x = k := by
  have hx : tq x ∈ tg.map Prod.fst := List.mem_map.mpr ⟨tg[k.1], List.getElem_mem k.2, hk.symm⟩
  have h1 := typeOf_spec tg hpos tq x hx
  have hl : (tg.map Prod.fst).length = tg.length := List.length_map _
  have e1 : (tg.map Prod.fst)[(typeOf tg hpos tq x).1]'(by rw [hl]; exact (typeOf tg hpos tq x).2)
      = (tg.map Prod.fst)[k.1]'(by rw [hl]; exact k.2) := by
    simp only [List.getElem_map]
    rw [← h1]
    exact hk
  exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).mp e1)

/-- **The counts of the bridge**: if every value of `tq` on `range W` is a rank of `tg`, the ranks of `tg` are
distinct, and rank `tg[k].1` is taken exactly `tg[k].2` times, then type `k` is taken exactly `tg[k].2` times. -/
theorem card_typeOf (tg : List (ℕ × ℕ)) (hpos : 0 < tg.length) (hnd : (tg.map Prod.fst).Nodup)
    (tq : ℕ → ℕ) (W : ℕ) (hval : ∀ x, x < W → tq x ∈ tg.map Prod.fst)
    (hcnt : ∀ k : Fin tg.length, ((range W).filter (fun x => tq x = (tg[k.1]'k.2).1)).card = (tg[k.1]'k.2).2)
    (k : Fin tg.length) : ((range W).filter (fun x => typeOf tg hpos tq x = k)).card = (tg[k.1]'k.2).2 := by
  rw [← hcnt k]
  congr 1
  apply Finset.filter_congr
  intro x hx
  have hxW : x < W := Finset.mem_range.mp hx
  constructor
  · intro h
    subst h
    exact typeOf_spec tg hpos tq x (hval x hxW)
  · intro h
    exact typeOf_getElem tg hpos hnd tq x k h

end Types

/-! ### The paid rounds of a `(rank, count)` list -/

section RkList

/-- The paid rounds of a list `(rank, count)`, in list order. -/
def rkFlat (l : List (ℕ × ℕ)) : List ℕ := l.flatMap (fun b => List.replicate b.2 b.1)

lemma count_rkFlat (l : List (ℕ × ℕ)) (r : ℕ) : (rkFlat l).count r = histFn l r := by
  induction l with
  | nil => simp [rkFlat, histFn_nil]
  | cons b l ih =>
    rw [histFn_cons, ← ih]
    simp only [rkFlat, List.flatMap_cons, List.count_append, List.count_replicate]
    by_cases h : b.1 = r
    · subst h; simp [Nat.add_comm]
    · have h' : (b.1 == r) = false := by simp [h]
      simp [h, h']

lemma count_eq_sum_ite (l : List ℕ) (r : ℕ) : l.count r = (l.map fun a => if a = r then 1 else 0).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.count_cons, List.map_cons, List.sum_cons, ih]
    by_cases h : a = r
    · subst h; simp [Nat.add_comm]
    · have h' : (a == r) = false := by simp [h]
      simp [h, h']

/-- The `j`-th paid round. -/
def rkList (l : List (ℕ × ℕ)) (j : Fin (rkFlat l).length) : ℕ := (rkFlat l)[j.1]

theorem card_rkList (l : List (ℕ × ℕ)) (r : ℕ) :
    (Finset.univ.filter fun j => rkList l j = r).card = histFn l r := by
  rw [← count_rkFlat, count_eq_sum_ite, Finset.card_filter]
  unfold rkList
  exact Fin.sum_univ_fun_getElem (rkFlat l) (fun a => if a = r then 1 else 0)

lemma rkList_mem (l : List (ℕ × ℕ)) (j : Fin (rkFlat l).length) :
    ∃ b ∈ l, rkList l j = b.1 ∧ 1 ≤ b.2 := by
  have hm : rkList l j ∈ rkFlat l := List.getElem_mem j.2
  unfold rkFlat at hm
  obtain ⟨b, hb, hm'⟩ := List.mem_flatMap.mp hm
  refine ⟨b, hb, List.eq_of_mem_replicate hm', ?_⟩
  have := List.length_pos_of_mem hm'
  simp only [List.length_replicate] at this
  omega

end RkList

end OAI.PowerSaving.MX
