import Submission.Work.MixedCost.EngineFinal
import Submission.Work.MixedCost.BridgeTwo
import Submission.Work.Mixed.HeadM1
import Submission.Work.BlockApply.Exact

/-!
# p-bridge: from the heads-first network certificate to the mixed engine's inputs (round wht45/lever)

The hosted network certifies (p-hfirst's `XNet.heads_first`, from p-a3's `xnet_certificate`): there is a proper
word `body` with `GLiveKernel e (heads ++ body)` whose price is, for EVERY price list `φ`,
`G * listCost φ U - |heads| * φ (a + b)` (`G` gauge copies of the unit profile `U`, minus the heads).
The mixed engine (e-r3prog/e-r3cost `Eng.engine_seam_final`) needs an `Eng` (word with mixed targets and
separation), a rule `R` with `BridgeHyp`, and the rate fact `R.RateQ z1 1`.  This file is the adapter:

* `ind`, `costR_ind`, `hist_eq_price`   (c) the histogram is the price at the indicator price lists;
* `hist_headsFirst`, `sep_of_price`      the body's histogram from the heads-first price; (b) separation from
                                          indicator prices (no block above `rmax`);
* `count_blockRanks`, `card_rkI`, `rkI_mem`   (a) `P` and `rk` read off the word: `rk j` = rank of the `j`-th block
                                          letter in word order (e-r3cost's `Eng.nB`, `Eng.rkI`);
* `headS`, `headS_card`, `head_hz`       (e) head targets in the form `cut_heads_half` takes, for heads on lines of
                                          a frame;
* `HFNet`, `cutWord`, `cutEng`            the half-cut engine built from the network data;
* `cutWord_hist_eq`                       (d) the cut word's histogram is `G * histFn cut` (R5's `hcnt`, times `G`);
* `rate_scaled`                           R5's moment fact for one unit gives the rate fact for `G` copies;
* `cut_bundle`                            (f) the hypothesis bundle of `Eng.engine_seam_final`;
* `cut_engine`                            the engine theorem itself (the `hillsZ_program` shape) from the network.

No `sorry`, no new axiom, no `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.PB
open Binary Matrix Finset GF MX RAM

noncomputable section

universe U

/-! ## 1. Indicator price lists, histograms, separation -/

/-- The price list `1` at rank `r`, `0` elsewhere. -/
def ind (r : ℕ) : ℕ → ℝ := fun q => if q = r then 1 else 0

section Words
variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

/-- The indicator price list of rank `r` counts the blocks of rank `r`. -/
lemma costR_ind (w : GWord α ρ) (r : ℕ) : w.costR (ind r) = (w.hist r : ℝ) := by
  rw [GWord.costR_shadow]
  exact BWord.costR_ind w.shadow r

/-- **(c) The histogram identity**: if `w`'s price is `c φ` for every price list `φ`, the number of blocks of rank
`r` is the price at the indicator of `r`. -/
theorem hist_eq_price {c : (ℕ → ℝ) → ℝ} {w : GWord α ρ} (hcost : ∀ φ, w.costR φ = c φ) (r : ℕ) :
    (w.hist r : ℝ) = c (ind r) := by
  rw [← costR_ind, hcost]

/-- The histogram of a word priced as `G` copies of a profile `U` minus `K` blocks of rank `r0`. -/
theorem hist_headsFirst {w : GWord α ρ} {G K r0 : ℕ} {U : List (ℕ × ℕ)}
    (hcost : ∀ φ, w.costR φ = (G : ℝ) * listCost φ U - (K : ℝ) * φ r0) (r : ℕ) :
    w.hist r + (if r = r0 then K else 0) = G * BlockAccounting.histFn U r := by
  have h := hist_eq_price hcost r
  have hl : listCost (ind r) U = (BlockAccounting.histFn U r : ℝ) := listCost_ind U r
  have hi : ind r r0 = if r0 = r then 1 else 0 := rfl
  rw [hl, hi] at h
  by_cases hr : r = r0
  · rw [if_pos hr.symm, mul_one] at h
    rw [if_pos hr]
    have : ((w.hist r : ℕ) : ℝ) + (K : ℝ) = (G : ℝ) * (BlockAccounting.histFn U r : ℝ) := by linarith
    exact_mod_cast this
  · rw [if_neg (Ne.symm hr), mul_zero, sub_zero] at h
    rw [if_neg hr, add_zero]
    exact_mod_cast h

/-- Ranks of a proper letter lie in `[1, u)`. -/
lemma rk_bounds {u r : ℕ} {mv : GMove α ρ} (hp : mv.Proper u) (hr : mv.rk? = some r) : 1 ≤ r ∧ r < u := by
  cases mv with
  | old mv =>
    cases mv with
    | localM g => exact absurd hr (by simp [GMove.rk?, GMove.shadow, BMove.rk?])
    | shift l z => exact absurd hr (by simp [GMove.rk?, GMove.shadow, BMove.rk?])
    | block l rk z ind =>
      have hr' : rk = r := by simpa [GMove.rk?, GMove.shadow, BMove.rk?] using hr
      subst hr'
      exact hp
  | perm l G => exact absurd hr (by simp [GMove.rk?, GMove.shadow, BMove.rk?])
  | phase l z c => exact absurd hr (by simp [GMove.rk?, GMove.shadow, BMove.rk?])

/-- A block letter of rank `r` in `w` makes `hist w r ≥ 1`. -/
lemma hist_pos_of_mem {w : GWord α ρ} {mv : GMove α ρ} (hmv : mv ∈ w) {r : ℕ} (hr : mv.rk? = some r) :
    1 ≤ w.hist r := by
  have h : 0 < w.shadow.countP (fun mv => decide (mv.rk? = some r)) :=
    List.countP_pos_iff.mpr ⟨mv.shadow, List.mem_map.mpr ⟨mv, hmv, rfl⟩, decide_eq_true hr⟩
  exact h

/-- **(b) Separation from indicator price lists**: if the price vanishes at the indicator of every rank above
`rmax`, no block letter of `w` has rank above `rmax`. -/
theorem sep_of_price {c : (ℕ → ℝ) → ℝ} {w : GWord α ρ} (hcost : ∀ φ, w.costR φ = c φ) {rmax : ℕ}
    (hc : ∀ r, rmax < r → c (ind r) = 0) : ∀ mv ∈ w, ∀ r, mv.rk? = some r → r ≤ rmax := by
  intro mv hmv r hr
  by_contra hlt
  push_neg at hlt
  have h1 := hist_pos_of_mem hmv hr
  have h2 := hist_eq_price hcost r
  rw [hc r hlt] at h2
  have : w.hist r = 0 := by exact_mod_cast h2
  omega

/-! ## 2. The paid rounds read off the word (Rule fields `P`, `rk`) -/

lemma mem_blockRanks {w : GWord α ρ} {r : ℕ} : r ∈ Eng.blockRanks w ↔ ∃ mv ∈ w, mv.rk? = some r := by
  unfold Eng.blockRanks
  exact List.mem_filterMap

lemma blockRanks_append (w w' : GWord α ρ) :
    Eng.blockRanks (w ++ w') = Eng.blockRanks w ++ Eng.blockRanks w' := by
  unfold Eng.blockRanks
  exact List.filterMap_append

/-- The number of block letters of rank `r` is the histogram. -/
lemma count_blockRanks (w : GWord α ρ) (r : ℕ) : (Eng.blockRanks w).count r = w.hist r := by
  induction w with
  | nil => simp [Eng.blockRanks, GWord.hist, GWord.shadow, BWord.hist]
  | cons mv w ih =>
    have hh : GWord.hist (mv :: w) r = GWord.hist w r + if mv.rk? = some r then 1 else 0 := by
      show BWord.hist (mv.shadow :: GWord.shadow w) r = _
      rw [BWord.hist_cons]
      rfl
    rw [hh, ← ih]
    unfold Eng.blockRanks
    rw [List.filterMap_cons]
    cases h : mv.rk? with
    | none => simp
    | some q =>
      by_cases hq : q = r
      · subst hq; simp
      · simp [hq]

lemma count_eq_sum_range (l : List ℕ) (r : ℕ) :
    l.count r = ∑ i ∈ Finset.range l.length, if l.getD i 0 = r then 1 else 0 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.count_cons, ih]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    congr 1
    by_cases h : a = r <;> simp [h]

lemma card_filter_getD (l : List ℕ) (r : ℕ) :
    (Finset.univ.filter fun j : Fin l.length => l.getD j 0 = r).card = l.count r := by
  rw [Finset.card_filter, count_eq_sum_range]
  exact Fin.sum_univ_eq_sum_range (fun i => if l.getD i 0 = r then 1 else 0) l.length

/-- The price of a word is the sum of the price list over its paid ranks (in word order). -/
lemma costR_eq_blockRanks (w : GWord α ρ) (f : ℕ → ℝ) : w.costR f = ((Eng.blockRanks w).map f).sum := by
  induction w with
  | nil => simp [Eng.blockRanks, GWord.costR]
  | cons mv w ih =>
    rw [GWord.costR_cons, ih]
    unfold Eng.blockRanks
    rw [List.filterMap_cons]
    have hc : mv.costR f = match mv.rk? with | some r => f r | none => 0 := rfl
    rw [hc]
    cases mv.rk? with
    | none => simp
    | some q => simp

lemma sum_map_eq_sum_range (l : List ℕ) (f : ℕ → ℝ) :
    (l.map f).sum = ∑ i ∈ Finset.range l.length, f (l.getD i 0) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.map_cons, List.sum_cons, ih, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

end Words

section EngFacts
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]

/-- **(a) / (d)** The number of paid rounds of rank `r` (`rk j = rkI j`, the rank of the `j`-th block letter of the
engine word, in word order) is the histogram of the word. -/
theorem card_rkI (E : Eng α ρ σ) (r : ℕ) :
    (Finset.univ.filter fun j : Fin E.nB => E.rkI j = r).card = E.wd.hist r := by
  rw [← count_blockRanks]
  exact card_filter_getD (Eng.blockRanks E.wd) r

/-- Every paid round is the rank of a block letter of the word. -/
lemma rkI_mem (E : Eng α ρ σ) (j : Fin E.nB) : ∃ mv ∈ E.wd, mv.rk? = some (E.rkI j) := by
  have hj : (j : ℕ) < (Eng.blockRanks E.wd).length := j.2
  have : E.rkI j = (Eng.blockRanks E.wd)[(j : ℕ)] := by
    unfold Eng.rkI
    exact List.getD_eq_getElem _ _ hj
  rw [this]
  exact mem_blockRanks.mp (List.getElem_mem hj)

/-- **(d) in moment form**: the sum of a price list over the paid rounds is the price of the engine word
(with `f r = r ^ z`: `∑ j, rk_j ^ z = c (r ↦ r ^ z)`). -/
theorem sum_rkI_eq_costR (E : Eng α ρ σ) (f : ℕ → ℝ) : ∑ j : Fin E.nB, f (E.rkI j) = E.wd.costR f := by
  rw [costR_eq_blockRanks, sum_map_eq_sum_range]
  exact Fin.sum_univ_eq_sum_range (fun i => f ((Eng.blockRanks E.wd).getD i 0)) (Eng.blockRanks E.wd).length

lemma rkI_pos (E : Eng α ρ σ) (j : Fin E.nB) : 1 ≤ E.rkI j := by
  obtain ⟨mv, hmv, hr⟩ := rkI_mem E j
  exact (rk_bounds (E.hP mv hmv) hr).1

lemma rkI_le (E : Eng α ρ σ) {rmax : ℕ} (hwr : ∀ mv ∈ E.wd, ∀ r, mv.rk? = some r → r ≤ rmax)
    (j : Fin E.nB) : E.rkI j ≤ rmax := by
  obtain ⟨mv, hmv, hr⟩ := rkI_mem E j
  exact hwr mv hmv _ hr

lemma mx_eq (E : Eng α ρ σ) : E.mx = Fintype.card α := (Layout.card E.X).symm
lemma W_eq (E : Eng α ρ σ) : E.W = Fintype.card σ := (Layout.card E.Q).symm

lemma tq_of_lt (E : Eng α ρ σ) (i : Fin E.W) : E.tq i = E.tr (E.Q.atFin i) := by
  unfold Eng.tq
  rw [dif_pos i.2]

/-- Target ranks of a cut engine: `card α - a` on the head roles, `card α` elsewhere. -/
lemma tq_cases (E : Eng α ρ σ) (L : List σ) {a : ℕ} (A : σ → OBase α) (S : σ → Finset α)
    (htr : ∀ l, E.tr l = (cutTgt L A S l).1) (hS : ∀ l ∈ L, (S l).card = a) :
    ∀ x, x < E.W → E.tq x = E.mx ∨ E.tq x = E.mx - a := by
  intro x hx
  have h1 := tq_of_lt E ⟨x, hx⟩
  simp only at h1
  rw [h1, htr, cutTgt_rank, mx_eq]
  split_ifs with hl
  · right; rw [hS _ hl]
  · left; rfl

/-- The cut roles are exactly the head list. -/
lemma card_tq (E : Eng α ρ σ) (L : List σ) (hL : L.Nodup) {a : ℕ} (A : σ → OBase α) (S : σ → Finset α)
    (htr : ∀ l, E.tr l = (cutTgt L A S l).1) (hS : ∀ l ∈ L, (S l).card = a) (ha : 1 ≤ a)
    (haα : a < Fintype.card α) :
    ((Finset.range E.W).filter (fun x => E.tq x = E.mx - a)).card = L.length := by
  rw [Finset.card_filter, ← Fin.sum_univ_eq_sum_range (fun x => if E.tq x = E.mx - a then 1 else 0) E.W]
  have h1 : ∀ i : Fin E.W, (if E.tq i = E.mx - a then 1 else 0)
      = (fun l => if E.tr l = E.mx - a then 1 else 0) (E.Q.index.symm i) := by
    intro i
    rw [tq_of_lt]
    rfl
  rw [Finset.sum_congr rfl (fun i _ => h1 i)]
  rw [Equiv.sum_comp E.Q.index.symm (fun l => if E.tr l = E.mx - a then 1 else 0)]
  have h2 : ∀ l, (if E.tr l = E.mx - a then 1 else 0) = if l ∈ L then 1 else 0 := by
    intro l
    rw [htr, cutTgt_rank, mx_eq]
    by_cases hl : l ∈ L
    · rw [if_pos hl, hS l hl, if_pos rfl, if_pos hl]
    · rw [if_neg hl, if_neg hl, if_neg (by omega)]
  rw [Finset.sum_congr rfl (fun l _ => h2 l), Finset.sum_boole]
  have h3 : (Finset.univ.filter fun l : σ => l ∈ L) = L.toFinset := by
    ext l; simp
  rw [h3, List.toFinset_card_of_nodup hL]
  simp

end EngFacts

/-! ## 3. Head targets for `cut_heads_half` (heads on lines of a frame) -/

section Heads
variable {α σ : Type*} [Fintype α] [DecidableEq α]

/-- The `a` cut lines of a head on the lines `d` of the frame `A` (`|d| = a + b`): its first `a` lines in `A.fam`
order (exactly the `S` of e-r45m1's `bph_partA_fam`). -/
def headS (A : OBase α) (d : Finset α) {a b : ℕ} (h : d.card = a + b) : Finset α :=
  Finset.univ.map ⟨fun i : Fin a => (d.equivFin.symm (Fin.cast h.symm (Fin.castAdd b i))).1,
    fun i j hij => Fin.castAdd_injective a b (Fin.cast_injective _
      (d.equivFin.symm.injective (Subtype.ext hij)))⟩

lemma headS_card (A : OBase α) (d : Finset α) {a b : ℕ} (h : d.card = a + b) : (headS A d h).card = a := by
  simp [headS]

/-- **(e) Head targets**: heads whose directions are the lines `d l` of frames `A l` (in `A.fam` order) satisfy the
hypothesis `hz` of `cut_heads_half` with `S l = headS (A l) (d l)`, `|S l| = a`. -/
theorem head_hz {L : List σ} {a b : ℕ} (z : σ → Fin (a + b) → Space α) (A : σ → OBase α) (d : σ → Finset α)
    (hd : ∀ l, (d l).card = a + b)
    (hzd : ∀ l ∈ L, ∀ i, z l i = (A l).fam (d l) (Fin.cast (hd l).symm i)) :
    ∀ l ∈ L, ∀ x, bph (partA z l) x = bph ((A l).fam (headS (A l) (d l) (hd l))) x := by
  intro l hl x
  have : partA z l = fun i : Fin a => (A l).fam (d l) (Fin.cast (hd l).symm (Fin.castAdd b i)) := by
    funext i
    exact hzd l hl _
  rw [this]
  exact bph_partA_fam (A l) (d l) (hd l) x

/-- The cut lines on the head roles only (`∅` elsewhere): for heads whose line sets are given on `L` only. -/
def headSL [DecidableEq σ] (L : List σ) (A : σ → OBase α) (d : σ → Finset α) {a b : ℕ}
    (hd : ∀ l ∈ L, (d l).card = a + b) (l : σ) : Finset α :=
  if h : l ∈ L then headS (A l) (d l) (hd l h) else ∅

lemma headSL_card [DecidableEq σ] (L : List σ) (A : σ → OBase α) (d : σ → Finset α) {a b : ℕ}
    (hd : ∀ l ∈ L, (d l).card = a + b) : ∀ l ∈ L, (headSL L A d hd l).card = a := by
  intro l hl
  unfold headSL
  rw [dif_pos hl]
  exact headS_card _ _ _

/-- **(e) Head targets, lines given on the head roles only.** -/
theorem head_hzL [DecidableEq σ] {L : List σ} {a b : ℕ} (z : σ → Fin (a + b) → Space α) (A : σ → OBase α)
    (d : σ → Finset α) (hd : ∀ l ∈ L, (d l).card = a + b)
    (hzd : ∀ l (hl : l ∈ L), ∀ i, z l i = (A l).fam (d l) (Fin.cast (hd l hl).symm i)) :
    ∀ l ∈ L, ∀ x, bph (partA z l) x = bph ((A l).fam (headSL L A d hd l)) x := by
  intro l hl x
  have hS : headSL L A d hd l = headS (A l) (d l) (hd l hl) := by unfold headSL; rw [dif_pos hl]
  have : partA z l = fun i : Fin a => (A l).fam (d l) (Fin.cast (hd l hl).symm (Fin.castAdd b i)) := by
    funext i
    exact hzd l hl _
  rw [this, hS]
  exact bph_partA_fam (A l) (d l) (hd l hl) x

end Heads

/-! ## 4. The network side, the half-cut word and its engine -/

section Cut
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]

omit [Fintype σ] [DecidableEq σ] in
lemma blockRanks_headWord (e : σ → ρ) (L : List σ) (c : ℕ) (z : σ → Fin c → Space α)
    (ind : ∀ l, LinearIndependent F (z l)) :
    Eng.blockRanks (headWord e L (fun _ => c) z ind) = List.replicate L.length c := by
  unfold Eng.blockRanks headWord
  induction L with
  | nil => rfl
  | cons l L ih => rw [List.map_cons, List.filterMap_cons, List.length_cons, List.replicate_succ, ← ih]; rfl

omit [Fintype σ] [DecidableEq σ] in
lemma blockRanks_shiftWord (e : σ → ρ) (L : List σ) (c : σ → Space α) :
    Eng.blockRanks (shiftWord e L c : GWord α ρ) = [] := by
  unfold Eng.blockRanks shiftWord
  induction L with
  | nil => rfl
  | cons l L ih => rw [List.map_cons, List.filterMap_cons]; exact ih

/-- **The heads-first network certificate** (what p-hfirst's `XNet.heads_first` gives, plus the head geometry and
the unit profile): heads of rank `a + b` on the roles `L`, the first `a` directions of each head the lines `S l` of
a frame `A l`, and a proper body priced, for every price list, as `G` copies of the profile `U` minus the heads. -/
structure HFNet (α ρ σ : Type*) [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
    [Fintype σ] [DecidableEq σ] where
  e : σ → ρ
  he : Function.Injective e
  L : List σ
  hL : L.Nodup
  a : ℕ
  b : ℕ
  z : σ → Fin (a + b) → Space α
  ind : ∀ l, LinearIndependent F (z l)
  A : σ → OBase α
  S : σ → Finset α
  hz : ∀ l ∈ L, ∀ x, bph (partA z l) x = bph ((A l).fam (S l)) x
  hS : ∀ l ∈ L, (S l).card = a
  body : GWord α ρ
  hP : body.Proper (Fintype.card α)
  hk : GLiveKernel e (headWord e L (fun _ => a + b) z ind ++ body)
  G : ℕ
  U : List (ℕ × ℕ)
  hcost : ∀ φ, body.costR φ = (G : ℝ) * listCost φ U - (L.length : ℝ) * φ (a + b)

namespace HFNet
variable (N : HFNet α ρ σ)

/-- The half-cut word: rank-`b` remnants of the heads, the body, one free shift per head role. -/
def cutWord : GWord α ρ :=
  (headWord N.e N.L (fun _ => N.b) (partB N.z) (partB_indep N.ind) ++ N.body) ++ shiftWord N.e N.L (cutShift N.A N.S)

/-- **(a)** The paid rounds of the cut word in word order: `|L|` remnants of rank `b`, then the body's blocks. -/
theorem cutWord_blockRanks : Eng.blockRanks N.cutWord = List.replicate N.L.length N.b ++ Eng.blockRanks N.body := by
  unfold cutWord
  rw [blockRanks_append, blockRanks_append, blockRanks_headWord, blockRanks_shiftWord, List.append_nil]

lemma cutWord_hist (r : ℕ) : N.cutWord.hist r = (if r = N.b then N.L.length else 0) + N.body.hist r :=
  hist_cut_half N.e N.L N.z N.ind (cutShift N.A N.S) N.body r

/-- The price of the cut word: the remnants plus the network's price of the body. -/
theorem cutWord_costR (f : ℕ → ℝ) :
    N.cutWord.costR f = (N.L.length : ℝ) * f N.b + ((N.G : ℝ) * listCost f N.U - (N.L.length : ℝ) * f (N.a + N.b)) := by
  rw [costR_eq_blockRanks, cutWord_blockRanks, List.map_append, List.sum_append, List.map_replicate,
    List.sum_replicate, ← costR_eq_blockRanks, N.hcost f, nsmul_eq_mul]

/-- **(d) The cut word's histogram is `G` copies of the cut profile**, given the profile identity `hcut`
(cut profile = unit profile with `Hd` heads of rank `a + b` replaced by `Hd` remnants of rank `b`). -/
theorem cutWord_hist_eq {Hd : ℕ} {cut : List (ℕ × ℕ)}
    (hcut : ∀ r, (if r = N.b then Hd else 0) + BlockAccounting.histFn N.U r
      = BlockAccounting.histFn cut r + (if r = N.a + N.b then Hd else 0))
    (hLlen : N.L.length = N.G * Hd) (r : ℕ) :
    N.cutWord.hist r = N.G * BlockAccounting.histFn cut r := by
  have h1 := hist_headsFirst N.hcost r
  have h2 : (if r = N.b then N.G * Hd else 0) + N.G * BlockAccounting.histFn N.U r
      = N.G * BlockAccounting.histFn cut r + (if r = N.a + N.b then N.G * Hd else 0) := by
    have := congrArg (fun t => N.G * t) (hcut r)
    simp only [Nat.mul_add, mul_ite, mul_zero] at this
    exact this
  rw [cutWord_hist, hLlen]
  rw [hLlen] at h1
  generalize N.G * Hd = K at *
  generalize N.G * BlockAccounting.histFn N.U r = X at *
  generalize N.G * BlockAccounting.histFn cut r = Y at *
  generalize N.body.hist r = B at *
  split_ifs at * <;> omega

/-- **(b) Separation of the cut word**: every paid rank is a rank of the cut profile, hence at most `rmax`. -/
theorem cutWord_ranks_le {cut : List (ℕ × ℕ)} {rmax : ℕ}
    (hhist : ∀ r, N.cutWord.hist r = N.G * BlockAccounting.histFn cut r) (hcutr : ∀ q ∈ cut, q.1 ≤ rmax) :
    ∀ mv ∈ N.cutWord, ∀ r, mv.rk? = some r → r ≤ rmax := by
  intro mv hmv r hr
  have h1 := hist_pos_of_mem hmv hr
  rw [hhist] at h1
  have h2 : BlockAccounting.histFn cut r ≠ 0 := by
    intro h0
    rw [h0, Nat.mul_zero] at h1
    omega
  have h3 := BlockAccounting.mem_keys_of_histFn_ne_zero cut r h2
  unfold BlockAccounting.keys at h3
  rw [List.mem_toFinset, List.mem_map] at h3
  obtain ⟨q, hq, rfl⟩ := h3
  exact hcutr q hq

/-- **The half-cut engine** of the network: word `cutWord`, targets `cutTgt` (rank `card α - a` on head roles,
`card α` elsewhere; the head lemma `cut_heads_half` is the certificate). -/
def cutEng (rmax : ℕ) (hwr : ∀ mv ∈ N.cutWord, ∀ r, mv.rk? = some r → r ≤ rmax)
    (hsep : rmax < Fintype.card α - N.a) (hb : 1 ≤ N.b) (hab : N.a + N.b < Fintype.card α)
    (h3 : 3 ≤ Fintype.card α) (hσ : 0 < Fintype.card σ) : Eng α ρ σ where
  X := Layout.someLayout α
  R := Layout.someLayout ρ
  Q := Layout.someLayout σ
  e := N.e
  he := N.he
  tr := fun l => (cutTgt N.L N.A N.S l).1
  tz := fun l => (cutTgt N.L N.A N.S l).2
  tind := cutTgt_indep N.L N.A N.S
  tr_le := fun l => by
    show (cutTgt N.L N.A N.S l).1 ≤ (Layout.someLayout α).n
    rw [← Layout.card (Layout.someLayout α), cutTgt_rank]
    split_ifs <;> omega
  tr_pos := fun l => by
    show 1 ≤ (cutTgt N.L N.A N.S l).1
    rw [cutTgt_rank]
    split_ifs with hl
    · rw [N.hS l hl]; omega
    · omega
  wd := N.cutWord
  hP := by
    rw [← Layout.card (Layout.someLayout α)]
    exact proper_cut_half _ N.e N.L N.z N.ind _ N.body hb (by omega) N.hP
  sep := fun mv hmv r hr l => by
    have h1 := hwr mv hmv r hr
    show r < (cutTgt N.L N.A N.S l).1
    rw [cutTgt_rank]
    split_ifs with hl
    · rw [N.hS l hl]; omega
    · omega
  W_pos := by rw [← Layout.card (Layout.someLayout σ)]; exact hσ
  three := by rw [← Layout.card (Layout.someLayout α)]; exact h3
  hw := cut_heads_half N.he N.L N.hL N.z N.ind N.A N.S N.hz N.body N.hk

end HFNet

/-! ## 5. The rate fact for `G` copies from R5's moment fact for one unit -/

/-- R5's moment fact for one unit (`moment m z cut ≤ (W0 - Hd) + T m z kc Hd`) gives, for `G` copies
(`W = G W0` arrays, `H = G Hd` cut arrays, every count `G` times), the hypothesis `h` of e-r12's
`Rule.twoTarget_rateQ_hist`. -/
theorem rate_scaled {P : ℕ} (rk : Fin P → ℕ) {m kc rmax G W0 Hd W H : ℕ} {z : ℝ} (cut : List (ℕ × ℕ))
    (hcutr : ∀ q ∈ cut, q.1 ≤ rmax)
    (hmom : BlockAccounting.moment m z cut ≤ ((W0 - Hd : ℕ) : ℝ) + BlockAccounting.T m z kc Hd)
    (hcnt : ∀ r, (Finset.univ.filter fun j => rk j = r).card = G * BlockAccounting.histFn cut r)
    (hW : W = G * W0) (hH : H = G * Hd) :
    ∑ r ∈ Finset.range (rmax + 1), ((Finset.univ.filter fun j => rk j = r).card : ℝ) * ((r : ℝ) / m) ^ z
      ≤ ((W - H : ℕ) : ℝ) + (H : ℝ) * ((kc : ℝ) / m) ^ z := by
  simp_rw [hcnt]
  have e1 : ∑ r ∈ Finset.range (rmax + 1), (((G * BlockAccounting.histFn cut r : ℕ) : ℝ)) * ((r : ℝ) / m) ^ z
      = (G : ℝ) * BlockAccounting.moment m z cut := by
    have := BlockAccounting.sum_histFn cut (fun r => ((r : ℝ) / m) ^ z) (Finset.range (rmax + 1))
      (fun q hq => Finset.mem_range.mpr (by have := hcutr q hq; omega))
    unfold BlockAccounting.moment
    rw [← this, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    push_cast
    ring
  rw [e1]
  have e2 : ((W - H : ℕ) : ℝ) = (G : ℝ) * ((W0 - Hd : ℕ) : ℝ) := by
    rw [hW, hH, ← Nat.mul_sub]
    push_cast
    ring
  have e3 : (H : ℝ) * ((kc : ℝ) / m) ^ z = (G : ℝ) * BlockAccounting.T m z kc Hd := by
    unfold BlockAccounting.T
    rw [hH]
    push_cast
    ring
  rw [e2, e3, ← mul_add]
  exact mul_le_mul_of_nonneg_left hmom (Nat.cast_nonneg G)

/-! ## 6. (f) The hypothesis bundle of the mixed engine, and the engine theorem -/

/-- The two-target rule and `BridgeHyp` for ANY engine whose targets are `cutTgt` (rank `card α - a` on the roles of
`L`, `card α` elsewhere) and whose paid ranks are at most `rmax < card α - a`. -/
theorem bridge_of_eng (E : Eng α ρ σ) (L : List σ) (hL : L.Nodup) {a : ℕ} (A : σ → OBase α)
    (S : σ → Finset α) (htr : ∀ l, E.tr l = (cutTgt L A S l).1) (hS : ∀ l ∈ L, (S l).card = a)
    (ha : 1 ≤ a) (haα : a < Fintype.card α) {rmax : ℕ} (hsep : rmax < Fintype.card α - a)
    (h2 : 2 ≤ Fintype.card α - a) (hwr : ∀ mv ∈ E.wd, ∀ r, mv.rk? = some r → r ≤ rmax)
    (hH : 1 ≤ L.length) :
    ∃ (R : MX.Rule) (typ : ℕ → Fin R.K), E.BridgeHyp R typ (Fintype.card α - a) ∧
      R.K = 2 ∧ R.m = Fintype.card α ∧ R.kmin = Fintype.card α - a ∧ R.rmax = rmax ∧ R.P = E.nB := by
  have hmx := mx_eq E
  have hrk1 : ∀ j : Fin E.nB, 1 ≤ E.rkI j := rkI_pos E
  have hrk : ∀ j : Fin E.nB, E.rkI j ≤ rmax := rkI_le E hwr
  have hsep' : rmax < E.mx - a := by rw [hmx]; exact hsep
  have hkc : E.mx - a ≤ E.mx := Nat.sub_le _ _
  have h2' : 2 ≤ E.mx - a := by rw [hmx]; exact h2
  have hB := E.bridge_twoTarget (E.mx - a) rmax L.length hrk1 hrk hsep' hkc h2' hH
    (tq_cases E L A S htr hS) (by rw [hmx]; omega) (card_tq E L hL A S htr hS ha haα)
  exact ⟨_, _, { hB with hkmin := by rw [hB.hkmin, hmx] }, rfl, hmx, by
    show E.mx - a = _; rw [hmx], rfl, rfl⟩

/-- The rule, `BridgeHyp` and the rate fact for ANY engine whose targets are `cutTgt` and whose word has the
histogram `G * histFn cut` (separated: ranks `≤ rmax < card α - a`). -/
theorem bundle_of_eng (E : Eng α ρ σ) (L : List σ) (hL : L.Nodup) {a : ℕ} (A : σ → OBase α)
    (S : σ → Finset α) (htr : ∀ l, E.tr l = (cutTgt L A S l).1) (hS : ∀ l ∈ L, (S l).card = a)
    (ha : 1 ≤ a) (haα : a < Fintype.card α) {rmax : ℕ} (hsep : rmax < Fintype.card α - a)
    (h2 : 2 ≤ Fintype.card α - a) (hwr : ∀ mv ∈ E.wd, ∀ r, mv.rk? = some r → r ≤ rmax)
    (hH : 1 ≤ L.length) {G W0 Hd : ℕ} (cut : List (ℕ × ℕ)) (hcutr : ∀ q ∈ cut, q.1 ≤ rmax)
    (hhist : ∀ r, E.wd.hist r = G * BlockAccounting.histFn cut r)
    (hLlen : L.length = G * Hd) (hσ : Fintype.card σ = G * W0) {z1 : ℝ}
    (hmom : BlockAccounting.moment (Fintype.card α) z1 cut
      ≤ ((W0 - Hd : ℕ) : ℝ) + BlockAccounting.T (Fintype.card α) z1 (Fintype.card α - a) Hd) :
    ∃ (R : MX.Rule) (typ : ℕ → Fin R.K), E.BridgeHyp R typ (Fintype.card α - a) ∧ R.RateQ z1 1 := by
  have hmx := mx_eq E
  have hrk1 : ∀ j : Fin E.nB, 1 ≤ E.rkI j := rkI_pos E
  have hrk : ∀ j : Fin E.nB, E.rkI j ≤ rmax := rkI_le E hwr
  have hsep' : rmax < E.mx - a := by rw [hmx]; exact hsep
  have hkc : E.mx - a ≤ E.mx := Nat.sub_le _ _
  have h2' : 2 ≤ E.mx - a := by rw [hmx]; exact h2
  have hB := E.bridge_twoTarget (E.mx - a) rmax L.length hrk1 hrk hsep' hkc h2' hH
    (tq_cases E L A S htr hS) (by rw [hmx]; omega) (card_tq E L hL A S htr hS ha haα)
  refine ⟨_, _, { hB with hkmin := by rw [hB.hkmin, hmx] }, ?_⟩
  refine MX.Rule.twoTarget_rateQ_hist hrk1 hrk hsep' hkc h2' hH ?_
  have hcnt : ∀ r, (Finset.univ.filter fun j : Fin E.nB => (fun j : Fin E.nB => E.rkI j) j = r).card
      = G * BlockAccounting.histFn cut r := fun r => (card_rkI E r).trans (hhist r)
  have := rate_scaled (fun j : Fin E.nB => E.rkI j) (m := E.mx) (kc := E.mx - a) (rmax := rmax)
    (W := E.W) (H := L.length) cut hcutr (by rw [hmx]; exact hmom) hcnt (by rw [W_eq]; exact hσ) hLlen
  exact this

namespace HFNet
variable (N : HFNet α ρ σ)

/-- **(a), (b), (d) without the rate fact**: the engine of the network, a two-target rule with `BridgeHyp`
(`P` and `rk` read off the cut word), and the paid-round counts in R5's `hcnt` form, `G` times the cut profile. -/
theorem cut_bridge {Hd : ℕ} (cut : List (ℕ × ℕ))
    (hcut : ∀ r, (if r = N.b then Hd else 0) + BlockAccounting.histFn N.U r
      = BlockAccounting.histFn cut r + (if r = N.a + N.b then Hd else 0))
    (hLlen : N.L.length = N.G * Hd) (hG : 1 ≤ N.G) (hHd : 1 ≤ Hd) (hσ0 : 0 < Fintype.card σ)
    (rmax : ℕ) (hcutr : ∀ q ∈ cut, q.1 ≤ rmax) (hsep : rmax < Fintype.card α - N.a)
    (ha : 1 ≤ N.a) (hb : 1 ≤ N.b) (hab : N.a + N.b < Fintype.card α) (h2 : 2 ≤ Fintype.card α - N.a) :
    ∃ (E : Eng α ρ σ) (R : MX.Rule) (typ : ℕ → Fin R.K),
      E.wd = N.cutWord ∧ E.e = N.e ∧ (∀ l, E.tr l = (cutTgt N.L N.A N.S l).1) ∧ E.mx = Fintype.card α ∧
      E.BridgeHyp R typ (Fintype.card α - N.a) ∧ R.kmin = Fintype.card α - N.a ∧ R.rmax = rmax ∧
      (∀ r, (Finset.univ.filter fun j : Fin E.nB => E.rkI j = r).card = N.G * BlockAccounting.histFn cut r) := by
  have hhist := N.cutWord_hist_eq hcut hLlen
  have hwr := N.cutWord_ranks_le hhist hcutr
  have hH : 1 ≤ N.L.length := by
    rw [hLlen]; exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  let E := N.cutEng rmax hwr hsep hb hab (by omega) hσ0
  obtain ⟨R, typ, hB, -, -, hk, hr, -⟩ :=
    bridge_of_eng E N.L N.hL N.A N.S (fun l => rfl) N.hS ha (by omega) hsep h2 hwr hH
  exact ⟨E, R, typ, rfl, rfl, fun l => rfl, mx_eq E, hB, hk, hr, fun r => (card_rkI E r).trans (hhist r)⟩

/-- **(f) THE BUNDLE**: from the heads-first network certificate, the profile identity and R5's moment fact for one
unit, the hypothesis bundle of `Eng.engine_seam_final` (an engine, a rule with `BridgeHyp` at `kmin = card α - a`,
the rate fact `RateQ z1 1`). -/
theorem cut_bundle {W0 Hd : ℕ} (cut : List (ℕ × ℕ))
    (hcut : ∀ r, (if r = N.b then Hd else 0) + BlockAccounting.histFn N.U r
      = BlockAccounting.histFn cut r + (if r = N.a + N.b then Hd else 0))
    (hLlen : N.L.length = N.G * Hd) (hσ : Fintype.card σ = N.G * W0) (hG : 1 ≤ N.G) (hHd : 1 ≤ Hd)
    (hHW : Hd ≤ W0) (rmax : ℕ) (hcutr : ∀ q ∈ cut, q.1 ≤ rmax) (hsep : rmax < Fintype.card α - N.a)
    (ha : 1 ≤ N.a) (hb : 1 ≤ N.b) (hab : N.a + N.b < Fintype.card α) (h2 : 2 ≤ Fintype.card α - N.a) {z1 : ℝ}
    (hmom : BlockAccounting.moment (Fintype.card α) z1 cut
      ≤ ((W0 - Hd : ℕ) : ℝ) + BlockAccounting.T (Fintype.card α) z1 (Fintype.card α - N.a) Hd) :
    ∃ (E : Eng α ρ σ) (R : MX.Rule) (typ : ℕ → Fin R.K),
      E.wd = N.cutWord ∧ E.e = N.e ∧ (∀ l, E.tr l = (cutTgt N.L N.A N.S l).1) ∧ E.mx = Fintype.card α ∧
      E.BridgeHyp R typ (Fintype.card α - N.a) ∧ R.RateQ z1 1 := by
  have hhist := N.cutWord_hist_eq hcut hLlen
  have hwr := N.cutWord_ranks_le hhist hcutr
  have hH : 1 ≤ N.L.length := by rw [hLlen]; exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hσ0 : 0 < Fintype.card σ := by
    rw [hσ]; exact Nat.mul_pos (by omega) (by omega)
  let E := N.cutEng rmax hwr hsep hb hab (by omega) hσ0
  obtain ⟨R, typ, hB, hR⟩ := bundle_of_eng E N.L N.hL N.A N.S (fun l => rfl) N.hS ha (by omega) hsep h2 hwr hH
    cut hcutr hhist hLlen hσ hmom
  exact ⟨E, R, typ, rfl, rfl, fun l => rfl, mx_eq E, hB, hR⟩

/-- **THE ENGINE THEOREM FROM THE NETWORK** (the `hillsZ_program` shape at every `zE ∈ (z1, 1]`): the bundle fed to
`Eng.engine_seam_final`. -/
theorem cut_engine {W0 Hd : ℕ} (cut : List (ℕ × ℕ))
    (hcut : ∀ r, (if r = N.b then Hd else 0) + BlockAccounting.histFn N.U r
      = BlockAccounting.histFn cut r + (if r = N.a + N.b then Hd else 0))
    (hLlen : N.L.length = N.G * Hd) (hσ : Fintype.card σ = N.G * W0) (hG : 1 ≤ N.G) (hHd : 1 ≤ Hd)
    (hHW : Hd ≤ W0) (rmax : ℕ) (hcutr : ∀ q ∈ cut, q.1 ≤ rmax) (hsep : rmax < Fintype.card α - N.a)
    (ha : 1 ≤ N.a) (hb : 1 ≤ N.b) (hab : N.a + N.b < Fintype.card α) (h2 : 2 ≤ Fintype.card α - N.a)
    {z1 zE : ℝ}
    (hmom : BlockAccounting.moment (Fintype.card α) z1 cut
      ≤ ((W0 - Hd : ℕ) : ℝ) + BlockAccounting.T (Fintype.card α) z1 (Fintype.card α - N.a) Hd)
    (hz1 : 0 < z1) (h12 : z1 < zE) (hzE : zE ≤ 1)
    (m : Bool) (cl : Paint) {ι : Type U} (k : ι → ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2 ^ k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2 ^ k i * envelope zE (k i)) := by
  obtain ⟨E, R, typ, -, -, -, -, hB, hR⟩ :=
    N.cut_bundle cut hcut hLlen hσ hG hHd hHW rmax hcutr hsep ha hb hab h2 hmom
  exact E.engine_seam_final hB E.mx le_rfl hR hz1 h12 hzE m cl k v

end HFNet

end Cut

/-! ## 7. Profile identities by a finite check -/

/-- The profile identity `hcut` for all ranks from a check on a finite key list `K` containing every rank of both
profiles and the two special ranks (`decide` discharges `hchk` for concrete lists). -/
theorem hcut_of_check (U cut : List (ℕ × ℕ)) (b ab Hd : ℕ) (K : List ℕ)
    (hU : ∀ q ∈ U, q.1 ∈ K) (hc : ∀ q ∈ cut, q.1 ∈ K) (hb : b ∈ K) (hab : ab ∈ K)
    (hchk : ∀ r ∈ K, (if r = b then Hd else 0) + BlockAccounting.histFn U r
      = BlockAccounting.histFn cut r + (if r = ab then Hd else 0)) :
    ∀ r, (if r = b then Hd else 0) + BlockAccounting.histFn U r
      = BlockAccounting.histFn cut r + (if r = ab then Hd else 0) := by
  intro r
  by_cases hr : r ∈ K
  · exact hchk r hr
  · have h0 : ∀ l : List (ℕ × ℕ), (∀ q ∈ l, q.1 ∈ K) → BlockAccounting.histFn l r = 0 := by
      intro l hl
      by_contra hne
      have := BlockAccounting.mem_keys_of_histFn_ne_zero l r hne
      unfold BlockAccounting.keys at this
      rw [List.mem_toFinset, List.mem_map] at this
      obtain ⟨q, hq, rfl⟩ := this
      exact hr (hl q hq)
    rw [h0 U hU, h0 cut hc, if_neg (fun h : r = b => hr (h ▸ hb)), if_neg (fun h : r = ab => hr (h ▸ hab))]

end
end PowerSaving.PB
end OAI

#print axioms OAI.PowerSaving.PB.hist_eq_price
#print axioms OAI.PowerSaving.PB.hist_headsFirst
#print axioms OAI.PowerSaving.PB.sep_of_price
#print axioms OAI.PowerSaving.PB.card_rkI
#print axioms OAI.PowerSaving.PB.sum_rkI_eq_costR
#print axioms OAI.PowerSaving.PB.HFNet.cutWord_costR
#print axioms OAI.PowerSaving.PB.card_tq
#print axioms OAI.PowerSaving.PB.head_hz
#print axioms OAI.PowerSaving.PB.head_hzL
#print axioms OAI.PowerSaving.PB.HFNet.cutWord_blockRanks
#print axioms OAI.PowerSaving.PB.HFNet.cutWord_hist_eq
#print axioms OAI.PowerSaving.PB.HFNet.cutWord_ranks_le
#print axioms OAI.PowerSaving.PB.rate_scaled
#print axioms OAI.PowerSaving.PB.bundle_of_eng
#print axioms OAI.PowerSaving.PB.bridge_of_eng
#print axioms OAI.PowerSaving.PB.HFNet.cut_bridge
#print axioms OAI.PowerSaving.PB.HFNet.cut_bundle
#print axioms OAI.PowerSaving.PB.HFNet.cut_engine
#print axioms OAI.PowerSaving.PB.hcut_of_check
