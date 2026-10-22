import Submission.Work.MixedCost.TopCountM
import Submission.Work.Mixed.Prog.Loops
import Submission.Work.MixedCost.Close

/-!
# Mixed engine, top body part 3b: the consumption count as a RAM program

(agent e-r3cost, round wht45/lever, 19 Oct 2026.)

* `can_srcU`   the indicator of `srcU n h μ r u` on a code `u < W^(h+1)` (two region tests);
* `can_ownCnt` the number of source slots of a child, by one counting loop over `W^(h+1)` codes;
* `can_cons`   `cons n h μ` by ONE recursion over the class tree (`recurse_list`), polynomial work.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset GF MXR
noncomputable section

universe U

namespace Eng
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]
variable (E : Eng α ρ σ)
variable {ι : Type U} {m : Bool} {B : ι → ℕ} {s : Ty} {x : ι → T s}

lemma colS_le (h sv : ℕ) : colS E.W E.tq h sv ≤ E.mx^h := (E.stepC_iter_le h sv).1

/-- The test `mx * (μ * colS h u) ≤ n` as `1` / `0`. -/
lemma can_fits {n h μ u : ι → ℕ} (hn : Knows m B s x n) (hh : Knows m B s x h) (hμ : Knows m B s x μ)
    (hu : Knows m B s x u) (hns : Small B n) (hhs : Small B h) (hμs : Small B μ) (hus : Small B u)
    (hpow : Small B (fun i => E.mx^(h i))) :
    Can m B s w x (fun i => if E.mx * (μ i * colS E.W E.tq (h i) (u i)) ≤ n i then 1 else 0)
      (fun i => h i + 1) := by
  have hcol := E.can_colS hh hhs hu hus hpow
  have hcs : Small B (fun i => colS E.W E.tq (h i) (u i)) := hpow.mono (fun i => E.colS_le _ _)
  have hv : Can m B s w x (fun i => E.mx * (μ i * colS E.W E.tq (h i) (u i))) (fun i => h i + 1) :=
    (Can.wc E.mx).times ((hμ.mono (fun _ => Nat.zero_le _)).times hcol hμs hcs)
      (Small.const _ E.mx) (hμs.mul hcs)
  refine ((Can.wc 1).wsub ((hn.mono (fun _ => Nat.zero_le _)).wlt hv)
    ((Small.const _ 1).mono (fun _ => Nat.sub_le _ _))).cong (fun _ => rfl) (fun i => ?_)
  by_cases h2 : E.mx * (μ i * colS E.W E.tq (h i) (u i)) ≤ n i
  · simp [h2, Nat.not_lt.mpr h2]
  · simp [h2, Nat.lt_of_not_le h2]

/-- **The indicator of a source code** `u < W^(h+1)` of the child `(h, μ*r)` of `(h+1, μ)`. -/
lemma can_srcU {n h μ r u : ι → ℕ} (hn : Knows m B s x n) (hh : Knows m B s x h) (hμ : Knows m B s x μ)
    (hr : Knows m B s x r) (hu : Knows m B s x u) (hlt : ∀ i, u i < E.W^(h i) * E.W)
    (hns : Small B n) (hhs : Small B h) (hμs : Small B μ) (hrs : Small B r) (hus : Small B u)
    (hpow : Small B (fun i => E.mx^(h i + 1))) :
    Can m B s w x (fun i => if E.srcU (n i) (h i) (μ i) (r i) (u i) then 1 else 0)
      (fun i => 2 * h i + 3) := by
  have hW := E.W_pos
  have hpow0 : Small B (fun i => E.mx^(h i)) :=
    hpow.mono (fun i => Nat.pow_le_pow_right (lt_of_lt_of_le (by norm_num) E.three) (Nat.le_succ _))
  have hμr : Knows m B s x (fun i => μ i * r i) := hμ.times hr hμs hrs
  have hud : Knows m B s x (fun i => u i / E.W) := hu.dvdW (Can.wc E.W) hus
  have h1 := E.can_fits hn hh hμr hud hns hhs (hμs.mul hrs) hus.div hpow0
  have hh1 : Knows m B s x (fun i => h i + 1) := hh.plus (Can.wc 1) hhs (Small.const _ 1)
  have h2 := E.can_fits hn hh1 hμ hu hns (hhs.add (Small.const _ 1)) hμs hus hpow
  have h2' : Can m B s w x (fun i => 1 - (if E.mx * (μ i * colS E.W E.tq (h i + 1) (u i)) ≤ n i then 1 else 0))
      (fun i => h i + 1 + 1) := (Can.wc 1).wsub h2 ((Small.const _ 1).mono (fun _ => Nat.sub_le _ _))
  have H := (h1.mono (W' := fun i => 2 * h i + 3) (fun i => by omega)).times
    (h2'.mono (W' := fun i => 2 * h i + 3) (fun i => by omega))
    ((Small.const _ 1).mono (fun i => by split <;> omega)) ((Small.const _ 1).mono (fun _ => Nat.sub_le _ _))
  refine H.cong (fun _ => rfl) (fun i => ?_)
  have hd : u i / E.W < E.W^(h i) := (Nat.div_lt_iff_lt_mul hW).2 (hlt i)
  have hu1 : u i < E.W^(h i + 1) := by rw [pow_succ]; exact hlt i
  unfold srcU inRS
  by_cases c1 : E.mx * (μ i * r i * colS E.W E.tq (h i) (u i / E.W)) ≤ n i <;>
    by_cases c2 : E.mx * (μ i * colS E.W E.tq (h i + 1) (u i)) ≤ n i <;>
    simp [c1, c2, hd, hu1, mul_assoc]

/-- **The source slots of a child, counted**: one loop over `W^(h+1)` codes (`W^h` ready). -/
lemma can_ownCnt {n h μ r : ι → ℕ} (hn : Knows m B s x n) (hh : Knows m B s x h) (hμ : Knows m B s x μ)
    (hr : Knows m B s x r) (hWh : Knows m B s x (fun i => E.W^(h i)))
    (hns : Small B n) (hhs : Small B h) (hμs : Small B μ) (hrs : Small B r)
    (hWs : Small B (fun i => E.W^(h i) * E.W)) (hpow : Small B (fun i => E.mx^(h i + 1))) :
    Can m B s w x (fun i => Nat.count (E.srcU (n i) (h i) (μ i) (r i)) (E.W^(h i) * E.W))
      (fun i => E.W^(h i) * E.W * (2 * h i + 3 + 1) + 1) := by
  have hT : Knows m B s x (fun i => E.W^(h i) * E.W) :=
    hWh.times (Can.wc E.W) (hWs.mono (fun i => Nat.le_mul_of_pos_right _ E.W_pos)) (Small.const _ _)
  let BD (d : During (fun i => E.W^(h i) * E.W)) := B d.i
  have F : ∀ {t : Ty} {y : ι → T t}, Has m B s t x y →
      Has m BD (p s w) t (fun d => (x d.i, d.j)) (fun d => y d.i) :=
    fun g => Can.first.then_do (g.reindex (fun d : During (fun i => E.W^(h i) * E.W) => d.i))
  have hind := E.can_srcU (F hn) (F hh) (F hμ) (F hr) (Can.second) (fun d => d.hj)
    (hns.reindex (fun d : During (fun i => E.W^(h i) * E.W) => d.i)) (hhs.reindex (fun d : During (fun i => E.W^(h i) * E.W) => d.i)) (hμs.reindex (fun d : During (fun i => E.W^(h i) * E.W) => d.i)) (hrs.reindex (fun d : During (fun i => E.W^(h i) * E.W) => d.i))
    ((hWs.reindex (fun d : During (fun i => E.W^(h i) * E.W) => d.i)).mono (fun d => d.hj.le))
    (hpow.reindex (fun d : During (fun i => E.W^(h i) * E.W) => d.i))
  exact can_count hT hWs hind

/-! ## The recursion over the class tree -/

/-- Children of a count descriptor `(n, h, μ)`: one per block letter. -/
def kidsCnt (d : ℕ × ℕ × ℕ) : List (ℕ × ℕ × ℕ) :=
  match d.2.1 with
  | 0 => []
  | h + 1 => (List.range E.nB).map (fun j => (d.1, h, d.2.2 * E.rkI j))

/-- The answer of a count descriptor. -/
def outCnt (d : ℕ × ℕ × ℕ) : ℕ := E.cons d.1 d.2.1 d.2.2

def Rs : ℕ := (blockRanks E.wd).sum + 1

lemma rkI_le (j : ℕ) : E.rkI j ≤ E.Rs := by
  unfold rkI Rs
  by_cases hj : j < (blockRanks E.wd).length
  · rw [List.getD_eq_getElem _ _ hj]
    have := List.le_sum_of_mem (List.getElem_mem hj)
    omega
  · rw [List.getD_eq_default _ _ (by omega)]; omega

/-- `A = (nB + 1) * (W + 1)`. -/
def Ac : ℕ := (E.nB + 1) * (E.W + 1)

lemma Ac_pos : 1 ≤ E.Ac := by unfold Ac; nlinarith

lemma cons_le (n h μ : ℕ) : E.cons n h μ ≤ E.Ac ^ (2 * h) := by
  induction h generalizing μ with
  | zero => rw [cons_zero]; exact Nat.zero_le _
  | succ h ih =>
    rw [cons_succ_idx]
    have hA := E.Ac_pos
    have hW := E.W_pos
    have h1 : ∀ j ∈ Finset.range E.nB, Nat.count (E.srcU n h μ (E.rkI j)) (E.W^h * E.W) +
        E.cons n h (μ * E.rkI j) ≤ E.Ac^(2*h+1) + E.Ac^(2*h) := by
      intro j _
      refine Nat.add_le_add ?_ (ih _)
      refine le_trans (count_le_self _) ?_
      rw [← pow_succ]
      calc E.W^(h+1) ≤ E.Ac^(h+1) :=
            Nat.pow_le_pow_left (by unfold Ac; nlinarith) _
        _ ≤ E.Ac^(2*h+1) := Nat.pow_le_pow_right hA (by omega)
    refine le_trans (Finset.sum_le_sum h1) ?_
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    have h2 : E.Ac^(2*h) ≤ E.Ac^(2*h+1) := Nat.pow_le_pow_right hA (by omega)
    have h3 : 2 * E.nB ≤ E.Ac := by unfold Ac; nlinarith
    calc E.nB * (E.Ac^(2*h+1) + E.Ac^(2*h)) ≤ E.nB * (2 * E.Ac^(2*h+1)) := by
          apply Nat.mul_le_mul_left; omega
      _ = (2 * E.nB) * E.Ac^(2*h+1) := by ring
      _ ≤ E.Ac * E.Ac^(2*h+1) := Nat.mul_le_mul_right _ h3
      _ = E.Ac^(2 * (h+1)) := by ring

/-- A constant dominating every quantity of one step of the recursion. -/
def Kb : ℕ := E.Ac^2 * E.W * E.mx * E.Rs + 2

lemma Kb_ge : 2 ≤ E.Kb := by unfold Kb; omega

/-- The word driver of the count recursion. -/
def bndC (d : ℕ × ℕ × ℕ) : ℕ := (d.1 + 2) * E.Kb^(d.2.1 + 1) * (d.2.2 + 1)

/-- Local work of a count step (children at height `h`). -/
def locH (h : ℕ) : ℕ := E.nB * (E.W^h * E.W * (2 * h + 3 + 1) + 1 + (h + 1) + 4)

def locC (d : ℕ × ℕ × ℕ) : ℕ :=
  match d.2.1 with
  | 0 => 0
  | h + 1 => E.locH h

def cstC : ℕ → ℕ
  | 0 => 1
  | h + 1 => E.locH h + 1 + E.nB * cstC h

lemma W_le_Kb : E.W ≤ E.Kb := by
  have h1 : E.W ≤ E.Ac := by unfold Ac; nlinarith
  have h2 : E.Ac ≤ E.Ac^2 := by nlinarith [E.Ac_pos]
  have h3 : 1 ≤ E.mx := le_trans (by norm_num) E.three
  have h4 : 1 ≤ E.Rs := by unfold Rs; omega
  have h5 : E.Ac^2 ≤ E.Ac^2 * E.W * E.mx * E.Rs := by
    have := E.W_pos; nlinarith [Nat.mul_le_mul (Nat.mul_le_mul (le_refl (E.Ac^2)) (show 1 ≤ E.W from E.W_pos)) h3]
  unfold Kb; omega

lemma mx_le_Kb : E.mx ≤ E.Kb := by
  have h1 : 1 ≤ E.Ac^2 * E.W * E.Rs := by
    have := E.Ac_pos; have := E.W_pos; have h4 : 1 ≤ E.Rs := by unfold Rs; omega
    have : 1 ≤ E.Ac^2 := Nat.one_le_pow _ _ E.Ac_pos
    nlinarith [Nat.mul_le_mul this (show 1 ≤ E.W from E.W_pos)]
  unfold Kb
  nlinarith [Nat.mul_le_mul_left E.mx h1]

lemma Rs_le_Kb : E.Rs ≤ E.Kb := by
  have h1 : 1 ≤ E.Ac^2 * E.W * E.mx := by
    have : 1 ≤ E.Ac^2 := Nat.one_le_pow _ _ E.Ac_pos
    have h3 : 1 ≤ E.mx := le_trans (by norm_num) E.three
    nlinarith [Nat.mul_le_mul this (show 1 ≤ E.W from E.W_pos)]
  unfold Kb
  nlinarith [Nat.mul_le_mul_right E.Rs h1]

lemma nB_le_Kb : E.nB ≤ E.Kb := by
  have h1 : E.nB ≤ E.Ac := by unfold Ac; nlinarith [E.W_pos]
  have h2 : E.Ac ≤ E.Ac^2 := by nlinarith [E.Ac_pos]
  have h3 : E.Ac^2 ≤ E.Ac^2 * E.W * E.mx * E.Rs := by
    have h4 : 1 ≤ E.Rs := by unfold Rs; omega
    have h5 : 1 ≤ E.mx := le_trans (by norm_num) E.three
    have h6 : 1 ≤ E.W * E.mx * E.Rs := by
      have := E.W_pos; nlinarith [Nat.mul_le_mul (show 1 ≤ E.W from E.W_pos) h5]
    nlinarith [Nat.mul_le_mul_left (E.Ac^2) h6]
  unfold Kb; omega

lemma Ac2_le_Kb : E.Ac^2 ≤ E.Kb := by
  have h4 : 1 ≤ E.Rs := by unfold Rs; omega
  have h5 : 1 ≤ E.mx := le_trans (by norm_num) E.three
  have h6 : 1 ≤ E.W * E.mx * E.Rs := by
    have := E.W_pos; nlinarith [Nat.mul_le_mul (show 1 ≤ E.W from E.W_pos) h5]
  have : E.Ac^2 ≤ E.Ac^2 * E.W * E.mx * E.Rs := by nlinarith [Nat.mul_le_mul_left (E.Ac^2) h6]
  unfold Kb; omega

/-- Children have smaller drivers. -/
lemma bndC_kid (d c : ℕ × ℕ × ℕ) (hc : c ∈ E.kidsCnt d) : E.bndC c ≤ E.bndC d := by
  unfold kidsCnt at hc
  rcases d with ⟨n, h, μ⟩
  cases h with
  | zero => simp at hc
  | succ h =>
    simp only [List.mem_map, List.mem_range] at hc
    obtain ⟨j, -, rfl⟩ := hc
    unfold bndC
    simp only
    have hr := E.rkI_le j
    have hK := E.Rs_le_Kb
    have e1 : μ * E.rkI j + 1 ≤ (μ + 1) * E.Kb := by nlinarith [E.Kb_ge]
    calc (n + 2) * E.Kb ^ (h + 1) * (μ * E.rkI j + 1) ≤ (n + 2) * E.Kb ^ (h + 1) * ((μ + 1) * E.Kb) :=
          Nat.mul_le_mul_left _ e1
      _ = (n + 2) * E.Kb ^ (h + 1 + 1) * (μ + 1) := by ring

/-- A quantity at most `bnd^2` is small. -/
lemma small_sq {κ : Type*} {Bk f : κ → ℕ} (h : ∀ k, f k ≤ Bk k * Bk k) : Small Bk f :=
  ⟨2, fun k => le_trans (h k) (by nlinarith)⟩

/-- The partial sums of the count step. -/
def vC (n h μ j : ℕ) : ℕ :=
  ∑ j' ∈ Finset.range j, (Nat.count (E.srcU n h μ (E.rkI j')) (E.W^h * E.W) + E.cons n h (μ * E.rkI j'))

lemma vC_le (n h μ j : ℕ) (hj : j ≤ E.nB) : E.vC n h μ j ≤ E.Ac^(2 * (h+1)) := by
  have h1 : E.vC n h μ j ≤ E.vC n h μ E.nB :=
    Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 hj)
  have h2 : E.vC n h μ E.nB = E.cons n (h+1) μ := (cons_succ_idx E n h μ).symm
  rw [h2] at h1
  exact le_trans h1 (E.cons_le n (h+1) μ)

open PowerSaving.MCost in
/-- **The body of the count recursion**: `h = 0` answers `0`; otherwise one loop over the block
letters: count the child's source slots, ONE call for the child's subtree, add. -/
theorem cnt_body (m : Bool) :
    Able m (gfunds (s := p w (p w w)) (t := w) (fun d : ℕ × ℕ × ℕ => d) E.outCnt
        (fun d c => c ∈ E.kidsCnt d) E.bndC) (p w (p w w)) w
      (fun i => i.d) (fun i => E.outCnt i.d) (fun i => E.locC i.d)
      (fun i => listCharge E.kidsCnt i.d i.tau) := by
  let G := GDesc (s := p w (p w w)) (t := w) (fun d : ℕ × ℕ × ℕ => d) E.outCnt (fun d c => c ∈ E.kidsCnt d)
  let b := gfunds (s := p w (p w w)) (t := w) (fun d : ℕ × ℕ × ℕ => d) E.outCnt
    (fun d c => c ∈ E.kidsCnt d) E.bndC
  have hx : Able m b (p w (p w w)) w (fun i => i.d) (fun i => i.d.2.1) (fun _ => 0) (fun _ => 0) :=
    Able.of_can (Can.second.fst)
  -- h = 0
  have hz : Able m (b.comap (fun i : {i : G // i.d.2.1 = 0} => i.val)) (p w (p w w)) w
      (fun i => i.val.d) (fun i => E.outCnt i.val.d) (fun i => E.locC i.val.d)
      (fun i => listCharge E.kidsCnt i.val.d i.val.tau) := by
    refine ((Able.of_can (Can.wc 0)).mono (fun _ => Nat.zero_le _) (fun _ => Nat.zero_le _)).cong
      (fun _ => rfl) (fun i => ?_)
    show 0 = E.cons i.val.d.1 i.val.d.2.1 i.val.d.2.2
    rw [i.2, cons_zero]
  -- h ≥ 1: one loop over the block letters
  let S := {i : G // i.d.2.1 ≠ 0}
  let b3 := b.comap (fun i : S => i.val)
  let nS (i : S) := i.val.d.1
  let hS (i : S) := i.val.d.2.1 - 1
  let μS (i : S) := i.val.d.2.2
  let child (i : S) (j : ℕ) : ℕ × ℕ × ℕ := (nS i, hS i, μS i * E.rkI j)
  have hmem : ∀ (i : S) (j : ℕ), j < E.nB → child i j ∈ E.kidsCnt i.val.d := by
    intro i j hj
    obtain ⟨⟨⟨n, h, μ⟩, use, tau, peak, works⟩, h0⟩ := i
    have h0' : h ≠ 0 := h0
    obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
    simp only [kidsCnt, List.mem_map, List.mem_range]
    exact ⟨j, hj, by simp [child, nS, hS, μS]⟩
  let Wb (i : S) (_ : ℕ) : ℕ := E.W^(hS i) * E.W * (2 * hS i + 3 + 1) + 1 + (hS i + 1)
  let Zb (i : S) (j : ℕ) : ℕ := i.val.tau (child i j)
  let Dd := During (fun _ : S => E.nB)
  let b4 := b3.comap (During.i (n := fun _ : S => E.nB))
  let env (d : Dd) : T (p (p w (p w w)) (p w w)) := (d.i.val.d, (d.j, E.vC (nS d.i) (hS d.i) (μS d.i) d.j))
  let Bd (d : Dd) : ℕ := E.bndC d.i.val.d
  have hb4 : b4.B = Bd := rfl
  -- bounds
  have hbnd : ∀ d : Dd, (nS d.i + 2) * E.Kb^(hS d.i + 1 + 1) * (μS d.i + 1) = Bd d := by
    intro d
    have h0 : d.i.val.d.2.1 ≠ 0 := d.i.2
    simp only [Bd, bndC, nS, hS, μS]
    congr 2; congr 1; omega
  have hKp : ∀ d : Dd, E.Kb^(hS d.i + 1 + 1) ≤ Bd d := by
    intro d; rw [← hbnd d]
    calc E.Kb^(hS d.i + 1 + 1) = 1 * E.Kb^(hS d.i + 1 + 1) * 1 := by ring
      _ ≤ (nS d.i + 2) * E.Kb^(hS d.i + 1 + 1) * (μS d.i + 1) := by gcongr <;> omega
  have hKpow : ∀ d : Dd, ∀ e ≤ hS d.i + 1 + 1, E.Kb^e ≤ Bd d := fun d e he =>
    le_trans (Nat.pow_le_pow_right (by have := E.Kb_ge; omega) he) (hKp d)
  have hK1 : ∀ d : Dd, E.Kb ≤ Bd d := fun d => by simpa using hKpow d 1 (by omega)
  have hnB : ∀ d : Dd, nS d.i ≤ Bd d := by
    intro d; rw [← hbnd d]
    have h1 : 1 ≤ E.Kb^(hS d.i + 1 + 1) := Nat.one_le_pow _ _ (by have := E.Kb_ge; omega)
    calc nS d.i ≤ (nS d.i + 2) * 1 * 1 := by omega
      _ ≤ (nS d.i + 2) * E.Kb^(hS d.i + 1 + 1) * (μS d.i + 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul le_rfl h1) (by omega)
  have hμB : ∀ d : Dd, μS d.i ≤ Bd d := by
    intro d; rw [← hbnd d]
    have h1 : 1 ≤ E.Kb^(hS d.i + 1 + 1) := Nat.one_le_pow _ _ (by have := E.Kb_ge; omega)
    calc μS d.i ≤ 1 * 1 * (μS d.i + 1) := by omega
      _ ≤ (nS d.i + 2) * E.Kb^(hS d.i + 1 + 1) * (μS d.i + 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul (by omega) h1) le_rfl
  have hB4 : ∀ d : Dd, 4 ≤ Bd d := by
    intro d
    have h1 : 2^2 ≤ E.Kb^2 := Nat.pow_le_pow_left E.Kb_ge 2
    have h2 := hKpow d 2 (by omega)
    norm_num at h1; omega
  have hhB : ∀ d : Dd, hS d.i + 1 ≤ Bd d := by
    intro d
    have h1 : hS d.i + 1 < 2^(hS d.i + 1) := Nat.lt_two_pow_self
    have h2 : 2^(hS d.i + 1) ≤ E.Kb^(hS d.i + 1) := Nat.pow_le_pow_left E.Kb_ge _
    have h3 := hKpow d (hS d.i + 1) (by omega)
    omega
  have hWB : ∀ d : Dd, E.W^(hS d.i) * E.W ≤ Bd d := by
    intro d
    have h1 : E.W^(hS d.i) * E.W = E.W^(hS d.i + 1) := by ring
    rw [h1]
    exact le_trans (Nat.pow_le_pow_left E.W_le_Kb _) (hKpow d _ (by omega))
  have hmxB : ∀ d : Dd, E.mx^(hS d.i + 1) ≤ Bd d := fun d =>
    le_trans (Nat.pow_le_pow_left E.mx_le_Kb _) (hKpow d _ (by omega))
  have hjB : ∀ d : Dd, d.j ≤ Bd d := fun d => le_trans (le_trans d.hj.le E.nB_le_Kb) (hK1 d)
  have hrB : ∀ d : Dd, E.rkI d.j ≤ Bd d := fun d => le_trans (le_trans (E.rkI_le _) E.Rs_le_Kb) (hK1 d)
  have hvB : ∀ d : Dd, E.vC (nS d.i) (hS d.i) (μS d.i) d.j ≤ Bd d := by
    intro d
    have h1 := E.vC_le (nS d.i) (hS d.i) (μS d.i) d.j d.hj.le
    have h2 : E.Ac^(2 * (hS d.i + 1)) ≤ E.Kb^(hS d.i + 1) := by
      rw [pow_mul]; exact Nat.pow_le_pow_left E.Ac2_le_Kb _
    exact le_trans h1 (le_trans h2 (hKpow d _ (by omega)))
  have hcB : ∀ d : Dd, E.cons (nS d.i) (hS d.i) (μS d.i * E.rkI d.j) ≤ Bd d := by
    intro d
    have h1 := E.cons_le (nS d.i) (hS d.i) (μS d.i * E.rkI d.j)
    have h2 : E.Ac^(2 * hS d.i) ≤ E.Kb^(hS d.i) := by
      rw [pow_mul]; exact Nat.pow_le_pow_left E.Ac2_le_Kb _
    exact le_trans h1 (le_trans h2 (hKpow d _ (by omega)))
  have hcntB : ∀ d : Dd, Nat.count (E.srcU (nS d.i) (hS d.i) (μS d.i) (E.rkI d.j)) (E.W^(hS d.i) * E.W) ≤ Bd d :=
    fun d => le_trans (count_le_self _) (hWB d)
  -- the step
  have hs : Able m b4 (p (p w (p w w)) (p w w)) w env
      (fun d => E.vC (nS d.i) (hS d.i) (μS d.i) (d.j + 1)) (fun d => Wb d.i d.j) (fun d => Zb d.i d.j) := by
    have nK : Knows m Bd (p (p w (p w w)) (p w w)) env (fun d => nS d.i) := Can.first.then_do Can.first
    have hhK : Knows m Bd (p (p w (p w w)) (p w w)) env (fun d => d.i.val.d.2.1) :=
      Can.first.then_do Can.second.fst
    have μK : Knows m Bd (p (p w (p w w)) (p w w)) env (fun d => μS d.i) := Can.first.then_do Can.second.snd
    have jK : Knows m Bd (p (p w (p w w)) (p w w)) env (fun d => d.j) := Can.second.fst
    have aK : Knows m Bd (p (p w (p w w)) (p w w)) env (fun d => E.vC (nS d.i) (hS d.i) (μS d.i) d.j) :=
      Can.second.snd
    have sh : Small Bd (fun d => d.i.val.d.2.1) := small_sq (fun d => by
      have := hhB d; have h0 : d.i.val.d.2.1 ≠ 0 := d.i.2
      have : d.i.val.d.2.1 ≤ Bd d := by simp only [hS] at this; omega
      nlinarith)
    have hK' : Knows m Bd (p (p w (p w w)) (p w w)) env (fun d => hS d.i) := hhK.minus (Can.wc 1) sh
    have rK : Knows m Bd (p (p w (p w w)) (p w w)) env (fun d => E.rkI d.j) := by
      apply Can.cases_code (q := fun d : Dd => (⟨d.j, d.hj⟩ : Fin E.nB)) (Layout.std E.nB) jK
      intro f
      refine (Can.wc (E.rkI f)).cong (fun _ => rfl) (fun d => ?_)
      show E.rkI f = E.rkI d.1.j
      rw [show d.1.j = (f : ℕ) from congrArg Fin.val d.2]
    have sn : Small Bd (fun d => nS d.i) := small_sq (fun d => by nlinarith [hnB d])
    have sμ : Small Bd (fun d => μS d.i) := small_sq (fun d => by nlinarith [hμB d])
    have sr : Small Bd (fun d => E.rkI d.j) := small_sq (fun d => by nlinarith [hrB d])
    have shS : Small Bd (fun d => hS d.i) := small_sq (fun d => by nlinarith [hhB d])
    have sμr : Small Bd (fun d => μS d.i * E.rkI d.j) := small_sq (fun d => Nat.mul_le_mul (hμB d) (hrB d))
    have μrK : Knows m Bd (p (p w (p w w)) (p w w)) env (fun d => μS d.i * E.rkI d.j) := μK.times rK sμ sr
    -- the child's input and the call
    have hin : Has m Bd (p (p w (p w w)) (p w w)) (p w (p w w)) env (fun d => child d.i d.j) :=
      nK.pair (hK'.pair μrK)
    have hcall : Able m b4 (p w (p w w)) w (fun d => child d.i d.j)
        (fun d => E.cons (nS d.i) (hS d.i) (μS d.i * E.rkI d.j)) (fun _ => 0) (fun d => Zb d.i d.j) :=
      Able.use_call (fun d => d.i.val.works (child d.i d.j) (hmem d.i d.j d.hj))
    have A2 : Able m b4 (p (p w (p w w)) (p w w)) w env
        (fun d => E.cons (nS d.i) (hS d.i) (μS d.i * E.rkI d.j)) (fun _ => 0 + 0) (fun d => 0 + Zb d.i d.j) :=
      (Able.of_can (b := b4) hin).comp hcall
    -- the count
    have sW : Small Bd (fun d => E.W^(hS d.i)) := small_sq (fun d => by
      have := hWB d; have : E.W^(hS d.i) ≤ E.W^(hS d.i) * E.W := Nat.le_mul_of_pos_right _ E.W_pos
      nlinarith)
    have p2 : Can m Bd (p (p w (p w w)) (p w w)) w env (fun d => E.W^(hS d.i)) (fun d => hS d.i + 1) :=
      can_powv E.W E.W_pos hK' shS sW
    let env' (d : Dd) : T (p (p (p w (p w w)) (p w w)) w) := (env d, E.W^(hS d.i))
    have F : ∀ {t : Ty} {y : Dd → T t}, Has m Bd (p (p w (p w w)) (p w w)) t env y →
        Has m Bd (p (p (p w (p w w)) (p w w)) w) t env' y := fun g => Can.first.then_do g
    have cnt := E.can_ownCnt (F nK) (F hK') (F μK) (F rK) (Can.second) sn shS sμ sr
      (small_sq (fun d => by nlinarith [hWB d])) (small_sq (fun d => by nlinarith [hmxB d]))
    have A1c : Can m Bd (p (p w (p w w)) (p w w)) w env
        (fun d => Nat.count (E.srcU (nS d.i) (hS d.i) (μS d.i) (E.rkI d.j)) (E.W^(hS d.i) * E.W))
        (fun d => (hS d.i + 1) + (E.W^(hS d.i) * E.W * (2 * hS d.i + 3 + 1) + 1)) :=
      Can.save p2 cnt
    have A1 := Able.of_can (b := b4) A1c
    have A3 := Able.of_can (b := b4) aK
    have Fk := A3.fork (A1.fork A2)
    -- add
    let tri (d : Dd) : T (p w (p w w)) := (E.vC (nS d.i) (hS d.i) (μS d.i) d.j,
      (Nat.count (E.srcU (nS d.i) (hS d.i) (μS d.i) (E.rkI d.j)) (E.W^(hS d.i) * E.W),
       E.cons (nS d.i) (hS d.i) (μS d.i * E.rkI d.j)))
    have hadd : Knows m Bd (p w (p w w)) tri
        (fun d => (tri d).1 + ((tri d).2.1 + (tri d).2.2)) :=
      Can.first.plus (Can.second.fst.plus Can.second.snd
        (small_sq (fun d => le_trans (hcntB d) (by nlinarith [hB4 d])))
        (small_sq (fun d => le_trans (hcB d) (by nlinarith [hB4 d]))))
        (small_sq (fun d => le_trans (hvB d) (by nlinarith [hB4 d])))
        (small_sq (fun d => by
          have h1 := hcntB d; have h2 := hcB d; have h3 := hB4 d
          show _ + _ ≤ _
          nlinarith))
    have H := Fk.comp (Able.of_can (b := b4) hadd)
    refine (H.cong (fun _ => rfl) (fun d => ?_)).weaken (Dom.of_le (fun d => ?_)) (fun d => by simp)
    · show E.vC (nS d.i) (hS d.i) (μS d.i) d.j + (Nat.count (E.srcU (nS d.i) (hS d.i) (μS d.i) (E.rkI d.j))
        (E.W^(hS d.i) * E.W) + E.cons (nS d.i) (hS d.i) (μS d.i * E.rkI d.j)) = E.vC (nS d.i) (hS d.i) (μS d.i) (d.j + 1)
      simp only [vC, Finset.sum_range_succ]
    · simp only [Wb]; omega
  have hloop := Able.loop (b := b3) (s := p w (p w w)) (x := fun i : S => (i.val.d : T (p w (p w w))))
    (n := fun _ : S => E.nB) (v := fun i j => E.vC (nS i) (hS i) (μS i) j)
    (Wb := Wb) (Zb := Zb) (Able.of_can (Can.wc (W := fun _ => 0) E.nB))
    (Able.of_can ((Can.wc (W := fun _ => 0) 0).cong (fun _ => rfl) (fun i => by simp [vC]))) hs (Small.const _ _)
  have hn : Able m (b.comap (fun i : {i : G // i.d.2.1 ≠ 0} => i.val)) (p w (p w w)) w
      (fun i => i.val.d) (fun i => E.outCnt i.val.d) (fun i => E.locC i.val.d)
      (fun i => listCharge E.kidsCnt i.val.d i.val.tau) := by
    refine (hloop.cong (fun _ => rfl) (fun i => ?_)).weaken (Dom.of_le (fun i => ?_)) (fun i => ?_)
    · obtain ⟨⟨⟨n, h, μ⟩, use, tau, peak, works⟩, h0⟩ := i
      have h0' : h ≠ 0 := h0
      obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
      show E.vC n (h' + 1 - 1) μ E.nB = E.cons n (h' + 1) μ
      simp only [Nat.add_sub_cancel]
      exact (cons_succ_idx E n h' μ).symm
    · obtain ⟨⟨⟨n, h, μ⟩, use, tau, peak, works⟩, h0⟩ := i
      have h0' : h ≠ 0 := h0
      obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
      simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, Wb, hS, locC, locH, Nat.add_sub_cancel]
      nlinarith
    · obtain ⟨⟨⟨n, h, μ⟩, use, tau, peak, works⟩, h0⟩ := i
      have h0' : h ≠ 0 := h0
      obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
      simp only [Zb, child, nS, hS, μS, listCharge, kidsCnt, Nat.add_sub_cancel, zero_add]
      rw [List.map_map, sum_map_range]
      rfl
  have H := Able.ifz (t := w) (y := fun i : G => E.outCnt i.d) (W := fun i : G => E.locC i.d)
    (Z := fun i : G => listCharge E.kidsCnt i.d i.tau) hx hz hn
  exact H.mono (fun i => by simp) (fun i => by simp)

open PowerSaving.MCost in
/-- **The consumption count as ONE closed program**: `cons n h μ` in work `cstC h`. -/
theorem can_cons (m : Bool) {ι : Type U} (dd : ι → ℕ × ℕ × ℕ) :
    Can m (fun i => E.bndC (dd i)) (p w (p w w)) w (fun i => dd i) (fun i => E.cons (dd i).1 (dd i).2.1 (dd i).2.2)
      (fun i => E.cstC (dd i).2.1) := by
  refine recurse_list (s := p w (p w w)) (t := w) m (fun d => d) E.outCnt E.kidsCnt E.bndC E.locC
    (fun d => d.2.1) (fun d => d.2.1 + 1) (fun d => E.cstC d.2.1) (E.cnt_body m) ?_ (E.bndC_kid) ?_ ?_
    (fun d => Nat.lt_succ_self _) ?_ dd
  · intro d c hc
    rcases d with ⟨n, h, μ⟩
    cases h with
    | zero => simp [kidsCnt] at hc
    | succ h =>
      simp only [kidsCnt, List.mem_map, List.mem_range] at hc
      obtain ⟨j, -, rfl⟩ := hc
      simp
  · intro d
    rcases d with ⟨n, h, μ⟩
    cases h with
    | zero => simp [locC, kidsCnt, cstC]
    | succ h =>
      simp only [locC, kidsCnt, List.map_map, cstC]
      rw [show ((List.range E.nB).map ((fun d : ℕ × ℕ × ℕ => E.cstC d.2.1) ∘ fun j => (n, h, μ * E.rkI j))).sum
          = E.nB * E.cstC h by
        rw [sum_map_range]; simp]
  · have hfs : Small E.bndC (fun d : ℕ × ℕ × ℕ => d.2.1 + 1) := ⟨1, fun d => by
      simp only [bndC, pow_one]
      have h1 : d.2.1 + 1 < 2^(d.2.1 + 1) := Nat.lt_two_pow_self
      have h2 : 2^(d.2.1 + 1) ≤ E.Kb^(d.2.1 + 1) := Nat.pow_le_pow_left E.Kb_ge _
      have h3 : E.Kb^(d.2.1 + 1) ≤ (d.1 + 2) * E.Kb^(d.2.1 + 1) * (d.2.2 + 1) := by
        calc E.Kb^(d.2.1 + 1) = 1 * E.Kb^(d.2.1 + 1) * 1 := by ring
          _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul (by omega) le_rfl) (by omega)
      exact le_trans (le_of_lt (lt_of_lt_of_le h1 (le_trans h2 h3))) (Nat.le_add_right _ _)⟩
    exact ((Can.second.fst).plus (Can.wc 1) (hfs.mono (fun d => Nat.le_succ _)) (Small.const _ 1)).mono
      (fun _ => Nat.zero_le _)
  · exact ⟨1, fun d => by
      simp only [bndC, pow_one]
      have h1 : d.2.1 + 1 < 2^(d.2.1 + 1) := Nat.lt_two_pow_self
      have h2 : 2^(d.2.1 + 1) ≤ E.Kb^(d.2.1 + 1) := Nat.pow_le_pow_left E.Kb_ge _
      have h3 : E.Kb^(d.2.1 + 1) ≤ (d.1 + 2) * E.Kb^(d.2.1 + 1) * (d.2.2 + 1) := by
        calc E.Kb^(d.2.1 + 1) = 1 * E.Kb^(d.2.1 + 1) * 1 := by ring
          _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul (by omega) le_rfl) (by omega)
      exact le_trans (le_of_lt (lt_of_lt_of_le h1 (le_trans h2 h3))) (Nat.le_add_right _ _)⟩

lemma locH_mono {h h' : ℕ} (hh : h ≤ h') : E.locH h ≤ E.locH h' := by
  unfold locH
  apply Nat.mul_le_mul_left
  have h1 : E.W^h ≤ E.W^h' := Nat.pow_le_pow_right E.W_pos hh
  have h2 : E.W^h * E.W * (2 * h + 3 + 1) ≤ E.W^h' * E.W * (2 * h' + 3 + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_right _ h1) (by omega)
  omega

/-- The work of the count is at most `(nB+1)^h * (locH h + 2)`. -/
lemma cstC_le (h : ℕ) : E.cstC h ≤ (E.nB + 1)^h * (E.locH h + 2) := by
  induction h with
  | zero => simp [cstC]
  | succ h ih =>
    simp only [cstC]
    have hm : E.locH h ≤ E.locH (h+1) := E.locH_mono (by omega)
    have h1 : E.nB * E.cstC h ≤ E.nB * ((E.nB + 1)^h * (E.locH (h+1) + 2)) :=
      Nat.mul_le_mul_left _ (le_trans ih (Nat.mul_le_mul_left _ (by omega)))
    have h2 : 1 ≤ (E.nB + 1)^h := Nat.one_le_pow _ _ (by omega)
    calc E.locH h + 1 + E.nB * E.cstC h ≤ (E.locH (h+1) + 2) + E.nB * ((E.nB + 1)^h * (E.locH (h+1) + 2)) := by
          omega
      _ ≤ (E.nB + 1)^h * (E.locH (h+1) + 2) + E.nB * ((E.nB + 1)^h * (E.locH (h+1) + 2)) := by
          have : E.locH (h+1) + 2 ≤ (E.nB + 1)^h * (E.locH (h+1) + 2) := Nat.le_mul_of_pos_left _ h2
          omega
      _ = (E.nB + 1)^(h+1) * (E.locH (h+1) + 2) := by ring

end Eng

end
end PowerSaving.RAM
end OAI

#print axioms OAI.PowerSaving.RAM.Eng.can_ownCnt
#print axioms OAI.PowerSaving.RAM.Eng.cnt_body
#print axioms OAI.PowerSaving.RAM.Eng.can_cons
