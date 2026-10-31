import Submission.Work.Mixed.Prog.Merged1

/-!
# Mixed engine, R3 program part 7: counting loops (agent e-r3prog)

Generic RAM loops for the index tables of a class (all polynomial bookkeeping, `O(W^h)` codes):

* `can_count`  `Nat.count P T` by one loop over `j < T` (one indicator test per step);
* `can_nthc`   `Nat.nth P p` (when `p < count P T`) by one search loop;
* `can_powv`   `W^h` for a variable `h`;
* `Eng.knows_tq`  the target rank of a live-role position (a fixed finite case split);
* `Eng.can_colS`  the column factor `colS h s` by `h` steps of `stepC`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset GF MXR
noncomputable section

universe U

section Loops
variable {ι : Type U} {m : Bool} {B : ι → ℕ} {s : Ty} {x : ι → T s}

/-- The loop environment `(x, (j, acc))` contains the index environment `(x, j)`. -/
lemma env_ix {t : Ty} {n : ι → ℕ} {v : ι → ℕ → T t} :
    Has m (fun d : During n => B d.i) (p s (p w t)) (p s w) (fun d => (x d.i, d.j, v d.i d.j))
      (fun d => (x d.i, d.j)) :=
  Can.first.pair (Can.fst Can.second)

/-- **Counting loop.** -/
lemma can_count {P : ι → ℕ → Prop} [∀ i, DecidablePred (P i)] {T Wt : ι → ℕ}
    (hT : Knows m B s x T) (hTs : Small B T)
    (hind : Can m (fun d : During T => B d.i) (p s w) w (fun d => (x d.i, d.j))
      (fun d => if P d.i d.j then 1 else 0) (fun d => Wt d.i)) :
    Can m B s w x (fun i => Nat.count (P i) (T i)) (fun i => T i * (Wt i + 1) + 1) := by
  have hs : Can m (fun d : During T => B d.i) (p s (p w w)) w
      (fun d => (x d.i, d.j, Nat.count (P d.i) d.j)) (fun d => Nat.count (P d.i) (d.j + 1))
      (fun d => Wt d.i) := by
    have hacc : Knows m (fun d : During T => B d.i) (p s (p w w))
        (fun d => (x d.i, d.j, Nat.count (P d.i) d.j)) (fun d => Nat.count (P d.i) d.j) :=
      Can.snd Can.second
    have hI := (env_ix (t:=w) (v:=fun i j => Nat.count (P i) j)).pipe hind
    have hsm : Small (fun d : During T => B d.i) (fun d => Nat.count (P d.i) d.j) :=
      (hTs.reindex (fun d : During T => d.i)).mono (fun d => le_trans (count_le_self _) d.hj.le)
    refine ((hacc.mono (fun _ => Nat.zero_le _)).plus (hI.mono (fun _ => le_of_eq (by simp))) hsm
      (Small.const _ 1 |>.mono (fun d => by split <;> omega))).cong (fun _ => rfl) (fun d => ?_)
    rw [Nat.count_succ]
  have H := Can.loop (t:=w) (v:=fun i j => Nat.count (P i) j) (W':=fun _ => 0)
    (uB:=fun i _ => Wt i) hT (by simpa using (Can.wc (m:=m) (B:=B) (s:=s) (x:=x) (W:=fun _ => 0) 0)) hs hTs
  refine H.mono (fun i => ?_)
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
  change 0 + 0 + T i + T i * Wt i ≤ _
  nlinarith

/-- The state of the search loop for the `q`-th element. -/
def nthAcc (P : ℕ → Prop) [DecidablePred P] (q j : ℕ) : ℕ × ℕ :=
  (Nat.count P j, if q < Nat.count P j then Nat.nth P q else 0)

lemma nthAcc_succ (P : ℕ → Prop) [DecidablePred P] (q j : ℕ) :
    nthAcc P q (j+1) = ((nthAcc P q j).1 + (if P j then 1 else 0),
      if (if P j then 1 else 0) * (if (nthAcc P q j).1 = q then 1 else 0) = 0 then (nthAcc P q j).2 else j) := by
  unfold nthAcc
  rw [Nat.count_succ]
  by_cases hp : P j
  · by_cases hc : Nat.count P j = q
    · simp only [hp, if_true, hc, one_mul, one_ne_zero, if_false]
      refine Prod.ext rfl ?_
      simp only [lt_add_iff_pos_right, Nat.lt_one_iff, if_true, zero_lt_one]
      rw [← hc]; exact Nat.nth_count hp
    · simp only [hp, if_true, hc, if_false, mul_zero]
      refine Prod.ext rfl ?_
      have : q < Nat.count P j + 1 ↔ q < Nat.count P j := by omega
      simp only [this]
  · simp [hp]

/-- **Search loop**: the `q`-th element of a decidable set (`0` if there are fewer). -/
lemma can_nthc {P : ι → ℕ → Prop} [∀ i, DecidablePred (P i)] {T Wt q : ι → ℕ}
    (hT : Knows m B s x T) (hTs : Small B T) (hq : Knows m B s x q)
    (hind : Can m (fun d : During T => B d.i) (p s w) w (fun d => (x d.i, d.j))
      (fun d => if P d.i d.j then 1 else 0) (fun d => Wt d.i)) :
    Can m B s w x (fun i => if q i < Nat.count (P i) (T i) then Nat.nth (P i) (q i) else 0)
      (fun i => T i * (Wt i + 1) + 1) := by
  let v (i : ι) (j : ℕ) : ℕ × ℕ := nthAcc (P i) (q i) j
  have hsT : ∀ d : During T, Nat.count (P d.i) d.j ≤ T d.i := fun d => le_trans (count_le_self _) d.hj.le
  have hs : Can m (fun d : During T => B d.i) (p s (p w (p w w))) (p w w)
      (fun d => (x d.i, d.j, v d.i d.j)) (fun d => v d.i (d.j + 1)) (fun d => Wt d.i) := by
    let BD (d : During T) := B d.i
    have hc : Knows m BD (p s (p w (p w w))) (fun d => (x d.i, d.j, v d.i d.j)) (fun d => (v d.i d.j).1) :=
      Can.fst (Can.snd Can.second)
    have ha : Knows m BD (p s (p w (p w w))) (fun d => (x d.i, d.j, v d.i d.j)) (fun d => (v d.i d.j).2) :=
      Can.snd (Can.snd Can.second)
    have hj : Knows m BD (p s (p w (p w w))) (fun d => (x d.i, d.j, v d.i d.j)) (fun d => d.j) :=
      Can.fst Can.second
    have hqD : Knows m BD (p s (p w (p w w))) (fun d => (x d.i, d.j, v d.i d.j)) (fun d => q d.i) :=
      Can.first.then_do (hq.reindex (fun d : During T => d.i))
    have hI := (env_ix (t:=p w w) (v:=v)).pipe hind
    have hsm : Small BD (fun d => (v d.i d.j).1) := (hTs.reindex (fun d : During T => d.i)).mono hsT
    have hi1 : Small BD (fun d => if P d.i d.j then 1 else 0) :=
      (Small.const _ 1).mono (fun d => by split <;> omega)
    have hnew : Can m BD (p s (p w (p w w))) w (fun d => (x d.i, d.j, v d.i d.j))
        (fun d => (v d.i d.j).1 + (if P d.i d.j then 1 else 0)) (fun d => 0 + Wt d.i) :=
      (hc.mono (fun _ => Nat.zero_le _)).plus hI hsm hi1
    have heq : Knows m BD (p s (p w (p w w))) (fun d => (x d.i, d.j, v d.i d.j))
        (fun d => if (v d.i d.j).1 = q d.i then 1 else 0) :=
      ((Can.wc 1).wsub (hc.eqbit hqD) ((Small.const _ 1).mono (fun d => Nat.sub_le _ _))).cong (fun _ => rfl)
        (fun d => by split <;> simp_all)
    have hf : Can m BD (p s (p w (p w w))) w (fun d => (x d.i, d.j, v d.i d.j))
        (fun d => (if P d.i d.j then 1 else 0) * (if (v d.i d.j).1 = q d.i then 1 else 0))
        (fun d => 0 + Wt d.i) :=
      hI.times (heq.mono (fun _ => Nat.zero_le _)) hi1 ((Small.const _ 1).mono (fun d => by split <;> omega))
    have hans : Can m BD (p s (p w (p w w))) w (fun d => (x d.i, d.j, v d.i d.j))
        (fun d => if (if P d.i d.j then 1 else 0) * (if (v d.i d.j).1 = q d.i then 1 else 0) = 0
          then (v d.i d.j).2 else d.j) (fun d => 0 + Wt d.i) := by
      apply Can.testz hf
      · exact ((ha.mono (W':=fun d => 0 + Wt d.i) (fun _ => Nat.zero_le _)).reindex Subtype.val).cong
          (fun _ => rfl) (fun d => (if_pos d.2).symm)
      · refine Can.cong ((hj.mono (W':=fun d => 0 + Wt d.i) (fun _ => Nat.zero_le _)).reindex Subtype.val)
          (fun _ => rfl) (fun d => ?_)
        exact (if_neg d.2).symm
    refine ((hnew.pair hans).mono (fun _ => le_of_eq (by simp))).cong (fun _ => rfl) (fun d => ?_)
    exact (nthAcc_succ (P d.i) (q d.i) d.j).symm
  have hi : Can m B s (p w w) x (fun i => v i 0) (fun _ => 0) :=
    ((Can.wc 0).pair (Can.wc 0)).cong (fun _ => rfl) (fun i => by simp [v, nthAcc])
  have H := Can.loop (t:=p w w) (v:=v) (W':=fun _ => 0) (uB:=fun i _ => Wt i) hT hi hs hTs
  refine (Can.snd H).mono (fun i => ?_)
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
  change 0 + 0 + T i + T i * Wt i ≤ _
  nlinarith

/-- `W^h` for a variable exponent: one loop. -/
lemma can_powv (W : ℕ) (hW : 0 < W) {h : ι → ℕ} (hh : Knows m B s x h) (hhs : Small B h)
    (hsm : Small B (fun i => W^(h i))) :
    Can m B s w x (fun i => W^(h i)) (fun i => h i + 1) := by
  have hs : Can m (fun d : During h => B d.i) (p s (p w w)) w
      (fun d => (x d.i, d.j, W^d.j)) (fun d => W^(d.j + 1)) (fun _ => 0) := by
    have hp : Small (fun d : During h => B d.i) (fun d => W^d.j) :=
      (hsm.reindex (fun d : During h => d.i)).mono (fun d => Nat.pow_le_pow_right hW d.hj.le)
    exact ((Can.snd Can.second).times (Can.wc W) hp (Small.const _ W)).cong (fun _ => rfl)
      (fun d => by rw [pow_succ])
  have H := Can.loop (t:=w) (v:=fun _ j => W^j) (W':=fun _ => 0) (uB:=fun _ _ => 0) hh
    (by simpa using (Can.wc (m:=m) (B:=B) (s:=s) (x:=x) (W:=fun _ => 0) 1)) hs hhs
  refine H.mono (fun i => ?_)
  simp

end Loops

namespace Eng
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]
variable (E : Eng α ρ σ)
variable {ι : Type U} {m : Bool} {B : ι → ℕ} {s : Ty} {x : ι → T s}

lemma tq_le (a : ℕ) : E.tq a ≤ E.mx := by
  unfold tq; split_ifs
  · exact E.tr_le _
  · exact Nat.zero_le _

/-- The target rank of a position `a < W` (fixed finite case split over the live roles). -/
lemma knows_tq {a : ι → ℕ} (ha : Knows m B s x a) (hlt : ∀ i, a i < E.W) :
    Knows m B s x (fun i => E.tq (a i)) := by
  let qq (i : ι) : σ := E.Q.atFin ⟨a i, hlt i⟩
  apply Can.cases_code (q:=qq) E.Q (ha.cong (fun _ => rfl) (fun i => by simp [qq]))
  intro f
  refine (Can.wc (E.tr f)).cong (fun _ => rfl) (fun i => ?_)
  have h1 : E.tq (a i.1) = E.tr (qq i.1) := by simp [tq, hlt i.1, qq]
  rw [h1, i.2]

lemma stepC_iter_le (h : ℕ) (sv : ℕ) :
    ((stepC E.W E.tq)^[h] (1, sv)).1 ≤ E.mx^h ∧ ((stepC E.W E.tq)^[h] (1, sv)).2 ≤ sv := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [Function.iterate_succ_apply']
    simp only [stepC]
    refine ⟨?_, le_trans (Nat.div_le_self _ _) ih.2⟩
    rw [pow_succ]
    exact Nat.mul_le_mul ih.1 (E.tq_le _)

/-- **The column factor of a code** by `h` steps. -/
lemma can_colS {h sv : ι → ℕ} (hh : Knows m B s x h) (hhs : Small B h) (hsv : Knows m B s x sv)
    (hss : Small B sv) (hpow : Small B (fun i => E.mx^(h i))) :
    Can m B s w x (fun i => colS E.W E.tq (h i) (sv i)) (fun i => h i + 1) := by
  let v (i : ι) (j : ℕ) : ℕ × ℕ := (stepC E.W E.tq)^[j] (1, sv i)
  have hs : Can m (fun d : During h => B d.i) (p s (p w (p w w))) (p w w)
      (fun d => (x d.i, d.j, v d.i d.j)) (fun d => v d.i (d.j + 1)) (fun _ => 0) := by
    let BD (d : During h) := B d.i
    have h1 : Knows m BD (p s (p w (p w w))) (fun d => (x d.i, d.j, v d.i d.j)) (fun d => (v d.i d.j).1) :=
      Can.fst (Can.snd Can.second)
    have h2 : Knows m BD (p s (p w (p w w))) (fun d => (x d.i, d.j, v d.i d.j)) (fun d => (v d.i d.j).2) :=
      Can.snd (Can.snd Can.second)
    have hs2 : Small BD (fun d => (v d.i d.j).2) :=
      (hss.reindex (fun d : During h => d.i)).mono (fun d => (E.stepC_iter_le d.j (sv d.i)).2)
    have hs1 : Small BD (fun d => (v d.i d.j).1) :=
      (hpow.reindex (fun d : During h => d.i)).mono (fun d => le_trans (E.stepC_iter_le d.j (sv d.i)).1
        (Nat.pow_le_pow_right (lt_of_lt_of_le (by norm_num) E.three) d.hj.le))
    have hr : Knows m BD (p s (p w (p w w))) (fun d => (x d.i, d.j, v d.i d.j)) (fun d => (v d.i d.j).2 % E.W) :=
      h2.modW (Can.wc E.W) hs2
    have ht := E.knows_tq hr (fun d => Nat.mod_lt _ E.W_pos)
    refine (h1.times ht hs1 ((Small.const _ E.mx).mono (fun d => E.tq_le _))).pair (h2.dvdW (Can.wc E.W) hs2)
      |>.cong (fun _ => rfl) (fun d => ?_)
    simp only [v]
    rw [Function.iterate_succ_apply']
    rfl
  have hi : Can m B s (p w w) x (fun i => v i 0) (fun _ => 0) :=
    ((Can.wc 1).pair hsv).cong (fun _ => rfl) (fun i => by simp [v])
  have H := Can.loop (t:=p w w) (v:=v) (W':=fun _ => 0) (uB:=fun _ _ => 0) hh hi hs hhs
  refine (Can.fst H).mono (fun i => ?_)
  simp

end Eng

end
end PowerSaving.RAM
end OAI
