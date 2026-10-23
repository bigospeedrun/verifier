import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Algebra.Order.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# R1: the job-model flow of Theorem 1G (rl-prove), natural numbers only

rb-r12, 14 Oct 2026.  The dilated lockstep tree for a SEPARATED mixed rule (every paid rank below every
target rank), with `L = n`.

* `Rule`        : K target ranks `kr k` with `Wk k` arrays each; P paid rounds `rk j` in word order.
* `uh h a`      : Pascal weights on the points of height `h` (`u 0 = 1`, `u b = ∑_{b k ≥ 1} Wk k * u (b - e k)`).
* `pts n h ρ`   : the points of a class of height `h` and multiplier `ρ`: `∑ a = h`, `m * ρ * col a ≤ n`.
* `inMS / outMS / srcMS` : the jobs (as multisets of sizes) a class consumes, emits in round `j`, takes from the top.
* `exitsSub / srcBelow / unitsSub` : the same summed over a subtree, by recursion on the height.
* `srcT n / exT n / unitsT n / Nsrc n` : the whole tree (root of height `G n`, multiplier 1).

Lemmas: `balance` (Lemma B: a class's inputs = its parent's round-`j` outputs + its own sources),
`src_size` (Lemma C: sources lie in `(n/m, n]`), `exit_size`, `exit_lt` (Lemma D: exits are products of
`G+1` paid ranks, smaller than `n`), `sum_uh` (`∑ u = W^h`), `Nsrc_pos`, `card_srcT_le` (polynomial count).
The real-valued Phi facts (Lemma D's conservation, Lemma E) are in `Work.Mixed.Phi`.
-/

namespace OAI.PowerSaving.MX

open Finset

/-- A mixed rule with grouped paid blocks (Theorem 1G, rl-prove section 3), with the separation hypothesis. -/
structure Rule where
  K : ℕ
  kr : Fin K → ℕ
  Wk : Fin K → ℕ
  m : ℕ
  P : ℕ
  rk : Fin P → ℕ
  kmin : ℕ
  rmax : ℕ
  kmin_le : ∀ k, kmin ≤ kr k
  kr_le : ∀ k, kr k ≤ m
  rk_pos : ∀ j, 1 ≤ rk j
  rk_le : ∀ j, rk j ≤ rmax
  /-- hypothesis (S): every paid rank is below every target rank -/
  sep : rmax < kmin
  two_le_kmin : 2 ≤ kmin
  /-- the smallest target rank is attained by a target type that occurs -/
  kmin_att : ∃ k, kr k = kmin ∧ 1 ≤ Wk k

lemma mem_nsmul_single {c x s : ℕ} (hx : x ∈ c • ({s} : Multiset ℕ)) : x = s := by
  rcases Multiset.mem_nsmul.1 hx with ⟨_, h⟩
  simpa using h

namespace Rule

variable (R : Rule)

/-- points of the lattice `ℕ^K` -/
abbrev Pt := Fin R.K → ℕ

/-- column factor `c(a) = ∏ k, kr k ^ a k` -/
def col (a : R.Pt) : ℕ := ∏ k, R.kr k ^ a k

/-- unit vector -/
def e (k : Fin R.K) : R.Pt := Pi.single k 1

/-- total number of arrays of a unit -/
def W : ℕ := ∑ k, R.Wk k

/-- Pascal weights by height: `uh 0 = [a = 0]`, `uh (h+1) a = ∑_{a k ≥ 1} Wk k * uh h (a - e k)`. -/
def uh : ℕ → R.Pt → ℕ
  | 0, a => if a = 0 then 1 else 0
  | h + 1, a => ∑ k, if 1 ≤ a k then R.Wk k * uh h (a - R.e k) else 0

/-- the tree depth `G n = max {g ≤ n : m * kmin^g ≤ n}` -/
def G (n : ℕ) : ℕ := Nat.findGreatest (fun g => R.m * R.kmin ^ g ≤ n) n

/-- points of height `h`, multiplier `ρ` (the set `R(ρ)` of rl-prove, restricted to `|a| = h`) -/
def pts (n h ρ : ℕ) : Finset R.Pt :=
  (Finset.Nat.antidiagonalTuple R.K h).filter (fun b => R.m * ρ * R.col b ≤ n)

/-- what a class of height `h`, multiplier `ρ` consumes: at each point `b`, `uh h b * Wk k` jobs of size
`ρ * kr k * col b` -/
def inMS (n h ρ : ℕ) : Multiset ℕ :=
  ∑ b ∈ R.pts n h ρ, ∑ k, (R.uh h b * R.Wk k) • ({ρ * R.kr k * R.col b} : Multiset ℕ)

/-- what round `j` of a class emits: at each point `b`, `uh h b` jobs of size `ρ * rk j * col b` -/
def outMS (n h ρ : ℕ) (j : Fin R.P) : Multiset ℕ :=
  ∑ b ∈ R.pts n h ρ, R.uh h b • ({ρ * R.rk j * R.col b} : Multiset ℕ)

/-- sources of a (non-root) class whose parent has multiplier `ρp`: inputs whose producer point `b + e k`
lies outside the parent's region -/
def srcMS (n h ρ ρp : ℕ) : Multiset ℕ :=
  ∑ b ∈ R.pts n h ρ, ∑ k,
    if n < R.m * ρp * R.col (b + R.e k) then (R.uh h b * R.Wk k) • ({ρ * R.kr k * R.col b} : Multiset ℕ)
    else 0

/-- number of fluid units of a class -/
def unitsC (n h ρ : ℕ) : ℕ := ∑ b ∈ R.pts n h ρ, R.uh h b

/-- exits of a subtree (outputs of its leaf classes) -/
def exitsSub (n : ℕ) : ℕ → ℕ → Multiset ℕ
  | 0, ρ => ∑ j, R.outMS n 0 ρ j
  | h + 1, ρ => ∑ j, exitsSub n h (ρ * R.rk j)

/-- sources of the strict descendants of a class -/
def srcBelow (n : ℕ) : ℕ → ℕ → Multiset ℕ
  | 0, _ => 0
  | h + 1, ρ => ∑ j, (R.srcMS n h (ρ * R.rk j) ρ + srcBelow n h (ρ * R.rk j))

/-- fluid units of a subtree -/
def unitsSub (n : ℕ) : ℕ → ℕ → ℕ
  | 0, ρ => R.unitsC n 0 ρ
  | h + 1, ρ => R.unitsC n (h + 1) ρ + ∑ j, unitsSub n h (ρ * R.rk j)

/-- all sources of the tree for `n` (the root's inputs are all sources) -/
def srcT (n : ℕ) : Multiset ℕ := R.inMS n (R.G n) 1 + R.srcBelow n (R.G n) 1

/-- all exits of the tree for `n` -/
def exT (n : ℕ) : Multiset ℕ := R.exitsSub n (R.G n) 1

/-- all fluid units of the tree for `n` -/
def unitsT (n : ℕ) : ℕ := R.unitsSub n (R.G n) 1

/-- number of source vectors of one tree copy -/
def Nsrc (n : ℕ) : ℕ := Multiset.card (R.srcT n)

/-! ### basic facts -/

lemma e_apply (k k' : Fin R.K) : R.e k k' = if k' = k then 1 else 0 := by
  unfold e; rw [Pi.single_apply]

lemma sum_add_e (b : R.Pt) (k : Fin R.K) : ∑ i, (b + R.e k) i = ∑ i, b i + 1 := by
  simp only [Pi.add_apply, Finset.sum_add_distrib, e_apply, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

lemma col_add_e (b : R.Pt) (k : Fin R.K) : R.col (b + R.e k) = R.kr k * R.col b := by
  unfold col
  simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib, e_apply]
  rw [mul_comm]
  congr 1
  rw [Finset.prod_eq_single k]
  · simp
  · intro b _ hb; simp [hb]
  · simp

lemma sub_e_add_e (a : R.Pt) (k : Fin R.K) (h : 1 ≤ a k) : a - R.e k + R.e k = a := by
  funext i
  simp only [Pi.add_apply, Pi.sub_apply, e_apply]
  split_ifs with hi
  · subst hi; omega
  · omega

lemma add_e_sub_e (b : R.Pt) (k : Fin R.K) : b + R.e k - R.e k = b := by
  funext i
  simp only [Pi.add_apply, Pi.sub_apply, e_apply]
  omega

lemma add_e_apply_self (b : R.Pt) (k : Fin R.K) : 1 ≤ (b + R.e k) k := by
  simp [e_apply]

/-- The reindexing behind Lemma B: pairs `(b, k)` with `∑ b = h` correspond to pairs `(a, k)` with
`∑ a = h + 1`, `a k ≥ 1`, through `a = b + e k`. -/
lemma sum_shift {M : Type*} [AddCommMonoid M] (h : ℕ) (F : R.Pt → Fin R.K → M) :
    ∑ b ∈ Finset.Nat.antidiagonalTuple R.K h, ∑ k, F b k =
      ∑ a ∈ Finset.Nat.antidiagonalTuple R.K (h + 1), ∑ k, if 1 ≤ a k then F (a - R.e k) k else 0 := by
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.Nat.antidiagonalTuple R.K (h + 1))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun b => b + R.e k) (fun a => a - R.e k) ?_ ?_ ?_ ?_ ?_
  · intro b hb
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hb ⊢
    exact ⟨by rw [R.sum_add_e, hb], R.add_e_apply_self b k⟩
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at ha ⊢
    have h1 := R.sum_add_e (a - R.e k) k
    rw [R.sub_e_add_e a k ha.2, ha.1] at h1
    omega
  · intro b _; exact R.add_e_sub_e b k
  · intro a ha
    simp only [Finset.mem_filter] at ha
    exact R.sub_e_add_e a k ha.2
  · intro b _; rw [R.add_e_sub_e]

lemma rk_lt_kr (j : Fin R.P) (k : Fin R.K) : R.rk j < R.kr k :=
  lt_of_le_of_lt (R.rk_le j) (lt_of_lt_of_le R.sep (R.kmin_le k))

lemma two_le_m : 2 ≤ R.m := by
  obtain ⟨k, hk, _⟩ := R.kmin_att
  have := R.kr_le k; have := R.two_le_kmin; omega

lemma kmin_pos : 0 < R.kmin := by have := R.two_le_kmin; omega

lemma kr_pos (k : Fin R.K) : 0 < R.kr k := lt_of_lt_of_le R.kmin_pos (R.kmin_le k)

lemma col_pos (b : R.Pt) : 0 < R.col b := by
  unfold col; exact Finset.prod_pos (fun k _ => pow_pos (R.kr_pos k) _)

lemma pow_le_col (b : R.Pt) : R.kmin ^ (∑ i, b i) ≤ R.col b := by
  unfold col
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod' (fun k _ => Nat.pow_le_pow_left (R.kmin_le k) _)

lemma col_zero : R.col 0 = 1 := by simp [col]

lemma mem_T_zero {b : R.Pt} (hb : b ∈ Finset.Nat.antidiagonalTuple R.K 0) : b = 0 := by
  rw [Finset.Nat.antidiagonalTuple_zero_right, Finset.mem_singleton] at hb; exact hb

/-- `G n` is the largest `g` with `m * kmin^g ≤ n` (when `m ≤ n`). -/
lemma m_kmin_pow_G_le {n : ℕ} (hn : R.m ≤ n) : R.m * R.kmin ^ R.G n ≤ n :=
  Nat.findGreatest_spec (P := fun g => R.m * R.kmin ^ g ≤ n) (Nat.zero_le n) (by simpa using hn)

lemma lt_m_kmin_pow_G_succ (n : ℕ) : n < R.m * R.kmin ^ (R.G n + 1) := by
  by_cases hle : R.G n + 1 ≤ n
  · have := Nat.findGreatest_is_greatest (P := fun g => R.m * R.kmin ^ g ≤ n) (Nat.lt_succ_self _) hle
    exact Nat.lt_of_not_le this
  · have h1 : n < 2 ^ (R.G n + 1) := lt_of_lt_of_le (by omega : n < R.G n + 1) (Nat.lt_two_pow_self).le
    have h2 : 2 ^ (R.G n + 1) ≤ R.kmin ^ (R.G n + 1) := Nat.pow_le_pow_left R.two_le_kmin _
    have h3 : R.kmin ^ (R.G n + 1) ≤ R.m * R.kmin ^ (R.G n + 1) :=
      Nat.le_mul_of_pos_left _ (by have := R.two_le_m; omega)
    omega


/-! ### Lemma B: exact balance -/

/-- **Lemma B** (exact balance, rl-prove section 3). The inputs of the child class `ρp * rk j` of height `h`
are exactly the round-`j` outputs of its parent (height `h+1`, multiplier `ρp`) plus the child's sources. -/
theorem balance (n h ρp : ℕ) (j : Fin R.P) :
    R.inMS n h (ρp * R.rk j) = R.outMS n (h + 1) ρp j + R.srcMS n h (ρp * R.rk j) ρp := by
  set ρ := ρp * R.rk j with hρ
  -- split every input by whether its producer lies in the parent's region
  have hsplit : R.inMS n h ρ =
      (∑ b ∈ R.pts n h ρ, ∑ k, if n < R.m * ρp * R.col (b + R.e k) then 0
          else (R.uh h b * R.Wk k) • ({ρ * R.kr k * R.col b} : Multiset ℕ)) + R.srcMS n h ρ ρp := by
    unfold inMS srcMS
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    split_ifs <;> simp
  rw [hsplit, add_left_inj]
  -- move to sums over the whole antidiagonal and shift
  unfold outMS pts
  rw [Finset.sum_filter, Finset.sum_filter]
  have hL : (∑ b ∈ Finset.Nat.antidiagonalTuple R.K h, if R.m * ρ * R.col b ≤ n then
        ∑ k, (if n < R.m * ρp * R.col (b + R.e k) then 0
          else (R.uh h b * R.Wk k) • ({ρ * R.kr k * R.col b} : Multiset ℕ)) else 0) =
      ∑ b ∈ Finset.Nat.antidiagonalTuple R.K h, ∑ k,
        (if R.m * ρ * R.col b ≤ n ∧ ¬ n < R.m * ρp * R.col (b + R.e k) then
          (R.uh h b * R.Wk k) • ({ρ * R.kr k * R.col b} : Multiset ℕ) else 0) := by
    refine Finset.sum_congr rfl (fun b _ => ?_)
    split_ifs with h1
    · refine Finset.sum_congr rfl (fun k _ => ?_)
      split_ifs <;> simp_all
    · symm; refine Finset.sum_eq_zero (fun k _ => ?_)
      rw [if_neg]; tauto
  rw [hL, R.sum_shift h]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  -- the parent side: expand `uh (h+1) a` by Pascal's rule
  have hR : (if R.m * ρp * R.col a ≤ n then R.uh (h + 1) a • ({ρp * R.rk j * R.col a} : Multiset ℕ) else 0) =
      ∑ k, if 1 ≤ a k then (if R.m * ρp * R.col a ≤ n then
        (R.Wk k * R.uh h (a - R.e k)) • ({ρp * R.rk j * R.col a} : Multiset ℕ) else 0) else 0 := by
    split_ifs with h1
    · simp only [uh]
      rw [← Finset.sum_nsmul_assoc]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      split_ifs <;> simp
    · simp
  rw [hR]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases hak : 1 ≤ a k
  · rw [if_pos hak, if_pos hak]
    have hcol : R.col a = R.kr k * R.col (a - R.e k) := by
      conv_lhs => rw [← R.sub_e_add_e a k hak]
      exact R.col_add_e _ _
    rw [R.sub_e_add_e a k hak]
    have hiff : (R.m * ρ * R.col (a - R.e k) ≤ n ∧ ¬ n < R.m * ρp * R.col a) ↔ R.m * ρp * R.col a ≤ n := by
      constructor
      · rintro ⟨_, h2⟩; omega
      · intro h2
        refine ⟨?_, by omega⟩
        rw [hρ]
        have := R.rk_lt_kr j k
        calc R.m * (ρp * R.rk j) * R.col (a - R.e k) = R.m * ρp * (R.rk j * R.col (a - R.e k)) := by ring
          _ ≤ R.m * ρp * (R.kr k * R.col (a - R.e k)) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ this.le)
          _ = R.m * ρp * R.col a := by rw [hcol]
          _ ≤ n := h2
    by_cases hc : R.m * ρp * R.col a ≤ n
    · rw [if_pos (hiff.2 hc), if_pos hc, mul_comm (R.uh h _), hcol, hρ,
        show ρp * R.rk j * R.kr k * R.col (a - R.e k) = ρp * R.rk j * (R.kr k * R.col (a - R.e k)) by ring]
    · rw [if_neg (fun h' => hc (hiff.1 h')), if_neg hc]
  · rw [if_neg hak, if_neg hak]

/-! ### Lemma C: sources lie in `(n/m, n]` -/

lemma mem_srcMS {n h ρp : ℕ} {j : Fin R.P} {x : ℕ} (hx : x ∈ R.srcMS n h (ρp * R.rk j) ρp) :
    n < R.m * x ∧ x ≤ n := by
  unfold srcMS at hx
  obtain ⟨b, hb, hx⟩ := Multiset.mem_sum.1 hx
  obtain ⟨k, -, hx⟩ := Multiset.mem_sum.1 hx
  simp only [pts, Finset.mem_filter] at hb
  split_ifs at hx with hc
  · have hx := mem_nsmul_single hx
    subst hx
    rw [R.col_add_e] at hc
    have h1 := R.rk_pos j
    have h2 := R.kr_le k
    constructor
    · calc n < R.m * ρp * (R.kr k * R.col b) := hc
        _ = 1 * (R.m * (ρp * R.kr k * R.col b)) := by ring
        _ ≤ R.rk j * (R.m * (ρp * R.kr k * R.col b)) := Nat.mul_le_mul_right _ h1
        _ = R.m * (ρp * R.rk j * R.kr k * R.col b) := by ring
    · calc ρp * R.rk j * R.kr k * R.col b ≤ ρp * R.rk j * R.m * R.col b :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h2)
        _ = R.m * (ρp * R.rk j) * R.col b := by ring
        _ ≤ n := hb.2
  · simp at hx

lemma mem_srcBelow {n h ρ x : ℕ} (hx : x ∈ R.srcBelow n h ρ) : n < R.m * x ∧ x ≤ n := by
  induction h generalizing ρ with
  | zero => simp [srcBelow] at hx
  | succ h ih =>
    simp only [srcBelow] at hx
    obtain ⟨j, -, hx⟩ := Multiset.mem_sum.1 hx
    rcases Multiset.mem_add.1 hx with hx | hx
    · exact R.mem_srcMS hx
    · exact ih hx

lemma mem_inMS_root {n x : ℕ} (hx : x ∈ R.inMS n (R.G n) 1) : n < R.m * x ∧ x ≤ n := by
  unfold inMS at hx
  obtain ⟨b, hb, hx⟩ := Multiset.mem_sum.1 hx
  obtain ⟨k, -, hx⟩ := Multiset.mem_sum.1 hx
  have hx := mem_nsmul_single hx
  subst hx
  simp only [pts, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hb
  constructor
  · have h1 := R.lt_m_kmin_pow_G_succ n
    have h2 := R.pow_le_col (b + R.e k)
    rw [R.sum_add_e, hb.1, R.col_add_e] at h2
    calc n < R.m * R.kmin ^ (R.G n + 1) := h1
      _ ≤ R.m * (R.kr k * R.col b) := Nat.mul_le_mul_left _ h2
      _ = R.m * (1 * R.kr k * R.col b) := by ring
  · have h2 := R.kr_le k
    calc 1 * R.kr k * R.col b ≤ R.m * R.col b := by rw [one_mul]; exact Nat.mul_le_mul_right _ h2
      _ = R.m * 1 * R.col b := by ring
      _ ≤ n := hb.2

/-- **Lemma C**: every source of the tree for `n` has size in `(n/m, n]`. -/
theorem src_size {n x : ℕ} (hx : x ∈ R.srcT n) : n < R.m * x ∧ x ≤ n := by
  rcases Multiset.mem_add.1 hx with hx | hx
  · exact R.mem_inMS_root hx
  · exact R.mem_srcBelow hx

lemma src_pos {n x : ℕ} (hx : x ∈ R.srcT n) : 1 ≤ x := by
  have := (R.src_size hx).1
  rcases Nat.eq_zero_or_pos x with h | h
  · subst h; simp at this
  · exact h

/-! ### Lemma D (sizes): exits are products of `G + 1` paid ranks, below `n` -/

lemma mem_exitsSub {n h ρ x : ℕ} (hx : x ∈ R.exitsSub n h ρ) :
    ∃ ρ' : ℕ, ∃ j : Fin R.P, x = ρ' * R.rk j ∧ R.m * ρ' ≤ n ∧ ρ ≤ ρ' ∧ ρ' ≤ ρ * R.rmax ^ h := by
  induction h generalizing ρ with
  | zero =>
    simp only [exitsSub] at hx
    obtain ⟨j, -, hx⟩ := Multiset.mem_sum.1 hx
    unfold outMS at hx
    obtain ⟨b, hb, hx⟩ := Multiset.mem_sum.1 hx
    have hx := mem_nsmul_single hx
    simp only [pts, Finset.mem_filter] at hb
    have hb0 := R.mem_T_zero hb.1
    subst hb0
    rw [R.col_zero] at hx hb
    exact ⟨ρ, j, by rw [hx]; ring, by simpa using hb.2, le_rfl, by simp⟩
  | succ h ih =>
    simp only [exitsSub] at hx
    obtain ⟨j, -, hx⟩ := Multiset.mem_sum.1 hx
    obtain ⟨ρ', j', h1, h2, h3, h4⟩ := ih hx
    refine ⟨ρ', j', h1, h2, ?_, ?_⟩
    · exact le_trans (Nat.le_mul_of_pos_right _ (R.rk_pos j)) h3
    · calc ρ' ≤ ρ * R.rk j * R.rmax ^ h := h4
        _ ≤ ρ * R.rmax * R.rmax ^ h := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (R.rk_le j))
        _ = ρ * R.rmax ^ (h + 1) := by ring

/-- **Lemma D (sizes)**: every exit of the tree for `n` is at least 1, at most `rmax^(G n + 1)`, and below `n`. -/
theorem exit_size {n x : ℕ} (hx : x ∈ R.exT n) : 1 ≤ x ∧ x ≤ R.rmax ^ (R.G n + 1) ∧ x < n := by
  obtain ⟨ρ', j, rfl, h2, h3, h4⟩ := R.mem_exitsSub hx
  have hr := R.rk_pos j
  refine ⟨Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), ?_, ?_⟩
  · calc ρ' * R.rk j ≤ (1 * R.rmax ^ R.G n) * R.rmax := Nat.mul_le_mul h4 (R.rk_le j)
      _ = R.rmax ^ (R.G n + 1) := by ring
  · have h5 : R.rk j < R.m := lt_of_lt_of_le (R.rk_lt_kr j (R.kmin_att.choose)) (R.kr_le _)
    calc ρ' * R.rk j < ρ' * R.m := Nat.mul_lt_mul_of_pos_left h5 (by omega)
      _ = R.m * ρ' := by ring
      _ ≤ n := h2

/-! ### counts -/

lemma uh_single (k : Fin R.K) (h : ℕ) (hW : 1 ≤ R.Wk k) : 1 ≤ R.uh h (Pi.single k h) := by
  induction h with
  | zero => simp [uh]
  | succ h ih =>
    simp only [uh]
    have hk : 1 ≤ (Pi.single k (h + 1) : R.Pt) k := by simp
    have hsub : (Pi.single k (h + 1) : R.Pt) - R.e k = Pi.single k h := by
      funext i; simp only [Pi.sub_apply, e_apply, Pi.single_apply]; split_ifs <;> omega
    calc 1 ≤ R.Wk k * R.uh h (Pi.single k h) := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
      _ = (fun k' => if 1 ≤ (Pi.single k (h + 1) : R.Pt) k' then
            R.Wk k' * R.uh h ((Pi.single k (h + 1) : R.Pt) - R.e k') else 0) k := by
          simp only [if_pos hk, hsub]
      _ ≤ ∑ k', (if 1 ≤ (Pi.single k (h + 1) : R.Pt) k' then
            R.Wk k' * R.uh h ((Pi.single k (h + 1) : R.Pt) - R.e k') else 0) :=
          Finset.single_le_sum (f := fun k' => if 1 ≤ (Pi.single k (h + 1) : R.Pt) k' then
            R.Wk k' * R.uh h ((Pi.single k (h + 1) : R.Pt) - R.e k') else 0)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)

lemma card_inMS (n h ρ : ℕ) :
    Multiset.card (R.inMS n h ρ) = ∑ b ∈ R.pts n h ρ, ∑ k, R.uh h b * R.Wk k := by
  simp [inMS, Multiset.card_sum, Multiset.card_nsmul]

/-- the tree for `n ≥ m` has at least one source -/
theorem Nsrc_pos {n : ℕ} (hn : R.m ≤ n) : 1 ≤ R.Nsrc n := by
  obtain ⟨k, hk, hW⟩ := R.kmin_att
  obtain ⟨b, hbdef⟩ : ∃ b : R.Pt, b = Pi.single k (R.G n) := ⟨_, rfl⟩
  have hub : 1 ≤ R.uh (R.G n) b := by rw [hbdef]; exact R.uh_single k (R.G n) hW
  have hbT : b ∈ R.pts n (R.G n) 1 := by
    simp only [pts, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple]
    refine ⟨by simp [hbdef], ?_⟩
    have : R.col b = R.kmin ^ R.G n := by
      simp only [col, hbdef, Pi.single_apply]
      rw [Finset.prod_eq_single k]
      · simp [hk]
      · intro i _ hi; simp [hi]
      · simp
    rw [this, mul_one]; exact R.m_kmin_pow_G_le hn
  have h1 : 1 ≤ R.uh (R.G n) b * R.Wk k := Nat.one_le_iff_ne_zero.2
    (Nat.mul_ne_zero (by omega) (by omega))
  have h2 : R.uh (R.G n) b * R.Wk k ≤ ∑ k', R.uh (R.G n) b * R.Wk k' :=
    Finset.single_le_sum (f := fun k' => R.uh (R.G n) b * R.Wk k') (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  have h3 : ∑ k', R.uh (R.G n) b * R.Wk k' ≤ ∑ b' ∈ R.pts n (R.G n) 1, ∑ k', R.uh (R.G n) b' * R.Wk k' :=
    Finset.single_le_sum (f := fun b' => ∑ k', R.uh (R.G n) b' * R.Wk k') (fun _ _ => Nat.zero_le _) hbT
  unfold Nsrc srcT
  rw [Multiset.card_add, card_inMS]
  omega

/-- the multinomial theorem in Pascal form: `∑_{|b| = h} u b = W^h` -/
theorem sum_uh (h : ℕ) : ∑ b ∈ Finset.Nat.antidiagonalTuple R.K h, R.uh h b = R.W ^ h := by
  induction h with
  | zero =>
    rw [Finset.Nat.antidiagonalTuple_zero_right]; simp [uh]
  | succ h ih =>
    have := R.sum_shift h (fun b k => R.Wk k * R.uh h b)
    simp only [uh]
    rw [← this]
    simp_rw [← Finset.sum_mul]
    rw [← Finset.mul_sum, ih]; unfold W; ring

lemma card_inMS_le (n h ρ : ℕ) : Multiset.card (R.inMS n h ρ) ≤ R.W ^ (h + 1) := by
  rw [card_inMS]
  calc ∑ b ∈ R.pts n h ρ, ∑ k, R.uh h b * R.Wk k
      = ∑ b ∈ R.pts n h ρ, R.uh h b * R.W := by simp_rw [← Finset.mul_sum]; rfl
    _ ≤ ∑ b ∈ Finset.Nat.antidiagonalTuple R.K h, R.uh h b * R.W :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => Nat.zero_le _)
    _ = R.W ^ (h + 1) := by rw [← Finset.sum_mul, sum_uh, pow_succ]

lemma card_srcMS_le (n h ρ ρp : ℕ) : Multiset.card (R.srcMS n h ρ ρp) ≤ Multiset.card (R.inMS n h ρ) := by
  unfold srcMS inMS
  simp only [Multiset.card_sum]
  refine Finset.sum_le_sum (fun b _ => Finset.sum_le_sum (fun k _ => ?_))
  split_ifs <;> simp

lemma card_sub_le (n h ρ : ℕ) :
    Multiset.card (R.inMS n h ρ) + Multiset.card (R.srcBelow n h ρ) ≤ (R.P + R.W + 1) ^ (h + 1) := by
  induction h generalizing ρ with
  | zero =>
    simp only [srcBelow, Multiset.card_zero, add_zero, zero_add, pow_one]
    have := R.card_inMS_le n 0 ρ
    simp at this; omega
  | succ h ih =>
    have h1 := R.card_inMS_le n (h + 1) ρ
    have h2 : Multiset.card (R.srcBelow n (h + 1) ρ) ≤ R.P * (R.P + R.W + 1) ^ (h + 1) := by
      simp only [srcBelow, Multiset.card_sum, Multiset.card_add]
      calc ∑ j, (Multiset.card (R.srcMS n h (ρ * R.rk j) ρ) + Multiset.card (R.srcBelow n h (ρ * R.rk j)))
          ≤ ∑ _j : Fin R.P, (R.P + R.W + 1) ^ (h + 1) := Finset.sum_le_sum (fun j _ =>
            le_trans (Nat.add_le_add_right (R.card_srcMS_le n h _ ρ) _) (ih _))
        _ = R.P * (R.P + R.W + 1) ^ (h + 1) := by simp
    have h3 : R.W ^ (h + 1 + 1) ≤ R.W * (R.P + R.W + 1) ^ (h + 1) := by
      rw [pow_succ', ]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    calc Multiset.card (R.inMS n (h + 1) ρ) + Multiset.card (R.srcBelow n (h + 1) ρ)
        ≤ R.W * (R.P + R.W + 1) ^ (h + 1) + R.P * (R.P + R.W + 1) ^ (h + 1) := by omega
      _ ≤ (R.P + R.W + 1) * (R.P + R.W + 1) ^ (h + 1) := by
          rw [← add_mul]; exact Nat.mul_le_mul_right _ (by omega)
      _ = (R.P + R.W + 1) ^ (h + 1 + 1) := by ring

/-- the number of sources is polynomial in `n`: at most `(P + W + 1)^(G n + 1)` -/
theorem Nsrc_le (n : ℕ) : R.Nsrc n ≤ (R.P + R.W + 1) ^ (R.G n + 1) := by
  unfold Nsrc srcT; rw [Multiset.card_add]; exact R.card_sub_le n (R.G n) 1

end Rule

end OAI.PowerSaving.MX
