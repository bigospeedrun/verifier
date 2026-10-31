import Submission.Work.Mixed.Flow

/-!
# Mixed engine, cost part 2: the bill of the lockstep engine (R3 cost against R1/R2)

(agent e-r3cost, round wht45/lever, 19 Oct 2026; resumes rb-r3cost of 14 Oct.)

The RAM program of the mixed engine (Theorem 1G realised as in lg-g2/DESIGN.md section 4) makes
calls of two shapes:

* `Shape.top n B`   `Do(n, B)`: `B` vectors of `2^n` entries, the kernel on all `n` bits of each;
* `Shape.cls n h ρ` `Process`: one class of the tree for `n`, of height `h` and multiplier `ρ`.

`kidsS` lists the calls a body makes (with multiplicity) and `locS` its local work up to a constant:

* `top n B`, `n0 ≤ n`, `Nsrc n ≤ B`: `λ = B / Nsrc n` root-class calls (one per tree copy), then
  ONE rest call `top (n - s) (2^s)` per copy and source of size `s` (its `s` finished bits become
  batch); the `B % Nsrc n` leftover vectors are done naively.  Otherwise (small `n`, or fewer than `Nsrc n` vectors) the
  whole job is naive and makes no call.
* `cls n (h+1) ρ`: one child-class call `cls n h (ρ * rk j)` per paid round `j` (word order);
* `cls n 0 ρ` (leaf): one exit call `top (ρ * rk j) (2^(n - ρ * rk j))` per paid round `j`.

The cost function `costS` (exact: the recursion closer `recurse_inv` of `Work.MixedCost.Close`
absorbs every constant factor of the local work) is

* `topCost n B = B * J n + LftS n B + (n+1)*2^n + 1`,
* `clsCost`: local work + 1 + the children, by recursion on the height,

and `bill` proves `locS d + 1 + ∑ (kidsS d) costS ≤ costS d` on every reachable shape, for ANY
per-vector cost `J` obeying the job recurrence `JobRec` (`treeCost J n + Rnd n ≤ Nsrc n * J n`).
`allotM` is the least such `J` (well-founded), with the matching upper recurrence for R2.
-/

set_option linter.unusedSectionVars false

namespace OAI.PowerSaving.MX

open Finset

/-- The shapes of the calls of the mixed engine. -/
inductive Shape where
  /-- `Do(n, B)`: `B` vectors of `2^n` entries, the kernel on all `n` bits of each. -/
  | top (n B : ℕ)
  /-- `Process`: a class of the tree for `n`, of height `h` and multiplier `ρ`. -/
  | cls (n h ρ : ℕ)
  deriving DecidableEq

/-- A rank that every call lowers. -/
def Shape.rank : Shape → ℕ
  | .top n _ => (n + 1) * (n + 2)
  | .cls n h _ => (n + 1) * (n + 1) + h

/-- Natural-number Phi of a multiset of sizes, as an additive monoid map. -/
def PhiN (g : ℕ → ℕ) : Multiset ℕ →+ ℕ where
  toFun s := (s.map g).sum
  map_zero' := by simp
  map_add' := by intro a b; simp

@[simp] lemma PhiN_apply (g : ℕ → ℕ) (s : Multiset ℕ) : PhiN g s = (s.map g).sum := rfl

lemma PhiN_mono {g g' : ℕ → ℕ} (s : Multiset ℕ) (h : ∀ x ∈ s, g x ≤ g' x) : PhiN g s ≤ PhiN g' s := by
  simp only [PhiN_apply]; exact Multiset.sum_map_le_sum_map _ _ h

namespace Rule

variable (R : Rule)

/-! ## 1. The shapes, their calls, their local work -/

/-- Invariant of the reachable shapes: every class is non-empty. -/
def InvS : Shape → Prop
  | .top _ _ => True
  | .cls n h ρ => 1 ≤ ρ ∧ R.m * ρ * R.kmin ^ h ≤ n

/-- The rest calls of a top job with `lam` tree copies: one per copy and source, on the `2^s` vectors
of `2^(n-s)` entries that a source of size `s` leaves (its `s` finished bits become batch). -/
def restMS (n lam : ℕ) : Multiset Shape :=
  lam • (R.srcT n).map (fun s => Shape.top (n - s) (2 ^ s))

/-- The calls made by the body on a shape, with multiplicity. -/
def kidsS (n0 : ℕ) : Shape → Multiset Shape
  | .top n B =>
      if n0 ≤ n ∧ R.Nsrc n ≤ B then
        Multiset.replicate (B / R.Nsrc n) (Shape.cls n (R.G n) 1) + R.restMS n (B / R.Nsrc n)
      else 0
  | .cls n (h + 1) ρ => Finset.univ.val.map (fun j : Fin R.P => Shape.cls n h (ρ * R.rk j))
  | .cls n 0 ρ =>
      Finset.univ.val.map (fun j : Fin R.P => Shape.top (ρ * R.rk j) (2 ^ (n - ρ * R.rk j)))

/-- The local work of the body on a shape (up to a constant factor):
* top, `n0 ≤ n`: one pass over the `B` vectors (re-layout of the tree copies' sources and of the
  rests, loop control), plus the naive transform of the `B % Nsrc n` leftover vectors;
* top, `n < n0`: the naive transform of all `B` vectors;
* class: one sweep of every letter over the class table (`unitsC` fluid units of `2^n` entries per
  role), plus the subtree sources it passes down (`card srcBelow` vectors of `2^n` entries). -/
def locS (n0 : ℕ) : Shape → ℕ
  | .top n B =>
      if n0 ≤ n then (B + 1) * 2 ^ n + (B % R.Nsrc n) * (n + 1) * 2 ^ n
      else (B + 1) * (n + 1) * 2 ^ n
  | .cls n h ρ => 2 ^ n * (R.unitsC n h ρ + Multiset.card (R.srcBelow n h ρ))

/-! ## 2. The cost function -/

/-- The naive leftover of a top job. -/
def LftS (n0 n B : ℕ) : ℕ := if n0 ≤ n then (B % R.Nsrc n) * (n + 1) * 2 ^ n else 0

/-- The cost of a top job `Do(n, B)`, for a per-vector cost `J`. -/
def topCost (n0 : ℕ) (J : ℕ → ℕ) (n B : ℕ) : ℕ :=
  B * J n + R.LftS n0 n B + (n + 1) * 2 ^ n + 1

/-- The cost of a class (exactly its local work, one unit, and its calls). -/
def clsCost (n0 : ℕ) (J : ℕ → ℕ) (n : ℕ) : ℕ → ℕ → ℕ
  | 0, ρ => 2 ^ n * R.unitsC n 0 ρ + 1 +
      ∑ j : Fin R.P, R.topCost n0 J (ρ * R.rk j) (2 ^ (n - ρ * R.rk j))
  | h + 1, ρ => 2 ^ n * (R.unitsC n (h + 1) ρ + Multiset.card (R.srcBelow n (h + 1) ρ)) + 1 +
      ∑ j : Fin R.P, clsCost n0 J n h (ρ * R.rk j)

/-- The cost of a shape. -/
def costS (n0 : ℕ) (J : ℕ → ℕ) : Shape → ℕ
  | .top n B => R.topCost n0 J n B
  | .cls n h ρ => R.clsCost n0 J n h ρ

/-! ## 3. The job recurrence (what R2 sees) -/

/-- What an exit `e` of the tree for `n` costs per tree copy, beyond the internal work. -/
def exF (J : ℕ → ℕ) (n e : ℕ) : ℕ := 2 ^ (n - e) * J e + (R.Nsrc e + 1) * (e + 1) * 2 ^ e + 1

/-- What a source `s` of the tree for `n` costs per tree copy in its rest call. -/
def srF (J : ℕ → ℕ) (n s : ℕ) : ℕ :=
  2 ^ s * J (n - s) + (R.Nsrc (n - s) + 1) * (n - s + 1) * 2 ^ (n - s) + 1

/-- One tree copy on `Nsrc n` vectors: sweeps and source copies, exits, rests. -/
def treeCost (J : ℕ → ℕ) (n : ℕ) : ℕ :=
  (2 * R.unitsT n + R.Nsrc n * (R.G n + 1)) * 2 ^ n
    + ((R.exT n).map (fun e => 2 ^ (n - e) * J e)).sum
    + ((R.srcT n).map (fun s => 2 ^ s * J (n - s))).sum

/-- Leftovers (naive vectors of the exit and rest calls) and one unit per call. -/
def Rnd (n : ℕ) : ℕ :=
  ((R.exT n).map (fun e => (R.Nsrc e + 1) * (e + 1) * 2 ^ e + 1)).sum
    + ((R.srcT n).map (fun s => (R.Nsrc (n - s) + 1) * (n - s + 1) * 2 ^ (n - s) + 1)).sum

/-- **The job recurrence**: a per-vector cost `J` pays for the naive transform below `n0` and for
one tree copy plus its leftovers above. -/
def JobRec (n0 : ℕ) (J : ℕ → ℕ) : Prop :=
  (∀ n, n < n0 → (n + 1) * 2 ^ n ≤ J n) ∧
    ∀ n, n0 ≤ n → R.treeCost J n + R.Rnd n ≤ R.Nsrc n * J n

lemma treeCost_add_Rnd (J : ℕ → ℕ) (n : ℕ) :
    R.treeCost J n + R.Rnd n =
      R.Nsrc n * 2 ^ n + (2 ^ n * (2 * R.unitsT n + R.G n * R.Nsrc n)
        + PhiN (R.exF J n) (R.exT n) + PhiN (R.srF J n) (R.srcT n)) := by
  unfold treeCost Rnd exF srF
  simp only [PhiN_apply, Multiset.sum_map_add]
  ring

/-! ## 4. Facts about the tree used by the bill -/

lemma card_srcBelow_zero (n ρ : ℕ) : Multiset.card (R.srcBelow n 0 ρ) = 0 := by
  simp [srcBelow]

lemma pts_zero {n ρ : ℕ} (hρ : R.m * ρ ≤ n) : R.pts n 0 ρ = {0} := by
  unfold pts
  rw [Finset.Nat.antidiagonalTuple_zero_right, Finset.filter_singleton, if_pos]
  rw [R.col_zero, mul_one]; exact hρ

lemma unitsC_zero {n ρ : ℕ} (hρ : R.m * ρ ≤ n) : R.unitsC n 0 ρ = 1 := by
  unfold unitsC; rw [R.pts_zero hρ, Finset.sum_singleton]; simp [uh]

lemma outMS_zero {n ρ : ℕ} (hρ : R.m * ρ ≤ n) (j : Fin R.P) : R.outMS n 0 ρ j = {ρ * R.rk j} := by
  unfold outMS; rw [R.pts_zero hρ, Finset.sum_singleton]; simp [uh, R.col_zero, one_nsmul]

lemma PhiN_exitsSub_zero {n ρ : ℕ} (hρ : R.m * ρ ≤ n) (g : ℕ → ℕ) :
    PhiN g (R.exitsSub n 0 ρ) = ∑ j : Fin R.P, g (ρ * R.rk j) := by
  simp only [exitsSub, map_sum, R.outMS_zero hρ]
  simp

lemma PhiN_exitsSub_succ (n h ρ : ℕ) (g : ℕ → ℕ) :
    PhiN g (R.exitsSub n (h + 1) ρ) = ∑ j : Fin R.P, PhiN g (R.exitsSub n h (ρ * R.rk j)) := by
  simp only [exitsSub, map_sum]

lemma card_srcBelow_succ (n h ρ : ℕ) :
    ∑ j : Fin R.P, Multiset.card (R.srcBelow n h (ρ * R.rk j)) ≤
      Multiset.card (R.srcBelow n (h + 1) ρ) := by
  simp only [srcBelow, Multiset.card_sum, Multiset.card_add]
  exact Finset.sum_le_sum (fun j _ => Nat.le_add_left _ _)

/-- Every class satisfying the invariant has a fluid unit. -/
lemma unitsC_pos {n h ρ : ℕ} (hinv : R.m * ρ * R.kmin ^ h ≤ n) : 1 ≤ R.unitsC n h ρ := by
  obtain ⟨k, hk, hW⟩ := R.kmin_att
  obtain ⟨b, hbdef⟩ : ∃ b : R.Pt, b = Pi.single k h := ⟨_, rfl⟩
  have hub : 1 ≤ R.uh h b := by rw [hbdef]; exact R.uh_single k h hW
  have hcol : R.col b = R.kmin ^ h := by
    simp only [col, hbdef, Pi.single_apply]
    rw [Finset.prod_eq_single k]
    · simp [hk]
    · intro i _ hi; simp [hi]
    · simp
  have hb : b ∈ R.pts n h ρ := by
    simp only [pts, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple]
    exact ⟨by simp [hbdef], by rw [hcol]; exact hinv⟩
  unfold unitsC
  exact le_trans hub (Finset.single_le_sum (f := fun b => R.uh h b) (fun _ _ => Nat.zero_le _) hb)

lemma rk_le_kmin (j : Fin R.P) : R.rk j ≤ R.kmin := le_trans (R.rk_le j) R.sep.le

lemma rk_lt_m (j : Fin R.P) : R.rk j < R.m := by
  obtain ⟨k, -, -⟩ := R.kmin_att
  exact lt_of_lt_of_le (R.rk_lt_kr j k) (R.kr_le k)

/-- The invariant passes to the child classes. -/
lemma inv_child {n h ρ : ℕ} (j : Fin R.P) (hinv : R.m * ρ * R.kmin ^ (h + 1) ≤ n) :
    R.m * (ρ * R.rk j) * R.kmin ^ h ≤ n := by
  calc R.m * (ρ * R.rk j) * R.kmin ^ h = R.m * ρ * (R.rk j * R.kmin ^ h) := by ring
    _ ≤ R.m * ρ * (R.kmin * R.kmin ^ h) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (R.rk_le_kmin j))
    _ = R.m * ρ * R.kmin ^ (h + 1) := by ring
    _ ≤ n := hinv

lemma Nsrc_pos_of {n0 n : ℕ} (hn0 : R.m ≤ n0) (h : n0 ≤ n) : 1 ≤ R.Nsrc n :=
  R.Nsrc_pos (le_trans hn0 h)

lemma LftS_le {n0 : ℕ} (hn0 : R.m ≤ n0) (n B : ℕ) : R.LftS n0 n B ≤ R.Nsrc n * (n + 1) * 2 ^ n := by
  unfold LftS
  split_ifs with h
  · have hN := R.Nsrc_pos_of hn0 h
    have : B % R.Nsrc n ≤ R.Nsrc n := (Nat.mod_lt _ (by omega)).le
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ this)
  · exact Nat.zero_le _

lemma topCost_exit_le {n0 : ℕ} (hn0 : R.m ≤ n0) (J : ℕ → ℕ) (n e : ℕ) :
    R.topCost n0 J e (2 ^ (n - e)) ≤ R.exF J n e := by
  unfold topCost exF
  have := R.LftS_le hn0 e (2 ^ (n - e))
  nlinarith

/-! ## 5. The class bill, summed over a subtree -/

/-- **A class costs at most** `2^n * (2 * units + h * subtree sources)` plus its exits. -/
theorem clsCost_le {n0 : ℕ} (hn0 : R.m ≤ n0) (J : ℕ → ℕ) (n : ℕ) :
    ∀ h ρ, R.m * ρ * R.kmin ^ h ≤ n →
      R.clsCost n0 J n h ρ ≤ 2 ^ n * (2 * R.unitsSub n h ρ + h * Multiset.card (R.srcBelow n h ρ))
        + PhiN (R.exF J n) (R.exitsSub n h ρ) := by
  intro h
  induction h with
  | zero =>
    intro ρ hinv
    have hρ : R.m * ρ ≤ n := by simpa using hinv
    simp only [clsCost, unitsSub, R.unitsC_zero hρ, R.PhiN_exitsSub_zero hρ, R.card_srcBelow_zero,
      zero_mul, add_zero]
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have h2 : ∑ j : Fin R.P, R.topCost n0 J (ρ * R.rk j) (2 ^ (n - ρ * R.rk j)) ≤
        ∑ j : Fin R.P, R.exF J n (ρ * R.rk j) :=
      Finset.sum_le_sum (fun j _ => R.topCost_exit_le hn0 J n _)
    omega
  | succ h ih =>
    intro ρ hinv
    simp only [clsCost, unitsSub, R.PhiN_exitsSub_succ]
    have hU := R.unitsC_pos hinv
    have hk : ∀ j : Fin R.P, R.clsCost n0 J n h (ρ * R.rk j) ≤
        2 ^ n * (2 * R.unitsSub n h (ρ * R.rk j) + h * Multiset.card (R.srcBelow n h (ρ * R.rk j)))
          + PhiN (R.exF J n) (R.exitsSub n h (ρ * R.rk j)) :=
      fun j => ih (ρ * R.rk j) (R.inv_child j hinv)
    have hsum := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin R.P))) => hk j)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum] at hsum
    have hc := R.card_srcBelow_succ n h ρ
    have hc' : h * ∑ j : Fin R.P, Multiset.card (R.srcBelow n h (ρ * R.rk j)) ≤
        h * Multiset.card (R.srcBelow n (h + 1) ρ) := Nat.mul_le_mul_left _ hc
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have h2 : 2 ^ n * 1 ≤ 2 ^ n * R.unitsC n (h + 1) ρ := Nat.mul_le_mul_left _ hU
    have h3 : 2 ^ n * (h * ∑ j : Fin R.P, Multiset.card (R.srcBelow n h (ρ * R.rk j))) ≤
        2 ^ n * (h * Multiset.card (R.srcBelow n (h + 1) ρ)) := Nat.mul_le_mul_left _ hc'
    nlinarith

/-- The root class of the tree for `n` (`n ≥ m`). -/
theorem rootCost_le {n0 : ℕ} (hn0 : R.m ≤ n0) (J : ℕ → ℕ) {n : ℕ} (hn : R.m ≤ n) :
    R.clsCost n0 J n (R.G n) 1 ≤ 2 ^ n * (2 * R.unitsT n + R.G n * R.Nsrc n)
      + PhiN (R.exF J n) (R.exT n) := by
  have h := R.clsCost_le hn0 J n (R.G n) 1 (by simpa using R.m_kmin_pow_G_le hn)
  have hc : Multiset.card (R.srcBelow n (R.G n) 1) ≤ R.Nsrc n := by
    unfold Nsrc srcT; rw [Multiset.card_add]; exact Nat.le_add_left _ _
  have : 2 ^ n * (2 * R.unitsSub n (R.G n) 1 + R.G n * Multiset.card (R.srcBelow n (R.G n) 1)) ≤
      2 ^ n * (2 * R.unitsT n + R.G n * R.Nsrc n) := by
    unfold unitsT
    exact Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.mul_le_mul_left _ hc) _)
  unfold exT
  omega

/-! ## 6. The bill -/

lemma J_ge {n0 : ℕ} (hn0 : R.m ≤ n0) {J : ℕ → ℕ} (hJ : R.JobRec n0 J) (n : ℕ) : 2 ^ n ≤ J n := by
  by_cases h : n < n0
  · exact le_trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos n)) (hJ.1 n h)
  · push_neg at h
    have hN := R.Nsrc_pos_of hn0 h
    have h2 := hJ.2 n h
    have h3 : R.Nsrc n * 2 ^ n ≤ R.treeCost J n := by
      unfold treeCost
      have : R.Nsrc n * 2 ^ n ≤ (2 * R.unitsT n + R.Nsrc n * (R.G n + 1)) * 2 ^ n :=
        Nat.mul_le_mul_right _ (le_trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
          (Nat.le_add_left _ _))
      omega
    exact Nat.le_of_mul_le_mul_left (le_trans h3 (le_trans (Nat.le_add_right _ _) h2)) hN

lemma charge_rest (n0 : ℕ) (J : ℕ → ℕ) (n lam : ℕ) :
    ((R.restMS n lam).map (R.costS n0 J)).sum =
      lam * ((R.srcT n).map (fun s => R.topCost n0 J (n - s) (2 ^ s))).sum := by
  unfold restMS
  rw [Multiset.map_nsmul, Multiset.sum_nsmul, Multiset.map_map, smul_eq_mul]
  rfl

/-- The rests cost at most `lam` times their per-copy price. -/
lemma rest_le {n0 : ℕ} (hn0 : R.m ≤ n0) (J : ℕ → ℕ) (n lam : ℕ) (hlam : 1 ≤ lam) :
    ((R.restMS n lam).map (R.costS n0 J)).sum ≤ lam * PhiN (R.srF J n) (R.srcT n) := by
  rw [R.charge_rest, PhiN_apply]
  refine Nat.mul_le_mul_left _ (Multiset.sum_map_le_sum_map _ _ (fun s _ => ?_))
  have hL := R.LftS_le hn0 (n - s) (2 ^ s)
  unfold topCost srF
  have hA : R.Nsrc (n - s) * (n - s + 1) * 2 ^ (n - s) + (n - s + 1) * 2 ^ (n - s) =
      (R.Nsrc (n - s) + 1) * (n - s + 1) * 2 ^ (n - s) := by ring
  omega

/-- **The bill on a top job.** -/
theorem bill_top {n0 : ℕ} (hn0 : R.m ≤ n0) {J : ℕ → ℕ} (hJ : R.JobRec n0 J) (n B : ℕ) :
    R.locS n0 (.top n B) + 1 + ((R.kidsS n0 (.top n B)).map (R.costS n0 J)).sum ≤
      R.costS n0 J (.top n B) := by
  have hJn := R.J_ge hn0 hJ n
  simp only [locS, kidsS, costS, topCost, LftS]
  by_cases hn : n0 ≤ n
  · have hN := R.Nsrc_pos_of hn0 hn
    rw [if_pos hn, if_pos hn]
    by_cases hB : R.Nsrc n ≤ B
    · rw [if_pos ⟨hn, hB⟩, Multiset.map_add, Multiset.sum_add, Multiset.map_replicate,
        Multiset.sum_replicate, smul_eq_mul]
      set N := R.Nsrc n
      set lam := B / N
      set r := B % N
      have hlam : 1 ≤ lam := (Nat.le_div_iff_mul_le (by omega)).2 (by simpa using hB)
      have hBd : N * lam + r = B := Nat.div_add_mod B N
      have hroot := R.rootCost_le hn0 J (le_trans hn0 hn)
      have hrest := R.rest_le hn0 J n lam hlam
      have hrec := hJ.2 n hn
      rw [R.treeCost_add_Rnd] at hrec
      set T := 2 ^ n * (2 * R.unitsT n + R.G n * N) + PhiN (R.exF J n) (R.exT n) +
        PhiN (R.srF J n) (R.srcT n)
      have hroot' : R.costS n0 J (Shape.cls n (R.G n) 1) ≤ 2 ^ n * (2 * R.unitsT n + R.G n * N)
          + PhiN (R.exF J n) (R.exT n) := hroot
      have hlr : lam * R.costS n0 J (Shape.cls n (R.G n) 1) + lam * PhiN (R.srF J n) (R.srcT n)
          ≤ lam * T := by
        rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by simp only [T]; omega)
      have hl2 : lam * (N * 2 ^ n + T) ≤ lam * (N * J n) := Nat.mul_le_mul_left _ hrec
      have hr2 : r * 2 ^ n ≤ r * J n := Nat.mul_le_mul_left _ hJn
      have h1 : 2 ^ n ≤ (n + 1) * 2 ^ n := Nat.le_mul_of_pos_left _ (Nat.succ_pos n)
      rw [← hBd]
      nlinarith
    · rw [if_neg (fun h => hB h.2)]
      simp only [Multiset.map_zero, Multiset.sum_zero, add_zero]
      have hr : B % R.Nsrc n = B := Nat.mod_eq_of_lt (by omega)
      rw [hr]
      have h1 : B * 2 ^ n ≤ B * J n := Nat.mul_le_mul_left _ hJn
      have h2 : 2 ^ n ≤ (n + 1) * 2 ^ n := Nat.le_mul_of_pos_left _ (Nat.succ_pos n)
      nlinarith
  · rw [if_neg hn, if_neg hn, if_neg (fun h => hn h.1)]
    simp only [Multiset.map_zero, Multiset.sum_zero, add_zero]
    push_neg at hn
    have h1 := hJ.1 n hn
    have h2 : B * ((n + 1) * 2 ^ n) ≤ B * J n := Nat.mul_le_mul_left _ h1
    nlinarith

/-- **The bill on a class** (exact, by the definition of `clsCost`). -/
theorem bill_cls (n0 : ℕ) (J : ℕ → ℕ) (n h ρ : ℕ) :
    R.locS n0 (.cls n h ρ) + 1 + ((R.kidsS n0 (.cls n h ρ)).map (R.costS n0 J)).sum ≤
      R.costS n0 J (.cls n h ρ) := by
  cases h with
  | zero =>
    simp only [locS, kidsS, costS, clsCost, R.card_srcBelow_zero, add_zero, Multiset.map_map]
    rfl
  | succ h =>
    simp only [locS, kidsS, costS, clsCost, Multiset.map_map]
    rfl

/-- **The bill** (hypothesis `hcost` of `recurse_inv`): on every reachable shape, local work + 1 +
the costs of the calls is at most the cost. -/
theorem bill {n0 : ℕ} (hn0 : R.m ≤ n0) {J : ℕ → ℕ} (hJ : R.JobRec n0 J) (d : Shape) :
    R.locS n0 d + 1 + ((R.kidsS n0 d).map (R.costS n0 J)).sum ≤ R.costS n0 J d := by
  cases d with
  | top n B => exact R.bill_top hn0 hJ n B
  | cls n h ρ => exact R.bill_cls n0 J n h ρ

/-! ## 7. Calls keep the invariant and lower the rank -/

lemma mem_kidsS_top {n0 n B : ℕ} {c : Shape} (hc : c ∈ R.kidsS n0 (.top n B)) :
    n0 ≤ n ∧ R.Nsrc n ≤ B ∧ (c = Shape.cls n (R.G n) 1 ∨
      ∃ s ∈ R.srcT n, c = Shape.top (n - s) (2 ^ s)) := by
  simp only [kidsS] at hc
  split_ifs at hc with h
  · refine ⟨h.1, h.2, ?_⟩
    rcases Multiset.mem_add.1 hc with hc | hc
    · exact Or.inl (Multiset.eq_of_mem_replicate hc)
    · right
      unfold restMS at hc
      obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.1 (Multiset.mem_of_mem_nsmul hc)
      exact ⟨s, hs, rfl⟩
  · simp at hc

theorem kids_inv {n0 : ℕ} (hn0 : R.m ≤ n0) {d c : Shape} (hd : R.InvS d) (hc : c ∈ R.kidsS n0 d) :
    R.InvS c := by
  cases d with
  | top n B =>
    obtain ⟨hn, -, h | ⟨s, -, rfl⟩⟩ := R.mem_kidsS_top hc
    · subst h
      exact ⟨le_rfl, by simpa using R.m_kmin_pow_G_le (le_trans hn0 hn)⟩
    · trivial
  | cls n h ρ =>
    cases h with
    | zero =>
      simp only [kidsS] at hc
      obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hc
      trivial
    | succ h =>
      simp only [kidsS] at hc
      obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hc
      exact ⟨le_trans hd.1 (Nat.le_mul_of_pos_right _ (R.rk_pos j)), R.inv_child j hd.2⟩

theorem kids_rank {n0 : ℕ} {d c : Shape} (hd : R.InvS d) (hc : c ∈ R.kidsS n0 d) :
    c.rank < d.rank := by
  cases d with
  | top n B =>
    obtain ⟨-, -, h | ⟨s, hs, rfl⟩⟩ := R.mem_kidsS_top hc
    · subst h
      simp only [Shape.rank]
      have : R.G n ≤ n := Nat.findGreatest_le n
      have h2 : (n + 1) * (n + 2) = (n + 1) * (n + 1) + n + 1 := by ring
      omega
    · simp only [Shape.rank]
      have h1 := R.src_pos hs
      have h2 := (R.src_size hs).2
      have h3 : n - s + 1 ≤ n := by omega
      have h4 : (n - s + 1) * (n - s + 2) ≤ n * (n + 1) := Nat.mul_le_mul h3 (by omega)
      have h5 : n * (n + 1) < (n + 1) * (n + 2) := by nlinarith
      omega
  | cls n h ρ =>
    cases h with
    | zero =>
      simp only [kidsS] at hc
      obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hc
      simp only [Shape.rank]
      have hρ : R.m * ρ ≤ n := by simpa using hd.2
      have hr := R.rk_lt_m j
      have h1 : ρ * R.rk j < n := by
        calc ρ * R.rk j < ρ * R.m := Nat.mul_lt_mul_of_pos_left hr (by have := hd.1; omega)
          _ = R.m * ρ := by ring
          _ ≤ n := hρ
      have h2 : (ρ * R.rk j + 1) * (ρ * R.rk j + 2) ≤ n * (n + 1) :=
        Nat.mul_le_mul (Nat.succ_le_of_lt h1) (by omega)
      have h3 : n * (n + 1) < (n + 1) * (n + 1) := by nlinarith
      omega
    | succ h =>
      simp only [kidsS] at hc
      obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hc
      simp only [Shape.rank]
      omega

/-! ## 8. The least solution of the job recurrence (for R2) -/

lemma treeCost_congr {J J' : ℕ → ℕ} {n : ℕ} (he : ∀ e ∈ R.exT n, J e = J' e)
    (hs : ∀ s ∈ R.srcT n, J (n - s) = J' (n - s)) : R.treeCost J n = R.treeCost J' n := by
  unfold treeCost
  rw [Multiset.map_congr rfl (fun e h => by rw [he e h]),
    Multiset.map_congr (s := R.srcT n) rfl (fun s h => by rw [hs s h])]

/-- `allotM` with fuel. -/
def allotF (n0 : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, n => if n < n0 then (n + 1) * 2 ^ n
      else (R.treeCost (allotF n0 f) n + R.Rnd n) / R.Nsrc n + 1

lemma allotF_stable (n0 : ℕ) : ∀ n f g, n < f → n < g → R.allotF n0 f n = R.allotF n0 g n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro f g hf hg
  obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
  simp only [allotF]
  split_ifs with h
  · rfl
  · rw [R.treeCost_congr (J := R.allotF n0 f) (J' := R.allotF n0 g)]
    · intro e he
      have := (R.exit_size he).2.2
      exact ih e this f g (by omega) (by omega)
    · intro s hs
      have := R.src_pos hs
      have := (R.src_size hs).2
      exact ih (n - s) (by omega) f g (by omega) (by omega)

/-- **The per-vector cost of the mixed engine**: the least solution of the job recurrence. -/
def allotM (n0 : ℕ) (n : ℕ) : ℕ := R.allotF n0 (n + 1) n

lemma allotM_eq (n0 n : ℕ) : R.allotM n0 n =
    if n < n0 then (n + 1) * 2 ^ n else (R.treeCost (R.allotM n0) n + R.Rnd n) / R.Nsrc n + 1 := by
  show R.allotF n0 (n + 1) n = _
  simp only [allotF]
  split_ifs with h
  · rfl
  · rw [R.treeCost_congr (J := R.allotF n0 n) (J' := R.allotM n0)]
    · intro e he
      have := (R.exit_size he).2.2
      exact R.allotF_stable n0 e n (e + 1) this (by omega)
    · intro s hs
      have := R.src_pos hs
      have := (R.src_size hs).2
      exact R.allotF_stable n0 (n - s) n (n - s + 1) (by omega) (by omega)

/-- `allotM` satisfies the job recurrence (the bill's hypothesis). -/
theorem allotM_jobRec {n0 : ℕ} (hn0 : R.m ≤ n0) : R.JobRec n0 (R.allotM n0) := by
  refine ⟨fun n hn => by rw [R.allotM_eq, if_pos hn], fun n hn => ?_⟩
  rw [R.allotM_eq, if_neg (by omega)]
  have hN := R.Nsrc_pos_of hn0 hn
  set X := R.treeCost (R.allotM n0) n + R.Rnd n
  have := Nat.lt_mul_div_succ X (show 0 < R.Nsrc n by omega)
  omega

/-- **The upper recurrence of `allotM`** (what R2's induction, `lemmaA`, takes). -/
theorem allotM_upper {n0 : ℕ} (hn0 : R.m ≤ n0) :
    (∀ n, n < n0 → R.allotM n0 n = (n + 1) * 2 ^ n) ∧
    ∀ n, n0 ≤ n → R.Nsrc n * R.allotM n0 n ≤ R.treeCost (R.allotM n0) n + R.Rnd n + R.Nsrc n := by
  refine ⟨fun n hn => by rw [R.allotM_eq, if_pos hn], fun n hn => ?_⟩
  rw [R.allotM_eq, if_neg (by omega), Nat.mul_add, mul_one]
  exact Nat.add_le_add_right (Nat.mul_div_le _ _) _

end Rule

end OAI.PowerSaving.MX

#print axioms OAI.PowerSaving.MX.Rule.bill
#print axioms OAI.PowerSaving.MX.Rule.kids_inv
#print axioms OAI.PowerSaving.MX.Rule.kids_rank
#print axioms OAI.PowerSaving.MX.Rule.allotM_jobRec
#print axioms OAI.PowerSaving.MX.Rule.allotM_upper
