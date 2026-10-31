import Submission.Work.Mixed.Flow
import Submission.Work.Mixed.Prog.Seq
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

/-!
# Mixed engine, cost part 7: the program's unit codes counted by Flow's Pascal weights

(agent e-r3cost, round wht45/lever, 19 Oct 2026.)

e-r3prog's program (`Work.Mixed.Prog.Seq`, namespace `MXR`) codes the units of a class of height
`h` as sequences of `h` roles, a code `s < W^h` in base `W` (first letter least significant), with
column `colS W tq h s = ∏ tq (letters)`.  Flow (`Work.Mixed.Flow`) counts the same units by type
points `a ∈ ℕ^K` with Pascal weights `uh h a`.  With a type map `typ` on the roles
(`tq x = kr (typ x)`, `Wk k` roles of type `k`):

* `cntS`          the type point of a code;
* `colS_eq_col`   `colS h s = col (cntS h s)`;
* `sum_codes`     `∑_{s < W^h} f (cntS h s) = ∑_{|a| = h} uh h a • f a`  (sequences by type count);
* `NU_eq_unitsC`  **the program's unit count of a class is Flow's `unitsC`**;
* `card_srcMS_eq` the program's source count of a class (inputs whose parent code lies outside the
                  parent's region) is `card (srcMS n h ρ ρp)`.
-/

set_option linter.unusedSectionVars false

namespace OAI.PowerSaving.MX

open Finset

/-- Codes below `N * W` split into a high part `τ < N` and a low letter `x < W`. -/
lemma sum_range_mul_split {M : Type*} [AddCommMonoid M] (g : ℕ → M) (W N : ℕ) :
    ∑ s ∈ range (N * W), g s = ∑ τ ∈ range N, ∑ x ∈ range W, g (x + W * τ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    refine Finset.sum_congr rfl (fun x _ => ?_)
    congr 1; ring

namespace Rule

variable (R : Rule)

/-- The type point of the sequence coded by `s` (length `h`, base `W`). -/
def cntS (typ : ℕ → Fin R.K) (W : ℕ) : ℕ → ℕ → R.Pt
  | 0, _ => 0
  | h + 1, s => R.e (typ (s % W)) + cntS typ W h (s / W)

lemma cntS_cons (typ : ℕ → Fin R.K) {W : ℕ} (h x τ : ℕ) (hx : x < W) :
    R.cntS typ W (h + 1) (x + W * τ) = R.e (typ x) + R.cntS typ W h τ := by
  have hW : 0 < W := lt_of_le_of_lt (Nat.zero_le _) hx
  have h1 : (x + W * τ) % W = x := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
  have h2 : (x + W * τ) / W = τ := by
    rw [Nat.add_mul_div_left _ _ hW, Nat.div_eq_of_lt hx, zero_add]
  simp only [cntS, h1, h2]

lemma colS_eq_col (typ : ℕ → Fin R.K) {W : ℕ} (hW : 0 < W) {tq : ℕ → ℕ}
    (htq : ∀ x, x < W → tq x = R.kr (typ x)) (h s : ℕ) :
    MXR.colS W tq h s = R.col (R.cntS typ W h s) := by
  induction h generalizing s with
  | zero => simp [cntS, R.col_zero]
  | succ h ih =>
    rw [MXR.colS_succ, ih, cntS, add_comm, R.col_add_e, htq _ (Nat.mod_lt _ hW)]

/-- Grouping a sum over the roles by their type. -/
lemma sum_roles_by_type {M : Type*} [AddCommMonoid M] (typ : ℕ → Fin R.K) {W : ℕ}
    (hW : ∀ k, ((range W).filter (fun x => typ x = k)).card = R.Wk k) (G : Fin R.K → M) :
    ∑ x ∈ range W, G (typ x) = ∑ k, R.Wk k • G k := by
  rw [← Finset.sum_fiberwise (range W) typ (fun x => G (typ x))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.1 hx).2]), Finset.sum_const, hW k]

/-- **Sequences by type count**: summing over the codes of length `h` is summing over the type points
with the Pascal weights. -/
theorem sum_codes {M : Type*} [AddCommMonoid M] (typ : ℕ → Fin R.K) {W : ℕ}
    (hW : ∀ k, ((range W).filter (fun x => typ x = k)).card = R.Wk k) (h : ℕ) (f : R.Pt → M) :
    ∑ s ∈ range (W ^ h), f (R.cntS typ W h s) =
      ∑ a ∈ Finset.Nat.antidiagonalTuple R.K h, R.uh h a • f a := by
  induction h generalizing f with
  | zero =>
    simp [cntS, uh, Finset.Nat.antidiagonalTuple_zero_right]
  | succ h ih =>
    rw [pow_succ, sum_range_mul_split]
    -- the inner sums run over the letters `x < W`
    have e1 : ∑ τ ∈ range (W ^ h), ∑ x ∈ range W, f (R.cntS typ W (h + 1) (x + W * τ)) =
        ∑ x ∈ range W, ∑ τ ∈ range (W ^ h), f (R.e (typ x) + R.cntS typ W h τ) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun x hx => Finset.sum_congr rfl (fun τ _ => ?_))
      rw [R.cntS_cons typ h x τ (Finset.mem_range.1 hx)]
    rw [e1]
    rw [Finset.sum_congr rfl (fun x _ => ih (fun b => f (R.e (typ x) + b)))]
    rw [R.sum_roles_by_type typ hW (fun k => ∑ a ∈ Finset.Nat.antidiagonalTuple R.K h,
      R.uh h a • f (R.e k + a))]
    have e2 : ∑ k, R.Wk k • ∑ a ∈ Finset.Nat.antidiagonalTuple R.K h, R.uh h a • f (R.e k + a) =
        ∑ a ∈ Finset.Nat.antidiagonalTuple R.K h, ∑ k, (R.Wk k * R.uh h a) • f (a + R.e k) := by
      rw [Finset.sum_comm]
      simp_rw [Finset.smul_sum]
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun k _ => ?_))
      rw [mul_smul, add_comm]
    rw [e2, R.sum_shift h (fun b k => (R.Wk k * R.uh h b) • f (b + R.e k))]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [show R.uh (h + 1) a = ∑ k, (if 1 ≤ a k then R.Wk k * R.uh h (a - R.e k) else 0) from rfl]
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    split_ifs with hak
    · rw [R.sub_e_add_e a k hak]
    · rw [zero_smul]

/-- **The program's unit count is Flow's.** -/
theorem NU_eq_unitsC (typ : ℕ → Fin R.K) {W : ℕ} (hW0 : 0 < W) {tq : ℕ → ℕ}
    (htq : ∀ x, x < W → tq x = R.kr (typ x))
    (hW : ∀ k, ((range W).filter (fun x => typ x = k)).card = R.Wk k) (n h ρ : ℕ) :
    MXR.NU W tq R.m n h ρ = R.unitsC n h ρ := by
  unfold MXR.NU MXR.PC
  rw [Nat.count_eq_card_filter_range, Finset.card_filter]
  have e1 : ∑ s ∈ range (W ^ h), (if MXR.inRS W tq R.m n h ρ s then 1 else 0) =
      ∑ s ∈ range (W ^ h), (fun a => if R.m * ρ * R.col a ≤ n then 1 else 0) (R.cntS typ W h s) := by
    refine Finset.sum_congr rfl (fun s hs => ?_)
    have hs' := Finset.mem_range.1 hs
    simp only [MXR.inRS, hs', true_and, R.colS_eq_col typ hW0 htq, mul_assoc]
  rw [e1, R.sum_codes typ hW h (fun a => if R.m * ρ * R.col a ≤ n then 1 else 0), unitsC, pts,
    Finset.sum_filter]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  split_ifs <;> simp

/-- **The program's source count of a class is Flow's.**  A source of the class `(n, h, ρ)` whose
parent has multiplier `ρp` is an input role `x` of a unit `s` of the class whose parent code
`x + W * s` (the parent unit) does not fit the parent's region. -/
theorem card_srcMS_eq (typ : ℕ → Fin R.K) {W : ℕ} (hW0 : 0 < W) {tq : ℕ → ℕ}
    (htq : ∀ x, x < W → tq x = R.kr (typ x))
    (hW : ∀ k, ((range W).filter (fun x => typ x = k)).card = R.Wk k) (n h ρ ρp : ℕ) :
    ∑ s ∈ (range (W ^ h)).filter (MXR.inRS W tq R.m n h ρ),
        ((range W).filter (fun x => n < R.m * (ρp * MXR.colS W tq (h + 1) (x + W * s)))).card =
      Multiset.card (R.srcMS n h ρ ρp) := by
  -- move to a sum over all codes of a function of the type point
  let F : R.Pt → ℕ := fun b => if R.m * ρ * R.col b ≤ n then
      ∑ k, R.Wk k * (if n < R.m * ρp * R.col (b + R.e k) then 1 else 0) else 0
  have e1 : ∑ s ∈ (range (W ^ h)).filter (MXR.inRS W tq R.m n h ρ),
        ((range W).filter (fun x => n < R.m * (ρp * MXR.colS W tq (h + 1) (x + W * s)))).card =
      ∑ s ∈ range (W ^ h), F (R.cntS typ W h s) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    have hs' := Finset.mem_range.1 hs
    simp only [MXR.inRS, hs', true_and, F, R.colS_eq_col typ hW0 htq, ← mul_assoc]
    split_ifs with hc
    · rw [Finset.card_filter]
      have e2 : ∀ x ∈ range W, (if n < R.m * ρp * R.col (R.cntS typ W (h + 1) (x + W * s)) then 1 else 0)
          = (fun k => if n < R.m * ρp * R.col (R.cntS typ W h s + R.e k) then 1 else 0) (typ x) := by
        intro x hx
        rw [R.cntS_cons typ h x s (Finset.mem_range.1 hx), add_comm]
      rw [Finset.sum_congr rfl e2, R.sum_roles_by_type typ hW
        (fun k => if n < R.m * ρp * R.col (R.cntS typ W h s + R.e k) then 1 else 0)]
      simp only [smul_eq_mul]
    · rfl
  rw [e1, R.sum_codes typ hW h F]
  simp only [srcMS, Multiset.card_sum]
  rw [pts, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp only [F]
  split_ifs with hb
  · rw [smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    split_ifs <;> simp [Multiset.card_nsmul]
  · simp

end Rule

end OAI.PowerSaving.MX

#print axioms OAI.PowerSaving.MX.Rule.sum_codes
#print axioms OAI.PowerSaving.MX.Rule.NU_eq_unitsC
#print axioms OAI.PowerSaving.MX.Rule.card_srcMS_eq
