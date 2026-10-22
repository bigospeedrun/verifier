import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Mixed engine, R3 program part 1: units of a class as sequences (agent e-r3prog, 19 Oct 2026)

The units of a class of height `h` are the sequences of `h` live roles (Pascal: the first letter
of a parent unit is the role it feeds in the child unit, the rest of the letters is the child
unit).  A sequence is coded by a number `s < W^h` in base `W` (first letter = least significant
digit), so that the parent unit `a :: τ` has code `a + W * τ`.

* `colS h s`       the column factor `∏ tq (digit)` (by iteration, as the RAM computes it);
* `inRS`           the region of a class `(n, h, ρ)`: `s < W^h ∧ mx * (ρ * colS h s) ≤ n`;
* `PC t`           the number of region codes below `t` (`Nat.count`), `NU` the number of units,
                   `U p` the `p`-th unit (`Nat.nth`), with `nth_spec`, `PC_U`, `U_PC`.
-/

namespace OAI.PowerSaving.MXR

open Finset

section Iter
variable (W : ℕ) (tq : ℕ → ℕ)

/-- One step of the column loop: multiply by the factor of the lowest digit, drop it. -/
def stepC (x : ℕ × ℕ) : ℕ × ℕ := (x.1 * tq (x.2 % W), x.2 / W)

lemma stepC_iter_snd (h : ℕ) (p s : ℕ) : ((stepC W tq)^[h] (p, s)).2 = s / W^h := by
  induction h generalizing p s with
  | zero => simp
  | succ h ih =>
    rw [Function.iterate_succ_apply]
    simp only [stepC]
    rw [ih, Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm (W^h) W]

lemma stepC_iter_fst (h : ℕ) (p s : ℕ) :
    ((stepC W tq)^[h] (p, s)).1 = p * ((stepC W tq)^[h] (1, s)).1 := by
  induction h generalizing p s with
  | zero => simp
  | succ h ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    simp only [stepC]
    rw [ih, ih (1 * tq (s % W))]
    ring

/-- Column factor of the sequence coded by `s` (length `h`). -/
def colS (h s : ℕ) : ℕ := ((stepC W tq)^[h] (1, s)).1

@[simp] lemma colS_zero (s : ℕ) : colS W tq 0 s = 1 := rfl

lemma colS_succ (h s : ℕ) : colS W tq (h+1) s = tq (s % W) * colS W tq h (s / W) := by
  unfold colS
  rw [Function.iterate_succ_apply]
  simp only [stepC, one_mul]
  exact stepC_iter_fst W tq h (tq (s % W)) (s / W)

/-- The parent code `a + W * τ` has first letter `a` and tail `τ`. -/
lemma colS_cons (h a τ : ℕ) (ha : a < W) :
    colS W tq (h+1) (a + W * τ) = tq a * colS W tq h τ := by
  have hW : 0 < W := lt_of_le_of_lt (Nat.zero_le _) ha
  rw [colS_succ]
  have h1 : (a + W * τ) % W = a := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
  have h2 : (a + W * τ) / W = τ := by
    rw [Nat.add_mul_div_left _ _ hW, Nat.div_eq_of_lt ha, zero_add]
  rw [h1, h2]

lemma colS_pos (hq : ∀ a, a < W → 1 ≤ tq a) (h s : ℕ) (hs : s < W^h) : 1 ≤ colS W tq h s := by
  induction h generalizing s with
  | zero => simp
  | succ h ih =>
    have hW : 0 < W := by
      rcases Nat.eq_zero_or_pos W with h0 | h0
      · subst h0; simp at hs
      · exact h0
    rw [colS_succ]
    have h1 := hq (s % W) (Nat.mod_lt _ hW)
    have h2 : s / W < W^h := by
      rw [Nat.div_lt_iff_lt_mul hW, ← pow_succ]; exact hs
    have h3 := ih (s / W) h2
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))

lemma lt_of_cons (h a τ : ℕ) (ha : a < W) (hτ : τ < W^h) : a + W * τ < W^(h+1) := by
  rw [pow_succ, Nat.mul_comm (W^h) W]
  calc a + W * τ < W + W * τ := by omega
    _ = W * (τ + 1) := by ring
    _ ≤ W * W^h := Nat.mul_le_mul_left _ hτ

end Iter

/-! ## Counting and enumerating a finite decidable set of naturals -/

section Count
variable {p : ℕ → Prop} [DecidablePred p]

/-- The `k`-th element of a bounded set: in the set, below the bound, and counted exactly. -/
lemma nth_spec {N k : ℕ} (hk : k < Nat.count p N) :
    p (Nat.nth p k) ∧ Nat.nth p k < N ∧ Nat.count p (Nat.nth p k) = k := by
  have hc : ∀ hf : (Set.ofPred p).Finite, k < #hf.toFinset :=
    fun hf => lt_of_lt_of_le hk (Nat.count_le_card hf N)
  exact ⟨Nat.nth_mem k hc, Nat.nth_lt_of_lt_count hk, Nat.count_nth hc⟩

lemma count_lt_of_mem {N s : ℕ} (hs : p s) (hsN : s < N) : Nat.count p s < Nat.count p N :=
  Nat.count_strict_mono hs hsN

lemma count_le_self (t : ℕ) : Nat.count p t ≤ t := by
  rw [Nat.count_eq_card_filter_range]
  exact le_trans (Finset.card_filter_le _ _) (by simp)

end Count

/-! ## The units of a class -/

section Class
variable (W : ℕ) (tq : ℕ → ℕ) (mx : ℕ)

/-- The region of a class `(n, h, ρ)`: codes of length-`h` sequences whose unit fits. -/
def inRS (n h ρ s : ℕ) : Prop := s < W^h ∧ mx * (ρ * colS W tq h s) ≤ n

instance (n h ρ : ℕ) : DecidablePred (inRS W tq mx n h ρ) := fun s => by
  unfold inRS; infer_instance

/-- Number of region codes below `t`. -/
def PC (n h ρ t : ℕ) : ℕ := Nat.count (inRS W tq mx n h ρ) t
/-- Number of units of the class. -/
def NU (n h ρ : ℕ) : ℕ := PC W tq mx n h ρ (W^h)
/-- The `p`-th unit (its code). -/
noncomputable def U (n h ρ p : ℕ) : ℕ := Nat.nth (inRS W tq mx n h ρ) p
/-- Column of unit `p`. -/
noncomputable def cU (n h ρ p : ℕ) : ℕ := ρ * colS W tq h (U W tq mx n h ρ p)
/-- Instance bits of unit `p`. -/
noncomputable def iU (n h ρ p : ℕ) : ℕ := n - mx * cU W tq mx n h ρ p

variable {W tq mx}

lemma U_spec {n h ρ p : ℕ} (hp : p < NU W tq mx n h ρ) :
    inRS W tq mx n h ρ (U W tq mx n h ρ p) ∧ U W tq mx n h ρ p < W^h ∧
      PC W tq mx n h ρ (U W tq mx n h ρ p) = p :=
  nth_spec hp

lemma U_lt {n h ρ p : ℕ} (hp : p < NU W tq mx n h ρ) : U W tq mx n h ρ p < W^h :=
  (U_spec hp).2.1

lemma U_fits {n h ρ p : ℕ} (hp : p < NU W tq mx n h ρ) : mx * cU W tq mx n h ρ p ≤ n :=
  (U_spec hp).1.2

lemma PC_U {n h ρ p : ℕ} (hp : p < NU W tq mx n h ρ) :
    PC W tq mx n h ρ (U W tq mx n h ρ p) = p := (U_spec hp).2.2

lemma U_PC {n h ρ s : ℕ} (hs : inRS W tq mx n h ρ s) : U W tq mx n h ρ (PC W tq mx n h ρ s) = s :=
  Nat.nth_count hs

lemma PC_lt {n h ρ s : ℕ} (hs : inRS W tq mx n h ρ s) : PC W tq mx n h ρ s < NU W tq mx n h ρ :=
  count_lt_of_mem hs hs.1

lemma iU_add {n h ρ p : ℕ} (hp : p < NU W tq mx n h ρ) :
    mx * cU W tq mx n h ρ p + iU W tq mx n h ρ p = n := by
  have := U_fits hp; unfold iU; omega

lemma NU_le (n h ρ : ℕ) : NU W tq mx n h ρ ≤ W^h := count_le_self _

end Class

end OAI.PowerSaving.MXR
