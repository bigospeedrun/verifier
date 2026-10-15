/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.AllEdges.ScanPairs
public import Submission.ThreeSumApsp.AllEdges.Task
public import Submission.ThreeSumApsp.Programs.Sec3.Theorem17.Host.FailedScans

/-!
# All-edges host: the marks, as pure data

The all-edges host runs the instances of Theorem 17 and keeps a mark for every pair `(a, b)`.
`HostData.marks t` are the marks before instance `t`; `HostData.aeExecs t` is the number of scans
of instance `t`.  A scan is a failed scan or sets a new mark, so all instances together make at most
`F(p) + n²` scans (`HostData.sum_aeExecs_le`).  After all instances the mark of `(a, b)` is set if
and only if some `c` has `S(a,b,c) = 0` (`HostData.marks_m_iff`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

namespace HostData

variable (X : HostData)

/-- The place of the query pair number `i` of instance `t`, as scanPairsAE computes it. -/
abbrev aePl (t : ℕ) : ℕ → ℕ := plOf X.n (X.WI t) (X.WJ t)

/-- The marks before instance `t`. -/
def marks : ℕ → ℕ → Bool
  | 0 => fun _ => false
  | t + 1 => marksUpto (X.acc t) (X.hit t) (X.aePl t) (marks t) (X.w t)

/-- The number of scans of instance `t`. -/
def aeExecs (t : ℕ) : ℕ := aeExecsUpto (X.acc t) (X.hit t) (X.aePl t) (X.marks t) (X.w t)

variable {X}

theorem aePl_eq {t i : ℕ} (hi : i < X.w t) : X.aePl t i = X.place t i := by
  rw [aePl, plOf, getD_WI hi, getD_WJ hi, rowOf_mul_add_colOf]

/-- Scans are failures or new marks. -/
theorem sum_aeExecs_le (hv : X.Valid) :
    ∑ t ∈ Finset.range X.m, X.aeExecs t
      ≤ (triOf X.n X.AB X.BC X.AC).F X.p + X.n * X.n := by
  have key : ∀ T, T ≤ X.m → ∑ t ∈ Finset.range T, X.aeExecs t
      ≤ ∑ t ∈ Finset.range T, X.fails t + markCount (X.n * X.n) (X.marks T) := by
    intro T
    induction T with
    | zero => intro _; simp [markCount, marks]
    | succ T ih =>
      intro hT
      have hstep := aeExecsUpto_le (X.acc T) (X.hit T) (X.aePl T) (X.marks T) (X.n * X.n) (X.w T)
        fun i hi => (aePl_eq hi).trans_lt (hv.place_lt (by omega) hi)
      have := ih (by omega)
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hstep' : X.aeExecs T + markCount (X.n * X.n) (X.marks T)
          ≤ X.fails T + markCount (X.n * X.n) (X.marks (T + 1)) := hstep
      omega
  have h1 := key X.m le_rfl
  have h2 := sum_fails_le hv
  have h3 := markCount_le (X.n * X.n) (X.marks X.m)
  omega

/-- The marks: a mark is set if and only if an accepted query pair at its place has a successful
scan. -/
theorem marks_iff (T q : ℕ) :
    X.marks T q = true ↔ ∃ t < T, ∃ i < X.w t,
      X.acc t i = true ∧ X.hit t i = true ∧ X.aePl t i = q := by
  induction T with
  | zero => simp [marks]
  | succ T ih =>
    rw [marks, marksUpto, Bool.or_eq_true, ih, List.any_eq_true]
    constructor
    · rintro (⟨t, ht, h⟩ | ⟨i, hi, h⟩)
      · exact ⟨t, by omega, h⟩
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        exact ⟨T, by omega, i, List.mem_range.1 hi, h.1.1, h.1.2, h.2⟩
    · rintro ⟨t, ht, i, hi, ha, hh, hq⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with hlt | rfl
      · exact Or.inl ⟨t, hlt, i, hi, ha, hh, hq⟩
      · exact Or.inr ⟨i, List.mem_range.2 hi, by simp [ha, hh, hq]⟩

/-- **After all instances the mark of `(a, b)` is set if and only if some `c` has `S(a,b,c) = 0`.**
-/
theorem marks_m_iff (hv : X.Valid) {q : ℕ} (hq : q < X.n * X.n) :
    X.marks X.m q = true ↔ ∃ c < X.n, X.sumAt (q / X.n) (q % X.n) c = 0 := by
  have hn := hv.n_pos
  rw [marks_iff]
  constructor
  · rintro ⟨t, ht, i, hi, -, hhit, hpl⟩
    obtain ⟨c, hc, hzero⟩ := (hit_iff hi).1 hhit
    have hpiece := hv.piece_le ht
    have hcol := hv.colOf_lt ht hi
    rw [aePl_eq hi, ← rowOf_mul_add_colOf] at hpl
    have hdiv : q / X.n = X.rowOf t i := by
      rw [← hpl, Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hcol,
        Nat.zero_add]
    have hmod : q % X.n = X.colOf t i := by
      rw [← hpl, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hcol]
    exact ⟨X.c0 t + c, by omega, by rw [hdiv, hmod]; exact hzero⟩
  · rintro ⟨c, hc, hzero⟩
    obtain ⟨t, ht, i, hi, ha, hb, c', hc', rfl⟩ :=
      hv.exists_query (Nat.div_lt_of_lt_mul hq) (Nat.mod_lt _ (by omega)) hc
    refine ⟨t, ht, i, hi, (acc_iff hv ht hi).2 ⟨c', hc', ?_⟩, (hit_iff hi).2 ⟨c', hc', ?_⟩, ?_⟩
    · rw [ha, hb, hzero]; exact dvd_zero _
    · rw [ha, hb]; exact hzero
    · rw [aePl_eq hi, ← rowOf_mul_add_colOf, ha, hb, Nat.div_add_mod']

/-- The marks after all instances are the flags of all-edges Exact Triangle. -/
theorem bit_marks_m (hv : X.Valid) {q : ℕ} (hq : q < X.n * X.n) :
    bit (X.marks X.m q) = bit (aeHit X.n X.AB X.BC X.AC q) := by
  congr 1
  rw [Bool.eq_iff_iff, marks_m_iff hv hq, aeHit_iff hq]
  refine exists_congr fun c => and_congr_right fun _ => ?_
  rw [sumAt, Nat.div_add_mod']

end HostData

end Light.Sec3
