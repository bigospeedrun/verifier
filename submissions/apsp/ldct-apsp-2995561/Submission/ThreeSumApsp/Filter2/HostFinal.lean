/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Filter2.HostProcs
public import Submission.ThreeSumApsp.AllEdges.Task

/-!
# The filtering host: the last phase

For every group `g` that is not done, the blocks of its active candidates are scanned
(`groupBody`); the flag of `g` is 1 if it is done or a scan finds a zero triangle.  The time depends
on the number of active candidates (`final_spec`).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Filter2

open ThreeSumApsp.Spec Light.Sec3

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Counting loops whose rounds take different times -/

/-- **Counting loops whose rounds take different times**: round `j` takes at most `b j` steps. -/
theorem Ends.forVar {σ : State} {i : ℕ} {hi : Expr} {body : Stmt} {T : ℕ} {Q : State → Prop}
    (I : ℕ → State → Prop) (n : ℕ) (b : ℕ → ℕ)
    (start : I 0 { σ with loc := Function.update σ.loc i 0 })
    (round : ∀ (j : ℕ) (σ : State), j < n → σ.loc i = j → I j σ → Ends lim P d body σ (b j) fun σ' =>
      σ'.loc i = j ∧ I (j + 1) { σ' with loc := Function.update σ'.loc i ((j : ℤ) + 1) })
    (done : ∀ σ : State, σ.loc i = n → I n σ → Q σ)
    (bound : ∀ (j : ℕ) (σ : State), j ≤ n → σ.loc i = j → I j σ → hi.Safe lim σ ∧ hi.val σ = n)
    (hn : (n : ℤ) ≤ lim.word)
    (hT : ∑ j ∈ Finset.range n, (hi.cost + b j + 7) + hi.cost + 5 ≤ T) :
    Ends lim P d (Stmt.for i hi body) σ T Q := by
  have h0 : (0 : ℤ) ≤ lim.word := le_trans (Int.natCast_nonneg n) hn
  refine Ends.seq 2 (∑ j ∈ Finset.range n, (hi.cost + b j + 7) + hi.cost + 3)
    (Ends.set (by simpa using h0) (by simp) ?_) (by omega)
  refine (Ends.while (fun j σ => σ.loc i = j ∧ I j σ) n (fun j => b j + 4)
    ⟨by simp, by simpa using start⟩ ?_ ?_).mono
    (le_of_eq ?_) fun _ h => h
  case refine_3 =>
    simp only [Cond.cost, Expr.cost]
    have e : ∀ j, 1 + hi.cost + 1 + 1 + (b j + 4) = hi.cost + b j + 7 := fun j => by ring
    simp only [e]
    ring
  · rintro j σ hj ⟨hc, hI⟩
    obtain ⟨hs, hv⟩ := bound j σ hj.le hc hI
    refine ⟨⟨trivial, hs⟩, ?_, Ends.seq (b j) 4 ((round j σ hj hc hI).mono le_rfl ?_) le_rfl⟩
    · change σ.loc i < hi.val σ
      rw [hc, hv]
      exact_mod_cast hj
    · rintro σ' ⟨hc', hI'⟩
      have hval : (v i +' k 1).val σ' = (j : ℤ) + 1 := by simp [hc']
      have hj' : (j : ℤ) + 1 ≤ n := by exact_mod_cast hj
      refine Ends.set ⟨trivial, ?_, ?_⟩ (by simp) ⟨?_, ?_⟩
      · change ((1 : ℕ) : ℤ) ≤ lim.word
        push_cast
        omega
      · change |(v i +' k 1).val σ'| ≤ lim.word
        rw [hval, abs_of_nonneg (by omega)]
        omega
      · simp [hc']
      · rw [hval]
        exact hI'
  · rintro σ ⟨hc, hI⟩
    obtain ⟨hs, hv⟩ := bound n σ le_rfl hc hI
    refine ⟨⟨trivial, hs⟩, ?_, done σ hc hI⟩
    change ¬ σ.loc i < hi.val σ
    rw [hc, hv]
    exact lt_irrefl _

/-! ## The scan of a block -/

/-- The scan of the block `j` for the pair of the group `g`. -/
def blockHit (n s : ℕ) (AB BC AC : List ℤ) (j g : ℕ) : Bool :=
  scanHit n AB BC AC (g / n) (g % n) (j * s) (min s (n - j * s))

theorem blockHit_iff {n s : ℕ} {AB BC AC : List ℤ} {j g : ℕ} (hg : g < n * n) (hjs : j * s < n) :
    blockHit n s AB BC AC j g = true ↔ 0 < cntOf n s 0 AB BC AC (j * (n * n) + g) := by
  have hgn : g / n * n + g % n = g := Nat.div_add_mod' g n
  unfold blockHit cntOf
  rw [div_block hg, mod_block hg, Finset.card_pos]
  simp only [scanHit, List.any_eq_true, List.mem_range, decide_eq_true_eq, Finset.Nonempty,
    Finset.mem_filter, Finset.mem_range, Nat.cast_zero, zero_dvd_iff, triSum, InBlock]
  rw [hgn]
  constructor
  · rintro ⟨c, hc, h⟩
    refine ⟨j * s + c, by omega, ⟨by omega, ?_, by omega⟩, ?_⟩
    · rw [Nat.add_mul, Nat.one_mul]; omega
    · rw [show g % n * n + (j * s + c) = g % n * n + j * s + c by ring,
        show g / n * n + (j * s + c) = g / n * n + j * s + c by ring]
      exact h
  · rintro ⟨c, hc, ⟨h1, h2, h3⟩, h⟩
    rw [Nat.add_mul, Nat.one_mul] at h2
    refine ⟨c - j * s, by omega, ?_⟩
    rw [show g % n * n + j * s + (c - j * s) = g % n * n + c by omega,
      show g / n * n + j * s + (c - j * s) = g / n * n + c by omega]
    exact h

theorem bit_eq_bitB (b : Bool) : Light.Sec3.bit b = bitB b := by cases b <;> rfl

/-! ## One group -/

/-- One block of the group.  Locals: 0 n, 1 ab, 2 bc, 3 ac, 4 out, 5 done, 6 act, 7 s, 8 m, 9 N,
10 a, 11 b, 12 g, 13 hit, 14 j, 15 c0, 16 len. -/
def groupRound (pScan : ℕ) : Stmt :=
  .ite (v 13 =' k 0)
    (.ite (M (v 6 +' v 14 *' v 9 +' v 12) =' k 0) .skip
      (.set 15 (v 14 *' v 7) ;;
       .set 16 (v 7) ;;
       .ite (v 0 -' v 15 <' v 7) (.set 16 (v 0 -' v 15)) .skip ;;
       .call pScan [v 1, v 2, v 3, v 0, v 10, v 11, v 15, v 16] 13))
    .skip

/-- group(n, ab, bc, ac, out, done, act, s, m, N, a, b, g): the flag of the group `g = a n + b`. -/
def groupBody (pScan : ℕ) : Stmt :=
  .set 13 (M (v 5 +' v 12)) ;;
  Stmt.for 14 (v 8) (groupRound pScan) ;;
  .store (v 4 +' v 12) (v 13) ;;
  .set 0 (k 0)

/-- The flag of the group `g` after the first `j` blocks. -/
def hitB (n s : ℕ) (AB BC AC : List ℤ) (act D : ℕ → Bool) (g j : ℕ) : Bool :=
  D g || (List.range j).any fun j' => act (j' * (n * n) + g) && blockHit n s AB BC AC j' g

theorem hitB_succ (n s : ℕ) (AB BC AC : List ℤ) (act D : ℕ → Bool) (g j : ℕ) :
    hitB n s AB BC AC act D g (j + 1) =
      (hitB n s AB BC AC act D g j || (act (j * (n * n) + g) && blockHit n s AB BC AC j g)) := by
  simp [hitB, List.range_succ, List.any_append, Bool.or_assoc]

/-- The number of active candidates of a group that is not done. -/
def cntG (N m : ℕ) (act D : ℕ → Bool) (g : ℕ) : ℕ :=
  ∑ j ∈ Finset.range m, if (act (j * N + g) && !D g) then 1 else 0

/-- The time of group. -/
def tGroup (m s c : ℕ) : ℕ := 60 * m + 20 + c * tScan s

theorem sum_round_time (N m g t : ℕ) (act D : ℕ → Bool) :
    ∑ j ∈ Finset.range m, (1 + (50 + (if (act (j * N + g) && !D g) then t else 0)) + 7) =
      58 * m + cntG N m act D g * t := by
  unfold cntG
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, add_mul]
    split_ifs <;> ring

theorem flag_scan_eq {n s : ℕ} {AB BC AC : List ℤ} {j g : ℕ} :
    flag (scanHit n AB BC AC (g / n) (g % n) (j * s) (min s (n - j * s)) = true) =
      bitB (blockHit n s AB BC AC j g) := by
  rw [flag_eq_bit, bit_eq_bitB]
  rfl

theorem group_spec {pScan : ℕ} (hS : P[pScan]? = some scanBody) {μ : ℕ → ℤ}
    {n U ab bc ac out done act s m g : ℕ} {AB BC AC : List ℤ} {D actB : ℕ → Bool}
    (hW : Weights lim μ ab bc ac n U AB BC AC)
    (hdone : Arr μ done (n * n) fun g => bitB (D g))
    (hact : Arr μ act (m * (n * n)) fun i => bitB (actB i))
    (hg : g < n * n) (hm : ∀ j < m, j * s < n)
    (hsd : done + n * n ≤ lim.space) (hsa : act + m * (n * n) ≤ lim.space)
    (hso : out + n * n ≤ lim.space) (hword : ((m * (n * n) + n + s : ℕ) : ℤ) ≤ lim.word)
    (hdep : d < lim.depth) :
    Ends lim P d (groupBody pScan)
      ⟨frame [n, ab, bc, ac, out, done, act, s, m, n * n, ((g / n : ℕ) : ℤ), ((g % n : ℕ) : ℤ), g], μ⟩
      (tGroup m s (cntG (n * n) m actB D g)) fun σ' =>
        σ'.mem = Function.update μ (out + g) (bitB (hitB n s AB BC AC actB D g m)) := by
  light_facts hW
  push_cast at hword
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at hg
    · exact h
  have ha : g / n < n := (Nat.div_lt_iff_lt_mul hn).2 hg
  have hb : g % n < n := Nat.mod_lt _ hn
  have hD := hdone g hg
  have hD0 := bitB_nonneg (D g)
  have hD1 := bitB_le_one (D g)
  have hsum := sum_round_time (n * n) m g (tScan s) actB D
  have hmN : m ≤ m * (n * n) := Nat.le_mul_of_pos_right m (by positivity)
  have hmNZ : (m : ℤ) ≤ (m : ℤ) * ((n : ℤ) * (n : ℤ)) := by exact_mod_cast hmN
  unfold groupBody tGroup
  light_set (bitB (D g)) using hD
  refine Ends.next (∑ j ∈ Finset.range m,
      (1 + (50 + (if (actB (j * (n * n) + g) && !D g) then tScan s else 0)) + 7) + 1 + 5)
    (Ends.forVar (fun j σ => ∃ c15 c16 : ℤ, σ = ⟨frame [n, ab, bc, ac, out, done, act, s, m, n * n,
      g / n, g % n, g, bitB (hitB n s AB BC AC actB D g j), j, c15, c16], μ⟩) m
      (fun j => 50 + (if (actB (j * (n * n) + g) && !D g) then tScan s else 0))
      ?start ?round ?done ?bound (by omega) (by simp)) (by rw [hsum]; simp only [Expr.cost]; omega)
  case start =>
    refine ⟨0, 0, ?_⟩
    simp only [update_frame_setLocal, setLocal, Nat.cast_ofNat]
    have : hitB n s AB BC AC actB D g 0 = D g := by simp [hitB]
    rw [this]
    simpa using (frame_append_zeros [(n : ℤ), ab, bc, ac, out, done, act, s, m, ((n * n : ℕ) : ℤ),
      ((g / n : ℕ) : ℤ), ((g % n : ℕ) : ℤ), g, bitB (D g), 0] 2).symm
  case bound =>
    rintro j _ - - ⟨c15, c16, rfl⟩
    simp
  case done =>
    rintro _ - ⟨c15, c16, rfl⟩
    have h0 := bitB_nonneg (hitB n s AB BC AC actB D g m)
    have h1 := bitB_le_one (hitB n s AB BC AC actB D g m)
    light_store (out + g) (bitB (hitB n s AB BC AC actB D g m))
    light_set (0 : ℕ)
    rfl
  case round =>
    rintro j _ hj - ⟨c15, c16, rfl⟩
    have hjs := hm j hj
    have hjN : j * (n * n) + g < m * (n * n) := by
      have := Nat.mul_le_mul_right (n * n) (show j + 1 ≤ m by omega)
      rw [Nat.add_mul, Nat.one_mul] at this
      omega
    have hA := hact _ hjN
    have hA0 := bitB_nonneg (actB (j * (n * n) + g))
    have hA1 := bitB_le_one (actB (j * (n * n) + g))
    have hH0 := bitB_nonneg (hitB n s AB BC AC actB D g j)
    have hH1 := bitB_le_one (hitB n s AB BC AC actB D g j)
    have haddr : ((act : ℤ) + (j : ℤ) * ((n : ℤ) * (n : ℤ)) + (g : ℤ)).toNat =
        act + (j * (n * n) + g) := by
      rw [show (act : ℤ) + (j : ℤ) * ((n : ℤ) * (n : ℤ)) + (g : ℤ) =
        ((act + (j * (n * n) + g) : ℕ) : ℤ) by push_cast; ring, Int.toNat_natCast]
    have hjNZ : (0 : ℤ) ≤ (j : ℤ) * ((n : ℤ) * (n : ℤ)) := by positivity
    have hjNZ' : (j : ℤ) * ((n : ℤ) * (n : ℤ)) + g < (m : ℤ) * ((n : ℤ) * (n : ℤ)) := by
      exact_mod_cast hjN
    refine Ends.ite (46 + (if (actB (j * (n * n) + g) && !D g) then tScan s else 0))
      (by light_side) (fun hc => ?_) (fun hc => ?_) (by simp only [Cond.cost, Expr.cost]; omega)
    · -- no zero triangle found yet
      have hH : hitB n s AB BC AC actB D g j = false := bitB_eq_zero.1 (by simpa using hc)
      have hDg : D g = false := by
        simp only [hitB, Bool.or_eq_false_iff] at hH
        exact hH.1
      refine Ends.ite (35 + (if (actB (j * (n * n) + g) && !D g) then tScan s else 0))
        (by light_side [haddr, hA]) (fun hc2 => ?_) (fun hc2 => ?_)
        (by simp only [Cond.cost, Expr.cost]; omega)
      · have hAf : actB (j * (n * n) + g) = false := bitB_eq_zero.1 (by simpa [haddr, hA] using hc2)
        refine Ends.skip ⟨by simp, c15, c16, ?_⟩
        rw [hitB_succ, hAf]
        simp [update_frame_setLocal]
      · have hAt : actB (j * (n * n) + g) = true := by
          cases h : actB (j * (n * n) + g)
          · simp [haddr, hA, h] at hc2
          · rfl
        rw [hAt, hDg]
        simp only [Bool.not_false, Bool.and_self, if_true]
        light_set (j * s : ℕ)
        light_set s
        have hlen : ∃ len : ℕ, len = min s (n - j * s) := ⟨_, rfl⟩
        obtain ⟨len, hlen⟩ := hlen
        have hlen1 : len ≤ s := hlen ▸ Nat.min_le_left _ _
        have hlen2 : j * s + len ≤ n := by rw [hlen]; omega
        have htail : ∀ l16 : ℤ, l16 = len → Ends lim P d
            (.call pScan [v 1, v 2, v 3, v 0, v 10, v 11, v 15, v 16] 13)
            ⟨frame (setLocal (setLocal [n, ab, bc, ac, out, done, act, s, m, n * n, g / n, g % n, g,
              bitB (hitB n s AB BC AC actB D g j), j, c15, c16] 15 (j * s : ℕ)) 16 l16), μ⟩
            (tScan len + 10) fun σ' => σ'.loc 14 = j ∧
              ∃ c15 c16 : ℤ, { σ' with loc := Function.update σ'.loc 14 ((j : ℤ) + 1) } =
                ⟨frame [n, ab, bc, ac, out, done, act, s, m, n * n, g / n, g % n, g,
                  bitB (hitB n s AB BC AC actB D g (j + 1)), j + 1, c15, c16], μ⟩ := by
          rintro _ rfl
          refine Ends.callTo (scan_meets (d := d + 1) hS hW ha hb hlen2) ?_ ?_ hdep (by light_time)
          · rintro r μ' ⟨hr, rfl⟩
            refine ⟨by simp, (j * s : ℕ), len, ?_⟩
            rw [hitB_succ, hH, hAt, hr, hlen, flag_scan_eq]
            simp [update_frame_setLocal]
          · constructor
            · intro e he
              simp only [List.mem_cons, List.not_mem_nil, or_false] at he
              rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
            · simp
        refine Ends.iteThen (fun hc3 => ?_) (fun hc3 => ?_) (by light_side) (by light_time)
        · have hc3' : n - j * s < s := by
            have : (n : ℤ) - (j * s : ℕ) < s := by simpa using hc3
            omega
          refine Ends.setToThen ((n - j * s : ℕ) : ℤ) ?_ (by light_side) (by light_time)
          exact (htail _ (by rw [hlen]; push_cast; omega)).mono (by
            have : tScan len ≤ tScan s := by unfold tScan; omega
            simp only [Cond.cost, Expr.cost]
            omega) fun _ h => h
        · have hc3' : ¬ n - j * s < s := by
            have : ¬ (n : ℤ) - (j * s : ℕ) < s := by simpa using hc3
            omega
          refine Ends.next 0 (Ends.skip ?_)
          exact (htail _ (by rw [hlen]; push_cast; omega)).mono (by
            have : tScan len ≤ tScan s := by unfold tScan; omega
            simp only [Cond.cost, Expr.cost]
            omega) fun _ h => h
    · -- found already
      have hH : hitB n s AB BC AC actB D g j = true := by
        cases h : hitB n s AB BC AC actB D g j
        · simp [h] at hc
        · rfl
      refine Ends.skip ⟨by simp, c15, c16, ?_⟩
      rw [hitB_succ, hH]
      simp [update_frame_setLocal]

/-! ## All groups -/

theorem Weights.congr {μ μ' : ℕ → ℤ} {ab bc ac n U : ℕ} {AB BC AC : List ℤ}
    (h : Weights lim μ ab bc ac n U AB BC AC)
    (hs : SameOn (fun a => Inside ab (n * n) a ∨ Inside bc (n * n) a ∨ Inside ac (n * n) a) μ μ') :
    Weights lim μ' ab bc ac n U AB BC AC :=
  { h with
    arrAB := ⟨h.arrAB.len, h.arrAB.seg.keep (fun a ha => hs a (Or.inl (by rw [h.arrAB.len] at ha; exact ha))),
      h.arrAB.bound, h.arrAB.below⟩
    arrBC := ⟨h.arrBC.len, h.arrBC.seg.keep
      (fun a ha => hs a (Or.inr (Or.inl (by rw [h.arrBC.len] at ha; exact ha)))),
      h.arrBC.bound, h.arrBC.below⟩
    arrAC := ⟨h.arrAC.len, h.arrAC.seg.keep
      (fun a ha => hs a (Or.inr (Or.inr (by rw [h.arrAC.len] at ha; exact ha)))),
      h.arrAC.bound, h.arrAC.below⟩ }

/-- final(n, ab, bc, ac, out, done, act, s, m, N): the flags of all groups.
Locals: 0 n, 1 ab, 2 bc, 3 ac, 4 out, 5 done, 6 act, 7 s, 8 m, 9 N, 10 a, 11 b, 12 g, 13 r. -/
def finalBody (pGroup : ℕ) : Stmt :=
  Stmt.for 12 (v 9) (
    .call pGroup [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12] 13 ;;
    .set 11 (v 11 +' k 1) ;;
    .ite (v 11 =' v 0) (.set 11 (k 0) ;; .set 10 (v 10 +' k 1)) .skip) ;;
  .set 0 (k 0)

/-- The time of final, with `c` the number of active candidates of the groups that are not done. -/
def tFinal (N m s c : ℕ) : ℕ := N * (60 * m + 60) + c * tScan s + 10

theorem sum_tGroup (N m s : ℕ) (f : ℕ → ℕ) :
    ∑ g ∈ Finset.range N, (1 + (tGroup m s (f g) + 29) + 7) =
      N * (60 * m + 57) + (∑ g ∈ Finset.range N, f g) * tScan s := by
  unfold tGroup
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    ring

theorem final_spec {pGroup pScan : ℕ} (hG : P[pGroup]? = some (groupBody pScan))
    (hS : P[pScan]? = some scanBody) {μ : ℕ → ℤ}
    {n U ab bc ac out done act s m : ℕ} {AB BC AC : List ℤ} {D actB : ℕ → Bool}
    (hW : Weights lim μ ab bc ac n U AB BC AC)
    (hdone : Arr μ done (n * n) fun g => bitB (D g))
    (hact : Arr μ act (m * (n * n)) fun i => bitB (actB i))
    (hm : ∀ j < m, j * s < n) (hn : 1 ≤ n)
    (hsd : done + n * n ≤ lim.space) (hsa : act + m * (n * n) ≤ lim.space)
    (hso : out + n * n ≤ lim.space)
    (hoab : Apart out (n * n) ab (n * n)) (hobc : Apart out (n * n) bc (n * n))
    (hoac : Apart out (n * n) ac (n * n)) (hod : Apart out (n * n) done (n * n))
    (hoa : Apart out (n * n) act (m * (n * n)))
    (hword : ((m * (n * n) + n + s : ℕ) : ℤ) ≤ lim.word) (hdep : d + 1 < lim.depth) :
    Ends lim P d (finalBody pGroup) ⟨frame [n, ab, bc, ac, out, done, act, s, m, n * n], μ⟩
      (tFinal (n * n) m s (∑ g ∈ Finset.range (n * n), cntG (n * n) m actB D g)) fun σ' =>
        Arr σ'.mem out (n * n) (fun g => bitB (hitB n s AB BC AC actB D g m)) ∧
          SameOutside μ σ'.mem out (n * n) := by
  light_facts hW
  push_cast at hword
  have hnn : n ≤ n * n := Nat.le_mul_of_pos_left n hn
  have hmN : m ≤ m * (n * n) := Nat.le_mul_of_pos_right m (by positivity)
  have hNw : ((n * n : ℕ) : ℤ) ≤ lim.word := by have := hW.hw; push_cast at hword ⊢; omega
  push_cast at hNw
  have hsum := sum_tGroup (n * n) m s (cntG (n * n) m actB D)
  have hexp : n * n * (60 * m + 60) = n * n * (60 * m + 57) + 3 * (n * n) := by ring
  unfold finalBody tFinal
  refine Ends.next (∑ g ∈ Finset.range (n * n), (1 + (tGroup m s (cntG (n * n) m actB D g) + 29) + 7)
      + 1 + 5)
    (Ends.forVar (fun g σ => ∃ r : ℤ, σ = ⟨frame [n, ab, bc, ac, out, done, act, s, m, n * n,
      ((g / n : ℕ) : ℤ), ((g % n : ℕ) : ℤ), g, r], wrote μ out (fun g => bitB (hitB n s AB BC AC actB D g m)) g⟩) (n * n)
      (fun g => tGroup m s (cntG (n * n) m actB D g) + 29)
      ?start ?round ?done ?bound (by push_cast; omega) le_rfl)
    (by rw [hsum]; omega)
  case start =>
    refine ⟨0, ?_⟩
    rw [wrote_zero]
    simpa [update_frame_setLocal] using (frame_append_zeros [(n : ℤ), ab, bc, ac, out, done, act, s, m,
      ((n * n : ℕ) : ℤ), 0, 0, 0] 1).symm
  case bound =>
    rintro g _ - - ⟨r, rfl⟩
    simp
  case done =>
    rintro _ - ⟨r, rfl⟩
    refine Ends.setTo 0 ⟨fun g hg => wrote_done (μ := μ) (dst := out)
        (f := fun g => bitB (hitB n s AB BC AC actB D g m)) hg,
      sameOutside_wrote (μ := μ) (dst := out)
        (f := fun g => bitB (hitB n s AB BC AC actB D g m)) le_rfl⟩
      (by light_side) (by simp only [Expr.cost]; rw [hsum]; omega)
  case round =>
    rintro g _ hg - ⟨r, rfl⟩
    set F : ℕ → ℤ := fun g => bitB (hitB n s AB BC AC actB D g m) with hF
    have hsame : SameOutside μ (wrote μ out F g) out (n * n) := sameOutside_wrote (by omega)
    have hW' := Weights.congr hW (μ' := wrote μ out F g)
      (SameOn.mono hsame fun a ha => by rcases ha with h | h | h <;> omega)
    have hdone' : Arr (wrote μ out F g) done (n * n) fun g => bitB (D g) :=
      hdone.congr fun i hi => hsame _ (by omega)
    have hact' : Arr (wrote μ out F g) act (m * (n * n)) fun i => bitB (actB i) :=
      hact.congr fun i hi => hsame _ (by omega)
    have hcall : Meets lim P pGroup (d + 1)
        [n, ab, bc, ac, out, done, act, s, m, (n * n : ℕ), (g / n : ℕ), (g % n : ℕ), g]
        (wrote μ out F g) (tGroup m s (cntG (n * n) m actB D g))
        fun _ μ' => μ' = Function.update (wrote μ out F g) (out + g) (F g) :=
      Meets.of_body hG (group_spec (d := d + 1) hS hW' hdone' hact' hg hm hsd hsa hso
        (by push_cast; omega) (by omega))
    light_call hcall with r' μ' rfl
    rw [wrote_succ]
    have hb : g % n < n := Nat.mod_lt _ (by omega)
    light_set ((g % n + 1 : ℕ) : ℤ)
    light_if hl1 hl2 : g % n + 1 = n
    · obtain ⟨hdiv, hmod⟩ := Nat.succ_div_mod_of_eq hl1
      have ha : g / n < n := (Nat.div_lt_iff_lt_mul (by omega)).2 hg
      have hzb : (g : ℤ) / (n : ℤ) < n := by rw [← Int.natCast_div]; exact_mod_cast ha
      have hz0 : 0 ≤ (g : ℤ) / (n : ℤ) := Int.ediv_nonneg (by positivity) (by positivity)
      light_set (0 : ℕ)
      light_set ((g / n + 1 : ℕ) : ℤ)
      refine ⟨by simp, r', ?_⟩
      rw [hdiv, hmod]
      simp [update_frame_setLocal]
    · obtain ⟨hdiv, hmod⟩ := Nat.succ_div_mod_of_ne (by omega) hl2
      light_skip
      refine ⟨by simp, r', ?_⟩
      rw [hdiv, hmod]
      simp [update_frame_setLocal]

end Light.Filter2
