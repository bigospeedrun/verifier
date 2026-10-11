/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Filter2.HostMath
public import Submission.ThreeSumApsp.Lang.Tactics
public import Submission.ThreeSumApsp.Lang.Lib.Copy

/-!
# The filtering host: small procedures

* `div(a, b) = ⌊a/b⌋` and `pow2(e) = 2^e`, by counting up.
* `aggr(cnt, act, dst, N, m)`: `dst[g] := Σ_{j<m} act[j N + g] · cnt[j N + g]` for `g < N`.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Filter2

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Helpers for expressions -/

theorem gives_load {σ : State} {a : Expr} {b : ℕ} {z : ℤ} (ha : a.Gives lim σ (b : ℤ))
    (hb : b < lim.space) (hz : σ.mem b = z) : (M a).Gives lim σ z := by
  refine ⟨⟨ha.1, ?_⟩, ?_⟩
  · rw [ha.2]
    exact ⟨Int.natCast_nonneg b, by exact_mod_cast hb⟩
  · simp only [Expr.val, ha.2, Int.toNat_natCast, hz]

theorem gives_op {σ : State} {o : Op} {a b : Expr} {za zb : ℤ} (ha : a.Gives lim σ za)
    (hb : b.Gives lim σ zb) (hw : |o.eval za zb| ≤ lim.word) :
    (Expr.op o a b).Gives lim σ (o.eval za zb) := by
  refine ⟨⟨ha.1, hb.1, ?_⟩, ?_⟩
  · rw [ha.2, hb.2]; exact hw
  · simp only [Expr.val, ha.2, hb.2]

theorem gives_var (σ : State) (x : ℕ) : (v x).Gives lim σ (σ.loc x) := ⟨trivial, rfl⟩

theorem gives_const (σ : State) {c : ℕ} (hc : (c : ℤ) ≤ lim.word) : (k c).Gives lim σ c :=
  ⟨hc, rfl⟩

theorem gives_of_eq {σ : State} {e : Expr} {z z' : ℤ} (h : e.Gives lim σ z) (he : z = z') :
    e.Gives lim σ z' := he ▸ h

/-! ## Division and powers of two, by counting up -/

/-- div(a, b).  Locals: 0 a, 1 b, 2 the candidate q, 3 the multiple (q + 1) b. -/
def divBody : Stmt :=
  .set 2 (k 0) ;;
  .set 3 (v 1) ;;
  .while (v 3 ≤' v 0) (
    .set 3 (v 3 +' v 1) ;;
    .set 2 (v 2 +' k 1)) ;;
  .set 0 (v 2)

/-- The time of div. -/
def tDiv (a b : ℕ) : ℕ := 14 * (a / b) + 12

/-- **div** returns `⌊a/b⌋`, for `b ≥ 1`. -/
theorem div_meets {μ : ℕ → ℤ} {q a b : ℕ} (hP : P[q]? = some divBody) (hb : 1 ≤ b)
    (hword : ((a + b + 1 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P q d [a, b] μ (tDiv a b) fun r μ' => r = (a / b : ℕ) ∧ μ' = μ := by
  refine .of_body hP ?_
  have test : ∀ i, (i + 1) * b ≤ a ↔ i < a / b := fun i => by
    rw [← Nat.le_div_iff_mul_le hb]; omega
  have hle : a / b * b ≤ a := Nat.div_mul_le_self a b
  unfold tDiv
  generalize a / b = Q at test hle
  push_cast at hword
  light_set (0 : ℕ)
  light_set b
  refine Ends.next _ (Ends.whileBlock (fun i σ => σ = ⟨frame [a, b, i, ((i + 1) * b : ℕ)], μ⟩) Q
    (by simp) ?round ?done le_rfl)
  case round =>
    rintro i _ hi rfl
    have hlt := (test i).2 hi
    have hle' : i ≤ (i + 1) * b := by nlinarith
    rw [show (i + 1 + 1) * b = (i + 1) * b + b by ring]
    generalize (i + 1) * b = w at hlt hle'
    exact ⟨by light_side, by light_side, by light_side, by simp [update_frame_setLocal]⟩
  case done =>
    rintro _ rfl
    have hnot : ¬ (Q + 1) * b ≤ a := fun h => absurd ((test Q).1 h) (lt_irrefl Q)
    have hQ : Q ≤ a := le_trans (Nat.le_mul_of_pos_right Q hb) hle
    generalize (Q + 1) * b = w at hnot
    exact ⟨by light_side, by light_side, Ends.setTo Q (by simp)⟩

/-- pow2(e).  Locals: 0 e, 1 the counter i, 2 the power 2^i. -/
def pow2Body : Stmt :=
  .set 1 (k 0) ;;
  .set 2 (k 1) ;;
  .while (v 1 <' v 0) (
    .set 2 (v 2 +' v 2) ;;
    .set 1 (v 1 +' k 1)) ;;
  .set 0 (v 2)

/-- The time of pow2. -/
def tPow2 (e : ℕ) : ℕ := 12 * e + 12

/-- **pow2** returns `2^e`. -/
theorem pow2_meets {μ : ℕ → ℤ} {q e : ℕ} (hP : P[q]? = some pow2Body)
    (hword : ((2 ^ e + e + 1 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P q d [e] μ (tPow2 e) fun r μ' => r = (2 ^ e : ℕ) ∧ μ' = μ := by
  refine .of_body hP ?_
  unfold tPow2
  push_cast at hword
  have h0 : (0 : ℤ) ≤ 2 ^ e := by positivity
  light_set (0 : ℕ)
  light_set (1 : ℕ)
  refine Ends.next _ (Ends.whileBlock (fun i σ => σ = ⟨frame [e, i, (2 ^ i : ℕ)], μ⟩) e
    (by simp) ?round ?done le_rfl)
  case round =>
    rintro i _ hi rfl
    have hpow : 2 ^ (i + 1) ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) hi
    have hpowZ : ((2 ^ (i + 1) : ℕ) : ℤ) ≤ 2 ^ e := by exact_mod_cast hpow
    rw [show 2 ^ (i + 1) = 2 ^ i + 2 ^ i by ring] at hpowZ ⊢
    generalize 2 ^ i = w at hpowZ
    push_cast at hpowZ
    exact ⟨by light_side, by light_side, by light_side, by simp [update_frame_setLocal]⟩
  case done =>
    rintro _ rfl
    exact ⟨by light_side, by light_side, Ends.setTo (2 ^ e : ℕ) (by simp)⟩

/-! ## Aggregation -/

/-- The inner loop of aggr.  Locals: 0 cnt, 1 act, 2 dst, 3 N, 4 m, 5 g, 6 acc, 7 j. -/
def aggrInner : Stmt :=
  Stmt.for 7 (v 4) (.set 6 (v 6 +' M (v 1 +' v 7 *' v 3 +' v 5) *' M (v 0 +' v 7 *' v 3 +' v 5)))

/-- aggr(cnt, act, dst, N, m): `dst[g] := Σ_{j<m} act[j N + g] · cnt[j N + g]` for `g < N`. -/
def aggrBody : Stmt :=
  Stmt.for 5 (v 3) (.set 6 (k 0) ;; aggrInner ;; .store (v 2 +' v 5) (v 6)) ;;
  .set 0 (k 0)

/-- The sum over the first `j` blocks of the counts of the active candidates of the group `g`. -/
def aggrSum (N g : ℕ) (A : ℕ → Bool) (c : ℕ → ℕ) (j : ℕ) : ℕ :=
  ∑ j' ∈ Finset.range j, if A (j' * N + g) then c (j' * N + g) else 0

theorem aggrSum_succ (N g : ℕ) (A : ℕ → Bool) (c : ℕ → ℕ) (j : ℕ) :
    ((aggrSum N g A c (j + 1) : ℕ) : ℤ) =
      (aggrSum N g A c j : ℤ) + bitB (A (j * N + g)) * (c (j * N + g) : ℤ) := by
  unfold aggrSum
  rw [Finset.sum_range_succ]
  cases A (j * N + g) <;> simp

theorem aggrSum_le (N g : ℕ) (A : ℕ → Bool) {c : ℕ → ℕ} {cmax : ℕ} (j : ℕ)
    (hc : ∀ j' < j, c (j' * N + g) ≤ cmax) : aggrSum N g A c j ≤ j * cmax := by
  unfold aggrSum
  calc _ ≤ ∑ j' ∈ Finset.range j, cmax := Finset.sum_le_sum fun j' hj' => by
        split_ifs
        · exact hc j' (Finset.mem_range.1 hj')
        · exact Nat.zero_le _
    _ = j * cmax := by simp

theorem toNat_lin (a j N g : ℕ) : ((a : ℤ) + (j : ℤ) * (N : ℤ) + (g : ℤ)).toNat = a + (j * N + g) := by
  rw [show (a : ℤ) + (j : ℤ) * (N : ℤ) + (g : ℤ) = ((a + (j * N + g) : ℕ) : ℤ) by push_cast; ring,
    Int.toNat_natCast]

/-- The time of aggr. -/
def tAggr (N m : ℕ) : ℕ := N * (30 * m + 30) + 10

theorem aggrInner_spec {ν : ℕ → ℤ} {cnt act dst N m g cmax : ℕ} {A : ℕ → Bool} {c : ℕ → ℕ}
    (hact : ∀ j < m, ν (act + (j * N + g)) = bitB (A (j * N + g)))
    (hcnt : ∀ j < m, ν (cnt + (j * N + g)) = (c (j * N + g) : ℤ))
    (hc : ∀ j < m, c (j * N + g) ≤ cmax) (hg : g < N)
    (hsa : act + m * N ≤ lim.space) (hsc : cnt + m * N ≤ lim.space)
    (hw : (lim.space : ℤ) ≤ lim.word) (hword : ((m * cmax + m + 1 : ℕ) : ℤ) ≤ lim.word)
    (a7 : ℤ) :
    Ends lim P d aggrInner ⟨frame [cnt, act, dst, N, m, g, 0, a7], ν⟩ (28 * m + 6)
      (· = ⟨frame [cnt, act, dst, N, m, g, (aggrSum N g A c m : ℕ), m], ν⟩) := by
  push_cast at hword
  have hmc : (0 : ℤ) ≤ (m : ℤ) * cmax := by positivity
  refine Ends.for (fun j σ => σ = ⟨frame [cnt, act, dst, N, m, g, (aggrSum N g A c j : ℕ), j], ν⟩)
    m 20 ?start ?round ?done ?bound (by omega) (by simp; omega)
  case start => simp [update_frame_setLocal, aggrSum]
  case bound =>
    rintro j _ - - rfl
    simp
  case done =>
    rintro _ - rfl
    rfl
  case round =>
    rintro j _ hj - rfl
    have hjN : j * N + N ≤ m * N := by
      have := Nat.mul_le_mul_right N (show j + 1 ≤ m by omega)
      rwa [Nat.add_mul, Nat.one_mul] at this
    have hsum := aggrSum_le N g A (j := j + 1) (cmax := cmax) fun j' hj' => hc j' (by omega)
    have hsucc := aggrSum_succ N g A c j
    have hcj := hc j hj
    have hb0 := bitB_nonneg (A (j * N + g))
    have hb1 := bitB_le_one (A (j * N + g))
    have hprod0 : 0 ≤ bitB (A (j * N + g)) * (c (j * N + g) : ℤ) := by positivity
    have hprod1 : bitB (A (j * N + g)) * (c (j * N + g) : ℤ) ≤ cmax := by
      calc bitB (A (j * N + g)) * (c (j * N + g) : ℤ) ≤ 1 * (c (j * N + g) : ℤ) :=
            mul_le_mul_of_nonneg_right hb1 (by positivity)
        _ ≤ cmax := by simpa using hcj
    have hsumZ : ((aggrSum N g A c (j + 1) : ℕ) : ℤ) ≤ ((j + 1) * cmax : ℕ) := by exact_mod_cast hsum
    have hjm : ((j + 1) * cmax : ℕ) ≤ m * cmax := Nat.mul_le_mul_right _ hj
    have hjmZ : (((j + 1) * cmax : ℕ) : ℤ) ≤ ((m * cmax : ℕ) : ℤ) := by exact_mod_cast hjm
    push_cast at hjmZ
    have hA := hact j hj
    have hC := hcnt j hj
    refine Ends.setTo (aggrSum N g A c (j + 1) : ℕ) ?_ ?_ (by light_time)
    · refine ⟨by simp, ?_⟩
      simp [update_frame_setLocal]
    · have ga : (v 1 +' v 7 *' v 3 +' v 5).Gives lim
          ⟨frame [cnt, act, dst, N, m, g, (aggrSum N g A c j : ℕ), j], ν⟩ ((act + (j * N + g) : ℕ) : ℤ) := by
        light_side
      have gc : (v 0 +' v 7 *' v 3 +' v 5).Gives lim
          ⟨frame [cnt, act, dst, N, m, g, (aggrSum N g A c j : ℕ), j], ν⟩ ((cnt + (j * N + g) : ℕ) : ℤ) := by
        light_side
      refine gives_of_eq (gives_op (gives_var _ 6) (gives_op (gives_load ga (by omega) hA)
        (gives_load gc (by omega) hC) ?_) ?_) ?_
      · simp only [Op.eval]
        rw [abs_le]
        constructor <;> omega
      · simp only [Op.eval, frame, List.getD_cons_succ, List.getD_cons_zero]
        rw [abs_le]
        constructor <;> omega
      · simp only [Op.eval, frame, List.getD_cons_succ, List.getD_cons_zero]
        rw [hsucc]

/-- **aggr(cnt, act, dst, N, m)** writes, for every group `g < N`, the sum of the counts of its
active candidates to `dst + g`, and changes no other cell. -/
theorem aggr_meets {μ : ℕ → ℤ} {p cnt act dst N m cmax : ℕ} {A : ℕ → Bool} {c : ℕ → ℕ}
    (hP : P[p]? = some aggrBody)
    (hact : Arr μ act (m * N) fun i => bitB (A i)) (hcnt : Arr μ cnt (m * N) fun i => (c i : ℤ))
    (hc : ∀ i < m * N, c i ≤ cmax)
    (hsa : act + m * N ≤ lim.space) (hsc : cnt + m * N ≤ lim.space) (hsd : dst + N ≤ lim.space)
    (hda : Apart dst N act (m * N)) (hdc : Apart dst N cnt (m * N))
    (hw : (lim.space : ℤ) ≤ lim.word) (hword : ((m * cmax + m + 1 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [cnt, act, dst, N, m] μ (tAggr N m) fun _ μ' =>
      Arr μ' dst N (fun g => (aggrSum N g A c m : ℤ)) ∧ SameOutside μ μ' dst N := by
  refine .of_body hP ?_
  have hmc : (0 : ℤ) ≤ ((m * cmax : ℕ) : ℤ) := by positivity
  have hm1 : (m : ℤ) ≤ lim.word := by push_cast at hword hmc ⊢; omega
  unfold aggrBody tAggr
  refine Ends.next _ (Ends.for (fun g σ => ∃ a6 a7 : ℤ,
      σ = ⟨frame [cnt, act, dst, N, m, g, a6, a7],
        wrote μ dst (fun g => (aggrSum N g A c m : ℤ)) g⟩) N (28 * m + 13)
    ?start ?round ?done ?bound (by omega) le_rfl) (by light_time)
  case start =>
    refine ⟨0, 0, ?_⟩
    rw [wrote_zero]
    simpa [update_frame_setLocal] using
      (frame_append_zeros [(cnt : ℤ), act, dst, N, m, 0] 2).symm
  case bound =>
    rintro g _ - - ⟨a6, a7, rfl⟩
    simp
  case done =>
    rintro _ - ⟨a6, a7, rfl⟩
    refine Ends.setTo 0 ⟨fun g hg => wrote_done (μ := μ) (dst := dst)
        (f := fun g => (aggrSum N g A c m : ℤ)) hg,
      sameOutside_wrote (μ := μ) (dst := dst) (f := fun g => (aggrSum N g A c m : ℤ)) le_rfl⟩
      (by light_side) (by light_time)
  case round =>
    rintro g _ hg - ⟨a6, a7, rfl⟩
    have hν : ∀ i < m * N, ∀ base, (base = act ∨ base = cnt) →
        wrote μ dst (fun g => (aggrSum N g A c m : ℤ)) g (base + i) = μ (base + i) := by
      intro i hi base hb
      refine wrote_rest ?_
      rcases hb with rfl | rfl <;> omega
    have hjN : ∀ j < m, j * N + g < m * N := fun j hj => by
      have := Nat.mul_le_mul_right N (show j + 1 ≤ m by omega)
      rw [Nat.add_mul, Nat.one_mul] at this
      omega
    light_set (0 : ℕ)
    light_piece (aggrInner_spec (A := A) (c := c) (cmax := cmax)
      (fun j hj => (hν _ (hjN j hj) act (Or.inl rfl)).trans (hact _ (hjN j hj)))
      (fun j hj => (hν _ (hjN j hj) cnt (Or.inr rfl)).trans (hcnt _ (hjN j hj)))
      (fun j hj => hc _ (hjN j hj)) hg hsa hsc hw hword a7) with _ rfl
    light_store (dst + g) ((aggrSum N g A c m : ℕ) : ℤ)
    refine ⟨by simp, (aggrSum N g A c m : ℤ), m, ?_⟩
    simp only [update_frame_setLocal, setLocal, Nat.cast_add, Nat.cast_one]
    rw [← wrote_succ (f := fun g => (aggrSum N g A c m : ℤ))]

/-! ## Certification -/

/-- The inner loop of cert: the test of the group `g` against every prime of the pool.
Locals: 0 ua, 1 gt, 2 done, 3 N, 4 Q, 5 h, 6 g, 7 flag, 8 t. -/
def certInner : Stmt :=
  Stmt.for 8 (v 4) (.ite (v 4 *' M (v 1 +' v 8 *' v 3 +' v 6) <' v 5 *' M (v 0 +' v 6) +' k 1)
    (.set 7 (k 0)) .skip)

/-- cert(ua, gt, done, N, Q, h): every group `g < N` that is not done is certified, `done[g] := 1`,
if `h · ua[g] < Q · gt[t N + g]` for every `t < Q`. -/
def certBody : Stmt :=
  Stmt.for 6 (v 3) (.ite (M (v 2 +' v 6) =' k 0)
    (.set 7 (k 1) ;; certInner ;; .store (v 2 +' v 6) (v 7)) .skip) ;;
  .set 0 (k 0)

/-- The time of cert. -/
def tCert (N Q : ℕ) : ℕ := N * (30 * Q + 30) + 10

/-- One more cell is written, with the value that it holds already. -/
theorem wrote_succ_of_eq {μ : ℕ → ℤ} {dst j : ℕ} {f : ℕ → ℤ} (h : μ (dst + j) = f j) :
    wrote μ dst f (j + 1) = wrote μ dst f j := by
  rw [← wrote_succ]
  funext a
  by_cases ha : a = dst + j
  · subst ha
    rw [Function.update_self, wrote_rest (by omega), h]
  · rw [Function.update_of_ne ha]

theorem certInner_spec {ν : ℕ → ℤ} {ua gt done N Q h g Uv vmax : ℕ} {Gv : ℕ → ℕ}
    (hU : ν (ua + g) = Uv) (hG : ∀ t < Q, ν (gt + (t * N + g)) = Gv t)
    (hUb : Uv ≤ vmax) (hGb : ∀ t < Q, Gv t ≤ vmax) (hg : g < N)
    (hsu : ua + N ≤ lim.space) (hsg : gt + Q * N ≤ lim.space)
    (hw : (lim.space : ℤ) ≤ lim.word) (hword : (((Q + h + 1) * (vmax + 1) : ℕ) : ℤ) ≤ lim.word)
    (a8 : ℤ) :
    Ends lim P d certInner ⟨frame [ua, gt, done, N, Q, h, g, 1, a8], ν⟩ (30 * Q + 6)
      (· = ⟨frame [ua, gt, done, N, Q, h, g, bitB (decide (∀ t < Q, h * Uv < Q * Gv t)), Q], ν⟩) := by
  have hb1 : (Q + h + 1) * (vmax + 1) = Q * vmax + h * vmax + Q + h + vmax + 1 := by ring
  have hQv : Q * Uv ≤ Q * vmax := Nat.mul_le_mul_left _ hUb
  have hhv : h * Uv ≤ h * vmax := Nat.mul_le_mul_left _ hUb
  rw [hb1] at hword
  push_cast at hword
  have hQv0 : (0 : ℤ) ≤ (Q : ℤ) * vmax := by positivity
  have hhv0 : (0 : ℤ) ≤ (h : ℤ) * vmax := by positivity
  refine Ends.for (fun t σ => σ = ⟨frame [ua, gt, done, N, Q, h, g,
      bitB (decide (∀ t' < t, h * Uv < Q * Gv t')), t], ν⟩)
    Q 22 ?start ?round ?done ?bound (by omega) (by simp; omega)
  case start => simp [update_frame_setLocal]
  case bound =>
    rintro t _ - - rfl
    simp
  case done =>
    rintro _ - rfl
    rfl
  case round =>
    rintro t _ ht - rfl
    have hjN : t * N + N ≤ Q * N := by
      have := Nat.mul_le_mul_right N (show t + 1 ≤ Q by omega)
      rwa [Nat.add_mul, Nat.one_mul] at this
    have hGt := hG t ht
    have hGbt := hGb t ht
    have hQG : Q * Gv t ≤ Q * vmax := Nat.mul_le_mul_left _ hGbt
    have haddr : ((gt : ℤ) + (t : ℤ) * (N : ℤ) + (g : ℤ)).toNat = gt + (t * N + g) := toNat_lin _ _ _ _
    have hQGZ : ((Q * Gv t : ℕ) : ℤ) ≤ ((Q * vmax : ℕ) : ℤ) := by exact_mod_cast hQG
    have hhUZ : ((h * Uv : ℕ) : ℤ) ≤ ((h * vmax : ℕ) : ℤ) := by exact_mod_cast hhv
    push_cast at hQGZ hhUZ
    have hsucc : (∀ t' < t + 1, h * Uv < Q * Gv t') ↔ (∀ t' < t, h * Uv < Q * Gv t') ∧ h * Uv < Q * Gv t :=
      ⟨fun H => ⟨fun t' ht' => H t' (by omega), H t (by omega)⟩, fun H t' ht' => by
        rcases Nat.lt_succ_iff_lt_or_eq.1 ht' with h' | rfl
        · exact H.1 t' h'
        · exact H.2⟩
    refine Ends.ite 2 ?_ (fun hc => ?_) (fun hc => ?_) (by light_time)
    · light_side [haddr, hGt, hU]
    · -- the test holds: Q · G ≤ h · U, the group fails
      have hc' : Q * Gv t ≤ h * Uv := by
        have : (Q : ℤ) * (Gv t : ℤ) < (h : ℤ) * (Uv : ℤ) + 1 := by
          simpa [haddr, hGt, hU] using hc
        exact_mod_cast (show (Q : ℤ) * (Gv t) ≤ h * Uv by omega)
      refine Ends.setTo 0 ⟨by simp, ?_⟩ (by light_side) (by light_time)
      have hf : decide (∀ t' < t + 1, h * Uv < Q * Gv t') = false := by
        simp only [decide_eq_false_iff_not, hsucc, not_and]
        intro _; omega
      rw [hf]
      simp [update_frame_setLocal]
    · have hc' : h * Uv < Q * Gv t := by
        have : ¬ (Q : ℤ) * (Gv t : ℤ) < (h : ℤ) * (Uv : ℤ) + 1 := by
          simpa [haddr, hGt, hU] using hc
        exact_mod_cast (show (h : ℤ) * Uv < Q * (Gv t) by omega)
      refine Ends.skip ⟨by simp, ?_⟩
      have hf : decide (∀ t' < t + 1, h * Uv < Q * Gv t') = decide (∀ t' < t, h * Uv < Q * Gv t') := by
        simp only [hsucc, hc', and_true]
      rw [hf]
      simp [update_frame_setLocal]

/-- **cert(ua, gt, done, N, Q, h)** marks as done every group that is certified, and changes no
other cell. -/
theorem cert_meets {μ : ℕ → ℤ} {p ua gt done N Q h vmax : ℕ} {D : ℕ → Bool} {Uv : ℕ → ℕ}
    {Gv : ℕ → ℕ → ℕ} (hP : P[p]? = some certBody)
    (hdone : Arr μ done N fun g => bitB (D g))
    (hU : ∀ g < N, D g = false → μ (ua + g) = Uv g)
    (hG : ∀ t < Q, ∀ g < N, μ (gt + (t * N + g)) = Gv t g)
    (hUb : ∀ g < N, Uv g ≤ vmax) (hGb : ∀ t < Q, ∀ g < N, Gv t g ≤ vmax)
    (hsu : ua + N ≤ lim.space) (hsg : gt + Q * N ≤ lim.space) (hsd : done + N ≤ lim.space)
    (hdu : Apart done N ua N) (hdg : Apart done N gt (Q * N))
    (hw : (lim.space : ℤ) ≤ lim.word) (hword : (((Q + h + 1) * (vmax + 1) : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [ua, gt, done, N, Q, h] μ (tCert N Q) fun _ μ' =>
      Arr μ' done N (fun g => bitB (D g || decide (∀ t < Q, h * Uv g < Q * Gv t g))) ∧
        SameOutside μ μ' done N := by
  refine .of_body hP ?_
  have hb1 : (Q + h + 1) * (vmax + 1) = Q * vmax + h * vmax + Q + h + vmax + 1 := by ring
  have hN1 : (N : ℤ) ≤ lim.word := by push_cast at hw; omega
  have hQv0 : (0 : ℤ) ≤ (Q : ℤ) * vmax := by positivity
  have hhv0 : (0 : ℤ) ≤ (h : ℤ) * vmax := by positivity
  have hword' := hword
  rw [hb1] at hword'
  push_cast at hword'
  unfold certBody tCert
  refine Ends.next _ (Ends.for (fun g σ => ∃ a7 a8 : ℤ,
      σ = ⟨frame [ua, gt, done, N, Q, h, g, a7, a8],
        wrote μ done (fun g => bitB (D g || decide (∀ t < Q, h * Uv g < Q * Gv t g))) g⟩)
      N (30 * Q + 20) ?start ?round ?done ?bound (by omega) le_rfl) (by light_time)
  case start =>
    refine ⟨0, 0, ?_⟩
    rw [wrote_zero]
    simpa [update_frame_setLocal] using
      (frame_append_zeros [(ua : ℤ), gt, done, N, Q, h, 0] 2).symm
  case bound =>
    rintro g _ - - ⟨a7, a8, rfl⟩
    simp
  case done =>
    rintro _ - ⟨a7, a8, rfl⟩
    refine Ends.setTo 0 ⟨fun g hg => wrote_done (μ := μ) (dst := done)
        (f := fun g => bitB (D g || decide (∀ t < Q, h * Uv g < Q * Gv t g))) hg,
      sameOutside_wrote (μ := μ) (dst := done)
        (f := fun g => bitB (D g || decide (∀ t < Q, h * Uv g < Q * Gv t g))) le_rfl⟩
      (by light_side) (by light_time)
  case round =>
    rintro g _ hg - ⟨a7, a8, rfl⟩
    set F : ℕ → ℤ := fun g => bitB (D g || decide (∀ t < Q, h * Uv g < Q * Gv t g)) with hF
    have hcell : wrote μ done F g (done + g) = bitB (D g) := by
      rw [wrote_rest (by omega)]
      exact hdone g hg
    have hD0 := bitB_nonneg (D g)
    have hD1 := bitB_le_one (D g)
    refine Ends.ite (30 * Q + 13) (by light_side [hcell]) (fun hc => ?_) (fun hc => ?_)
      (by light_time)
    · -- not done: the test of the group
      have hD : D g = false := bitB_eq_zero.1 (by simpa [hcell] using hc)
      have hUg : wrote μ done F g (ua + g) = Uv g := by
        rw [wrote_rest (by omega)]
        exact hU g hg hD
      have hGg : ∀ t < Q, wrote μ done F g (gt + (t * N + g)) = Gv t g := fun t ht => by
        have : t * N + N ≤ Q * N := by
          have := Nat.mul_le_mul_right N (show t + 1 ≤ Q by omega)
          rwa [Nat.add_mul, Nat.one_mul] at this
        rw [wrote_rest (by omega)]
        exact hG t ht g hg
      light_set (1 : ℕ)
      light_piece (certInner_spec (ν := wrote μ done F g) (Gv := fun t => Gv t g) (vmax := vmax)
        hUg hGg (hUb g hg) (fun t ht => hGb t ht g hg) hg hsu hsg hw hword _) with _ rfl
      have hval : F g = bitB (decide (∀ t < Q, h * Uv g < Q * Gv t g)) := by
        simp [hF, hD]
      have hb0 := bitB_nonneg (decide (∀ t < Q, h * Uv g < Q * Gv t g))
      have hb1 := bitB_le_one (decide (∀ t < Q, h * Uv g < Q * Gv t g))
      light_store (done + g) (F g) using hval
      refine ⟨by simp, bitB (decide (∀ t < Q, h * Uv g < Q * Gv t g)), Q, ?_⟩
      simp only [update_frame_setLocal, setLocal, Nat.cast_add, Nat.cast_one]
      rw [← wrote_succ (f := F)]
    · -- done already
      have hD : D g = true := by
        cases hDg : D g
        · simp [hcell, hDg] at hc
        · rfl
      refine Ends.skip ⟨by simp, a7, a8, ?_⟩
      simp only [update_frame_setLocal, setLocal, Nat.cast_add, Nat.cast_one]
      rw [wrote_succ_of_eq (by rw [hdone g hg]; simp [hF, hD])]

/-! ## The choice of the prime -/

/-- The inner loop of argmin: the remaining mass of the row `t`.
Locals: 0 gt, 1 done, 2 N, 3 Q, 4 t, 5 S, 6 g, 7 best, 8 arg. -/
def argInner : Stmt :=
  Stmt.for 6 (v 2) (.set 5 (v 5 +' (k 1 -' M (v 1 +' v 6)) *' M (v 0 +' v 4 *' v 2 +' v 6)))

/-- argmin(gt, done, N, Q): the first row `t < Q` of least remaining mass
`Σ_{g < N} (1 - done[g]) gt[t N + g]`. -/
def argminBody : Stmt :=
  Stmt.for 4 (v 3) (.set 5 (k 0) ;; argInner ;;
    .ite (v 4 =' k 0) (.set 7 (v 5) ;; .set 8 (v 4))
      (.ite (v 5 <' v 7) (.set 7 (v 5) ;; .set 8 (v 4)) .skip)) ;;
  .set 0 (v 8)

/-- The time of argmin. -/
def tArgmin (N Q : ℕ) : ℕ := Q * (30 * N + 30) + 10

/-- The remaining mass of the first `g` groups in the row `t`. -/
def remSum (D : ℕ → Bool) (Gv : ℕ → ℕ → ℕ) (t g : ℕ) : ℕ :=
  ∑ g' ∈ Finset.range g, if D g' then 0 else Gv t g'

theorem remSum_succ (D : ℕ → Bool) (Gv : ℕ → ℕ → ℕ) (t g : ℕ) :
    ((remSum D Gv t (g + 1) : ℕ) : ℤ) = (remSum D Gv t g : ℤ) + (1 - bitB (D g)) * (Gv t g : ℤ) := by
  unfold remSum
  rw [Finset.sum_range_succ]
  cases D g <;> simp

theorem remSum_le (D : ℕ → Bool) {Gv : ℕ → ℕ → ℕ} {vmax t : ℕ} (g : ℕ)
    (hG : ∀ g' < g, Gv t g' ≤ vmax) : remSum D Gv t g ≤ g * vmax := by
  unfold remSum
  calc _ ≤ ∑ g' ∈ Finset.range g, vmax := Finset.sum_le_sum fun g' hg' => by
        split_ifs
        · exact Nat.zero_le _
        · exact hG g' (Finset.mem_range.1 hg')
    _ = g * vmax := by simp

theorem argInner_spec {μ : ℕ → ℤ} {gt done N Q t vmax : ℕ} {D : ℕ → Bool} {Gv : ℕ → ℕ → ℕ}
    (hdone : Arr μ done N fun g => bitB (D g))
    (hG : ∀ g < N, μ (gt + (t * N + g)) = Gv t g) (hGb : ∀ g < N, Gv t g ≤ vmax)
    (hsd : done + N ≤ lim.space) (hsg : gt + t * N + N ≤ lim.space)
    (hw : (lim.space : ℤ) ≤ lim.word) (hword : ((N * vmax + N + 1 : ℕ) : ℤ) ≤ lim.word)
    (a6 b7 a8 : ℤ) :
    Ends lim P d argInner ⟨frame [gt, done, N, Q, t, 0, a6, b7, a8], μ⟩ (26 * N + 6)
      (· = ⟨frame [gt, done, N, Q, t, (remSum D Gv t N : ℕ), N, b7, a8], μ⟩) := by
  push_cast at hword
  have hNv : (0 : ℤ) ≤ (N : ℤ) * vmax := by positivity
  refine Ends.for (fun g σ => σ = ⟨frame [gt, done, N, Q, t, (remSum D Gv t g : ℕ), g, b7, a8], μ⟩)
    N 18 ?start ?round ?done ?bound (by omega) (by simp; omega)
  case start => simp [update_frame_setLocal, remSum]
  case bound =>
    rintro g _ - - rfl
    simp
  case done =>
    rintro _ - rfl
    rfl
  case round =>
    rintro g _ hg - rfl
    have hsum := remSum_le D (t := t) (vmax := vmax) (Gv := Gv) (g + 1) fun g' hg' => hGb g' (by omega)
    have hsucc := remSum_succ D Gv t g
    have hGg := hGb g hg
    have hb0 := bitB_nonneg (D g)
    have hb1 := bitB_le_one (D g)
    have hprod0 : 0 ≤ (1 - bitB (D g)) * (Gv t g : ℤ) := by
      apply mul_nonneg <;> [omega; positivity]
    have hprod1 : (1 - bitB (D g)) * (Gv t g : ℤ) ≤ vmax := by
      calc (1 - bitB (D g)) * (Gv t g : ℤ) ≤ 1 * (Gv t g : ℤ) :=
            mul_le_mul_of_nonneg_right (by omega) (by positivity)
        _ ≤ vmax := by simpa using hGg
    have hsumZ : ((remSum D Gv t (g + 1) : ℕ) : ℤ) ≤ ((g + 1) * vmax : ℕ) := by exact_mod_cast hsum
    have hjm : ((g + 1) * vmax : ℕ) ≤ N * vmax := Nat.mul_le_mul_right _ hg
    have hjmZ : (((g + 1) * vmax : ℕ) : ℤ) ≤ ((N * vmax : ℕ) : ℤ) := by exact_mod_cast hjm
    push_cast at hjmZ
    have hD := hdone g hg
    have hGt := hG g hg
    refine Ends.setTo (remSum D Gv t (g + 1) : ℕ) ?_ ?_ (by light_time)
    · simp [update_frame_setLocal]
    · have ga : (v 1 +' v 6).Gives lim
          ⟨frame [gt, done, N, Q, t, (remSum D Gv t g : ℕ), g, b7, a8], μ⟩ ((done + g : ℕ) : ℤ) := by
        light_side
      have gc : (v 0 +' v 4 *' v 2 +' v 6).Gives lim
          ⟨frame [gt, done, N, Q, t, (remSum D Gv t g : ℕ), g, b7, a8], μ⟩
          ((gt + (t * N + g) : ℕ) : ℤ) := by
        light_side
      have g1 : (k 1).Gives lim ⟨frame [gt, done, N, Q, t, (remSum D Gv t g : ℕ), g, b7, a8], μ⟩
          ((1 : ℕ) : ℤ) := gives_const _ (by push_cast; omega)
      refine gives_of_eq (gives_op (gives_var _ 5) (gives_op (gives_op g1
        (gives_load ga (by omega) hD) ?_) (gives_load gc (by omega) hGt) ?_) ?_) ?_
      · simp only [Op.eval]
        rw [abs_le]
        constructor <;> omega
      · simp only [Op.eval]
        push_cast
        rw [abs_le]
        constructor <;> omega
      · simp only [Op.eval, frame, List.getD_cons_succ, List.getD_cons_zero]
        push_cast
        rw [abs_le]
        constructor <;> omega
      · simp only [Op.eval, frame, List.getD_cons_succ, List.getD_cons_zero]
        rw [hsucc]
        push_cast
        ring

/-- **argmin(gt, done, N, Q)** returns a row `t* < Q` of least remaining mass (for `Q ≥ 1`), and
changes no cell. -/
theorem argmin_meets {μ : ℕ → ℤ} {p gt done N Q vmax : ℕ} {D : ℕ → Bool} {Gv : ℕ → ℕ → ℕ}
    (hP : P[p]? = some argminBody)
    (hdone : Arr μ done N fun g => bitB (D g))
    (hG : ∀ t < Q, ∀ g < N, μ (gt + (t * N + g)) = Gv t g)
    (hGb : ∀ t < Q, ∀ g < N, Gv t g ≤ vmax)
    (hsd : done + N ≤ lim.space) (hsg : gt + Q * N ≤ lim.space)
    (hw : (lim.space : ℤ) ≤ lim.word) (hword : ((N * vmax + N + Q + 1 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [gt, done, N, Q] μ (tArgmin N Q) fun r μ' => μ' = μ ∧ ∃ ts : ℕ, r = ts ∧
      (0 < Q → ts < Q ∧ ∀ t < Q, remSum D Gv ts N ≤ remSum D Gv t N) := by
  refine .of_body hP ?_
  have hword' : ((N * vmax + N + 1 : ℕ) : ℤ) ≤ lim.word := le_trans (by push_cast; omega) hword
  push_cast at hword
  have hNv : (0 : ℤ) ≤ (N : ℤ) * vmax := by positivity
  unfold argminBody tArgmin
  refine Ends.next _ (Ends.for (fun t σ => ∃ (s5 a6 b7 : ℤ) (arg : ℕ),
      σ = ⟨frame [gt, done, N, Q, t, s5, a6, b7, arg], μ⟩ ∧
        (0 < t → b7 = (remSum D Gv arg N : ℤ) ∧ arg < t ∧ ∀ t' < t, remSum D Gv arg N ≤ remSum D Gv t' N))
      Q (26 * N + 20) ?start ?round ?done ?bound (by omega) le_rfl) (by light_time)
  case start =>
    refine ⟨0, 0, 0, 0, ?_, fun h => absurd h (lt_irrefl 0)⟩
    simpa [update_frame_setLocal] using
      (frame_append_zeros [(gt : ℤ), done, N, Q, 0] 4).symm
  case bound =>
    rintro t _ - - ⟨s5, a6, b7, arg, rfl, -⟩
    simp
  case done =>
    rintro _ - ⟨s5, a6, b7, arg, rfl, hinv⟩
    refine Ends.setTo arg ⟨rfl, arg, rfl, fun hQ => ⟨(hinv hQ).2.1, (hinv hQ).2.2⟩⟩
      (by light_side) (by light_time)
  case round =>
    rintro t _ ht - ⟨s5, a6, b7, arg, rfl, hinv⟩
    have htN : t * N + N ≤ Q * N := by
      have := Nat.mul_le_mul_right N (show t + 1 ≤ Q by omega)
      rwa [Nat.add_mul, Nat.one_mul] at this
    have hSt : remSum D Gv t N ≤ N * vmax := remSum_le D N fun g hg => hGb t ht g hg
    have hStZ : ((remSum D Gv t N : ℕ) : ℤ) ≤ ((N * vmax : ℕ) : ℤ) := by exact_mod_cast hSt
    push_cast at hStZ
    light_set (0 : ℕ)
    light_piece (argInner_spec (Q := Q) (D := D) (Gv := Gv) (vmax := vmax) hdone (hG t ht)
      (hGb t ht) hsd (by omega) hw hword' a6 b7 arg) with _ rfl
    light_if h0 h1 : t = 0
    · -- the first row
      subst h0
      light_set (remSum D Gv 0 N : ℕ)
      light_set (0 : ℕ)
      refine ⟨by simp, (remSum D Gv 0 N : ℕ), N, (remSum D Gv 0 N : ℕ), 0, ?_, fun _ => ⟨rfl, by omega, fun t' ht' => ?_⟩⟩
      · simp [update_frame_setLocal]
      · obtain rfl : t' = 0 := by omega
        exact le_rfl
    · obtain ⟨hb7, harg, hmin⟩ := hinv (by omega)
      light_if h2 h3 : remSum D Gv t N < remSum D Gv arg N using hb7
      · light_set (remSum D Gv t N : ℕ)
        light_set t
        refine ⟨by simp, (remSum D Gv t N : ℕ), N, (remSum D Gv t N : ℕ), t, ?_, fun _ => ⟨rfl, by omega, fun t' ht' => ?_⟩⟩
        · simp [update_frame_setLocal]
        · rcases Nat.lt_succ_iff_lt_or_eq.1 ht' with h' | rfl
          · exact (le_of_lt h2).trans (hmin t' h')
          · exact le_rfl
      · light_skip
        refine ⟨by simp, (remSum D Gv t N : ℕ), N, b7, arg, ?_, fun _ => ⟨hb7, by omega, fun t' ht' => ?_⟩⟩
        · simp [update_frame_setLocal]
        · rcases Nat.lt_succ_iff_lt_or_eq.1 ht' with h' | rfl
          · exact hmin t' h'
          · omega

/-! ## The end of a round -/

/-- filterAct(act, cnt, L): `act[i] := 0` where `cnt[i] = 0`.  Locals: 0 act, 1 cnt, 2 L, 3 i. -/
def filterActBody : Stmt :=
  Stmt.for 3 (v 2) (.ite (M (v 1 +' v 3) =' k 0) (.store (v 0 +' v 3) (k 0)) .skip) ;;
  .set 0 (k 0)

/-- The time of filterAct. -/
def tFilterAct (L : ℕ) : ℕ := 20 * L + 10

/-- **filterAct(act, cnt, L)** keeps the candidates whose count is positive, and changes no other
cell. -/
theorem filterAct_meets {μ : ℕ → ℤ} {p act cnt L : ℕ} {A : ℕ → Bool} {c : ℕ → ℕ}
    (hP : P[p]? = some filterActBody)
    (hact : Arr μ act L fun i => bitB (A i)) (hcnt : Arr μ cnt L fun i => (c i : ℤ))
    (hsa : act + L ≤ lim.space) (hsc : cnt + L ≤ lim.space) (hac : Apart act L cnt L)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : (1 : ℤ) ≤ lim.word) :
    Meets lim P p d [act, cnt, L] μ (tFilterAct L) fun _ μ' =>
      Arr μ' act L (fun i => bitB (A i && decide (0 < c i))) ∧ SameOutside μ μ' act L := by
  refine .of_body hP ?_
  unfold filterActBody tFilterAct
  refine Ends.next _ (Ends.forFrame (fun j μ' => μ' = wrote μ act
      (fun i => bitB (A i && decide (0 < c i))) j) L wrote_zero.symm ?round ?done
    (by intros; light_side) (by omega) le_rfl) (by light_time)
  case done =>
    intro μ' hμ'
    subst hμ'
    refine Ends.setTo 0 ⟨fun i hi => wrote_done (μ := μ) (dst := act)
        (f := fun i => bitB (A i && decide (0 < c i))) hi,
      sameOutside_wrote (μ := μ) (dst := act) (f := fun i => bitB (A i && decide (0 < c i))) le_rfl⟩
      (by light_side) (by light_time)
  case round =>
    intro j μ' hj hμ'
    subst hμ'
    have hc := hcnt j hj
    have hcell : wrote μ act (fun i => bitB (A i && decide (0 < c i))) j (cnt + j) = c j := by
      rw [wrote_rest (by omega)]
      exact hc
    refine Ends.ite _ (by light_side [hcell]) (fun h0 => ?_) (fun h0 => ?_) (by light_time)
    · have hz : c j = 0 := by
        have : (c j : ℤ) = 0 := by simpa [hcell] using h0
        exact_mod_cast this
      refine Ends.storeTo (act + j) 0 ⟨by simp, ?_⟩ (by light_side) (by light_time)
      rw [← wrote_succ]
      simp [hz]
    · have hz : 0 < c j := by
        have : (c j : ℤ) ≠ 0 := by simpa [hcell] using h0
        omega
      refine Ends.skip ⟨by simp, ?_⟩
      rw [wrote_succ_of_eq (by rw [hact j hj]; simp [hz])]

/-! ## The pool -/

/-- poolFilter(src, c, R, dst): the entries `≥ R` of the `c` cells from `src` are written, in their
order, to the cells from `dst`; it returns their number.
Locals: 0 src, 1 c, 2 R, 3 dst, 4 i, 5 the number so far. -/
def poolFilterBody : Stmt :=
  Stmt.for 4 (v 1) (.ite (v 2 ≤' M (v 0 +' v 4))
    (.store (v 3 +' v 5) (M (v 0 +' v 4)) ;; .set 5 (v 5 +' k 1)) .skip) ;;
  .set 0 (v 5)

/-- The time of poolFilter. -/
def tPoolFilter (c : ℕ) : ℕ := 30 * c + 10

theorem take_succ_filter (l : List ℕ) (p : ℕ → Bool) {i : ℕ} (hi : i < l.length) :
    (l.take (i + 1)).filter p = (l.take i).filter p ++ (if p l[i] then [l[i]] else []) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.filter_append]
  congr 1
  by_cases h : p l[i] <;> simp [h]

theorem length_take_filter_le (l : List ℕ) (p : ℕ → Bool) (i : ℕ) :
    ((l.take i).filter p).length ≤ i :=
  (List.length_filter_le _ _).trans (List.length_take_le _ _)

/-- **poolFilter(src, c, R, dst)** writes the entries `≥ R` of the list at `src` to `dst`, returns
their number, and changes no cell outside the `c` cells from `dst`. -/
theorem poolFilter_meets {μ : ℕ → ℤ} {p src c R dst W : ℕ} {l : List ℕ}
    (hP : P[p]? = some poolFilterBody) (hsrc : SegN μ src l) (hlen : l.length = c)
    (hl : ∀ x ∈ l, x < W)
    (hss : src + c ≤ lim.space) (hsd : dst + c ≤ lim.space) (hap : Apart src c dst c)
    (hw : (lim.space : ℤ) ≤ lim.word) (hword : ((R + W + 1 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [src, c, R, dst] μ (tPoolFilter c) fun r μ' =>
      r = ((l.filter fun q => decide (R ≤ q)).length : ℤ) ∧
        SegN μ' dst (l.filter fun q => decide (R ≤ q)) ∧ SameOutside μ μ' dst c := by
  refine .of_body hP ?_
  subst hlen
  push_cast at hword
  unfold poolFilterBody tPoolFilter
  refine Ends.next _ (Ends.for (fun i σ => ∃ μ', σ = ⟨frame [src, l.length, R, dst, i,
      (((l.take i).filter fun q => decide (R ≤ q)).length : ℕ)], μ'⟩ ∧
      SegN μ' dst ((l.take i).filter fun q => decide (R ≤ q)) ∧ SameOutside μ μ' dst l.length)
    l.length 21 ?start ?round ?done ?bound (by omega) le_rfl) (by light_time)
  case start =>
    refine ⟨μ, ?_, by simp [SegN], SameOn.refl⟩
    simpa [update_frame_setLocal] using (frame_append_zeros [(src : ℤ), l.length, R, dst, 0] 1).symm
  case bound =>
    rintro i _ - - ⟨μ', rfl, -⟩
    simp
  case done =>
    rintro _ - ⟨μ', rfl, hseg, hsame⟩
    rw [List.take_length] at hseg ⊢
    exact Ends.setTo _ ⟨rfl, hseg, hsame⟩ (by light_side) (by light_time)
  case round =>
    rintro i _ hi - ⟨μ', rfl, hseg, hsame⟩
    have hil : i < l.length := by omega
    have hread : μ' (src + i) = (l[i] : ℤ) := by
      rw [hsame _ (by omega)]
      exact hsrc.getElem hil
    have hW : l[i] < W := hl _ (List.getElem_mem hil)
    have hlenF := length_take_filter_le l (fun q => decide (R ≤ q)) i
    have hstep := take_succ_filter l (fun q => decide (R ≤ q)) hil
    refine Ends.ite 12 (by light_side [hread]) (fun hc => ?_) (fun hc => ?_) (by light_time)
    · have hc' : R ≤ l[i] := by
        have : (R : ℤ) < (l[i] : ℤ) + 1 := by simpa [hread] using hc
        omega
      simp only [hc', decide_true, if_true] at hstep
      refine Ends.storeToThen (dst + ((l.take i).filter fun q => decide (R ≤ q)).length) (l[i] : ℤ)
        ?_ (by light_side [hread]) (by light_time)
      refine Ends.setTo (((l.take i).filter fun q => decide (R ≤ q)).length + 1 : ℕ) ⟨by simp, ?_⟩
        (by light_side) (by light_time)
      refine ⟨Function.update μ' (dst + ((l.take i).filter fun q => decide (R ≤ q)).length)
        (l[i] : ℤ), ?_, ?_, hsame.update (by omega) _⟩
      · simp [update_frame_setLocal, hstep]
      · rw [hstep]
        exact hseg.snoc l[i]
    · have hc' : ¬ R ≤ l[i] := by
        have : ¬ (R : ℤ) < (l[i] : ℤ) + 1 := by simpa [hread] using hc
        omega
      simp only [hc', decide_false] at hstep
      refine Ends.skip ⟨by simp, μ', ?_, ?_, hsame⟩
      · simp [update_frame_setLocal, hstep]
      · rw [hstep]
        simpa using hseg

end Light.Filter2
