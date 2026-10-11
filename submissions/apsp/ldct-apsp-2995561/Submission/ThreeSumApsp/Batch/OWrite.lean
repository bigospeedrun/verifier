/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Batch.OSpecs

/-!
# The batched counting oracle: writeSrc

`writeSrc_ok`: the procedure writeSrc (82) meets `WriteSrcSpec`.

It clears the source, then runs through the tuples `(u, a, l, cl)` (the product, the two digits of
the row `R = a k + l`, the vertex of the middle block) and marks one cell for each.  `Cells` says that
the cells of the source hold 1 exactly at the marks of the tuples handled so far (`marks`, with the
lexicographic order `lexBefore`), and the end identifies the marks of all tuples with `srcVal = 1`.
-/

@[expose] public section

namespace Light.Batch

open ThreeSumApsp ThreeSumApsp.Batch Light.Sec4

/-! ## The tuples and their cells -/

/-- The length of the middle block from `c`: `min s (n - c)`, as the program computes it. -/
def wsLen (n s c : ℕ) : ℕ := if c + s ≤ n then s else n - c

/-- The residue of the tuple `(u, a, l, cl)`. -/
def wsF (n p s j0 : ℕ) (T1 T2 : List ℕ) (u a l cl : ℕ) : ℕ :=
  (T1.getD (a * n + (j0 + u) * s + cl) 0 + T2.getD l 0) % p

/-- The cell (from base) that the tuple `(u, a, l, cl)` marks. -/
def wsPos (n k p s j0 D KK N0 : ℕ) (T1 T2 : List ℕ) (u a l cl : ℕ) : ℕ :=
  srcOf KK N0 u (a * k + l) * D + (cl * p + wsF n p s j0 T1 T2 u a l cl)

/-- The tuples that the loops run through. -/
def WsOk (n k s j0 KKb : ℕ) (u a l cl : ℕ) : Prop :=
  u < KKb ∧ a < n ∧ l < k ∧ cl < wsLen n s ((j0 + u) * s)

/-- The tuple `(u', a', l', cl')` comes before `(u, a, l, cl)`. -/
def lexBefore (u a l cl : ℕ) (u' a' l' cl' : ℕ) : Prop :=
  u' < u ∨ (u' = u ∧ (a' < a ∨ (a' = a ∧ (l' < l ∨ (l' = l ∧ cl' < cl)))))

/-- The cell `i` is the cell of a tuple of `ok` that satisfies `dn`. -/
def marks (ok : ℕ → ℕ → ℕ → ℕ → Prop) (pos : ℕ → ℕ → ℕ → ℕ → ℕ)
    (dn : ℕ → ℕ → ℕ → ℕ → Prop) (i : ℕ) : Prop :=
  ∃ u a l cl, ok u a l cl ∧ dn u a l cl ∧ pos u a l cl = i

section marksLemmas

variable {ok : ℕ → ℕ → ℕ → ℕ → Prop} {pos : ℕ → ℕ → ℕ → ℕ → ℕ}

theorem marks_congr {dn dn' : ℕ → ℕ → ℕ → ℕ → Prop}
    (h : ∀ u a l cl, ok u a l cl → (dn u a l cl ↔ dn' u a l cl)) (i : ℕ) :
    marks ok pos dn i ↔ marks ok pos dn' i := by
  constructor
  · rintro ⟨u, a, l, cl, h1, h2, h3⟩
    exact ⟨u, a, l, cl, h1, (h _ _ _ _ h1).1 h2, h3⟩
  · rintro ⟨u, a, l, cl, h1, h2, h3⟩
    exact ⟨u, a, l, cl, h1, (h _ _ _ _ h1).2 h2, h3⟩

theorem marks_step {u a l cl : ℕ} (hok : ok u a l cl) (i : ℕ) :
    marks ok pos (lexBefore u a l (cl + 1)) i ↔
      marks ok pos (lexBefore u a l cl) i ∨ i = pos u a l cl := by
  unfold lexBefore
  constructor
  · rintro ⟨u', a', l', cl', h1, h2, h3⟩
    by_cases e : u' = u ∧ a' = a ∧ l' = l ∧ cl' = cl
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := e
      exact Or.inr h3.symm
    · exact Or.inl ⟨u', a', l', cl', h1, by omega, h3⟩
  · rintro (⟨u', a', l', cl', h1, h2, h3⟩ | rfl)
    · exact ⟨u', a', l', cl', h1, by omega, h3⟩
    · exact ⟨u, a, l, cl, hok, by omega, rfl⟩

theorem marks_none (i : ℕ) : ¬ marks ok pos (lexBefore 0 0 0 0) i := by
  rintro ⟨u', a', l', cl', -, h2, -⟩
  unfold lexBefore at h2
  omega

end marksLemmas

/-! ## The cells of the source -/

/-- The `sz` cells from base hold 1 at the cells of `S` and 0 at the others; no other cell has
changed. -/
def Cells (μ μ' : ℕ → ℤ) (base sz : ℕ) (S : ℕ → Prop) : Prop :=
  (∀ i < sz, (S i → μ' (base + i) = 1) ∧ (¬ S i → μ' (base + i) = 0)) ∧
    SameOutside μ μ' base sz

theorem Cells.congr {μ μ' : ℕ → ℤ} {base sz : ℕ} {S S' : ℕ → Prop} (h : Cells μ μ' base sz S)
    (hS : ∀ i, S i ↔ S' i) : Cells μ μ' base sz S' :=
  ⟨fun i hi => ⟨fun h' => (h.1 i hi).1 ((hS i).2 h'), fun h' => (h.1 i hi).2 fun h'' =>
    h' ((hS i).1 h'')⟩, h.2⟩

theorem Cells.step {μ μ' : ℕ → ℤ} {base sz c : ℕ} {S : ℕ → Prop} (h : Cells μ μ' base sz S)
    (hc : c < sz) : Cells μ (Function.update μ' (base + c) 1) base sz fun i => S i ∨ i = c := by
  refine ⟨fun i hi => ⟨fun h' => ?_, fun h' => ?_⟩, h.2.write (by omega) _⟩
  · by_cases e : i = c
    · rw [e, Function.update_self]
    · rw [Function.update_of_ne (by omega)]
      exact (h.1 i hi).1 (h'.resolve_right e)
  · rw [Function.update_of_ne (by omega)]
    exact (h.1 i hi).2 fun h'' => h' (Or.inl h'')

/-! ## The end: the marks are the entries 1 of the source -/

theorem divmod_unique {D x y r r' : ℕ} (hr : r < D) (hr' : r' < D) (h : x * D + r = y * D + r') :
    x = y ∧ r = r' := by
  have h1 : (x * D + r) / D = x := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hr, Nat.zero_add]
  have h2 : (y * D + r') / D = y := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hr', Nat.zero_add]
  have hxy : x = y := by rw [← h1, h, h2]
  subst hxy
  exact ⟨rfl, by omega⟩

theorem srcOf_rowU_rowR (KK N0 ρ : ℕ) (hN0 : 0 < N0) :
    srcOf KK N0 (rowU KK N0 ρ) (rowR KK N0 ρ) = ρ := by
  unfold srcOf rowU rowR
  have h1 : (ρ / N0 / KK * N0 + ρ % N0) / N0 = ρ / N0 / KK := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hN0, Nat.div_eq_of_lt (Nat.mod_lt _ hN0),
      Nat.zero_add]
  have h2 : (ρ / N0 / KK * N0 + ρ % N0) % N0 = ρ % N0 := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_mod]
  rw [h1, h2, Nat.div_add_mod' (ρ / N0) KK, Nat.div_add_mod' ρ N0]

/-- The residue of a tuple is `fGen`. -/
theorem fGen_eq_wsF {n s p k KK bt : ℕ} {T1 T2 : List ℕ} (hk : 0 < k) {u a l cl : ℕ} (hl : l < k) :
    fGen n s p k KK bt (fun q => T1.getD q 0) (fun l => T2.getD l 0) u (a * k + l) cl =
      wsF n p s (bt * KK) T1 T2 u a l cl := by
  have hR1 : (a * k + l) / k = a := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hk, Nat.div_eq_of_lt hl, Nat.zero_add]
  have hR2 : (a * k + l) % k = l := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hl]
  unfold fGen wsF
  rw [hR1, hR2, Nat.add_assoc (a * n)]

/-- **The marks of all tuples are the entries 1 of the source.** -/
theorem marks_iff {n k p s D KK N0 KKb bt : ℕ} {T1 T2 : List ℕ} (hk : 0 < k) (hp : 0 < p)
    (hN0 : 0 < N0) (hKKb : KKb ≤ KK) (hsp : s * p ≤ D) {ρ κ : ℕ} (hκ : κ < D) :
    marks (WsOk n k s (bt * KK) KKb) (wsPos n k p s (bt * KK) D KK N0 T1 T2)
        (fun _ _ _ _ => True) (ρ * D + κ) ↔
      (κ / p < s ∧ okX n s k (bt * KK + KKb) KK bt (rowU KK N0 ρ) (rowR KK N0 ρ) (κ / p) = true ∧
        κ % p = fGen n s p k KK bt (fun q => T1.getD q 0) (fun l => T2.getD l 0)
          (rowU KK N0 ρ) (rowR KK N0 ρ) (κ / p)) := by
  constructor
  · rintro ⟨u, a, l, cl, ⟨hu, ha, hl, hcl⟩, -, hpos⟩
    unfold wsPos at hpos
    have hf : wsF n p s (bt * KK) T1 T2 u a l cl < p := Nat.mod_lt _ hp
    have hcs : cl < s := by unfold wsLen at hcl; split_ifs at hcl <;> omega
    have hclp : cl * p + wsF n p s (bt * KK) T1 T2 u a l cl < D :=
      (Nat.mul_add_lt_mul hcs hf).trans_le hsp
    obtain ⟨rfl, rfl⟩ := divmod_unique hclp hκ hpos
    obtain ⟨hdiv, hmod⟩ : (cl * p + wsF n p s (bt * KK) T1 T2 u a l cl) / p = cl ∧
        (cl * p + wsF n p s (bt * KK) T1 T2 u a l cl) % p = wsF n p s (bt * KK) T1 T2 u a l cl := by
      refine ⟨?_, ?_⟩
      · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hf, Nat.zero_add]
      · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hf]
    have huK : u < KK := by omega
    rw [hdiv, hmod, rowU_srcOf huK hN0, rowR_srcOf huK hN0, fGen_eq_wsF hk hl]
    have hR1 : (a * k + l) / k = a := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hk, Nat.div_eq_of_lt hl, Nat.zero_add]
    refine ⟨hcs, ?_, rfl⟩
    simp only [okX, jOf, hR1, decide_eq_true_eq]
    unfold wsLen at hcl
    split_ifs at hcl with hc
    · exact ⟨by omega, ha, by omega⟩
    · exact ⟨by omega, ha, by omega⟩
  · rintro ⟨hcs, hok, hf⟩
    simp only [okX, jOf, decide_eq_true_eq] at hok
    obtain ⟨hu, ha, hc⟩ := hok
    set u := rowU KK N0 ρ
    set R := rowR KK N0 ρ
    have hl : R % k < k := Nat.mod_lt _ hk
    have hR : R / k * k + R % k = R := Nat.div_add_mod' R k
    refine ⟨u, R / k, R % k, κ / p, ⟨by omega, ha, hl, ?_⟩, trivial, ?_⟩
    · unfold wsLen
      split_ifs <;> omega
    · unfold wsPos
      rw [← fGen_eq_wsF hk hl, hR, ← hf, Nat.div_add_mod' κ p, srcOf_rowU_rowR KK N0 ρ hN0]

/-- `srcVal` is 1 or 0. -/
theorem srcVal_eq {s p KK N0 : ℕ} {ok : ℕ → ℕ → ℕ → Bool} {f : ℕ → ℕ → ℕ → ℕ} {ρ κ : ℕ}
    (q : Prop) (hq : q ↔ (κ / p < s ∧ ok (rowU KK N0 ρ) (rowR KK N0 ρ) (κ / p) = true ∧
      κ % p = f (rowU KK N0 ρ) (rowR KK N0 ρ) (κ / p))) :
    (q → srcVal s p KK N0 ok f ρ κ = 1) ∧ (¬ q → srcVal s p KK N0 ok f ρ κ = 0) := by
  unfold srcVal
  constructor
  · intro h; rw [if_pos (hq.1 h)]
  · intro h; rw [if_neg fun h' => h (hq.2 h')]

/-! ## The locals of writeSrc -/

/-- The arguments of writeSrc stand in the locals 0 to 12. -/
def WsArgs (loc : ℕ → ℤ) (base t1 t2 rs n k p D N0 j0 KKb s sz : ℕ) : Prop :=
  loc 0 = base ∧ loc 1 = t1 ∧ loc 2 = t2 ∧ loc 3 = rs ∧ loc 4 = n ∧ loc 5 = k ∧ loc 6 = p ∧
    loc 7 = D ∧ loc 8 = N0 ∧ loc 9 = j0 ∧ loc 10 = KKb ∧ loc 11 = s ∧ loc 12 = sz

theorem WsArgs.update {loc : ℕ → ℤ} {base t1 t2 rs n k p D N0 j0 KKb s sz : ℕ}
    (h : WsArgs loc base t1 t2 rs n k p D N0 j0 KKb s sz) {x : ℕ} (hx : 13 ≤ x) (z : ℤ) :
    WsArgs (Function.update loc x z) base t1 t2 rs n k p D N0 j0 KKb s sz := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [Function.update_of_ne (by omega)] <;> assumption

theorem WsArgs.congr {loc loc' : ℕ → ℤ} {base t1 t2 rs n k p D N0 j0 KKb s sz : ℕ}
    (h : WsArgs loc base t1 t2 rs n k p D N0 j0 KKb s sz) (he : ∀ x, x < 13 → loc' x = loc x) :
    WsArgs loc' base t1 t2 rs n k p D N0 j0 KKb s sz := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [he _ (by omega)] <;> assumption

theorem getD_lt_of_mem {L : List ℕ} {p i : ℕ} (h : ∀ x ∈ L, x < p) (hi : i < L.length) :
    L.getD i 0 < p := by
  rw [List.getD_eq_getElem _ 0 hi]
  exact h _ (List.getElem_mem hi)

section prog

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
  {base t1 t2 rs n kd p D N0 j0 KKb s KK NP : ℕ} {T1 T2 : List ℕ}

/-- The row of a tuple lies in the source. -/
theorem srcOf_lt_rows (pre : WriteSrcPre lim μ base t1 t2 rs n kd p D N0 j0 KKb s KK NP T1 T2)
    {u a l : ℕ} (hu : u < KKb) (ha : a < n) (hl : l < kd) :
    srcOf KK N0 u (a * kd + l) < KK * NP := by
  obtain ⟨c, hc⟩ := pre.NP_mul
  have hR : a * kd + l < n * kd := Nat.mul_add_lt_mul ha hl
  have hnk := pre.nk_le
  have := srcOf_lt (KK := KK) (N0 := N0) (nb := c) (u := u) (R := a * kd + l)
    (by have := pre.KKb_le; omega) (by rw [Nat.mul_comm c N0, ← hc]; omega)
  rwa [Nat.mul_comm c N0, ← hc] at this

open WS in
/-- **One cell**: the tuple `(u, a, l, cl)` marks its cell. -/
theorem wsCell_ok (pre : WriteSrcPre lim μ base t1 t2 rs n kd p D N0 j0 KKb s KK NP T1 T2)
    {u a l cl : ℕ} (hok : WsOk n kd s j0 KKb u a l cl) {loc μ' : ℕ → ℤ}
    (hA : WsArgs loc base t1 t2 rs n kd p D N0 j0 KKb s (KK * NP * D))
    (h14 : loc 14 = a) (h15 : loc 15 = l) (h16 : loc 16 = cl) (h17 : loc 17 = ((j0 + u) * s : ℕ))
    (h20 : loc 20 = ((base + srcOf KK N0 u (a * kd + l) * D : ℕ) : ℤ))
    (hrest : SameOutside μ μ' base (KK * NP * D)) :
    Ends lim P d writeSrcCell ⟨loc, μ'⟩ 33 fun σ' =>
      σ'.mem = Function.update μ' (base + wsPos n kd p s j0 D KK N0 T1 T2 u a l cl) 1 ∧
      ∀ x, x ≠ 19 → σ'.loc x = loc x := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hA
  obtain ⟨hu, ha, hl, hcl⟩ := hok
  have hstd := pre.std
  have hw1 := hstd.space_le
  have hw2 := hstd.const_le
  have hword := pre.word
  have hblk := pre.blocks u hu
  have hsp := pre.sp_le
  have hspace := pre.space
  have hap1 := pre.apart1
  have hap2 := pre.apart2
  have hb1 := pre.below1
  have hb2 := pre.below2
  have hp := pre.p_pos
  have hcs : cl < s ∧ (j0 + u) * s + cl < n := by
    unfold wsLen at hcl; split_ifs at hcl <;> omega
  have hidx : a * n + ((j0 + u) * s + cl) < n * n := Nat.mul_add_lt_mul ha hcs.2
  have hread1 : μ' (t1 + (a * n + (j0 + u) * s + cl)) =
      ((T1.getD (a * n + (j0 + u) * s + cl) 0 : ℕ) : ℤ) := by
    rw [hrest _ (by omega)]
    exact pre.seg1.read (by rw [pre.len1]; omega)
  have hread2 : μ' (t2 + l) = ((T2.getD l 0 : ℕ) : ℤ) := by
    rw [hrest _ (by omega)]
    exact pre.seg2.read (by rw [pre.len2]; omega)
  have hv1 : T1.getD (a * n + (j0 + u) * s + cl) 0 < p :=
    getD_lt_of_mem pre.lt1 (by rw [pre.len1]; omega)
  have hv2 : T2.getD l 0 < p := getD_lt_of_mem pre.lt2 (by rw [pre.len2]; omega)
  have hsrc := srcOf_lt_rows pre hu ha hl
  have hrowD : srcOf KK N0 u (a * kd + l) * D + D ≤ KK * NP * D := by
    have := Nat.mul_le_mul_right D hsrc
    rw [Nat.succ_mul] at this
    exact this
  have hwsF : wsF n p s j0 T1 T2 u a l cl =
      (T1.getD (a * n + (j0 + u) * s + cl) 0 + T2.getD l 0) % p := rfl
  have hcp : ∀ t < p, cl * p + t < D := fun t ht =>
    (Nat.mul_add_lt_mul hcs.1 ht).trans_le hsp
  have han : a * n ≤ n * n := Nat.mul_le_mul_right n ha.le
  unfold wsPos
  rw [hwsF]
  generalize srcOf KK N0 u (a * kd + l) = ρ at *
  generalize (j0 + u) * s = c0 at *
  generalize T1.getD (a * n + c0 + cl) 0 = v1 at *
  generalize T2.getD l 0 = v2 at *
  have hcpp := hcp ((v1 + v2) % p) (Nat.mod_lt _ (by omega))
  have hmod : (v1 + v2) % p = if v1 + v2 < p then v1 + v2 else v1 + v2 - p := by
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  -- the store, once the temporary holds the residue
  generalize (v1 + v2) % p = t at *
  have haddr1 : ((t1 : ℤ) + a * n + c0 + cl).toNat = t1 + (a * n + c0 + cl) := by omega
  have haddr2 : ((t2 : ℤ) + l).toNat = t2 + l := by omega
  -- the store, once the temporary holds the residue
  have mark : ∀ (loc' : ℕ → ℤ), loc' 19 = (t : ℤ) → (∀ x, x ≠ 19 → loc' x = loc x) →
      Ends lim P d (.store (v Row +' v Cl *' v Pr +' v Tmp) (k 1)) ⟨loc', μ'⟩ 9 fun σ' =>
        σ'.mem = Function.update μ' (base + (ρ * D + (cl * p + t))) 1 ∧
        ∀ x, x ≠ 19 → σ'.loc x = loc x := by
    intro loc' h19 hrest'
    have e20 := hrest' 20 (by omega)
    have e16 := hrest' 16 (by omega)
    have e6 := hrest' 6 (by omega)
    refine Ends.storeLast ⟨?_, hrest'⟩ ?_ (by light_time)
    · simp only [Expr.val, Op.eval, e20, e16, e6, h19, h20, h16, h6]
      congr 1
      · push_cast
        omega
    · simp only [Expr.Safe, Expr.val, Op.eval, e20, e16, e6, h19, h20, h16, h6, Limits.Addr,
        abs_le]
      have := Nat.mul_le_mul_right p hcs.1.le
      push_cast
      simp only [true_and]
      refine ⟨⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_, ?_⟩
      all_goals first | trivial | omega
  unfold writeSrcCell
  refine Ends.setValThen ((v1 + v2 : ℕ) : ℤ) ?_ ?_ (by light_time)
  · refine Ends.iteThen (fun hc => ?_) (fun hc => ?_) ?_ (by light_time)
    · simp only [Cond.Holds, Expr.val, Function.update_self, Function.update_of_ne
        (show (6 : ℕ) ≠ 19 by omega), h6] at hc
      have ht : t = v1 + v2 := by rw [hmod, if_pos (by omega)]
      refine Ends.skipThen ((mark _ (by simp [ht]) fun x hx => ?_).mono (by light_time) fun _ h => h)
      rw [Function.update_of_ne hx]
    · simp only [Cond.Holds, Expr.val, Function.update_self, Function.update_of_ne
        (show (6 : ℕ) ≠ 19 by omega), h6] at hc
      have ht : t = v1 + v2 - p := by rw [hmod, if_neg (by omega)]
      refine Ends.setValThen ((v1 + v2 - p : ℕ) : ℤ)
        ((mark _ (by simp [ht]) fun x hx => ?_).mono (by light_time) fun _ h => h) ?_
        (by light_time)
      · rw [Function.update_of_ne hx, Function.update_of_ne hx]
      · simp only [Expr.Gives, Expr.Safe, Expr.val, Op.eval, Function.update_self,
          Function.update_of_ne (show (6 : ℕ) ≠ 19 by omega), h6, abs_le, true_and]
        push_cast
        repeat' apply And.intro
        all_goals omega
    · simp only [Cond.Safe, Expr.Safe]
      exact ⟨trivial, trivial⟩
  · simp only [Expr.Gives, Expr.Safe, Expr.val, Op.eval, h1, h14, h4, h17, h16, h2, h15,
      Limits.Addr, abs_le, haddr1, haddr2, hread1, hread2, true_and]
    push_cast
    repeat' apply And.intro
    all_goals omega

theorem wsLen_le (n s c : ℕ) : wsLen n s c ≤ s := by
  unfold wsLen; split_ifs <;> omega

/-- The cell of a tuple lies in the source. -/
theorem wsPos_lt (pre : WriteSrcPre lim μ base t1 t2 rs n kd p D N0 j0 KKb s KK NP T1 T2)
    {u a l cl : ℕ} (hok : WsOk n kd s j0 KKb u a l cl) :
    wsPos n kd p s j0 D KK N0 T1 T2 u a l cl < KK * NP * D := by
  obtain ⟨hu, ha, hl, hcl⟩ := hok
  have hsrc := srcOf_lt_rows pre hu ha hl
  have hrowD : srcOf KK N0 u (a * kd + l) * D + D ≤ KK * NP * D := by
    have := Nat.mul_le_mul_right D hsrc
    rw [Nat.succ_mul] at this
    exact this
  have hcp : cl * p + wsF n p s j0 T1 T2 u a l cl < D :=
    (Nat.mul_add_lt_mul ((wsLen_le n s _).trans_lt' hcl) (Nat.mod_lt _ (by have := pre.p_pos; omega))).trans_le
      pre.sp_le
  unfold wsPos
  omega

/-- The numbers of the loops fit in a word. -/
theorem wsWord (pre : WriteSrcPre lim μ base t1 t2 rs n kd p D N0 j0 KKb s KK NP T1 T2) :
    (s : ℤ) ≤ lim.word ∧ (n : ℤ) ≤ lim.word ∧ (kd : ℤ) ≤ lim.word ∧ (KKb : ℤ) ≤ lim.word := by
  have hword := pre.word
  have h1 : s ≤ (j0 + KKb + 1) * (s + 1) := by nlinarith
  have h2 : KKb ≤ (j0 + KKb + 1) * (s + 1) := by nlinarith
  have h3 : n ≤ n * n + 1 := by nlinarith
  have hb2 := pre.below2
  have hw := pre.std.space_le
  have hle : ∀ x : ℕ, x ≤ (j0 + KKb + 1) * (s + 1) + n * n + n * kd + 2 * p + 4 →
      (x : ℤ) ≤ lim.word := fun x hx => le_trans (by exact_mod_cast hx) hword
  exact ⟨hle s (by omega), hle n (by omega), by omega, hle KKb (by omega)⟩

open WS in
/-- **One row**: the row `R = a k + l` of the product `u` marks the cells of its tuples. -/
theorem wsRow_ok (pre : WriteSrcPre lim μ base t1 t2 rs n kd p D N0 j0 KKb s KK NP T1 T2)
    (hD : 1 ≤ D) {u a l : ℕ} (hu : u < KKb) (ha : a < n) (hl : l < kd) {loc μ' : ℕ → ℤ}
    (hA : WsArgs loc base t1 t2 rs n kd p D N0 j0 KKb s (KK * NP * D))
    (h13 : loc 13 = u) (h14 : loc 14 = a) (h15 : loc 15 = l) (h17 : loc 17 = ((j0 + u) * s : ℕ))
    (h18 : loc 18 = (wsLen n s ((j0 + u) * s) : ℕ))
    (hC : Cells μ μ' base (KK * NP * D)
      (marks (WsOk n kd s j0 KKb) (wsPos n kd p s j0 D KK N0 T1 T2) (lexBefore u a l 0))) :
    Ends lim P d writeSrcRow ⟨loc, μ'⟩ (41 * s + 23) fun σ' =>
      Cells μ σ'.mem base (KK * NP * D)
        (marks (WsOk n kd s j0 KKb) (wsPos n kd p s j0 D KK N0 T1 T2) (lexBefore u a (l + 1) 0)) ∧
      ∀ x, x ≠ 16 → x ≠ 19 → x ≠ 20 → σ'.loc x = loc x := by
  have hA' := hA
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hA'
  have hls := wsLen_le n s ((j0 + u) * s)
  obtain ⟨hws, hwn, hwk, hwK⟩ := wsWord pre
  unfold writeSrcRow
  refine Ends.setValThen ((base + srcOf KK N0 u (a * kd + l) * D : ℕ) : ℤ) ?_ ?_ (by light_time)
  · refine Ends.for (fun j σ => (∀ x, x ≠ 16 → x ≠ 19 → σ.loc x =
        Function.update loc 20 ((base + srcOf KK N0 u (a * kd + l) * D : ℕ) : ℤ) x) ∧
        Cells μ σ.mem base (KK * NP * D) (marks (WsOk n kd s j0 KKb)
          (wsPos n kd p s j0 D KK N0 T1 T2) (lexBefore u a l j)))
      (wsLen n s ((j0 + u) * s)) 33 ⟨fun x hx _ => Function.update_of_ne hx _ _, hC⟩
      ?round ?done ?bound (by omega) (by simp only [Expr.cost]; omega)
    case bound =>
      rintro j ⟨loc', μ''⟩ - - ⟨hl', -⟩
      dsimp only at hl'
      refine ⟨trivial, ?_⟩
      simp only [Expr.val]
      rw [hl' 18 (by omega) (by omega), Function.update_of_ne (by omega), h18]
    case done =>
      rintro ⟨loc', μ''⟩ - ⟨hl', hc'⟩
      dsimp only at hl'
      refine ⟨hc'.congr (marks_congr ?_), fun x h16 h19 h20 => ?_⟩
      · rintro u' a' l' cl' ⟨-, -, -, hcl'⟩
        unfold lexBefore
        rcases eq_or_ne u' u with rfl | hne
        · constructor <;> intro h <;> omega
        · constructor <;> intro h <;> omega
      · show loc' x = loc x
        rw [hl' x h16 h19, Function.update_of_ne h20]
    case round =>
      rintro j ⟨loc', μ''⟩ hj hc ⟨hl', hc'⟩
      dsimp only at hl' hc
      have hok : WsOk n kd s j0 KKb u a l j := ⟨hu, ha, hl, hj⟩
      have e : ∀ x, x ≠ 16 → x ≠ 19 → x ≠ 20 → loc' x = loc x := fun x h16 h19 h20 => by
        rw [hl' x h16 h19, Function.update_of_ne h20]
      refine (wsCell_ok pre hok (hA.congr fun x hx => e x (by omega) (by omega) (by omega))
        (by rw [e 14 (by omega) (by omega) (by omega), h14])
        (by rw [e 15 (by omega) (by omega) (by omega), h15]) hc
        (by rw [e 17 (by omega) (by omega) (by omega), h17])
        (by rw [hl' 20 (by omega) (by omega), Function.update_self]) hc'.2).mono le_rfl ?_
      rintro ⟨loc'', μ3⟩ ⟨hmem, hloc⟩
      dsimp only at hmem hloc
      refine ⟨show loc'' 16 = j by rw [hloc 16 (by omega), hc], fun x h16 h19 => ?_, ?_⟩
      · simp only
        rw [Function.update_of_ne h16, hloc x h19, hl' x h16 h19]
      · simp only at hmem ⊢
        rw [hmem]
        exact (hc'.step (wsPos_lt pre hok)).congr fun i => (marks_step hok i).symm
  · have hR : a * kd + l < n * kd := Nat.mul_add_lt_mul ha hl
    have hnk := pre.nk_le
    have hapRS := pre.apartRS
    have hbRS := pre.belowRS
    have hspace := pre.space
    have hw1 := pre.std.space_le
    have hwr := pre.word
    have hak : a * kd ≤ n * kd := Nat.mul_le_mul_right kd ha.le
    have hreadRS : μ' (rs + (a * kd + l)) =
        (((a * kd + l) / N0 * (KK * N0) + (a * kd + l) % N0 : ℕ) : ℤ) := by
      rw [hC.2 _ (by omega), pre.segRS.read (by simp; omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_range (show a * kd + l < NP by omega)]
    have hV : (a * kd + l) / N0 * (KK * N0) + (a * kd + l) % N0 + u * N0 =
        srcOf KK N0 u (a * kd + l) := by
      unfold srcOf; ring
    have hsrc := srcOf_lt_rows pre hu ha hl
    have hrowD : srcOf KK N0 u (a * kd + l) * D + D ≤ KK * NP * D := by
      have := Nat.mul_le_mul_right D hsrc
      rw [Nat.succ_mul] at this
      exact this
    have hle : srcOf KK N0 u (a * kd + l) ≤ srcOf KK N0 u (a * kd + l) * D :=
      Nat.le_mul_of_pos_right _ hD
    have haddr : ((rs : ℤ) + a * kd + l).toNat = rs + (a * kd + l) := by omega
    generalize (a * kd + l) / N0 * (KK * N0) + (a * kd + l) % N0 = V at hreadRS hV
    generalize srcOf KK N0 u (a * kd + l) = ρ at hV hrowD hle hsrc ⊢
    have hVz : (V : ℤ) + u * N0 = ρ := by exact_mod_cast hV
    have huN : u * N0 ≤ ρ := by omega
    simp only [Expr.Gives, Expr.Safe, Expr.val, Op.eval, h0, h3, h14, h5, h15, h13, h8, h7,
      Limits.Addr, abs_le, haddr, hreadRS, hVz, true_and]
    push_cast
    repeat' apply And.intro
    all_goals omega

open WS in
/-- **The rows of one `a`**: `l < k`. -/
theorem wsRows_ok (pre : WriteSrcPre lim μ base t1 t2 rs n kd p D N0 j0 KKb s KK NP T1 T2)
    {u a : ℕ} (hu : u < KKb) (ha : a < n) {loc μ' : ℕ → ℤ}
    (hA : WsArgs loc base t1 t2 rs n kd p D N0 j0 KKb s (KK * NP * D))
    (h13 : loc 13 = u) (h14 : loc 14 = a) (h17 : loc 17 = ((j0 + u) * s : ℕ))
    (h18 : loc 18 = (wsLen n s ((j0 + u) * s) : ℕ))
    (hC : Cells μ μ' base (KK * NP * D)
      (marks (WsOk n kd s j0 KKb) (wsPos n kd p s j0 D KK N0 T1 T2) (lexBefore u a 0 0))) :
    Ends lim P d (Stmt.for Lc (v Kd) writeSrcRow) ⟨loc, μ'⟩ (kd * (41 * s + 31) + 6) fun σ' =>
      Cells μ σ'.mem base (KK * NP * D)
        (marks (WsOk n kd s j0 KKb) (wsPos n kd p s j0 D KK N0 T1 T2) (lexBefore u (a + 1) 0 0)) ∧
      ∀ x, x ≠ 15 → x ≠ 16 → x ≠ 19 → x ≠ 20 → σ'.loc x = loc x := by
  have hA' := hA
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hA'
  obtain ⟨hws, hwn, hwk, hwK⟩ := wsWord pre
  refine Ends.for (fun j σ => (∀ x, x ≠ 15 → x ≠ 16 → x ≠ 19 → x ≠ 20 → σ.loc x = loc x) ∧
      Cells μ σ.mem base (KK * NP * D) (marks (WsOk n kd s j0 KKb)
        (wsPos n kd p s j0 D KK N0 T1 T2) (lexBefore u a j 0)))
    kd (41 * s + 23) ⟨fun x hx _ _ _ => Function.update_of_ne hx _ _, hC⟩
    ?round ?done ?bound (by omega) (by simp only [Expr.cost]; ring_nf; omega)
  case bound =>
    rintro j ⟨loc', μ''⟩ - - ⟨hl', -⟩
    dsimp only at hl'
    refine ⟨trivial, ?_⟩
    simp only [Expr.val]
    rw [hl' 5 (by omega) (by omega) (by omega) (by omega), h5]
  case done =>
    rintro ⟨loc', μ''⟩ - ⟨hl', hc'⟩
    dsimp only at hl'
    refine ⟨hc'.congr (marks_congr ?_), hl'⟩
    rintro u' a' l' cl' ⟨-, -, hl'', -⟩
    unfold lexBefore
    constructor <;> intro h <;> omega
  case round =>
    rintro j ⟨loc', μ''⟩ hj hc ⟨hl', hc'⟩
    dsimp only at hl' hc
    have e : ∀ x, x ≠ 15 → x ≠ 16 → x ≠ 19 → x ≠ 20 → loc' x = loc x := hl'
    refine (wsRow_ok pre pre.D_pos hu ha hj
      (hA.congr fun x hx => e x (by omega) (by omega) (by omega) (by omega))
      (by rw [e 13 (by omega) (by omega) (by omega) (by omega), h13])
      (by rw [e 14 (by omega) (by omega) (by omega) (by omega), h14]) hc
      (by rw [e 17 (by omega) (by omega) (by omega) (by omega), h17])
      (by rw [e 18 (by omega) (by omega) (by omega) (by omega), h18]) hc').mono le_rfl ?_
    rintro ⟨loc'', μ3⟩ ⟨hc3, hloc⟩
    dsimp only at hc3 hloc
    refine ⟨show loc'' 15 = j by rw [hloc 15 (by omega) (by omega) (by omega), hc],
      fun x h15 h16 h19 h20 => ?_, hc3⟩
    simp only
    rw [Function.update_of_ne h15, hloc x h16 h19 h20, hl' x h15 h16 h19 h20]

open WS in
/-- **The rows of one product**: `a < n`. -/
theorem wsAs_ok (pre : WriteSrcPre lim μ base t1 t2 rs n kd p D N0 j0 KKb s KK NP T1 T2)
    {u : ℕ} (hu : u < KKb) {loc μ' : ℕ → ℤ}
    (hA : WsArgs loc base t1 t2 rs n kd p D N0 j0 KKb s (KK * NP * D))
    (h13 : loc 13 = u) (h17 : loc 17 = ((j0 + u) * s : ℕ))
    (h18 : loc 18 = (wsLen n s ((j0 + u) * s) : ℕ))
    (hC : Cells μ μ' base (KK * NP * D)
      (marks (WsOk n kd s j0 KKb) (wsPos n kd p s j0 D KK N0 T1 T2) (lexBefore u 0 0 0))) :
    Ends lim P d (Stmt.for A (v N) (Stmt.for Lc (v Kd) writeSrcRow)) ⟨loc, μ'⟩
      (n * (kd * (41 * s + 31) + 14) + 6) fun σ' =>
      Cells μ σ'.mem base (KK * NP * D)
        (marks (WsOk n kd s j0 KKb) (wsPos n kd p s j0 D KK N0 T1 T2) (lexBefore (u + 1) 0 0 0)) ∧
      ∀ x, x < 14 → σ'.loc x = loc x := by
  have hA' := hA
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hA'
  obtain ⟨hws, hwn, hwk, hwK⟩ := wsWord pre
  refine Ends.for (fun j σ => (∀ x, x ≠ 14 → x ≠ 15 → x ≠ 16 → x ≠ 19 → x ≠ 20 → σ.loc x = loc x) ∧
      Cells μ σ.mem base (KK * NP * D) (marks (WsOk n kd s j0 KKb)
        (wsPos n kd p s j0 D KK N0 T1 T2) (lexBefore u j 0 0)))
    n (kd * (41 * s + 31) + 6) ⟨fun x hx _ _ _ _ => Function.update_of_ne hx _ _, hC⟩
    ?round ?done ?bound (by omega) (by simp only [Expr.cost]; ring_nf; omega)
  case bound =>
    rintro j ⟨loc', μ''⟩ - - ⟨hl', -⟩
    dsimp only at hl'
    refine ⟨trivial, ?_⟩
    simp only [Expr.val]
    rw [hl' 4 (by omega) (by omega) (by omega) (by omega) (by omega), h4]
  case done =>
    rintro ⟨loc', μ''⟩ - ⟨hl', hc'⟩
    dsimp only at hl'
    refine ⟨hc'.congr (marks_congr ?_), fun x hx => hl' x (by omega) (by omega) (by omega)
      (by omega) (by omega)⟩
    rintro u' a' l' cl' ⟨-, ha'', -, -⟩
    unfold lexBefore
    constructor <;> intro h <;> omega
  case round =>
    rintro j ⟨loc', μ''⟩ hj hc ⟨hl', hc'⟩
    dsimp only at hl' hc
    have e : ∀ x, x ≠ 14 → x ≠ 15 → x ≠ 16 → x ≠ 19 → x ≠ 20 → loc' x = loc x := hl'
    refine (wsRows_ok pre hu hj
      (hA.congr fun x hx => e x (by omega) (by omega) (by omega) (by omega) (by omega))
      (by rw [e 13 (by omega) (by omega) (by omega) (by omega) (by omega), h13]) hc
      (by rw [e 17 (by omega) (by omega) (by omega) (by omega) (by omega), h17])
      (by rw [e 18 (by omega) (by omega) (by omega) (by omega) (by omega), h18]) hc').mono
      le_rfl ?_
    rintro ⟨loc'', μ3⟩ ⟨hc3, hloc⟩
    dsimp only at hc3 hloc
    refine ⟨show loc'' 14 = j by rw [hloc 14 (by omega) (by omega) (by omega) (by omega), hc],
      fun x h14 h15 h16 h19 h20 => ?_, hc3⟩
    simp only
    rw [Function.update_of_ne h14, hloc x h15 h16 h19 h20, hl' x h14 h15 h16 h19 h20]

open WS in
/-- **One product** `u`: its middle block, then its rows. -/
theorem wsProd_ok (pre : WriteSrcPre lim μ base t1 t2 rs n kd p D N0 j0 KKb s KK NP T1 T2)
    {u : ℕ} (hu : u < KKb) {loc μ' : ℕ → ℤ}
    (hA : WsArgs loc base t1 t2 rs n kd p D N0 j0 KKb s (KK * NP * D)) (h13 : loc 13 = u)
    (hC : Cells μ μ' base (KK * NP * D)
      (marks (WsOk n kd s j0 KKb) (wsPos n kd p s j0 D KK N0 T1 T2) (lexBefore u 0 0 0))) :
    Ends lim P d writeSrcProd ⟨loc, μ'⟩ (n * (kd * (41 * s + 31) + 14) + 24) fun σ' =>
      Cells μ σ'.mem base (KK * NP * D)
        (marks (WsOk n kd s j0 KKb) (wsPos n kd p s j0 D KK N0 T1 T2) (lexBefore (u + 1) 0 0 0)) ∧
      ∀ x, x < 14 → σ'.loc x = loc x := by
  have hA' := hA
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hA'
  have hblk := pre.blocks u hu
  have hword := pre.word
  have hc0w : (j0 + u) * s + s ≤ (j0 + KKb + 1) * (s + 1) := by nlinarith
  have hle : ∀ x : ℕ, x ≤ (j0 + KKb + 1) * (s + 1) + n * n + n * kd + 2 * p + 4 →
      (x : ℤ) ≤ lim.word := fun x hx => le_trans (by exact_mod_cast hx) hword
  have hw1 := hle ((j0 + u) * s + s) (by omega)
  have hw2 := hle (n + 1) (by have := Nat.le_mul_self n; omega)
  have hw0 := pre.std.const_le
  unfold writeSrcProd
  refine Ends.setValThen (((j0 + u) * s : ℕ) : ℤ) ?_ ?_ (by light_time)
  · -- the length of the middle block, then the rows
    have rest : ∀ loc' : ℕ → ℤ, (∀ x, x ≠ 18 → loc' x =
        Function.update loc 17 (((j0 + u) * s : ℕ) : ℤ) x) →
        loc' 18 = (wsLen n s ((j0 + u) * s) : ℕ) →
        Ends lim P d (Stmt.for A (v N) (Stmt.for Lc (v Kd) writeSrcRow)) ⟨loc', μ'⟩
          (n * (kd * (41 * s + 31) + 14) + 6) fun σ' =>
          Cells μ σ'.mem base (KK * NP * D) (marks (WsOk n kd s j0 KKb)
            (wsPos n kd p s j0 D KK N0 T1 T2) (lexBefore (u + 1) 0 0 0)) ∧
          ∀ x, x < 14 → σ'.loc x = loc x := by
      intro loc' e h18
      have e' : ∀ x, x < 17 → loc' x = loc x := fun x hx => by
        rw [e x (by omega), Function.update_of_ne (by omega)]
      refine (wsAs_ok pre hu (hA.congr fun x hx => e' x (by omega))
        (by rw [e' 13 (by omega), h13]) (by rw [e 17 (by omega), Function.update_self]) h18
        hC).mono le_rfl fun σ' h => ⟨h.1, fun x hx => ?_⟩
      rw [h.2 x hx, e' x (by omega)]
    have e17 : ∀ x, x ≠ 17 → Function.update loc 17 (((j0 + u) * s : ℕ) : ℤ) x = loc x :=
      fun x hx => Function.update_of_ne hx _ _
    refine Ends.iteThen (fun hc => ?_) (fun hc => ?_) ?_ (by light_time)
    · simp only [Cond.Holds, Expr.val, Function.update_self, e17 11 (by omega),
        e17 4 (by omega), h11, h4, Op.eval, Nat.cast_one] at hc
      have hl : wsLen n s ((j0 + u) * s) = s := by unfold wsLen; rw [if_pos (by generalize (j0 + u) * s = c0 at *; omega)]
      refine Ends.setValThen (s : ℤ) ((rest _ (fun x hx => Function.update_of_ne hx _ _)
        (by rw [Function.update_self, hl])).mono (by light_time) fun _ h => h) ?_ (by light_time)
      simp only [Expr.Gives, Expr.Safe, Expr.val, e17 11 (by omega), h11]
      exact ⟨trivial, trivial⟩
    · simp only [Cond.Holds, Expr.val, Function.update_self, e17 11 (by omega),
        e17 4 (by omega), h11, h4, Op.eval, Nat.cast_one] at hc
      have hl : wsLen n s ((j0 + u) * s) = n - (j0 + u) * s := by
        unfold wsLen; rw [if_neg (by generalize (j0 + u) * s = c0 at *; omega)]
      refine Ends.setValThen ((n - (j0 + u) * s : ℕ) : ℤ) ((rest _
        (fun x hx => Function.update_of_ne hx _ _)
        (by rw [Function.update_self, hl])).mono (by light_time) fun _ h => h) ?_ (by light_time)
      simp only [Expr.Gives, Expr.Safe, Expr.val, Op.eval, Function.update_self,
        e17 4 (by omega), h4, abs_le, true_and]
      generalize (j0 + u) * s = c0 at *
      repeat' apply And.intro
      all_goals omega
    · simp only [Cond.Safe, Expr.Safe, Expr.val, Op.eval, Function.update_self,
        e17 11 (by omega), e17 4 (by omega), h11, h4, abs_le, true_and]
      generalize (j0 + u) * s = c0 at *
      repeat' apply And.intro
      all_goals omega
  · have hm : ((j0 : ℤ) + u) * s = (((j0 + u) * s : ℕ) : ℤ) := by push_cast; ring
    simp only [Expr.Gives, Expr.Safe, Expr.val, Op.eval, h9, h13, h11, abs_le, true_and, hm]
    have : (((j0 + u) * s : ℕ) : ℤ) ≤ lim.word := hle _ (by omega)
    have : ((j0 + u : ℕ) : ℤ) ≤ lim.word := hle _ (by nlinarith)
    push_cast at this
    generalize (j0 + u) * s = c0 at *
    repeat' apply And.intro
    all_goals first | trivial | omega

end prog

/-- **writeSrc meets its specification.** -/
theorem writeSrc_ok {lim : Limits} {P : Program} (hP : P[pWriteSrc]? = some writeSrcBody)
    (hF : Light.Sec4.FillSpec lim P) : WriteSrcSpec lim P := by
  intro base t1 t2 rs n kd p D N0 bt KKb s KK NP T1 T2 μ d pre hd
  refine Meets.of_body hP ?_
  have hspace := pre.space
  have hw1 := pre.std.space_le
  have hw0 := pre.std.const_le
  obtain ⟨hws, hwn, hwk, hwK⟩ := wsWord pre
  have hargs : WsArgs (frame [(base : ℤ), t1, t2, rs, n, kd, p, D, N0, bt * KK, KKb, s,
      KK * NP * D]) base t1 t2 rs n kd p D N0 (bt * KK) KKb s (KK * NP * D) := by
    simp [WsArgs, frame]
  have hT1 : kd * (41 * s + 31) ≤ kd * (s * 60 + 60) := Nat.mul_le_mul_left _ (by omega)
  have hT2 : n * (kd * (41 * s + 31) + 14) ≤ n * (kd * (s * 60 + 60) + 30) :=
    Nat.mul_le_mul_left _ (by omega)
  have hT3 : KKb * (n * (kd * (41 * s + 31) + 14) + 32) ≤
      KKb * (n * (kd * (s * 60 + 60) + 30) + 60) := Nat.mul_le_mul_left _ (by omega)
  unfold writeSrcBody
  refine Ends.callThen (hF base (KK * NP * D) 0 μ (by omega) (by omega) (d + 1) hd) ?_ ?_ (by omega)
    ?_
  · rintro r μ' ⟨hz, hrest⟩
    refine Ends.for (fun j σ => WsArgs σ.loc base t1 t2 rs n kd p D N0 (bt * KK) KKb s (KK * NP * D) ∧
        Cells μ σ.mem base (KK * NP * D) (marks (WsOk n kd s (bt * KK) KKb)
          (wsPos n kd p s (bt * KK) D KK N0 T1 T2) (lexBefore j 0 0 0)))
      KKb (n * (kd * (41 * s + 31) + 14) + 24)
      ⟨(hargs.update (x := 19) (by omega) r).update (x := 13) (by omega) 0,
        fun i hi => ⟨fun h => absurd h (marks_none i), fun _ => by simpa using hz i hi⟩, hrest⟩
      ?round ?done ?bound (by omega) ?time
    case time =>
      unfold tWriteSrc
      simp only [Expr.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      have e : KKb * (1 + (n * (kd * (41 * s + 31) + 14) + 24) + 7) =
          KKb * (n * (kd * (41 * s + 31) + 14) + 32) := by ring
      omega
    case bound =>
      rintro j ⟨loc', μ''⟩ - - ⟨hA, -⟩
      exact ⟨trivial, hA.2.2.2.2.2.2.2.2.2.2.1⟩
    case round =>
      rintro j ⟨loc', μ''⟩ hj hc ⟨hA, hC⟩
      dsimp only at hA hC hc
      refine (wsProd_ok pre hj hA hc hC).mono le_rfl ?_
      rintro ⟨loc'', μ3⟩ ⟨hC3, hloc⟩
      dsimp only at hC3 hloc
      exact ⟨show loc'' 13 = j by rw [hloc 13 (by omega), hc],
        (hA.congr fun x hx => hloc x (by omega)).update (x := 13) (by omega) _, hC3⟩
    case done =>
      rintro ⟨loc', μ''⟩ - ⟨-, hC⟩
      dsimp only at hC ⊢
      refine ⟨fun ρ hρ κ hκ => ?_, hC.2⟩
      have hi : ρ * D + κ < KK * NP * D := by
        have := Nat.mul_le_mul_right D hρ
        rw [Nat.succ_mul] at this
        omega
      have hiff := (marks_congr (ok := WsOk n kd s (bt * KK) KKb)
        (pos := wsPos n kd p s (bt * KK) D KK N0 T1 T2)
        (dn := lexBefore KKb 0 0 0) (dn' := fun _ _ _ _ => True)
        (fun u a l cl hok => by unfold lexBefore; exact ⟨fun _ => trivial, fun _ => Or.inl hok.1⟩)
        (ρ * D + κ)).trans (marks_iff (bt := bt) (by have := pre.k_pos; omega)
          (by have := pre.p_pos; omega) (by have := pre.N0_pos; omega) pre.KKb_le pre.sp_le hκ)
      have hval := srcVal_eq (s := s) (p := p) (KK := KK) (N0 := N0)
        (ok := okX n s kd (bt * KK + KKb) KK bt)
        (f := fGen n s p kd KK bt (fun q => T1.getD q 0) (fun l => T2.getD l 0)) (ρ := ρ) (κ := κ)
        _ hiff
      rw [Nat.add_assoc]
      by_cases hm : marks (WsOk n kd s (bt * KK) KKb) (wsPos n kd p s (bt * KK) D KK N0 T1 T2)
          (lexBefore KKb 0 0 0) (ρ * D + κ)
      · rw [(hC.1 _ hi).1 hm, hval.1 hm]
      · rw [(hC.1 _ hi).2 hm, hval.2 hm]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, List.map_cons, List.map_nil]
    refine ⟨?_, ?_⟩
    · rintro e (rfl | rfl | rfl) <;> (simp; try omega)
    · simp [frame]
  · unfold tWriteSrc
    simp only [Expr.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega

end Light.Batch
