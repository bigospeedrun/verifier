import Submission.Work.Mixed.Prog.Glue

/-!
# Mixed engine, R3 program part 20: the local work of a class (agent e-r3prog)

`Eng.clsLoc_le`: the local work of a valid class is at most
`C * (2^n * (NU + cons) + (W^(h+1)+1)^2 * (h+3) + n + 1)` — the sweeps cost `2^n` per unit and per
consumed source (each child's input has one slot per parent unit plus its own sources), the rest is
polynomial bookkeeping.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset GF MXR
noncomputable section

namespace Eng
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]
variable (E : Eng α ρ σ)

/-- A fed child slot is the slot of its parent unit. -/
lemma slotR_ppR (n h μ r t : ℕ) (hf : E.fedP n h μ r t) : E.slotR n h μ r (E.ppR n h μ r t) = t := by
  obtain ⟨ht, hin⟩ := hf
  have hW := E.W_pos
  have hU : E.Uc n (h+1) μ (E.ppR n h μ r t) = E.parCode n h μ r t := U_PC hin
  have hq : t / E.W < E.NUc n h (μ * r) := (Nat.div_lt_iff_lt_mul hW).2 ht
  have e1 : E.parCode n h μ r t % E.W = t % E.W := by
    unfold parCode; rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (Nat.mod_lt _ hW)]
  have e2 : E.parCode n h μ r t / E.W = E.Uc n h (μ * r) (t / E.W) := by
    unfold parCode; rw [Nat.add_mul_div_left _ _ hW, Nat.div_eq_of_lt (Nat.mod_lt _ hW), zero_add]
  unfold slotR
  rw [hU, e1, e2]
  have : E.PCc n h (μ * r) (E.Uc n h (μ * r) (t / E.W)) = t / E.W := PC_U hq
  rw [this, Nat.mul_comm]
  exact Nat.div_add_mod t E.W

/-- **A child has one slot per parent unit plus its own sources.** -/
lemma slots_le (n h μ r : ℕ) :
    E.NUc n h (μ * r) * E.W ≤ E.NUc n (h+1) μ + Nat.count (E.srcP n h μ r) (E.NUc n h (μ * r) * E.W) := by
  set NJ := E.NUc n h (μ * r) * E.W
  have hsplit : Nat.count (E.fedP n h μ r) NJ + Nat.count (E.srcP n h μ r) NJ = NJ := by
    rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
    have e1 : (range NJ).filter (E.fedP n h μ r) =
        (range NJ).filter (fun t => inRS E.W E.tq E.mx n (h+1) μ (E.parCode n h μ r t)) := by
      ext t; simp only [mem_filter, mem_range, fedP]; constructor
      · rintro ⟨h1, _, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, h1, h2⟩
    have e2 : (range NJ).filter (E.srcP n h μ r) =
        (range NJ).filter (fun t => ¬ inRS E.W E.tq E.mx n (h+1) μ (E.parCode n h μ r t)) := by
      ext t; simp only [mem_filter, mem_range, srcP]; constructor
      · rintro ⟨h1, _, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, h1, h2⟩
    rw [e1, e2, Finset.card_filter_add_card_filter_not, card_range]
  have hfed : Nat.count (E.fedP n h μ r) NJ ≤ E.NUc n (h+1) μ := by
    rw [Nat.count_eq_card_filter_range]
    have : ((range NJ).filter (E.fedP n h μ r)).card ≤ (range (E.NUc n (h+1) μ)).card := by
      apply Finset.card_le_card_of_injOn (E.ppR n h μ r)
      · intro t ht
        simp only [coe_filter, Set.mem_setOf_eq, mem_coe, mem_range] at ht ⊢
        exact PC_lt ht.2.2
      · intro t1 ht1 t2 ht2 heq
        simp only [coe_filter, Set.mem_setOf_eq] at ht1 ht2
        rw [← E.slotR_ppR n h μ r t1 ht1.2, ← E.slotR_ppR n h μ r t2 ht2.2, heq]
    simpa using this
  omega

lemma ownSrc_le_accR (n h μ r : ℕ) : (E.ownSrc n h μ r).length ≤ (E.accR n h μ r).length := by
  simp [accR]

/-- The routing tables' cost does not depend on the rank. -/
def rtB (n h : ℕ) : ℕ := 9 * (E.W^(h+1) + 1) * (E.W^(h+1) + 1) * (h + 3) + 8

lemma rtCost_le (n h μ r : ℕ) : E.rtCost n h μ r ≤ E.rtB n h := by
  unfold rtCost rtB idxCost
  have h1 : E.W^h ≤ E.W^(h+1) := Nat.pow_le_pow_right E.W_pos (by omega)
  have h2 : (E.W^h + 1) * (E.W^h + 1) * (h + 2) ≤ (E.W^(h+1) + 1) * (E.W^(h+1) + 1) * (h + 3) := by
    gcongr <;> omega
  nlinarith

/-- One letter's cost, bounded. -/
def letB (n h μ C : ℕ) : ℕ := E.rtB n h + (2 * E.NUc n (h+1) μ + C) * 2^n + 2 * C + 20

lemma swCost_le (n h μ C : ℕ) :
    ∀ (ws : GWord α ρ) (L : ℕ), L + (E.accW n h μ ws).length ≤ C →
      E.swCost n h μ L ws ≤ ws.length * E.letB n h μ C := by
  intro ws
  induction ws with
  | nil => intro L _; simp [swCost]
  | cons mv ws ih =>
    intro L hL
    rw [accW_cons] at hL
    simp only [swCost, List.length_cons]
    rcases hmv : mv.rk? with _ | r
    · simp only [hmv, List.nil_append, Nat.add_zero] at hL ⊢
      have := ih L hL
      have h1 : E.NUc n (h+1) μ * 2^n ≤ E.letB n h μ C := by
        unfold letB; nlinarith [Nat.two_pow_pos n]
      nlinarith
    · simp only [hmv, List.length_append] at hL ⊢
      have := ih (L + (E.accR n h μ r).length) (by omega)
      have h1 : E.blkCost n h μ r L ≤ E.letB n h μ C := by
        unfold blkCost letB
        have e1 := E.rtCost_le n h μ r
        have e2 := E.slots_le n h μ r
        have e3 := E.ownSrc_len n h μ r
        have e4 := E.ownSrc_le_accR n h μ r
        have e5 : (E.NUc n h (μ * r) * E.W + E.NUc n (h+1) μ) * 2^n ≤ (2 * E.NUc n (h+1) μ + C) * 2^n := by
          apply Nat.mul_le_mul_right; omega
        omega
      nlinarith

lemma lfCost_le (n μ : ℕ) : ∀ ws : GWord α ρ, E.lfCost n μ ws ≤ ws.length * (E.NUc n 0 μ * 2^n + 2 * n + 2) := by
  intro ws
  induction ws with
  | nil => simp [lfCost]
  | cons mv ws ih =>
    simp only [lfCost, List.length_cons]
    rcases hmv : mv.rk? with _ | r
    · simp only [hmv]; nlinarith
    · simp only [hmv]; nlinarith

lemma arith_leaf (a P W n Q T Cn lf : ℕ) (hT1 : n + 1 ≤ T) (hQ : 8 ≤ Q) (hlf : lf ≤ P * (a * T + 2 * n + 2)) :
    n + 1 + 8 + a * (4 * n + 4 * 0 + 8) + a * (2 * T + 2) + a * T + lf + a * W * T ≤
      100 * (P + 1) * (W + 1) * (T * (a + Cn) + Q + n + 1) := by
  set K := (P + 1) * (W + 1) with hK
  have hP : P ≤ K := by rw [hK]; nlinarith
  have hW : W ≤ K := by rw [hK]; nlinarith
  have hK1 : 1 ≤ K := by rw [hK]; nlinarith
  have f1 : a * (4 * n + 4 * 0 + 8) ≤ 8 * (a * T) := by
    have : 4 * n + 4 * 0 + 8 ≤ 8 * T := by omega
    calc a * (4 * n + 4 * 0 + 8) ≤ a * (8 * T) := Nat.mul_le_mul_left _ this
      _ = 8 * (a * T) := by ring
  have f2 : a * (2 * T + 2) ≤ 4 * (a * T) := by
    have : 2 * T + 2 ≤ 4 * T := by omega
    calc a * (2 * T + 2) ≤ a * (4 * T) := Nat.mul_le_mul_left _ this
      _ = 4 * (a * T) := by ring
  have f3 : P * (a * T + 2 * n + 2) ≤ K * (a * T) + K * (2 * n + 2) := by
    calc P * (a * T + 2 * n + 2) ≤ K * (a * T + 2 * n + 2) := Nat.mul_le_mul_right _ hP
      _ = K * (a * T) + K * (2 * n + 2) := by ring
  have f4 : a * W * T ≤ K * (a * T) := by
    calc a * W * T = W * (a * T) := by ring
      _ ≤ K * (a * T) := Nat.mul_le_mul_right _ hW
  have f5 : 100 * (P + 1) * (W + 1) * (T * (a + Cn) + Q + n + 1) ≥ 100 * K * (a * T + Q + n + 1) := by
    have : a * T + Q + n + 1 ≤ T * (a + Cn) + Q + n + 1 := by nlinarith
    calc 100 * K * (a * T + Q + n + 1) ≤ 100 * K * (T * (a + Cn) + Q + n + 1) := Nat.mul_le_mul_left _ this
      _ = _ := by rw [hK]; ring
  have f6 : 100 * K * (a * T + Q + n + 1) = 100 * (K * (a * T)) + 100 * (K * Q) + 100 * (K * (n + 1)) := by ring
  have f7 : K * (2 * n + 2) = 2 * (K * (n + 1)) := by ring
  have g1 : a * T ≤ K * (a * T) := Nat.le_mul_of_pos_left _ hK1
  have g2 : Q ≤ K * Q := Nat.le_mul_of_pos_left _ hK1
  have g3 : n + 1 ≤ K * (n + 1) := Nat.le_mul_of_pos_left _ hK1
  omega

lemma arith_up (h' a P W n Q T Cn sw idx : ℕ) (hT1 : n + 1 ≤ T) (hh : h' + 1 ≤ n) (hidx : idx ≤ Q)
    (hsw : sw ≤ P * (9 * Q + 8 + (2 * (a * T) + Cn * T) + 2 * Cn + 20)) :
    n + 1 + idx + a * (4 * n + 4 * (h' + 1) + 8) + a * (2 * T + 2) + a * T + sw + a * W * T ≤
      100 * (P + 1) * (W + 1) * (T * (a + Cn) + Q + n + 1) := by
  set K := (P + 1) * (W + 1) with hK
  have hP : P ≤ K := by rw [hK]; nlinarith
  have hW : W ≤ K := by rw [hK]; nlinarith
  have hK1 : 1 ≤ K := by rw [hK]; nlinarith
  have f1 : a * (4 * n + 4 * (h' + 1) + 8) ≤ 16 * (a * T) := by
    have : 4 * n + 4 * (h' + 1) + 8 ≤ 16 * T := by omega
    calc a * (4 * n + 4 * (h' + 1) + 8) ≤ a * (16 * T) := Nat.mul_le_mul_left _ this
      _ = 16 * (a * T) := by ring
  have f2 : a * (2 * T + 2) ≤ 4 * (a * T) := by
    have : 2 * T + 2 ≤ 4 * T := by omega
    calc a * (2 * T + 2) ≤ a * (4 * T) := Nat.mul_le_mul_left _ this
      _ = 4 * (a * T) := by ring
  have hCn : Cn ≤ Cn * T := Nat.le_mul_of_pos_right _ (by omega)
  have f3 : P * (9 * Q + 8 + (2 * (a * T) + Cn * T) + 2 * Cn + 20) ≤
      9 * (K * Q) + 28 * K + 2 * (K * (a * T)) + 3 * (K * (Cn * T)) := by
    have h1 : 9 * Q + 8 + (2 * (a * T) + Cn * T) + 2 * Cn + 20 ≤ 9 * Q + 28 + 2 * (a * T) + 3 * (Cn * T) := by
      omega
    calc P * (9 * Q + 8 + (2 * (a * T) + Cn * T) + 2 * Cn + 20) ≤ K * (9 * Q + 28 + 2 * (a * T) + 3 * (Cn * T)) :=
          Nat.mul_le_mul hP h1
      _ = _ := by ring
  have f4 : a * W * T ≤ K * (a * T) := by
    calc a * W * T = W * (a * T) := by ring
      _ ≤ K * (a * T) := Nat.mul_le_mul_right _ hW
  have f5 : 100 * (P + 1) * (W + 1) * (T * (a + Cn) + Q + n + 1) =
      100 * (K * (a * T)) + 100 * (K * (Cn * T)) + 100 * (K * Q) + 100 * (K * (n + 1)) := by rw [hK]; ring
  have g1 : a * T ≤ K * (a * T) := Nat.le_mul_of_pos_left _ hK1
  have g2 : Q ≤ K * Q := Nat.le_mul_of_pos_left _ hK1
  have g3 : n + 1 ≤ K * (n + 1) := Nat.le_mul_of_pos_left _ hK1
  have g4 : K ≤ K * (n + 1) := Nat.le_mul_of_pos_right _ (by omega)
  omega

/-- **The local work of a valid class.** -/
theorem clsLoc_le {kmin : ℕ} (hk : E.KMin kmin) : ∃ C : ℕ, ∀ (n h μ o BS : ℕ) (J sup : ℕ → Bits n → ℂ),
    E.Valid kmin (MDesc.cls n h μ o BS J sup) →
    E.clsLoc n h μ ≤ C * (2^n * (E.NUc n h μ + E.cons n h μ) + (E.W^(h+1) + 1) * (E.W^(h+1) + 1) * (h + 3) + n + 1) := by
  refine ⟨100 * (E.wd.length + 1) * (E.W + 1), fun n h μ o BS J sup hd => ?_⟩
  obtain ⟨_, hhn, _, _⟩ := E.valid_facts hk hd
  have hn1 : n + 1 ≤ 2^n := Nat.lt_two_pow_self
  have hW := E.W_pos
  unfold clsLoc
  split_ifs with h0
  · subst h0
    unfold locLeaf
    have e2 : E.idxCost n 0 μ = 8 := by simp [idxCost]
    rw [e2]
    have hQ8 : 8 ≤ (E.W^(0+1) + 1) * (E.W^(0+1) + 1) * (0 + 3) := by
      simp only [zero_add, pow_one]; nlinarith
    exact arith_leaf _ _ _ _ _ _ _ _ hn1 hQ8 (E.lfCost_le n μ E.wd)
  · obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    unfold locUp
    have hcons : (E.accW n h' μ E.wd).length = E.cons n (h'+1) μ := rfl
    have e1 := E.swCost_le n h' μ (E.cons n (h'+1) μ) E.wd 0 (by omega)
    unfold letB at e1
    have e2 : E.idxCost n (h'+1) μ ≤ (E.W^(h'+1+1) + 1) * (E.W^(h'+1+1) + 1) * (h' + 1 + 3) := by
      unfold idxCost
      have : E.W^(h'+1) ≤ E.W^(h'+1+1) := Nat.pow_le_pow_right hW (by omega)
      gcongr <;> omega
    have e3 : E.rtB n h' ≤ 9 * ((E.W^(h'+1+1) + 1) * (E.W^(h'+1+1) + 1) * (h' + 1 + 3)) + 8 := by
      unfold rtB
      have : E.W^(h'+1) ≤ E.W^(h'+1+1) := Nat.pow_le_pow_right hW (by omega)
      have h4 : (E.W^(h'+1) + 1) * (E.W^(h'+1) + 1) * (h' + 3) ≤
          (E.W^(h'+1+1) + 1) * (E.W^(h'+1+1) + 1) * (h' + 1 + 3) := by gcongr <;> omega
      nlinarith
    refine arith_up h' _ _ _ _ _ _ _ _ _ hn1 hhn e2 ?_
    refine le_trans e1 (Nat.mul_le_mul_left _ ?_)
    have : (2 * E.NUc n (h' + 1) μ + E.cons n (h' + 1) μ) * 2^n =
        2 * (E.NUc n (h' + 1) μ * 2^n) + E.cons n (h' + 1) μ * 2^n := by ring
    omega

end Eng

end
end PowerSaving.RAM
end OAI
