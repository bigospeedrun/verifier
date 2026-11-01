import Submission.Work.Mixed.Prog.ClsDom
import Submission.Work.MixedCost.Bridge

/-!
# Mixed engine, R3 program part 22: the class halves of `mixed_close`'s hypotheses (agent e-r3prog)

For a rule `R` bridged to the engine (`BridgeHyp`, e-r3cost):
* `BridgeHyp.kminE`        the smallest target rank is attained (`KMin`);
* `BridgeHyp.clsLoc_dom`   class work `O(locS)`;
* `BridgeHyp.kidsC_shape`  the calls of a valid class have exactly the shapes `kidsS` charges;
* `bnd_kidsC`              the word driver does not grow along a class's calls.
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
variable {E : Eng α ρ σ} {R : MX.Rule} {typ : ℕ → Fin R.K} {kmin : ℕ}

lemma BridgeHyp.kminE (H : E.BridgeHyp R typ kmin) : E.KMin kmin := by
  refine ⟨by rw [← H.hkmin]; exact R.two_le_kmin, ?_⟩
  obtain ⟨k, hk, hW⟩ := R.kmin_att
  have hcard := H.hW k
  rw [← hcard] at hW
  obtain ⟨x, hx⟩ := Finset.card_pos.1 hW
  rw [Finset.mem_filter, Finset.mem_range] at hx
  refine ⟨E.Q.atFin ⟨x, hx.1⟩, ?_⟩
  have h1 := H.htq x hx.1
  rw [hx.2, hk, H.hkmin] at h1
  unfold tq at h1; rw [dif_pos hx.1] at h1
  exact h1

lemma BridgeHyp.cons_eq (H : E.BridgeHyp R typ kmin) (n h μ : ℕ) :
    E.cons n h μ = Multiset.card (R.srcBelow n h μ) := by
  rw [← H.srcSizes_eq n h μ, Multiset.coe_card]; rfl

/-- **Class work is `O(locS)`.** -/
theorem BridgeHyp.clsLoc_dom (H : E.BridgeHyp R typ kmin) (n0 : ℕ) :
    ∃ C : ℕ, ∀ (n h μ o BS : ℕ) (J sup : ℕ → Bits n → ℂ), E.Valid kmin (MDesc.cls n h μ o BS J sup) →
      E.clsLoc n h μ + 1 ≤ C * (R.locS n0 (MX.Shape.cls n h μ) + 1) := by
  obtain ⟨C, hC⟩ := E.clsLoc_dom H.kminE
  refine ⟨C, fun n h μ o BS J sup hd => ?_⟩
  have := hC n h μ o BS J sup hd
  rw [H.NUc_eq, H.cons_eq] at this
  exact this

/-- The shapes of the children of a class along a proper word. -/
lemma kidsUp_shape (sh : MDesc → MX.Shape)
    (hsh2 : ∀ n h μ o BS J sup, sh (MDesc.cls n h μ o BS J sup) = MX.Shape.cls n h μ)
    (n h μ BS : ℕ) (sup : ℕ → Bits n → ℂ) :
    ∀ (ws : GWord α ρ), ws.Proper E.X.n → ∀ (V : E.CState n (h+1) μ) (o : ℕ),
      (E.kidsUp n h μ BS sup V o ws).map sh = (blockRanks ws).map (fun r => MX.Shape.cls n h (μ * r)) := by
  intro ws
  induction ws with
  | nil => intro _ V o; rfl
  | cons mv ws ih =>
    intro hP V o
    cases mv with
    | old mv =>
      cases mv with
      | localM g => exact ih hP.tail _ _
      | shift l z => exact ih hP.tail _ _
      | block l r z ind =>
        have hr : r ≤ E.X.n := (show 1 ≤ r ∧ r < E.X.n from hP.head).2.le
        simp only [kidsUp, dif_pos hr, List.singleton_append, List.map_cons, blockRanks, List.filterMap_cons]
        rw [ih hP.tail]
        simp only [GMove.rk?, GMove.shadow, BMove.rk?, childC, hsh2]
        rfl
    | perm l G => exact ih hP.tail _ _
    | phase l z c => exact ih hP.tail _ _

/-- The shapes of the exits of a leaf class with one unit. -/
lemma kidsLeaf_shape (sh : MDesc → MX.Shape) (hsh1 : ∀ n B v, sh (MDesc.top n B v) = MX.Shape.top n B)
    (n μ : ℕ) (h1 : E.NUc n 0 μ = 1) (hfit : E.X.n * μ ≤ n) :
    ∀ (ws : GWord α ρ), ws.Proper E.X.n → ∀ (V : E.CState n 0 μ),
      (E.kidsLeaf n μ V ws).map sh = (blockRanks ws).map (fun r => MX.Shape.top (μ * r) (2^(n - μ * r))) := by
  intro ws
  induction ws with
  | nil => intro _ V; rfl
  | cons mv ws ih =>
    intro hP V
    cases mv with
    | old mv =>
      cases mv with
      | localM g => exact ih hP.tail _
      | shift l z => exact ih hP.tail _
      | block l r z ind =>
        have hr : r ≤ E.X.n := (show 1 ≤ r ∧ r < E.X.n from hP.head).2.le
        have hk : r * μ ≤ n := le_trans (Nat.mul_le_mul_right _ hr) hfit
        simp only [kidsLeaf, dif_pos hr, List.singleton_append, List.map_cons, blockRanks, List.filterMap_cons]
        rw [ih hP.tail]
        simp only [GMove.rk?, GMove.shadow, BMove.rk?, exitC, dif_pos hk, hsh1, h1, one_mul]
        rw [Nat.mul_comm r μ]
        rfl
    | perm l G => exact ih hP.tail _
    | phase l z c => exact ih hP.tail _

lemma ofFn_getD_map {β : Type*} (L : List ℕ) (P : ℕ) (hP : P = L.length) (f : ℕ → β) (g : Fin P → ℕ)
    (hg : ∀ j : Fin P, g j = L.getD j 0) : List.ofFn (fun j => f (g j)) = L.map f := by
  subst hP
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_ofFn, List.getElem_map, hg]
  rw [List.getD_eq_getElem _ _ (by simpa using h1)]

/-- **The calls of a valid class have exactly the shapes the bill charges.** -/
theorem BridgeHyp.kidsC_shape (H : E.BridgeHyp R typ kmin) (sh : MDesc → MX.Shape)
    (hsh1 : ∀ n B v, sh (MDesc.top n B v) = MX.Shape.top n B)
    (hsh2 : ∀ n h μ o BS J sup, sh (MDesc.cls n h μ o BS J sup) = MX.Shape.cls n h μ) (n0 : ℕ)
    (n h μ o BS : ℕ) (J sup : ℕ → Bits n → ℂ) (hd : E.Valid kmin (MDesc.cls n h μ o BS J sup)) :
    (((E.kidsC (MDesc.cls n h μ o BS J sup)).map sh : List MX.Shape) : Multiset MX.Shape) =
      R.kidsS n0 (MX.Shape.cls n h μ) := by
  have hPl : R.P = (blockRanks E.wd).length := H.hP
  cases h with
  | zero =>
    have hk := H.kminE
    have hfit := (E.valid_facts hk hd).1 rfl
    have h1 : E.NUc n 0 μ = 1 := le_antisymm (by simpa using E.NU_le' n 0 μ) (E.NU_pos hk hd)
    simp only [kidsC, MX.Rule.kidsS]
    rw [E.kidsLeaf_shape sh hsh1 n μ h1 hfit E.wd E.hP, Fin.univ_val_map]
    congr 1
    exact (ofFn_getD_map (blockRanks E.wd) R.P hPl (fun r => MX.Shape.top (μ * r) (2^(n - μ * r))) R.rk
      (fun j => H.hrk j)).symm
  | succ h =>
    simp only [kidsC, MX.Rule.kidsS]
    rw [E.kidsUp_shape sh hsh2 n h μ BS sup E.wd E.hP, Fin.univ_val_map]
    congr 1
    exact (ofFn_getD_map (blockRanks E.wd) R.P hPl (fun r => MX.Shape.cls n h (μ * r)) R.rk
      (fun j => H.hrk j)).symm

lemma kidsUp_bnd (n h μ BS : ℕ) (sup : ℕ → Bits n → ℂ) :
    ∀ (ws : GWord α ρ) (V : E.CState n (h+1) μ) (o : ℕ), ∀ c ∈ E.kidsUp n h μ BS sup V o ws,
      bndD c = (BS + 2) * 2^n := by
  intro ws
  induction ws with
  | nil => intro V o c hc; simp [kidsUp] at hc
  | cons mv ws ih =>
    intro V o c hc
    cases mv with
    | old mv =>
      cases mv with
      | localM g => exact ih _ _ c hc
      | shift l z => exact ih _ _ c hc
      | block l r z ind =>
        simp only [kidsUp] at hc
        rcases List.mem_append.1 hc with hc | hc
        · split_ifs at hc with hr
          · rw [List.mem_singleton] at hc; subst hc; rfl
          · simp at hc
        · exact ih _ _ c hc
    | perm l G => exact ih _ _ c hc
    | phase l z c' => exact ih _ _ c hc

lemma kidsLeaf_bnd (n μ BS : ℕ) (hNU : E.NUc n 0 μ ≤ 1) (hμ : 1 ≤ μ) (hfit : E.X.n * μ ≤ n) :
    ∀ (ws : GWord α ρ), ws.Proper E.X.n → ∀ (V : E.CState n 0 μ), ∀ c ∈ E.kidsLeaf n μ V ws,
      bndD c ≤ (BS + 2) * 2^n := by
  intro ws
  induction ws with
  | nil => intro _ V c hc; simp [kidsLeaf] at hc
  | cons mv ws ih =>
    intro hP V c hc
    cases mv with
    | old mv =>
      cases mv with
      | localM g => exact ih hP.tail _ c hc
      | shift l z => exact ih hP.tail _ c hc
      | block l r z ind =>
        have hpr : 1 ≤ r ∧ r < E.X.n := hP.head
        simp only [kidsLeaf] at hc
        rcases List.mem_append.1 hc with hc | hc
        · split_ifs at hc with hr
          · rw [List.mem_singleton] at hc; subst hc
            unfold exitC
            split_ifs with hk
            · show (E.NUc n 0 μ * 2^(n - r * μ) + 2) * 2^(r * μ) ≤ (BS + 2) * 2^n
              have hlt : r * μ < n := lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hpr.2 hμ) hfit
              have e1 : 2^(n - r * μ) * 2^(r * μ) = 2^n := by rw [← pow_add, Nat.sub_add_cancel hk]
              have e2 : 2 * 2^(r * μ) ≤ 2^n := by
                rw [← pow_succ']; exact Nat.pow_le_pow_right (by omega) hlt
              have e3 : E.NUc n 0 μ * 2^(n - r * μ) ≤ 2^(n - r * μ) := by
                calc E.NUc n 0 μ * 2^(n - r * μ) ≤ 1 * 2^(n - r * μ) := Nat.mul_le_mul_right _ hNU
                  _ = _ := one_mul _
              have e4 : (E.NUc n 0 μ * 2^(n - r * μ) + 2) * 2^(r * μ) ≤ 2^n + 2^n := by
                calc (E.NUc n 0 μ * 2^(n - r * μ) + 2) * 2^(r * μ) ≤ (2^(n - r * μ) + 2) * 2^(r * μ) :=
                      Nat.mul_le_mul_right _ (by omega)
                  _ = 2^(n - r * μ) * 2^(r * μ) + 2 * 2^(r * μ) := by ring
                  _ ≤ 2^n + 2^n := by rw [e1]; omega
              have e5 : 2^n + 2^n ≤ (BS + 2) * 2^n := by
                calc 2^n + 2^n = 2 * 2^n := by ring
                  _ ≤ (BS + 2) * 2^n := Nat.mul_le_mul_right _ (by omega)
              exact le_trans e4 e5
            · show (0 + 2) * 2^0 ≤ (BS + 2) * 2^n
              simp only [pow_zero, mul_one]; nlinarith [Nat.one_le_two_pow (n:=n)]
          · simp at hc
        · exact ih hP.tail _ c hc
    | perm l G => exact ih hP.tail _ c hc
    | phase l z c' => exact ih hP.tail _ c hc

/-- The word driver does not grow along a valid class's calls. -/
lemma bnd_kidsC (hk : E.KMin kmin) (n h μ o BS : ℕ) (J sup : ℕ → Bits n → ℂ)
    (hd : E.Valid kmin (MDesc.cls n h μ o BS J sup)) :
    ∀ c ∈ E.kidsC (MDesc.cls n h μ o BS J sup), bndD c ≤ bndD (MDesc.cls n h μ o BS J sup) := by
  intro c hc
  cases h with
  | zero =>
    have hfit := (E.valid_facts hk hd).1 rfl
    have hNU : E.NUc n 0 μ ≤ 1 := by simpa using E.NU_le' n 0 μ
    exact E.kidsLeaf_bnd n μ BS hNU hd.1 hfit E.wd E.hP _ c hc
  | succ h =>
    exact le_of_eq (E.kidsUp_bnd n h μ BS sup E.wd _ o c hc)

end Eng

end
end PowerSaving.RAM
end OAI
