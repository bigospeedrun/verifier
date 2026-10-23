import Submission.Work.TensorEng.Product
import Submission.Work.TensorProto.Strictify

/-!
# T1, part 6: tensor powers of a certified unit

`BU` bundles a certified unit with its label, role and live-role types; `BU.prod` is the tensor product of
`Product.lean`, `BU.pow A n` the `(n+1)`-fold product.  Along the power:

* the paid ranks (a multiset) are the products of paid ranks: `ranks_pow : (A.pow n).ranks = tpow A.ranks (n+1)`;
* the target ranks of the live roles likewise: `tgts_pow : (A.pow n).tgts = tpow A.tgts (n+1)`;
* the label dimension is the power: `card_pow`.

(`tens`, `tpow` are the inventory operations of `TensorProto.Strictify`.)

-- changed for the tensor-power extension (30103/10000000); see Submission.lean
-/

namespace TensorEng
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.GF OAI.PowerSaving.MX Matrix Finset
open TensorProto (tens tpow)

noncomputable section

/-- A certified unit with its types bundled. -/
structure BU where
  α : Type
  ρ : Type
  σ : Type
  [fα : Fintype α]
  [dα : DecidableEq α]
  [fρ : Fintype ρ]
  [dρ : DecidableEq ρ]
  [fσ : Fintype σ]
  [dσ : DecidableEq σ]
  u : CU α ρ σ

attribute [instance] BU.fα BU.dα BU.fρ BU.dρ BU.fσ BU.dσ

namespace BU

/-- The tensor product of bundled units. -/
def prod (A B : BU) : BU where
  α := A.α × B.α
  ρ := RW A.ρ B.σ B.ρ A.u.wd.length
  σ := A.σ × B.σ
  u :=
    { e := fun ll => Sum.inl (A.u.e ll.1, ll.2)
      he := fun a b h => by
        have h' := Prod.mk.inj (Sum.inl.inj h)
        exact Prod.ext (A.u.he h'.1) h'.2
      tr := fun ll => Fintype.card (Fin (B.u.tr ll.2)) * A.u.tr ll.1
      tz := tzP A.u B.u
      tind := tzP_ind A.u B.u
      wd := prodWord A.u B.u
      hw := prod_cert A.u B.u }

/-- The `(n+1)`-fold tensor power. -/
def pow (A : BU) : ℕ → BU
  | 0 => A
  | n + 1 => (A.pow n).prod A

/-- The paid ranks of a unit, as a multiset. -/
def ranks (A : BU) : Multiset ℕ := ((A.u.wd.filterMap GMove.rk? : List ℕ) : Multiset ℕ)

/-- The target ranks of the live roles of a unit, as a multiset. -/
def tgts (A : BU) : Multiset ℕ := (Finset.univ : Finset A.σ).val.map A.u.tr

lemma ranks_prod (A B : BU) : (A.prod B).ranks = tens A.ranks B.ranks := by
  show (((prodWord A.u B.u).filterMap GMove.rk? : List ℕ) : Multiset ℕ) = _
  rw [rk_prodWord]
  unfold tens ranks
  rw [← Multiset.coe_bind]
  congr 1
  all_goals (funext k; simp [Multiset.map_coe])

lemma tgts_prod (A B : BU) : (A.prod B).tgts = tens A.tgts B.tgts := by
  show ((Finset.univ : Finset (A.σ × B.σ)).val.map
      fun ll => Fintype.card (Fin (B.u.tr ll.2)) * A.u.tr ll.1) = _
  unfold tens tgts
  show Multiset.map _ (Multiset.bind (Finset.univ : Finset A.σ).val
      fun a => Multiset.map (Prod.mk a) (Finset.univ : Finset B.σ).val) = _
  rw [Multiset.map_bind, Multiset.bind_map]
  congr 1
  funext a
  rw [Multiset.map_map, Multiset.map_map]
  congr 1
  funext b
  simp only [Function.comp_apply, Fintype.card_fin]
  ring

lemma tens_one_left (P : Multiset ℕ) : tens {1} P = P := by
  unfold tens
  rw [Multiset.singleton_bind]
  simp

lemma ranks_pow (A : BU) (n : ℕ) : (A.pow n).ranks = tpow A.ranks (n + 1) := by
  induction n with
  | zero =>
    show A.ranks = tens {1} A.ranks
    rw [tens_one_left]
  | succ n ih =>
    show ((A.pow n).prod A).ranks = tens (tpow A.ranks (n + 1)) A.ranks
    rw [ranks_prod, ih]

lemma tgts_pow (A : BU) (n : ℕ) : (A.pow n).tgts = tpow A.tgts (n + 1) := by
  induction n with
  | zero =>
    show A.tgts = tens {1} A.tgts
    rw [tens_one_left]
  | succ n ih =>
    show ((A.pow n).prod A).tgts = tens (tpow A.tgts (n + 1)) A.tgts
    rw [tgts_prod, ih]

lemma card_prod (A B : BU) : Fintype.card (A.prod B).α = Fintype.card A.α * Fintype.card B.α :=
  Fintype.card_prod A.α B.α

lemma card_pow (A : BU) (n : ℕ) : Fintype.card (A.pow n).α = Fintype.card A.α ^ (n + 1) := by
  induction n with
  | zero =>
    show Fintype.card A.α = Fintype.card A.α ^ (0 + 1)
    rw [zero_add, pow_one]
  | succ n ih =>
    show Fintype.card ((A.pow n).prod A).α = _
    rw [card_prod, ih]
    ring

/-- Every paid letter of a unit is a block of rank `≥ 1`, `< card α`. -/
def RanksOK (A : BU) : Prop := ∀ r ∈ A.u.wd.filterMap GMove.rk?, 1 ≤ r ∧ r < Fintype.card A.α

/-- Every target rank is `≥ 1` and `≤ card α`. -/
def TgtsOK (A : BU) : Prop := ∀ l, 1 ≤ A.u.tr l ∧ A.u.tr l ≤ Fintype.card A.α

lemma ranksOK_prod {A B : BU} (hA : A.RanksOK) (hB : B.RanksOK) : (A.prod B).RanksOK := by
  intro m hm
  obtain ⟨k, hk, k', hk', rfl⟩ := prod_rk_mem A.u B.u hm
  obtain ⟨h1, h2⟩ := hA k hk
  obtain ⟨h3, h4⟩ := hB k' hk'
  rw [card_prod]
  exact ⟨Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), Nat.mul_lt_mul'' h2 h4⟩

lemma tgtsOK_prod {A B : BU} (hA : A.TgtsOK) (hB : B.TgtsOK) : (A.prod B).TgtsOK := by
  intro ll
  obtain ⟨h1, h2⟩ := hA ll.1
  obtain ⟨h3, h4⟩ := hB ll.2
  show 1 ≤ Fintype.card (Fin (B.u.tr ll.2)) * A.u.tr ll.1
    ∧ Fintype.card (Fin (B.u.tr ll.2)) * A.u.tr ll.1 ≤ Fintype.card (A.α × B.α)
  rw [Fintype.card_fin, Fintype.card_prod]
  exact ⟨Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)),
    by rw [Nat.mul_comm]; exact Nat.mul_le_mul h2 h4⟩

lemma ranksOK_pow {A : BU} (hA : A.RanksOK) (n : ℕ) : (A.pow n).RanksOK := by
  induction n with
  | zero => exact hA
  | succ n ih => exact ranksOK_prod ih hA

lemma tgtsOK_pow {A : BU} (hA : A.TgtsOK) (n : ℕ) : (A.pow n).TgtsOK := by
  induction n with
  | zero => exact hA
  | succ n ih => exact tgtsOK_prod ih hA

end BU

end

end TensorEng
