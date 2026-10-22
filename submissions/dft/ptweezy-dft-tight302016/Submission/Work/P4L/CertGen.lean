import Submission.Work.P4L.Word
import Submission.Work.Mixed.Bridge.Core
-- changed for the tensor-power extension (30103/10000000); see Submission.lean

/-!
# P4-L-fresh: the certificate with its histogram and target counts, for ANY provider (generic)

`certGen`: from `P4L.wordCert`, for any provider `I`, start frames `base`, helper end sets `D`, a price list `P` of ONE
gauge copy (`hP`: nine calls, the window blocks of `|T|` ports, the helpers' end blocks) and a target list `L` of one
gauge copy (`hL`: the main roles `|T|` per kind, the helpers `9` per slot), the word has the mixed certificate with
block targets `rawTz`, the histogram `|Γ| * histFn P` and the target counts `|Γ| * histFn L`.  Everything here is
generic in the types, so no cardinality of the gauge group `Γ = Orth (LC (Fin 8) H l)` is ever reduced; an instance
only supplies `hP` and `hL`, statements about one gauge copy.
No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace P4L
open Binary Matrix Finset RAM SS CB RF BC GX GF XHostTW P4Ctrl

noncomputable section

/-- counting the live roles of a given target rank: `|Γ|` copies of the per-copy count. -/
lemma card_live {Γ T Sl : Type} [Fintype Γ] [DecidableEq Γ] [Fintype T] [DecidableEq T] [Fintype Sl]
    [DecidableEq Sl] (f : PLive Γ T Sl → ℕ) (fm : R8 → ℕ) (ff : Sl → ℕ)
    (hm : ∀ g i t, f (Sum.inl (g, (i, t))) = fm i) (hf : ∀ g k q, f (Sum.inr (g, (k, q))) = ff q) (r : ℕ) :
    (Finset.univ.filter fun l => f l = r).card
      = Fintype.card Γ * ∑ i, Fintype.card T * (if fm i = r then 1 else 0)
        + Fintype.card Γ * (9 * ∑ q, if ff q = r then 1 else 0) := by
  rw [Finset.card_filter, Fintype.sum_sum_type]
  have h1 : ∀ g : Γ, (∑ y : R8 × T, if f (Sum.inl (g, y)) = r then 1 else 0)
      = ∑ i, Fintype.card T * (if fm i = r then 1 else 0) := by
    intro g
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have e : ∀ t : T, (if f (Sum.inl (g, (i, t))) = r then 1 else 0) = (if fm i = r then 1 else 0) :=
      fun t => by rw [hm g i t]
    rw [Finset.sum_congr rfl (fun t _ => e t), Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have h2 : ∀ g : Γ, (∑ y : Fin 9 × Sl, if f (Sum.inr (g, y)) = r then 1 else 0)
      = 9 * ∑ q, if ff q = r then 1 else 0 := by
    intro g
    rw [Fintype.sum_prod_type]
    have e : ∀ (k : Fin 9) (q : Sl),
        (if f (Sum.inr (g, (k, q))) = r then 1 else 0) = (if ff q = r then 1 else 0) :=
      fun k q => by rw [hf g k q]
    rw [Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun q _ => e k q)), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have h1' : (∑ x : Γ × (R8 × T), if f (Sum.inl x) = r then 1 else 0)
      = Fintype.card Γ * ∑ i, Fintype.card T * (if fm i = r then 1 else 0) := by
    rw [Fintype.sum_prod_type, Finset.sum_congr rfl (fun g _ => h1 g), Finset.sum_const, Finset.card_univ,
      smul_eq_mul]
  have h2' : (∑ x : Γ × (Fin 9 × Sl), if f (Sum.inr x) = r then 1 else 0)
      = Fintype.card Γ * (9 * ∑ q, if ff q = r then 1 else 0) := by
    rw [Fintype.sum_prod_type, Finset.sum_congr rfl (fun g _ => h2 g), Finset.sum_const, Finset.card_univ,
      smul_eq_mul]
  rw [h1', h2']

/-- a word priced as `G` copies of a list has `G` copies of its histogram. -/
lemma hist_of_price {α ρ : Type} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] (w : GWord α ρ)
    (G : ℕ) (L : List (ℕ × ℕ)) (h : ∀ φ, w.costR φ = (G : ℝ) * listCost φ L) (r : ℕ) :
    w.hist r = G * BlockAccounting.histFn L r := by
  have h1 := PB.hist_eq_price h r
  have hl : listCost (PB.ind r) L = (BlockAccounting.histFn L r : ℝ) := listCost_ind L r
  rw [hl] at h1
  exact_mod_cast h1

/-- the price identity of `certGen`, with every quantity a variable (no atom of the instance is compared). -/
lemma price_alg (G c t w s : ℝ) : 9 * (G * c) + G * t * w + G * 9 * s = G * (9 * c + t * w + 9 * s) := by ring

section Gen
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T] [Fintype Sl] [DecidableEq Sl]
  [Fintype C] [DecidableEq C] {Ok : ∀ {β : Type} [Fintype β] [DecidableEq β], GWin H β → Prop}
  (I : GInvW H T Sl C Ok) (base : T → OBase H) (l : H) (hbase : ∀ t, I.tv t = (base t).v l)
  (hH : Fintype.card H = 9) (hOk : ∀ (n : ℕ) (d : Orth (LC (Fin 8) H l)), Ok (win401N l hH n d))

include hbase hH hOk in
/-- **The P4-L-fresh certificate with its histogram and target counts**, for any provider. -/
theorem certGen (D : Sl → Finset (LC (Fin 8) H l)) (hload : ∀ q, Fintype.card H - (I.ent q).dim ≤ (D q).card)
    (hrk : ∀ q, (D q).card - (Fintype.card H - (I.ent q).dim) < Fintype.card (LC (Fin 8) H l))
    (P L : List (ℕ × ℕ))
    (hP : ∀ φ, 9 * I.cost φ + (Fintype.card T : ℝ) * (6 * bcost φ 8 + 4 * bcost φ 16 + 2 * bcost φ 32)
      + 9 * ∑ q, bcost φ ((D q).card - (Fintype.card H - (I.ent q).dim)) = listCost φ P)
    (hL : ∀ r, ∑ i, Fintype.card T * (if rankM i = r then 1 else 0)
      + 9 * ∑ q, (if (D q).card = r then 1 else 0) = BlockAccounting.histFn L r) :
    ∃ w : GWord (LC (Fin 8) H l) (PRole (Orth (LC (Fin 8) H l)) T Sl C),
      w.Proper (Fintype.card (LC (Fin 8) H l)) ∧
      MX.GLiveKernelM (fun l' : PLive (Orth (LC (Fin 8) H l)) T Sl => (Sum.inl l' : PRole (Orth (LC (Fin 8) H l)) T Sl C))
        (fun l' => blockMat (rawTz base l D l').2) w ∧
      (∀ r, w.hist r = Fintype.card (Orth (LC (Fin 8) H l)) * BlockAccounting.histFn P r) ∧
      (∀ r, (Finset.univ.filter fun l' : PLive (Orth (LC (Fin 8) H l)) T Sl => (rawTz base l D l').1 = r).card
        = Fintype.card (Orth (LC (Fin 8) H l)) * BlockAccounting.histFn L r) := by
  obtain ⟨w, hwP, hwc, hwk⟩ := wordCert (I := I) (base := base) (l := l) (hbase := hbase) (hH := hH)
    (hOk := hOk) D hload hrk
  have hcost : ∀ φ, w.costR φ = (Fintype.card (Orth (LC (Fin 8) H l)) : ℝ) * listCost φ P := by
    intro φ
    rw [hwc φ, rawCost, ← hP φ]
    exact price_alg _ _ _ _ _
  refine ⟨w, hwP, hwk, hist_of_price w _ P hcost, fun r => ?_⟩
  rw [card_live (fun l' => (rawTz base l D l').1) rankM (fun q => (D q).card)
    (fun g i t => rawTz_main base l hH D g i t) (fun g k q => rawTz_fresh base l D g k q) r, ← mul_add, hL r]

end Gen

end
end P4L
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.P4L.certGen
