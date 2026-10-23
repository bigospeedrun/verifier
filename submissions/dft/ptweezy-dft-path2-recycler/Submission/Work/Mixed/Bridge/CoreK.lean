import Submission.Work.Mixed.Bridge.Core
import Submission.Work.Mixed.MultiTarget
-- changed for the tensor-power extension (30103/10000000); see Submission.lean

/-!
# The K-target bundle of an engine (typechecked against the head-cut-sharp tree, 22 Oct 2026)

`bundle_ofList`: an engine `E` (any word with mixed targets, e-r3prog's `Eng`) whose live target ranks take the
DISTINCT ranks of a list `tg`, rank `tg[k].1` on exactly `G * tg[k].2` live roles, whose word has the histogram
`G * histFn paid` with every paid rank `≤ rmax < kmin`, and the moment fact of ONE unit
`moment m z1 paid ≤ moment m z1 tg`, gives the hypothesis bundle of `Eng.engine_seam_final` with the K-target rule
`Rule.ofList` (any K).  This replaces `bundle_of_eng` / `bridge_twoTarget` (K = 2) for the p3 unit (K = 6).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.PB
open Binary Matrix Finset GF MX RAM BlockAccounting

noncomputable section

section K
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]

/-- Target ranks counted on positions `range W` (through the layout `Q`) are counted on live roles. -/
lemma card_tq_eq (E : Eng α ρ σ) (r : ℕ) :
    ((range E.W).filter (fun x => E.tq x = r)).card = (Finset.univ.filter fun l : σ => E.tr l = r).card := by
  rw [Finset.card_filter, ← Fin.sum_univ_eq_sum_range (fun x => if E.tq x = r then 1 else 0) E.W]
  have h1 : ∀ i : Fin E.W, (if E.tq i = r then 1 else 0)
      = (fun l => if E.tr l = r then 1 else 0) (E.Q.index.symm i) := by
    intro i
    rw [tq_of_lt]
    rfl
  rw [Finset.sum_congr rfl (fun i _ => h1 i)]
  rw [Equiv.sum_comp E.Q.index.symm (fun l => if E.tr l = r then 1 else 0)]
  rw [Finset.card_filter]

/-- **The K-target bundle** of an engine. -/
theorem bundle_ofList (E : Eng α ρ σ) (tg paid : List (ℕ × ℕ)) (G : ℕ)
    (hpos : 0 < tg.length) (hnd : (tg.map Prod.fst).Nodup) {kmin rmax : ℕ}
    (htrv : ∀ l, E.tr l ∈ tg.map Prod.fst)
    (htrc : ∀ k : Fin tg.length, (Finset.univ.filter fun l : σ => E.tr l = tg[k.1].1).card = G * tg[k.1].2)
    (hhist : ∀ r, E.wd.hist r = G * histFn paid r) (hpaid : ∀ b ∈ paid, b.1 ≤ rmax)
    (hwr : ∀ mv ∈ E.wd, ∀ r, mv.rk? = some r → r ≤ rmax) (hsep : rmax < kmin)
    (htg : ∀ b ∈ tg, kmin ≤ b.1 ∧ b.1 ≤ Fintype.card α) (h2 : 2 ≤ kmin)
    (hatt : ∃ b ∈ tg, b.1 = kmin ∧ 1 ≤ G * b.2) {z1 : ℝ}
    (hmom : moment (Fintype.card α) z1 paid ≤ moment (Fintype.card α) z1 tg) :
    ∃ (R : MX.Rule) (typ : ℕ → Fin R.K), E.BridgeHyp R typ kmin ∧ R.RateQ z1 1 := by
  have hmx := mx_eq E
  have hrk1 : ∀ j : Fin E.nB, 1 ≤ E.rkI j := rkI_pos E
  have hrk : ∀ j : Fin E.nB, E.rkI j ≤ rmax := rkI_le E hwr
  have htgG : ∀ b ∈ scaleL G tg, kmin ≤ b.1 ∧ b.1 ≤ E.mx := by
    intro b hb
    obtain ⟨c, hc, rfl⟩ := mem_scaleL hb
    rw [hmx]; exact htg c hc
  have hattG : ∃ b ∈ scaleL G tg, b.1 = kmin ∧ 1 ≤ b.2 := by
    obtain ⟨c, hc, h1, h2'⟩ := hatt
    exact ⟨(c.1, G * c.2), List.mem_map.mpr ⟨c, hc, rfl⟩, h1, h2'⟩
  have hposG : 0 < (scaleL G tg).length := by simpa [scaleL] using hpos
  have hlen : (scaleL G tg).length = tg.length := by simp [scaleL]
  have hndG : ((scaleL G tg).map Prod.fst).Nodup := by
    have : (scaleL G tg).map Prod.fst = tg.map Prod.fst := by simp [scaleL, Function.comp_def]
    rw [this]; exact hnd
  have hget : ∀ k : Fin (scaleL G tg).length,
      (scaleL G tg)[k.1] = ((tg[k.1]'(hlen ▸ k.2)).1, G * (tg[k.1]'(hlen ▸ k.2)).2) := by
    intro k; simp [scaleL]
  refine ⟨MX.Rule.ofList E.mx (scaleL G tg) E.nB (fun j => E.rkI j) kmin rmax hrk1 hrk hsep htgG h2 hattG,
    MX.typeOf (scaleL G tg) hposG E.tq, ⟨rfl, rfl, fun j => rfl, ?_, ?_, rfl⟩, ?_⟩
  · -- htq
    intro x hx
    have hv : E.tq x ∈ (scaleL G tg).map Prod.fst := by
      have h1 := tq_of_lt E ⟨x, hx⟩
      simp only at h1
      have : (scaleL G tg).map Prod.fst = tg.map Prod.fst := by simp [scaleL, Function.comp_def]
      rw [this, h1]; exact htrv _
    exact MX.typeOf_spec (scaleL G tg) hposG E.tq x hv
  · -- hW
    intro k
    refine MX.card_typeOf (scaleL G tg) hposG hndG E.tq E.W (fun x hx => ?_) (fun k' => ?_) k
    · have h1 := tq_of_lt E ⟨x, hx⟩
      simp only at h1
      have : (scaleL G tg).map Prod.fst = tg.map Prod.fst := by simp [scaleL, Function.comp_def]
      rw [this, h1]; exact htrv _
    · rw [card_tq_eq, hget k']
      exact htrc ⟨k'.1, hlen ▸ k'.2⟩
  · -- the rate fact, `G` copies of the unit's moment fact
    refine MX.Rule.ofList_rateQ hrk1 hrk hsep htgG h2 hattG (paid := scaleL G paid) ?_ ?_ ?_
    · intro b hb
      obtain ⟨c, hc, rfl⟩ := mem_scaleL hb
      exact hpaid c hc
    · intro r
      rw [histFn_scaleL]
      exact (card_rkI E r).trans (hhist r)
    · rw [hmx]
      exact moment_scaleL_le hmom

end K

end
end PowerSaving.PB
end OAI

#print axioms OAI.PowerSaving.PB.bundle_ofList
