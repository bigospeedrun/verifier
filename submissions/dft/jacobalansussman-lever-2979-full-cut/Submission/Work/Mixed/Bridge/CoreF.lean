import Submission.Work.Mixed.Bridge.Core

/-!
# fc-engine: the FULL cut with the 24 + 24 split, from the heads-first network certificate to the mixed engine

Round wht45/fullcut (19-20 Oct 2026).  p-bridge's `Core.lean` builds the HALF-cut engine (`HFNet.cutWord`,
`cut_heads_half`).  This file builds the FULL-cut engine of the same certificate:

* the heads (one block of rank `rk l` per head role `l ∈ L`, directions the lines `S l` of a frame `A l`) are removed
  ENTIRELY (e-r45m1's `MX.cut_heads_full`): the body followed by one free shift per head role realises the block of
  the remaining lines `(S l)ᶜ` on the head roles (target rank `card α - |S l|`) and the kernel elsewhere;
* then EVERY block of rank `a + b` of that word is split into its first `a` and last `b` directions
  (e-r45m1's `MX.splitWord`; `gwalk_splitWord`: the walk, hence the mixed certificate, is unchanged;
  `hist_splitWord`: the histogram moves rank `a + b` to ranks `a` and `b`).

So the engine word is `fullWord = splitWord a b (body ++ shifts)`, its targets are `cutTgt L A S`, and every paid
rank is a rank of the full-cut profile.  Separation is `rmax < card α - |S l|` (for design B: `24 < 25`).
The rule, `BridgeHyp` and the rate fact come from p-bridge's generic `bundle_of_eng`; the engine theorem from
e-r3cost's `Eng.engine_seam_final` (Theorem 1G), exactly as for the half cut.

* `fullWord`, `fullWord_hist`, `fullWord_proper`         the word, its histogram, properness;
* `fullWord_hist_eq`                                       its histogram is `G * histFn cut` given the profile identity
                                                           `hcutF` (unit profile -> full-cut profile);
* `ranks_le_of_hist`                                       separation from the histogram;
* `fullEng`                                                the engine record (certificate: `cut_heads_full` + split);
* `full_bundle`, `full_engine`                             the hypothesis bundle of `Eng.engine_seam_final` and the
                                                           engine theorem (the `hillsZ_program` shape);
* `hcutF_of_check`                                         the profile identity from a finite check (`decide`).
fc-engine (wht45/fullcut) on p-bridge's Core.lean and e-r45m1's HeadM1.lean; prepared with assistance from Claude.
No `sorry`, no new axiom, no `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.PB
open Binary Matrix Finset GF MX RAM

noncomputable section

universe U

section CutF
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]

/-- **The full-cut word**: the body (the heads removed), one free shift per head role, then every block of rank
`a + b` split into its first `a` and its last `b` directions. -/
def fullWord (e : σ → ρ) (L : List σ) (A : σ → OBase α) (S : σ → Finset α) (a b : ℕ) (body : GWord α ρ) :
    GWord α ρ :=
  MX.splitWord a b (body ++ shiftWord e L (cutShift A S))

/-- Histogram of the full-cut word: the body's, with its rank-`(a + b)` blocks moved to ranks `a` and `b`. -/
lemma fullWord_hist (e : σ → ρ) (L : List σ) (A : σ → OBase α) (S : σ → Finset α) {a b : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (body : GWord α ρ) (r : ℕ) :
    (fullWord e L A S a b body).hist r
      = (if r = a + b then 0 else body.hist r) + (if r = a then body.hist (a + b) else 0)
        + (if r = b then body.hist (a + b) else 0) := by
  unfold fullWord
  rw [MX.hist_splitWord a b ha hb]
  simp only [MX.hist_append, MX.hist_shiftWord, add_zero]

/-- Properness of the full-cut word (every paid rank in `[1, u)`). -/
lemma fullWord_proper (e : σ → ρ) (L : List σ) (A : σ → OBase α) (S : σ → Finset α) {a b u : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hau : a < u) (hbu : b < u) (body : GWord α ρ) (hP : body.Proper u) :
    (fullWord e L A S a b body).Proper u := by
  unfold fullWord
  apply MX.proper_splitWord u a b ha hb hau hbu
  intro mv hmv
  rcases List.mem_append.mp hmv with h | h
  · exact hP mv h
  · exact MX.proper_shiftWord u e L _ mv h

/-- **(d) for the full cut**: if the body is priced as `G` copies of the unit profile `U` minus `|L| = G Hd` heads of
rank `a + b`, and the full-cut profile `cut` is `U` with the `Hd` heads removed and every remaining rank-`(a + b)`
block split into ranks `a` and `b` (`hcutF`), the full-cut word's histogram is `G` copies of `cut`. -/
theorem fullWord_hist_eq (e : σ → ρ) (L : List σ) (A : σ → OBase α) (S : σ → Finset α) {a b : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (body : GWord α ρ) {G Hd : ℕ} {U cut : List (ℕ × ℕ)}
    (hcost : ∀ φ, body.costR φ = (G : ℝ) * listCost φ U - (L.length : ℝ) * φ (a + b))
    (hcutF : ∀ r, BlockAccounting.histFn cut r
      = (if r = a + b then 0 else BlockAccounting.histFn U r)
        + (if r = a then BlockAccounting.histFn U (a + b) - Hd else 0)
        + (if r = b then BlockAccounting.histFn U (a + b) - Hd else 0))
    (hLlen : L.length = G * Hd) (r : ℕ) :
    (fullWord e L A S a b body).hist r = G * BlockAccounting.histFn cut r := by
  have h1 := hist_headsFirst hcost r
  have h2 := hist_headsFirst hcost (a + b)
  rw [if_pos rfl, hLlen] at h2
  rw [hLlen] at h1
  rw [fullWord_hist e L A S ha hb body r, hcutF r]
  have hm : G * (BlockAccounting.histFn U (a + b) - Hd)
      = G * BlockAccounting.histFn U (a + b) - G * Hd := by rw [Nat.mul_sub]
  simp only [Nat.mul_add, mul_ite, mul_zero, hm]
  by_cases hr : r = a + b
  · subst hr
    generalize G * BlockAccounting.histFn U (a + b) = Y at *
    generalize G * Hd = K at *
    generalize body.hist (a + b) = B' at *
    split_ifs <;> omega
  · rw [if_neg hr] at h1
    generalize G * BlockAccounting.histFn U (a + b) = Y at *
    generalize G * BlockAccounting.histFn U r = X at *
    generalize G * Hd = K at *
    generalize body.hist (a + b) = B' at *
    generalize body.hist r = B at *
    split_ifs <;> omega

/-- **(b) Separation from the histogram**: every paid rank of a word whose histogram is `G` copies of a profile is a
rank of the profile, hence at most `rmax`. -/
theorem ranks_le_of_hist {w : GWord α ρ} {G : ℕ} {cut : List (ℕ × ℕ)} {rmax : ℕ}
    (hhist : ∀ r, w.hist r = G * BlockAccounting.histFn cut r) (hcutr : ∀ q ∈ cut, q.1 ≤ rmax) :
    ∀ mv ∈ w, ∀ r, mv.rk? = some r → r ≤ rmax := by
  intro mv hmv r hr
  have h1 := hist_pos_of_mem hmv hr
  rw [hhist] at h1
  have h2 : BlockAccounting.histFn cut r ≠ 0 := by
    intro h0
    rw [h0, Nat.mul_zero] at h1
    omega
  have h3 := BlockAccounting.mem_keys_of_histFn_ne_zero cut r h2
  unfold BlockAccounting.keys at h3
  rw [List.mem_toFinset, List.mem_map] at h3
  obtain ⟨q, hq, rfl⟩ := h3
  exact hcutr q hq

/-- **The full-cut engine** of a heads-first certificate: word `fullWord` (heads removed, free shifts, every block
of rank `a + b` split), targets `cutTgt L A S` (rank `card α - c` on the head roles, `card α` elsewhere).
Its mixed certificate is e-r45m1's `cut_heads_full` followed by `GLiveKernelM.splitWord`. -/
def fullEng (e : σ → ρ) (he : Function.Injective e) (L : List σ) (hL : L.Nodup) (rk : σ → ℕ)
    (z : ∀ l, Fin (rk l) → Space α) (ind : ∀ l, LinearIndependent F (z l)) (A : σ → OBase α)
    (S : σ → Finset α) (hz : ∀ l ∈ L, ∀ x, bph (z l) x = bph ((A l).fam (S l)) x) {c : ℕ}
    (hS : ∀ l ∈ L, (S l).card = c) (body : GWord α ρ) (hP : body.Proper (Fintype.card α))
    (hk : GLiveKernel e (headWord e L rk z ind ++ body)) (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hau : a < Fintype.card α) (hbu : b < Fintype.card α) (rmax : ℕ)
    (hwr : ∀ mv ∈ fullWord e L A S a b body, ∀ r, mv.rk? = some r → r ≤ rmax)
    (hsep : rmax < Fintype.card α - c) (hc : c < Fintype.card α) (h3 : 3 ≤ Fintype.card α)
    (hσ : 0 < Fintype.card σ) : Eng α ρ σ where
  X := Layout.someLayout α
  R := Layout.someLayout ρ
  Q := Layout.someLayout σ
  e := e
  he := he
  tr := fun l => (cutTgt L A S l).1
  tz := fun l => (cutTgt L A S l).2
  tind := cutTgt_indep L A S
  tr_le := fun l => by
    show (cutTgt L A S l).1 ≤ (Layout.someLayout α).n
    rw [← Layout.card (Layout.someLayout α), cutTgt_rank]
    split_ifs <;> omega
  tr_pos := fun l => by
    show 1 ≤ (cutTgt L A S l).1
    rw [cutTgt_rank]
    split_ifs with hl
    · rw [hS l hl]; omega
    · omega
  wd := fullWord e L A S a b body
  hP := by
    rw [← Layout.card (Layout.someLayout α)]
    exact fullWord_proper e L A S ha hb hau hbu body hP
  sep := fun mv hmv r hr l => by
    have h1 := hwr mv hmv r hr
    show r < (cutTgt L A S l).1
    rw [cutTgt_rank]
    split_ifs with hl
    · rw [hS l hl]; omega
    · omega
  W_pos := by rw [← Layout.card (Layout.someLayout σ)]; exact hσ
  three := by rw [← Layout.card (Layout.someLayout α)]; exact h3
  hw := MX.GLiveKernelM.splitWord a b (cut_heads_full he L hL rk z ind A S hz body hk)

/-- **(f) THE BUNDLE, full cut**: from the heads-first certificate (heads on the lines `S l`, `|S l| = c`), the
full-cut profile identity and the moment fact for one unit (target `card α - c` on the `Hd` cut arrays of each of the
`G` copies), the hypothesis bundle of `Eng.engine_seam_final`. -/
theorem full_bundle (e : σ → ρ) (he : Function.Injective e) (L : List σ) (hL : L.Nodup) (rk : σ → ℕ)
    (z : ∀ l, Fin (rk l) → Space α) (ind : ∀ l, LinearIndependent F (z l)) (A : σ → OBase α)
    (S : σ → Finset α) (hz : ∀ l ∈ L, ∀ x, bph (z l) x = bph ((A l).fam (S l)) x) {c : ℕ}
    (hS : ∀ l ∈ L, (S l).card = c) (body : GWord α ρ) (hP : body.Proper (Fintype.card α))
    (hk : GLiveKernel e (headWord e L rk z ind ++ body)) (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hau : a < Fintype.card α) (hbu : b < Fintype.card α) {G W0 Hd : ℕ} {U : List (ℕ × ℕ)}
    (cut : List (ℕ × ℕ))
    (hcost : ∀ φ, body.costR φ = (G : ℝ) * listCost φ U - (L.length : ℝ) * φ (a + b))
    (hcutF : ∀ r, BlockAccounting.histFn cut r
      = (if r = a + b then 0 else BlockAccounting.histFn U r)
        + (if r = a then BlockAccounting.histFn U (a + b) - Hd else 0)
        + (if r = b then BlockAccounting.histFn U (a + b) - Hd else 0))
    (hLlen : L.length = G * Hd) (hσ : Fintype.card σ = G * W0) (hG : 1 ≤ G) (hHd : 1 ≤ Hd)
    (hHW : Hd ≤ W0) (rmax : ℕ) (hcutr : ∀ q ∈ cut, q.1 ≤ rmax) (hsep : rmax < Fintype.card α - c)
    (hc1 : 1 ≤ c) (hc : c < Fintype.card α) (h2 : 2 ≤ Fintype.card α - c) {z1 : ℝ}
    (hmom : BlockAccounting.moment (Fintype.card α) z1 cut
      ≤ ((W0 - Hd : ℕ) : ℝ) + BlockAccounting.T (Fintype.card α) z1 (Fintype.card α - c) Hd) :
    ∃ (E : Eng α ρ σ) (R : MX.Rule) (typ : ℕ → Fin R.K),
      E.wd = fullWord e L A S a b body ∧ E.e = e ∧ (∀ l, E.tr l = (cutTgt L A S l).1) ∧
      E.mx = Fintype.card α ∧ E.BridgeHyp R typ (Fintype.card α - c) ∧ R.RateQ z1 1 := by
  have hhist : ∀ r, (fullWord e L A S a b body).hist r = G * BlockAccounting.histFn cut r :=
    fullWord_hist_eq e L A S ha hb body hcost hcutF hLlen
  have hwr := ranks_le_of_hist hhist hcutr
  have hH : 1 ≤ L.length := by
    rw [hLlen]; exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hσ0 : 0 < Fintype.card σ := by
    rw [hσ]; exact Nat.mul_pos (by omega) (by omega)
  let E := fullEng e he L hL rk z ind A S hz hS body hP hk a b ha hb hau hbu rmax hwr hsep hc (by omega) hσ0
  obtain ⟨R, typ, hB, hR⟩ := bundle_of_eng E L hL A S (fun l => rfl) hS hc1 hc hsep h2 hwr hH
    cut hcutr hhist hLlen hσ hmom
  exact ⟨E, R, typ, rfl, rfl, fun l => rfl, mx_eq E, hB, hR⟩

/-- **THE FULL-CUT ENGINE THEOREM** (the `hillsZ_program` shape at every `zE ∈ (z1, 1]`): the bundle fed to
`Eng.engine_seam_final`. -/
theorem full_engine (e : σ → ρ) (he : Function.Injective e) (L : List σ) (hL : L.Nodup) (rk : σ → ℕ)
    (z : ∀ l, Fin (rk l) → Space α) (ind : ∀ l, LinearIndependent F (z l)) (A : σ → OBase α)
    (S : σ → Finset α) (hz : ∀ l ∈ L, ∀ x, bph (z l) x = bph ((A l).fam (S l)) x) {c : ℕ}
    (hS : ∀ l ∈ L, (S l).card = c) (body : GWord α ρ) (hP : body.Proper (Fintype.card α))
    (hk : GLiveKernel e (headWord e L rk z ind ++ body)) (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hau : a < Fintype.card α) (hbu : b < Fintype.card α) {G W0 Hd : ℕ} {U : List (ℕ × ℕ)}
    (cut : List (ℕ × ℕ))
    (hcost : ∀ φ, body.costR φ = (G : ℝ) * listCost φ U - (L.length : ℝ) * φ (a + b))
    (hcutF : ∀ r, BlockAccounting.histFn cut r
      = (if r = a + b then 0 else BlockAccounting.histFn U r)
        + (if r = a then BlockAccounting.histFn U (a + b) - Hd else 0)
        + (if r = b then BlockAccounting.histFn U (a + b) - Hd else 0))
    (hLlen : L.length = G * Hd) (hσ : Fintype.card σ = G * W0) (hG : 1 ≤ G) (hHd : 1 ≤ Hd)
    (hHW : Hd ≤ W0) (rmax : ℕ) (hcutr : ∀ q ∈ cut, q.1 ≤ rmax) (hsep : rmax < Fintype.card α - c)
    (hc1 : 1 ≤ c) (hc : c < Fintype.card α) (h2 : 2 ≤ Fintype.card α - c) {z1 zE : ℝ}
    (hmom : BlockAccounting.moment (Fintype.card α) z1 cut
      ≤ ((W0 - Hd : ℕ) : ℝ) + BlockAccounting.T (Fintype.card α) z1 (Fintype.card α - c) Hd)
    (hz1 : 0 < z1) (h12 : z1 < zE) (hzE : zE ≤ 1)
    (m : Bool) (cl : Paint) {ι : Type U} (k : ι → ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2 ^ k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2 ^ k i * envelope zE (k i)) := by
  obtain ⟨E, R, typ, -, -, -, -, hB, hR⟩ :=
    full_bundle e he L hL rk z ind A S hz hS body hP hk a b ha hb hau hbu cut hcost hcutF hLlen hσ hG hHd hHW
      rmax hcutr hsep hc1 hc h2 hmom
  exact E.engine_seam_final hB E.mx le_rfl hR hz1 h12 hzE m cl k v

end CutF

/-! ## The full-cut profile identity by a finite check -/

/-- The full-cut profile identity `hcutF` for all ranks from a check on a finite key list `K` containing every rank
of both profiles and the split ranks `a`, `b` (`decide` discharges `hchk` for concrete lists). -/
theorem hcutF_of_check (U cut : List (ℕ × ℕ)) (a b Hd : ℕ) (K : List ℕ)
    (hU : ∀ q ∈ U, q.1 ∈ K) (hc : ∀ q ∈ cut, q.1 ∈ K) (ha : a ∈ K) (hb : b ∈ K)
    (hchk : ∀ r ∈ K, BlockAccounting.histFn cut r
      = (if r = a + b then 0 else BlockAccounting.histFn U r)
        + (if r = a then BlockAccounting.histFn U (a + b) - Hd else 0)
        + (if r = b then BlockAccounting.histFn U (a + b) - Hd else 0)) :
    ∀ r, BlockAccounting.histFn cut r
      = (if r = a + b then 0 else BlockAccounting.histFn U r)
        + (if r = a then BlockAccounting.histFn U (a + b) - Hd else 0)
        + (if r = b then BlockAccounting.histFn U (a + b) - Hd else 0) := by
  intro r
  by_cases hr : r ∈ K
  · exact hchk r hr
  · have h0 : ∀ l : List (ℕ × ℕ), (∀ q ∈ l, q.1 ∈ K) → BlockAccounting.histFn l r = 0 := by
      intro l hl
      by_contra hne
      have := BlockAccounting.mem_keys_of_histFn_ne_zero l r hne
      unfold BlockAccounting.keys at this
      rw [List.mem_toFinset, List.mem_map] at this
      obtain ⟨q, hq, rfl⟩ := this
      exact hr (hl q hq)
    rw [h0 U hU, h0 cut hc, if_neg (fun h : r = a => hr (h ▸ ha)), if_neg (fun h : r = b => hr (h ▸ hb))]
    split_ifs <;> rfl

end
end PowerSaving.PB
end OAI

#print axioms OAI.PowerSaving.PB.fullWord_hist
#print axioms OAI.PowerSaving.PB.fullWord_proper
#print axioms OAI.PowerSaving.PB.fullWord_hist_eq
#print axioms OAI.PowerSaving.PB.ranks_le_of_hist
#print axioms OAI.PowerSaving.PB.full_bundle
#print axioms OAI.PowerSaving.PB.full_engine
#print axioms OAI.PowerSaving.PB.hcutF_of_check
