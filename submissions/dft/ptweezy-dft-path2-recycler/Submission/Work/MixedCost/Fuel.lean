import Submission.Work.Mixed.Prog.Glue
import Submission.Work.MixedCost.TopDom
import Submission.Work.MixedCost.Wire

/-!
# Mixed engine: the remaining generic hypotheses of `mixed_close` (agent e-r3cost)

For the descriptors `VD` of e-r3prog's open body (`Glue.lean`):

* `shapeD`        the shape of a descriptor (top `Do(n,B)` ↦ `.top n B`, class ↦ `.cls n h μ`);
* `fuelD`, `can_fuel`, `rank_lt_fuel`, `small_fuel`   the fuel (`(n+1)(n+2)+1`, computed from the input);
* `bnd_kidsTop`   the word driver does not grow along a top job's calls;
* `kidsV_top_shape`, `locD_top_dom`   the top halves of `hkids` and `hloc`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset GF MXR
noncomputable section

universe U

namespace Eng
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]
variable (E : Eng α ρ σ)

/-- The shape of a descriptor. -/
def shapeD : MDesc → MX.Shape
  | .top n B _ => .top n B
  | .cls n h μ _ _ _ _ => .cls n h μ

/-- The size `n` of a descriptor. -/
def nD : MDesc → ℕ
  | .top n _ _ => n
  | .cls n _ _ _ _ _ _ => n

/-- The fuel of a descriptor. -/
def fuelD (d : MDesc) : ℕ := (nD d + 1) * (nD d + 2) + 1

lemma enc_fst (cl : Paint) (d : MDesc) : (E.enc cl d).1 = nD d := by
  cases d <;> rfl

lemma bndD_ge (d : MDesc) : 2 ^ nD d ≤ bndD d := by
  cases d with
  | top n B v => exact Nat.le_mul_of_pos_left _ (by omega)
  | cls n h μ o BS J sup => exact Nat.le_mul_of_pos_left _ (by omega)

/-- **The fuel, computed from the input** (constant work). -/
lemma can_fuel {kmin : ℕ} (cl : Paint) (m : Bool) {P : E.VD kmin → Prop} :
    Can m (fun d : {d : E.VD kmin // P d} => bndD d.1.1) (portIn cl) w (fun d => E.encV kmin cl d.1)
      (fun d => fuelD d.1.1) (fun _ => 0) := by
  have hn : Knows m (fun d : {d : E.VD kmin // P d} => bndD d.1.1) (portIn cl) (fun d => E.encV kmin cl d.1)
      (fun d => nD d.1.1) := (Can.first).cong (fun _ => rfl) (fun d => E.enc_fst cl d.1.1)
  have hns : Small (fun d : {d : E.VD kmin // P d} => bndD d.1.1) (fun d => nD d.1.1) :=
    ⟨1, fun d => by have := bndD_ge d.1.1; have := (Nat.lt_two_pow_self : nD d.1.1 < 2 ^ nD d.1.1); simp; omega⟩
  have h1 := hn.plus (Can.wc 1) hns (Small.const _ 1)
  have h2 := hn.plus (Can.wc 2) hns (Small.const _ 2)
  have h3 := h1.times h2 (hns.add (Small.const _ 1)) (hns.add (Small.const _ 2))
  exact h3.plus (Can.wc 1) ((hns.add (Small.const _ 1)).mul (hns.add (Small.const _ 2))) (Small.const _ 1)

/-- The fuel is polynomial in the driver. -/
lemma small_fuel {kmin : ℕ} {P : E.VD kmin → Prop} :
    Small (fun d : {d : E.VD kmin // P d} => bndD d.1.1) (fun d => fuelD d.1.1) := by
  refine ⟨2, fun d => ?_⟩
  have h1 := bndD_ge d.1.1
  have h2 : nD d.1.1 < 2 ^ nD d.1.1 := Nat.lt_two_pow_self
  unfold fuelD
  nlinarith

/-- The fuel exceeds the rank of every reachable shape. -/
lemma rank_lt_fuel (R : MX.Rule) (d : MDesc) (hd : R.InvS (shapeD d)) : (shapeD d).rank < fuelD d := by
  cases d with
  | top n B v => simp only [shapeD, MX.Shape.rank, fuelD, nD]; omega
  | cls n h μ o BS J sup =>
    simp only [shapeD, MX.Rule.InvS] at hd
    simp only [shapeD, MX.Shape.rank, fuelD, nD]
    have h1 : 2 ^ h ≤ R.kmin ^ h := Nat.pow_le_pow_left R.two_le_kmin _
    have h2 : R.kmin ^ h ≤ R.m * μ * R.kmin ^ h := by
      have : 1 ≤ R.m * μ := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by have := R.two_le_m; omega) (by omega))
      exact Nat.le_mul_of_pos_left _ this
    have h3 : h < 2 ^ h := Nat.lt_two_pow_self
    have hh : h ≤ n := by omega
    nlinarith

/-- The word driver does not grow along a top job's calls. -/
lemma bnd_kidsTop (kmin n0 n B : ℕ) (v : ℕ → Bits n → ℂ) :
    ∀ c ∈ E.kidsTop kmin n0 n B v, bndD c ≤ bndD (MDesc.top n B v) := by
  intro c hc
  unfold kidsTop at hc
  split_ifs at hc with hcond
  · obtain ⟨t, ht, hc⟩ := List.mem_flatMap.1 hc
    have hlam : 1 ≤ B / E.topN kmin n := by have := List.mem_range.1 ht; omega
    rcases List.mem_cons.1 hc with rfl | hc
    · simp only [topRoot, bndD]; exact le_rfl
    · obtain ⟨j, -, rfl⟩ := List.mem_map.1 hc
      simp only [topRest, bndD]
      have hs := topSz_le E kmin n j
      have hB : 1 ≤ B := by
        have h1 : E.topN kmin n ≠ 0 := by intro h0; rw [h0, Nat.div_zero] at hlam; omega
        have := hcond.2; omega
      have e1 : (2 ^ E.topSz kmin n j + 2) * 2 ^ (n - E.topSz kmin n j) =
          2 ^ n + 2 * 2 ^ (n - E.topSz kmin n j) := by
        rw [add_mul, ← pow_add, Nat.add_sub_cancel' hs]
      have e2 : 2 ^ (n - E.topSz kmin n j) ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _)
      rw [e1]
      have e3 : 1 * 2 ^ n ≤ B * 2 ^ n := Nat.mul_le_mul_right _ hB
      have e4 : (B + 2) * 2 ^ n = B * 2 ^ n + 2 * 2 ^ n := by ring
      rw [e4]
      omega
  · simp at hc

lemma map_attach_val {β γ : Type*} {P : β → Prop} (l : List β) (hP : ∀ c ∈ l, P c) (f : β → γ) :
    ((l.attach.map (fun c => (⟨c.1, hP c.1 c.2⟩ : {c // P c}))).map (fun c => f c.1)) = l.map f := by
  rw [List.map_map]
  exact List.attach_map_val

/-- **The top half of `hkids`.** -/
theorem kidsV_top_shape {kmin : ℕ} (hk : E.KMin kmin) (n0 : ℕ) (hn0 : E.mx ≤ n0)
    {R : MX.Rule} {typ : ℕ → Fin R.K} (H : E.BridgeHyp R typ kmin) (d : E.VD kmin) (n B : ℕ)
    (v : ℕ → Bits n → ℂ) (hd : d.1 = MDesc.top n B v) :
    ((↑(E.kidsV hk n0 hn0 d) : Multiset (E.VD kmin)).map (fun c => shapeD c.1)) = R.kidsS n0 (shapeD d.1) := by
  rw [Multiset.map_coe]
  unfold kidsV
  simp only [List.map_map, Function.comp_def]
  rw [List.attach_map_val]
  rw [hd]
  exact H.kidsTop_shape shapeD (fun _ _ _ => rfl) (fun _ _ _ _ _ _ _ => rfl) n0 n B v

end Eng

end
end PowerSaving.RAM
end OAI

#print axioms OAI.PowerSaving.RAM.Eng.can_fuel
#print axioms OAI.PowerSaving.RAM.Eng.rank_lt_fuel
#print axioms OAI.PowerSaving.RAM.Eng.bnd_kidsTop
#print axioms OAI.PowerSaving.RAM.Eng.kidsV_top_shape
