import Submission.Work.MixedCost.Fuel
import Submission.Work.MixedCost.SeamPort

/-!
# Mixed engine: `mixed_close` on the ONE open body, down to the seam (agent e-r3cost)

`engine_portTop`: e-r3prog's open body `Eng.hbody` (Glue.lean) closed by `mixed_close`, given the CLASS halves of
`hkids`, `hloc`, `hbd` (hypotheses `hkC`, `hlC`, `hbC`, e-r3prog's to prove); the top halves are mine
(`kidsV_top_shape`, `locTop_dom`, `bnd_kidsTop`), and the fuel (`can_fuel`, `rank_lt_fuel`, `small_fuel`).
`engine_seam`: with `seam_of_port`, the kernel on one vector of `k` bits in work `O(2^k * envelope z k)`.
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

lemma mem_kidsV {kmin : ℕ} (hk : E.KMin kmin) (n0 : ℕ) (hn0 : E.mx ≤ n0) (d c : E.VD kmin)
    (hc : c ∈ (↑(E.kidsV hk n0 hn0 d) : Multiset (E.VD kmin))) : c.1 ∈ E.kidsAll kmin n0 d.1 := by
  rw [Multiset.mem_coe] at hc
  unfold kidsV at hc
  obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
  exact c'.2

lemma kidsV_shape_eq {kmin : ℕ} (hk : E.KMin kmin) (n0 : ℕ) (hn0 : E.mx ≤ n0) (d : E.VD kmin) :
    ((↑(E.kidsV hk n0 hn0 d) : Multiset (E.VD kmin)).map (fun c => shapeD c.1)) =
      (((E.kidsAll kmin n0 d.1).map shapeD : List MX.Shape) : Multiset MX.Shape) := by
  rw [Multiset.map_coe]
  unfold kidsV
  simp only [List.map_map, Function.comp_def]
  rw [List.attach_map_val]

/-- **`mixed_close` on the open body**: the closed engine on every family of top descriptors. -/
theorem engine_portTop {kmin : ℕ} (hk : E.KMin kmin) (n0 : ℕ) (hn0 : E.mx ≤ n0)
    {R : MX.Rule} {typ : ℕ → Fin R.K} (H : E.BridgeHyp R typ kmin) (m : Bool) (cl : Paint)
    (hkC : ∀ n h μ o BS J sup, E.Valid kmin (MDesc.cls n h μ o BS J sup) → R.InvS (MX.Shape.cls n h μ) →
      (((E.kidsC (MDesc.cls n h μ o BS J sup)).map shapeD : List MX.Shape) : Multiset MX.Shape) =
        R.kidsS n0 (MX.Shape.cls n h μ))
    (hlC : ∃ C, ∀ n h μ o BS J sup, E.Valid kmin (MDesc.cls n h μ o BS J sup) →
      E.clsLoc n h μ + 1 ≤ C * (R.locS n0 (MX.Shape.cls n h μ) + 1))
    (hbC : ∀ n h μ o BS J sup, E.Valid kmin (MDesc.cls n h μ o BS J sup) →
      ∀ c ∈ E.kidsC (MDesc.cls n h μ o BS J sup), bndD c ≤ bndD (MDesc.cls n h μ o BS J sup)) :
    MCost.PortTop.{U} E m cl (fun n N => (N + 2) * 2 ^ n) (fun n N => R.topCost n0 (R.allotM n0) n N) := by
  intro ι n N u
  have hRn0 : R.m ≤ n0 := by rw [H.hm]; exact hn0
  -- the class and top halves
  have hloc : Dom (fun d : E.VD kmin => R.locS n0 (shapeD d.1)) (fun d => E.locD kmin n0 d.1) := by
    obtain ⟨C1, h1⟩ := H.locTop_dom hk.two n0
    obtain ⟨C2, h2⟩ := hlC
    refine ⟨C1 + C2, fun d => ?_⟩
    obtain ⟨d, hd⟩ := d
    cases d with
    | top n' B v =>
      have := h1 n' B
      simp only [locD, shapeD] at this ⊢
      nlinarith
    | cls n' h μ o BS J sup =>
      have := h2 n' h μ o BS J sup hd
      simp only [locD, shapeD] at this ⊢
      nlinarith
  have hkids : ∀ d : E.VD kmin, R.InvS (shapeD d.1) →
      ((↑(E.kidsV hk n0 hn0 d) : Multiset (E.VD kmin)).map (fun c => shapeD c.1)) = R.kidsS n0 (shapeD d.1) := by
    intro d hinv
    rw [E.kidsV_shape_eq hk n0 hn0 d]
    obtain ⟨d, hd⟩ := d
    cases d with
    | top n' B v => exact H.kidsTop_shape shapeD (fun _ _ _ => rfl) (fun _ _ _ _ _ _ _ => rfl) n0 n' B v
    | cls n' h μ o BS J sup => exact hkC n' h μ o BS J sup hd hinv
  have hbd : ∀ d c : E.VD kmin, R.InvS (shapeD d.1) →
      c ∈ (↑(E.kidsV hk n0 hn0 d) : Multiset (E.VD kmin)) → bndD c.1 ≤ bndD d.1 := by
    intro d c _ hc
    have hm := E.mem_kidsV hk n0 hn0 d c hc
    obtain ⟨d, hd⟩ := d
    cases d with
    | top n' B v => exact E.bnd_kidsTop kmin n0 n' B v c.1 hm
    | cls n' h μ o BS J sup => exact hbC n' h μ o BS J sup hd c.1 hm
  have H0 := MCost.mixed_close R hRn0 (R.allotM_jobRec hRn0) m (E.encV kmin cl) (E.outV kmin cl)
    (fun d => shapeD d.1) (fun d => ↑(E.kidsV hk n0 hn0 d)) (fun d => bndD d.1) (fun d => E.locD kmin n0 d.1)
    (fun d => fuelD d.1) (E.hbody hk n0 hn0 m cl) hloc hkids hbd
    ((E.can_fuel cl m (P := fun d => R.InvS (shapeD d.1))).mono (fun _ => Nat.zero_le _))
    (fun d hd => rank_lt_fuel R d.1 hd) E.small_fuel
    (fun i => (⟨MDesc.top (n i) (N i) (u i), trivial⟩ : E.VD kmin)) (fun i => trivial)
  exact H0

/-- **The engine at the seam**: the kernel on one vector of `k` bits in work `O(2^k * envelope z k)`. -/
theorem engine_seam {kmin : ℕ} (hk : E.KMin kmin) (n0 : ℕ) (hn0 : E.mx ≤ n0)
    {R : MX.Rule} {typ : ℕ → Fin R.K} (H : E.BridgeHyp R typ kmin) {z1 z : ℝ} (hrate : R.RateQ z1 1)
    (hz1 : 0 < z1) (h12 : z1 < z) (hz : z ≤ 1) (m : Bool) (cl : Paint)
    (hkC : ∀ n h μ o BS J sup, E.Valid kmin (MDesc.cls n h μ o BS J sup) → R.InvS (MX.Shape.cls n h μ) →
      (((E.kidsC (MDesc.cls n h μ o BS J sup)).map shapeD : List MX.Shape) : Multiset MX.Shape) =
        R.kidsS n0 (MX.Shape.cls n h μ))
    (hlC : ∃ C, ∀ n h μ o BS J sup, E.Valid kmin (MDesc.cls n h μ o BS J sup) →
      E.clsLoc n h μ + 1 ≤ C * (R.locS n0 (MX.Shape.cls n h μ) + 1))
    (hbC : ∀ n h μ o BS J sup, E.Valid kmin (MDesc.cls n h μ o BS J sup) →
      ∀ c ∈ E.kidsC (MDesc.cls n h μ o BS J sup), bndD c ≤ bndD (MDesc.cls n h μ o BS J sup))
    {ι : Type U} (k : ι → ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2 ^ k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2 ^ k i * envelope z (k i)) := by
  have hRn0 : R.m ≤ n0 := by rw [H.hm]; exact hn0
  refine MCost.seam_of_port E R hrate hz1 h12 hz hRn0 (Bd := fun n N => (N + 2) * 2 ^ n)
    (E.engine_portTop hk n0 hn0 H m cl hkC hlC hbC)
    ⟨2, fun n N => ?_⟩ k v
  have hX : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  generalize 2 ^ n = X at *
  have h1 : (N + 2) * X ≤ 2 * ((N + 1) * X + 2) := by nlinarith
  have hY : 2 ≤ (N + 1) * X + 2 := by omega
  generalize (N + 1) * X + 2 = Y at *
  have h2 : 2 * Y ≤ Y ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right _ hY
  omega

end Eng

end
end PowerSaving.RAM
end OAI

#print axioms OAI.PowerSaving.RAM.Eng.engine_portTop
#print axioms OAI.PowerSaving.RAM.Eng.engine_seam
