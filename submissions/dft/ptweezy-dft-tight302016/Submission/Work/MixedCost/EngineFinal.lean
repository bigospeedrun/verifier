import Submission.Work.MixedCost.EngineClose
import Submission.Work.Mixed.Prog.ClassSide

/-!
# The mixed engine at the seam, with no open hypothesis (agents e-r3cost + e-r3prog)

`engine_seam_final`: for any engine `E` (a word with mixed targets and its separation, e-r3prog's `Eng`) and any
rule `R` with `BridgeHyp` (its numbers are `E`'s), the rate fact at `z1 > 0` gives, for every `z ∈ (z1, 1]`, ONE
program computing the kernel on one vector of `k` bits in work `O(2^k * envelope z k)` — `hillsZ_program`'s
statement at exponent `z`.  Class side: e-r3prog's `kidsC_shape`, `clsLoc_dom`, `bnd_kidsC`, `kminE`
(ClassSide.lean); top side, closer and seam: e-r3cost.
-/

set_option linter.unusedSectionVars false

namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset GF MXR
noncomputable section

universe U

namespace Eng
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]

/-- **The mixed engine at the seam.** -/
theorem engine_seam_final (E : Eng α ρ σ) {R : MX.Rule} {typ : ℕ → Fin R.K} {kmin : ℕ}
    (H : E.BridgeHyp R typ kmin) (n0 : ℕ) (hn0 : E.mx ≤ n0) {z1 z : ℝ} (hrate : R.RateQ z1 1)
    (hz1 : 0 < z1) (h12 : z1 < z) (hz : z ≤ 1) (m : Bool) (cl : Paint)
    {ι : Type U} (k : ι → ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2 ^ k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2 ^ k i * envelope z (k i)) :=
  E.engine_seam H.kminE n0 hn0 H hrate hz1 h12 hz m cl
    (fun n h μ o BS J sup hd _ => H.kidsC_shape shapeD (fun _ _ _ => rfl) (fun _ _ _ _ _ _ _ => rfl) n0
      n h μ o BS J sup hd)
    (H.clsLoc_dom n0)
    (fun n h μ o BS J sup hd => bnd_kidsC H.kminE n h μ o BS J sup hd) k v

end Eng

end
end PowerSaving.RAM
end OAI

#print axioms OAI.PowerSaving.RAM.Eng.engine_seam_final
