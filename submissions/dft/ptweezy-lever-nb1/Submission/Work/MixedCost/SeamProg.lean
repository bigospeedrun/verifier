import Submission.Work.MixedCost.Adapter
import Submission.Work.MixedCost.Final

/-!
# Mixed engine, cost part 9: the seam statement from the closed top jobs

(agent e-r3cost, round wht45/lever, 19 Oct 2026.)

* `top_bits_of_std` : a closed top-job engine stated on `Fin B` slices (`loaded cl (Layout.std B) n`,
                      the natural form of `mixed_close`'s top shapes) also serves slices coded by
                      `Bits b` (the form the adapter uses);
* `seam_program`    : **the seam**: from the closed top jobs with the least per-vector cost
                      `allotM` and the rate fact at `z1`, the kernel on one vector of `k` bits in
                      work `O(2^k * envelope z k)`, for every `z ∈ (z1, 1]` — the exact statement of
                      `hillsZ_program` / `envelope_program_ge` (Work/Fourier/Seam.lean) at exponent `z`.
-/

set_option linter.unusedSectionVars false

namespace OAI
namespace PowerSaving.MCost
open PowerSaving.RAM PowerSaving.Binary PowerSaving.MX Ty

noncomputable section

universe U

/-- Relabelling the slices of a top job by their positions. -/
lemma tape_relabel {ρ : Type*} (R : Layout ρ) (n : ℕ) (u : Sim ρ n → ℂ) :
    (sim R n).tape u = (sim (Layout.std R.n) n).tape (fun z => u (R.atFin z.1, z.2)) := by
  refine Layout.verify _ _ 0 _ rfl ?_
  intro z
  have hl : (sim (Layout.std R.n) n).loc z = (sim R n).loc (R.atFin z.1, z.2) := by
    unfold sim
    rw [Layout.pair_loc, Layout.pair_loc, Layout.loc_atFin]
    rfl
  rw [hl, Layout.read]

lemma whole_relabel {ρ : Type*} (R : Layout ρ) (n : ℕ) (u : Sim ρ n → ℂ) :
    (fun z : Fin R.n × Bits n => whole n u (R.atFin z.1, z.2)) =
      whole n (fun z : Fin R.n × Bits n => u (R.atFin z.1, z.2)) := by
  funext z; rfl

/-- **Top jobs on `Fin B` slices serve `Bits b` slices.** -/
theorem top_bits_of_std (R : Rule) (n0 : ℕ) (J : ℕ → ℕ) (cl : Paint) (m : Bool) {ι : Type U}
    (hTop : ∀ (n B : ι → ℕ) (u : ∀ i, Sim (Fin (B i)) (n i) → ℂ),
      Can m (fun i => (B i + 1) * 2 ^ n i) (simIn cl) (bundle cl)
        (fun i => loaded cl (Layout.std (B i)) (n i) (u i))
        (fun i => (sim (Layout.std (B i)) (n i)).tape (whole (n i) (u i)))
        (fun i => R.topCost n0 J (n i) (B i)))
    (n b : ι → ℕ) (u : ∀ i, Sim (Bits (b i)) (n i) → ℂ) :
    Can m (fun i => (2 ^ b i + 1) * 2 ^ n i) (simIn cl) (bundle cl)
      (fun i => loaded cl (bits (b i)) (n i) (u i))
      (fun i => (sim (bits (b i)) (n i)).tape (whole (n i) (u i)))
      (fun i => R.topCost n0 J (n i) (2 ^ b i)) := by
  have H := hTop n (fun i => 2 ^ b i) (fun i z => u i ((bits (b i)).atFin z.1, z.2))
  refine H.cong (fun i => ?_) (fun i => ?_)
  · unfold loaded
    rw [tape_relabel (bits (b i)) (n i) (u i)]
    rfl
  · rw [tape_relabel (bits (b i)) (n i) (whole (n i) (u i))]
    rfl

/-- **The seam from the closed top jobs.** -/
theorem seam_program (R : Rule) {z1 z : ℝ} (hrate : R.RateQ z1 1) (hz1 : 0 < z1) (h12 : z1 < z)
    (hz : z ≤ 1) {n0 : ℕ} (hn0 : R.m ≤ n0) (cl : Paint) (m : Bool) {ι : Type U}
    (hTop : ∀ (n B : ι → ℕ) (u : ∀ i, Sim (Fin (B i)) (n i) → ℂ),
      Can m (fun i => (B i + 1) * 2 ^ n i) (simIn cl) (bundle cl)
        (fun i => loaded cl (Layout.std (B i)) (n i) (u i))
        (fun i => (sim (Layout.std (B i)) (n i)).tape (whole (n i) (u i)))
        (fun i => R.topCost n0 (R.allotM n0) (n i) (B i)))
    (k : ι → ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2 ^ k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2 ^ k i * envelope z (k i)) :=
  R.seam_weaken hrate hz1 h12 hz hn0 k
    (adapter_program R n0 (R.allotM n0) cl m (top_bits_of_std R n0 (R.allotM n0) cl m hTop) k v)

end
end PowerSaving.MCost
end OAI

#print axioms OAI.PowerSaving.MCost.top_bits_of_std
#print axioms OAI.PowerSaving.MCost.seam_program
