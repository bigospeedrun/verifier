import Submission.Work.MixedCost.SeamCost
import Submission.Work.Mixed.Bound

/-!
# Mixed engine, cost part 6: the seam envelope from the rate fact

(agent e-r3cost, round wht45/lever, 19 Oct 2026.)  R2's bound on the least per-vector cost
(`Rule.allotM_bound`, e-r12's `Work.Mixed.Bound`) and the seam adapter's bill (`Rule.seam_dom`)
give the envelope the seam needs:

* `adapter_dom`  : `adapterCost (allotM) = O(2^k * envelope z k)` for every `z ∈ (z1, 1]`;
* `seam_weaken`  : any program family whose work is `O(adapterCost)` (the seam adapter: two
                   `Do` calls and the relabels) has work `O(2^k * envelope z k)` — the exact cost
                   shape of `hillsZ_program` / `envelope_program_ge` (Work/Fourier/Seam.lean).
-/

namespace OAI.PowerSaving.MX

open PowerSaving.RAM PowerSaving.RAM.Ty

namespace Rule

variable (R : Rule)

theorem adapter_dom {z1 z : ℝ} (hrate : R.RateQ z1 1) (hz1 : 0 < z1) (h12 : z1 < z) (hz : z ≤ 1)
    {n0 : ℕ} (hn0 : R.m ≤ n0) {ι : Type*} (k : ι → ℕ) :
    Dom (fun i => 2 ^ k i * envelope z (k i)) (fun i => R.adapterCost n0 (R.allotM n0) (k i)) := by
  obtain ⟨C, -, hC⟩ := R.allotM_bound hrate hz1 h12 hz hn0
  exact R.seam_dom hn0 (by linarith) hC k

/-- **The seam envelope**: a program whose work is `O(adapterCost)` has work `O(2^k envelope z k)`. -/
theorem seam_weaken {z1 z : ℝ} (hrate : R.RateQ z1 1) (hz1 : 0 < z1) (h12 : z1 < z) (hz : z ≤ 1)
    {n0 : ℕ} (hn0 : R.m ≤ n0) {m : Bool} {ι : Type*} {B : ι → ℕ} {s t : Ty} {x : ι → T s}
    {y : ι → T t} (k : ι → ℕ)
    (h : Can m B s t x y (fun i => R.adapterCost n0 (R.allotM n0) (k i))) :
    Can m B s t x y (fun i => 2 ^ k i * envelope z (k i)) :=
  Able.weaken h (R.adapter_dom hrate hz1 h12 hz hn0 k) (fun _ => le_rfl)

end Rule

end OAI.PowerSaving.MX

#print axioms OAI.PowerSaving.MX.Rule.adapter_dom
#print axioms OAI.PowerSaving.MX.Rule.seam_weaken
