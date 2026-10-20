import Submission.Work.MixedCost.Jobs
import Submission.Work.MixedCost.TopDom

/-!
# Mixed engine, the last link: the closed port engine gives the seam

(agent e-r3cost, round wht45/lever, 19 Oct 2026.)  `mixed_close` (Wire.lean) applied to e-r3prog's ONE open
body (`Eng.hbody`, Glue.lean) gives a closed program on the port for every family of top descriptors, with
cost `costS (top n N) = topCost n0 allotM n N`.  From it:

* `jobs_of_port`  the jobs-form top engine `(n, I, jobs) ↦ jobs answered` that `seam_of_jobs` takes;
* `seam_of_port`  **the kernel on one vector of `k` bits in work `O(2^k * envelope z k)`**, every
                  `z ∈ (z1, 1]`: `hillsZ_program`'s statement at exponent `z`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.MCost
open PowerSaving.RAM PowerSaving.Binary PowerSaving.MX Ty

noncomputable section

universe U

variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ] (E : Eng α ρ σ)

/-- The closed port engine on top descriptors, for every family (the shape `mixed_close` gives). -/
def PortTop (m : Bool) (cl : Paint) (Bd : ℕ → ℕ → ℕ) (cost : ℕ → ℕ → ℕ) : Prop :=
  ∀ {ι : Type U} (n N : ι → ℕ) (u : ∀ i, ℕ → Bits (n i) → ℂ),
    Can m (fun i => Bd (n i) (N i)) (portIn cl) (portOut cl)
      (fun i => E.enc cl (MDesc.top (n i) (N i) (u i))) (fun i => E.out cl (MDesc.top (n i) (N i) (u i)))
      (fun i => cost (n i) (N i))

/-- **The jobs-form top engine from the closed port engine.** -/
theorem jobs_of_port {m : Bool} {cl : Paint} {Bd cost : ℕ → ℕ → ℕ} (hP : PortTop.{U} E m cl Bd cost)
    (hBd : ∃ d, ∀ n N, Bd n N ≤ ((N + 1) * 2 ^ n + 2) ^ d) {ι : Type U}
    (n N : ι → ℕ) (u : ∀ i, ℕ → Bits (n i) → ℂ) :
    Can m (fun i => (N i + 1) * 2 ^ n i) (jobIn cl) (a (a (c cl)))
      (fun i => (n i, Complex.I, jobsT' (n i) (N i) (u i)))
      (fun i => jobsT' (n i) (N i) (fun t => ripple (n i) (u i t)))
      (fun i => cost (n i) (N i)) := by
  let x (i : ι) : T (jobIn cl) := (n i, Complex.I, jobsT' (n i) (N i) (u i))
  -- the empty supply
  have hemp : Has m (fun i => (N i + 1) * 2 ^ n i) (jobIn cl) (a (a (c cl))) x
      (fun i => jobsTape (n i) 0 (fun _ _ => 0)) := by
    have H := Can.tab (m := m) (B := fun i => (N i + 1) * 2 ^ n i) (s := jobIn cl) (x := x)
      (t := a (c cl)) (n := fun _ => 0) (uB := fun _ _ => 0) (v := fun _ _ => Tape.empty ℂ) (W := fun _ => 0)
      (Can.wc (W := fun _ => 0) 0) (Can.tab (t := c cl) (n := fun _ => 0) (uB := fun _ _ => 0)
        (v := fun _ _ => 0) (Can.wc 0) Can.zero (Small.const _ 0) |>.cong (fun _ => rfl) (fun d => by
          refine Tape.ext_look rfl 0 (fun j hj => absurd hj (Nat.not_lt_zero _)))) (Small.const _ 0)
    refine (H.cong (fun _ => rfl) (fun i => ?_)).mono (fun i => by simp)
    exact Tape.ext_look rfl (Tape.empty ℂ) (fun j hj => absurd hj (Nat.not_lt_zero _))
  have hin : Can m (fun i => (N i + 1) * 2 ^ n i) (jobIn cl) (portIn cl) x
      (fun i => E.enc cl (MDesc.top (n i) (N i) (u i))) (fun i => cost (n i) (N i)) := by
    refine ((Can.first.mono (fun _ => Nat.zero_le _)).pair ((Can.second.fst.mono (fun _ => Nat.zero_le _)).pair
      ((Can.wc 0).pair ((Can.wc 0).pair ((Can.wc 0).pair ((Can.second.snd.mono (fun _ => Nat.zero_le _)).pair
        (hemp.mono (fun _ => Nat.zero_le _)))))))).cong (fun _ => rfl) (fun i => rfl)
  obtain ⟨d, hd⟩ := hBd
  have hcl := (hP n N u).ambient (B' := fun i => (N i + 1) * 2 ^ n i) ⟨d, fun i => hd (n i) (N i)⟩
  exact Can.fst (hin.then_do hcl)

/-- **The seam from the closed port engine.** -/
theorem seam_of_port (R : Rule) {z1 z : ℝ} (hrate : R.RateQ z1 1) (hz1 : 0 < z1) (h12 : z1 < z)
    (hz : z ≤ 1) {n0 : ℕ} (hn0 : R.m ≤ n0) {m : Bool} {cl : Paint} {Bd : ℕ → ℕ → ℕ}
    (hP : PortTop.{U} E m cl Bd (fun n N => R.topCost n0 (R.allotM n0) n N))
    (hBd : ∃ d, ∀ n N, Bd n N ≤ ((N + 1) * 2 ^ n + 2) ^ d)
    {ι : Type U} (k : ι → ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2 ^ k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2 ^ k i * envelope z (k i)) :=
  seam_of_jobs R hrate hz1 h12 hz hn0 (fun n N u => jobs_of_port E hP hBd n N u) k v

end
end PowerSaving.MCost
end OAI

#print axioms OAI.PowerSaving.MCost.seam_of_port
