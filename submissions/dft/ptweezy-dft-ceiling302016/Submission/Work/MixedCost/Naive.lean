import Submission.OAI.Computability.FourierTransform.TensorProgram

/-!
# Mixed engine, cost part 10: the naive jobs (base case and leftovers of the top job)

(agent e-r3cost, round wht45/lever, 19 Oct 2026.)  `naive_jobs`: the kernel on every job of a tape of
`N` jobs of `2^n` entries (e-r3prog's `jobsTape n N u = (Layout.std N).tape (fun t => (bits n).tape (u t))`),
each by OpenAI's own `hills_program`, in work `N * ((n+1) * 2^n + 1)`.  This is the top job's base case
(`n < n0`, or fewer than `Nsrc n` jobs) and its `B % Nsrc n` leftover jobs (`locS`).
-/

namespace OAI
namespace PowerSaving.MCost
open PowerSaving.RAM PowerSaving.Binary Ty

noncomputable section

universe U

section
variable {m : Bool} {ι : Type U} {cl : Paint} {s : Ty} {x : ι → T s} {Bd : ι → ℕ}

theorem naive_jobs (n N : ι → ℕ) (u : ∀ i, ℕ → Bits (n i) → ℂ)
    (ht : Has m Bd s (a (a (c cl))) x (fun i => (Layout.std (N i)).tape (fun t => (bits (n i)).tape (u i t))))
    (hn : Knows m Bd s x n) (hN : Knows m Bd s x N) (hI : Has m Bd s sc x (fun _ => Complex.I))
    (hNs : Small Bd N) (h2s : Small Bd (fun i => 2 ^ n i)) :
    Can m Bd s (a (a (c cl))) x
      (fun i => (Layout.std (N i)).tape (fun t => (bits (n i)).tape (ripple (n i) (u i t))))
      (fun i => N i * ((n i + 1) * 2 ^ n i + 1)) := by
  let Q := Σ i, Fin (N i)
  let σ : Q → ι := Sigma.fst
  let E (d : Q) : T (p s w) := (x d.1, (Layout.std (N d.1)).loc d.2)
  -- the input of `hills_program` for job `d`
  have hin : Can m (fun d : Q => Bd d.1) (p s w) (simIn cl) E
      (fun d => givenBits cl (n d.1) (u d.1 d.2)) (fun d => (n d.1 + 1) * 2 ^ n d.1) := by
    have hn' : Knows m (fun d : Q => Bd d.1) (p s w) E (fun d => n d.1) := Can.first.then_do (hn.reindex σ)
    have hI' : Has m (fun d : Q => Bd d.1) (p s w) sc E (fun _ => Complex.I) := Can.first.then_do (hI.reindex σ)
    have hj : Has m (fun d : Q => Bd d.1) (p s w) (a (c cl)) E (fun d => (bits (n d.1)).tape (u d.1 d.2)) :=
      Can.fetch (t := a (c cl)) (L := fun d : Q => Layout.std (N d.1))
        (v := fun d : Q => fun t : Fin (N d.1) => (bits (n d.1)).tape (u d.1 t)) (i := fun d : Q => d.2)
        (Can.first.then_do (ht.reindex σ)) Can.second
    exact ((Can.pair hn' (Can.pair hI' hj)).mono (fun _ => Nat.zero_le _))
  have hh := (hills_program cl m (fun d : Q => n d.1) (fun d => u d.1 d.2)).ambient
    (B' := fun d : Q => Bd d.1) (h2s.reindex σ)
  have hval : Can m (fun d : Q => Bd d.1) (p s w) (a (c cl)) E
      (fun d => (bits (n d.1)).tape (ripple (n d.1) (u d.1 d.2))) (fun d => (n d.1 + 1) * 2 ^ n d.1) := by
    refine hin.then_do (hh.mono (fun d => ?_))
    rw [mul_comm]
    exact Nat.mul_le_mul_right _ (hills_le _)
  have H := Can.layout (L := fun i => Layout.std (N i)) (t := a (c cl)) (P := fun i => (n i + 1) * 2 ^ n i)
    (v := fun i t => (bits (n i)).tape (ripple (n i) (u i t))) hN hval hNs
  refine H.mono (fun i => ?_)
  change 0 + N i + N i * ((n i + 1) * 2 ^ n i) ≤ N i * ((n i + 1) * 2 ^ n i + 1)
  rw [Nat.mul_add, mul_one]; omega

end

end
end PowerSaving.MCost
end OAI

#print axioms OAI.PowerSaving.MCost.naive_jobs
