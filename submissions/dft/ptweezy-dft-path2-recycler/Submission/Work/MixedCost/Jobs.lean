import Submission.Work.MixedCost.SeamProg

/-!
# Mixed engine, cost part 11: flat tapes and tapes of jobs

(agent e-r3cost, round wht45/lever, 19 Oct 2026.)  e-r3prog's port carries jobs as a tape of tapes
(`jobsTape n N J = (Layout.std N).tape (fun t => (bits n).tape (J t))`); the seam side carries `N`
vectors of `2^n` entries as ONE flat tape (`loaded cl (Layout.std N) n u`).  One relabel pass each way:

* `jobs_of_flat`  flat → jobs, work `N * 2^n`;
* `flat_of_jobs`  jobs → flat, work `N * 2^n`;
* `top_std_of_jobs` a closed top engine on jobs `(n, I, jobs) ↦ jobs answered` with cost `topCost`
                  gives `seam_program`'s hypothesis (flat form), at the same cost up to a constant.
-/

set_option linter.unusedSectionVars false

namespace OAI
namespace PowerSaving.MCost
open PowerSaving.RAM PowerSaving.Binary PowerSaving.MX Ty

noncomputable section

universe U

/-- A tape of jobs (e-r3prog's `jobsTape`, restated so this file needs only the port's shape). -/
def jobsT' (n N : ℕ) (J : ℕ → Bits n → ℂ) : Tape (Tape ℂ) :=
  (Layout.std N).tape (fun t => (bits n).tape (J t))

/-- The input of a top job on a tape of jobs: `(n, I, jobs)`. -/
abbrev jobIn (cl : Paint) : Ty := p w (p sc (a (a (c cl))))

section
variable {m : Bool} {ι : Type U} {cl : Paint} {s : Ty} {x : ι → T s} {Bd : ι → ℕ}

/-- **flat → jobs**: from the flat tape of `N` vectors of `2^n` entries, the tape of jobs. -/
theorem jobs_of_flat (n N : ι → ℕ) (u : ∀ i, Sim (Fin (N i)) (n i) → ℂ)
    (ht : Has m Bd s (bundle cl) x (fun i => (sim (Layout.std (N i)) (n i)).tape (u i)))
    (hN : Knows m Bd s x N) (h2 : Knows m Bd s x (fun i => 2 ^ n i))
    (hNs : Small Bd N) (h2s : Small Bd (fun i => 2 ^ n i)) :
    Can m Bd s (a (a (c cl))) x
      (fun i => jobsT' (n i) (N i) (fun t z => if h : t < N i then u i (⟨t, h⟩, z) else 0))
      (fun i => N i + N i * (2 ^ n i + 2 ^ n i)) := by
  -- outer layout over the jobs, inner layout over the entries of one job
  let Q := Σ i, Fin (N i)
  let σ : Q → ι := Sigma.fst
  let E (d : Q) : T (p s w) := (x d.1, (Layout.std (N d.1)).loc d.2)
  have h2Q : Knows m (fun d : Q => Bd d.1) (p s w) E (fun d => (bits (n d.1)).n) :=
    Can.first.then_do (h2.reindex σ)
  let Q2 := Σ d : Q, Bits (n d.1)
  let σ2 : Q2 → Q := Sigma.fst
  let E2 (e : Q2) : T (p (p s w) w) := (E e.1, (bits (n e.1.1)).loc e.2)
  have hval : Has m (fun e : Q2 => Bd e.1.1) (p (p s w) w) (c cl) E2
      (fun e => u e.1.1 (e.1.2, e.2)) := by
    have hadr : Knows m (fun e : Q2 => Bd e.1.1) (p (p s w) w) E2
        (fun e => (sim (Layout.std (N e.1.1)) (n e.1.1)).loc (e.1.2, e.2)) := by
      have ht1 : Knows m (fun e : Q2 => Bd e.1.1) (p (p s w) w) E2 (fun e => (Layout.std (N e.1.1)).loc e.1.2) :=
        Can.first.then_do Can.second
      have ht2 : Knows m (fun e : Q2 => Bd e.1.1) (p (p s w) w) E2 (fun e => (bits (n e.1.1)).loc e.2) :=
        Can.second
      have hd : Knows m (fun e : Q2 => Bd e.1.1) (p (p s w) w) E2 (fun e => (bits (n e.1.1)).n) :=
        Can.first.then_do (h2Q.reindex σ2)
      exact Can.addr_join (L := fun e : Q2 => Layout.std (N e.1.1)) (R := fun e : Q2 => bits (n e.1.1))
        (u := fun e : Q2 => (e.1.2, e.2)) ht1 ht2 hd ((hNs.reindex σ).reindex σ2) ((h2s.reindex σ).reindex σ2)
    exact Can.fetch (t := c cl) (L := fun e : Q2 => sim (Layout.std (N e.1.1)) (n e.1.1))
      (v := fun e : Q2 => u e.1.1) (i := fun e : Q2 => (e.1.2, e.2))
      (Can.first.then_do (Can.first.then_do ((ht.reindex σ).reindex σ2))) hadr
  have hjob : Can m (fun d : Q => Bd d.1) (p s w) (a (c cl)) E
      (fun d => (bits (n d.1)).tape (fun z => u d.1 (d.2, z))) (fun d => 2 ^ n d.1) := by
    refine (Can.layout (L := fun d : Q => bits (n d.1)) (t := c cl) (P := fun _ => 0)
      (v := fun d z => u d.1 (d.2, z)) h2Q hval (h2s.reindex σ)).mono (fun d => ?_)
    show 0 + 2 ^ n d.1 + 2 ^ n d.1 * 0 ≤ 2 ^ n d.1
    simp
  have H := Can.layout (L := fun i => Layout.std (N i)) (t := a (c cl))
    (P := fun i => 2 ^ n i) (v := fun i t => (bits (n i)).tape (fun z => u i (t, z)))
    hN hjob hNs
  refine (H.cong (fun _ => rfl) (fun i => ?_)).mono (fun i => ?_)
  rotate_left
  · show 0 + N i + N i * 2 ^ n i ≤ N i + N i * (2 ^ n i + 2 ^ n i)
    rw [Nat.zero_add]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)) _
  unfold jobsT'
  congr 1
  funext t
  simp [t.isLt]

/-- **jobs → flat**: from the tape of `N` jobs of `2^n` entries, the flat tape. -/
theorem flat_of_jobs (n N : ι → ℕ) (J : ∀ i, ℕ → Bits (n i) → ℂ)
    (ht : Has m Bd s (a (a (c cl))) x (fun i => jobsT' (n i) (N i) (J i)))
    (hN : Knows m Bd s x N) (h2 : Knows m Bd s x (fun i => 2 ^ n i))
    (hNs : Small Bd N) (h2s : Small Bd (fun i => 2 ^ n i)) :
    Can m Bd s (bundle cl) x
      (fun i => (sim (Layout.std (N i)) (n i)).tape (fun z => J i z.1 z.2))
      (fun i => N i * 2 ^ n i) := by
  let Q := Σ i, Fin (N i) × Bits (n i)
  let σ : Q → ι := Sigma.fst
  let E (d : Q) : T (p s w) := (x d.1, (sim (Layout.std (N d.1)) (n d.1)).loc d.2)
  have hsQ : Small (fun d : Q => Bd d.1) (fun d => (Layout.std (N d.1)).n * (bits (n d.1)).n) :=
    (hNs.mul h2s).reindex σ
  have h2Q : Knows m (fun d : Q => Bd d.1) (p s w) E (fun d => (bits (n d.1)).n) :=
    Can.first.then_do (h2.reindex σ)
  have hpos : Knows m (fun d : Q => Bd d.1) (p s w) E
      (fun d => ((Layout.std (N d.1)).pair (bits (n d.1))).loc d.2) := Can.second
  have ht1 : Knows m (fun d : Q => Bd d.1) (p s w) E (fun d => (Layout.std (N d.1)).loc d.2.1) :=
    Can.addr_high (L := fun d : Q => Layout.std (N d.1)) (R := fun d : Q => bits (n d.1))
      (u := fun d : Q => d.2) hpos h2Q hsQ
  have hz : Knows m (fun d : Q => Bd d.1) (p s w) E (fun d => (bits (n d.1)).loc d.2.2) :=
    Can.addr_low (L := fun d : Q => Layout.std (N d.1)) (R := fun d : Q => bits (n d.1))
      (u := fun d : Q => d.2) hpos h2Q hsQ
  have hjob : Has m (fun d : Q => Bd d.1) (p s w) (a (c cl)) E
      (fun d => (bits (n d.1)).tape (J d.1 d.2.1)) :=
    Can.fetch (t := a (c cl)) (L := fun d : Q => Layout.std (N d.1))
      (v := fun d : Q => fun t : Fin (N d.1) => (bits (n d.1)).tape (J d.1 t)) (i := fun d : Q => d.2.1)
      (Can.first.then_do (ht.reindex σ)) ht1
  have hval : Has m (fun d : Q => Bd d.1) (p s w) (c cl) E (fun d => J d.1 d.2.1 d.2.2) :=
    Can.fetch (t := c cl) (L := fun d : Q => bits (n d.1)) (v := fun d : Q => J d.1 d.2.1)
      (i := fun d : Q => d.2.2) hjob hz
  have hn : Knows m Bd s x (fun i => (sim (Layout.std (N i)) (n i)).n) := hN.times h2 hNs h2s
  have H := Can.layout (L := fun i => sim (Layout.std (N i)) (n i)) (t := c cl) (P := fun _ => 0)
    (v := fun i z => J i z.1 z.2) hn hval (hNs.mul h2s)
  refine H.mono (fun i => ?_)
  show 0 + N i * 2 ^ n i + N i * 2 ^ n i * 0 ≤ N i * 2 ^ n i
  simp

/-- **A closed top engine on jobs serves the flat form** that `seam_program` takes. -/
theorem top_std_of_jobs (R : Rule) (n0 : ℕ) (J : ℕ → ℕ) (hJge : ∀ n, 2 ^ n ≤ J n)
    (hJ : ∀ (n N : ι → ℕ) (u : ∀ i, ℕ → Bits (n i) → ℂ),
      Can m (fun i => (N i + 1) * 2 ^ n i) (jobIn cl) (a (a (c cl)))
        (fun i => (n i, Complex.I, jobsT' (n i) (N i) (u i)))
        (fun i => jobsT' (n i) (N i) (fun t => ripple (n i) (u i t)))
        (fun i => R.topCost n0 J (n i) (N i)))
    (n N : ι → ℕ) (u : ∀ i, Sim (Fin (N i)) (n i) → ℂ) :
    Can m (fun i => (N i + 1) * 2 ^ n i) (simIn cl) (bundle cl)
      (fun i => loaded cl (Layout.std (N i)) (n i) (u i))
      (fun i => (sim (Layout.std (N i)) (n i)).tape (whole (n i) (u i)))
      (fun i => R.topCost n0 J (n i) (N i)) := by
  let Bd : ι → ℕ := fun i => (N i + 1) * 2 ^ n i
  let Wt : ι → ℕ := fun i => R.topCost n0 J (n i) (N i)
  let x0 : ι → T (simIn cl) := fun i => loaded cl (Layout.std (N i)) (n i) (u i)
  have h2le : ∀ i, 2 ^ n i ≤ Bd i := fun i => Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  have hNle : ∀ i, N i ≤ Bd i := fun i => by
    have : 1 ≤ 2 ^ n i := Nat.one_le_two_pow
    calc N i ≤ (N i + 1) * 1 := by omega
      _ ≤ Bd i := Nat.mul_le_mul_left _ this
  have hnle : ∀ i, n i ≤ Bd i := fun i => le_trans (Nat.lt_two_pow_self).le (h2le i)
  have sN : Small Bd N := ⟨1, fun i => by have := hNle i; simp only [pow_one]; omega⟩
  have s2 : Small Bd (fun i => 2 ^ n i) := ⟨1, fun i => by have := h2le i; simp only [pow_one]; omega⟩
  have sn : Small Bd n := ⟨1, fun i => by have := hnle i; simp only [pow_one]; omega⟩
  have hWt : ∀ i, N i * 2 ^ n i + (n i + 1) * 2 ^ n i ≤ Wt i := fun i => by
    have := Nat.mul_le_mul_left (N i) (hJge (n i))
    simp only [Wt, Rule.topCost]; omega
  have hWt2 : ∀ i, n i ≤ Wt i := fun i => by
    have := hWt i
    have : n i ≤ (n i + 1) * 2 ^ n i :=
      le_trans (Nat.le_succ _) (Nat.le_mul_of_pos_right _ Nat.one_le_two_pow)
    omega
  -- the environment: the input and `2^n`
  have hn0 : Knows m Bd (simIn cl) x0 n := Can.first
  have h20 : Can m Bd (simIn cl) w x0 (fun i => 2 ^ n i) Wt :=
    Can.wTwo (hn0.mono (fun _ => Nat.zero_le _)) sn s2 (Dom.of_le hWt2)
  let sE : Ty := p (simIn cl) w
  let E0 : ι → T sE := fun i => (x0 i, 2 ^ n i)
  have hE0 : Can m Bd (simIn cl) sE x0 E0 Wt := Can.pair Can.id h20
  have hN : Knows m Bd sE E0 N := by
    -- the number of jobs: the flat length divided by `2^n`
    have hl : Knows m Bd sE E0 (fun i => (sim (Layout.std (N i)) (n i)).n) :=
      (Can.first.then_do (Can.second.snd)).len ((sN.mul s2))
    refine (hl.dvdW (Can.second) (sN.mul s2)).cong (fun _ => rfl) (fun i => ?_)
    show N i * 2 ^ n i / 2 ^ n i = N i
    exact Nat.mul_div_cancel _ (Nat.two_pow_pos _)
  have h2E : Knows m Bd sE E0 (fun i => 2 ^ n i) := Can.second
  -- flat → jobs
  let u' (i : ι) : ℕ → Bits (n i) → ℂ := fun t z => if h : t < N i then u i (⟨t, h⟩, z) else 0
  have hj : Can m Bd sE (a (a (c cl))) E0 (fun i => jobsT' (n i) (N i) (u' i)) Wt :=
    (jobs_of_flat (cl := cl) n N u (Can.first.then_do Can.second.snd) hN h2E sN s2).weaken
      ⟨3, fun i => by
        have h1 := hWt i
        have h2 : N i ≤ N i * 2 ^ n i := Nat.le_mul_of_pos_right _ Nat.one_le_two_pow
        nlinarith⟩
  -- the call
  have hin : Can m Bd sE (jobIn cl) E0 (fun i => (n i, Complex.I, jobsT' (n i) (N i) (u' i))) Wt :=
    Can.pair ((Can.first.then_do hn0).mono (fun _ => Nat.zero_le _))
      (Can.pair ((Can.first.then_do Can.second.fst).mono (fun _ => Nat.zero_le _)) hj)
  have hcall : Can m Bd sE (a (a (c cl))) E0
      (fun i => jobsT' (n i) (N i) (fun t => ripple (n i) (u' i t))) Wt :=
    hin.then_do (hJ n N u')
  -- jobs → flat, keeping the environment
  have hback : Can m Bd (p sE (a (a (c cl)))) (bundle cl)
      (fun i => (E0 i, jobsT' (n i) (N i) (fun t => ripple (n i) (u' i t))))
      (fun i => (sim (Layout.std (N i)) (n i)).tape (fun z => ripple (n i) (u' i z.1) z.2)) Wt :=
    (flat_of_jobs (cl := cl) n N (fun i t => ripple (n i) (u' i t)) Can.second
      (Can.first.then_do hN) (Can.first.then_do h2E) sN s2).mono (fun i => by have := hWt i; omega)
  refine (hE0.then_do (Can.bind hcall hback)).cong (fun _ => rfl) (fun i => ?_)
  congr 1
  funext z
  simp only [u', z.1.isLt, dite_true]
  rfl

/-- **The seam from a closed top engine on jobs** (the form closest to e-r3prog's port): the kernel
on one vector of `k` bits in work `O(2^k * envelope z k)`, every `z ∈ (z1, 1]`. -/
theorem seam_of_jobs (R : Rule) {z1 z : ℝ} (hrate : R.RateQ z1 1) (hz1 : 0 < z1) (h12 : z1 < z)
    (hz : z ≤ 1) {n0 : ℕ} (hn0 : R.m ≤ n0)
    (hJ : ∀ (n N : ι → ℕ) (u : ∀ i, ℕ → Bits (n i) → ℂ),
      Can m (fun i => (N i + 1) * 2 ^ n i) (jobIn cl) (a (a (c cl)))
        (fun i => (n i, Complex.I, jobsT' (n i) (N i) (u i)))
        (fun i => jobsT' (n i) (N i) (fun t => ripple (n i) (u i t)))
        (fun i => R.topCost n0 (R.allotM n0) (n i) (N i)))
    (k : ι → ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2 ^ k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2 ^ k i * envelope z (k i)) :=
  seam_program R hrate hz1 h12 hz hn0 cl m
    (top_std_of_jobs R n0 (R.allotM n0) (R.J_ge hn0 (R.allotM_jobRec hn0)) hJ) k v

end

end
end PowerSaving.MCost
end OAI

#print axioms OAI.PowerSaving.MCost.jobs_of_flat
#print axioms OAI.PowerSaving.MCost.flat_of_jobs
#print axioms OAI.PowerSaving.MCost.top_std_of_jobs
#print axioms OAI.PowerSaving.MCost.seam_of_jobs
