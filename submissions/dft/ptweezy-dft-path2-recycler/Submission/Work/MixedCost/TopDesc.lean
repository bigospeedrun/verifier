import Submission.Work.Mixed.Prog.Merged1

/-!
# Mixed engine, top body part 1: the calls of a top job and the rest identity

(agent e-r3cost, round wht45/lever, 19 Oct 2026; against e-r3prog's `Work.Mixed.Prog.Desc`.)

A top job `Do(n, B)` with `n0 ≤ n` and at least `N = NU0 * W + cons n G 1` vectors (one tree copy) runs
`λ = B / N` tree copies.  Copy `t` owns the vectors `t*N, …, t*N + N - 1`: the first `NU0 * W` are the
root class's own jobs, the next `cons n G 1` its subtree's supply (consumed from offset `t*N + NU0*W`).
The root answers every vector `j` of its copy with the kernel on its low `topSz j` bits; ONE rest call
per vector does the high `n - topSz j` bits (`hiVec`: the low bits become the batch), and `fromHi` puts
the answers back: `fromHi_ripple` (commuting Hadamards on disjoint bits).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset GF MXR
noncomputable section

namespace Eng
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]
variable (E : Eng α ρ σ)

/-- The height of the root class of the tree for `n` (`= Flow's G n` when `kmin` is the smallest target). -/
def topG (kmin n : ℕ) : ℕ := Nat.findGreatest (fun g => E.mx * kmin ^ g ≤ n) n
/-- Units of the root class. -/
def topNU0 (kmin n : ℕ) : ℕ := E.NUc n (E.topG kmin n) 1
/-- Vectors per tree copy. -/
def topN (kmin n : ℕ) : ℕ := E.topNU0 kmin n * E.W + E.cons n (E.topG kmin n) 1
/-- Size (low bits done by the tree) of vector `j` of a copy. -/
def topSz (kmin n j : ℕ) : ℕ :=
  if j < E.topNU0 kmin n * E.W then E.slotSize n (E.topG kmin n) 1 j
  else E.csz n (E.topG kmin n) 1 (j - E.topNU0 kmin n * E.W)

/-- The root class call of copy `t`. -/
def topRoot (kmin n B : ℕ) (v : ℕ → Bits n → ℂ) (t : ℕ) : MDesc :=
  MDesc.cls n (E.topG kmin n) 1 (t * E.topN kmin n + E.topNU0 kmin n * E.W) B
    (fun j => v (t * E.topN kmin n + j)) v

/-- Vector `j` of copy `t` as the root answers it. -/
def topAns (kmin n : ℕ) (v : ℕ → Bits n → ℂ) (t j : ℕ) : Bits n → ℂ :=
  hlow n (E.topSz kmin n j) (v (t * E.topN kmin n + j))

end Eng

/-- A vector whose low `s` bits are done, as `2^s` vectors of its high `n - s` bits (batch = low bits). -/
def hiVec (n s : ℕ) (w : Bits n → ℂ) : ℕ → Bits (n - s) → ℂ :=
  if hs : s ≤ n then fun q y => w (castB (Nat.add_sub_cancel' hs) (catB s (n - s) (bitsOf s q, y)))
  else fun _ _ => 0

/-- The `2^s` answered vectors of the high bits, put back into one vector of `2^n` entries. -/
def fromHi (n s : ℕ) (Y : ℕ → Bits (n - s) → ℂ) : Bits n → ℂ :=
  fun e => Y ((bits n).loc e % 2^s) (bitsOf (n - s) ((bits n).loc e / 2^s))

/-- The kernel on the high `b` bits after the kernel on the low `a` bits, across a cast. -/
lemma ripple_hi_lo (k a b : ℕ) (h : a + b = k) (v : Bits k → ℂ) (x : Bits a) (y : Bits b) :
    ripple b (fun y' => hlow k a v (castB h (catB a b (x, y')))) y = ripple k v (castB h (catB a b (x, y))) := by
  subst h
  have e1 : ∀ y', hlow (a+b) a v (castB rfl (catB a b (x, y'))) = hlow (a+b) a v (catB a b (x, y')) :=
    fun y' => rfl
  simp only [e1]
  have e2 : ripple b (fun y' => hlow (a+b) a v (catB a b (x, y'))) y =
      hhigh (a+b) a (hlow (a+b) a v) (catB a b (x, y)) := by
    unfold hhigh ripple
    simp only [Matrix.mulVec, dotProduct]
    rw [← Equiv.sum_comp (catB a b), Fintype.sum_prod_type]
    simp only [maskHi_catB]
    rw [Finset.sum_eq_single x]
    · refine Finset.sum_congr rfl (fun y' _ => ?_)
      simp
    · intro x' _ hx'
      refine Finset.sum_eq_zero (fun y' _ => ?_)
      rw [if_neg (Ne.symm hx')]; ring
    · intro h; exact absurd (Finset.mem_univ x) h
  rw [e2, hhigh_hlow]
  rfl

/-- **The rest identity**: the root's answer (low `s` bits), its rest call (high `n - s` bits) and
`fromHi` give the whole kernel. -/
lemma fromHi_ripple (n s : ℕ) (hs : s ≤ n) (v : Bits n → ℂ) :
    fromHi n s (fun q => ripple (n - s) (hiVec n s (hlow n s v) q)) = ripple n v := by
  funext e
  obtain ⟨⟨x, y⟩, hxy⟩ : ∃ z : Bits s × Bits (n - s),
      castB (Nat.add_sub_cancel' hs) (catB s (n - s) z) = e :=
    ⟨(catB s (n - s)).symm ((castB (Nat.add_sub_cancel' hs)).symm e), by simp⟩
  subst hxy
  unfold fromHi
  have hx : (bits s).loc x < 2^s := by have := (bits s).bd x; rwa [bits_len] at this
  have h2 : 0 < 2^s := Nat.two_pow_pos s
  rw [loc_castB_catB n s hs]
  have e1 : ((bits s).loc x + 2^s * (bits (n - s)).loc y) % 2^s = (bits s).loc x := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
  have e2 : ((bits s).loc x + 2^s * (bits (n - s)).loc y) / 2^s = (bits (n - s)).loc y := by
    rw [Nat.add_mul_div_left _ _ h2, Nat.div_eq_of_lt hx, zero_add]
  rw [e1, e2, bitsOf_of_loc]
  have e3 : hiVec n s (hlow n s v) ((bits s).loc x) =
      fun y' => hlow n s v (castB (Nat.add_sub_cancel' hs) (catB s (n - s) (x, y'))) := by
    unfold hiVec
    rw [dif_pos hs, bitsOf_of_loc]
  show ripple (n - s) (hiVec n s (hlow n s v) ((bits s).loc x)) y = _
  rw [e3]
  exact ripple_hi_lo n s (n - s) _ v x y

namespace Eng
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]
variable (E : Eng α ρ σ)

/-- The rest call of vector `j` of copy `t`. -/
def topRest (kmin n : ℕ) (v : ℕ → Bits n → ℂ) (t j : ℕ) : MDesc :=
  MDesc.top (n - E.topSz kmin n j) (2 ^ E.topSz kmin n j)
    (hiVec n (E.topSz kmin n j) (E.topAns kmin n v t j))

/-- **The calls of a top job.** -/
def kidsTop (kmin n0 n B : ℕ) (v : ℕ → Bits n → ℂ) : List MDesc :=
  if n0 ≤ n ∧ E.topN kmin n ≤ B then
    (List.range (B / E.topN kmin n)).flatMap
      (fun t => E.topRoot kmin n B v t :: (List.range (E.topN kmin n)).map (E.topRest kmin n v t))
  else []

end Eng

end
end PowerSaving.RAM
end OAI

#print axioms OAI.PowerSaving.RAM.fromHi_ripple
