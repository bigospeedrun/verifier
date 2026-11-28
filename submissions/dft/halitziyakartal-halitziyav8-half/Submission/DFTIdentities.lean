-- Algebraic identities behind the transform programs: roots of unity, the DFT and its inverse, cyclic
-- convolution, the even/odd split, the chirp (Bluestein) reduction, Toeplitz inversion and the
-- Newton factorization of the root Vandermonde matrix. The proofs are this tree's own (primitive roots come
-- from Mathlib's `IsPrimitiveRoot`; see texts/credits.lean, item 1).
import Submission.Goal
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.RootsOfUnity.Complex
set_option linter.all false

section

namespace OAI
namespace PowerSaving
open Complex Matrix Finset
noncomputable section

/-- `ζ` has multiplicative order exactly `k`: Mathlib's `IsPrimitiveRoot`, whose API (`pow_eq_one`,
`ne_zero`, `inv`, `pow_of_dvd`, `pow_inj`, ...) the rest of the tree uses through dot notation. -/
abbrev Spectral.PrimRoot (ζ : ℂ) (k : ℕ) : Prop := IsPrimitiveRoot ζ k

abbrev Line := ℕ → ℂ

namespace Spectral

def freq (n : ℕ) (u : ℂ) (x : Line) : Line :=
  fun i => ∑ j ∈ range n, u ^ (i*j) * x j

/-- the `n × n` matrix of powers `u ^ (i j)`. -/
def rootVandermonde (n : ℕ) (u : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => u ^ (i.val*j.val)

def front (n : ℕ) (x : Line) : Vec n := fun i => x i.val

lemma root_eq (n : ℕ) : root n = Complex.exp (2 * Real.pi * Complex.I / (n : ℂ)) := rfl

lemma root_primitive (n : ℕ) (hn : 0<n) : PrimRoot (root n) n :=
  Complex.isPrimitiveRoot_exp n hn.ne'

lemma root_four : root 4 = I := by
  have e : 2 * (Real.pi : ℂ) * I / ((4 : ℕ) : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) * I := by push_cast; ring
  rw [root_eq, e, exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

/-- powers of `root (m q)` in steps of `q` give `root m`. -/
lemma root_factor {n m : ℕ} (hn : 0<n) (hm : m ∣ n) :
    (root n)^(n/m)=root m := by
  obtain ⟨q, rfl⟩ := hm
  have hm0 : 0 < m := Nat.pos_of_ne_zero fun e => by simp [e] at hn
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 fun e => by simp [e] at hn
  rw [Nat.mul_div_cancel_left _ hm0, root_eq, root_eq, ← Complex.exp_nat_mul, Nat.cast_mul,
    mul_div_assoc', mul_comm (q : ℂ), mul_div_mul_right _ _ hq0]

/-- exponents only matter modulo the order. -/
lemma power_mod {M : Type*} [Monoid M] {u : M} {n : ℕ} (hu : u^n=1) (i : ℕ) :
    u^(i%n)=u^i := by
  calc u ^ (i % n) = (u ^ n) ^ (i / n) * u ^ (i % n) := by rw [hu, one_pow, one_mul]
    _ = u ^ i := by rw [← pow_mul, ← pow_add, Nat.div_add_mod]

lemma conj_of_root {n : ℕ} {u : ℂ} (hn : 0<n) (hu : u^n=1) :
    (starRingEnd ℂ) u = u⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_eq_one_of_pow_eq_one hu hn.ne']
  simp

lemma freq_congr {n : ℕ} {x y : Line} (h : ∀ i < n, x i=y i) (u : ℂ) :
    freq n u x = freq n u y :=
  funext fun i => sum_congr rfl fun j hj => congrArg (u ^ (i*j) * ·) (h j (mem_range.1 hj))

/-- orthogonality of characters: the `n`-term geometric sum of `u⁻¹ ^ i u ^ k` is `n` on the
diagonal and `0` off it. -/
lemma char_orth {n : ℕ} {u : ℂ} (hu : PrimRoot u n) {i k : ℕ} (hi : i < n) (hk : k < n) :
    ∑ j ∈ range n, (u⁻¹ ^ i * u ^ k) ^ j = if k = i then (n : ℂ) else 0 := by
  have hu0 : u ≠ 0 := hu.ne_zero (Nat.ne_zero_of_lt hi)
  split_ifs with e
  · subst e
    rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hu0)]
    simp
  · have hne : u⁻¹ ^ i * u ^ k ≠ 1 := fun h => e (hu.pow_inj hk hi
      ((inv_mul_eq_one₀ (pow_ne_zero _ hu0)).1 (by rwa [inv_pow] at h)).symm)
    have hpow : (u⁻¹ ^ i * u ^ k) ^ n = 1 := by
      rw [show (u⁻¹ ^ i * u ^ k) ^ n = (u⁻¹ ^ n) ^ i * (u ^ n) ^ k by ring, hu.inv.pow_eq_one,
        hu.pow_eq_one, one_pow, one_pow, one_mul]
    rw [geom_sum_eq hne, hpow, sub_self, zero_div]

/-- the inverse transform (`u⁻¹`, scaled by `1/n`) undoes the forward one on `[0, n)`. -/
lemma freq_inv {n : ℕ} {u : ℂ} (hu : PrimRoot u n) (x : Line)
    (i : ℕ) (hi : i<n) :
    (n:ℂ)⁻¹ * freq n u⁻¹ (freq n u x) i = x i := by
  have hn : (n:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hi)
  have swap : freq n u⁻¹ (freq n u x) i =
      ∑ k ∈ range n, x k * ∑ j ∈ range n, (u⁻¹ ^ i * u ^ k) ^ j := by
    simp only [freq, mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
  rw [swap, sum_congr rfl fun k hk => by rw [char_orth hu hi (mem_range.1 hk)]]
  simp only [mul_ite, mul_zero, sum_ite_eq', mem_range, hi, if_true]
  rw [mul_comm]; exact mul_inv_cancel_right₀ hn (x i)

def predAt (n i j : ℕ) := if j ≤ i then i-j else i+n-j

def cyclic (n : ℕ) (h x : Line) : Line :=
  fun i => ∑ j ∈ range n, h (predAt n i j) * x j

/-- for `j < n`, `i ↦ predAt n i j` (subtract `j` modulo `n`) permutes `[0, n)`. -/
lemma cyc_reindex (n j : ℕ) (hj : j < n) (f : ℕ → ℂ) :
    ∑ i ∈ range n, f (predAt n i j) = ∑ m ∈ range n, f m := by
  refine sum_nbij' (predAt n · j) (fun m => if n ≤ m + j then m + j - n else m + j) ?_ ?_ ?_ ?_
    (fun _ _ => rfl)
  all_goals intro a ha
  all_goals rw [mem_range] at ha
  · rw [mem_range]
    unfold predAt
    by_cases h : j ≤ a
    · rw [if_pos h]; exact (Nat.sub_le a j).trans_lt ha
    · rw [if_neg h]
      exact Nat.sub_lt_left_of_lt_add (hj.le.trans (Nat.le_add_left n a))
        (Nat.add_lt_add_right (Nat.lt_of_not_le h) n)
  · rw [mem_range]
    by_cases h : n ≤ a + j
    · rw [if_pos h]; exact Nat.sub_lt_left_of_lt_add h (Nat.add_lt_add ha hj)
    · rw [if_neg h]; exact Nat.lt_of_not_le h
  · show (if n ≤ predAt n a j + j then predAt n a j + j - n else predAt n a j + j) = a
    unfold predAt
    by_cases h : j ≤ a
    · rw [if_pos h, Nat.sub_add_cancel h, if_neg (Nat.not_le.2 ha)]
    · rw [if_neg h, Nat.sub_add_cancel (hj.le.trans (Nat.le_add_left n a)),
        if_pos (Nat.le_add_left n a), Nat.add_sub_cancel]
  · show predAt n (if n ≤ a + j then a + j - n else a + j) j = a
    unfold predAt
    by_cases h : n ≤ a + j
    · rw [if_pos h, if_neg (Nat.not_le.2 (Nat.sub_lt_left_of_lt_add h (Nat.add_lt_add_right ha j))),
        Nat.sub_add_cancel h, Nat.add_sub_cancel]
    · rw [if_neg h, if_pos (Nat.le_add_left j a), Nat.add_sub_cancel]

/-- `u ^ (k i)` splits along `i = predAt n i j + j (mod n)`. -/
lemma pow_predAt {n : ℕ} {u : ℂ} (hu : u^n=1) (k i j : ℕ) (hj : j < n) :
    u^(k*i) = u^(k*predAt n i j) * u^(k*j) := by
  rw [← pow_add, ← mul_add]
  unfold predAt
  split_ifs with h
  · rw [Nat.sub_add_cancel h]
  · have e : u^(k*n) = 1 := by rw [pow_mul', hu, one_pow]
    rw [Nat.sub_add_cancel (hj.le.trans (Nat.le_add_left n i)), mul_add, pow_add, e, mul_one]

/-- convolution theorem: the transform of a cyclic convolution is the pointwise product. -/
lemma freq_cyclic {n : ℕ} {u : ℂ} (hu : u^n=1) (h x : Line) (k : ℕ) :
    freq n u (cyclic n h x) k = freq n u h k * freq n u x k := by
  simp only [freq, cyclic, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun j hj => ?_
  rw [sum_mul, ← cyc_reindex n j (mem_range.1 hj) (fun m => u^(k*m) * h m * (u^(k*j) * x j))]
  exact sum_congr rfl fun i _ => by rw [pow_predAt hu k i j (mem_range.1 hj)]; ring

/-- a sum over `[0, 2n)` read in pairs `(2j, 2j+1)`. -/
lemma sum_range_pairs (f : ℕ → ℂ) : ∀ n : ℕ,
    ∑ j ∈ range (n+n), f j = ∑ j ∈ range n, (f (2*j) + f (2*j+1))
  | 0 => rfl
  | n+1 => by
    rw [show n+1+(n+1) = n+n+1+1 from congrArg (· + 1) (Nat.add_right_comm n 1 n), sum_range_succ f (n+n+1), sum_range_succ f (n+n),
      sum_range_pairs f n, sum_range_succ (fun j => f (2*j) + f (2*j+1)) n, two_mul, add_assoc]

lemma freq_eo (n : ℕ) (u : ℂ) (i : ℕ) (x : Line) :
    freq (n+n) u x i =
    freq n (u^2) (fun j => x (2*j)) i +
    u^i * freq n (u^2) (fun j => x (2*j+1)) i := by
  unfold freq
  rw [sum_range_pairs, sum_add_distrib, mul_sum]
  exact congrArg₂ (· + ·) (sum_congr rfl fun j _ => by ring) (sum_congr rfl fun j _ => by ring)

lemma even_prim {n : ℕ} {u : ℂ} (hu : PrimRoot u (n+n)) :
    PrimRoot (u^2) n := by
  simpa [show (n+n)/2 = n by rw [← two_mul, Nat.mul_div_cancel_left n two_pos]] using
    hu.pow_of_dvd two_ne_zero ⟨n, (two_mul n).symm⟩

lemma freq_period {n : ℕ} {v : ℂ} (hv : v^n = 1) (y : Line) (i : ℕ) :
    freq n v y (n+i) = freq n v y i :=
  sum_congr rfl fun j _ => by rw [add_mul, pow_add, pow_mul, hv, one_pow, one_mul]

/-- upper half of the even/odd split: the twiddle `u ^ (n+i) = - u ^ i`. -/
lemma freq_eo' {n : ℕ} {u : ℂ} (hn : 0<n) (hu : PrimRoot u (n+n))
    (i : ℕ) (x : Line) :
    freq (n+n) u x (n+i) =
    freq n (u^2) (fun j => x (2*j)) i -
    u^i * freq n (u^2) (fun j => x (2*j+1)) i := by
  have half : u^n = -1 := by
    have := hu.pow_of_dvd hn.ne' ⟨2, (mul_two n).symm⟩
    rw [show (n+n)/n = 2 from Nat.div_eq_of_eq_mul_left hn (by ring)] at this
    exact this.eq_neg_one_of_two_right
  have h2 := (even_prim hu).pow_eq_one
  rw [freq_eo, freq_period h2, freq_period h2, pow_add, half]
  ring

end Spectral
end
end PowerSaving
end OAI

namespace OAI
namespace PowerSaving
open Finset Complex Matrix
noncomputable section
namespace Spectral

/-- `signedRoot false n = root n`, `signedRoot true n = (root n)⁻¹` (forward and inverse transform). -/
def signedRoot (r : Bool) (n : ℕ) : ℂ := bif r then (root n)⁻¹ else root n

lemma primitive_pr (n : ℕ) (hn : 0<n) (r : Bool) :
    PrimRoot (signedRoot r n) n := by
  cases r
  · exact root_primitive n hn
  · exact (root_primitive n hn).inv

/-- cyclic convolution computed through transforms. -/
lemma cyc_formula {u : ℂ} {n : ℕ} (hu : PrimRoot u n) (x h : Line) {i} (hi : i<n) :
    (n:ℂ)⁻¹ * freq n u⁻¹ (fun j => freq n u h j * freq n u x j) i =
    cyclic n h x i := by
  have e : (fun j => freq n u h j * freq n u x j) = freq n u (cyclic n h x) :=
    funext fun j => (freq_cyclic hu.pow_eq_one h x j).symm
  rw [e, freq_inv hu _ i hi]

/-- truncation: a sum of `if i < n then x i else 0` over a longer range. -/
lemma range_pad (n N : ℕ) (h : n ≤ N) (x : Line) :
    ∑ i ∈ range N, (if i < n then x i else 0) = ∑ i ∈ range n,x i := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [sum_range_add, sum_congr rfl fun i hi => if_pos (mem_range.1 hi),
    sum_eq_zero fun i _ => if_neg (by omega), add_zero]

def chirp (z : ℂ) : Line := fun i => z ^ (i*i)

def chirpSeed (n : ℕ) (z : ℂ) (x : Line) : Line :=
  fun i => if i<n then chirp z i * x i else 0

def chirpDist (n N : ℕ) (i : ℕ) := if i < n then i else N-i

def chirpFilter (n N : ℕ) (z : ℂ) : Line :=
  fun i => (chirp z (chirpDist n N i))⁻¹

/-- the chirp identity `i² + j² - (i-j)² = 2 i j`, read through the cyclic index. -/
lemma chirp_pair {z : ℂ} (hz : z ≠ 0) {n N i j : ℕ} (hN : 2*n ≤ N) (hi : i < n) (hj : j < n) :
    chirp z i * chirpFilter n N z (predAt N i j) * chirp z j = (z^2)^(i*j) := by
  obtain ⟨d, hd, hsq⟩ : ∃ d, chirpDist n N (predAt N i j) = d ∧ i*i + j*j = d*d + 2*(i*j) := by
    unfold chirpDist predAt
    by_cases hji : j ≤ i
    · refine ⟨i - j, by rw [if_pos hji, if_pos ((Nat.sub_le i j).trans_lt hi)], ?_⟩
      obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hji
      rw [Nat.add_sub_cancel_left]; ring
    · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le (Nat.lt_of_not_le hji).le
      have he : e < n := (Nat.le_add_left e i).trans_lt hj
      have hnN : n + e ≤ N := (Nat.add_le_add_left he.le n).trans ((two_mul n).symm.le.trans hN)
      refine ⟨e, ?_, by ring⟩
      rw [if_neg hji, Nat.add_sub_add_left, if_neg (Nat.not_lt.2 (Nat.le_sub_of_add_le hnN)),
        Nat.sub_sub_self ((Nat.le_add_left e n).trans hnN)]
  simp only [chirp, chirpFilter, hd]
  rw [mul_right_comm, ← pow_add, hsq, pow_add, mul_comm (z^(d*d)),
    mul_inv_cancel_right₀ (pow_ne_zero _ hz), pow_mul]

lemma chirp_cyclic (z : ℂ) (h : z≠0) (x : Line) {n N : ℕ} (hn : 2*n≤N) (i : ℕ) (hi : i<n) :
    chirp z i * (cyclic N (chirpFilter n N z) (chirpSeed n z x) i) =
    freq n (z^2) x i := by
  unfold cyclic freq
  rw [mul_sum, ← range_pad n N ((Nat.le_mul_of_pos_left n two_pos).trans hn) (fun j => (z^2)^(i*j) * x j)]
  refine sum_congr rfl fun j _ => ?_
  unfold chirpSeed
  split_ifs with hj
  · rw [← chirp_pair h hn hi hj]; ring
  · ring

def pointC (n : ℕ) (u : ℂ) (h x : Line) : Line :=
  fun i => freq n u h i * freq n u x i

def fetchC (n : ℕ) (u : ℂ) (h x : Line) : Line :=
  freq n u⁻¹ (pointC n u h x)

lemma signedRoot_sq (n : ℕ) (hn : 0 < n) (r : Bool) :
    signedRoot r (2*n) ^ 2 = signedRoot r n := by
  have e : root (2*n) ^ 2 = root n := by
    simpa [Nat.mul_div_cancel _ hn] using root_factor (n := 2*n) (m := n) (by omega) (dvd_mul_left n 2)
  cases r
  · exact e
  · exact (inv_pow _ _).trans (congrArg _ e)

/-- Bluestein: a length-`n` transform at `signedRoot ret n` from one cyclic convolution of length `N ≥ 2n`. -/
lemma bluestein_freq (n N : ℕ) (hn : 0<n) (hh : 2*n ≤ N) (ret : Bool) (x : Line)
    (i : ℕ) (hi : i<n) :
    let z := signedRoot ret (2*n)
    chirp z i * ((N:ℂ)⁻¹ * fetchC N (signedRoot false N) (chirpFilter n N z) (chirpSeed n z x) i)
      = freq n (signedRoot ret n) x i := by
  dsimp only
  have h2n : 0 < 2*n := Nat.mul_pos two_pos hn
  have hz : signedRoot ret (2*n) ≠ 0 := (primitive_pr (2*n) h2n ret).ne_zero h2n.ne'
  have conv := cyc_formula (primitive_pr N (h2n.trans_le hh) false) (chirpSeed n (signedRoot ret (2*n)) x)
    (chirpFilter n N (signedRoot ret (2*n))) (i := i) (hi.trans_le ((Nat.le_mul_of_pos_left n two_pos).trans hh))
  rw [← signedRoot_sq n hn ret, ← chirp_cyclic _ hz x hh i hi, ← conv]
  rfl

lemma dft_front (n : ℕ) (x : Line) :
    dft n (front n x) = front n (freq n (signedRoot false n) x) :=
  funext fun j => Fin.sum_univ_eq_sum_range (fun k => root n ^ (j.val * k) * x k) n

def extendLine {n : ℕ} (x : Vec n) : Line := fun i => if h : i<n then x ⟨i,h⟩ else 0

lemma front_exact {n : ℕ} (x : Vec n) : front n (extendLine x) = x :=
  funext fun i => dif_pos i.isLt

end Spectral
end
end PowerSaving
end OAI

namespace OAI
namespace PowerSaving.Spectral
open Matrix Finset Complex
noncomputable section

def rise (h : Line) (i j : ℕ) : ℂ := if j ≤ i then h (i-j) else 0

/-- the lower-triangular Toeplitz matrix of `h`. -/
def lowerToeplitz (n : ℕ) (h : Line) : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun a b => rise h a b

def gap (u : ℂ) : Line := fun i => ∏ j ∈ range i, (1-u^(j+1))

def roof (u : ℂ) : Line := fun i => ∏ j ∈ range i, (-(u^j))

def floorH (u : ℂ) : Line := fun i => (gap u i)⁻¹

def vandDiag (u : ℂ) : Line := fun i => gap u i * roof u i

abbrev RootMat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

def fade (n : ℕ) (d : Line) : RootMat n := Matrix.diagonal (front n d)

def vandLower (n : ℕ) (u : ℂ) : RootMat n :=
    fade n (gap u) * lowerToeplitz n (floorH u) * fade n (roof u)

lemma gap_ne_zero {n : ℕ} (u : ℂ) (h : PrimRoot u n) (j : ℕ) (hj : j<n) :
    gap u j ≠ 0 := by
  refine prod_ne_zero_iff.2 fun t ht e => ?_
  have ht' := mem_range.1 ht
  exact h.pow_ne_one_of_pos_of_lt (l := t+1) (Nat.succ_ne_zero t) ((Nat.succ_le_of_lt ht').trans_lt hj)
    (sub_eq_zero.1 e).symm

def toeplitzApply (v : ℕ) (h x : Line) : Line :=
  fun i => ∑ j ∈ range v, rise h i j * x j

/-- the transposed (upper-triangular) Toeplitz action. -/
def toeplitzApplyT (v : ℕ) (h x : Line) : Line :=
  fun i => ∑ j ∈ range v, x j * rise h j i

lemma front_stencil (v : ℕ) (h x : Line) :
    front v (toeplitzApply v h x)= lowerToeplitz v h *ᵥ front v x :=
  funext fun i => (Fin.sum_univ_eq_sum_range (fun j => rise h i j * x j) v).symm

lemma front_stencilT (v : ℕ) (h x : Line) :
    front v (toeplitzApplyT v h x)=(lowerToeplitz v h)ᵀ *ᵥ front v x := by
  funext i
  show ∑ j ∈ range v, x j * rise h j i = _
  rw [← Fin.sum_univ_eq_sum_range (fun j => x j * rise h j i) v]
  exact sum_congr rfl fun j _ => mul_comm _ _

/-- reversing the index turns the lower Toeplitz action into the upper one. -/
lemma stencil_reversed (v : ℕ) (h x : Line) (i : ℕ) (hi : i<v) :
    toeplitzApply v h (fun j => x (v-1-j)) (v-1-i) = toeplitzApplyT v h x i := by
  unfold toeplitzApply toeplitzApplyT
  rw [← sum_range_reflect]
  refine sum_congr rfl fun j hj => ?_
  have hj := mem_range.1 hj
  have hj1 : j ≤ v - 1 := Nat.le_sub_one_of_lt hj
  show rise h (v-1-i) (v-1-j) * x (v-1-(v-1-j)) = x j * rise h j i
  rw [Nat.sub_sub_self hj1, mul_comm]
  unfold rise
  by_cases c : i ≤ j
  · rw [if_pos (Nat.sub_le_sub_left c (v-1)), if_pos c, tsub_tsub_tsub_cancel_left hj1]
  · have c' : j < i := Nat.lt_of_not_le c
    rw [if_neg (Nat.not_le.2 (Nat.sub_lt_sub_left (c'.trans_le (Nat.le_sub_one_of_lt hi)) c')),
      if_neg c]

lemma stencil_left (v w : ℕ) (h x : Line) (i : ℕ) (hi : i<v) :
    toeplitzApply (v+w) h x i=toeplitzApply v h x i := by
  unfold toeplitzApply
  rw [sum_range_add, add_eq_left]
  exact sum_eq_zero fun k _ => by
    rw [rise, if_neg (Nat.not_le.2 (hi.trans_le (Nat.le_add_right v k))), zero_mul]

lemma stencil_right (v w : ℕ) (h x : Line) (i : ℕ) :
    toeplitzApply (v+w) h x (v+i)=toeplitzApply v h x (v+i)+toeplitzApply w h (fun j => x (v+j)) i := by
  unfold toeplitzApply
  rw [sum_range_add]
  congr 1
  exact sum_congr rfl fun k _ => by
    unfold rise
    by_cases c : k ≤ i
    · rw [if_pos (Nat.add_le_add_left c v), if_pos c, Nat.add_sub_add_left]
    · rw [if_neg (fun h => c (Nat.le_of_add_le_add_left h)), if_neg c]

lemma stencil_congr (v : ℕ) (h : Line) {x y : Line} (H : ∀ i<v, x i=y i) :
    toeplitzApply v h x = toeplitzApply v h y :=
  funext fun i => sum_congr rfl fun j hj => congrArg (rise h i j * ·) (H j (mem_range.1 hj))

def toeplitzInvUpTo (h : Line) : ℕ → Line
  | 0 => fun _ => (h 0)⁻¹
  | k+1 => fun j => if j ≤ k then toeplitzInvUpTo h k j
      else -(∑ i ∈ range (k+1), toeplitzInvUpTo h k (k-i)*h (i+1))/(h 0)

def toeplitzInv (h : Line) (j : ℕ) : ℂ := toeplitzInvUpTo h j j

lemma toeplitzInvUpTo_stable (h : Line) : ∀ k j, j ≤ k → toeplitzInvUpTo h k j = toeplitzInv h j
  | 0, j, hj => by obtain rfl : j = 0 := Nat.le_zero.1 hj
                   rfl
  | k+1, j, hj => by
    rcases Nat.lt_or_ge j (k+1) with c | c
    · show (if j ≤ k then toeplitzInvUpTo h k j else _) = _
      rw [if_pos (Nat.lt_succ_iff.1 c), toeplitzInvUpTo_stable h k j (Nat.lt_succ_iff.1 c)]
    · obtain rfl : j = k+1 := le_antisymm hj c
      rfl

/-- `toeplitzInv h` is the power-series inverse of `h`: its convolution with `h` is the unit sequence. -/
lemma toeplitzInv_conv (h : Line) (hh : h 0 ≠ 0) (m : ℕ) :
    ∑ k ∈ range (m+1), toeplitzInv h (m-k) * h k = if m = 0 then 1 else 0 := by
  cases m with
  | zero => rw [sum_range_one, if_pos rfl]; exact inv_mul_cancel₀ hh
  | succ m =>
    rw [if_neg (Nat.succ_ne_zero m), sum_range_succ', Nat.sub_zero]
    have top : toeplitzInv h (m+1) * h 0 = -∑ i ∈ range (m+1), toeplitzInvUpTo h m (m-i) * h (i+1) := by
      show (if m + 1 ≤ m then _ else _) * h 0 = _
      rw [if_neg (Nat.not_succ_le_self m), div_mul_cancel₀ _ hh]
    rw [top, ← sub_eq_add_neg, sub_eq_zero]
    exact sum_congr rfl fun i hi => by
      rw [toeplitzInvUpTo_stable h m (m-i) (Nat.sub_le m i), Nat.add_sub_add_right]

/-- row `i` of `lowerToeplitz (toeplitzInv h)` times column `l` of `lowerToeplitz h`. -/
lemma rise_inner (h : Line) (hh : h 0 ≠ 0) (v i l : ℕ) (hi : i < v) :
    ∑ j ∈ range v, rise (toeplitzInv h) i j * rise h j l = if l = i then 1 else 0 := by
  have outside : ∀ j ∈ range v, j ∉ Ico l (i+1) → rise (toeplitzInv h) i j * rise h j l = 0 :=
    fun j _ hj => by
      rw [mem_Ico, not_and_or, not_le, not_lt] at hj
      unfold rise
      rcases hj with c | c
      · rw [if_neg (Nat.not_le.2 c), mul_zero]
      · rw [if_neg (Nat.not_le.2 c), zero_mul]
  rw [← sum_subset (fun j hj => mem_range.2 ((Nat.lt_succ_iff.1 (mem_Ico.1 hj).2).trans_lt hi)) outside]
  by_cases hli : l ≤ i
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hli
    rw [sum_Ico_eq_sum_range, show l + m + 1 - l = m + 1 from Nat.add_sub_cancel_left l (m+1)]
    have e : ∀ k ∈ range (m+1),
        rise (toeplitzInv h) (l+m) (l+k) * rise h (l+k) l = toeplitzInv h (m-k) * h k := by
      intro k hk
      have := mem_range.1 hk
      unfold rise
      rw [if_pos (Nat.add_le_add_left (Nat.lt_succ_iff.1 this) l), if_pos (Nat.le_add_right l k),
        Nat.add_sub_add_left, Nat.add_sub_cancel_left]
    rw [sum_congr rfl e, toeplitzInv_conv h hh m]
    by_cases hm : m = 0 <;> simp [hm]
  · rw [Ico_eq_empty (fun h => hli (Nat.lt_succ_iff.1 h)), sum_empty, if_neg (fun e => hli e.le)]

/-- applying the Toeplitz matrix of `toeplitzInv h` after that of `h` is the identity on `[0, v)`. -/
lemma toeplitzInv_left_inv (v : ℕ) (h x : Line) (hh : h 0≠0) (i : ℕ) (hi : i<v) :
    toeplitzApply v (toeplitzInv h) (toeplitzApply v h x) i = x i := by
  unfold toeplitzApply
  simp only [mul_sum]
  rw [sum_comm]
  calc ∑ l ∈ range v, ∑ j ∈ range v, rise (toeplitzInv h) i j * (rise h j l * x l)
      = ∑ l ∈ range v, (if l = i then 1 else 0) * x l := sum_congr rfl fun l _ => by
        rw [← rise_inner h hh v i l hi, sum_mul]
        exact sum_congr rfl fun j _ => by ring
    _ = x i := by simp [hi]

/-- `newtonBasis u j` lists the coefficients of `∏ t < j, (X - u ^ t)`. -/
def newtonBasis (u : ℂ) : ℕ → ℕ → ℂ
  | 0, m => if m = 0 then 1 else 0
  | j+1, m => (if m = 0 then 0 else newtonBasis u j (m-1)) - u^j * newtonBasis u j m

theorem newtonBasis_zero_of_lt (u : ℂ) : ∀ j m : ℕ, j < m → newtonBasis u j m = 0
  | 0, m, h => if_neg (by omega)
  | j+1, m, h => by
    rw [newtonBasis, if_neg (Nat.ne_zero_of_lt h), newtonBasis_zero_of_lt u j (m-1) (Nat.lt_sub_of_add_lt h),
      newtonBasis_zero_of_lt u j m ((Nat.lt_succ_self j).trans h)]
    ring

theorem newtonBasis_self (u : ℂ) : ∀ j, newtonBasis u j j = 1
  | 0 => rfl
  | j+1 => by rw [newtonBasis, if_neg (Nat.succ_ne_zero j), Nat.add_sub_cancel, newtonBasis_self u j,
      newtonBasis_zero_of_lt u j (j+1) (Nat.lt_succ_self j)]; ring

/-- evaluating the coefficient list at `x`. -/
lemma newtonBasis_eval (u x : ℂ) {j n : ℕ} (hj : j < n) :
    ∑ m ∈ range n, newtonBasis u j m * x^m = ∏ t ∈ range j, (x - u^t) := by
  induction j generalizing n with
  | zero =>
    rw [prod_range_zero, sum_eq_single 0 (fun m _ hm => by simp [newtonBasis, hm])
      (fun h => absurd (mem_range.2 hj) h)]
    simp [newtonBasis]
  | succ j ih =>
    obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, (Nat.sub_add_cancel (Nat.one_le_of_lt hj)).symm⟩
    set S := ∑ m ∈ range N, newtonBasis u j m * x^m
    have hS : ∑ m ∈ range (N+1), newtonBasis u j m * x^m = S := by
      rw [sum_range_succ, newtonBasis_zero_of_lt u j N (Nat.lt_of_succ_lt_succ hj), zero_mul, add_zero]
    have shift : ∑ m ∈ range N, newtonBasis u j m * x^(m+1) = x * S := by
      rw [mul_sum]; exact sum_congr rfl fun m _ => by ring
    have low : ∑ m ∈ range N, newtonBasis u j (m+1) * x^(m+1) + newtonBasis u j 0 = S := by
      rw [← hS, sum_range_succ' _ N, pow_zero, mul_one]
    rw [prod_range_succ, ← ih (Nat.lt_of_succ_lt_succ hj), sum_range_succ', pow_zero, mul_one]
    simp only [newtonBasis, if_true, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, sub_mul,
      sum_sub_distrib, zero_sub]
    have e2 : ∑ m ∈ range N, u ^ j * newtonBasis u j (m + 1) * x ^ (m + 1) =
        u^j * ∑ m ∈ range N, newtonBasis u j (m+1) * x^(m+1) := by
      rw [mul_sum]; exact sum_congr rfl fun m _ => by ring
    rw [shift, e2]
    linear_combination (-u^j) * low

def newtonMat (n : ℕ) (u : ℂ) : RootMat n := Matrix.of fun m j => newtonBasis u j.val m.val

def nodeMat (n : ℕ) (u : ℂ) : RootMat n := Matrix.of fun i j => ∏ t ∈ range j.val, (u^i.val - u^t)

lemma node_zero (u : ℂ) {m a : ℕ} (h : m < a) : ∏ t ∈ range a, (u^m - u^t) = 0 :=
  prod_eq_zero (mem_range.2 h) (sub_self _)

lemma lower_entry {n : ℕ} {u : ℂ} (h : PrimRoot u n) {i : ℕ} (hi : i < n) (j : ℕ) :
    gap u i * rise (floorH u) i j * roof u j = ∏ t ∈ range j, (u^i - u^t) := by
  by_cases hji : j ≤ i
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le' hji
    have hg := gap_ne_zero u h d ((Nat.le_add_right d j).trans_lt hi)
    have e1 : gap u (d + j) = gap u d * ∏ s ∈ range j, (1 - u^(d+s+1)) := by
      simp only [gap]
      rw [prod_range_add]
    have e2 : ∏ t ∈ range j, (u^(d+j) - u^t) = roof u j * ∏ s ∈ range j, (1 - u^(d+s+1)) := by
      simp only [roof]
      rw [← prod_range_reflect (fun s => 1 - u^(d+s+1)) j, ← prod_mul_distrib]
      refine prod_congr rfl fun t ht => ?_
      rw [mem_range] at ht
      have e3 : u^(d+j) = u^t * u^(d+j-t) := by
        rw [← pow_add, Nat.add_sub_cancel' (ht.le.trans (Nat.le_add_left j d))]
      rw [show d + (j - 1 - t) + 1 = d + j - t by
        rw [Nat.add_assoc, Nat.sub_right_comm, Nat.sub_add_cancel (Nat.sub_pos_of_lt ht),
          Nat.add_sub_assoc ht.le], e3]
      ring
    simp only [rise, if_pos hji, Nat.add_sub_cancel, floorH]
    rw [e2, e1, mul_right_comm (gap u d), mul_inv_cancel₀ hg, one_mul, mul_comm]
  · rw [rise, if_neg hji, mul_zero, zero_mul, node_zero u (Nat.lt_of_not_le hji)]

lemma vandDiag_eq {n : ℕ} {u : ℂ} (h : PrimRoot u n) {a : ℕ} (ha : a < n) :
    vandDiag u a = ∏ t ∈ range a, (u^a - u^t) := by
  rw [← lower_entry h ha a]
  simp [vandDiag, rise, floorH, gap]

lemma newtonMat_cancel {n : ℕ} (u : ℂ) {X : RootMat n} (hX : X * newtonMat n u = 0) : X = 0 := by
  ext i j
  suffices H : ∀ k (j : Fin n), j.val = k → X i j = 0 from H _ j rfl
  intro k
  refine Nat.strong_induction_on k fun k ih => ?_
  intro j hj
  have e : (X * newtonMat n u) i j = 0 := by simp [hX]
  rw [Matrix.mul_apply, Fintype.sum_eq_single j] at e
  · simpa [newtonMat, newtonBasis_self] using e
  · intro m hm
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hm) with h | h
    · rw [ih m.val (by omega) m rfl, zero_mul]
    · show X i m * newtonBasis u j.val m.val = 0
      rw [newtonBasis_zero_of_lt u _ _ h, mul_zero]

theorem rootVandermonde_factor (n : ℕ) (u : ℂ) (h : PrimRoot u n) :
    rootVandermonde n u =
      vandLower n u * fade n (fun i => (vandDiag u i)⁻¹) * (vandLower n u)ᵀ := by
  have hL : vandLower n u = nodeMat n u := by
    ext i j
    simp only [vandLower, fade, mul_diagonal, diagonal_mul, front, lowerToeplitz, nodeMat, of_apply]
    exact lower_entry h i.isLt j.val
  have hVN : rootVandermonde n u * newtonMat n u = nodeMat n u := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [rootVandermonde, newtonMat, nodeMat, of_apply, pow_mul]
    rw [Fin.sum_univ_eq_sum_range (fun m => (u^i.val)^m * newtonBasis u j.val m) n,
      ← newtonBasis_eval u (u^i.val) j.isLt]
    exact sum_congr rfl fun m _ => mul_comm _ _
  have hVt : (rootVandermonde n u)ᵀ = rootVandermonde n u := by
    ext i j
    simp only [transpose_apply, rootVandermonde, Nat.mul_comm]
  have hsym : (nodeMat n u)ᵀ * newtonMat n u = (newtonMat n u)ᵀ * nodeMat n u := by
    rw [← hVN, Matrix.transpose_mul, hVt, Matrix.mul_assoc]
  have tz : ∀ m a b : ℕ, m < a ∨ b < m →
      (∏ t ∈ range a, (u^m - u^t)) * newtonBasis u b m = 0 := by
    intro m a b hm
    rcases hm with hm | hm
    · rw [node_zero u hm, zero_mul]
    · rw [newtonBasis_zero_of_lt u b m hm, mul_zero]
  have hD : (nodeMat n u)ᵀ * newtonMat n u = fade n (vandDiag u) := by
    ext a b
    rcases eq_or_ne a b with rfl | hab
    · rw [fade, diagonal_apply_eq, Matrix.mul_apply, Fintype.sum_eq_single a]
      · simp only [transpose_apply, newtonMat, nodeMat, of_apply, front, newtonBasis_self, mul_one]
        exact (vandDiag_eq h a.isLt).symm
      · intro m hm
        have hm' : m.val ≠ a.val := fun e => hm (Fin.ext e)
        simp only [transpose_apply, newtonMat, nodeMat, of_apply]
        exact tz _ _ _ (Nat.lt_or_gt_of_ne hm')
    · rw [fade, diagonal_apply_ne _ hab]
      rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with h' | h'
      · rw [hsym, Matrix.mul_apply]
        refine sum_eq_zero fun m _ => ?_
        simp only [transpose_apply, newtonMat, nodeMat, of_apply]
        rw [mul_comm]
        exact tz m.val b.val a.val ((Nat.lt_or_ge m.val b.val).imp_right fun hm => h'.trans_le hm)
      · rw [Matrix.mul_apply]
        refine sum_eq_zero fun m _ => ?_
        simp only [transpose_apply, newtonMat, nodeMat, of_apply]
        exact tz m.val a.val b.val ((Nat.lt_or_ge m.val a.val).imp_right fun hm => h'.trans_le hm)
  have hΔ : fade n (fun i => (vandDiag u i)⁻¹) * fade n (vandDiag u) = 1 := by
    rw [fade, fade, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    have u0 := h.ne_zero (Nat.ne_zero_of_lt i.isLt)
    have hr : roof u i.val ≠ 0 :=
      prod_ne_zero_iff.mpr fun t _ => neg_ne_zero.mpr (pow_ne_zero _ u0)
    exact inv_mul_cancel₀ (mul_ne_zero (gap_ne_zero u h i.val i.isLt) hr)
  have h0 := newtonMat_cancel u (X := rootVandermonde n u
      - nodeMat n u * fade n (fun i => (vandDiag u i)⁻¹) * (nodeMat n u)ᵀ) (by
    rw [Matrix.sub_mul, hVN, Matrix.mul_assoc _ (nodeMat n u)ᵀ, hD,
      Matrix.mul_assoc (nodeMat n u) _ (fade n (vandDiag u)), hΔ, Matrix.mul_one, sub_self])
  rw [hL]
  exact sub_eq_zero.mp h0

end
end PowerSaving.Spectral
end OAI
end
