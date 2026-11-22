--might be  containing modified Apache-2.0 codes pieces from one or several sources; notices and credits: Credits.lean
import Submission.OAI.Computability.FourierTransform.Goal

namespace OAI
namespace PowerSaving
open Complex Matrix Finset
noncomputable section

structure Spectral.PrimRoot (ζ : ℂ) (k : ℕ) : Prop where
  pow_eq_one : ζ ^ k = 1
  dvd_of_pow_eq_one : ∀ l : ℕ, ζ ^ l = 1 → k ∣ l

namespace Spectral.PrimRoot
variable {ζ : ℂ} {k : ℕ} (h : Spectral.PrimRoot ζ k)
include h

theorem pow_ne_one_of_pos_of_lt {l : ℕ} (h0 : l ≠ 0) (hl : l < k) : ζ ^ l ≠ 1 := fun e =>
  absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) (h.dvd_of_pow_eq_one l e)) (by omega)

protected theorem ne_zero (hk : k ≠ 0) : ζ ≠ 0 := by
  rintro rfl
  have := h.pow_eq_one
  rw [zero_pow hk] at this
  exact zero_ne_one this

theorem inv : Spectral.PrimRoot ζ⁻¹ k :=
  ⟨by rw [inv_pow, h.pow_eq_one, inv_one], fun l hl =>
    h.dvd_of_pow_eq_one l (by rw [inv_pow] at hl; exact inv_eq_one.mp hl)⟩

theorem pow_of_dvd {p : ℕ} (hp : p ≠ 0) (hd : p ∣ k) : Spectral.PrimRoot (ζ ^ p) (k / p) := by
  obtain ⟨m, rfl⟩ := hd
  rw [Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hp)]
  refine ⟨by rw [← pow_mul, h.pow_eq_one], fun l hl => ?_⟩
  rw [← pow_mul] at hl
  exact (mul_dvd_mul_iff_left hp).mp (h.dvd_of_pow_eq_one _ hl)

theorem pow_inj {a b : ℕ} (ha : a < k) (hb : b < k) (e : ζ ^ a = ζ ^ b) : a = b := by
  wlog hab : a ≤ b generalizing a b
  · exact (this hb ha e.symm (by omega)).symm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [pow_add] at e
  have hd : ζ ^ d = 1 :=
    mul_left_cancel₀ (pow_ne_zero a (h.ne_zero (by omega))) (e.symm.trans (mul_one _).symm)
  by_contra hne
  exact h.pow_ne_one_of_pos_of_lt (l := d) (by omega) (by omega) hd

end Spectral.PrimRoot

abbrev Line := ℕ → ℂ

namespace Spectral

def freq (n : ℕ) (u : ℂ) (x : Line) : Line :=
  fun i => ∑ j ∈ range n, u ^ (i*j) * x j

def rootVandermonde (n : ℕ) (u : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => u ^ (i.val*j.val)

def front (n : ℕ) (x : Line) : Vec n := fun i => x i.val

lemma root_eq (n : ℕ) : root n = Complex.exp (2 * Real.pi * Complex.I / (n : ℂ)) := rfl

lemma root_primitive (n : ℕ) (hn : 0 < n) : Spectral.PrimRoot (root n) n := by
  have hn' : (n:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have key : ∀ l : ℕ, root n ^ l = Complex.exp (2 * Real.pi * Complex.I * l / n) := fun l => by
    rw [root_eq, ← Complex.exp_nat_mul]; congr 1; ring
  refine ⟨?_, fun l hl => ?_⟩
  · rw [key, mul_div_assoc, div_self hn', mul_one, Complex.exp_two_pi_mul_I]
  · rw [key, Complex.exp_eq_one_iff] at hl
    obtain ⟨m, hm⟩ := hl
    rw [div_eq_iff hn'] at hm
    have h0 : (2 * Real.pi * Complex.I) * ((l:ℂ) - m * n) = 0 := by linear_combination hm
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd h1 Complex.two_pi_I_ne_zero
    · have h2 : ((l:ℤ):ℂ) = ((m * n : ℤ) : ℂ) := by push_cast; exact sub_eq_zero.mp h1
      have h3 : (l:ℤ) = m * n := Int.cast_injective h2
      exact Int.natCast_dvd_natCast.mp ⟨m, by rw [h3]; ring⟩

lemma root_four : root 4 = I := by
  have : root 4 = Complex.exp ((Real.pi:ℂ) / 2 * I) := by
    rw [root_eq]; congr 1; push_cast; ring
  rw [this, Complex.exp_mul_I, Complex.cos_pi_div_two, Complex.sin_pi_div_two]
  simp

lemma root_factor {n m : ℕ} (hn : 0<n) (hm : m ∣ n) :
    (root n)^(n/m)=root m := by
  obtain ⟨q, rfl⟩ := hm
  have hm0 : m ≠ 0 := by rintro rfl; simp at hn
  have hq0 : q ≠ 0 := by rintro rfl; simp at hn
  have hm' : (m:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm0
  have hq' : (q:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq0
  rw [Nat.mul_div_cancel_left q (Nat.pos_of_ne_zero hm0), root_eq, root_eq, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp
  <;> ring

lemma power_mod {M : Type*} [Monoid M] {u : M} {n : ℕ} (hu : u^n=1) (i : ℕ) :
    u^(i%n)=u^i := by
  conv_rhs => rw [← Nat.mod_add_div i n, pow_add, pow_mul, hu, one_pow, mul_one]

lemma conj_of_root {n : ℕ} {u : ℂ} (hn : 0<n) (hu : u^n=1) :
    (starRingEnd ℂ) u = u⁻¹ := by
  have h1 : ‖u‖ = 1 := by
    have : ‖u‖ ^ n = 1 := by rw [← norm_pow, hu, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').mp this
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, h1]
  simp

lemma freq_congr {n : ℕ} {x y : Line} (h : ∀ i < n, x i=y i) (u : ℂ) :
    freq n u x = freq n u y := by
  funext i
  simp only [freq]
  exact sum_congr rfl fun j hj => by rw [h j (mem_range.mp hj)]

lemma freq_add (n : ℕ) (u : ℂ) (x y : Line) :
    freq n u (x+y) = freq n u x + freq n u y := by
  funext i
  simp only [freq, Pi.add_apply, mul_add, sum_add_distrib]

lemma freq_inv {n : ℕ} {u : ℂ} (hu : Spectral.PrimRoot u n) (x : Line)
    (i : ℕ) (hi : i<n) :
    (n:ℂ)⁻¹ * freq n u⁻¹ (freq n u x) i = x i := by
  have hn : (n:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have u0 := hu.ne_zero (by omega)
  have key : ∀ k ∈ range n,
      x k * ∑ j ∈ range n, (u⁻¹ ^ i * u ^ k) ^ j = if i = k then x k * n else 0 := by
    intro k hk
    rw [mem_range] at hk
    split_ifs with hik
    · subst hik
      simp [u0]
    · have hw : (u⁻¹ ^ i * u ^ k) ^ n = 1 := by
        rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm i, mul_comm k, pow_mul, pow_mul,
          hu.inv.pow_eq_one, hu.pow_eq_one, one_pow, one_pow, one_mul]
      have hw1 : u⁻¹ ^ i * u ^ k ≠ 1 := by
        intro e
        rw [inv_pow, inv_mul_eq_one₀ (pow_ne_zero _ u0)] at e
        exact hik (hu.pow_inj hi hk e)
      rw [geom_sum_eq hw1, hw, sub_self, zero_div, mul_zero]
  rw [show freq n u⁻¹ (freq n u x) i = ∑ k ∈ range n, x k * ∑ j ∈ range n, (u⁻¹ ^ i * u ^ k) ^ j by
      simp only [freq, mul_sum]
      rw [sum_comm]
      exact sum_congr rfl fun k _ => sum_congr rfl fun j _ => by ring,
    sum_congr rfl key, sum_ite_eq, if_pos (mem_range.mpr hi), mul_comm, mul_assoc, mul_inv_cancel₀ hn,
    mul_one]

def predAt (n i j : ℕ) := if j ≤ i then i-j else i+n-j

def cyclic (n : ℕ) (h x : Line) : Line :=
  fun i => ∑ j ∈ range n, h (predAt n i j) * x j

lemma cyc_reindex (n j : ℕ) (hj : j < n) (f : ℕ → ℂ) :
    ∑ i ∈ range n, f (predAt n i j) = ∑ m ∈ range n, f m := by
  refine sum_nbij' (fun i => predAt n i j) (fun m => if m + j < n then m + j else m + j - n)
    ?_ ?_ ?_ ?_ (fun _ _ => rfl) <;>
  (intro a ha; simp only [mem_coe, mem_range, predAt] at ha ⊢; split_ifs <;> omega)

lemma freq_cyclic {n : ℕ} {u : ℂ} (hu : u^n=1) (h x : Line) (k : ℕ) :
    freq n u (cyclic n h x) k = freq n u h k * freq n u x k := by
  have hexp : ∀ i j, j < n → u^(k*i) = u^(k*predAt n i j) * u^(k*j) := by
    intro i j hj
    rw [← pow_add, ← mul_add]
    unfold predAt
    split_ifs with hji
    · rw [Nat.sub_add_cancel hji]
    · rw [Nat.sub_add_cancel (by omega : j ≤ i + n), mul_add, pow_add, mul_comm k n,
        show u ^ (n * k) = 1 by rw [pow_mul, hu, one_pow], mul_one]
  have step : ∀ j ∈ range n, ∑ i ∈ range n, u^(k*i) * (h (predAt n i j) * x j)
      = (∑ m ∈ range n, u^(k*m) * h m) * (u^(k*j) * x j) := fun j hj => by
    rw [sum_mul, ← cyc_reindex n j (mem_range.mp hj) (fun m => u^(k*m) * h m * (u^(k*j) * x j))]
    exact sum_congr rfl fun i _ => by rw [hexp i j (mem_range.mp hj)]; ring
  simp only [freq, cyclic, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl step

lemma freq_eo (n : ℕ) (u : ℂ) (i : ℕ) (x : Line) :
    freq (n+n) u x i =
    freq n (u^2) (fun j => x (2*j)) i +
    u^i * freq n (u^2) (fun j => x (2*j+1)) i := by
  simp only [freq, two_mul]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show n + 1 + (n + 1) = n + n + 1 + 1 by omega]
    simp only [sum_range_succ, ih]
    ring

lemma even_prim {n : ℕ} {u : ℂ} (hu : Spectral.PrimRoot u (n+n)) :
    Spectral.PrimRoot (u^2) n := by
  have := hu.pow_of_dvd two_ne_zero ⟨n, by omega⟩
  rwa [show (n+n)/2 = n by omega] at this

lemma freq_period {n : ℕ} {v : ℂ} (hv : v^n = 1) (y : Line) (i : ℕ) :
    freq n v y (n+i) = freq n v y i := by
  simp only [freq]
  refine sum_congr rfl fun j _ => ?_
  rw [add_mul, pow_add, pow_mul, hv, one_pow, one_mul]

lemma freq_eo' {n : ℕ} {u : ℂ} (hn : 0<n) (hu : Spectral.PrimRoot u (n+n))
    (i : ℕ) (x : Line) :
    freq (n+n) u x (n+i) =
    freq n (u^2) (fun j => x (2*j)) i -
    u^i * freq n (u^2) (fun j => x (2*j+1)) i := by
  have h2 := (even_prim hu).pow_eq_one
  have hn1 : u^n = -1 := by
    have hsq : u^n * u^n = 1 := by rw [← pow_add, hu.pow_eq_one]
    rcases mul_self_eq_one_iff.mp hsq with h | h
    · exact absurd h (hu.pow_ne_one_of_pos_of_lt (by omega) (by omega))
    · exact h
  rw [freq_eo, freq_period h2, freq_period h2, pow_add, hn1]
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

def signedRoot : Bool→ℕ→ℂ
  | false => root
  | true => fun n => (root n)⁻¹

lemma primitive_pr (n : ℕ) (hn : 0<n) (r : Bool) :
    Spectral.PrimRoot (signedRoot r n) n := by
  cases r
  exacts [root_primitive n hn, (root_primitive n hn).inv]

lemma cyc_formula {u : ℂ} {n : ℕ} (hu : Spectral.PrimRoot u n) (x h : Line) {i} (hi : i<n) :
    (n:ℂ)⁻¹ * freq n u⁻¹ (fun j => freq n u h j * freq n u x j) i =
    cyclic n h x i := by
  rw [← freq_inv hu (cyclic n h x) i hi, funext (freq_cyclic hu.pow_eq_one h x)]

lemma range_pad (n N : ℕ) (h : n ≤ N) (x : Line) :
    ∑ i ∈ range N, (if i < n then x i else 0) = ∑ i ∈ range n,x i := by
  rw [← sum_filter]
  congr 1
  ext i
  simp only [mem_filter, mem_range]
  exact ⟨fun h' => h'.2, fun h' => ⟨by omega, h'⟩⟩

def chirp (z : ℂ) : Line := fun i => z ^ (i*i)

def chirpSeed (n : ℕ) (z : ℂ) (x : Line) : Line :=
  fun i => if i<n then chirp z i * x i else 0

def legdist (n N : ℕ) (i : ℕ) := if i < n then i else N-i

def chirpFilter (n N : ℕ) (z : ℂ) : Line :=
  fun i => (chirp z (legdist n N i))⁻¹

lemma chirp_pair {z : ℂ} (hz : z ≠ 0) {n N i j : ℕ} (hN : 2*n ≤ N) (hi : i < n) (hj : j < n) :
    chirp z i * chirpFilter n N z (predAt N i j) * chirp z j = (z^2)^(i*j) := by
  obtain ⟨d, hd, he⟩ : ∃ d, legdist n N (predAt N i j) = d ∧ i*i + j*j = 2*(i*j) + d*d := by
    rcases le_total j i with hji | hji <;> obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hji <;>
      exact ⟨d, by unfold legdist predAt; split_ifs <;> omega, by ring⟩
  simp only [chirpFilter, chirp, hd]
  rw [mul_right_comm, ← pow_add, he, pow_add z (2*(i*j)), pow_mul z 2,
    mul_inv_cancel_right₀ (pow_ne_zero _ hz)]

lemma chirp_cyclic (z : ℂ) (h : z≠0) (x : Line) {n N : ℕ} (hn : 2*n≤N) (i : ℕ) (hi : i<n) :
    chirp z i * (cyclic N (chirpFilter n N z) (chirpSeed n z x) i) =
    freq n (z^2) x i := by
  simp only [cyclic, chirpSeed, mul_ite, mul_zero]
  rw [range_pad n N (by omega) (fun j => chirpFilter n N z (predAt N i j) * (chirp z j * x j)),
    mul_sum]
  exact sum_congr rfl fun j hj => by rw [← chirp_pair h hn hi (mem_range.mp hj)]; ring

def pointC (n : ℕ) (u : ℂ) (h x : Line) : Line :=
  fun i => freq n u h i * freq n u x i

def fetchC (n : ℕ) (u : ℂ) (h x : Line) : Line :=
  freq n u⁻¹ (pointC n u h x)

lemma signedRoot_sq (n : ℕ) (hn : 0 < n) (r : Bool) :
    signedRoot r (2*n) ^ 2 = signedRoot r n := by
  have e := root_factor (n := 2*n) (m := n) (by omega) (dvd_mul_left n 2)
  rw [Nat.mul_div_cancel _ hn] at e
  cases r <;> simp only [signedRoot, inv_pow, e]

lemma bluestein_freq (n N : ℕ) (hn : 0<n) (hh : 2*n ≤ N) (ret : Bool) (x : Line)
    (i : ℕ) (hi : i<n) :
    let z := signedRoot ret (2*n)
    chirp z i * ((N:ℂ)⁻¹ * fetchC N (signedRoot false N) (chirpFilter n N z) (chirpSeed n z x) i)
      = freq n (signedRoot ret n) x i := by
  dsimp only
  rw [← signedRoot_sq n hn ret,
    ← chirp_cyclic _ ((primitive_pr (2*n) (by omega) ret).ne_zero (by omega)) x hh i hi]
  congr 1
  exact cyc_formula (primitive_pr N (by omega) false) _ _ (by omega)

lemma dft_front (n : ℕ) (x : Line) :
    dft n (front n x) = front n (freq n (signedRoot false n) x) := by
  funext j
  exact Fin.sum_univ_eq_sum_range (fun k => root n ^ (j.val * k) * x k) n

def extendLine {n : ℕ} (x : Vec n) : Line := fun i => if h : i<n then x ⟨i,h⟩ else 0

lemma front_exact {n : ℕ} (x : Vec n) : front n (extendLine x) = x := by
  funext i
  simp [front, extendLine]

end Spectral
end
end PowerSaving
end OAI

namespace OAI
namespace PowerSaving.Spectral
open Matrix Finset Complex
noncomputable section

def rise (h : Line) (i j : ℕ) : ℂ := if j ≤ i then h (i-j) else 0

def stairs (n : ℕ) (h : Line) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => rise h i.val j.val

def gap (u : ℂ) : Line := fun i => ∏ j ∈ range i, (1-u^(j+1))

def roof (u : ℂ) : Line := fun i => ∏ j ∈ range i, (-(u^j))

def floorH (u : ℂ) : Line := fun i => (gap u i)⁻¹

def vandDiag (u : ℂ) : Line := fun i => gap u i * roof u i

abbrev RootMat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

def fade (n : ℕ) (d : Line) : RootMat n := Matrix.diagonal (front n d)

def vandLower (n : ℕ) (u : ℂ) : RootMat n :=
    fade n (gap u) * stairs n (floorH u) * fade n (roof u)

lemma gap_ne_zero {n : ℕ} (u : ℂ) (h : Spectral.PrimRoot u n) (j : ℕ) (hj : j<n) :
    gap u j ≠ 0 :=
  prod_ne_zero_iff.mpr fun t ht => sub_ne_zero.mpr
    (h.pow_ne_one_of_pos_of_lt (l := t+1) (by omega) (by rw [mem_range] at ht; omega)).symm

def toeplitzApply (v : ℕ) (h x : Line) : Line :=
  fun i => ∑ j ∈ range v, rise h i j * x j

def toeplitzApplyT (v : ℕ) (h x : Line) : Line :=
  fun i => ∑ j ∈ range v, rise h j i * x j

lemma front_stencil (v : ℕ) (h x : Line) :
    front v (toeplitzApply v h x)= stairs v h *ᵥ front v x := by
  funext i
  exact (Fin.sum_univ_eq_sum_range (fun j => rise h i.val j * x j) v).symm

lemma front_creep (v : ℕ) (h x : Line) :
    front v (toeplitzApplyT v h x)=(stairs v h)ᵀ *ᵥ front v x := by
  funext i
  exact (Fin.sum_univ_eq_sum_range (fun j => rise h j i.val * x j) v).symm

lemma stencil_reversed (v : ℕ) (h x : Line) (i : ℕ) (hi : i<v) :
    toeplitzApply v h (fun j => x (v-1-j)) (v-1-i) = toeplitzApplyT v h x i := by
  simp only [toeplitzApply, toeplitzApplyT]
  rw [← sum_range_reflect (fun j => rise h (v-1-i) j * x (v-1-j)) v]
  refine sum_congr rfl fun j hj => ?_
  rw [mem_range] at hj
  simp only [rise, show v - 1 - (v - 1 - j) = j by omega]
  split_ifs <;> first | omega | rfl | (congr 2; omega)

lemma stencil_left (v w : ℕ) (h x : Line) (i : ℕ) (hi : i<v) :
    toeplitzApply (v+w) h x i=toeplitzApply v h x i := by
  have hz : ∀ k ∈ range w, rise h i (v+k) * x (v+k) = 0 := fun k _ => by
    rw [rise, if_neg (show ¬ v + k ≤ i by omega), zero_mul]
  simp only [toeplitzApply]
  rw [sum_range_add, sum_eq_zero hz, add_zero]

lemma stencil_right (v w : ℕ) (h x : Line) (i : ℕ) :
    toeplitzApply (v+w) h x (v+i)=toeplitzApply v h x (v+i)+toeplitzApply w h (fun j => x (v+j)) i := by
  simp only [toeplitzApply]
  rw [sum_range_add]
  congr 1
  refine sum_congr rfl fun k _ => ?_
  simp only [rise, Nat.add_sub_add_left]
  split_ifs <;> first | omega | rfl

lemma stencil_congr (v : ℕ) (h : Line) {x y : Line} (H : ∀ i<v, x i=y i) :
    toeplitzApply v h x = toeplitzApply v h y := by
  funext i
  simp only [toeplitzApply]
  exact sum_congr rfl fun j hj => by rw [H j (mem_range.mp hj)]

def recoilTo (h : Line) : ℕ → Line
  | 0 => fun _ => (h 0)⁻¹
  | k+1 => fun j => if j ≤ k then recoilTo h k j
      else -(∑ i ∈ range (k+1), recoilTo h k (k-i)*h (i+1))/(h 0)

def toeplitzInv (h : Line) (j : ℕ) : ℂ := recoilTo h j j

lemma recoilTo_stable (h : Line) : ∀ k j, j ≤ k → recoilTo h k j = toeplitzInv h j := by
  intro k
  induction k with
  | zero =>
    intro j hj
    obtain rfl : j = 0 := by omega
    rfl
  | succ k ih =>
    intro j hj
    rcases Nat.lt_or_ge j (k+1) with hjk | hjk
    · simp only [recoilTo]
      rw [if_pos (show j ≤ k by omega), ih j (by omega)]
    · obtain rfl : j = k + 1 := by omega
      rfl

lemma toeplitzInv_conv (h : Line) (hh : h 0 ≠ 0) (m : ℕ) :
    ∑ k ∈ range (m+1), toeplitzInv h (m-k) * h k = if m = 0 then 1 else 0 := by
  cases m with
  | zero => simp [toeplitzInv, recoilTo, hh]
  | succ m =>
    have e : toeplitzInv h (m+1)
        = -(∑ i ∈ range (m+1), recoilTo h m (m-i) * h (i+1)) / h 0 := by
      show recoilTo h (m+1) (m+1) = _
      simp only [recoilTo, if_neg (show ¬ (m + 1 ≤ m) by omega)]
    have e2 : ∑ i ∈ range (m+1), recoilTo h m (m-i) * h (i+1)
        = ∑ i ∈ range (m+1), toeplitzInv h (m+1-(i+1)) * h (i+1) :=
      sum_congr rfl fun i _ => by
        rw [recoilTo_stable h m (m-i) (by omega), Nat.add_sub_add_right]
    rw [sum_range_succ', Nat.sub_zero, e, div_mul_cancel₀ _ hh, ← e2,
      if_neg (show m + 1 ≠ 0 by omega)]
    ring

lemma rise_inner (h : Line) (hh : h 0 ≠ 0) (v i l : ℕ) (hi : i < v) :
    ∑ j ∈ range v, rise (toeplitzInv h) i j * rise h j l = if l = i then 1 else 0 := by
  have hs : ∑ j ∈ Ico l (i+1), rise (toeplitzInv h) i j * rise h j l
      = ∑ j ∈ range v, rise (toeplitzInv h) i j * rise h j l := sum_subset
    (by intro j hj; simp only [mem_Ico, mem_range] at hj ⊢; omega)
    (by intro j _ hj; rw [mem_Ico] at hj; simp only [rise]; split_ifs <;> first | omega | simp)
  rw [← hs, sum_Ico_eq_sum_range]
  by_cases hli : l ≤ i
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hli
    rw [show l + m + 1 - l = m + 1 by omega]
    trans ∑ k ∈ range (m+1), toeplitzInv h (m-k) * h k
    · refine sum_congr rfl fun k hk => ?_
      rw [mem_range] at hk
      simp only [rise]
      rw [if_pos (show l + k ≤ l + m by omega), if_pos (show l ≤ l + k by omega),
        Nat.add_sub_add_left, Nat.add_sub_cancel_left]
    · rw [toeplitzInv_conv h hh m]
      by_cases hm : m = 0 <;> simp [hm]
  · rw [show i + 1 - l = 0 by omega, sum_range_zero, if_neg (show l ≠ i by omega)]

lemma recoil_back (v : ℕ) (h x : Line) (hh : h 0≠0) (i : ℕ) (hi : i<v) :
    toeplitzApply v (toeplitzInv h) (toeplitzApply v h x) i = x i := by
  have e : ∀ l ∈ range v, ∑ j ∈ range v, rise (toeplitzInv h) i j * (rise h j l * x l)
      = if l = i then x l else 0 := fun l _ => by
    simp only [← mul_assoc, ← sum_mul, rise_inner h hh v i l hi, ite_mul, one_mul, zero_mul]
  simp only [toeplitzApply, mul_sum]
  rw [sum_comm, sum_congr rfl e, sum_ite_eq', if_pos (mem_range.mpr hi)]

def newt (u : ℂ) : ℕ → ℕ → ℂ
  | 0, 0 => 1
  | 0, _+1 => 0
  | j+1, 0 => -(u^j * newt u j 0)
  | j+1, m+1 => newt u j m - u^j * newt u j (m+1)

theorem newt_zero_of_lt (u : ℂ) : ∀ j m : ℕ, j < m → newt u j m = 0
  | _, 0, h => absurd h (Nat.not_lt_zero _)
  | 0, _+1, _ => rfl
  | j+1, m+1, h => by
    simp only [newt, newt_zero_of_lt u j m (by omega), newt_zero_of_lt u j (m+1) (by omega),
      mul_zero, sub_zero]

theorem newt_self (u : ℂ) : ∀ j, newt u j j = 1
  | 0 => rfl
  | j+1 => by
    simp only [newt, newt_self u j, newt_zero_of_lt u j (j+1) (by omega), mul_zero, sub_zero]

lemma newt_eval (u x : ℂ) (j : ℕ) :
    ∑ m ∈ range (j+1), newt u j m * x^m = ∏ t ∈ range j, (x - u^t) := by
  induction j with
  | zero => simp [newt]
  | succ j ih =>
    have h1 : ∑ m ∈ range (j+1+1), newt u j m * x^m = ∑ m ∈ range (j+1), newt u j m * x^m := by
      rw [sum_range_succ (fun m => newt u j m * x^m) (j+1),
        newt_zero_of_lt u j (j+1) (by omega), zero_mul, add_zero]
    have A : ∑ m ∈ range (j+1), newt u j m * x^(m+1) = (∑ m ∈ range (j+1), newt u j m * x^m) * x := by
      rw [sum_mul]; exact sum_congr rfl fun m _ => by ring
    have B : ∑ m ∈ range (j+1), newt u j (m+1) * x^(m+1) + newt u j 0
        = ∑ m ∈ range (j+1), newt u j m * x^m := by
      have := sum_range_succ' (fun m => newt u j m * x^m) (j+1)
      rw [h1, pow_zero, mul_one] at this
      exact this.symm
    have C : ∑ m ∈ range (j+1), u^j * newt u j (m+1) * x^(m+1)
        = u^j * ∑ m ∈ range (j+1), newt u j (m+1) * x^(m+1) := by
      rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
    rw [prod_range_succ, ← ih, sum_range_succ' (fun m => newt u (j+1) m * x^m) (j+1)]
    simp only [newt, sub_mul, sum_sub_distrib, pow_zero, mul_one]
    rw [C]
    linear_combination A - u^j * B

lemma newt_eval' (u x : ℂ) {j n : ℕ} (hj : j < n) :
    ∑ m ∈ range n, newt u j m * x^m = ∏ t ∈ range j, (x - u^t) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_lt hj
  have hz : ∀ m ∈ range r, newt u j (j+1+m) * x^(j+1+m) = 0 := fun m _ => by
    rw [newt_zero_of_lt u j (j+1+m) (by omega), zero_mul]
  rw [show j + r + 1 = (j+1) + r by omega, sum_range_add, sum_eq_zero hz, add_zero, newt_eval]

def newtMat (n : ℕ) (u : ℂ) : RootMat n := fun m j => newt u j.val m.val

def nodeMat (n : ℕ) (u : ℂ) : RootMat n := fun i j => ∏ t ∈ range j.val, (u^i.val - u^t)

lemma node_zero (u : ℂ) {m a : ℕ} (h : m < a) : ∏ t ∈ range a, (u^m - u^t) = 0 := by
  apply prod_eq_zero (mem_range.mpr h)
  exact sub_self _

lemma lower_entry {n : ℕ} {u : ℂ} (h : Spectral.PrimRoot u n) {i : ℕ} (hi : i < n) (j : ℕ) :
    gap u i * rise (floorH u) i j * roof u j = ∏ t ∈ range j, (u^i - u^t) := by
  by_cases hji : j ≤ i
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le' hji
    have hg := gap_ne_zero u h d (by omega)
    have e1 : gap u (d + j) = gap u d * ∏ s ∈ range j, (1 - u^(d+s+1)) := by
      simp only [gap]
      rw [prod_range_add]
    have e2 : ∏ t ∈ range j, (u^(d+j) - u^t) = roof u j * ∏ s ∈ range j, (1 - u^(d+s+1)) := by
      simp only [roof]
      rw [← prod_range_reflect (fun s => 1 - u^(d+s+1)) j, ← prod_mul_distrib]
      refine prod_congr rfl fun t ht => ?_
      rw [mem_range] at ht
      have e3 : u^(d+j) = u^t * u^(d+j-t) := by
        rw [← pow_add]; congr 1; omega
      rw [show d + (j - 1 - t) + 1 = d + j - t by omega, e3]
      ring
    simp only [rise, if_pos hji, Nat.add_sub_cancel, floorH]
    rw [e2, e1, mul_right_comm (gap u d), mul_inv_cancel₀ hg, one_mul, mul_comm]
  · rw [rise, if_neg hji, mul_zero, zero_mul, node_zero u (by omega : i < j)]

lemma vandDiag_eq {n : ℕ} {u : ℂ} (h : Spectral.PrimRoot u n) {a : ℕ} (ha : a < n) :
    vandDiag u a = ∏ t ∈ range a, (u^a - u^t) := by
  rw [← lower_entry h ha a]
  simp [vandDiag, rise, floorH, gap]

lemma newt_cancel {n : ℕ} (u : ℂ) {X : RootMat n} (hX : X * newtMat n u = 0) : X = 0 := by
  ext i j
  suffices H : ∀ k (j : Fin n), j.val = k → X i j = 0 from H _ j rfl
  intro k
  refine Nat.strong_induction_on k fun k ih => ?_
  intro j hj
  have e : (X * newtMat n u) i j = 0 := by simp [hX]
  rw [Matrix.mul_apply, Fintype.sum_eq_single j] at e
  · simpa [newtMat, newt_self] using e
  · intro m hm
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hm) with h | h
    · rw [ih m.val (by omega) m rfl, zero_mul]
    · show X i m * newt u j.val m.val = 0
      rw [newt_zero_of_lt u _ _ h, mul_zero]

theorem rootVandermonde_factor (n : ℕ) (u : ℂ) (h : Spectral.PrimRoot u n) :
    rootVandermonde n u =
      vandLower n u * fade n (fun i => (vandDiag u i)⁻¹) * (vandLower n u)ᵀ := by
  have hL : vandLower n u = nodeMat n u := by
    ext i j
    simp only [vandLower, fade, mul_diagonal, diagonal_mul, front, stairs, nodeMat]
    exact lower_entry h i.isLt j.val
  have hVN : rootVandermonde n u * newtMat n u = nodeMat n u := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [rootVandermonde, newtMat, nodeMat]
    rw [Fin.sum_univ_eq_sum_range (fun m => u^(i.val*m) * newt u j.val m) n,
      ← newt_eval' u (u^i.val) j.isLt]
    exact sum_congr rfl fun m _ => by rw [← pow_mul]; ring
  have hVt : (rootVandermonde n u)ᵀ = rootVandermonde n u := by
    ext i j
    show u^(j.val*i.val) = u^(i.val*j.val)
    rw [Nat.mul_comm]
  have hsym : (nodeMat n u)ᵀ * newtMat n u = (newtMat n u)ᵀ * nodeMat n u := by
    rw [← hVN, Matrix.transpose_mul, hVt, Matrix.mul_assoc]
  have tz : ∀ m a b : ℕ, m < a ∨ b < m →
      (∏ t ∈ range a, (u^m - u^t)) * newt u b m = 0 := by
    intro m a b hm
    rcases hm with hm | hm
    · rw [node_zero u hm, zero_mul]
    · rw [newt_zero_of_lt u b m hm, mul_zero]
  have hD : (nodeMat n u)ᵀ * newtMat n u = fade n (vandDiag u) := by
    ext a b
    rcases eq_or_ne a b with rfl | hab
    · rw [fade, diagonal_apply_eq, Matrix.mul_apply, Fintype.sum_eq_single a]
      · simp only [transpose_apply, newtMat, nodeMat, front, newt_self, mul_one]
        exact (vandDiag_eq h a.isLt).symm
      · intro m hm
        have hm' : m.val ≠ a.val := fun e => hm (Fin.ext e)
        simp only [transpose_apply, newtMat, nodeMat]
        exact tz _ _ _ (by omega)
    · rw [fade, diagonal_apply_ne _ hab]
      rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with h' | h'
      · rw [hsym, Matrix.mul_apply]
        refine sum_eq_zero fun m _ => ?_
        simp only [transpose_apply, newtMat, nodeMat]
        rw [mul_comm]
        exact tz m.val b.val a.val (by omega)
      · rw [Matrix.mul_apply]
        refine sum_eq_zero fun m _ => ?_
        simp only [transpose_apply, newtMat, nodeMat]
        exact tz m.val a.val b.val (by omega)
  have hΔ : fade n (fun i => (vandDiag u i)⁻¹) * fade n (vandDiag u) = 1 := by
    rw [fade, fade, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    have u0 := h.ne_zero (by have := i.isLt; omega)
    have hr : roof u i.val ≠ 0 :=
      prod_ne_zero_iff.mpr fun t _ => neg_ne_zero.mpr (pow_ne_zero _ u0)
    exact inv_mul_cancel₀ (mul_ne_zero (gap_ne_zero u h i.val i.isLt) hr)
  have h0 := newt_cancel u (X := rootVandermonde n u
      - nodeMat n u * fade n (fun i => (vandDiag u i)⁻¹) * (nodeMat n u)ᵀ) (by
    rw [Matrix.sub_mul, hVN, Matrix.mul_assoc _ (nodeMat n u)ᵀ, hD,
      Matrix.mul_assoc (nodeMat n u) _ (fade n (vandDiag u)), hΔ, Matrix.mul_one, sub_self])
  rw [hL]
  exact sub_eq_zero.mp h0

end
end PowerSaving.Spectral
end OAI
