/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Batch.Tiling
public import Mathlib.Data.ZMod.Basic

/-!
# The digit-lifted sources and the count identity

The sources of a batch are 0/1 matrices with at most one entry 1 in each inner block of `p` columns.
A source row `ρ = (i K₀² + u) N₀ + o` belongs to the product `u` (`rowU`) and is its row
`R = i N₀ + o` (`rowR`).  The inner index `κ = cl p + r` is the vertex `cl` of the middle block and
the residue `r`.  The entry is 1 iff the triple `(u, R, cl)` is valid (`ok`) and `r` is the residue
`f u R cl`.

* `sum_srcVal`: the inner product of a row of the left source and a column of the right source of the
  same product counts the `cl` where both are valid and the two residues agree.
* `lift_count`: with the residues of the digit construction (Lemma 4.1 of the note), the residues
  agree iff `p` divides the triangle sum.
-/

@[expose] public section

open Finset

namespace ThreeSumApsp.Batch

/-- The product of a source row. -/
def rowU (KK N0 ρ : ℕ) : ℕ := ρ / N0 % KK

/-- The row of its product that a source row is. -/
def rowR (KK N0 ρ : ℕ) : ℕ := ρ / N0 / KK * N0 + ρ % N0

/-- The source row of the row `R` of the product `u`. -/
def srcOf (KK N0 u R : ℕ) : ℕ := (R / N0 * KK + u) * N0 + R % N0

theorem rowU_srcOf {KK N0 u R : ℕ} (hu : u < KK) (hN0 : 0 < N0) : rowU KK N0 (srcOf KK N0 u R) = u := by
  unfold rowU srcOf
  rw [Nat.add_comm _ (R % N0), Nat.add_mul_div_right _ _ hN0, Nat.div_eq_of_lt (Nat.mod_lt _ hN0),
    Nat.zero_add, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hu]

theorem rowR_srcOf {KK N0 u R : ℕ} (hu : u < KK) (hN0 : 0 < N0) : rowR KK N0 (srcOf KK N0 u R) = R := by
  unfold rowR srcOf
  have h1 : ((R / N0 * KK + u) * N0 + R % N0) / N0 = R / N0 * KK + u := by
    rw [Nat.add_comm _ (R % N0), Nat.add_mul_div_right _ _ hN0, Nat.div_eq_of_lt (Nat.mod_lt _ hN0),
      Nat.zero_add]
  have hKK : 0 < KK := by omega
  have h2 : (R / N0 * KK + u) / KK = R / N0 := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hKK, Nat.div_eq_of_lt hu, Nat.zero_add]
  have h3 : ((R / N0 * KK + u) * N0 + R % N0) % N0 = R % N0 := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_mod]
  rw [h1, h2, h3, Nat.div_add_mod']

theorem srcOf_lt {KK N0 u R nb : ℕ} (hu : u < KK) (hR : R < nb * N0) :
    srcOf KK N0 u R < KK * (nb * N0) := by
  unfold srcOf
  have hN0 : 0 < N0 := by
    rcases Nat.eq_zero_or_pos N0 with h | h
    · simp [h] at hR
    · exact h
  have hi : R / N0 < nb := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
  have h1 : R / N0 * KK + u < nb * KK := by nlinarith
  have h2 := Nat.mod_lt R hN0
  calc (R / N0 * KK + u) * N0 + R % N0 < (R / N0 * KK + u) * N0 + N0 := by omega
    _ = (R / N0 * KK + u + 1) * N0 := by ring
    _ ≤ (nb * KK) * N0 := Nat.mul_le_mul_right _ h1
    _ = KK * (nb * N0) := by ring

/-- The entry `(ρ, κ)` of a source. -/
def srcVal (s p KK N0 : ℕ) (ok : ℕ → ℕ → ℕ → Bool) (f : ℕ → ℕ → ℕ → ℕ) (ρ κ : ℕ) : ℤ :=
  if κ / p < s ∧ ok (rowU KK N0 ρ) (rowR KK N0 ρ) (κ / p) = true ∧
      κ % p = f (rowU KK N0 ρ) (rowR KK N0 ρ) (κ / p) then 1 else 0

/-- One inner block of `p` columns. -/
theorem sum_block {p : ℕ} (hp : 0 < p) (a b : ℕ) (P Q : Prop) [Decidable P] [Decidable Q]
    (ha : a < p) (hb : b < p) :
    ∑ r ∈ range p, ((if P ∧ r = a then (1 : ℤ) else 0) * (if Q ∧ r = b then 1 else 0))
      = if P ∧ Q ∧ a = b then 1 else 0 := by
  have : ∀ r, ((if P ∧ r = a then (1 : ℤ) else 0) * (if Q ∧ r = b then 1 else 0))
      = if r = a then (if P ∧ Q ∧ a = b then 1 else 0) else 0 := by
    intro r
    by_cases hr : r = a
    · subst hr; by_cases hP : P <;> by_cases hQ : Q <;> by_cases hab : r = b <;> simp [hP, hQ, hab]
    · simp [hr]
  rw [sum_congr rfl fun r _ => this r, sum_ite_eq' (range p) a, if_pos (mem_range.2 ha)]

theorem sum_srcVal {s p KK N0 D : ℕ} (hp : 0 < p) (hsD : s * p ≤ D) {okX okY : ℕ → ℕ → ℕ → Bool}
    {fX fY : ℕ → ℕ → ℕ → ℕ} (hfX : ∀ u R cl, fX u R cl < p) (hfY : ∀ u R cl, fY u R cl < p)
    (ρ₁ ρ₂ : ℕ) (hu : rowU KK N0 ρ₁ = rowU KK N0 ρ₂) :
    ∑ κ ∈ range D, srcVal s p KK N0 okX fX ρ₁ κ * srcVal s p KK N0 okY fY ρ₂ κ
      = (((range s).filter fun cl => okX (rowU KK N0 ρ₁) (rowR KK N0 ρ₁) cl = true ∧
          okY (rowU KK N0 ρ₁) (rowR KK N0 ρ₂) cl = true ∧
          fX (rowU KK N0 ρ₁) (rowR KK N0 ρ₁) cl = fY (rowU KK N0 ρ₁) (rowR KK N0 ρ₂) cl).card : ℤ) := by
  set u := rowU KK N0 ρ₁
  set R₁ := rowR KK N0 ρ₁
  set R₂ := rowR KK N0 ρ₂
  -- the columns from s p on are zero
  have hzero : ∀ κ ∈ range D, κ ∉ range (s * p) →
      srcVal s p KK N0 okX fX ρ₁ κ * srcVal s p KK N0 okY fY ρ₂ κ = 0 := by
    intro κ _ hκ
    have : s ≤ κ / p := (Nat.le_div_iff_mul_le hp).2 (by simp at hκ; omega)
    simp [srcVal, show ¬ κ / p < s by omega]
  rw [← sum_subset (range_subset_range.2 hsD) hzero]
  -- by induction over the blocks
  have key : ∀ s' ≤ s, ∑ κ ∈ range (s' * p),
      srcVal s p KK N0 okX fX ρ₁ κ * srcVal s p KK N0 okY fY ρ₂ κ
      = (((range s').filter fun cl => okX u R₁ cl = true ∧ okY u R₂ cl = true ∧
          fX u R₁ cl = fY u R₂ cl).card : ℤ) := by
    intro s' hs'
    induction s' with
    | zero => simp
    | succ s' ih =>
      rw [Nat.succ_mul, sum_range_add, ih (by omega), range_add_one, filter_insert]
      have hblock : ∑ r ∈ range p, srcVal s p KK N0 okX fX ρ₁ (s' * p + r)
          * srcVal s p KK N0 okY fY ρ₂ (s' * p + r)
          = if okX u R₁ s' = true ∧ okY u R₂ s' = true ∧ fX u R₁ s' = fY u R₂ s' then 1 else 0 := by
        have hdiv : ∀ r < p, (s' * p + r) / p = s' := fun r hr => by
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hr, Nat.zero_add]
        have hmod : ∀ r < p, (s' * p + r) % p = r := fun r hr => by
          rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
        rw [← sum_block hp (fX u R₁ s') (fY u R₂ s') (okX u R₁ s' = true) (okY u R₂ s' = true)
          (hfX _ _ _) (hfY _ _ _)]
        refine sum_congr rfl fun r hr => ?_
        have hr' := mem_range.1 hr
        simp only [srcVal, hdiv r hr', hmod r hr', ← hu, show s' < s by omega, true_and]
        rfl
      rw [hblock]
      split_ifs with h
      · rw [card_insert_of_notMem (by simp)]; push_cast; ring
      · simp
  rw [key s le_rfl, hu]

/-! ## The residues of the digit construction -/

/-- The residue of an integer, as a natural number. -/
def resid (p : ℕ) (w : ℤ) : ℕ := (w % (p : ℤ)).toNat

theorem resid_lt {p : ℕ} (hp : 0 < p) (w : ℤ) : resid p w < p := by
  unfold resid
  have h0 := Int.emod_nonneg w (by exact_mod_cast hp.ne' : (p : ℤ) ≠ 0)
  have h1 := Int.emod_lt_of_pos w (by exact_mod_cast hp : (0 : ℤ) < p)
  omega

theorem cast_resid {p : ℕ} (hp : 0 < p) (w : ℤ) : ((resid p w : ℕ) : ZMod p) = (w : ZMod p) := by
  unfold resid
  have h0 : 0 ≤ w % (p : ℤ) := Int.emod_nonneg w (by exact_mod_cast hp.ne')
  have h1 : (((w % (p : ℤ)).toNat : ℕ) : ℤ) = w % (p : ℤ) := Int.toNat_of_nonneg h0
  calc (((w % (p : ℤ)).toNat : ℕ) : ZMod p) = ((((w % (p : ℤ)).toNat : ℕ) : ℤ) : ZMod p) :=
        (Int.cast_natCast _).symm
    _ = ((w % (p : ℤ) : ℤ) : ZMod p) := by rw [h1]
    _ = (w : ZMod p) := ZMod.intCast_mod w p

/-! ## The sources of the digit construction -/

section Digits

variable (n s p k T KK bt : ℕ) (AB BC AC : List ℤ)

/-- The product `u` of the batch `bt` is the product of the middle block `bt K₀² + u`. -/
abbrev jOf (u : ℕ) : ℕ := bt * KK + u

/-- The left source: row `R = a k + l` of the product of the middle block `j`, vertex `cl` of the
block; the residue is `(w(a, c) - l) mod p`. -/
def okX (u R cl : ℕ) : Bool := decide (jOf KK bt u < T ∧ R / k < n ∧ jOf KK bt u * s + cl < n)

def fX (u R cl : ℕ) : ℕ :=
  (resid p (AC.getD (R / k * n + (jOf KK bt u * s + cl)) 0) + (p - R % k) % p) % p

/-- The right source: column `C = b k + h`; the residue is `(h k - w(b, c)) mod p`. -/
def okY (u C cl : ℕ) : Bool := decide (jOf KK bt u < T ∧ C / k < n ∧ jOf KK bt u * s + cl < n)

def fY (u C cl : ℕ) : ℕ :=
  (C % k * k % p + resid p (-BC.getD (C / k * n + (jOf KK bt u * s + cl)) 0)) % p

end Digits

/-- **The residues agree iff `p` divides the triangle sum.** -/
theorem fX_eq_fY_iff {n s p k KK bt : ℕ} {AB BC AC : List ℤ} (hp : 0 < p) (hk : p ≤ k * k)
    (hkp : k ≤ p) {u a b cl : ℕ} (ha : a < n) (hb : b < n) :
    let z := resid p (-AB.getD (a * n + b) 0)
    fX n s p k KK bt AC u (a * k + z % k) cl = fY n s p k KK bt BC u (b * k + z / k) cl ↔
      (p : ℤ) ∣ AB.getD (a * n + b) 0 + BC.getD (b * n + (jOf KK bt u * s + cl)) 0
        + AC.getD (a * n + (jOf KK bt u * s + cl)) 0 := by
  intro z
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · simp [h] at hk; omega
    · exact h
  have hz : z < p := resid_lt hp _
  have hzk : z / k < k := Nat.div_lt_of_lt_mul (by nlinarith)
  have hR1 : (a * k + z % k) / k = a := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hk0, Nat.div_eq_of_lt (Nat.mod_lt _ hk0), Nat.zero_add]
  have hR2 : (a * k + z % k) % k = z % k := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_mod]
  have hC1 : (b * k + z / k) / k = b := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hk0, Nat.div_eq_of_lt hzk, Nat.zero_add]
  have hC2 : (b * k + z / k) % k = z / k := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hzk]
  have hlp : z % k ≤ p := (Nat.mod_lt _ hk0).le.trans hkp
  unfold fX fY
  rw [hR1, hR2, hC1, hC2, ← ZMod.natCast_eq_natCast_iff']
  set c := jOf KK bt u * s + cl
  have hzc : ((z : ℕ) : ZMod p) = ((-AB.getD (a * n + b) 0 : ℤ) : ZMod p) := cast_resid hp _
  have hzd : ((z : ℕ) : ZMod p) = ((z / k * k : ℕ) : ZMod p) + ((z % k : ℕ) : ZMod p) := by
    rw [← Nat.cast_add, Nat.div_add_mod']
  push_cast [cast_resid hp] at hzc hzd ⊢
  simp only [ZMod.natCast_mod]
  push_cast [Nat.cast_sub hlp, ZMod.natCast_self] at hzc hzd ⊢
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  constructor
  · intro h; linear_combination h + hzc - hzd
  · intro h; linear_combination h - hzc + hzd

/-- **The count.** The valid `cl` with agreeing residues are the vertices `c = j s + cl` of the
middle block `j` with `p` dividing the triangle sum. -/
theorem card_lift {n s p k T KK bt : ℕ} {AB BC AC : List ℤ} (hp : 0 < p) (hk : p ≤ k * k)
    (hkp : k ≤ p) {u a b : ℕ} (ha : a < n) (hb : b < n) (hj : jOf KK bt u < T) :
    let z := resid p (-AB.getD (a * n + b) 0)
    ((range s).filter fun cl => okX n s k T KK bt u (a * k + z % k) cl = true ∧
        okY n s k T KK bt u (b * k + z / k) cl = true ∧
        fX n s p k KK bt AC u (a * k + z % k) cl = fY n s p k KK bt BC u (b * k + z / k) cl).card
      = ((range n).filter fun c => (jOf KK bt u * s ≤ c ∧ c < (jOf KK bt u + 1) * s ∧ c < n) ∧
          (p : ℤ) ∣ AB.getD (a * n + b) 0 + BC.getD (b * n + c) 0 + AC.getD (a * n + c) 0).card := by
  intro z
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · simp [h] at hk; omega
    · exact h
  have hz : z < p := resid_lt hp _
  have hzk : z / k < k := Nat.div_lt_of_lt_mul (by nlinarith)
  have hR1 : (a * k + z % k) / k = a := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hk0, Nat.div_eq_of_lt (Nat.mod_lt _ hk0), Nat.zero_add]
  have hC1 : (b * k + z / k) / k = b := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hk0, Nat.div_eq_of_lt hzk, Nat.zero_add]
  have key : ∀ cl, fX n s p k KK bt AC u (a * k + z % k) cl = fY n s p k KK bt BC u (b * k + z / k) cl ↔
      (p : ℤ) ∣ AB.getD (a * n + b) 0 + BC.getD (b * n + (jOf KK bt u * s + cl)) 0
        + AC.getD (a * n + (jOf KK bt u * s + cl)) 0 := fun cl => fX_eq_fY_iff hp hk hkp ha hb
  simp only [okX, okY, hR1, hC1, decide_eq_true_eq]
  generalize jOf KK bt u = j at hj key ⊢
  rw [← card_image_of_injective _ (add_right_injective (j * s))]
  congr 1
  ext c
  simp only [mem_image, mem_filter, mem_range]
  have hjs : (j + 1) * s = j * s + s := by ring
  constructor
  · rintro ⟨cl, ⟨hcl, ⟨_, _, hc⟩, _, hfe⟩, rfl⟩
    exact ⟨hc, ⟨by omega, by omega, hc⟩, (key cl).1 hfe⟩
  · rintro ⟨hc, ⟨h1, h2, _⟩, hdvd⟩
    refine ⟨c - j * s, ⟨by omega, ⟨hj, ha, by omega⟩, ⟨hj, hb, by omega⟩, ?_⟩, by omega⟩
    refine (key _).2 ?_
    rwa [show j * s + (c - j * s) = c by omega]

/-! ## The virtual positions of a query -/

/-- The virtual position of the row `R` of the slot row `g`. -/
def virt (K0 N0 g R : ℕ) : ℕ := R / N0 * (K0 * N0) + g * N0 + R % N0

theorem virt_parts {K0 N0 g R : ℕ} (hg : g < K0) (hN0 : 0 < N0) :
    virt K0 N0 g R / (K0 * N0) = R / N0 ∧ virt K0 N0 g R / N0 % K0 = g ∧
      virt K0 N0 g R % N0 = R % N0 := by
  have hr := Nat.mod_lt R hN0
  have hK : 0 < K0 * N0 := Nat.mul_pos (by omega) hN0
  have hlow : g * N0 + R % N0 < K0 * N0 := by nlinarith
  unfold virt
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.add_assoc, Nat.add_comm, Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt hlow, Nat.zero_add]
  · have : (R / N0 * (K0 * N0) + g * N0 + R % N0) / N0 = R / N0 * K0 + g := by
      rw [show R / N0 * (K0 * N0) + g * N0 + R % N0 = R % N0 + (R / N0 * K0 + g) * N0 by ring,
        Nat.add_mul_div_right _ _ hN0, Nat.div_eq_of_lt hr, Nat.zero_add]
    rw [this, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hg]
  · rw [show R / N0 * (K0 * N0) + g * N0 + R % N0 = R % N0 + (R / N0 * K0 + g) * N0 by ring,
      Nat.add_mul_mod_self_right, Nat.mod_mod]

theorem srcRow_virt {L m : ℕ} (lay : Layout L m) {g h R C : ℕ} (hg : g < K0 L m) (hh : h < K0 L m) :
    srcRow lay (virt (K0 L m) (N0 L m) g R) (virt (K0 L m) (N0 L m) h C)
        = srcOf (K0 L m * K0 L m) (N0 L m) (g * K0 L m + h) R ∧
      srcCol lay (virt (K0 L m) (N0 L m) g R) (virt (K0 L m) (N0 L m) h C)
        = srcOf (K0 L m * K0 L m) (N0 L m) (g * K0 L m + h) C := by
  obtain ⟨hI1, hI2, hI3⟩ := virt_parts (R := R) hg (N0_pos L m)
  obtain ⟨hJ1, hJ2, hJ3⟩ := virt_parts (R := C) hh (N0_pos L m)
  unfold srcRow srcCol srcBlock bandOf blockOf bandSize srcOf
  simp only [hI1, hI2, hI3, hJ1, hJ2, hJ3]
  constructor <;> ring

end ThreeSumApsp.Batch
