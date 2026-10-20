import Mathlib

/-!
# Algebraic steps of the 8-by-4 unit-distance grid reduction

Source: rohanarun/unit-distance-grid-refinement, `proof.tex` at commit
4e7b3af. All statements hold over an arbitrary field `F`. The source's
generic-grid, private-valuation and Kummer lemmas are not formalized here;
where the written proof uses them, they enter as explicit hypotheses
(`det ≠ 0`, `R ≠ 0`, the automorphism `σ` fixing data, the transcendence
degree budget).

Contents, by section of `proof.tex`:

* §1, gauge invariance (eq. `gauge`): `gauge_sysEq_iff`, `gauge_sub_ne_zero_iff`.
* §1, normalization (eq. `normalized`): `normalization`. The translation
  must be `T = U₁ - ω J r₁`; the written `T = U₁` leaves `Ũ₁ = -ω J r₁`
  (`written_translation`, `written_translation_counterexample`).
* §1, Proposition 1, surviving generic point: `surviving_point`,
  `surviving_point_sharp`, `generator_budget`, `grid_counts`.
* §1, Proposition 1, Cramer and sign change: `sysEq_iff_linear`,
  `fixed_of_unique`, `sign_flip`, `rank_two_step`.
* §2, collinear anchors (eq. `parallel`): `collinear_velocity`,
  `collinear_parallel`.
* §3, common-line determinant: `common_line_det`.
-/

namespace UnitDistanceGrid

open Matrix

section Plane

variable {F : Type*} [Field F]

/-- Dot product on `F × F`. -/
def dot (x y : F × F) : F := x.1 * y.1 + x.2 * y.2

/-- Rotation by a right angle, `J (x, y) = (-y, x)`. -/
def J (x : F × F) : F × F := (-x.2, x.1)

/-- One equation of the source system: `2 (p - r) · (H - U) = R (A - A')`. -/
def SysEq (p r H U : F × F) (R A A' : F) : Prop :=
  2 * dot (p - r) (H - U) = R * (A - A')

/-- The gauge map on one velocity `X` at position `x`: `X ↦ c (X - T - ω J x)`. -/
def gauge (c ω : F) (T x X : F × F) : F × F := c • (X - T - ω • J x)

theorem dot_J_self (x : F × F) : dot x (J x) = 0 := by
  simp only [dot, J]
  ring

/-- The gauge multiplies the residual of each equation by `c`. -/
theorem gauge_residual (c ω R A A' : F) (T p r H U : F × F) :
    2 * dot (p - r) (gauge c ω T p H - gauge c ω T r U) - R * (c * A - c * A')
      = c * (2 * dot (p - r) (H - U) - R * (A - A')) := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨r1, r2⟩ := r
  obtain ⟨h1, h2⟩ := H
  obtain ⟨u1, u2⟩ := U
  obtain ⟨t1, t2⟩ := T
  simp only [dot, gauge, J, Prod.mk_sub_mk, Prod.smul_mk, smul_eq_mul]
  ring

/-- §1, eq. (gauge): for `c ≠ 0` the gauge preserves each equation, in both directions. -/
theorem gauge_sysEq_iff {c : F} (hc : c ≠ 0) (ω R A A' : F) (T p r H U : F × F) :
    SysEq p r (gauge c ω T p H) (gauge c ω T r U) R (c * A) (c * A')
      ↔ SysEq p r H U R A A' := by
  unfold SysEq
  have key := gauge_residual c ω R A A' T p r H U
  constructor
  · intro h
    have h0 : c * (2 * dot (p - r) (H - U) - R * (A - A')) = 0 := by
      rw [← key, h, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left hc)
  · intro h
    rw [← sub_eq_zero, key, h, sub_self, mul_zero]

/-- §1, eq. (gauge): the scaling keeps `A_i - A'_ℓ ≠ 0`. -/
theorem gauge_sub_ne_zero_iff {c : F} (hc : c ≠ 0) (A A' : F) :
    c * A - c * A' ≠ 0 ↔ A - A' ≠ 0 := by
  rw [← mul_sub]
  exact ⟨fun h h' => h (by rw [h', mul_zero]), fun h => mul_ne_zero hc h⟩

/-- Rotation parameter `ω = ((U₂ - U₁) · J v) / (v · v)` with `v = r₂ - r₁`. -/
def rotOf (r₁ r₂ U₁ U₂ : F × F) : F :=
  dot (U₂ - U₁) (J (r₂ - r₁)) / dot (r₂ - r₁) (r₂ - r₁)

/-- Scale parameter `τ = ((U₂ - U₁) · v) / (v · v)` with `v = r₂ - r₁`. -/
def tauOf (r₁ r₂ U₁ U₂ : F × F) : F :=
  dot (U₂ - U₁) (r₂ - r₁) / dot (r₂ - r₁) (r₂ - r₁)

/-- Corrected translation `T = U₁ - ω J r₁`. -/
def transOf (r₁ r₂ U₁ U₂ : F × F) : F × F :=
  U₁ - rotOf r₁ r₂ U₁ U₂ • J r₁

theorem rotate_first (r₁ r₂ U₁ U₂ : F × F) :
    gauge 1 (rotOf r₁ r₂ U₁ U₂) (transOf r₁ r₂ U₁ U₂) r₁ U₁ = 0 := by
  simp only [gauge, transOf, one_smul]
  abel

theorem rotate_second (r₁ r₂ U₁ U₂ : F × F) (hv : dot (r₂ - r₁) (r₂ - r₁) ≠ 0) :
    gauge 1 (rotOf r₁ r₂ U₁ U₂) (transOf r₁ r₂ U₁ U₂) r₂ U₂
      = tauOf r₁ r₂ U₁ U₂ • (r₂ - r₁) := by
  obtain ⟨a1, a2⟩ := r₁
  obtain ⟨b1, b2⟩ := r₂
  obtain ⟨u1, u2⟩ := U₁
  obtain ⟨w1, w2⟩ := U₂
  simp only [gauge, transOf, rotOf, tauOf, dot, J, Prod.mk_sub_mk, Prod.smul_mk,
    smul_eq_mul, one_mul] at hv ⊢
  have hι := mul_inv_cancel₀ hv
  rw [Prod.mk.injEq]
  constructor
  · linear_combination (-(w1 - u1)) * hι
  · linear_combination (-(w2 - u2)) * hι

/-- §1, eq. (normalized): one gauge map sends `U₁` to `0` and `U₂` to `0` or to
`v = r₂ - r₁`, provided `v · v ≠ 0`. -/
theorem normalization (r₁ r₂ U₁ U₂ : F × F) (hv : dot (r₂ - r₁) (r₂ - r₁) ≠ 0) :
    ∃ c ω : F, ∃ T : F × F, c ≠ 0 ∧ gauge c ω T r₁ U₁ = 0 ∧
      (gauge c ω T r₂ U₂ = 0 ∨ gauge c ω T r₂ U₂ = r₂ - r₁) := by
  have h1 := rotate_first r₁ r₂ U₁ U₂
  have h2 := rotate_second r₁ r₂ U₁ U₂ hv
  have hscale : ∀ (c : F) (x X : F × F), gauge c (rotOf r₁ r₂ U₁ U₂) (transOf r₁ r₂ U₁ U₂) x X
      = c • gauge 1 (rotOf r₁ r₂ U₁ U₂) (transOf r₁ r₂ U₁ U₂) x X := by
    intro c x X
    simp only [gauge, one_smul]
  by_cases hτ : tauOf r₁ r₂ U₁ U₂ = 0
  · refine ⟨1, rotOf r₁ r₂ U₁ U₂, transOf r₁ r₂ U₁ U₂, one_ne_zero, h1, Or.inl ?_⟩
    rw [h2, hτ, zero_smul]
  · refine ⟨(tauOf r₁ r₂ U₁ U₂)⁻¹, rotOf r₁ r₂ U₁ U₂, transOf r₁ r₂ U₁ U₂,
      inv_ne_zero hτ, ?_, Or.inr ?_⟩
    · rw [hscale, h1, smul_zero]
    · rw [hscale, h2, smul_smul, inv_mul_cancel₀ hτ, one_smul]

/-- With the translation `T = U₁` as written in `proof.tex` §1, the first anchor
velocity becomes `-ω J r₁` instead of `0`. -/
theorem written_translation (ω : F) (r₁ U₁ : F × F) :
    gauge 1 ω U₁ r₁ U₁ = -(ω • J r₁) := by
  rw [gauge, one_smul, sub_self, zero_sub]

/-- A concrete instance where the written translation `T = U₁` fails:
`r₁ = (1, 0)`, `r₂ = (2, 0)`, `U₁ = 0`, `U₂ = (0, 1)` give `ω = 1` and `Ũ₁ = (0, -1)`. -/
theorem written_translation_counterexample :
    gauge (1 : ℚ) (rotOf (1, 0) (2, 0) 0 (0, 1)) 0 (1, 0) 0 ≠ 0 := by
  norm_num [gauge, rotOf, dot, J]

/-- Each equation is linear in `(H.1, H.2, A)`; these are the rows of the Cramer system. -/
theorem sysEq_iff_linear (p r H U : F × F) (R A A' : F) :
    SysEq p r H U R A A' ↔
      2 * (p - r).1 * H.1 + 2 * (p - r).2 * H.2 + -R * A
        = 2 * dot (p - r) U - R * A' := by
  unfold SysEq dot
  simp only [Prod.fst_sub, Prod.snd_sub]
  constructor
  · intro h
    linear_combination h
  · intro h
    linear_combination h

/-- §2, Leibniz step: for anchors `r_ℓ = r₁ + σ (r₂ - r₁)` and velocities `U = ∂ r`,
`U_ℓ - U₁ = σ (U₂ - U₁) + (∂σ) v`. -/
theorem collinear_velocity {k : Type*} [CommRing k] [Algebra k F] (D : Derivation k F F)
    (r₁ r₂ : F × F) (σ : F) :
    (D (r₁.1 + σ * (r₂.1 - r₁.1)), D (r₁.2 + σ * (r₂.2 - r₁.2))) - (D r₁.1, D r₁.2)
      = σ • ((D r₂.1, D r₂.2) - (D r₁.1, D r₁.2)) + D σ • (r₂ - r₁) := by
  obtain ⟨a1, a2⟩ := r₁
  obtain ⟨b1, b2⟩ := r₂
  simp only [map_add, map_sub, Derivation.leibniz, smul_eq_mul, Prod.mk_sub_mk,
    Prod.smul_mk, Prod.mk_add_mk]
  rw [Prod.mk.injEq]
  constructor
  · ring
  · ring

/-- §2, eq. (parallel): after the normalization of §1, an anchor velocity on the line
through `r₁, r₂` is `(σ τ + ∂σ) v`, a multiple of `v`. -/
theorem collinear_parallel (r₁ r₂ rℓ U₁ U₂ Uℓ : F × F) (σ dσ : F)
    (hv : dot (r₂ - r₁) (r₂ - r₁) ≠ 0)
    (hr : rℓ = r₁ + σ • (r₂ - r₁))
    (hU : Uℓ = U₁ + (σ • (U₂ - U₁) + dσ • (r₂ - r₁))) :
    gauge 1 (rotOf r₁ r₂ U₁ U₂) (transOf r₁ r₂ U₁ U₂) rℓ Uℓ
      = (σ * tauOf r₁ r₂ U₁ U₂ + dσ) • (r₂ - r₁) := by
  subst hr hU
  obtain ⟨a1, a2⟩ := r₁
  obtain ⟨b1, b2⟩ := r₂
  obtain ⟨u1, u2⟩ := U₁
  obtain ⟨w1, w2⟩ := U₂
  simp only [gauge, transOf, rotOf, tauOf, dot, J, Prod.mk_sub_mk, Prod.mk_add_mk,
    Prod.smul_mk, smul_eq_mul, one_mul] at hv ⊢
  have hι := mul_inv_cancel₀ hv
  rw [Prod.mk.injEq]
  constructor
  · linear_combination (-(σ * (w1 - u1))) * hι
  · linear_combination (-(σ * (w2 - u2))) * hι

end Plane

section Galois

variable {E : Type*} [Field E]

/-- `σ` fixes both coordinates of `x`. -/
def Fixes (σ : E →+* E) (x : E × E) : Prop := σ x.1 = x.1 ∧ σ x.2 = x.2

/-- Prop. 1, Cramer step: if `σ` fixes the matrix and right side of a system with
nonzero determinant, it fixes the solution. -/
theorem fixed_of_unique {n : Type*} [Fintype n] [DecidableEq n] (σ : E →+* E)
    (M : Matrix n n E) (b x : n → E) (hM : M.map σ = M) (hb : σ ∘ b = b)
    (hdet : M.det ≠ 0) (hx : M *ᵥ x = b) : σ ∘ x = x := by
  have hσx : M *ᵥ (σ ∘ x) = b := by
    funext i
    have h := RingHom.map_mulVec σ M x i
    rw [hM, hx] at h
    rw [← h]
    exact congrFun hb i
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  have key : ∀ y, M *ᵥ y = b → y = M⁻¹ *ᵥ b := by
    intro y hy
    rw [← hy, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M hu, Matrix.one_mulVec]
  rw [key _ hσx, key _ hx]

/-- Prop. 1, sign change: if `σ` fixes every term of an equation except `R ↦ -R`,
then `A = A'`. -/
theorem sign_flip (σ : E →+* E) (h2 : (2 : E) ≠ 0) (p r H U : E × E) (R A A' : E)
    (hp : Fixes σ p) (hr : Fixes σ r) (hH : Fixes σ H) (hU : Fixes σ U)
    (hA : σ A = A) (hA' : σ A' = A') (hR : σ R = -R) (hR0 : R ≠ 0)
    (heq : SysEq p r H U R A A') : A - A' = 0 := by
  unfold SysEq dot at heq
  have h := congrArg σ heq
  simp only [map_mul, map_add, map_sub, map_ofNat, Prod.fst_sub, Prod.snd_sub,
    hp.1, hp.2, hr.1, hr.2, hH.1, hH.2, hU.1, hU.2, hA, hA', hR] at h
  simp only [Prod.fst_sub, Prod.snd_sub] at heq
  have h3 : (2 * R) * (A - A') = 0 := by
    linear_combination h - heq
  exact (mul_eq_zero.mp h3).resolve_left (mul_ne_zero h2 hR0)

/-- Prop. 1, rank-two case: three equations with a σ-fixed Cramer system of nonzero
determinant fix `(H.1, H.2, A)`; flipping only `R₄` in the fourth equation then
forces `A = A'₄`, contradicting `A - A'₄ ≠ 0`. -/
theorem rank_two_step (σ : E →+* E) (h2 : (2 : E) ≠ 0)
    (M : Matrix (Fin 3) (Fin 3) E) (b x : Fin 3 → E)
    (hM : M.map σ = M) (hb : σ ∘ b = b) (hdet : M.det ≠ 0) (hx : M *ᵥ x = b)
    (p r₄ U₄ : E × E) (R₄ A'₄ : E)
    (hp : Fixes σ p) (hr : Fixes σ r₄) (hU : Fixes σ U₄)
    (hA' : σ A'₄ = A'₄) (hR : σ R₄ = -R₄) (hR0 : R₄ ≠ 0)
    (h4 : SysEq p r₄ (x 0, x 1) U₄ R₄ (x 2) A'₄) : x 2 - A'₄ = 0 := by
  have hfix := fixed_of_unique σ M b x hM hb hdet hx
  have hfx : ∀ i, σ (x i) = x i := fun i => congrFun hfix i
  exact sign_flip σ h2 p r₄ (x 0, x 1) U₄ R₄ (x 2) A'₄ hp hr ⟨hfx 0, hfx 1⟩ hU
    (hfx 2) hA' hR hR0 h4

/-- §3: the common-line coefficient matrix has determinant `2 (s₂ R₁ - s₁ R₂)`. -/
theorem common_line_det (s₁ s₂ R₁ R₂ : E) :
    !![2 * s₁, -R₁; 2 * s₂, -R₂].det = 2 * (s₂ * R₁ - s₁ * R₂) := by
  rw [Matrix.det_fin_two_of]
  ring

end Galois

section Counting

/-- Prop. 1, surviving point: `N` left points each of transcendence degree at most `d`
over `K`, with joint degree at least `N d - cost` and `cost < N`, include one point of
degree exactly `d`. -/
theorem surviving_point {N d cost : ℕ} (f : Fin N → ℕ) (hle : ∀ i, f i ≤ d)
    (hsum : N * d ≤ (∑ i, f i) + cost) (hcost : cost < N) : ∃ i, f i = d := by
  by_contra h
  simp only [not_exists] at h
  have hlt : ∀ i, f i + 1 ≤ d := fun i => lt_of_le_of_ne (hle i) (h i)
  have hs : ∑ i, (f i + 1) ≤ ∑ _i : Fin N, d := Finset.sum_le_sum fun i _ => hlt i
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one] at hs
  generalize N * d = M at hs hsum
  generalize (∑ i, f i) = S at hs hsum
  omega

/-- The count is sharp: with `cost = N`, all points can have degree `d - 1`. -/
theorem surviving_point_sharp (N e : ℕ) :
    ∃ f : Fin N → ℕ, (∀ i, f i ≤ e + 1) ∧ N * (e + 1) ≤ (∑ i, f i) + N ∧
      ∀ i, f i ≠ e + 1 := by
  refine ⟨fun _ => e, fun _ => Nat.le_succ e, ?_, fun _ => Nat.ne_of_lt (Nat.lt_succ_self e)⟩
  simp [mul_add_one]

/-- Eqs. (cost) and (collinear-cost): normalized anchor data need `3j - 5`
generators in general and `2j - 3` on a line. -/
theorem generator_budget (j : ℕ) (hj : 2 ≤ j) :
    2 * (j - 2) + (j - 1) = 3 * j - 5 ∧ (j - 2) + (j - 1) = 2 * j - 3 := by
  omega

/-- The three branches: `(N, j, cost) = (8, 4, 7)`, `(6, 4, 5)`, `(4, 3, 3)` all have
`cost < N`, and the edge counts are `32`, `24`, `12`. -/
theorem grid_counts :
    (2 * (4 - 2) + (4 - 1) = 7 ∧ 7 < 8 ∧ 8 * 4 = 32) ∧
    ((4 - 2) + (4 - 1) = 5 ∧ 5 < 6 ∧ 6 * 4 = 24) ∧
    ((3 - 2) + (3 - 1) = 3 ∧ 3 < 4 ∧ 4 * 3 = 12) := by
  decide

/-- The 8-by-4 grid with `d₁ ∈ {1, 2}`: some left point survives as generic. -/
theorem general_grid_survives (d : ℕ) (f : Fin 8 → ℕ) (hle : ∀ i, f i ≤ d)
    (hsum : 8 * d ≤ (∑ i, f i) + 7) : ∃ i, f i = d :=
  surviving_point f hle hsum (by norm_num)

end Counting

end UnitDistanceGrid
