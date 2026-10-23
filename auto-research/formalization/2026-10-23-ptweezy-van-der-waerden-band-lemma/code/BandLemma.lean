import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith

open scoped InnerProductSpace

/-!
# The norm-band multiplicity lemma (`lem:band`) for van der Waerden

Formalizes Lemma `lem:band` of DaysSky's research note "Two refinements of
the October 2026 OpenAI math release" (`research-note.tex`, section
"A sharper norm-band multiplicity", lines 49–63), in
`DaysSky/van-der-waerden-refinement` at commit
`54ac9715fceab938ca77d5980c36ab691765a04d` (file sha256
`700a23a04b9ac5845fd961366c02fcf781c57334bd1af28a99b41130d28172c2`).

The lemma, verbatim from the note:

> Let points on a real affine line be pairwise separated by distance at
> least one. At most two of them can have squared norms in a single
> half-open interval [m, m+1).

The released construction's multiplicity lemma gives four occurrences;
this lemma is the note's improvement to two, and it is used at four
places in the note's parameter transfers (research-note.tex lines 79,
140, 213, 275). The note's proof: use signed arclength `t` from the
nearest point of the line to the origin, so the squared norm is `t² + C`;
if three points were in the band, two parameters share a sign class, and
for `0 ≤ u < v` with `v - u ≥ 1` one gets `v² - u² = (v - u)(v + u) ≥ 1`,
contradicting two numbers in `[m, m+1)` differing by less than one.

Formalization. In a real inner product space `E`, the affine line is
`{a + t • u | t : ℝ}` with `‖u‖ = 1` and `⟪a, u⟫_ℝ = 0` — i.e. `a` is the
line's nearest point to the origin, exactly the note's parameterization.
Then `‖a + t • u‖ ^ 2 = ‖a‖ ^ 2 + t ^ 2` and
`dist (a + s • u) (a + t • u) = |s - t|`, proved below as
`norm_sq_add_smul` and `dist_add_smul`.

The headline results are:

- `VanDerWaerden.card_le_two_of_band` — the pure real core: a finite set
  of reals, pairwise at least `1` apart, has at most two members whose
  squares lie in `[m, m + 1)`.
- `VanDerWaerden.band_card_le_two` — the lemma in the note's own
  parameterization by signed arclength.
- `VanDerWaerden.points_band_card_le_two` — the lemma as stated, for a
  finite set of points of `E` lying on the affine line.

"For a finite set of points" is the formal reading of "at most two of
them": the note's own proof argues by contradiction from three points,
and that exact form is proved here as `VanDerWaerden.band_three_points`.

Scope: this file formalizes only `lem:band`. The note's affinity and
separation lemmas (which place the construction's key points on such a
line), its run lemmas, and the parameter transfers that consume
`lem:band` all remain written proofs; see the package README.
-/

namespace VanDerWaerden

/-- Two reals whose squares lie in one half-open interval of length `1`
have squares differing by less than `1`. -/
lemma abs_sq_sub_lt_one {u v m : ℝ} (hu : u ^ 2 ∈ Set.Ico m (m + 1))
    (hv : v ^ 2 ∈ Set.Ico m (m + 1)) : |u ^ 2 - v ^ 2| < 1 := by
  obtain ⟨hu0, hu1⟩ := hu
  obtain ⟨hv0, hv1⟩ := hv
  rw [abs_lt]
  constructor <;> linarith

/-- The note's key step: two parameters in one sign class — `(-∞, 0)` or
`[0, ∞)` — that are separated by at least `1` have squares differing by
at least `1`. Indeed, writing their absolute values as `u ≤ v`, the
separation gives `v - u ≥ 1`, and `v² - u² = (v - u)(v + u) ≥ 1`. -/
lemma one_le_abs_sq_sub_of_same_class {u v : ℝ} (hsep : 1 ≤ |u - v|)
    (hclass : (0 ≤ u ∧ 0 ≤ v) ∨ (u < 0 ∧ v < 0)) : 1 ≤ |u ^ 2 - v ^ 2| := by
  have hmul : |u ^ 2 - v ^ 2| = |u - v| * |u + v| := by
    rw [← abs_mul]; congr 1; ring
  have hsum : 1 ≤ |u + v| := by
    rcases hclass with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [abs_of_nonneg (add_nonneg h1 h2)]
      rcases le_total u v with h | h
      · have h' : |u - v| = v - u := by
          rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h)]
        linarith
      · have h' : |u - v| = u - v := abs_of_nonneg (sub_nonneg.mpr h)
        linarith
    · rw [abs_of_neg (by linarith : u + v < 0)]
      rcases le_total u v with h | h
      · have h' : |u - v| = v - u := by
          rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h)]
        linarith
      · have h' : |u - v| = u - v := abs_of_nonneg (sub_nonneg.mpr h)
        linarith
  calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
    _ ≤ |u - v| * |u + v| := mul_le_mul hsep hsum zero_le_one (abs_nonneg _)
    _ = |u ^ 2 - v ^ 2| := hmul.symm

/-- A separated pair in one sign class cannot both lie in the band. -/
lemma band_pair_absurd {u v m : ℝ} (hsep : 1 ≤ |u - v|)
    (hu : u ^ 2 ∈ Set.Ico m (m + 1)) (hv : v ^ 2 ∈ Set.Ico m (m + 1))
    (hclass : (0 ≤ u ∧ 0 ≤ v) ∨ (u < 0 ∧ v < 0)) : False :=
  (not_le.mpr (abs_sq_sub_lt_one hu hv)) (one_le_abs_sq_sub_of_same_class hsep hclass)

/-- Among any three reals, some two lie in one sign class: `(-∞, 0)` or
`[0, ∞)`. This is the pigeonhole step of the note's proof. -/
lemma same_class_pair {a b c : ℝ} :
    ((0 ≤ a ∧ 0 ≤ b) ∨ (a < 0 ∧ b < 0)) ∨
    ((0 ≤ a ∧ 0 ≤ c) ∨ (a < 0 ∧ c < 0)) ∨
    ((0 ≤ b ∧ 0 ≤ c) ∨ (b < 0 ∧ c < 0)) := by
  rcases le_or_gt 0 a with ha | ha <;> rcases le_or_gt 0 b with hb | hb <;>
    rcases le_or_gt 0 c with hc | hc <;>
    first
      | exact Or.inl (Or.inl ⟨ha, hb⟩)
      | exact Or.inl (Or.inr ⟨ha, hb⟩)
      | exact Or.inr (Or.inl (Or.inl ⟨ha, hc⟩))
      | exact Or.inr (Or.inl (Or.inr ⟨ha, hc⟩))
      | exact Or.inr (Or.inr (Or.inl ⟨hb, hc⟩))
      | exact Or.inr (Or.inr (Or.inr ⟨hb, hc⟩))

/-- Any finset with more than two elements contains three distinct ones. -/
lemma exists_three_of_two_lt_card {α : Type*} {s : Finset α} (h : 2 < s.card) :
    ∃ x ∈ s, ∃ y ∈ s, ∃ z ∈ s, x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  classical
  obtain ⟨x, hx⟩ : s.Nonempty := Finset.card_pos.mp (by omega)
  have herase : (s.erase x).card = s.card - 1 := Finset.card_erase_of_mem hx
  obtain ⟨y, hy, z, hz, hyz⟩ :=
    Finset.one_lt_card.mp (show 1 < (s.erase x).card by omega)
  obtain ⟨hyx, hyS⟩ := Finset.mem_erase.mp hy
  obtain ⟨hzx, hzS⟩ := Finset.mem_erase.mp hz
  exact ⟨x, hx, y, hyS, z, hzS, Ne.symm hyx, Ne.symm hzx, hyz⟩

/-- The pure real core of `lem:band`: reals pairwise at least `1` apart
have at most two squares in a single half-open interval `[m, m + 1)`. -/
theorem card_le_two_of_band {s : Finset ℝ} {m : ℝ}
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → 1 ≤ |x - y|)
    (hmem : ∀ x ∈ s, x ^ 2 ∈ Set.Ico m (m + 1)) :
    s.card ≤ 2 := by
  by_contra h
  obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ :=
    exists_three_of_two_lt_card (not_le.mp h)
  rcases same_class_pair (a := x) (b := y) (c := z) with hp | hp | hp
  · exact band_pair_absurd (hsep x hx y hy hxy) (hmem x hx) (hmem y hy) hp
  · exact band_pair_absurd (hsep x hx z hz hxz) (hmem x hx) (hmem z hz) hp
  · exact band_pair_absurd (hsep y hy z hz hyz) (hmem y hy) (hmem z hz) hp

/-- Pythagoras for the line's parameterization: with `‖u‖ = 1` and `a`
orthogonal to `u`, the squared norm of `a + t • u` is `‖a‖ ^ 2 + t ^ 2`.
This is the note's "the squared norm is `t² + C`". -/
theorem norm_sq_add_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {a u : E} (hu : ‖u‖ = 1) (hau : ⟪a, u⟫_ℝ = 0) (t : ℝ) :
    ‖a + t • u‖ ^ 2 = ‖a‖ ^ 2 + t ^ 2 := by
  rw [norm_add_sq_real, real_inner_smul_right, hau]
  simp [norm_smul, hu, Real.norm_eq_abs, sq_abs]

/-- Distance along the line is arclength distance: with `‖u‖ = 1`,
`dist (a + t • u) (a + s • u) = |t - s|`. -/
theorem dist_add_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {a u : E} (hu : ‖u‖ = 1) (s t : ℝ) :
    dist (a + t • u) (a + s • u) = |t - s| := by
  have h : a + t • u - (a + s • u) = (t - s) • u := by
    rw [sub_smul]; abel
  rw [dist_eq_norm, h, norm_smul, hu, mul_one, Real.norm_eq_abs]

/-- Shifting a band membership by the constant `C = ‖a‖ ^ 2`. -/
lemma sq_mem_Ico_sub {t C m : ℝ} (h : C + t ^ 2 ∈ Set.Ico m (m + 1)) :
    t ^ 2 ∈ Set.Ico (m - C) (m - C + 1) := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨by linarith, by linarith⟩

/-- The note's proof in its exact form: there do not exist three distinct
points of the affine line `{a + t • u}`, pairwise at distance at least
`1`, whose squared norms all lie in one band `[m, m + 1)`. -/
theorem band_three_points {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {a u : E} (hu : ‖u‖ = 1) (hau : ⟪a, u⟫_ℝ = 0) {m : ℝ}
    {x y z : E} (hx : ∃ t : ℝ, x = a + t • u) (hy : ∃ t : ℝ, y = a + t • u)
    (hz : ∃ t : ℝ, z = a + t • u)
    (hxy : 1 ≤ dist x y) (hxz : 1 ≤ dist x z) (hyz : 1 ≤ dist y z)
    (hxm : ‖x‖ ^ 2 ∈ Set.Ico m (m + 1)) (hym : ‖y‖ ^ 2 ∈ Set.Ico m (m + 1))
    (hzm : ‖z‖ ^ 2 ∈ Set.Ico m (m + 1)) : False := by
  obtain ⟨tx, rfl⟩ := hx
  obtain ⟨ty, rfl⟩ := hy
  obtain ⟨tz, rfl⟩ := hz
  rw [dist_add_smul hu] at hxy hxz hyz
  rw [norm_sq_add_smul hu hau] at hxm hym hzm
  have htx : tx ^ 2 ∈ Set.Ico (m - ‖a‖ ^ 2) (m - ‖a‖ ^ 2 + 1) := sq_mem_Ico_sub hxm
  have hty : ty ^ 2 ∈ Set.Ico (m - ‖a‖ ^ 2) (m - ‖a‖ ^ 2 + 1) := sq_mem_Ico_sub hym
  have htz : tz ^ 2 ∈ Set.Ico (m - ‖a‖ ^ 2) (m - ‖a‖ ^ 2 + 1) := sq_mem_Ico_sub hzm
  rcases same_class_pair (a := tx) (b := ty) (c := tz) with hp | hp | hp
  · exact band_pair_absurd hxy htx hty hp
  · exact band_pair_absurd hxz htx htz hp
  · exact band_pair_absurd hyz hty htz hp

/-- `lem:band` in the note's parameterization: among finitely many
signed arclengths, pairwise at least `1` apart, at most two points of
the line have squared norm in `[m, m + 1)`. -/
theorem band_card_le_two {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {a u : E} (hu : ‖u‖ = 1) (hau : ⟪a, u⟫_ℝ = 0)
    (s : Finset ℝ) (m : ℝ)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → 1 ≤ |x - y|) :
    (s.filter fun t => ‖a + t • u‖ ^ 2 ∈ Set.Ico m (m + 1)).card ≤ 2 := by
  refine card_le_two_of_band (m := m - ‖a‖ ^ 2) ?_ ?_
  · intro x hx y hy hxy
    exact hsep x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy
  · intro x hx
    have hxband := (Finset.mem_filter.mp hx).2
    rw [norm_sq_add_smul hu hau] at hxband
    exact sq_mem_Ico_sub hxband

/-- `lem:band` as stated in the note: points of the real affine line
`{a + t • u}` (with `‖u‖ = 1` and `a` the line's nearest point to the
origin, i.e. `⟪a, u⟫_ℝ = 0`), pairwise separated by distance at least
one — at most two of them have squared norms in a single half-open
interval `[m, m + 1)`. -/
theorem points_band_card_le_two {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {a u : E} (hu : ‖u‖ = 1) (hau : ⟪a, u⟫_ℝ = 0)
    (s : Finset E) (m : ℝ)
    (hline : ∀ x ∈ s, ∃ t : ℝ, x = a + t • u)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → 1 ≤ dist x y) :
    (s.filter fun x => ‖x‖ ^ 2 ∈ Set.Ico m (m + 1)).card ≤ 2 := by
  by_contra h
  obtain ⟨x, hxF, y, hyF, z, hzF, hxy, hxz, hyz⟩ :=
    exists_three_of_two_lt_card (not_le.mp h)
  obtain ⟨hxS, hxm⟩ := Finset.mem_filter.mp hxF
  obtain ⟨hyS, hym⟩ := Finset.mem_filter.mp hyF
  obtain ⟨hzS, hzm⟩ := Finset.mem_filter.mp hzF
  exact band_three_points hu hau (hline x hxS) (hline y hyS) (hline z hzS)
    (hsep x hxS y hyS hxy) (hsep x hxS z hzS hxz) (hsep y hyS z hzS hyz)
    hxm hym hzm

#print axioms card_le_two_of_band
#print axioms band_three_points
#print axioms band_card_le_two
#print axioms points_band_card_le_two

end VanDerWaerden
