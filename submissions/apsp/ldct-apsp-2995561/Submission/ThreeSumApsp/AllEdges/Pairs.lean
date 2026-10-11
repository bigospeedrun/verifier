/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.AllEdges.PairsSpec
public import Submission.ThreeSumApsp.AllEdges.Task
public import Submission.ThreeSumApsp.Lang.Lib.Copy
public import Submission.ThreeSumApsp.Programs.Sec3.Theorem21b.MinPlus.Tasks
public import Submission.ThreeSumApsp.Programs.Sec3.Theorem21b.NegativeTriangle.Host

/-!
# All pairs from all-edges Exact Triangle, as a host

pa(n, U, x, y, v, out, fr) finds, for all pairs `(i, j)` at once, whether some `k` has
`X[i,k] + Y[k,j] < V[i,j]`.  It is the host nt of Negative Triangle with all-edges Exact Triangle in
the place of Exact Triangle: the weights are `−V`, `Yᵀ` and `X`, a triangle on the edge `(i, j)` is
negative exactly if the pair `(i, j)` has the property, and at each of the `2L` questions the flags
of the answer are or-ed into out (`isHost_pa`).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.Spec

/-! ## The text -/

namespace PaHost

abbrev Verts : ℕ := 0
abbrev Bound : ℕ := 1
abbrev MatX : ℕ := 2
abbrev MatY : ℕ := 3
abbrev MatV : ℕ := 4
abbrev Out : ℕ := 5
abbrev PreAB : ℕ := 6
abbrev Cells : ℕ := 7
abbrev Power : ℕ := 8
abbrev Levels : ℕ := 9
abbrev Round : ℕ := 10
abbrev Res : ℕ := 11
abbrev Bound6 : ℕ := 12
abbrev PreBC : ℕ := 13
abbrev PreAC : ℕ := 14
abbrev RestAB : ℕ := 15
abbrev RestBC : ℕ := 16
abbrev RestAC : ℕ := 17
abbrev Third : ℕ := 18
abbrev Flags : ℕ := 19
abbrev SolverFree : ℕ := 20
abbrev Cells3 : ℕ := 21

end PaHost

open PaHost

/-- The beginning of pa: sizes and addresses. -/
def paInit : Stmt :=
  .set Cells (v Verts *' v Verts) ;;
  .set Bound6 (k 6 *' v Bound) ;;
  .set PreBC (v PreAB +' v Cells) ;;
  .set PreAC (v PreBC +' v Cells) ;;
  .set RestAB (v PreAC +' v Cells) ;;
  .set RestBC (v RestAB +' v Cells) ;;
  .set RestAC (v RestBC +' v Cells) ;;
  .set Third (v RestAC +' v Cells) ;;
  .set Flags (v Third +' v Cells) ;;
  .set SolverFree (v Flags +' v Cells) ;;
  .set Cells3 (k 3 *' v Cells) ;;
  .set Power (k 1) ;;
  .set Levels (k 0)

/-- The number of levels L and the power 2^L, by doubling. -/
def paPow : Stmt :=
  .while (v Power ≤' v Bound6) (
    .set Power (k 2 *' v Power) ;;
    .set Levels (v Levels +' k 1))

/-- The arrays r and q at the top level, and zeros in out. -/
def paFill (pAff pTr pFill : ℕ) : Stmt :=
  .call pAff [v Cells, v MatV, k 0 -' k 2, k 2 *' v Bound, v RestAB] Res ;;
  .call pTr [v Verts, v MatY, v Third] Res ;;
  .call pAff [v Cells, v Third, k 2, k 2 *' v Bound, v RestBC] Res ;;
  .call pAff [v Cells, v MatX, k 0 -' k 2, k 4 *' v Bound, v RestAC] Res ;;
  .call pAff [v Cells3, v RestAB, k 0, k 0, v PreAB] Res ;;
  .call pFill [v Out, v Cells, k 0] Res

/-- One question to the solver of all-edges Exact Triangle, and the or of its flags into out. -/
def paProbe (pAE pAff pOr e : ℕ) : Stmt :=
  .call pAff [v Cells, v PreAC, k 0 -' k 1, k e, v Third] Res ;;
  .call pAE [v Verts, v Bound6, v PreAB, v PreBC, v Third, v Flags, v SolverFree] Res ;;
  .call pOr [v Cells, v Out, v Flags] Res

/-- One round: the next level, and its two questions. -/
def paRound (pAE pAff pDown pOr : ℕ) : Stmt :=
  .call pDown [v Cells3, v PreAB, v RestAB, v Power] Res ;;
  paProbe pAE pAff pOr 2 ;;
  paProbe pAE pAff pOr 3

/-- pa(n, U, x, y, v, out, fr). -/
def paBody (pAE pAff pDown pTr pFill pOr : ℕ) : Stmt :=
  paInit ;; paPow ;; paFill pAff pTr pFill ;;
    .for Round (v Levels) (paRound pAE pAff pDown pOr) ;; .set 0 (k 0)

/-- The time of pa, if the solver of all-edges Exact Triangle takes T n U steps. -/
def paTime (T : ℕ → ℕ → ℕ) (n U : ℕ) : ℕ :=
  250 * (n * n) + 400 + ntLevels U * (250 * (n * n) + 200 + 2 * T n (6 * U))

/-- The need of pa, if the solver needs r n U. -/
def paNeed (r : ℕ → ℕ → Need) (n U : ℕ) : Need where
  word := 24 * U + 8 + (r n (6 * U)).word
  cells := 8 * (n * n) + (r n (6 * U)).cells
  depth := (r n (6 * U)).depth + 2

theorem lt_two_pow_ntLevels' (U : ℕ) : 6 * U < 2 ^ ntLevels U :=
  Nat.lt_pow_succ_log_self (by norm_num) _

theorem two_pow_ntLevels_le' {U : ℕ} (hU : 1 ≤ U) : 2 ^ ntLevels U ≤ 12 * U := by
  have := Nat.pow_log_le_self 2 (show 6 * U ≠ 0 by omega)
  rw [ntLevels, pow_succ]
  omega

/-! ## The local variables and the hypotheses -/

namespace PaHost

/-- The locals of pa after its beginning. -/
abbrev locals (q : PairsInst) (fr : ℕ) (pw lv rd res : ℤ) : List ℤ :=
  [q.n, q.U, q.x, q.y, q.v, q.out, fr, (q.n * q.n : ℕ), pw, lv, rd, res, (6 * q.U : ℕ),
    (fr + q.n * q.n : ℕ), (fr + 2 * (q.n * q.n) : ℕ), (fr + 3 * (q.n * q.n) : ℕ),
    (fr + 4 * (q.n * q.n) : ℕ), (fr + 5 * (q.n * q.n) : ℕ), (fr + 6 * (q.n * q.n) : ℕ),
    (fr + 7 * (q.n * q.n) : ℕ), (fr + 8 * (q.n * q.n) : ℕ), (3 * (q.n * q.n) : ℕ)]

/-- The program has the solver and the loops over arrays, the instance is as the task prescribes,
and the limits allow for the need of pa. -/
structure Ctx (P₀ R' : Program) (p pAff pDown pTr pRow pFill pOr : ℕ) (T : ℕ → ℕ → ℕ)
    (r : ℕ → ℕ → Need) (lim : Limits) (d : ℕ) (q : PairsInst) (μ : ℕ → ℤ) (fr : ℕ) : Prop where
  solver : Solves aeTask P₀ p T r
  aff : (P₀ ++ R')[pAff]? = some affineBody
  down : (P₀ ++ R')[pDown]? = some prefDownBody
  tr : (P₀ ++ R')[pTr]? = some (transBody pRow)
  row : (P₀ ++ R')[pRow]? = some rowBody
  fill : (P₀ ++ R')[pFill]? = some fillBody
  or : (P₀ ++ R')[pOr]? = some orBody
  pre : q.Pre μ fr
  ok : (paNeed r q.n q.U).Ok lim fr d

variable {P₀ R' : Program} {p pAff pDown pTr pRow pFill pOr : ℕ} {T : ℕ → ℕ → ℕ}
  {r : ℕ → ℕ → Need} {lim : Limits} {d : ℕ} {q : PairsInst} {μ : ℕ → ℤ} {fr : ℕ}

local notation "Cx" => Ctx P₀ R' p pAff pDown pTr pRow pFill pOr T r lim d q μ fr

/-- The arithmetic facts of the hypotheses as one conjunction. -/
theorem Ctx.places (C : Cx) :
    ((lim.space : ℤ) ≤ lim.word ∧ 24 * (q.U : ℤ) + 8 + (r q.n (6 * q.U)).word ≤ lim.word ∧
      fr + (8 * (q.n * q.n) + (r q.n (6 * q.U)).cells) ≤ lim.space ∧
      d + ((r q.n (6 * q.U)).depth + 2) ≤ lim.depth) ∧ 1 ≤ q.n * q.n ∧ q.n ≤ q.n * q.n ∧
      (q.X.length = q.n * q.n ∧ q.Y.length = q.n * q.n ∧ q.V.length = q.n * q.n) ∧
      q.x + q.n * q.n ≤ fr ∧ q.y + q.n * q.n ≤ fr ∧ q.v + q.n * q.n ≤ fr ∧
      q.out + q.n * q.n ≤ fr ∧ 1 ≤ q.U :=
  ⟨⟨C.ok.space, by exact_mod_cast C.ok.word, C.ok.cells, C.ok.depth⟩,
    Nat.mul_pos C.pre.n_pos C.pre.n_pos, Nat.le_mul_of_pos_left _ C.pre.n_pos,
    ⟨C.pre.lenX, C.pre.lenY, C.pre.lenV⟩, C.pre.belowX, C.pre.belowY, C.pre.belowV,
    C.pre.belowOut, C.pre.U_pos⟩

/-- **affine** as a procedure, for a source and a destination that lie apart, below the free pointer
of the solver. -/
theorem Ctx.affine_meets (C : Cx) {μ' : ℕ → ℤ} {l : List ℤ} {src dst : ℕ} {m c : ℤ}
    (hl : Seg μ' src l)
    (hplace : src + l.length ≤ fr + 8 * (q.n * q.n) ∧ dst + l.length ≤ fr + 8 * (q.n * q.n) ∧
      (src + l.length ≤ dst ∨ dst + l.length ≤ src))
    (hfits : ∀ w ∈ l, |m * w| ≤ lim.word ∧ |m * w + c| ≤ lim.word) :
    Meets lim (P₀ ++ R') pAff (d + 1) [l.length, src, m, c, dst] μ' (20 * l.length + 6)
      fun _ μ'' => Seg μ'' dst (affL m c l) ∧ SameOutside μ' μ'' dst l.length := by
  have hplaces := C.places
  exact Sec3.affine_meets C.aff hl C.ok.space (by omega) (by omega) hplace.2.2 hfits

/-! ## The lists -/

/-- The shifted and doubled weights `2(−V + U)`, `2(Yᵀ + U)`, `2(2U − X)`. -/
noncomputable abbrev zs (q : PairsInst) : List ℤ := negStart q.U (negL q.V) (transL q.n q.Y) q.X

theorem affL_negL (U : ℕ) (V : List ℤ) : affL 2 (2 * U) (negL V) = affL (-2) (2 * U) V := by
  simp only [affL, negL, List.map_map]
  congr 1
  funext w
  simp only [Function.comp_apply]
  ring

theorem length_zs (C : Cx) : (zs q).length = 3 * (q.n * q.n) := by
  have hp := C.places
  simp only [zs, negStart, List.length_append, length_affL, negL, transL, List.length_map,
    List.length_range]
  omega

theorem zs_range (C : Cx) :
    ∀ z ∈ zs q, 0 ≤ z ∧ z ≤ 6 * (q.U : ℤ) ∧ z < 2 ^ ntLevels q.U := by
  intro z hz
  obtain ⟨h0, h1⟩ := bounds_of_mem_negStart (absLe_negL C.pre.leV) (absLe_transL C.pre.leY)
    C.pre.leX z hz
  have h2 : ((6 * q.U : ℕ) : ℤ) < ((2 ^ ntLevels q.U : ℕ) : ℤ) := by
    exact_mod_cast lt_two_pow_ntLevels' q.U
  push_cast at h2
  exact ⟨h0, h1, by omega⟩

/-- The flags of the pairs found at the levels from ℓ₀ on. -/
def PYes (q : PairsInst) (ℓ : ℕ) (e : ℤ) (i : ℕ) : Prop :=
  ∃ c < q.n, (pairsQAB q.U ℓ q.V).getD i 0 + (pairsQBC q.n q.U ℓ q.Y).getD (i % q.n * q.n + c) 0 +
    (negThird q.U ℓ e q.X).getD (i / q.n * q.n + c) 0 = 0

/-- A question at one of the levels from ℓ₀ on has found the pair `i`. -/
def PFound (q : PairsInst) (L ℓ₀ : ℕ) (i : ℕ) : Prop :=
  ∃ ℓ, ℓ₀ ≤ ℓ ∧ ℓ < L ∧ ∃ e : ℤ, (e = 2 ∨ e = 3) ∧ PYes q ℓ e i

/-- The memory of pa at the level ℓ: the prefixes and the rests, the flags found so far in out, and
nothing else below the free pointer has changed. -/
def PaMem (q : PairsInst) (μ : ℕ → ℤ) (fr ℓ : ℕ) (A : ℕ → Prop) (μ' : ℕ → ℤ) : Prop :=
  Seg μ' fr ((zs q).map (prefQ ℓ)) ∧
    Seg μ' (fr + 3 * (q.n * q.n)) ((zs q).map (prefR (ntLevels q.U) ℓ)) ∧
    Seg μ' q.out (flagsOf (q.n * q.n) A) ∧ KeptBut μ μ' fr q.out (q.n * q.n)

/-! ## The beginning -/

/-- **The beginning of pa** sets the sizes and the addresses. -/
theorem init_spec (C : Cx) :
    Ends lim (P₀ ++ R') d paInit ⟨frame [q.n, q.U, q.x, q.y, q.v, q.out, fr], μ⟩ paInit.blockCost
      fun σ' => σ' = ⟨frame (locals q fr 1 0 0 0), μ⟩ := by
  have hplaces := C.places
  have hsquare : (0 : ℤ) ≤ (q.n : ℤ) * q.n := by positivity
  unfold paInit
  light_set (q.n * q.n : ℕ)
  light_set (6 * q.U : ℕ)
  light_set (fr + q.n * q.n : ℕ)
  light_set (fr + 2 * (q.n * q.n) : ℕ)
  light_set (fr + 3 * (q.n * q.n) : ℕ)
  light_set (fr + 4 * (q.n * q.n) : ℕ)
  light_set (fr + 5 * (q.n * q.n) : ℕ)
  light_set (fr + 6 * (q.n * q.n) : ℕ)
  light_set (fr + 7 * (q.n * q.n) : ℕ)
  light_set (fr + 8 * (q.n * q.n) : ℕ)
  light_set (3 * (q.n * q.n) : ℕ)
  light_set 1
  light_set 0
  rfl

/-- The state of the loop that doubles after i rounds. -/
def PowInv (q : PairsInst) (μ : ℕ → ℤ) (fr i : ℕ) (σ : State) : Prop :=
  σ = ⟨frame (locals q fr (2 ^ i : ℕ) i 0 0), μ⟩

/-- **The loop that doubles** computes the number L of levels and 2^L. -/
theorem pow_spec (C : Cx) :
    Ends lim (P₀ ++ R') d paPow ⟨frame (locals q fr 1 0 0 0), μ⟩ (14 * ntLevels q.U + 6)
      fun σ' => σ' = ⟨frame (locals q fr (2 ^ ntLevels q.U : ℕ) (ntLevels q.U) 0 0), μ⟩ := by
  have hplaces := C.places
  have hL := two_pow_ntLevels_le' C.pre.U_pos
  refine Ends.whileBlock (PowInv q μ fr) (ntLevels q.U) (by simp [PowInv]) ?round ?done
    (by simp; omega)
  case round =>
    rintro i _ hi rfl
    have hpow : 2 ^ (i + 1) ≤ 2 ^ ntLevels q.U := Nat.pow_le_pow_right (by norm_num) hi
    have hlt : i + 1 < 2 ^ (i + 1) := Nat.lt_two_pow_self
    rw [pow_succ'] at hpow hlt
    generalize hpw : 2 ^ i = pw at hpow hlt ⊢
    exact ⟨by light_side, by simp; omega, by light_side,
      by simp [PowInv, pow_succ', hpw, update_frame_setLocal, locals]⟩
  case done =>
    rintro _ rfl
    have hlt := lt_two_pow_ntLevels' q.U
    generalize 2 ^ ntLevels q.U = pw at hL hlt ⊢
    exact ⟨by light_side, by simp; omega, rfl⟩

/-! ## The arrays at the top level -/

/-- The three shifted and doubled matrices, one after the other, are the array r at the start. -/
theorem seg_zs (C : Cx) {μ' : ℕ → ℤ}
    (h1 : Seg μ' (fr + 3 * (q.n * q.n)) (affL 2 (2 * q.U) (negL q.V)))
    (h2 : Seg μ' (fr + 4 * (q.n * q.n)) (affL 2 (2 * q.U) (transL q.n q.Y)))
    (h3 : Seg μ' (fr + 5 * (q.n * q.n)) (affL (-2) (4 * q.U) q.X)) :
    Seg μ' (fr + 3 * (q.n * q.n)) (zs q) := by
  have hp := C.places
  rw [zs, negStart, seg_append, seg_append]
  simp only [length_affL, negL, transL, List.length_map, List.length_range, hp.2.2.2.1.2.2]
  rw [show fr + 3 * (q.n * q.n) + q.n * q.n = fr + 4 * (q.n * q.n) by omega,
    show fr + 4 * (q.n * q.n) + q.n * q.n = fr + 5 * (q.n * q.n) by omega]
  exact ⟨h1, h2, h3⟩

theorem flagsOf_false (N : ℕ) {A : ℕ → Prop} (h : ∀ i, ¬ A i) :
    flagsOf N A = List.replicate N 0 := by
  simp [flagsOf, flag_of_not (h _), List.map_const']

theorem flagsOf_congr (N : ℕ) {A B : ℕ → Prop} (h : ∀ i, A i ↔ B i) : flagsOf N A = flagsOf N B := by
  simp only [flagsOf]
  congr 1
  funext i
  exact flag_congr (h i)

/-- **The calls of fill** write the arrays r and q for the top level, and zeros to out. -/
theorem fill_spec (C : Cx) (pw lv rd res : ℤ) :
    Ends lim (P₀ ++ R') d (paFill pAff pTr pFill) ⟨frame (locals q fr pw lv rd res), μ⟩
      (200 * (q.n * q.n) + 200) fun σ' => ∃ res' μ',
        σ' = ⟨frame (locals q fr pw lv rd res'), μ'⟩ ∧
          PaMem q μ fr (ntLevels q.U) (PFound q (ntLevels q.U) (ntLevels q.U)) μ' := by
  have hpre := C.pre
  have hplaces := C.places
  have hlenZ := length_zs C
  have hZ := zs_range C
  have hW : 24 * (q.U : ℤ) + 8 ≤ lim.word := by omega
  have hfits : ∀ (l : List ℤ) (m c : ℤ), AbsLe l q.U → (m = 2 ∨ m = -2) →
      (c = 2 * q.U ∨ c = 4 * q.U) → ∀ w ∈ l, |m * w| ≤ lim.word ∧ |m * w + c| ≤ lim.word := by
    intro l m c hl hm hc w hw
    have := abs_le.1 (hl w hw)
    rcases hm with rfl | rfl <;> rcases hc with rfl | rfl <;> simp only [abs_le] <;> omega
  have lT : (transL q.n q.Y).length = q.n * q.n := by simp [transL]
  unfold paFill
  -- Res := pAff(Cells, MatV, 0 - 2, 2 * Bound, RestAB)
  refine Ends.callToThen (C.affine_meets (m := -2) (c := 2 * q.U) (dst := fr + 3 * (q.n * q.n))
    hpre.segV (by omega) (hfits _ _ _ hpre.leV (.inr rfl) (.inl rfl))) ?_
    (ha := by light_side [hpre.lenV]) (hT := by simp [hpre.lenV]; omega)
  rintro r₁ μ₁ ⟨s₁, o₁⟩
  -- Res := pTr(Verts, MatY, Third)
  refine Ends.callToThen (transpose_meets (d := d + 1) C.tr C.row (hpre.segY.keep (by
      light_keep [hpre.lenV])) hpre.lenY C.ok.space (by omega) (dst := fr + 6 * (q.n * q.n))
      (by omega) (by omega) (by omega)) ?_
    (ha := by light_side) (hT := by simp [hpre.lenV, tTranspose]; omega)
  rintro r₂ μ₂ ⟨s₂, o₂⟩
  -- Res := pAff(Cells, Third, 2, 2 * Bound, RestBC)
  refine Ends.callToThen (C.affine_meets (m := 2) (c := 2 * q.U) (dst := fr + 4 * (q.n * q.n))
    s₂ (by rw [lT]; omega) (hfits _ _ _ (absLe_transL hpre.leY) (.inl rfl) (.inl rfl))) ?_
    (ha := by light_side [lT]) (hT := by simp [hpre.lenV, tTranspose, lT]; omega)
  rintro r₃ μ₃ ⟨s₃, o₃⟩
  -- Res := pAff(Cells, MatX, 0 - 2, 4 * Bound, RestAC)
  refine Ends.callToThen (C.affine_meets (m := -2) (c := 4 * q.U) (dst := fr + 5 * (q.n * q.n))
    (hpre.segX.keep (by light_keep [hpre.lenV, lT])) (by omega)
    (hfits _ _ _ hpre.leX (.inr rfl) (.inr rfl))) ?_
    (ha := by light_side [hpre.lenX]) (hT := by simp [hpre.lenV, tTranspose, lT, hpre.lenX]; omega)
  rintro r₄ μ₄ ⟨s₄, o₄⟩
  have sZ : Seg μ₄ (fr + 3 * (q.n * q.n)) (zs q) := by
    refine seg_zs C ?_ ?_ s₄
    · rw [affL_negL]
      exact s₁.keep (by light_keep [hpre.lenV, lT])
    · exact s₃.keep (by light_keep [hpre.lenX])
  -- Res := pAff(Cells3, RestAB, 0, 0, PreAB)
  refine Ends.callToThen (C.affine_meets (m := 0) (c := 0) (dst := fr) sZ (by omega)
    fun w _ => by simp; omega) ?_ (ha := by light_side [hlenZ])
    (hT := by simp [hpre.lenV, tTranspose, lT, hpre.lenX, hlenZ]; omega)
  rintro r₅ μ₅ ⟨s₅, o₅⟩
  -- Res := pFill(Out, Cells, 0)
  refine Ends.callTo (fill_meets (d := d + 1) (x := 0) C.fill C.ok.space
    (show q.out + q.n * q.n ≤ lim.space by omega)) ?_
    (ha := by light_side) (hT := by simp [hpre.lenV, tTranspose, lT, hpre.lenX, hlenZ]; omega)
  rintro r₆ μ₆ ⟨s₆, o₆⟩
  refine ⟨r₆, μ₆, rfl, ?_, ?_, ?_, ?_⟩
  · rw [map_prefQ_start fun z hz => ⟨(hZ z hz).1, (hZ z hz).2.2⟩]
    exact s₅.keep (by light_keep [hlenZ])
  · rw [map_prefR_start fun z hz => ⟨(hZ z hz).1, (hZ z hz).2.2⟩]
    exact sZ.keep (by light_keep [hlenZ])
  · rw [flagsOf_false _ fun i ⟨ℓ, h1, h2, _⟩ => by omega]
    exact s₆
  · intro c hc
    light_keep

/-! ## One question -/

/-- The instance of all-edges Exact Triangle for the level ℓ and the exact value e, as it lies in
the arrays of pa. -/
def aeQ (q : PairsInst) (fr ℓ : ℕ) (e : ℤ) : AEInst :=
  ⟨⟨q.n, 6 * q.U, fr, fr + q.n * q.n, fr + 6 * (q.n * q.n), pairsQAB q.U ℓ q.V,
    pairsQBC q.n q.U ℓ q.Y, negThird q.U ℓ e q.X⟩, fr + 7 * (q.n * q.n)⟩

/-- The prefixes are between 0 and 6U. -/
theorem prefQ_range' (C : Cx) (ℓ : ℕ) {z : ℤ} (hz : z ∈ zs q) :
    0 ≤ prefQ ℓ z ∧ prefQ ℓ z ≤ 6 * (q.U : ℤ) := by
  obtain ⟨h0, h1, -⟩ := zs_range C z hz
  exact ⟨prefQ_nonneg h0 ℓ, (prefQ_le h0 ℓ).trans h1⟩

/-- The three parts of the array q. -/
theorem seg_parts' (C : Cx) {μ' : ℕ → ℤ} {ℓ : ℕ} (hq : Seg μ' fr ((zs q).map (prefQ ℓ))) :
    Seg μ' fr (pairsQAB q.U ℓ q.V) ∧ Seg μ' (fr + q.n * q.n) (pairsQBC q.n q.U ℓ q.Y) ∧
      Seg μ' (fr + 2 * (q.n * q.n)) ((affL (-2) (4 * q.U) q.X).map (prefQ ℓ)) := by
  have hp := C.places
  simp only [zs, negStart, List.map_append] at hq
  rw [seg_append, seg_append] at hq
  simp only [List.length_map, length_affL, negL, transL, List.length_range, hp.2.2.2.1.2.2] at hq
  rwa [show fr + q.n * q.n + q.n * q.n = fr + 2 * (q.n * q.n) by omega] at hq

/-- The question is an instance of all-edges Exact Triangle as the task prescribes. -/
theorem aeQ_pre (C : Cx) {μ' : ℕ → ℤ} {ℓ : ℕ} {e : ℤ} (he : e = 2 ∨ e = 3)
    (hq : Seg μ' fr ((zs q).map (prefQ ℓ)))
    (hthird : Seg μ' (fr + 6 * (q.n * q.n)) (negThird q.U ℓ e q.X)) :
    (aeQ q fr ℓ e).Pre μ' (fr + 8 * (q.n * q.n)) := by
  obtain ⟨hqX, hqY, -⟩ := seg_parts' C hq
  have hp := C.places
  have hle : ∀ l : List ℤ, (∀ z ∈ l, z ∈ zs q) →
      AbsLe (l.map (prefQ ℓ)) ((6 * q.U : ℕ) : ℤ) := by
    intro l hl y hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    have := prefQ_range' C ℓ (hl z hz)
    push_cast
    exact abs_le.2 ⟨by omega, by omega⟩
  exact {
    n_pos := C.pre.n_pos
    U_pos := by simp only [aeQ]; omega
    lenAB := by simp [aeQ, pairsQAB, negL, hp.2.2.2.1.2.2]
    lenBC := by simp [aeQ, pairsQBC, transL]
    lenAC := by simp [aeQ, negThird, hp.2.2.2.1.1]
    segAB := hqX
    segBC := hqY
    segAC := hthird
    leAB := hle _ fun z hz => by simp [zs, negStart, hz]
    leBC := hle _ fun z hz => by simp [zs, negStart, hz]
    leAC := fun y hy => by
      simp only [aeQ]
      push_cast
      exact abs_le_of_mem_negThird C.pre.U_pos C.pre.leX ℓ he y hy
    belowAB := by simp only [aeQ]; omega
    belowBC := by simp only [aeQ]; omega
    belowAC := by simp only [aeQ]; omega
    belowOut := by simp only [aeQ]; omega
    apartAB := by simp only [aeQ]; omega
    apartBC := by simp only [aeQ]; omega
    apartAC := by simp only [aeQ]; omega }

/-- The state of pa between two steps of a round. -/
def St (q : PairsInst) (μ : ℕ → ℤ) (fr : ℕ) (rd : ℤ) (ℓ : ℕ) (A : ℕ → Prop) (σ : State) : Prop :=
  ∃ (res : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame (locals q fr (2 ^ ntLevels q.U : ℕ) (ntLevels q.U) rd res), μ'⟩ ∧
      PaMem q μ fr ℓ A μ'

/-- **One question** leaves the arrays as they are and or-s the flags of its answer into out. -/
theorem probe_spec (C : Cx) {ℓ e : ℕ} (he : e = 2 ∨ e = 3) {rd : ℤ} {A : ℕ → Prop} {σ : State}
    (hσ : St q μ fr rd ℓ A σ) :
    Ends lim (P₀ ++ R') d (paProbe p pAff pOr e) σ (55 * (q.n * q.n) + 60 + T q.n (6 * q.U))
      (St q μ fr rd ℓ fun i => A i ∨ PYes q ℓ e i) := by
  obtain ⟨res, μ₀, rfl, hq, hr, hout, hk⟩ := hσ
  have hpre := C.pre
  have hplaces := C.places
  have hlenZ := length_zs C
  have he' : (e : ℤ) = 2 ∨ (e : ℤ) = 3 := by rcases he with rfl | rfl <;> simp
  have hlenV : ((affL (-2) (4 * q.U) q.X).map (prefQ ℓ)).length = q.n * q.n := by
    simp [hpre.lenX]
  unfold paProbe
  -- Res := pAff(Cells, PreAC, 0 - 1, e, Third)
  refine Ends.callToThen (C.affine_meets (m := -1) (c := e) (dst := fr + 6 * (q.n * q.n))
    (seg_parts' C hq).2.2 (by omega) fun w hx => ?_) ?_
    (ha := by light_side [hlenV]) (hT := by simp [hlenV]; omega)
  · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
    have := prefQ_range' C ℓ (z := z) (by simp [zs, negStart, hz])
    simp only [abs_le]
    omega
  rintro r₁ μ₁ ⟨hthird, h₁⟩
  rw [hlenV] at h₁
  -- Res := pAE(Verts, Bound6, PreAB, PreBC, Third, Flags, SolverFree)
  refine Ends.callToThen (C.solver.meets R' (aeQ q fr ℓ e) (fr + 8 * (q.n * q.n))
    (aeQ_pre C he' (hq.keep (by light_keep [hlenZ])) hthird)
    { word := by simp only [aeTask, aeQ]; omega
      cells := by simp only [aeTask, aeQ]; omega
      space := C.ok.space
      depth := by simp only [aeTask, aeQ]; omega }) ?_ (by simp [aeTask, aeQ])
    (hT := by simp [aeTask, aeQ, hlenV]; omega)
  rintro r₂ μ₂ ⟨hflags, h₂⟩
  replace hflags : Seg μ₂ (fr + 7 * (q.n * q.n)) (flagsOf (q.n * q.n) (PYes q ℓ e)) := hflags
  replace h₂ : KeptBut μ₁ μ₂ (fr + 8 * (q.n * q.n)) (fr + 7 * (q.n * q.n)) (q.n * q.n) := h₂
  -- Res := pOr(Cells, Out, Flags)
  refine Ends.callTo (or_meets (d := d + 1) C.or (hout.keep (by light_keep [length_flagsOf])) hflags C.ok.space
    (by omega) (by omega) (by omega) (by omega)) ?_ (ha := by light_side)
    (hT := by simp [aeTask, aeQ, hlenV]; omega)
  rintro r₃ μ₃ ⟨hout₃, h₃⟩
  refine ⟨r₃, μ₃, ?_, hq.keep (by light_keep [hlenZ]), hr.keep (by light_keep [hlenZ]), hout₃,
    fun c hc => ?_⟩
  · rfl
  · light_keep

/-! ## The rounds -/

theorem pFound_step (q : PairsInst) {L ℓ : ℕ} (h : ℓ < L) (i : ℕ) :
    ((PFound q L (ℓ + 1) i ∨ PYes q ℓ 2 i) ∨ PYes q ℓ 3 i) ↔ PFound q L ℓ i := by
  constructor
  · rintro ((⟨ℓ', h1, h2, h3⟩ | h2) | h3)
    · exact ⟨ℓ', by omega, h2, h3⟩
    · exact ⟨ℓ, le_rfl, h, 2, Or.inl rfl, h2⟩
    · exact ⟨ℓ, le_rfl, h, 3, Or.inr rfl, h3⟩
  · rintro ⟨ℓ', h1, h2, e, he, h3⟩
    by_cases hℓ : ℓ' = ℓ
    · subst hℓ
      rcases he with rfl | rfl
      · exact Or.inl (Or.inr h3)
      · exact Or.inr h3
    · exact Or.inl (Or.inl ⟨ℓ', by omega, h2, e, he, h3⟩)

/-- What prefDown needs holds at every level above 0. -/
theorem down_pre' (C : Cx) {μ' : ℕ → ℤ} {ℓ : ℕ}
    (hℓ : ℓ + 1 ≤ ntLevels q.U) (hq : Seg μ' fr ((zs q).map (prefQ (ℓ + 1))))
    (hr : Seg μ' (fr + 3 * (q.n * q.n)) ((zs q).map (prefR (ntLevels q.U) (ℓ + 1)))) :
    PrefPre lim μ' fr (fr + 3 * (q.n * q.n)) (2 ^ ntLevels q.U)
      ((zs q).map (prefQ (ℓ + 1))) ((zs q).map (prefR (ntLevels q.U) (ℓ + 1))) := by
  have hplaces := C.places
  have hlenZ := length_zs C
  have hL : ((2 ^ ntLevels q.U : ℕ) : ℤ) ≤ ((12 * q.U : ℕ) : ℤ) := by
    exact_mod_cast two_pow_ntLevels_le' C.pre.U_pos
  push_cast at hL
  refine ⟨hq, hr, by simp, C.ok.space, by simp [hlenZ]; omega, by simp [hlenZ]; omega,
    by simp [hlenZ], by omega, fun y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    have := prefQ_range' C (ℓ + 1) hz
    simp only [abs_le]
    omega
  · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    have h0 := prefR_nonneg (ntLevels q.U) (ℓ + 1) z
    have h1 := prefR_lt hℓ z
    simp only [abs_le]
    omega

/-- **One round**: from the level ℓ + 1 to the level ℓ, and the two questions at the level ℓ. -/
theorem round_spec (C : Cx) {ℓ : ℕ} (hℓ : ℓ + 1 ≤ ntLevels q.U) {rd : ℤ} {σ : State}
    (hσ : St q μ fr rd (ℓ + 1) (PFound q (ntLevels q.U) (ℓ + 1)) σ) :
    Ends lim (P₀ ++ R') d (paRound p pAff pDown pOr) σ
      (230 * (q.n * q.n) + 140 + 2 * T q.n (6 * q.U))
      (St q μ fr rd ℓ (PFound q (ntLevels q.U) ℓ)) := by
  obtain ⟨res, μ₀, rfl, hq, hr, hout, hk⟩ := hσ
  have hplaces := C.places
  have hlenZ := length_zs C
  unfold paRound
  -- Res := pDown(Cells3, PreAB, RestAB, Power)
  refine Ends.callToThen (prefDown_meets C.down (down_pre' C hℓ hq hr)) ?_ (by simp [hlenZ])
    (hT := by simp [hlenZ]; omega)
  rintro r₁ μ₁ ⟨hq₁, hr₁, hrest⟩
  rw [zipWith_shiftQ hℓ] at hq₁
  rw [map_shiftR hℓ] at hr₁
  simp only [List.length_map, hlenZ] at hrest
  have hσ₁ : St q μ fr rd ℓ (PFound q (ntLevels q.U) (ℓ + 1))
      ⟨frame (locals q fr (2 ^ ntLevels q.U : ℕ) (ntLevels q.U) rd r₁), μ₁⟩ :=
    ⟨r₁, μ₁, rfl, hq₁, hr₁,
      hout.keep fun c hc => by
        simp only [Inside, length_flagsOf] at hc
        exact hrest c (Or.inl (by omega)) (Or.inl (by omega)),
      fun c hc => (hrest c (Or.inl hc.1) (Or.inl (by omega))).trans (hk c hc)⟩
  refine Ends.next _ ((probe_spec C (Or.inl rfl) hσ₁).mono le_rfl fun σ₂ hσ₂ => ?_)
    (by simp [hlenZ]; omega)
  refine (probe_spec C (Or.inr rfl) hσ₂).mono (by simp [hlenZ]; omega) fun σ₃ hσ₃ => ?_
  obtain ⟨r₃, μ₃, rfl, h1, h2, h3, h4⟩ := hσ₃
  refine ⟨r₃, μ₃, rfl, h1, h2, ?_, h4⟩
  simp only [Nat.cast_ofNat] at h3
  rwa [flagsOf_congr _ (pFound_step q (Nat.lt_of_succ_le hℓ))] at h3

/-- The number of the round can be read and changed. -/
theorem St.round {rd : ℤ} {ℓ : ℕ} {A : ℕ → Prop} {σ : State} (h : St q μ fr rd ℓ A σ) (rd' : ℤ) :
    σ.loc Round = rd ∧ St q μ fr rd' ℓ A { σ with loc := Function.update σ.loc Round rd' } := by
  obtain ⟨res, μ', rfl, hm⟩ := h
  exact ⟨rfl, res, μ', by rw [update_frame_setLocal]; rfl, hm⟩

/-- **The L rounds**: in the end out holds the flags of the pairs found at some level. -/
theorem rounds_spec (C : Cx) {res : ℤ} {μ' : ℕ → ℤ}
    (hm : PaMem q μ fr (ntLevels q.U) (PFound q (ntLevels q.U) (ntLevels q.U)) μ') :
    Ends lim (P₀ ++ R') d (.for Round (v Levels) (paRound p pAff pDown pOr))
      ⟨frame (locals q fr (2 ^ ntLevels q.U : ℕ) (ntLevels q.U) 0 res), μ'⟩
      (6 + ntLevels q.U * (230 * (q.n * q.n) + 148 + 2 * T q.n (6 * q.U)))
      (St q μ fr (ntLevels q.U) 0 (PFound q (ntLevels q.U) 0)) := by
  have hplaces := C.places
  have hL : ((ntLevels q.U : ℕ) : ℤ) ≤ ((12 * q.U : ℕ) : ℤ) := by
    exact_mod_cast (Nat.lt_two_pow_self (n := ntLevels q.U)).le.trans
      (two_pow_ntLevels_le' C.pre.U_pos)
  push_cast at hL
  refine Ends.for (fun t σ => St q μ fr t (ntLevels q.U - t)
    (PFound q (ntLevels q.U) (ntLevels q.U - t)) σ) (ntLevels q.U)
    (230 * (q.n * q.n) + 140 + 2 * T q.n (6 * q.U)) ?start ?round ?done ?bound (by omega) ?time
  case start =>
    refine ⟨res, μ', ?_, by simpa using hm⟩
    rw [update_frame_setLocal]
    rfl
  case round =>
    intro t σ ht _ hσ
    obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ntLevels q.U - t = ℓ + 1 := ⟨ntLevels q.U - t - 1, by omega⟩
    rw [show ntLevels q.U - (t + 1) = ℓ by omega]
    rw [hℓ] at hσ
    refine (round_spec C (by omega) hσ).mono le_rfl fun σ' hσ' => ?_
    exact_mod_cast hσ'.round ((t : ℤ) + 1)
  case done =>
    intro σ _ hσ
    simpa using hσ
  case bound =>
    rintro t _ - - ⟨res', μ'', rfl, -⟩
    exact ⟨trivial, rfl⟩
  case time =>
    simp
    ring_nf
    omega

theorem flagsOf_congr' (N : ℕ) {A B : ℕ → Prop} (h : ∀ i < N, A i ↔ B i) :
    flagsOf N A = flagsOf N B := by
  simp only [flagsOf]
  exact List.map_congr_left fun i hi => flag_congr (h i (List.mem_range.1 hi))

/-- **pa is correct**, in every program that begins with the solver's program and has the loops
over arrays. -/
theorem pa_spec (C : Cx) :
    Ends lim (P₀ ++ R') d (paBody p pAff pDown pTr pFill pOr)
      ⟨frame [q.n, q.U, q.x, q.y, q.v, q.out, fr], μ⟩ (paTime T q.n q.U)
      fun σ' => pairsTask.Post q μ fr (σ'.loc 0) σ'.mem := by
  have hpre := C.pre
  have hplaces := C.places
  have hrounds : ntLevels q.U * (250 * (q.n * q.n) + 200 + 2 * T q.n (6 * q.U)) =
      ntLevels q.U * (230 * (q.n * q.n) + 148 + 2 * T q.n (6 * q.U)) +
        ntLevels q.U * (20 * (q.n * q.n) + 52) := by
    ring
  have hL1 : 14 * ntLevels q.U ≤ ntLevels q.U * (20 * (q.n * q.n) + 52) := by nlinarith
  unfold paBody paTime
  refine Ends.next _ ((init_spec C).mono le_rfl ?_) (by simp [paInit]; omega)
  rintro _ rfl
  refine Ends.next _ ((pow_spec C).mono le_rfl ?_) (by simp [paInit]; omega)
  rintro _ rfl
  refine Ends.next _ ((fill_spec C _ _ _ _).mono le_rfl ?_) (by simp [paInit]; omega)
  rintro _ ⟨res, μ₁, rfl, hm⟩
  refine Ends.next _ ((rounds_spec C hm).mono le_rfl ?_) (by simp [paInit]; omega)
  rintro _ ⟨res', μ₂, rfl, -, -, hout, hk⟩
  refine Ends.setTo 0 ⟨?_, hk⟩ (hT := by simp [paInit]; omega)
  have h3 : 3 * q.U < 2 ^ ntLevels q.U := by have := lt_two_pow_ntLevels' q.U; omega
  change Seg μ₂ q.out (flagsOf (q.n * q.n) fun i => ∃ k < q.n,
    q.X.getD (i / q.n * q.n + k) 0 + q.Y.getD (k * q.n + i % q.n) 0 < q.V.getD i 0)
  rw [flagsOf_congr' _ fun i hi => pair_iff_exists_level hpre.lenX hpre.lenY hpre.lenV hpre.leX
    hpre.leY hpre.leV h3 hi]
  refine (flagsOf_congr _ fun i => ?_) ▸ hout
  exact ⟨fun ⟨ℓ, _, h2, h⟩ => ⟨ℓ, h2, h⟩, fun ⟨ℓ, h2, h⟩ => ⟨ℓ, Nat.zero_le _, h2, h⟩⟩

end PaHost

/-- The need of pa is polynomially bounded if the need of the solver is. -/
theorem polyNeed_paNeed {r : ℕ → ℕ → Need} (h : PolyNeed r) : PolyNeed (paNeed r) := by
  unfold paNeed
  poly_need [h.word, h.cells, h.depth]

/-- **All pairs from all-edges Exact Triangle.** -/
theorem isHost_pa : IsHost aeTask pairsTask paTime paNeed := by
  refine ⟨fun P p T r hsol => ⟨[affineBody, prefDownBody, rowBody, transBody (P.length + 2),
    fillBody, orBody, paBody p P.length (P.length + 1) (P.length + 3) (P.length + 4)
      (P.length + 5)], P.length + 6, paBody p P.length (P.length + 1) (P.length + 3)
      (P.length + 4) (P.length + 5), by simp, fun R lim d x μ fr hpre hok => ?_⟩,
    fun r => polyNeed_paNeed⟩
  rw [List.append_assoc]
  exact PaHost.pa_spec (pRow := P.length + 2) ⟨hsol, by simp, by simp, by simp, by simp, by simp, by simp, hpre, hok⟩

end Light.Sec3
