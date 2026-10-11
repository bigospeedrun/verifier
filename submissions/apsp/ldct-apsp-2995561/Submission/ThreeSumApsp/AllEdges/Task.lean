/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Programs.LightModel
public import Submission.ThreeSumApsp.Programs.Sec3.Theorem17.Witnesses.BruteForce

/-!
# All-edges Exact Triangle as a task

All-edges Exact Triangle: for every pair `(a, b)`, whether some `c` has
`w(a,b) + w(b,c) + w(a,c) = 0`.  The answers are `n²` flags, cell `a n + b` for the pair `(a, b)`.

`aeModel` is the reading of "solved in time T" of `lightModel` with Exact Triangle replaced by its
all-edges form, so that the deductions of the paper between running times (Theorems 17 and 19)
apply to it unchanged.

The brute force (`aeBruteBody`) scans all of `C` for every pair.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.Spec

/-! ## The task -/

/-- Three `n × n` matrices of weights, and the place for `n²` flags. -/
structure AEInst : Type extends TriInst where
  out : ℕ

/-- The matrices and the place for the flags lie below the free pointer; the flags do not meet the
matrices. -/
structure AEInst.Pre (x : AEInst) (μ : ℕ → ℤ) (fr : ℕ) : Prop
    extends TriInst.Pre x.toTriInst μ fr where
  belowOut : x.out + x.n * x.n ≤ fr
  apartAB : Apart x.ab (x.n * x.n) x.out (x.n * x.n)
  apartBC : Apart x.bc (x.n * x.n) x.out (x.n * x.n)
  apartAC : Apart x.ac (x.n * x.n) x.out (x.n * x.n)

/-- The flags: cell `q = a n + b` holds 1 if some `c < n` has `w(a,b) + w(b,c) + w(a,c) = 0`, and 0
if not. -/
noncomputable def aeFlags (n : ℕ) (AB BC AC : List ℤ) : List ℤ :=
  (List.range (n * n)).map fun q =>
    flag (∃ c < n, AB.getD q 0 + BC.getD (q % n * n + c) 0 + AC.getD (q / n * n + c) 0 = 0)

/-- **All-edges Exact Triangle**: ae(n, U, ab, bc, ac, out, fr) writes the `n²` flags to out. -/
noncomputable def aeTask : Task where
  Inst := AEInst
  size x := x.n
  bound x := x.U
  args x := [x.n, x.U, x.ab, x.bc, x.ac, x.out]
  Pre := AEInst.Pre
  Post x μ fr _ μ' := Seg μ' x.out (aeFlags x.n x.AB x.BC x.AC) ∧
    KeptBut μ μ' fr x.out (x.n * x.n)

end Light.Sec3

namespace Light

/-- The reading of `lightModel`, with all-edges Exact Triangle in the place of Exact Triangle. -/
noncomputable def aeModel : DetTimeModel :=
  { lightModel with exactTriangle := SolvedIn Sec3.aeTask }

end Light

namespace Light.Sec3

open ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The flags as scans -/

/-- The flag of the place `q`, as a scan of all of `C`. -/
def aeHit (n : ℕ) (AB BC AC : List ℤ) (q : ℕ) : Bool := scanHit n AB BC AC (q / n) (q % n) 0 n

theorem aeHit_iff {n : ℕ} {AB BC AC : List ℤ} {q : ℕ} (hq : q < n * n) :
    aeHit n AB BC AC q = true ↔
      ∃ c < n, AB.getD q 0 + BC.getD (q % n * n + c) 0 + AC.getD (q / n * n + c) 0 = 0 := by
  have hq' : q / n * n + q % n = q := Nat.div_add_mod' q n
  simp [aeHit, scanHit, hq']

/-- The flags, from the scans. -/
theorem getElem_aeFlags {n : ℕ} {AB BC AC : List ℤ} {q : ℕ} (hq : q < (aeFlags n AB BC AC).length) :
    (aeFlags n AB BC AC)[q] = bit (aeHit n AB BC AC q) := by
  have hq' : q < n * n := by simpa [aeFlags] using hq
  rw [← flag_eq_bit]
  simp only [aeFlags, List.getElem_map, List.getElem_range]
  exact flag_congr (aeHit_iff hq').symm

theorem length_aeFlags (n : ℕ) (AB BC AC : List ℤ) : (aeFlags n AB BC AC).length = n * n := by
  simp [aeFlags]

/-! ## The brute force -/

namespace AEBrute

/-- The locals of `aeBrute`.  The arguments: `n`, `U`, the addresses of the three arrays and of the
flags, and the free pointer.  Then the vertices `a` and `b`, and the result of a scan. -/
abbrev Size : ℕ := 0
@[inherit_doc Size] abbrev Bound : ℕ := 1
@[inherit_doc Size] abbrev AdrAB : ℕ := 2
@[inherit_doc Size] abbrev AdrBC : ℕ := 3
@[inherit_doc Size] abbrev AdrAC : ℕ := 4
@[inherit_doc Size] abbrev Out : ℕ := 5
@[inherit_doc Size] abbrev Free : ℕ := 6
@[inherit_doc Size] abbrev VtxA : ℕ := 7
@[inherit_doc Size] abbrev VtxB : ℕ := 8
@[inherit_doc Size] abbrev Res : ℕ := 9

end AEBrute

open AEBrute in
/-- One pair `(a, b)`: out[a n + b] := scan(ab, bc, ac, n, a, b, 0, n). -/
def aeBrutePair (pScan : ℕ) : Stmt :=
  .call pScan [v AdrAB, v AdrBC, v AdrAC, v Size, v VtxA, v VtxB, k 0, v Size] Res ;;
  .store ((v Out +' (v VtxA *' v Size)) +' v VtxB) (v Res)

open AEBrute in
/-- The inner loop: all `b` for one `a`. -/
def aeBruteInner (pScan : ℕ) : Stmt := Stmt.for VtxB (v Size) (aeBrutePair pScan)

open AEBrute in
/-- aeBrute(n, U, ab, bc, ac, out, fr); the parameter is the procedure number of `scan`. -/
def aeBruteBody (pScan : ℕ) : Stmt :=
  Stmt.for VtxA (v Size) (aeBruteInner pScan) ;; .set 0 (k 0)

/-- The time of aeBrute. -/
def tAEBrute (n : ℕ) : ℕ := 200 * n ^ 3 + 200

/-- What aeBrute needs: sums of three weights and the places of the flags, no cells, one call. -/
def aeBruteNeed (_n U : ℕ) : Need := ⟨3 * U + 1, 0, 1⟩

/-- The flags of the first `j` places, written. -/
abbrev aeWrote (μ : ℕ → ℤ) (out n : ℕ) (AB BC AC : List ℤ) (j : ℕ) : ℕ → ℤ :=
  wrote μ out (fun q => bit (aeHit n AB BC AC q)) j

/-- The weights are where the scans read them, while flags are written. -/
theorem AEInst.Pre.weights {x : AEInst} {μ : ℕ → ℤ} {fr : ℕ} (hpre : x.Pre μ fr)
    (hok : (aeBruteNeed x.n x.U).Ok lim fr d) {j : ℕ} (hj : j ≤ x.n * x.n) :
    Weights lim (aeWrote μ x.out x.n x.AB x.BC x.AC j) x.ab x.bc x.ac x.n x.U x.AB x.BC x.AC := by
  have hAB := hpre.apartAB
  have hBC := hpre.apartBC
  have hAC := hpre.apartAC
  have lAB := hpre.lenAB
  have lBC := hpre.lenBC
  have lAC := hpre.lenAC
  have sAB : Seg (aeWrote μ x.out x.n x.AB x.BC x.AC j) x.ab x.AB := fun i hi => by
    unfold aeWrote; rw [wrote_rest (by omega)]; exact hpre.segAB i hi
  have sBC : Seg (aeWrote μ x.out x.n x.AB x.BC x.AC j) x.bc x.BC := fun i hi => by
    unfold aeWrote; rw [wrote_rest (by omega)]; exact hpre.segBC i hi
  have sAC : Seg (aeWrote μ x.out x.n x.AB x.BC x.AC j) x.ac x.AC := fun i hi => by
    unfold aeWrote; rw [wrote_rest (by omega)]; exact hpre.segAC i hi
  exact
    { hw := hok.space
      hU := by exact_mod_cast hok.word
      arrAB := ⟨hpre.lenAB, sAB, hpre.leAB, hpre.belowAB.trans hok.cells⟩
      arrBC := ⟨hpre.lenBC, sBC, hpre.leBC, hpre.belowBC.trans hok.cells⟩
      arrAC := ⟨hpre.lenAC, sAC, hpre.leAC, hpre.belowAC.trans hok.cells⟩ }

section

variable {pScan : ℕ} {x : AEInst} {μ : ℕ → ℤ} {fr : ℕ}

/-- One pair: its flag is written. -/
theorem aeBrutePair_spec (hP : P[pScan]? = some scanBody) (hpre : x.Pre μ fr)
    (hok : (aeBruteNeed x.n x.U).Ok lim fr d) {a b : ℕ} (ha : a < x.n) (hb : b < x.n) (r : ℤ) :
    Ends lim P d (aeBrutePair pScan)
      ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, x.out, fr, a, b, r],
        aeWrote μ x.out x.n x.AB x.BC x.AC (a * x.n + b)⟩
      (tScan x.n + 30) fun σ' => ∃ r', σ' = ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, x.out, fr, a, b, r'],
        aeWrote μ x.out x.n x.AB x.BC x.AC (a * x.n + b + 1)⟩ := by
  have hab : a * x.n + b < x.n * x.n := by nlinarith
  have C := hpre.weights hok hab.le
  light_facts C C.arrAB C.arrBC C.arrAC
  have hbo := hpre.belowOut
  have hcells := hok.cells
  have hd : d < lim.depth := hok.depth
  have han : a * x.n ≤ x.n * x.n := by nlinarith
  unfold aeBrutePair
  -- res := scan(ab, bc, ac, n, a, b, 0, n)
  light_call (scan_meets hP C ha hb (c0 := 0) (Nat.zero_add x.n).le) with _ _ ⟨rfl, rfl⟩
  have hval : flag (scanHit x.n x.AB x.BC x.AC a b 0 x.n = true) =
      bit (aeHit x.n x.AB x.BC x.AC (a * x.n + b)) := by
    have hdiv : (a * x.n + b) / x.n = a := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hb, Nat.zero_add]
    have hmod : (a * x.n + b) % x.n = b := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
    rw [flag_eq_bit, aeHit, hdiv, hmod]
  rw [hval]
  -- out[a n + b] := res
  refine Ends.storeTo (x.out + (a * x.n + b)) (bit (aeHit x.n x.AB x.BC x.AC (a * x.n + b)))
    ⟨bit (aeHit x.n x.AB x.BC x.AC (a * x.n + b)), ?_⟩ (by light_side) (by light_time)
  have hw := wrote_succ (μ := μ) (dst := x.out) (f := fun q => bit (aeHit x.n x.AB x.BC x.AC q))
    (j := a * x.n + b)
  simp only [aeWrote] at hw ⊢
  rw [hw]
  simp [setLocal]


/-- The inner loop: the flags of all pairs `(a, b)` for one `a`. -/
theorem aeBruteInner_spec (hP : P[pScan]? = some scanBody) (hpre : x.Pre μ fr)
    (hok : (aeBruteNeed x.n x.U).Ok lim fr d) {a : ℕ} (ha : a < x.n) (b₀ r₀ : ℤ) :
    Ends lim P d (aeBruteInner pScan)
      ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, x.out, fr, a, b₀, r₀],
        aeWrote μ x.out x.n x.AB x.BC x.AC (a * x.n)⟩
      (x.n * (24 * x.n + 110) + 10) fun σ' => ∃ r, σ' =
        ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, x.out, fr, a, x.n, r],
          aeWrote μ x.out x.n x.AB x.BC x.AC ((a + 1) * x.n)⟩ := by
  have hw := hok.space
  have hbo := hpre.belowOut
  have hcells := hok.cells
  have hn1 := hpre.n_pos
  have hnn : x.n ≤ x.n * x.n := Nat.le_mul_of_pos_left _ hn1
  refine Ends.for (fun b σ => ∃ r, σ = ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, x.out, fr, a, b, r],
    aeWrote μ x.out x.n x.AB x.BC x.AC (a * x.n + b)⟩) x.n (tScan x.n + 30)
    ?start ?round ?done ?bound (hT := by simp [tScan]; ring_nf; omega)
  case start => exact ⟨r₀, by simp [update_frame_setLocal]⟩
  case bound =>
    rintro b _ - - ⟨r, rfl⟩
    simp
  case round =>
    rintro b _ hb - ⟨r, rfl⟩
    refine (aeBrutePair_spec hP hpre hok ha hb r).mono le_rfl ?_
    rintro _ ⟨r', rfl⟩
    exact ⟨by simp, r', by simp [update_frame_setLocal, Nat.add_assoc]⟩
  case done =>
    rintro _ - ⟨r, rfl⟩
    exact ⟨r, by rw [Nat.succ_mul]⟩

/-- The steps of the two loops of aeBrute are within its time. -/
theorem tAEBrute_ge (n : ℕ) : n * (1 + (n * (24 * n + 110) + 10) + 7) + 1 + 5 + 10 ≤ tAEBrute n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [tAEBrute]
  · have hsq : n ^ 2 ≤ n ^ 3 := Nat.pow_le_pow_right hn (by omega)
    have hlin : n ≤ n ^ 3 := Nat.le_self_pow (by omega) n
    rw [show n * (1 + (n * (24 * n + 110) + 10) + 7) = 24 * n ^ 3 + 110 * n ^ 2 + 18 * n by ring,
      tAEBrute]
    omega

/-- **The all-edges brute force.**  In any program that holds `scanBody` as its procedure number
`pScan`, `aeBruteBody pScan` writes the flags of all pairs and changes no other cell. -/
theorem aeBrute_spec (hP : P[pScan]? = some scanBody) (x : AEInst) (μ : ℕ → ℤ) (fr : ℕ)
    (hpre : x.Pre μ fr) (hok : (aeBruteNeed x.n x.U).Ok lim fr d) :
    Ends lim P d (aeBruteBody pScan) ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, x.out, fr], μ⟩
      (tAEBrute x.n) fun σ' => aeTask.Post x μ fr (σ'.loc 0) σ'.mem := by
  have hw := hok.space
  have hbo := hpre.belowOut
  have hcells := hok.cells
  have hn1 := hpre.n_pos
  have hnn : x.n ≤ x.n * x.n := Nat.le_mul_of_pos_left _ hn1
  have htime := tAEBrute_ge x.n
  unfold aeBruteBody
  -- for a < n
  refine Ends.next _ (Ends.for (fun a σ => ∃ b r, σ = ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, x.out, fr,
    a, b, r], aeWrote μ x.out x.n x.AB x.BC x.AC (a * x.n)⟩) x.n (x.n * (24 * x.n + 110) + 10)
    ?start ?round ?done ?bound (hT := le_rfl)) (by simp; omega)
  case start =>
    refine ⟨0, 0, ?_⟩
    simp only [Nat.zero_mul, aeWrote, wrote_zero]
    simpa [update_frame_setLocal] using
      (frame_append_zeros [(x.n : ℤ), x.U, x.ab, x.bc, x.ac, x.out, fr, 0] 2).symm
  case bound =>
    rintro a _ - - ⟨b, r, rfl⟩
    simp
  case round =>
    rintro a _ ha - ⟨b, r, rfl⟩
    refine (aeBruteInner_spec hP hpre hok ha b r).mono le_rfl ?_
    rintro _ ⟨r', rfl⟩
    exact ⟨by simp, x.n, r', by simp [update_frame_setLocal]⟩
  case done =>
    rintro _ - ⟨b, r, rfl⟩
    -- return 0
    refine Ends.setTo 0 ⟨?_, ?_⟩ (by simp; omega) (by simp; omega)
    · intro q hq
      rw [length_aeFlags] at hq
      simp only [aeWrote]
      rw [wrote_done hq, getElem_aeFlags]
    · exact SameOn.mono (sameOutside_wrote (μ := μ) (dst := x.out) (f := fun q => bit (aeHit x.n x.AB x.BC x.AC q)) le_rfl) fun _ h => h.2

/-- The specification of `aeBrute`, for its callers. -/
theorem aeBrute_meets {p : ℕ} (hB : P[p]? = some (aeBruteBody pScan))
    (hP : P[pScan]? = some scanBody) (x : AEInst) (μ : ℕ → ℤ) (fr : ℕ) (hpre : x.Pre μ fr)
    (hok : (aeBruteNeed x.n x.U).Ok lim fr d) :
    Meets lim P p d [x.n, x.U, x.ab, x.bc, x.ac, x.out, fr] μ (tAEBrute x.n)
      (aeTask.Post x μ fr) :=
  Meets.of_body hB (aeBrute_spec hP x μ fr hpre hok)

end

/-- **aeBrute** solves all-edges Exact Triangle. -/
theorem aeBrute_solves :
    Solves aeTask [aeBruteBody 1, scanBody] 0 (fun n _ => tAEBrute n) aeBruteNeed :=
  ⟨aeBruteBody 1, rfl, fun _ _ _ x μ fr hpre hok => aeBrute_spec rfl x μ fr hpre hok⟩

/-- "Smaller instances are solved by brute force", all-edges form. -/
theorem claim_aeBruteForce : Claim.BruteForce aeModel := by
  refine ⟨400, [aeBruteBody 1, scanBody], 0, fun n _ => tAEBrute n, aeBruteNeed,
    ⟨2, 1, fun n U => ?_⟩, aeBrute_solves, fun n U u hn _ _ => ?_⟩
  · have hbound : polyBound 2 1 [n, U] = 4 * ((n + 1) * (U + 1)) := by simp [polyBound]
    have hU : U + 1 ≤ (n + 1) * (U + 1) := Nat.le_mul_of_pos_left _ (by omega)
    rw [hbound]
    simp only [aeBruteNeed]
    exact ⟨by omega, by omega, by omega⟩
  · have hlog : 0 ≤ logU u := Real.log_nonneg (le_trans (by norm_num) (le_max_right u 2))
    have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ (by exact_mod_cast hn)
    calc ((tAEBrute n : ℕ) : ℝ) = 200 * (n : ℝ) ^ 3 + 200 := by rw [tAEBrute]; push_cast; rfl
      _ ≤ 400 * ((n : ℝ) ^ 3 * 1) := by linarith
      _ ≤ 400 * ((n : ℝ) ^ 3 * (1 + logU u)) := by gcongr; linarith

end Light.Sec3
