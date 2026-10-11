/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Filter2.HostAssemble
public import Submission.ThreeSumApsp.Lang.PolyBounded

/-!
# The filtering host solves all-edges Exact Triangle

`filter_host`: from a solver of the counting oracle, the host builds a solver of all-edges Exact
Triangle, within `filterTime To` steps and with the need `filterNeed needo`; its need is
polynomially bounded if that of the oracle is.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Filter2

open ThreeSumApsp.Spec Light.Sec3

/-! ## The program -/

/-- The procedures of the host, appended to a program of length `o` whose procedure `po` is the
counting oracle.  The host is procedure `o + 18`. -/
def hostProcs (o po : ℕ) : Program :=
  [aggrBody, certBody, argminBody, copyBody, filterActBody,
    stepBody po o (o + 1) (o + 2) (o + 3),
    roundBody po o (o + 5) (o + 4),
    scanBody, groupBody (o + 7), finalBody (o + 8), coreBody (o + 6) (o + 9),
    log2Body, sqrtBody, pow2Body, divBody, sieveBody, poolFilterBody, fillBody,
    topBody (o + 11) (o + 12) (o + 13) (o + 14) (o + 15) (o + 16) (o + 17) (o + 10)]

theorem get_host {P R : Program} {po i : ℕ} (hi : i < 19) :
    (P ++ hostProcs P.length po ++ R)[P.length + i]? = (hostProcs P.length po)[i]? := by
  rw [List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left (by simp [hostProcs]; omega)]

/-! ## The time and the need -/

/-- **The time of the host**: the parameters, the sieve, the pool, the marks, and the core, which
runs `roundsOf n` rounds of `rOf n` steps; a step calls the oracle `QOf n` times (once per prime of
the pool) and a round twice more, each call within `supTo To n U`. -/
def filterTime (To : List ℕ → ℕ) (n U : ℕ) : ℕ := tTop To n U

/-- The largest word of the oracle at the moduli up to `Pmax`. -/
def supW (needo : List ℕ → Need) (n U : ℕ) : ℕ :=
  (Finset.range (PmaxOf n + 1)).sup fun p => (needo [n, U, sOf n, p]).word

/-- The most cells of the oracle at the moduli up to `Pmax`. -/
def supC (needo : List ℕ → Need) (n U : ℕ) : ℕ :=
  (Finset.range (PmaxOf n + 1)).sup fun p => (needo [n, U, sOf n, p]).cells

/-- The largest depth of the oracle at the moduli up to `Pmax`. -/
def supD (needo : List ℕ → Need) (n U : ℕ) : ℕ :=
  (Finset.range (PmaxOf n + 1)).sup fun p => (needo [n, U, sOf n, p]).depth

/-- **The need of the host.** -/
def filterNeed (needo : List ℕ → Need) (n U : ℕ) : Need where
  word := filterWord n U + supW needo n U
  cells := aTOP n 0 + 2 * RR n + supC needo n U
  depth := supD needo n U + 5

theorem aTOP_eq (n fr : ℕ) : aTOP n fr = fr + aTOP n 0 := by
  unfold aTOP aGT aCNT aUA aDONE aACT; ring

variable {lim : Limits}

theorem env_of_ok {needo : List ℕ → Need} {d : ℕ} {x : AEInst} {fr : ℕ} {μ0 : ℕ → ℤ}
    (hpre : x.Pre μ0 fr) (hok : (filterNeed needo x.n x.U).Ok lim fr d) :
    Env lim d x fr μ0 needo := by
  obtain ⟨hw, hc, hs, hd⟩ := hok
  simp only [filterNeed] at hw hc hd
  have ha := aTOP_eq x.n fr
  refine ⟨hpre, hs, by omega, le_trans (by push_cast; omega) hw, fun p hp => ?_, by omega⟩
  have hmem : p ∈ Finset.range (PmaxOf x.n + 1) := Finset.mem_range.2 (by omega)
  have h1 : (needo [x.n, x.U, sOf x.n, p]).word ≤ supW needo x.n x.U :=
    Finset.le_sup (f := fun p => (needo [x.n, x.U, sOf x.n, p]).word) hmem
  have h2 : (needo [x.n, x.U, sOf x.n, p]).cells ≤ supC needo x.n x.U :=
    Finset.le_sup (f := fun p => (needo [x.n, x.U, sOf x.n, p]).cells) hmem
  have h3 : (needo [x.n, x.U, sOf x.n, p]).depth ≤ supD needo x.n x.U :=
    Finset.le_sup (f := fun p => (needo [x.n, x.U, sOf x.n, p]).depth) hmem
  exact ⟨le_trans (by push_cast; omega) hw, by omega, hs, by omega⟩

/-! ## The host solves all-edges Exact Triangle -/

theorem filter_solves {P : Program} {po : ℕ} {To : List ℕ → ℕ} {needo : List ℕ → Need}
    (hsol : SolvesN oracleTask P po To needo) :
    Solves aeTask (P ++ hostProcs P.length po) (P.length + 18) (filterTime To) (filterNeed needo) := by
  refine ⟨_, by rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]; rfl,
    fun R lim d x μ fr hpre hok => ?_⟩
  have E := env_of_ok (needo := needo) hpre hok
  have g := fun i (hi : i < 19) => get_host (P := P) (R := R) (po := po) hi
  rw [List.append_assoc]
  have HPa : ParamProcs (P ++ (hostProcs P.length po ++ R)) (P.length + 11) (P.length + 12)
      (P.length + 13) (P.length + 14) := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [← List.append_assoc]
    · exact (g 11 (by omega)).trans rfl
    · exact (g 12 (by omega)).trans rfl
    · exact (g 13 (by omega)).trans rfl
    · exact (g 14 (by omega)).trans rfl
  have gg : ∀ i (hi : i < 19), (P ++ (hostProcs P.length po ++ R))[P.length + i]? =
      (hostProcs P.length po)[i]? := fun i hi => by rw [← List.append_assoc]; exact g i hi
  have HT : TopProcs (P ++ (hostProcs P.length po ++ R)) (P.length + 15) (P.length + 16)
      (P.length + 17) := ⟨gg 15 (by omega), gg 16 (by omega), gg 17 (by omega)⟩
  have HP : RoundProcs (P ++ (hostProcs P.length po ++ R)) po P.length (P.length + 5)
      (P.length + 4) (P.length + 1) (P.length + 2) (P.length + 3) :=
    ⟨gg 5 (by omega), ⟨(gg 0 (by omega)).trans rfl, gg 1 (by omega), gg 2 (by omega),
      gg 3 (by omega)⟩, gg 4 (by omega)⟩
  have HF : FinalProcs (P ++ (hostProcs P.length po ++ R)) (P.length + 9) (P.length + 8)
      (P.length + 7) := ⟨gg 9 (by omega), gg 8 (by omega), gg 7 (by omega)⟩
  exact top_spec hsol HPa HT (gg 10 (by omega)) (gg 6 (by omega)) HP HF E


/-! ## The need is polynomially bounded -/

theorem two_pow_kOf_le (n : ℕ) : 2 ^ kOf n ≤ 2 * n + 1 := by
  unfold kOf
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h1 : 1 ≤ Nat.size n := Nat.size_pos.2 hn
    have h2 : 2 ^ (Nat.size n - 1) ≤ n := Nat.lt_size.1 (by omega)
    have : 2 ^ Nat.size n = 2 * 2 ^ (Nat.size n - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega

theorem exp_Pmax_le (n : ℕ) : (ellOf n + 1) * rOf n ≤ 11 * kOf n + 8 := by
  have hq : Nat.sqrt (kOf n) * Nat.sqrt (kOf n) ≤ kOf n := Nat.sqrt_le _
  have hqk : Nat.sqrt (kOf n) ≤ kOf n := Nat.sqrt_le_self _
  have hl : ellOf n = Nat.sqrt (kOf n) + 1 := rfl
  have hl1 := ellOf_pos n
  have hsl : Nat.sqrt (ellOf n) ≤ ellOf n := Nat.sqrt_le_self _
  have hb : bOf n ≤ 4 * kOf n + 2 := by
    unfold bOf
    calc ellOf n * (Nat.sqrt (ellOf n) + 1) ≤ ellOf n * (ellOf n + 1) :=
          Nat.mul_le_mul_left _ (by omega)
      _ ≤ 4 * kOf n + 2 := by rw [hl]; nlinarith
  have he : 336175 * kOf n / 10 ^ 7 ≤ kOf n := by
    rw [Nat.div_le_iff_le_mul_add_pred (by norm_num)]; omega
  have hcK : cKOf n ≤ kOf n + 1 := by
    unfold cKOf sOf
    exact Nat.size_le.2 (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hr : (ellOf n + 1) * rOf n ≤ 2 * (cKOf n + bOf n) + ellOf n + 1 := by
    unfold rOf
    have h1 : ellOf n * ((cKOf n + bOf n) / ellOf n) ≤ cKOf n + bOf n :=
      Nat.mul_div_le _ _
    have h3 : (cKOf n + bOf n) / ellOf n ≤ ellOf n * ((cKOf n + bOf n) / ellOf n) :=
      Nat.le_mul_of_pos_left _ hl1
    generalize (cKOf n + bOf n) / ellOf n = q at *
    calc (ellOf n + 1) * (q + 1) =
          ellOf n * q + q + ellOf n + 1 := by ring
      _ ≤ _ := by omega
  omega

/-- **The largest modulus is polynomial in `n`**: `Pmax ≤ 2^8 (2n + 1)^11`. -/
theorem Pmax_le (n : ℕ) : PmaxOf n ≤ 2 ^ 8 * (2 * n + 1) ^ 11 := by
  unfold PmaxOf RR
  calc (2 * 2 ^ ellOf n) ^ rOf n = 2 ^ ((ellOf n + 1) * rOf n) := by rw [← pow_succ', ← pow_mul]
    _ ≤ 2 ^ (11 * kOf n + 8) := Nat.pow_le_pow_right (by norm_num) (exp_Pmax_le n)
    _ = 2 ^ 8 * (2 ^ kOf n) ^ 11 := by ring
    _ ≤ 2 ^ 8 * (2 * n + 1) ^ 11 := by gcongr; exact two_pow_kOf_le n

theorem RR_le_Pmax (n : ℕ) : RR n ≤ PmaxOf n := by
  unfold PmaxOf
  have h1 : 1 ≤ rOf n := Nat.le_add_left 1 _
  calc RR n ≤ 2 * RR n := by omega
    _ = (2 * RR n) ^ 1 := (pow_one _).symm
    _ ≤ (2 * RR n) ^ rOf n := Nat.pow_le_pow_right (by have := RR_two_le n; omega) h1

theorem sOf_le_succ (n : ℕ) : sOf n ≤ 2 * n + 1 := by
  unfold sOf
  have he : 336175 * kOf n / 10 ^ 7 ≤ kOf n := by
    rw [Nat.div_le_iff_le_mul_add_pred (by norm_num)]; omega
  exact (Nat.pow_le_pow_right (by norm_num) he).trans (two_pow_kOf_le n)

/-- A bound on the need of the oracle at the moduli up to `Pmax`. -/
def oBound (s0 k0 n U : ℕ) : ℕ :=
  2 ^ s0 * ((n + 1) * ((U + 1) * ((2 * n + 2) * ((2 ^ 8 * (2 * n + 1) ^ 11 + 1) * 1)))) ^ k0

theorem polyBound_le_oBound {s0 k0 n U p : ℕ} (hp : p ≤ PmaxOf n) :
    polyBound s0 k0 [n, U, sOf n, p] ≤ oBound s0 k0 n U := by
  unfold polyBound oBound
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  have h1 := sOf_le_succ n
  have h2 := hp.trans (Pmax_le n)
  refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ k0)
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
    (Nat.mul_le_mul (by omega) (Nat.mul_le_mul_right 1 (by omega))))

theorem aTOP0_le (n : ℕ) : aTOP n 0 + 2 * RR n ≤ 12 * ((PmaxOf n + 1) * (n + 1) ^ 3) := by
  have hm := mOf_le n
  have hR := RR_le_Pmax n
  have h3 : (n + 1) ^ 3 = (n + 1) * (n + 1) * (n + 1) := by ring
  have hX1 : 1 ≤ (n + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hnn : n * n ≤ (n + 1) ^ 3 :=
    calc n * n ≤ (n + 1) * (n + 1) := Nat.mul_le_mul (by omega) (by omega)
      _ ≤ (n + 1) * (n + 1) * (n + 1) := Nat.le_mul_of_pos_right _ (by omega)
      _ = (n + 1) ^ 3 := by ring
  have hmn : mOf n * (n * n) ≤ (n + 1) ^ 3 :=
    calc mOf n * (n * n) ≤ n * (n * n) := Nat.mul_le_mul_right _ hm
      _ = n ^ 3 := by ring
      _ ≤ (n + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hRX : RR n ≤ (PmaxOf n + 1) * (n + 1) ^ 3 := by
    calc RR n ≤ (PmaxOf n + 1) * 1 := by omega
      _ ≤ _ := Nat.mul_le_mul_left _ hX1
  have hRN : RR n * (n * n) ≤ (PmaxOf n + 1) * (n + 1) ^ 3 :=
    Nat.mul_le_mul (by omega) hnn
  have hX : (n + 1) ^ 3 ≤ (PmaxOf n + 1) * (n + 1) ^ 3 := Nat.le_mul_of_pos_left _ (by omega)
  have e : 2 * RR n * (n * n) = 2 * (RR n * (n * n)) := by ring
  unfold aTOP aGT aCNT aUA aDONE aACT LL
  omega

/-- **The need of the host is polynomially bounded** if the need of the oracle is. -/
theorem filterNeed_poly {needo : List ℕ → Need} (h : PolyNeedN needo) :
    PolyNeed (filterNeed needo) := by
  obtain ⟨s0, k0, hb⟩ := h
  have hsup : ∀ n U, supW needo n U ≤ oBound s0 k0 n U ∧ supC needo n U ≤ oBound s0 k0 n U ∧
      supD needo n U ≤ oBound s0 k0 n U := by
    intro n U
    refine ⟨Finset.sup_le fun p hp => ?_, Finset.sup_le fun p hp => ?_,
      Finset.sup_le fun p hp => ?_⟩ <;>
    · have hp' : p ≤ PmaxOf n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hp)
      have := hb [n, U, sOf n, p]
      have := polyBound_le_oBound (s0 := s0) (k0 := k0) (U := U) hp'
      omega
  have hO : PolyBounded (fun n U => oBound s0 k0 n U) := by unfold oBound; growth_poly []
  refine PolyBounded.polyNeed ?_ ?_ ?_
  · refine PolyBounded.of_le (G := fun n U => 10 ^ 9 * ((n + 1) ^ 3 * (U + 1) *
      (2 ^ 8 * (2 * n + 1) ^ 11 + 1) * (2 ^ 8 * (2 * n + 1) ^ 11 + 1)) ^ 2 + oBound s0 k0 n U)
      (by growth_poly [hO]) fun n U => ?_
    simp only [filterNeed]
    have h1 := (hsup n U).1
    have hP := Pmax_le n
    have hR := (RR_le_Pmax n).trans hP
    have h2 : filterWord n U ≤ 10 ^ 9 * ((n + 1) ^ 3 * (U + 1) *
        (2 ^ 8 * (2 * n + 1) ^ 11 + 1) * (2 ^ 8 * (2 * n + 1) ^ 11 + 1)) ^ 2 := by
      unfold filterWord
      gcongr
    omega
  · refine PolyBounded.of_le (G := fun n U => 12 * ((2 ^ 8 * (2 * n + 1) ^ 11 + 1) * (n + 1) ^ 3) +
      oBound s0 k0 n U) (by growth_poly [hO]) fun n U => ?_
    simp only [filterNeed]
    have h1 := (hsup n U).2.1
    have h2 := aTOP0_le n
    have h3 : 12 * ((PmaxOf n + 1) * (n + 1) ^ 3) ≤
        12 * ((2 ^ 8 * (2 * n + 1) ^ 11 + 1) * (n + 1) ^ 3) := by
      have := Pmax_le n
      gcongr
    omega
  · refine PolyBounded.of_le (G := fun n U => oBound s0 k0 n U + 5) (by growth_poly [hO])
      fun n U => ?_
    simp only [filterNeed]
    have h1 := (hsup n U).2.2
    omega

/-- **The filtering host.** -/
theorem filter_host :
    (∀ (P : Program) (po : ℕ) (To : List ℕ → ℕ) (needo : List ℕ → Need),
      SolvesN oracleTask P po To needo →
      ∃ (R : Program) (p' : ℕ), Solves aeTask (P ++ R) p' (filterTime To) (filterNeed needo)) ∧
    (∀ needo, PolyNeedN needo → PolyNeed (filterNeed needo)) :=
  ⟨fun P po _ _ hsol => ⟨hostProcs P.length po, P.length + 18, filter_solves hsol⟩,
    fun _ h => filterNeed_poly h⟩

end Light.Filter2
