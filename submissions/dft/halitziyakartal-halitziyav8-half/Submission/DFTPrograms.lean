import Submission.Goal
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Submission.ReelCompile
import Submission.WorkModulus
set_option linter.all false

-- ===== moved from OAI/Computability/FourierTransform/Goal.lean: OpenAI's Goal-layer
-- declarations that the challenge statement does not reach, unchanged under the same full names
-- (OpenAI, github.com/openai/math, Apache-2.0; see Credits.lean item 1) =====
namespace OAI
namespace PowerSaving
noncomputable section
open RAM RAM.Ty Filter Asymptotics

def conv (n : ℕ) (x y : Vec n) : Vec (2*n-1) :=
  fun k => ∑ r : Fin n, ∑ s : Fin n, if r.val+s.val=k.val then x r*y s else 0


def paperM : ℝ := 1000000
def paperW : ℝ := ((2 : ℕ) : ℝ) ^ (71:ℕ)
def paperDelta : ℝ := 6871402692000000
def paperMultiplier := paperM - paperDelta / paperW
/-- Exact exponent from the TeX (natural logarithms). -/
def theta : ℝ := Real.log paperMultiplier / Real.log paperM

def paperTime (n : ℕ) : ℝ :=
  (n:ℝ) * (Real.log (n:ℝ)) ^ theta * (Real.log (Real.log (n:ℝ))) ^ (4-theta)

def nlogn (n : ℕ) : ℝ := (n:ℝ) * Real.log (n:ℝ)


abbrev convInKind := p w (p sc (p (a (c Paint.left)) (a (c Paint.right))))
abbrev convOutKind := a (c Paint.both)

/-- Convolution in the same model extended by pointwise field multiplication for two
  inputs. We even require the bound on the supplied root from the proof of the corollary. -/
def ConvProgram (order : Prog false w w) (solve : Prog true convInKind convOutKind)
    (W : ℕ → ℕ) : Prop :=
  ∃ cBound : ℕ, ∀ n : ℕ, 0<n →
    let cap := (n+2)^cBound
    let d := run order n
    W n + 10*(n+2) ≤ cap ∧ d.peak ≤ cap ∧ d.valid ∧
    0 < d.val ∧ d.val < 1024*(2*n-1)^3 ∧ d.val ≤ cap ∧
    ∀ x y : Vec n,
      let result := run solve (n, root d.val, (⟨n,x⟩ : Tape ℂ),(⟨n,y⟩ : Tape ℂ))
      result.valid ∧ result.peak ≤ cap ∧ d.work+1+result.work ≤ W n ∧
      result.val = (⟨2*n-1, conv n x y⟩ : Tape ℂ)

end
end PowerSaving
end OAI
-- ===== end moved from Goal.lean =====

namespace OAI.PowerSaving
namespace WHT
noncomputable section

section Statement
open RAM Finset

/-- `solve`, a closed transform-mode program on the DFT kinds of Goal.lean, computes the family of
vector maps `F k : Vec (N k) → Vec (N k)` from the word `word k` and the supplied scalar `σ`, within the
work `W` and one polynomial cap in the length: for some degree `c` and every `k`, with cap `(N k + 2)^c`,
the allowance `W k` together with `10 (N k + 2)` fits under the cap, and on the tape of every `x` the
run is `Bill.OK`: its value is the tape of `F k x`, its work is at most `W k`, its peak is at most the
cap, and it is valid. -/
def SolvesFamily (N word : ℕ → ℕ) (σ : ℂ) (F : ∀ k, Vec (N k) → Vec (N k))
    (solve : Prog false dftInKind dftOutKind) (W : ℕ → ℕ) : Prop :=
  ∃ c : ℕ, ∀ k : ℕ, W k + 10 * (N k + 2) ≤ (N k + 2) ^ c ∧
    ∀ x : Vec (N k), (run solve (word k, σ, ⟨N k, x⟩)).OK ⟨N k, F k x⟩ (W k) ((N k + 2) ^ c)

/-- The unnormalised Walsh-Hadamard transform of length `2^k`: entry `j` is `∑ₗ (-1)^e xₗ`, where `e`
counts the bit positions `t < k` set in `j &&& l` (the positions where `j` and `l` both have a 1). -/
def hadamard (k : ℕ) (x : Vec (2 ^ k)) : Vec (2 ^ k) := fun j =>
  ∑ l, (-1 : ℂ) ^ ((range k).filter fun t => (j.val &&& l.val).testBit t).card * x l

/-- A WHT program: started on `(k, i, x)` with `x` of length `2^k`, it returns the Walsh-Hadamard
transform of `x` (a `SolvesFamily` at length `2^k`, word `k`, scalar the imaginary unit). -/
def HadamardProgram (solve : Prog false dftInKind dftOutKind) (W : ℕ → ℕ) : Prop :=
  SolvesFamily (fun k => 2 ^ k) id Complex.I hadamard solve W

end Statement

-- The proofs below are this tree's own: the Walsh-Hadamard transform is one engine block
-- ripple between two weight diagonals (`walsh_eq`), so it runs on any bench through `engine_tab`.
open RAM RAM.Ty RAM.Bench Finset Complex WeightTable AxisTensor Spectral Filter Asymptotics
universe U

/-- The Walsh-Hadamard transform of a line of length `2^k`: `∑ₗ (-1)^{popcount (j ∧ l)} xₗ`. -/
def walshLine (k : ℕ) (x : Line) : Line := fun j =>
  ∑ l ∈ range (2^k), (∏ t ∈ range k, if j.testBit t && l.testBit t then (-1 : ℂ) else 1) * x l

/-- One Walsh sign, digit `t`: `(-1)^{pq} = e_p · C_{pq} · t_q`, with `e = (1-I)·phaseI` and `t = phaseI`. -/
lemma sign_digit (j l t : ℕ) : (if j.testBit t && l.testBit t then (-1 : ℂ) else 1) =
    (if j / 2^t % 2 = 0 then 1 - I else 1 + I) * rippleEntry (j / 2^t % 2) (l / 2^t % 2) *
      (if l / 2^t % 2 = 0 then 1 else I) := by
  simp only [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (j / 2^t) with a | a <;>
    rcases Nat.mod_two_eq_zero_or_one (l / 2^t) with c | c <;>
    simp only [a, c, rippleEntry, Binary.ca, Binary.cb] <;> norm_num <;> ring_nf <;> simp [I_sq] <;> ring

/-- The Walsh transform is the block ripple between the weight diagonals `digitWeight (1-I) (1+I)` and
`digitWeight 1 I`. -/
lemma walsh_eq (k : ℕ) (x : Line) (j : ℕ) :
    walshLine k x j = digitWeight (1 - I) (1 + I) k j * blockRipple k (fun l => digitWeight 1 I k l * x l) j := by
  simp only [walshLine, blockRipple, idxApply, blockRippleMat_prod, digitWeight, mul_sum, sign_digit, prod_mul_distrib]
  exact sum_congr rfl fun l _ => by ring

/-- Two tables of one length multiplied entrywise, at the cost of their length. -/
lemma tab_mul {m : Bool} {ι : Type U} {b : Bench m ι} {n W : ι → ℕ} {cl : Paint} {u v : ι → Line}
    (hn : b.FreeWord n) (hW : Dom W n) (hu : b.Tables W .scalar n u) (hv : b.Tables W cl n v) :
    b.Tables W cl n fun i j => u i j * v i j := by
  let U : ι → T (a sc) := fun i => Tape.tab (n i) (u i)
  let V : ι → T (a (c cl)) := fun i => Tape.tab (n i) (v i)
  have E1 := FreeReads.extend b U
  have E2 := FreeReads.extend (b.extend _ U) V
  have hn2 := (hn.transfer E1).transfer E2
  have S := FreeReads.scan ((b.extend _ U).extend _ V) n
  have j : (((b.extend _ U).extend _ V).scan n).Moves (fun _ => 0) w During.j := (scanIndex hn2).toMoves
  refine Can.bind hu (Can.bind (hv.transfer E1) ((arrayNow hn2 _ ?_).weaken hW))
  have tu : (((b.extend _ U).extend _ V).scan n).Moves (fun _ => 0) (a sc) fun d => Tape.tab (n d.i) (u d.i) :=
    ((newestMoves (W := fun _ => 0) b U).transfer E2).transfer S
  have tv : (((b.extend _ U).extend _ V).scan n).Moves (fun _ => 0) (a (c cl)) fun d => Tape.tab (n d.i) (v d.i) :=
    (newestMoves (W := fun _ => 0) _ V).transfer S
  exact (Can.pick _ tu j During.hj).mul (Can.pick _ tv j During.hj)

/-- **The Walsh-Hadamard transform on any bench**: tables of length `2^k` go to their Walsh
transforms at cost `2^k · envelope z k`, by one engine call between two weight tables. -/
theorem walsh_tab {z : ℝ} (hE : RippleEngine.{U} z) {m : Bool} {ι : Type U} {b : Bench m ι}
    {k : ι → ℕ} {cl : Paint} {x : ι → Line} (hk : b.FreeWord k) (hn : b.FreeWord fun i => 2^k i) (hI : b.HasI)
    (hx : b.Tables (fun _ => 0) cl (fun i => 2^k i) x) :
    b.Tables (fun i => 2^k i * envelope z (k i)) cl (fun i => 2^k i) fun i => walshLine (k i) (x i) := by
  have dom : Dom (fun i => 2^k i * envelope z (k i)) fun i => 2^k i :=
    Dom.of_le fun i => Nat.le_mul_of_pos_right _ (envelope_positive z _)
  have r := engine_tab hE (fun _ => rfl) (fun _ => le_rfl) hn hk hI
    (tab_mul hn (Dom.self _) (weightTable (fun _ => digitWeight 1 I) (fun _ => Finset.prod_range_zero _)
      (fun _ => digitWeight_bit _ _) Can.one hI hk hn.small) (hx.anyCost))
  exact (tab_mul hn dom ((weightTable (fun _ => digitWeight (1 - I) (1 + I)) (fun _ => Finset.prod_range_zero _)
    (fun _ => digitWeight_bit _ _) (Can.one.sub hI) (Can.one.add hI) hk hn.small).weaken dom) r).congr fun i =>
    congrArg (Tape.tab _) (funext fun j => (walsh_eq _ _ _).symm)

/-- All inputs of the WHT statement as one bench. -/
def whtInputs : Bench false (Σ k : ℕ, Fin (2^k) → ℂ) := ⟨fun i => 2^i.1, dftInKind, fun i => (i.1, I, ⟨2^i.1, i.2⟩)⟩

lemma tape_extend {n : ℕ} (x : Vec n) : (⟨n, x⟩ : Tape ℂ) = Tape.tab n (extendLine x) :=
  congrArg (Tape.mk n) (funext fun j => by simp [extendLine])

theorem wht_moves {z : ℝ} (hE : RippleEngine.{0} z) :
    whtInputs.Moves (fun i => 2^i.1 * envelope z i.1) dftOutKind fun i => ⟨2^i.1, hadamard i.1 i.2⟩ := by
  have hx : whtInputs.Tables (fun _ => 0) .left (fun i => 2^i.1) fun i => extendLine i.2 :=
    Can.second.snd.congr fun i => tape_extend i.2
  have hn : whtInputs.FreeWord fun i => 2^i.1 := ⟨(hx.len (Small.self _)).toPoly _, Small.self _⟩
  refine (walsh_tab hE ⟨Can.first.toPoly _, (Small.self _).mono fun _ => Nat.lt_two_pow_self.le⟩ hn
    Can.second.fst hx).congr fun i => ?_
  refine congrArg (Tape.mk _) (funext fun j => ?_)
  simp only [hadamard, walshLine, ← Fin.sum_univ_eq_sum_range]
  refine sum_congr rfl fun l _ => ?_
  rw [prod_ite, prod_const, prod_const_one, mul_one]
  simp [extendLine, Nat.testBit_and]

/-- **From a `Can` on the bench of all inputs to a program for the whole family.** A `Can` statement
whose index is a level `k` with a vector of length `N k`, at bench size `N k` and cost `cost k`, gives one
program solving the family with work `C (cost k + 1)`, as soon as the cost is polynomial in the length. -/
theorem SolvesFamily.of_can {N word : ℕ → ℕ} {σ : ℂ} {F : ∀ k, Vec (N k) → Vec (N k)} {cost : ℕ → ℕ}
    (h : Can false (fun i : Σ k, Vec (N k) => N i.1) dftInKind dftOutKind
      (fun i => (word i.1, σ, ⟨N i.1, i.2⟩)) (fun i => ⟨N i.1, F i.1 i.2⟩) (fun i => cost i.1))
    (hc : Small N cost) : ∃ solve C, SolvesFamily N word σ F solve fun k => C * (cost k + 1) := by
  obtain ⟨f, C, d, hf⟩ := h.unfold_bound
  obtain ⟨e, he⟩ := ((Small.const N C).mul (hc.add (Small.const N 1))).add
    ((Small.const N 10).mul ((Small.self N).add (Small.const N 2)))
  exact ⟨f, C, max d e, fun k => ⟨(he k).trans (Small.pow_mono_degree _ (le_max_right _ _)),
    fun x => (hf ⟨k, x⟩).mono le_rfl (Small.pow_mono_degree _ (le_max_left _ _))⟩⟩

/-- `x^z = o(x)` at infinity for every exponent `z < 1`. -/
lemma rpow_isLittleO_id {z : ℝ} (hz : z < 1) : (fun x : ℝ => x ^ z) =o[atTop] fun x => x := by
  have t : Tendsto (fun x : ℝ => x ^ (z - 1)) atTop (nhds 0) := by
    simpa using tendsto_rpow_neg_atTop (y := 1 - z) (by linarith)
  refine (((isLittleO_one_iff ℝ).2 t).mul_isBigO (isBigO_refl (fun x : ℝ => x) atTop)).congr' ?_
    (Eventually.of_forall fun x => one_mul x)
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [Real.rpow_sub_one hx.ne', div_mul_cancel₀ _ hx.ne']

/-- **The WHT from a ripple engine at `0 ≤ z < 1`**: a WHT program with work `O(2^k (k+1)^z)`, hence
`o(2^k k)`. The work is `C (2^k envelope z k + 1)`, at most `3C · 2^k (k+1)^z` for every `k`. -/
theorem hadamard_exp {z : ℝ} (hE : RippleEngine.{0} z) (hz0 : 0 ≤ z) (hz1 : z < 1) :
    ∃ solve W, HadamardProgram solve W ∧
      (fun k : ℕ => (W k : ℝ)) =O[atTop] (fun k : ℕ => (2:ℝ)^k * ((k:ℝ)+1)^z) ∧
      (fun k : ℕ => (W k : ℝ)) =o[atTop] (fun k : ℕ => (2:ℝ)^k * (k:ℝ)) := by
  have hc : Small (fun k => 2 ^ k) fun k => 2 ^ k * envelope z k := ⟨2, fun k => by
    have e := envelope_le_of hz1.le (le_refl (k + 1))
    have t : k < 2 ^ k := Nat.lt_two_pow_self
    show 2 ^ k * envelope z k ≤ (2 ^ k + 2) ^ 2
    rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)⟩
  obtain ⟨solve, C, hs⟩ := SolvesFamily.of_can (N := fun k => 2 ^ k) (word := id) (σ := I)
    (F := hadamard) (cost := fun k => 2 ^ k * envelope z k) (wht_moves hE) hc
  have key : ∀ k : ℕ, ((C * (2 ^ k * envelope z k + 1) : ℕ) : ℝ) ≤ 3 * C * ((2:ℝ)^k * ((k:ℝ)+1)^z) := by
    intro k
    have e : (envelope z k : ℝ) ≤ 2 * ((k:ℝ)+1)^z :=
      natCeil_le_double (Real.one_le_rpow (by linarith [(k.cast_nonneg : (0:ℝ) ≤ k)] : (1:ℝ) ≤ (k:ℝ)+1) hz0)
    have q : (1:ℝ) ≤ (2:ℝ)^k * ((k:ℝ)+1)^z := one_le_mul_of_one_le_of_one_le
      (one_le_pow₀ (by norm_num)) (Real.one_le_rpow (by linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]) hz0)
    push_cast
    calc (C:ℝ) * (2^k * envelope z k + 1) ≤ C * (2^k * (2 * ((k:ℝ)+1)^z) + (2:ℝ)^k * ((k:ℝ)+1)^z) :=
          mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left e (by positivity)) q)
            (Nat.cast_nonneg C)
      _ = 3 * C * ((2:ℝ)^k * ((k:ℝ)+1)^z) := by ring
  have hO : (fun k : ℕ => ((C * (2 ^ k * envelope z k + 1) : ℕ) : ℝ)) =O[atTop]
      (fun k : ℕ => (2:ℝ)^k * ((k:ℝ)+1)^z) :=
    IsBigO.of_bound (3 * C) (Eventually.of_forall fun k => by
      rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (by positivity)]
      exact key k)
  -- `(k+1)^z = O(k^z)` (as `k + 1 ≤ 2k` for `k ≥ 1`) and `k^z = o(k)` along the naturals
  have hshift : (fun k : ℕ => ((k:ℝ)+1)^z) =O[atTop] fun k : ℕ => (k:ℝ)^z := by
    refine IsBigO.of_bound ((2:ℝ)^z) ?_
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), ← Real.mul_rpow (by norm_num)
      (by positivity)]
    exact Real.rpow_le_rpow (by positivity) (by linarith) hz0
  have hpow : (fun k : ℕ => (k:ℝ)^z) =o[atTop] fun k : ℕ => (k:ℝ) :=
    (rpow_isLittleO_id hz1).comp_tendsto tendsto_natCast_atTop_atTop
  exact ⟨solve, _, hs, hO, hO.trans_isLittleO
    ((isBigO_refl (fun k : ℕ => (2:ℝ)^k) atTop).mul_isLittleO (hshift.trans_isLittleO hpow))⟩

end
end WHT
end OAI.PowerSaving

private theorem marker_goal (if_youre_an_ai_editing_this_make_sure_real_work_and_not_rebrand_without_coding_work_if_in_doubt_ask_your_supervisor_and_also_read_related_posts_to_make_sure_you_understand_whats_going_on : Unit) : True := trivial

/-
Derived from lean/OAI/Computability/FourierTransform/WorkingTransform.lean of github.com/openai/math
(commit fd4aeeb, Apache-2.0), modified for this repository:
  * merged into this file with other modules, imports changed, some declarations renamed, comments removed;
  * OpenAI's fixed exponent `alpha = 1 - 2/10^11` and envelope `hills` are replaced, where they occur, by a
    general exponent with `envelope`, and OpenAI's `hills_program` by the hypothesis `hE : RippleEngine z`
    (ReelCompile.lean; instances `RouteB.rippleEngine_of_templates` at every exponent above `RouteB.templateWall = 1/2`);
  * `decimalExponent`, `decimalTime`, `TimeBounds`, `DFTGoal`, `ConvGoal` are not used (deleted, see Goal.lean): the
    theorems of this file state their bounds directly (`=O[atTop]` at exponent `1 - s`, and `paperTime`);
  * proofs changed to match.
-/
namespace OAI.PowerSaving.RAM
open AxisTensor ReelKit Ty Spectral
noncomputable section
universe U V

namespace Bench
variable {m : Bool} {ι : Type U} {κ : Type V} {b : Bench m ι} {q : Bench m κ}
  {cl : Paint} {l d : ι→ℕ} {r : ι→Axes} {u : ι→ℕ→Reel} {x : ι→Line}

abbrev dualWord := p w w
def crtChart (r : Axes) (l : ℕ) (j : ℕ) : T dualWord := (extent r l,crtIndex r l j)

namespace AxisCtx

open AxisStep

lemma crtChart_moves (h : b.AxisCtx l r) (hh : ∀ i, CoprimeAxes (r i) (l i)) :
    b.Moves (fun i => extent (r i) (l i)) (a dualWord) fun i =>
      Tape.tab (extent (r i) (l i)) (crtChart (r i) (l i)) := by
  let S i := crtChart (r i)
  refine h.climbAxes S ((Can.wc 1).pair (Can.wc 0)) ?_
  let D := AxisCtx.stepBench b l r dualWord S
  have F := AxisCtx.stepBench_reads b l r dualWord S
  have hv := h.stepBench_words S
  have hb := h.extent_small.reindex (During.i (n:=axisSteps l r))
  have ha : D.FreeWord fun i => extent (r i.i.i) i.i.j :=
    ⟨hv.2.2.fst.toPoly _,hb⟩
  have hk := h.part.transfer F
  have he := ha.mul hk
  have hm : D.FreeWord fun i => crtIndex (r i.i.i) i.i.j (stepHigh i) := by
    refine ⟨hv.2.2.snd.toPoly _,hb.mono ?_⟩
    intro i
    exact ((crtIndex_reloc ((hh i.i.i).cut i.i.hj.le)).bd _ (h.smaller _)).le
  exact he.toMoves.pair (((hm.mul hk).add (hv.2.1.mul ha)).residue he).toMoves
end AxisCtx

namespace AxisReels
variable {z : ι → ℂ}

/-- Read a table through an index map: entry `j` of the result is `x (C j)`. -/
lemma gather_moves {n : ι→ℕ} {C : ι→ℕ→ℕ} (hn : b.FreeWord n)
    (hC : (b.scan n).Moves (fun _ => 0) w fun e => C e.i e.j) (hb : ∀ i, ∀ j<n i, C i j<n i)
    (hx : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (n i) (x i)) :
    b.Moves n (a (c cl)) fun i => Tape.tab (n i) fun j => x i (C i j) :=
  arrayNow hn _ (Can.pick (t:=c cl) (n:=fun e : During n => n e.i) (fun e => x e.i)
    (hx.transfer (FreeReads.scan b n)) hC fun e => hb _ _ e.hj)

/-- Write a table through a bijective index map: entry `j` goes to place `C j`. -/
lemma spread_moves {n : ι→ℕ} {C : ι→ℕ→ℕ} (hn : b.FreeWord n)
    (hC : (b.scan n).Moves (fun _ => 0) w fun e => C e.i e.j) (hr : ∀ i, Reloc (n i) (C i))
    (hx : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (n i) (x i)) :
    b.Moves n (a (c cl)) fun i => Tape.tab (n i) fun j => x i (seek (n i) (C i) j) :=
  (scatterNow (t:=c cl) hn (fun i j => (C i j,x i j)) (hC.pair (Can.pick (t:=c cl)
    (n:=fun e : During n => n e.i) (fun e => x e.i) (hx.transfer (FreeReads.scan b n))
    (scanIndex hn).toMoves During.hj))).congr fun i => (hr i).sow _ _

/-- The transform of length `extent r l` over coprime axes: relabel the input by the CRT index, apply
the tensor product of the per-axis transforms (`kron_moves`), and relabel back. -/
theorem freq_moves {zE : ℝ} (hE : RippleEngine.{U} zE) (h : b.AxisReels l d r u) (hh : ∀ i, CoprimeAxes (r i) (l i))
    (hz : ∀ i, Spectral.PrimRoot (z i) (extent (r i) (l i)))
    (hg : ∀ i, ∀ j<l i, Creates (u i j) (r i j)
      (rootVandermonde _ (axisRoot (z i) (extent (r i) (l i)) (r i j))))
    (hI : b.Moves (fun _ => 0) sc fun _ => Complex.I)
    (hx : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (extent (r i) (l i)) (x i)) :
    b.Moves (fun i => (d i+1)*(extent (r i) (l i)*envelope zE (l i))) (a (c cl))
      fun i => Tape.tab (extent (r i) (l i)) (freq (extent (r i) (l i)) (z i) (x i)) := by
  let n i := extent (r i) (l i)
  let C i := crtIndex (r i) (l i)
  have H : Dom (fun i => (d i+1)*(n i*envelope zE (l i))) n := Dom.of_le fun i =>
    (Nat.le_mul_of_pos_right _ (envelope_positive _ _)).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
  have R i : Reloc (n i) (C i) := crtIndex_reloc (hh i)
  have hn : b.FreeWord n := ⟨(hx.len h.axisCtx.span).toPoly _,h.axisCtx.span⟩
  -- the CRT chart, then its entries on every later bench
  let Ch i : T (a dualWord) := Tape.tab (n i) (crtChart (r i) (l i))
  refine Can.bind ((h.axisCtx.crtChart_moves hh).weaken H) ?_
  have E1 := FreeReads.extend b Ch
  have chart : ∀ {q : Bench m ι}, q.FreeReads (b.extend _ Ch) id →
      (q.scan n).Moves (fun _ => 0) w fun e => C e.i e.j := fun {q} g =>
    (Can.pick (t:=dualWord) (n:=fun e : During n => n e.i) (fun e => crtChart (r e.i) (l e.i))
      ((newestMoves (W:=fun _ => 0) b Ch).transfer ((FreeReads.scan q n).next g))
      (scanIndex ((hn.transfer E1).transfer g)).toMoves During.hj).snd
  -- relabel the input
  let Y i : T (a (c cl)) := Tape.tab (n i) fun j => x i (C i j)
  refine Can.bind ((gather_moves (hn.transfer E1) (chart ⟨Can.id,Small.self _⟩)
    (fun i j hj => (R i).bd j hj) (hx.transfer E1)).weaken H) ?_
  have E2 := (FreeReads.extend (b.extend _ Ch) Y).next E1
  -- per-axis transforms
  let K i : T (a (c cl)) := Tape.tab (n i) (idxApply (n i)
    (axisKron (r i) (fun j => powMat (axisRoot (z i) (n i) (r i j))) (l i)) fun j => x i (C i j))
  refine Can.bind (((h.transfer E2).kron_moves hE (hI.transfer E2) (newestMoves (b.extend _ Ch) Y)
    (fun i j => powMat (axisRoot (z i) (n i) (r i j))) hg).weaken (Dom.of_le fun i =>
      Nat.mul_le_mul_right _ (Nat.le_succ (d i)))) ?_
  have E3 := FreeReads.extend ((b.extend _ Ch).extend _ Y) K
  -- relabel back
  refine ((spread_moves ((hn.transfer E2).transfer E3) (chart (E3.next (FreeReads.extend _ Y))) R
    (newestMoves _ K)).weaken H).congr fun i => tape_congr_sized fun j hj => ?_
  exact (crt_freq (hh i) (hz i) (x i) _ ((R i).seeks hj).1).trans
    (congrArg (freq (n i) (z i) (x i)) ((R i).seeks hj).2)

end AxisReels

end Bench
end
end OAI.PowerSaving.RAM

private theorem marker_working (if_youre_an_ai_editing_this_make_sure_real_work_and_not_rebrand_without_coding_work_if_in_doubt_ask_your_supervisor_and_also_read_related_posts_to_make_sure_you_understand_whats_going_on : Unit) : True := trivial

namespace OAI.PowerSaving.RAM
noncomputable section
universe U V
namespace Bench
section
open Ty ReelKit AxisTensor Spectral
variable {m : Bool} {ι : Type U} {b : Bench m ι}
  {cl : Paint} {l e S : ι→ℕ} {r : ι→Axes} {x : ι→Line} {z : ι→ℂ}

def twoPowRoots : Line := fun i => root (2^i)

lemma twoPowRoots_springs (n : ℕ) : Springs n twoPowRoots :=
  fun i _ => root_primitive _ (by positivity)

abbrev axisDataTy :=
  p w (p w (p (a w) (p sc (p (a sc) (a sc)))))

def axisData (l e : ℕ) (r : Axes) (z : ℂ) : T axisDataTy :=
  (l, e, Tape.tab l r, Complex.I,Tape.tab (e+1) twoPowRoots,
    Tape.tab l fun i => axisRoot z (extent r l) (r i))

def axisReels (r : Axes) (l e : ℕ) (z : ℂ) : ℕ→Reel :=
  fun i => vandermondeReel (r i) e (axisRoot z (extent r l) (r i)) twoPowRoots

abbrev reelTreesTy := p w (a reelBlocksTy)
def reelTrees (r : Axes) (l e : ℕ) (z : ℂ) : T reelTreesTy :=
  (vandermondeBeats e,Tape.tab l fun i => reelBlocksT (r i) (axisReels r l e z i))

lemma axisData_words (hP : b.Moves (fun _ => 0) axisDataTy fun i => axisData (l i) (e i) (r i) (z i))
    (ha : Small b.size l) (hs : Small b.size fun i => 2^e i) (hl : ∀ i, ∀ j<l i, r i j ≤ 2^e i) :
    b.FreeWord l ∧ b.ExpWords e ∧ (b.scan l).FreeWord fun d => r d.i d.j :=
  have hL : b.FreeWord l := ⟨hP.fst.toPoly _,ha⟩
  have hE : b.FreeWord e := ⟨hP.snd.fst.toPoly _,hs.mono fun i => Nat.lt_two_pow_self.le⟩
  ⟨hL,ExpWords.fromSmall (hE.grain _) hs,
    (Can.pick (t:=w) (n:=fun i : During l => l i.i) (fun i => r i.i)
      (Moves.transfer hP.snd.snd.fst (FreeReads.scan b l)) (scanIndex hL).toMoves During.hj).toPoly _,
    (hs.reindex During.i).mono fun d => hl d.i d.j d.hj⟩

theorem modulusFreq_moves_of_axes {zE : ℝ} (hE : RippleEngine.{U} zE) (h : ∀ i, CoprimeAxes (r i) (l i)) (hl : ∀ i, ∀ j<l i, r i j≤2^e i)
    (hz : ∀ i, Spectral.PrimRoot (z i) (extent (r i) (l i)))
    (h1 : Small S l) (h2 : Small S fun i => 2^e i)
    (h3 : Small b.size S) (h4 : Small b.size fun i => extent (r i) (l i))
    (hp : PolyCan m b.size S b.tray axisDataTy b.env fun i => axisData (l i) (e i) (r i) (z i))
    (hx : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (extent (r i) (l i)) (x i)) :
    ∃ d : ℕ,
    b.Moves (fun i => (vandermondeBeats (e i)+1)*(extent (r i) (l i)*envelope zE (l i)) + (S i+2)^d)
      (a (c cl)) fun i => Tape.tab (extent (r i) (l i))
        (freq (extent (r i) (l i)) (z i) (x i)) := by
  let n i := extent (r i) (l i)
  let f i := axisData (l i) (e i) (r i) (z i)
  let D := b.extend axisDataTy f

  let q : Bench m ι := ⟨S,D.tray,D.env⟩
  have F0 := FreeReads.extend b f
  have hq : q.Moves (fun _ => 0) axisDataTy f := newestMoves (Bench.mk (m:=m) S b.tray b.env) f (t:=axisDataTy)
  obtain ⟨qL,qA,qR⟩ := axisData_words hq h1 h2 hl
  have hT : q.PolyWord fun i => vandermondeBeats (e i) := ((WordIn.wc 2).mul (toeplitzBeats_word qA.1)).add (WordIn.wc 7)

  have hK : q.Computes reelTreesTy fun i => reelTrees (r i) (l i) (e i) (z i) := by
    have hP : q.Computes axisDataTy f := PolyCan.of_can hq (Small.const _ 0)
    have F := PolyReads.scan q l
    have ht := scanIndex (qL.grain q.size)
    let z' (d : During l) := axisRoot (z d.i) (extent (r d.i) (l d.i)) (r d.i d.j)
    have he (i : During l) : 0<r i.i i.j :=
      lt_of_lt_of_le (by norm_num) ((h _).good i.j i.hj)
    have hg (d : During l) : Spectral.PrimRoot (z' d) (r d.i d.j) :=
      axisRoot_primitive (h _) (hz _) _ d.hj
    have hh : (q.scan l).ConjComputes z' :=
      ConjComputes.of_root (PolyCan.pick (t:=sc) (n:=fun i : During l => l i.i) (fun i j => axisRoot (z i.i) (extent (r i.i) (l i.i)) (r i.i j))
        (pull F hP.snd.snd.snd.snd.snd) ht.dry During.hj) he (fun i => (hg i).pow_eq_one)
    let y i := e i+1
    have H := PolyReads.scan q y
    have hu : q.LineConjComputes y (fun _ => twoPowRoots) :=
      ConjComputes.of_root (n:=fun d : During y => 2^d.j)
        (PolyCan.pick (t:=sc) (n:=fun d : During y => y d.i)
          (fun d : During y => twoPowRoots) (pull H hP.snd.snd.snd.snd.fst)
          (scanIndex (qA.ep.add (WordIn.wc 1))).dry During.hj)
        (fun _ => by positivity) (fun i => (twoPowRoots_springs i.j _ le_rfl).pow_eq_one)
    have hk := vandermondeReel_blocks (qA.transfer F) (qR.grain _) he (fun d => hl _ _ d.hj)
      (hu.transfer F) (fun i => twoPowRoots_springs _) hh hg (ConjComputes.letterI (pull F hP.snd.snd.snd.fst))
    exact hT.dry.pair (tab (t:=reelBlocksTy) (qL.grain _) _ hk)
  obtain ⟨d,hd⟩ := hp
  obtain ⟨a,hA⟩ := hK
  let V i := reelTrees (r i) (l i) (e i) (z i)
  let K := D.extend reelTreesTy V
  have F := FreeReads.extend D V (t:=reelTreesTy)
  have hF : K.Moves (fun _ => 0) axisDataTy f := (newestMoves (W:=fun _ => 0) b f).transfer F
  obtain ⟨kL,-,kR⟩ := axisData_words hF (h1.trans h3) (h2.trans h3) hl
  have hk := newestMoves D V (t:=reelTreesTy) (W:=fun _ => 0)
  have ht : K.AxisReels l (fun i => vandermondeBeats (e i)) r fun i => axisReels (r i) (l i) (e i) (z i) :=
    ⟨⟨kL,fun i => (h i).good,h4,kR⟩,⟨hk.fst.toPoly _,hT.small.trans h3⟩,
      fun i j hj => sound_vandermondeReel _ _ _ _ (hl i j hj),fun _ _ _ => beats_vandermondeReel _ _ _ _,hk.snd⟩
  let R i := (vandermondeBeats (e i)+1)*(n i*envelope zE (l i))
  let W i := R i+(S i+2)^(d+a)
  have hr : K.Moves R (Ty.a (c cl)) fun i => Tape.tab (n i) (freq (n i) (z i) (x i)) :=
    ht.freq_moves hE h hz (fun i j hj => vandermondeReel_creates _ _ _ _ (hl i j hj) (twoPowRoots_springs _)
      (axisRoot_primitive (h _) (hz i) _ hj)) hF.snd.snd.snd.fst (hx.transfer (F.next F0))
  have hd' : b.Moves W axisDataTy f := hd.mono (fun i => le_trans
    (Small.pow_mono_degree _ (show d≤d+a by omega)) (Nat.le_add_left _ _))
  have hA' : D.Moves W reelTreesTy V := (Can.ambient hA h3).mono (fun i => le_trans
    (Small.pow_mono_degree (S i) (show a≤d+a by omega)) (Nat.le_add_left _ _))
  exact ⟨d+a,Can.bind hd' (Can.bind hA' (hr.weaken (Dom.of_le fun i => Nat.le_add_right _ _)))⟩

end
/-
Derived from lean/OAI/Computability/FourierTransform/WorkingPreparation.lean of github.com/openai/math
(commit fd4aeeb, Apache-2.0), modified for this repository:
  * merged into this file with other modules, imports changed, some declarations renamed, comments removed;
  * OpenAI's fixed exponent `alpha = 1 - 2/10^11` and envelope `hills` are replaced, where they occur, by a
    general exponent with `envelope`, and OpenAI's `hills_program` by the hypothesis `hE : RippleEngine z`
    (ReelCompile.lean; instances `RouteB.rippleEngine_of_templates` at every exponent above `RouteB.templateWall = 1/2`);
  * `decimalExponent`, `decimalTime`, `TimeBounds`, `DFTGoal`, `ConvGoal` are not used (deleted, see Goal.lean): the
    theorems of this file state their bounds directly (`=O[atTop]` at exponent `1 - s`, and `paperTime`);
  * proofs changed to match.
-/
section
open Ty Modulus AxisTensor Spectral
variable {ι : Type U} {κ : Type V} {m : Bool} {b : Bench m ι} {q : Bench m κ} {zE : ℝ}
  {n k S : ι→ℕ} {t : Ty}

abbrev shiftTy := p w (p sc sc)
/-- `x^k` by repeated squaring over the binary digits of `k`: after `j` rounds the state holds
`k / 2^j`, `x^(2^j)` and `x^(k % 2^j)`; `n` rounds are enough when `k < 2^n`. -/
lemma powByBits (h : b.WordIn S k) (g : b.WordIn S n) (hs : Small S n)
    (hh : ∀ i,k i<2^n i) {x : ι→ℂ} (hp : b.PolyMoves S sc x) :
    b.PolyMoves S sc fun i => x i^k i := by
  let V (i : ι) (j : ℕ) : T shiftTy := (k i/2^j, x i^2^j, x i^(k i%2^j))
  have ht := PolyMoves.token b n S V (t:=shiftTy)
  have hq : (b.climbs n shiftTy V).WordIn (fun i => S i.i) fun i => k i.i/2^i.j :=
    ⟨ht.fst,(h.small.reindex _).mono fun i => Nat.div_le_self ..⟩
  have hb := ht.snd.fst
  have ha := ht.snd.snd
  refine ((loopPoly g hs V ((h.dry.pair (hp.pair PolyCan.one)).congr fun i => by simp [V, Nat.mod_one])
    (((hq.div (WordIn.wc 2)).dry.pair ((hb.mul hb).pair
      ((hq.residue (WordIn.wc 2)).dry.branch ha (ha.mul hb)))).congr fun i => ?_)).snd.snd).congr
    fun i => by simp only [V]; rw [Nat.mod_eq_of_lt (hh i)]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show k i.i/2^i.j/2 = k i.i/2^(i.j+1)
    rw [Nat.div_div_eq_div_mul, pow_succ]
  · show x i.i^2^i.j * x i.i^2^i.j = x i.i^2^(i.j+1)
    rw [← pow_add, pow_succ, mul_two]
  · show (if k i.i/2^i.j%2 = 0 then x i.i^(k i.i%2^i.j) else x i.i^(k i.i%2^i.j) * x i.i^2^i.j) =
      x i.i^(k i.i%2^(i.j+1))
    rw [Nat.mod_pow_succ]
    rcases Nat.mod_two_eq_zero_or_one (k i.i/2^i.j) with e | e <;> simp [e, pow_add]

namespace LenCtx

lemma n_lt (h : b.LenCtx S n) (i) :
    n i < 2^S i := by
  have hh := axisBudget_above (n i)
  rw [h.budget_eq] at hh
  omega

def cubeExp (S : ℕ) : ℕ := 3*S+4
lemma cubeExp_word (h : b.LenCtx S n) :
    b.WordIn S fun i => cubeExp (S i) :=
  (((WordIn.wc 3).mul (h.budgetFree.grain S)).add (WordIn.wc 4))
lemma cubeExp_small (S : ι→ℕ) : Small S fun i => cubeExp (S i) :=
  ((Small.const _ 3).mul (Small.self S)).add (Small.const _ 4)
lemma cubeExp_bound (h : b.LenCtx S n) (i) :
    8*(n i)^3 < 2^cubeExp (S i) := by
  have he : 0<n i := h.pos _
  rw [cubeExp,pow_add,Nat.mul_comm 3,pow_mul]
  calc
    _ ≤ 8*((2^S i)^3) := by gcongr; exact (h.n_lt i).le
    _ < _ := by
      have hh : 0 < (2^S i)^3 := by positivity
      norm_num
      omega

lemma rootOfDvd (h : b.LenCtx S n) (g : ∀ i,IsLargeLen (n i)) (u : b.WordIn S k)
    (hk : ∀ i,k i ∣ largeWorkModulus (n i))
    (hz : b.PolyMoves S sc fun i => root (workModulus (n i))) :
    b.PolyMoves S sc fun i => root (k i) := by
  have hp : ∀ i,k i∣workModulus (n i) := fun i => by
    simpa [workModulus,g i] using hk i
  have H := powByBits (h.workModulus_grain.div u) h.cubeExp_word (cubeExp_small _) (x:=fun i => root (workModulus (n i)))
    (fun i => lt_trans (lt_of_le_of_lt (Nat.div_le_self ..)
      (workModulus_bound _ (h.pos _)).2) (h.cubeExp_bound i)) hz
  exact H.congr fun i => root_factor (workModulus_bound _ (h.pos _)).1 (hp i)

lemma rootTwoN (h : b.LenCtx S n) (g : ∀ i,IsLargeLen (n i))
    (hz : b.PolyMoves S sc fun i => root (workModulus (n i))) :
    b.PolyMoves S sc fun i => root (2*n i) :=
  h.rootOfDvd g ((WordIn.wc 2).mul (h.num.grain S)) (fun i => eta_dvd_largeWorkModulus (n i)) hz

lemma rootVol (h : b.LenCtx S n) (g : ∀ i,IsLargeLen (n i))
    (hz : b.PolyMoves S sc fun i => root (workModulus (n i))) :
    b.PolyMoves S sc fun i => root (modulusAxes (n i)).vol :=
  h.rootOfDvd g h.modulusAxes_in.volL (fun _ => vol_dvd_largeWorkModulus _) hz

lemma ratioSq {a b n : ℕ} (h : a<4*n) (g : 2 ≤ b) :
    (a/b)*(a/b) ≤ 8*n^3 := by
  have H : (a/b)*2 ≤ a := le_trans (Nat.mul_le_mul_left _ g)
    (Nat.div_mul_le_self a b)
  have hh : a/b ≤ 2*n := by omega
  calc
    _ ≤ (2*n)*(2*n) := Nat.mul_le_mul hh hh
    _ = n^2*4 := by ring
    _ ≤ n^2*(8*n) := Nat.mul_le_mul_left _ (by omega)
    _ = 8*n^3 := by ring

lemma primeList_entry {X : ι→PrimeList} {e : ι→ℕ}
    (h : b.PrimeListIn S X) (g : Small b.size e) (hk : ∀ i, ∀ j<(X i).l, (X i).q j ≤ e i) :
    (b.scan fun i => (X i).l).WordIn (fun i => S i.i) fun i => (X i.i).q i.j := by
  let L i := (X i).l
  have H := h.dataL.transfer (FreeReads.scan b L)
  refine ⟨PolyCan.pick (t:=w) (k:=During.j) (n:=fun i : During L => L i.i)
    (v:=fun i j => (X i.i).q j) H (scanIndex h.dimL).dry During.hj,
    (g.reindex _).mono (fun i => hk _ i.j i.hj)⟩

lemma axisData_dry (h : b.LenCtx S n) (g : ∀ i,IsLargeLen (n i))
    {z : ι→ℂ} (hu : b.PolyMoves S sc z)
    (hz : b.PolyMoves S sc fun i => root (workModulus (n i))) :
    b.PolyMoves S axisDataTy fun i =>
      axisData (modulusAxes (n i)).l (axisLogBound (n i)) (modulusAxes (n i)).q (z i) := by
  suffices key : ∀ M : ℕ → PrimeList, (∀ i, ModulusSpec (n i) (M (n i))) → b.PrimeListIn S (fun i => M (n i)) →
      b.PolyMoves S axisDataTy fun i => axisData (M (n i)).l (axisLogBound (n i)) (M (n i)).q (z i) from
    key modulusAxes (fun i => modulusAxes_spec (n i) (h.pos _)) h.modulusAxes_in
  intro M hh H
  have hI : b.PolyMoves S sc fun i => Complex.I :=
    (h.rootOfDvd g (WordIn.wc 4) (fun i => four_dvd_largeWorkModulus (n i)) hz).congr (fun _ => root_four)
  have hY : b.WordIn S fun i => axisLogBound (n i)+1 := h.orderG.add (WordIn.wc 1)
  have hSY : Small S fun i => axisLogBound (n i)+1 := h.orderS.add (Small.const _ 1)
  have F := FreeReads.scan b fun i => axisLogBound (n i)+1
  have hj := scanIndex hY
  have hE : Small (b.scan fun i => axisLogBound (n i)+1).size (fun i => 2^i.j) :=
    ((h.powOrderS.trans h.budgetFree.small).reindex _).mono (fun i =>
      Nat.pow_le_pow_right (by omega) (Nat.le_of_lt_succ i.hj))
  have hk := hj.twoPow ((hSY.reindex _).mono fun i => i.hj.le) hE
  have hv := tabPoly hY hSY (fun _ => twoPowRoots) (t:=sc)
    ((h.transfer F).rootOfDvd (fun i => g i.i) hk
      (fun i => twoPow_dvd_largeWorkModulus _ _ (Nat.le_of_lt_succ i.hj)) (hz.transfer F))
  have G := FreeReads.scan b fun i => (M (n i)).l
  have hb := primeList_entry H h.powOrderG.small (fun i => (hh i).sizes)
  have Ha := H.volL.transfer G
  have HG := h.transfer G
  have HE (i : During fun i => (M (n i)).l) :
      ((M (n i.i)).vol / (M (n i.i)).q i.j) *
        ((M (n i.i)).vol / (M (n i.i)).q i.j) < 2 ^ cubeExp (S i.i) := by
    have He : 2 ≤ (M (n i.i)).q i.j := (hh _).square.isles.good i.j i.hj
    have Hh : (M (n i.i)).vol < 4*n i.i := (hh _).upper
    exact lt_of_le_of_lt (ratioSq Hh He) (HG.cubeExp_bound i)
  have HD := powByBits ((Ha.div hb).mul (Ha.div hb)) HG.cubeExp_word (cubeExp_small _) HE (hu.transfer G)
  have HS := tabPoly H.dimL H.countS
    (fun i j => axisRoot (z i) (extent (M (n i)).q (M (n i)).l)
      ((M (n i)).q j)) (t:=sc)
    (HD.congr fun i => by rw [axisRoot,show extent (M (n i.i)).q (M (n i.i)).l
      = (M (n i.i)).vol from (hh _).square.agrees.symm])
  exact H.dimL.dry.pair (h.orderG.dry.pair (H.dataL.pair (hI.pair (hv.pair HS))))

end LenCtx

open ReelKit
def axisDFTCost (zE : ℝ) (n : ℕ) := (vandermondeBeats (axisLogBound n)+1)*((modulusAxes n).vol*envelope zE (modulusAxes n).l)

end
section
open Ty Modulus Spectral
variable {ι : Type U} {κ : Type V} {m : Bool} {b : Bench m ι} {q : Bench m κ} {zE : ℝ}
  {s t : Ty} {S n N : ι→ℕ}

def budget (zE : ℝ) (d n : ℕ) := n+axisDFTCost zE n+(axisBudget n+2)^d + (if IsLargeLen n then 0 else (n+2)^d)

lemma budget_deg {c d : ℕ} (n : ℕ) (h : c≤d) : budget zE c n≤budget zE d n := by
  have := Small.pow_mono_degree (axisBudget n) h; have := Small.pow_mono_degree n h
  unfold budget; split <;> omega
lemma budget_left (n d : ℕ) : n + (axisBudget n+2)^d ≤ budget zE d n := by
  unfold budget; omega
lemma LenCtx.budget_fair (h : b.LenCtx S n) (g : ∀ i,IsLargeLen (n i)) (d : ℕ) (i : ι) :
    n i+axisDFTCost zE (n i)+(S i+2)^d ≤ budget zE d (n i) := by
  simp [budget, h.budget_eq, g i]

def BudgetMoves (zE : ℝ) (b : Bench m ι) (n : ι→ℕ) (t : Ty) (x : ι→T t) : Prop :=
  Can.Within m b.size (fun d i => budget zE d (n i)) b.tray t b.env x

namespace BudgetMoves
variable {x y : ι→T t}
lemma of_moves {W} (h : b.Moves W t x) (g : Dom n W) : b.BudgetMoves zE n t x :=
  ⟨0,h.weaken ((Dom.of_le fun i => (Nat.le_add_right _ _).trans (budget_left (n i) 0)).trans g)⟩
lemma of_dry (h : b.LenCtx S n) (g : ∀ i,IsLargeLen (n i)) (hx : b.PolyMoves S t x) : b.BudgetMoves zE n t x :=
  let ⟨d,hd⟩ := hx
  ⟨d, hd.mono fun i => (Nat.le_add_left _ _).trans (h.budget_fair g d i)⟩
lemma pair {v : ι→T s} (h : b.BudgetMoves zE n t x) (g : b.BudgetMoves zE n s v) :
    b.BudgetMoves zE n (p t s) fun i => (x i,v i) :=
  Can.Within.lift2 (fun h i => budget_deg (n i) h) h g Can.pair
lemma bind {v : ι→T s} (h : b.BudgetMoves zE n t x) (g : (b.extend t x).BudgetMoves zE n s v) :
    b.BudgetMoves zE n s v :=
  Can.Within.lift2 (fun h i => budget_deg (n i) h) h g Can.bind
end BudgetMoves

structure BluesteinCtx (b : Bench m ι) (n S N : ι→ℕ) : Prop where
  dims : b.LenCtx S n
  port : ∀ i, IsLargeLen (n i)
  rootP : b.PolyMoves S sc fun i => root (workModulus (n i))
  ac : ∀ i, (modulusAxes (n i)).vol=N i
  sizeL : b.FreeWord N

lemma signP (ret : Bool) (h : ∀ i,0<n i) (g : b.PolyMoves S sc fun i => root (n i)) :
    b.PolyMoves S sc fun i => signedRoot ret (n i) := by
  cases ret
  · exact g
  · exact g.inv fun i => (root_primitive _ (h i)).ne_zero (Nat.ne_of_gt (h i))

namespace BluesteinCtx
variable {cl : Paint} {x y : ι→Line}

lemma transfer {S n N : κ→ℕ} (h : q.BluesteinCtx n S N) {f} (g : b.FreeReads q f) :
    b.BluesteinCtx (fun i => n (f i)) (fun i => S (f i)) (fun i => N (f i)) :=
  ⟨h.dims.transfer g,fun _ => h.port _,h.rootP.transfer g,fun _ => h.ac _,h.sizeL.transfer g⟩

lemma volume_ge (h : b.BluesteinCtx n S N) (i) : 2*n i ≤ N i :=
  h.ac i ▸ (modulusAxes_spec _ (h.dims.pos i)).lower
lemma volume_lt (h : b.BluesteinCtx n S N) (i) : N i < 4*n i :=
  h.ac i ▸ (modulusAxes_spec _ (h.dims.pos i)).upper
lemma volume_pos (h : b.BluesteinCtx n S N) (i) : 0<N i := by
  have hh := h.volume_ge i; have hk := h.dims.pos i; omega

lemma dom (h : b.BluesteinCtx n S N) : Dom n N :=
  ⟨4,fun i => by have := h.volume_lt i; omega⟩

lemma modulusFreq_moves (hE : RippleEngine.{U} zE) (h : b.BluesteinCtx n S N) (r : Bool) (hx : b.BudgetMoves zE n (a (c cl)) fun i =>
    Tape.tab (N i) (x i)) :
    b.BudgetMoves zE n (a (c cl)) fun i => Tape.tab (N i) (freq (N i) (signedRoot r (N i)) (x i)) := by
  let V (i : ι) : T (a (c cl)) := Tape.tab (N i) (x i)
  have F := FreeReads.extend b V (t:=a (c cl))
  refine hx.bind ?_
  have h : (b.extend _ V).BluesteinCtx n S N := h.transfer F
  have hx : (b.extend _ V).Moves (fun _ => 0) (a (c cl)) V := newestMoves b V (t:=a (c cl))
  have hX i := modulusAxes_spec (n i) (h.dims.pos _)
  have he i : (modulusAxes (n i)).vol=AxisTensor.extent (modulusAxes (n i)).q (modulusAxes (n i)).l := (hX _).square.agrees
  have H (i) : AxisTensor.extent (modulusAxes (n i)).q (modulusAxes (n i)).l = N i := (he i).symm.trans (h.ac i)
  have hu := signP r h.volume_pos ((h.dims.rootVol h.port h.rootP).congr fun i => congrArg root (h.ac i))
  obtain ⟨d,hd⟩ := modulusFreq_moves_of_axes hE (r:=fun i => (modulusAxes (n i)).q) (l:=fun i => (modulusAxes (n i)).l)
    (z:=fun i => signedRoot r (N i)) (fun i => (hX _).square.isles)
    (fun i => (hX _).sizes) (fun i => (H i).symm ▸ show Spectral.PrimRoot (signedRoot r (N i)) (N i) from
      primitive_pr _ (h.volume_pos i) r) h.dims.modulusAxes_in.countS h.dims.powOrderS h.dims.budgetFree.small
    (h.dims.modulusAxes_in.volume.mono (fun i => (he i).symm.le)) (x:=x)
    (h.dims.axisData_dry h.port hu h.rootP) (hx.congr fun i => congrArg (fun u => Tape.tab u (x i)) (H i).symm)
  refine ⟨d,(hd.weaken (Dom.of_le fun i => ?_)).congr fun i => by rw [H]⟩
  have := h.dims.budget_fair (zE := zE) h.port d i
  unfold axisDFTCost at this; (try dsimp only); rw [← he i]; omega

lemma chirp_moves (h : b.BluesteinCtx n S N) (r : Bool)
    (hp : b.Moves (fun _ => 0) (a sc) fun i => tablePow (signedRoot r (2*n i)) (S i))
    {k} (hk : b.FreeWord k) :
    b.Moves (fun _ => 0) sc fun i => chirp (signedRoot r (2*n i)) (k i) :=
  square_pow hp ((WordIn.wc 2).mul h.dims.num)
    (fun i => ⟨by have := h.dims.pos i; omega,h.dims.budget_eq i ▸ (axisBudget_above (n i)).le⟩)
    (fun i => (primitive_pr (2*n i) (by have := h.dims.pos i; omega) r).pow_eq_one) hk

lemma bluestein_moves (hE : RippleEngine.{U} zE) (h : b.BluesteinCtx n S N) (r : Bool)
    (hx : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (n i) (x i)) :
    b.BudgetMoves zE n (a (c cl)) fun i =>
      Tape.tab (n i) (freq (n i) (signedRoot r (n i)) (x i)) := by
  let z (i) : T sc := signedRoot r (2*n i)
  let V i := tablePow (signedRoot r (2*n i)) (S i)
  have Fz := FreeReads.extend b z (t:=sc)
  have hz : b.BudgetMoves zE n sc z := BudgetMoves.of_dry h.dims h.port (signP r (fun i => by have := h.dims.pos i; omega)
      (h.dims.rootTwoN h.port h.rootP))
  have hT : b.BudgetMoves zE n (a sc) V := hz.bind (BudgetMoves.of_moves (powTable_moves (h.dims.budgetFree.transfer Fz)
    (g:=h.dims.budgetPow_small) (newestMoves b z (t:=sc))) ⟨4,fun i => by
    dsimp only [id]
    have hh : 2^S i ≤ 4*n i := h.dims.budget_eq i ▸ axisBudget_pow (n i) (h.dims.pos i); omega⟩)
  refine hT.bind ?_
  let B := b.extend (a sc) V
  have F0 := FreeReads.extend b V (t:=a sc)
  have hc : B.BluesteinCtx n S N := h.transfer F0
  have hp : B.Moves (fun _ => 0) (a sc) V := newestMoves b V (t:=a sc)
  have hx : B.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (n i) (x i) := hx.transfer F0
  have F := FreeReads.scan B N
  have hh := hc.transfer F
  have hj := scanIndex hc.sizeL

  have hR : B.BudgetMoves zE n (a (c cl)) fun i =>
      Tape.tab (N i) (chirpSeed (n i) (signedRoot r (2*n i)) (x i)) := by
    have H := (hh.chirp_moves r (hp.transfer F) hj).mul (pick_all (t:=c cl)
      (n:=fun i : During N => n i.i) (fun (i : During N) j => x i.i j) (hx.transfer F) hj)
    refine BudgetMoves.of_moves (arrayNow hc.sizeL _ (H.congr fun i => ?_)) hc.dom
    simp only [chirpSeed,mul_ite]; congr 1
    exact mul_zero _

  have hF : B.BudgetMoves zE n (a sc) fun i => Tape.tab (N i) (chirpFilter (n i) (N i) (signedRoot r (2*n i))) := by
    have hk := (((hj.cmp hh.dims.num).branch (hh.sizeL.sub hj) hj)).congr
      (y:=fun i => chirpDist (n i.i) (N i.i) i.j) (fun i => by
      by_cases e : i.j < n i.i <;> simp [chirpDist,e])
    refine BudgetMoves.of_moves (arrayNow hc.sizeL _ ((hh.chirp_moves r (hp.transfer F) hk).inv fun i => ?_)) hc.dom
    have Hu : 0<2*n i.i := by have := hc.dims.pos i.i; omega
    exact pow_ne_zero _ ((primitive_pr _ Hu r).ne_zero (Nat.ne_of_gt Hu))

  let A i := freq (N i) (signedRoot false (N i)) (chirpFilter (n i) (N i) (signedRoot r (2*n i)))
  let C i := freq (N i) (signedRoot false (N i)) (chirpSeed (n i) (signedRoot r (2*n i)) (x i))
  let D i := fetchC (N i) (signedRoot false (N i)) (chirpFilter (n i) (N i) (signedRoot r (2*n i)))
    (chirpSeed (n i) (signedRoot r (2*n i)) (x i))
  let Wl (i) : T (p (a sc) (a (c cl))) := (Tape.tab (N i) (A i),Tape.tab (N i) (C i))
  have hw := newestMoves B Wl (W:=fun _ => 0)
  have HW : (B.extend _ Wl).FreeWord N := hc.sizeL.transfer (FreeReads.extend B Wl)
  have hP : B.BudgetMoves zE n (a (c cl)) fun i => Tape.tab (N i) (D i) :=
    hc.modulusFreq_moves hE true (x:=fun i => pointC (N i) (signedRoot false (N i))
      (chirpFilter (n i) (N i) (signedRoot r (2*n i))) (chirpSeed (n i) (signedRoot r (2*n i)) (x i)))
    (((hc.modulusFreq_moves hE false hF).pair (hc.modulusFreq_moves hE false hR)).bind (BudgetMoves.of_moves
      (WHT.tab_mul HW (Dom.self N) hw.fst.anyCost hw.snd.anyCost) hc.dom))

  let U (i : ι) : T (p (a (c cl)) sc) := (Tape.tab (N i) (D i),(N i:ℂ))
  have G0 := FreeReads.extend B U
  have G := FreeReads.scan (B.extend _ U) n
  have hh' := hc.transfer (G.next G0)
  have hk := Moves.transfer (newestMoves B U (W:=fun _ => 0)) G
  have hn := hc.dims.num.transfer G0
  have HL := scanIndex hn
  have HS := Can.pick (n:=fun i : During n => N i.i) (t:=c cl)
    (fun i => D i.i) hk.fst HL.toMoves (fun i => by
      have := hc.volume_ge i.i; have := i.hj; omega)
  have hd := (hh'.chirp_moves r (hp.transfer (G.next G0)) HL).mul
    ((hk.snd.inv fun i => Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hc.volume_pos i.i))).mul HS)
  exact (hP.pair (BudgetMoves.of_moves hc.sizeL.numeralM hc.dom)).bind
    (BudgetMoves.of_moves (arrayNow hn _ (hd.congr fun i =>
      bluestein_freq _ _ (hc.dims.pos i.i) (hc.volume_ge i.i) r _ _ i.hj)) (Dom.self n))

end BluesteinCtx

lemma LenCtx.dft_moves_large (hE : RippleEngine.{U} zE) (h : b.LenCtx S n) (g : ∀ i,IsLargeLen (n i))
    (hz : b.PolyMoves S sc fun i => root (workModulus (n i))) (r : Bool)
    {x : ι→Line} {cl} (hx : b.Moves (fun _ => 0) (a (c cl)) fun i =>
      Tape.tab (n i) (x i)) :
    b.BudgetMoves zE n (a (c cl)) fun i =>
      Tape.tab (n i) (freq (n i) (signedRoot r (n i)) (x i)) := by
  let N i := (modulusAxes (n i)).vol
  have F := FreeReads.extend b N (t:=w)
  have hh : (b.extend w N).BluesteinCtx n S N :=
    ⟨h.transfer F,g,hz.transfer F,fun i => rfl,⟨(newestMoves b N (t:=w)).toPoly _,h.modulusAxes_in.volume⟩⟩
  exact (BudgetMoves.of_dry h g h.modulusAxes_in.volL.dry).bind (hh.bluestein_moves hE r (hx.transfer F))

end
-- heavily modified from github.com/openai/math lean/OAI/Computability/FourierTransform/TransformProgram.lean (commit fd4aeeb, Apache-2.0)
/-
Derived from lean/OAI/Computability/FourierTransform/TransformProgram.lean of github.com/openai/math
(commit fd4aeeb, Apache-2.0), heavily modified for this repository:
  * merged into this file with other modules, imports changed, some declarations renamed, comments removed;
  * OpenAI's fixed exponent `alpha = 1 - 2/10^11` and envelope `hills` are replaced, where they occur, by a
    general exponent with `envelope`, and OpenAI's `hills_program` by the hypothesis `hE : RippleEngine z`
    (ReelCompile.lean; instances `RouteB.rippleEngine_of_templates` at every exponent above `RouteB.templateWall = 1/2`);
  * `decimalExponent`, `decimalTime`, `TimeBounds`, `DFTGoal`, `ConvGoal` are not used (deleted, see Goal.lean): the
    theorems of this file state their bounds directly (`=O[atTop]` at exponent `1 - s`, and `paperTime`);
  * proofs changed to match.
-/
section
open Ty Modulus Spectral Finset
variable {ι : Type U} {κ : Type V} {m : Bool} {b : Bench m ι} {q : Bench m κ} {zE : ℝ}
  {s t : Ty} {n N k : ι→ℕ}

lemma PolyMoves.naive_freq (h : b.FreeWord N)
    {x : ι→Line} {cl} (hx : b.PolyMoves N (a (c cl)) fun i => Tape.tab (N i) (x i))
    {z : ι→ℂ} (hz : b.PolyMoves N sc z) :
    b.PolyMoves N (a (c cl)) fun i => Tape.tab (N i) (freq (N i) (z i) (x i)) := by
  have F := FreeReads.scan b N
  have hj := scanIndex (h.grain N)
  let K (d : During N) := N d.i
  -- row `j` uses the root `z^j`; the inner loop carries the partial sum and the running power of it
  let V (d : During N) (k : ℕ) : T (p (c cl) sc) :=
    (∑ k' ∈ range k, (z d.i^d.j)^k'*x d.i k', (z d.i^d.j)^k)
  have hk : (b.scan N).WordIn K K := (h.transfer F).grain _
  have G := FreeReads.climbs (b.scan N) K V
  have st := PolyMoves.token (b.scan N) K K V
  have hw := (powByBits hj hj (Small.self N).during (fun _ => Nat.lt_two_pow_self) (hz.transfer F)).transfer G
  have hxk := PolyCan.pick (t:=c cl) (v:=fun (e : During K) k => x e.i.i k) (n:=fun e : During K => N e.i.i)
    (hx.transfer (G.next F)) (climbIndex hk V).dry During.hj
  refine tabPoly (h.grain N) (Small.self N) _ (((loopPoly hk (Small.self K) V
    ((PolyCan.zero.pair PolyCan.one).congr fun d => by simp [V])
    (((st.fst.add (st.snd.mul hxk)).pair (st.snd.mul hw)).congr fun e =>
      Prod.ext (sum_range_succ ..).symm (pow_succ ..).symm)).fst).congr fun d => ?_)
  show ∑ k ∈ range (N d.i), (z d.i^d.j)^k*x d.i k = ∑ k ∈ range (N d.i), z d.i^(d.j*k)*x d.i k
  exact sum_congr rfl fun k _ => by rw [← pow_mul]

lemma LenCtx.dft_moves (hE : RippleEngine.{U} zE) (h : b.LenCtx (fun i => axisBudget (n i)) n)
    (hz : b.Moves (fun _ => 0) sc fun i => root (workModulus (n i)))
    (r : Bool) {x : ι→Line} {cl} (hx : b.Moves (fun _ => 0) (a (c cl)) fun i =>
      Tape.tab (n i) (x i)) :
    b.BudgetMoves zE n (a (c cl)) fun i => Tape.tab (n i) (freq (n i) (signedRoot r (n i)) (x i)) := by
  let f (i : ι) := if IsLargeLen (n i) then 0 else 1
  obtain ⟨d,hd⟩ := h.largeLen_word.dry
  have Fy := FreeReads.along b (Subtype.val (p:=fun i => f i = 0))
  have Fn := FreeReads.along b (Subtype.val (p:=fun i => f i ≠ 0))
  have hl := (h.transfer Fy).dft_moves_large hE (fun i => by
      by_contra k; have hi : f i.val=0 := i.property; simp [f,k] at hi)
    ((hz.transfer Fy).toPoly _) r (hx.transfer Fy)
  have hp : ∀ i : {i // f i ≠ 0}, ¬ IsLargeLen (n i.val) := fun i g => i.property (by simp [f,g])
  have H := h.transfer Fn
  obtain ⟨k,hk⟩ := PolyMoves.naive_freq H.num ((hx.transfer Fn).toPoly _) (signP r H.pos
    ((hz.transfer Fn).toPoly (fun i => n i.val) |>.congr
      (y':=fun i => root (n i.val)) fun i => by rw [workModulus,ite_eq_right (hp i)]))
  exact Can.Within.testz (fun h i => budget_deg (n i) h) (n := f)
    ⟨d, Can.mono hd fun i => (Nat.le_add_left _ _).trans (budget_left _ d)⟩ hl
    ⟨k, Can.mono hk fun i => by beta_reduce; unfold budget; rw [ite_eq_right (hp i)]; exact Nat.le_add_left _ _⟩

lemma FreeWord.order_moves (h : b.FreeWord N) (g : ∀ i, 0<N i) :
    b.BudgetMoves zE N w fun i => workModulus (N i) :=
  let ⟨d,hd⟩ := h.workModulus_moves g
  ⟨d, hd.weaken (Dom.of_le fun i => budget_left (N i) d)⟩
lemma FreeWord.dft_moves (hE : RippleEngine.{U} zE) (h : b.FreeWord N) (g : ∀ i, 0<N i)
    (hz : b.Moves (fun _ => 0) sc fun i => root (workModulus (N i)))
    (r : Bool) {x : ι→Line} {cl} (hx : b.BudgetMoves zE N (a (c cl)) fun i =>
      Tape.tab (N i) (x i)) :
    b.BudgetMoves zE N (a (c cl)) fun i => Tape.tab (N i) (freq (N i) (signedRoot r (N i)) (x i)) := by
  let V (i : ι) : T (a (c cl)) := Tape.tab (N i) (x i)
  have F := FreeReads.extend b V (t:=a (c cl))
  have hN : (b.extend _ V).FreeWord N := h.transfer F
  obtain ⟨hu,hk⟩ := hN.axisBudget_moves g
  have H := FreeReads.extend (b.extend _ V) (fun i => axisBudget (N i)) (t:=w)
  exact hx.bind ((BudgetMoves.of_moves hu (Dom.self N)).bind (hk.dft_moves hE ((hz.transfer F).transfer H) r
    ((newestMoves (W:=fun _ => 0) b V (t:=a (c cl))).transfer H)))
end
section
open RAM Ty Modulus Spectral Finset
variable {ι : Type U} {κ : Type V} {b : Bench true ι} {n N : ι→ℕ} {zE : ℝ}

def convLen (n : ℕ) := 2*n-1

def padLine (n : ℕ) (x : Line) : Line := fun j => if j<n then x j else 0

lemma freq_mul (n : ℕ) (u c : ℂ) (f g : Line) (i : ℕ) :
    freq n u (fun j => c*(f j*g j)) i = c*freq n u (fun j => g j*f j) i := by
  simp only [freq,mul_sum]; exact sum_congr rfl fun _ _ => by ring

lemma freq_pad_conv {n : ℕ} (hn : 0<n) (x y : Line) :
    Tape.tab (2*n-1) (freq (2*n-1) (signedRoot true (2*n-1)) fun j => ((2*n-1:ℕ):ℂ)⁻¹*
      (freq (2*n-1) (signedRoot false (2*n-1)) (padLine n x) j*freq (2*n-1) (signedRoot false (2*n-1)) (padLine n y) j)) =
    ⟨2*n-1,conv n (front n x) (front n y)⟩ := by
  refine congrArg (Tape.mk _) (funext fun k => ?_)
  have hk := k.isLt
  refine ((freq_mul ..).trans (cyc_formula (primitive_pr _ (by omega) false) _ _ hk)).trans ?_
  calc cyclic (2*n-1) (padLine n y) (padLine n x) k
      = ∑ r ∈ range n, ∑ s ∈ range n, if r+s=k then x r*y s else 0 := by
        unfold cyclic
        rw [← range_pad n (2*n-1) (by omega)]
        refine sum_congr rfl fun r _ => ?_
        by_cases hr : r<n
        · rw [ite_eq_left hr,show padLine n x r = x r from ite_eq_left hr]
          by_cases hi : r ≤ k
          · simp only [show ∀ s, r+s=(k:ℕ) ↔ s=k-r from fun s => by omega,sum_ite_eq',mem_range,
              padLine,predAt,ite_eq_left hi]
            split_ifs <;> ring
          · have h1 : ∀ s, ¬ r+s=(k:ℕ) := fun s => by omega
            have h2 : ¬ (k:ℕ)+(2*n-1)-r < n := by omega
            simp only [padLine,predAt,ite_eq_right hi,h1,h2,↓reduceIte,zero_mul,sum_const_zero]
        · rw [ite_eq_right hr,show padLine n x r = 0 from ite_eq_right hr,mul_zero]
    _ = _ := by simp only [sum_range]; rfl

lemma cross_moves (h : b.FreeWord N) {u : ι→ℂ} {x y : ι→Line}
    (hP : b.BudgetMoves zE N (p sc (p (a (c .left)) (a (c .right)))) fun i =>
      (u i,Tape.tab (N i) (x i),Tape.tab (N i) (y i))) :
    b.BudgetMoves zE N (a (c .both)) fun i => Tape.tab (N i) fun j => u i*(x i j*y i j) := by
  let P (i : ι) : T (p sc (p (a (c .left)) (a (c .right)))) := (u i,Tape.tab (N i) (x i),Tape.tab (N i) (y i))
  have hN : (b.extend _ P).FreeWord N := h.transfer (FreeReads.extend b P)
  have H := (newestMoves (W:=fun _ => 0) b P).transfer (FreeReads.scan _ N)
  have k := (scanIndex hN).toMoves
  exact hP.bind (BudgetMoves.of_moves (arrayNow (t:=c .both) hN (fun i j => u i*(x i j*y i j)) (H.fst.mul (cl:=.both) (Can.cross
    (Can.pick (t:=c .left) (n:=fun d : During N => N d.i) (fun d j => x d.i j) H.snd.fst k During.hj)
    (Can.pick (t:=c .right) (n:=fun d : During N => N d.i) (fun d j => y d.i j) H.snd.snd k During.hj))))
    (Dom.self N))

end
section
open RAM Ty Modulus Spectral ReelKit
variable {ι : Type U} {κ : Type*} {m : Bool} {b : Bench m ι} {zE : ℝ}
  {n : ι→ℕ} {t : Ty}

lemma budget_small (hz1 : zE ≤ 1) (N : ι→ℕ) (hn : ∀ i,0<N i) (d : ℕ) :
    Small N fun i => budget zE d (N i) := by
  have H := Small.self N
  have hX i := modulusAxes_spec (N i) (hn i)
  have h4 := (Small.const _ 4).mul H
  have hu := h4.mono (fun (i : ι) => axisBudget_le (N i) (hn i))
  have hk : Small N fun i => primeSearchLimit (N i) :=
    (((Small.const _ 16).mul (hu.add (Small.const _ 4))).pow 2)
  have hh := ((Small.const _ 8).mul hk).mono
    (fun i => Nat.lt_two_pow_self.le.trans (axisLogBound_pow (N i)))
  have hi := ((((Small.const _ 20000000).mul ((hh.add (Small.const _ 1)).pow 2)).add
    (Small.const _ 7))).mono (fun i => vandermondeBeats_le (axisLogBound (N i)))
  have hp : Small N fun i => envelope zE (modulusAxes (N i)).l :=
    (hu.add (Small.const _ 1)).mono fun i => envelope_le_of hz1
      (Nat.add_le_add_right (hX i).count _)
  have hj := (hi.add (Small.const _ 1)).mul
    ((h4.mono fun i => (hX i).upper.le).mul hp)
  have hl := H.add hj |>.add ((hu.add (Small.const _ 2)).pow d)
  exact hl.add (((H.add (Small.const _ 2)).pow d).mono fun i => by split <;> omega)

abbrev Sizes := {n : ℕ // 0<n}
abbrev entry : Sizes→ℕ := Subtype.val

structure CostWitness where
  d : ℕ
  c : ℕ
  p : ℕ
def stageCost (zE : ℝ) (a : CostWitness) (n : ℕ) := a.c*(budget zE a.d n+1)

lemma BudgetMoves.ration {x : ι→T t} (h : b.BudgetMoves zE n t x) :
    ∃ (s : Prog m b.tray t) (a : CostWitness), ∀ i,
      (run s (b.env i)).OK (x i) (stageCost zE a (n i)) ((b.size i+2)^a.p) := by
  obtain ⟨d,hd⟩ := h
  obtain ⟨s,c,p,hc⟩ := Can.unfold_bound hd
  exact ⟨s,⟨d,c,p⟩,hc⟩

def totalCost (zE : ℝ) (a b : CostWitness) (N : ℕ→ℕ) (n : ℕ) :=
  stageCost zE a (N n)+1+stageCost zE b (N n)

def lengthOnly : Bench false Sizes := ⟨entry,w,entry⟩
lemma lengthOnly_word : lengthOnly.FreeWord entry := ⟨PolyCan.id,Small.self _⟩

lemma assemble_program (hz1 : zE ≤ 1) {N : ℕ→ℕ} (hk : lengthOnly.FreeWord fun i => N (entry i))
    (h : ∀ n,0<n → 0<N n ∧ N n ≤ 2*n) (b : CostWitness) :
    ∃ (o : Prog false w w) (a : CostWitness) (c : ℕ), ∀ n,0<n →
      (run o n).val = workModulus (N n) ∧ totalCost zE a b N n + 10*(n+2) ≤ (n+2)^c ∧
      (run o n).peak ≤ (n+2)^c ∧ (run o n).valid ∧ 0 < workModulus (N n) ∧
      workModulus (N n) < 1024*N n^3 ∧ workModulus (N n) ≤ (n+2)^c ∧
      ∀ (v : Tape ℂ) (r : Bill (Tape ℂ)), r.OK v (stageCost zE b (N n)) ((n+2)^b.p) →
        r.valid ∧ r.peak ≤ (n+2)^c ∧ (run o n).work+1+r.work ≤ totalCost zE a b N n ∧ r.val = v := by
  obtain ⟨o,a,ho⟩ := (hk.order_moves (fun i => (h _ i.2).1)).ration
  let M i := N (entry i)
  have g : Small entry M := ((Small.const _ 2).mul (Small.self _)).mono fun i => (h _ i.2).2
  have H (a : CostWitness) : Small entry (fun i => stageCost zE a (M i)) :=
    (Small.const _ a.c).mul (((budget_small hz1 M (fun i => (h _ i.property).1) a.d).trans g).add
      (Small.const _ 1))
  have hu := (Small.self entry).add (Small.const _ 2)
  have hp := ((Small.const _ 8).mul (g.pow 3)).mono
    (fun i => (workModulus_bound _ (h _ i.property).1).2.le)
  obtain ⟨c,hc⟩ := ((((((H a).add (Small.const _ 1)).add (H b)).add ((Small.const _ 10).mul hu)).max
    (hu.pow a.p)).max (hu.pow b.p)).max hp
  refine ⟨o,a,c,fun n hn => ?_⟩
  have hx : max (max (max (totalCost zE a b N n + 10*(n+2)) ((n+2)^a.p)) ((n+2)^b.p)) (workModulus (N n)) ≤
      (n+2)^c := hc ⟨n,hn⟩
  have h1 := max_le_iff.mp hx
  have h2 := max_le_iff.mp h1.1
  have h3 := max_le_iff.mp h2.1
  have Ho := ho ⟨n,hn⟩
  have HH := workModulus_bound _ (h n hn).1
  exact ⟨Ho.result,h3.1,Ho.bound.trans h3.2,Ho.valid,HH.1,HH.2.trans_le (by omega),h1.2,
    fun v r hr => ⟨hr.valid,hr.bound.trans h2.2,add_le_add (add_le_add_left Ho.time 1) hr.time,hr.result⟩⟩

def dftInputs : Bench false (Sizes×Line) :=
  ⟨fun i => entry i.1,dftInKind,fun i =>
    (entry i.1, root (workModulus (entry i.1)),Tape.tab (entry i.1) i.2)⟩

lemma dft_solve_program (hE : RippleEngine.{0} zE) : ∃ (s : Prog false dftInKind dftOutKind) (a : CostWitness),
    ∀ (n : ℕ),0<n → ∀ x : Vec n,
    (run s (n, root (workModulus n), (⟨n,x⟩ : Tape ℂ))).OK
      (⟨n, dft n x⟩ : Tape ℂ) (stageCost zE a n) ((n+2)^a.p) := by
  have ht : dftInputs.Moves (fun _ => 0) dftInKind dftInputs.env := Can.id
  obtain ⟨s,a,ha⟩ := ((show dftInputs.FreeWord fun i => entry i.1 from ⟨ht.fst.toPoly _,Small.self _⟩).dft_moves hE
    (fun i => i.1.property) ht.snd.fst false (x:=Prod.snd) (cl:=Paint.left)
    (BudgetMoves.of_moves ht.snd.snd (Dom.const _ 0))).ration
  refine ⟨s,a,fun n hn x => ?_⟩
  specialize ha ((⟨n,hn⟩:Sizes),extendLine x)
  change (run s (n,root (workModulus n),(⟨n,front n (extendLine x)⟩:Tape ℂ))).OK
    (⟨n,front n (freq n (signedRoot false n) (extendLine x))⟩ : Tape ℂ) _ _ at ha
  rw [← dft_front n,front_exact] at ha
  exact ha

lemma conv_solve_program (hE : RippleEngine.{0} zE) : ∃ (s : Prog true convInKind convOutKind) (a : CostWitness),
    ∀ n,0<n → ∀ x y : Vec n,
    (run s (n,root (workModulus (convLen n)),(⟨n,x⟩ : Tape ℂ),(⟨n,y⟩ : Tape ℂ))).OK
      (⟨2*n-1,conv n x y⟩ : Tape ℂ) (stageCost zE a (convLen n)) ((n+2)^a.p) := by
  let K : Bench true (Sizes×Line×Line) := ⟨fun i => i.1.val,convInKind,fun i =>
    (i.1.val,root (workModulus (convLen i.1.val)),Tape.tab i.1.val i.2.1,Tape.tab i.1.val i.2.2)⟩
  have ht : K.Moves (fun _ => 0) convInKind K.env := Can.id
  let N (i : Sizes×Line×Line) := convLen i.1.val
  have hN : K.FreeWord N := ((WordIn.wc 2).mul (⟨ht.fst.toPoly _,Small.self _⟩ : K.FreeWord fun i => i.1.val)).sub (WordIn.wc 1)
  have gN : ∀ i, 0<N i := fun i => by have := i.1.property; show 0<2*_-1; omega

  have F (cl : Paint) (v : Sizes×Line×Line → Line)
      (hv : K.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab i.1.val (v i)) :=
    hN.dft_moves hE gN ht.snd.fst false (BudgetMoves.of_moves (arrayNow (t:=c cl) hN (fun i => padLine i.1.val (v i))
      (pick_all (t:=c cl) (n:=fun d : During N => d.i.1.val) (fun d j => v d.i j) (hv.transfer (FreeReads.scan K N)) (scanIndex hN))) (Dom.self N))
  have hP := (BudgetMoves.of_moves (hN.numeralM.inv fun i => Nat.cast_ne_zero.mpr (gN i).ne') (Dom.self N)).pair
    ((F _ (fun i => i.2.1) ht.snd.snd.fst).pair (F _ (fun i => i.2.2) ht.snd.snd.snd))

  obtain ⟨s,a,ha⟩ := (hN.dft_moves hE gN ht.snd.fst true (cross_moves hN hP)).ration
  refine ⟨s,a,fun n hn x y => ?_⟩
  rw [← front_exact x,← front_exact y,← freq_pad_conv hn]
  exact ha (⟨n,hn⟩,extendLine x,extendLine y)

theorem conv_program (hE : RippleEngine.{0} zE) (hz1 : zE ≤ 1) : ∃ order solve a b,
    ConvProgram order solve (totalCost zE a b convLen) ∧
    ∀ n, 0<n → (run order n).val = workModulus (convLen n) := by
  obtain ⟨s,b,hs⟩ := conv_solve_program hE
  obtain ⟨o,a,c,hc⟩ := assemble_program hz1 (N:=convLen) (((WordIn.wc 2).mul lengthOnly_word).sub (WordIn.wc 1))
    (fun n h => by unfold convLen; omega) b
  refine ⟨o,s,a,b,⟨c,fun n hn => ?_⟩,fun n hn => (hc n hn).1⟩
  obtain ⟨he,h1,h2,h3,h4,h5,h6,h7⟩ := hc n hn
  dsimp only
  rw [he]
  exact ⟨h1,h2,h3,h4,h5,h6,fun x y => h7 _ _ (hs n hn x y)⟩

theorem dft_program (hE : RippleEngine.{0} zE) (hz1 : zE ≤ 1) : ∃ order solve a b,
    DFTProgram order solve (totalCost zE a b id) ∧
    ∀ n, 0<n → (run order n).val = workModulus n := by
  obtain ⟨s,b,hs⟩ := dft_solve_program hE
  obtain ⟨o,a,c,hc⟩ := assemble_program hz1 (N:=id) lengthOnly_word (fun n h => ⟨h,show n ≤ 2*n by omega⟩) b
  refine ⟨o,s,a,b,⟨c,fun n hn => ?_⟩,fun n hn => (hc n hn).1⟩
  obtain ⟨he,h1,h2,h3,h4,h5,h6,h7⟩ := hc n hn
  dsimp only
  rw [he]
  exact ⟨h1,h2,h3,h4,h5,h6,fun x => h7 _ _ (hs n hn x)⟩

end
end Bench
end
end OAI.PowerSaving.RAM

-- heavily modified from github.com/openai/math lean/OAI/Computability/FourierTransform/Asymptotics.lean (commit fd4aeeb, Apache-2.0)
/-
Derived from lean/OAI/Computability/FourierTransform/Asymptotics.lean of github.com/openai/math
(commit fd4aeeb, Apache-2.0), heavily modified for this repository:
  * merged into this file with other modules, imports changed, some declarations renamed, comments removed;
  * OpenAI's fixed exponent `alpha = 1 - 2/10^11` and envelope `hills` are replaced, where they occur, by a
    general exponent with `envelope`, and OpenAI's `hills_program` by the hypothesis `hE : RippleEngine z`
    (ReelCompile.lean; instances `RouteB.rippleEngine_of_templates` at every exponent above `RouteB.templateWall = 1/2`);
  * `decimalExponent`, `decimalTime`, `TimeBounds`, `DFTGoal`, `ConvGoal` are not used (deleted, see Goal.lean): the
    theorems of this file state their bounds directly (`=O[atTop]` at exponent `1 - s`, and `paperTime`);
  * proofs changed to match.
-/
namespace OAI.PowerSaving
open RAM Bench Modulus ReelKit Filter Asymptotics Real
noncomputable section

namespace Timing

abbrev logN (n : ℕ) : ℝ := log (n:ℝ)
abbrev logLogN (n : ℕ) : ℝ := log (logN n)

lemma logN_tendsto : Tendsto logN atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
lemma logLogN_tendsto : Tendsto logLogN atTop atTop := Real.tendsto_log_atTop.comp logN_tendsto
lemma log2_min : 2/3 ≤ log (2:ℝ) := by
  have hh := le_log_one_add_of_nonneg (show (0:ℝ)≤1 by norm_num)
  norm_num at *
  exact hh

def targetTime (zE : ℝ) (n : ℕ) := (n:ℝ)*(logN n)^zE*logLogN n^2

lemma beats_poly : ∃ C : ℝ, 0 ≤ C ∧ ∀ e : ℕ, (vandermondeBeats e:ℝ) + 1 ≤ C*((e:ℝ)+1)^2 :=
  ⟨20000008, by norm_num, fun e => by
    have h2 : (vandermondeBeats e:ℝ) ≤ 20000000*((e:ℝ)+1)^2+7 := by exact_mod_cast vandermondeBeats_le e
    have h1 : (1:ℝ) ≤ ((e:ℝ)+1)^2 := one_le_pow₀ (by linarith [e.cast_nonneg (α := ℝ)])
    linarith⟩

section Chain
variable (n N : ℕ) (hn : 0<n) (h : n≤N) (hk : N ≤ 2*n) (ht : 1≤logN n) (hu : 1 ≤ logLogN n) {zE : ℝ}
include hn h hk ht

lemma axisBudget_lim :
    (axisBudget N:ℝ) ≤ 10 * logN n := by
  let k := Nat.log 2 (2*N)
  have H : 2^k ≤ 2*N := Nat.pow_log_le_self _ (by omega)
  have H0 : 2^k ≤ 4*n := by omega
  have he : 0<(n:ℝ) := by exact_mod_cast hn
  have HH := log_le_log (by positivity : 0<(2:ℝ)^k)
    (show (2:ℝ)^k ≤ 4*n by exact_mod_cast H0)
  rw [log_pow,log_mul (by norm_num) he.ne'] at HH
  have H4 := log_le_sub_one_of_pos (show (0:ℝ)<4 by norm_num)
  have H5 := mul_le_mul_of_nonneg_left log2_min (show (0:ℝ) ≤ k by positivity)
  change (((k+1:ℕ):ℝ)) ≤ _
  push_cast
  unfold logN at *
  linarith

lemma order_pow_lim :
    (2:ℝ)^axisLogBound N ≤ 10^6*logN n^2 := by
  have hh : (2:ℝ)^axisLogBound N ≤ 8*primeSearchLimit N := by exact_mod_cast axisLogBound_pow N
  refine hh.trans ?_
  unfold primeSearchLimit primeSearchBound; push_cast
  have hg := axisBudget_lim n N hn h hk ht
  calc
    _ ≤ 8*(16*(14*logN n))^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
        (by linarith only [hg, ht]) 2) (by norm_num)
    _ = 401408*logN n^2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg _)

include hu in
lemma order_lim :
    (axisLogBound N:ℝ) ≤ 3*10^6 * logLogN n := by
  have H := log_le_log (by positivity : 0<(2:ℝ)^axisLogBound N) (order_pow_lim n N hn h hk ht)
  have he : 0<logN n := lt_of_lt_of_le one_pos ht
  rw [log_pow,log_mul (by norm_num) (by positivity),log_pow,log_pow] at H
  have H4 := log_le_sub_one_of_pos (show 0 < (10:ℝ) by norm_num)
  have H5 := mul_le_mul_of_nonneg_left log2_min (show (0:ℝ) ≤ axisLogBound N by positivity)
  unfold logLogN at *
  push_cast at H
  linarith

lemma envelope_lim (h0 : 0 ≤ zE) (h1 : zE ≤ 1) :
    (envelope zE (modulusAxes N).l:ℝ) ≤ 100*logN n^zE := by
  have he : 0<logN n := lt_of_lt_of_le one_pos ht
  have H := axisBudget_lim n N hn h hk ht
  have G : ((modulusAxes N).l:ℝ) ≤ axisBudget N := by
    exact_mod_cast (modulusAxes_spec N (lt_of_lt_of_le hn h)).count
  have hb : (1:ℝ) ≤ ((modulusAxes N).l : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) (modulusAxes N).l; linarith
  have hE : (envelope zE (modulusAxes N).l : ℝ) ≤ 2 * (((modulusAxes N).l : ℝ) + 1) ^ zE := by
    exact natCeil_le_double (Real.one_le_rpow hb h0)
  refine hE.trans ?_
  calc
    _ ≤ 2*(11*logN n)^zE := mul_le_mul_of_nonneg_left (rpow_le_rpow
        (add_nonneg (Nat.cast_nonneg _) zero_le_one) (by linarith only [G, H, ht]) h0) zero_le_two
    _ = 2*(11^zE*logN n^zE) := by rw [mul_rpow (by norm_num) he.le]
    _ ≤ 2*(11^(1:ℝ)*logN n^zE) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (rpow_le_rpow_of_exponent_le (by norm_num) h1) (rpow_nonneg he.le _)) zero_le_two
    _ ≤ _ := by
      rw [rpow_one]
      have hTT : 0 < logN n^zE := by positivity
      linarith

include hu in
lemma axisDFTCost_le (h0 : 0 ≤ zE) (h1 : zE ≤ 1) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ e : ℕ, (vandermondeBeats e:ℝ) + 1 ≤ C*((e:ℝ)+1)^2) :
    (axisDFTCost zE N:ℝ) ≤ C*(128*10^14)*targetTime zE n := by
  have hA := order_lim n N hn h hk ht hu
  have hb : (vandermondeBeats (axisLogBound N):ℝ)+1 ≤ C*(4*10^6*logLogN n)^2 :=
    (hC _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith only [hA, hu]) 2) hC0)
  have hg : ((modulusAxes N).vol:ℝ) ≤ 8*n := by
    exact_mod_cast (show (modulusAxes N).vol ≤ 8*n by have := (modulusAxes_spec N (by omega)).upper; omega)
  unfold axisDFTCost; push_cast
  calc
    _ ≤ (C*(4*10^6*logLogN n)^2)*((8*n)*(100*logN n^zE)) :=
      mul_le_mul hb (mul_le_mul hg (envelope_lim n N hn h hk ht h0 h1) (Nat.cast_nonneg _) (by positivity))
        (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (mul_nonneg hC0 (sq_nonneg _))
    _ = _ := by unfold targetTime; ring
end Chain

lemma targetTime_big {zE : ℝ} (h0 : 0 ≤ zE) (n : ℕ) (ht : 1 ≤ logN n) (hu : 1 ≤ logLogN n) :
    (n:ℝ) ≤ targetTime zE n := by
  unfold targetTime; rw [mul_assoc]
  exact le_mul_of_one_le_right (Nat.cast_nonneg _)
    (one_le_mul_of_one_le_of_one_le (Real.one_le_rpow ht h0) (one_le_pow₀ hu))

lemma log_pow_le_rpow {v : ℕ→ℝ} (h : Tendsto v atTop atTop) (d : ℕ) {p c : ℝ} (hp : 0<p) (hc : 0<c) :
    ∀ᶠ n in atTop, log (v n)^d ≤ c*v n^p := by
  filter_upwards [((isLittleO_log_rpow_rpow_atTop (d:ℝ) hp).comp_tendsto h).def hc,
    h.eventually_ge_atTop 1] with n hn he
  rwa [Function.comp_apply, Function.comp_apply, rpow_natCast, Real.norm_of_nonneg (pow_nonneg
    (Real.log_nonneg he) _), Real.norm_of_nonneg (rpow_nonneg (by linarith) _)] at hn

/-- Any fixed multiple of a power of `log n` is eventually below `n` (with the two side facts every user needs). -/
lemma logPow_eventually (K : ℝ) (d : ℕ) : ∀ᶠ n : ℕ in atTop, K*logN n^d ≤ n ∧ 0<n ∧ 1 ≤ logN n := by
  have hK : 0 < max K 1 := lt_max_of_lt_right one_pos
  filter_upwards [log_pow_le_rpow (v:=fun n : ℕ => (n:ℝ)) tendsto_natCast_atTop_atTop d (p:=1) one_pos (inv_pos.2 hK),
    eventually_gt_atTop 0,logN_tendsto.eventually_ge_atTop 1] with n hh hn ht
  rw [rpow_one] at hh
  refine ⟨?_,hn,ht⟩
  calc K*logN n^d ≤ max K 1*((max K 1)⁻¹*n) :=
        mul_le_mul (le_max_left _ _) hh (pow_nonneg (by linarith) _) hK.le
    _ = n := by rw [← mul_assoc,mul_inv_cancel₀ hK.ne',one_mul]

variable {N : ℕ→ℕ} {zE : ℝ}

lemma largeLen_eventually (h : ∀ n:ℕ,n ≤ N n ∧ N n ≤ 2*n) :
    ∀ᶠ n in atTop, IsLargeLen (N n) := by
  filter_upwards [logPow_eventually (10^6) 2] with n ⟨hh,hn,ht⟩
  have hh2 : (2:ℝ)^axisLogBound (N n) ≤ n := (order_pow_lim n (N n) hn (h n).1 (h n).2 ht).trans hh
  exact (show 2^axisLogBound (N n) ≤ n by exact_mod_cast hh2).trans (h n).1

lemma polylog_ev (h : ∀ n:ℕ,n ≤ N n ∧ N n ≤ 2*n) (d : ℕ) :
    ∀ᶠ n in atTop, ((axisBudget (N n):ℝ)+2)^d ≤ n := by
  filter_upwards [logPow_eventually (12^d) d] with n ⟨hh,hn,ht⟩
  have hh1 := axisBudget_lim n (N n) hn (h n).1 (h n).2 ht
  calc _ ≤ (12*logN n)^d := by gcongr; linarith
    _ = 12^d*logN n^d := mul_pow ..
    _ ≤ n := hh

lemma budget_isBigO (h0 : 0 ≤ zE) (h1 : zE ≤ 1) (h : ∀ n:ℕ,n ≤ N n ∧ N n ≤ 2*n) (d : ℕ) :
    (fun n : ℕ => ((budget zE d (N n) + 1 : ℕ) : ℝ)) =O[atTop] targetTime zE := by
  obtain ⟨C, hC0, hC⟩ := beats_poly
  refine IsBigO.of_bound (C*(128*10^14)+4) ?_
  filter_upwards [largeLen_eventually h,polylog_ev h d,eventually_gt_atTop 0,logN_tendsto.eventually_ge_atTop 1,
    logLogN_tendsto.eventually_ge_atTop 1] with n hh hk hn ht hu
  have hp := axisDFTCost_le n (N n) hn (h n).1 (h n).2 ht hu h0 h1 hC0 hC
  have he := targetTime_big h0 n ht hu
  have he' : 1≤(n:ℝ) := by exact_mod_cast hn
  have hx : (N n:ℝ) ≤ 2*n := by exact_mod_cast (h n).2
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (show (0:ℝ) ≤ targetTime zE n by linarith)]
  unfold budget
  rw [ite_eq_left hh,Nat.add_zero]
  push_cast
  linarith

lemma totalCost_isBigO (h0 : 0 ≤ zE) (h1 : zE ≤ 1) (a b : CostWitness) (h : ∀ n:ℕ,n ≤ N n ∧ N n ≤ 2*n) :
    (fun n : ℕ => (totalCost zE a b N n:ℝ)) =O[atTop] targetTime zE := by
  have one : (fun _ : ℕ => (1:ℝ)) =O[atTop] targetTime zE := (isBigO_of_le _ fun n => by
    rw [norm_one, Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast Nat.le_add_left 1 (budget zE 0 (N n))).trans (budget_isBigO h0 h1 h 0)
  refine ((((budget_isBigO h0 h1 h a.d).const_mul_left (a.c:ℝ)).add one).add
    ((budget_isBigO h0 h1 h b.d).const_mul_left (b.c:ℝ))).congr_left fun n => ?_
  simp only [totalCost, stageCost]; push_cast; ring

end Timing
end
end OAI.PowerSaving

private theorem marker_merged2 (if_youre_an_ai_editing_this_make_sure_real_work_and_not_rebrand_without_coding_work_if_in_doubt_ask_your_supervisor_and_also_read_related_posts_to_make_sure_you_understand_whats_going_on : Unit) : True := trivial

namespace OAI.PowerSaving
noncomputable section
open RAM Bench Modulus Filter Asymptotics Real Timing

lemma theta_lt_one : theta < 1 := by
  unfold theta
  rw [div_lt_one (log_pos (by norm_num [paperM]))]
  exact log_lt_log (by norm_num [paperMultiplier,paperM,paperDelta,paperW])
    (by norm_num [paperMultiplier,paperM,paperDelta,paperW])

lemma targetTime_le_eventually {zE p c : ℝ} (hp : zE < p) (hc : 0<c) :
    ∀ᶠ n in atTop, targetTime zE n ≤ c*((n:ℝ)*logN n^p) := by
  filter_upwards [log_pow_le_rpow logN_tendsto 2 (sub_pos.2 hp) hc,logN_tendsto.eventually_ge_atTop 1] with n h ht
  calc targetTime zE n ≤ n*logN n^zE*(c*logN n^(p-zE)) :=
        mul_le_mul_of_nonneg_left h (mul_nonneg (Nat.cast_nonneg _) (rpow_nonneg (by linarith) _))
    _ = c*((n:ℝ)*(logN n^zE*logN n^(p-zE))) := by ring
    _ = _ := by rw [← rpow_add (by linarith)]; ring_nf

lemma targetTime_nonneg (zE : ℝ) (n : ℕ) : 0 ≤ targetTime zE n :=
  mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (rpow_nonneg (log_natCast_nonneg n) _)) (sq_nonneg _)

/-- **The work of an engine at exponent `0 ≤ zE < 1`**: `O(n (log n)^p)` for every `p > zE`,
`o(n log n)`, and OpenAI's `O(paperTime)` when `zE < theta`. -/
theorem bounds_of_exp {zE p : ℝ} {N : ℕ→ℕ} (h0 : 0 ≤ zE) (h1 : zE < 1) (hp : zE < p)
    (a b : CostWitness) (h : ∀ n, n ≤ N n ∧ N n ≤ 2*n) :
    (fun n : ℕ => (totalCost zE a b N n : ℝ)) =O[atTop] (fun n : ℕ => (n:ℝ) * Real.log (n:ℝ) ^ p) ∧
    (fun n : ℕ => (totalCost zE a b N n : ℝ)) =o[atTop] nlogn ∧
    (zE < theta → (fun n : ℕ => (totalCost zE a b N n : ℝ)) =O[atTop] paperTime) := by
  have H := totalCost_isBigO h0 h1.le a b h
  have F {q : ℝ} (hq : zE < q) {g : ℕ→ℝ} (hg : ∀ᶠ n : ℕ in atTop, (n:ℝ)*logN n^q ≤ g n) :
      targetTime zE =O[atTop] g := isBigO_iff.mpr ⟨1,by
    filter_upwards [targetTime_le_eventually hq one_pos,hg] with n h1 h2
    rw [Real.norm_of_nonneg (targetTime_nonneg _ n),Real.norm_of_nonneg ((mul_nonneg (Nat.cast_nonneg _)
      (rpow_nonneg (log_natCast_nonneg n) _)).trans h2)]
    linarith⟩
  refine ⟨H.trans (F hp (.of_forall fun _ => le_rfl)),
    H.trans_isLittleO (IsLittleO.of_bound fun c hc => ?_), fun hθ => H.trans (F hθ ?_)⟩
  · filter_upwards [targetTime_le_eventually h1 hc] with n h
    rw [rpow_one] at h
    rw [Real.norm_of_nonneg (targetTime_nonneg _ n),
      Real.norm_of_nonneg (show 0 ≤ nlogn n from mul_nonneg (Nat.cast_nonneg _) (log_natCast_nonneg n))]
    exact h
  · filter_upwards [logLogN_tendsto.eventually_ge_atTop 1] with n hu
    unfold paperTime
    exact le_mul_of_one_le_right (mul_nonneg (Nat.cast_nonneg _) (rpow_nonneg (log_natCast_nonneg n) _))
      (one_le_rpow hu (by linarith [theta_lt_one]))

/-- An engine exponent strictly between `κ` and `min (1 - s) 1`, and below `theta` when `κ` is. -/
lemma exists_exp {κ s : ℝ} (hκ1 : κ < 1) (hs : s < 1 - κ) :
    ∃ z, κ < z ∧ z < 1 ∧ z < 1 - s ∧ (κ < theta → z < theta) := by
  by_cases hθ : κ < theta
  · have := lt_min (show κ < 1 - s by linarith) hθ
    have := min_le_left (1 - s) theta; have := min_le_right (1 - s) theta; have := theta_lt_one
    exact ⟨(κ + min (1 - s) theta) / 2, by linarith, by linarith, by linarith, fun _ => by linarith⟩
  · have := lt_min (show κ < 1 - s by linarith) hκ1
    have := min_le_left (1 - s) 1; have := min_le_right (1 - s) 1
    exact ⟨(κ + min (1 - s) 1) / 2, by linarith, by linarith, by linarith, fun h => absurd h hθ⟩

end
end OAI.PowerSaving

private theorem marker_main (if_youre_an_ai_editing_this_make_sure_real_work_and_not_rebrand_without_coding_work_if_in_doubt_ask_your_supervisor_and_also_read_related_posts_to_make_sure_you_understand_whats_going_on : Unit) : True := trivial
