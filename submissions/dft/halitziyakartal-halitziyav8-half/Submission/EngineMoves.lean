-- Bit words, role tables and the direct ripple (part 1); letter splittings and the engine's move
-- language (part 2). Each part has its own notices and credits; see texts/credits.lean.
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.BinaryKernel
import Submission.CostCalculus
import Submission.DFTIdentities
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
set_option linter.all false


-- ===== begin part 1: bit words, role tables, the direct ripple =====
section

/-! Words of bit vectors and their machine addresses.

A *word* (`Sky α f`) is `f` letters, each letter a vector of `α`-bits; a *role table*
(`Data α ρ f`) holds one amplitude per role and word. A letter matrix `M` acts on a word
amplitude letter by letter (`letterwise`, a monoid map into linear endomorphisms). Addresses: `bits k` numbers `k`-bit vectors in binary,
`gridLayout X r f` numbers a pad of `r` bits together with a word, and `roleLayout` adds the role. -/

namespace OAI
namespace PowerSaving.Binary
open Matrix Finset

section Words
variable (α ρ : Type*) (f : ℕ)
abbrev Sky := Fin f → Space α
abbrev Data := ρ → Sky α f → ℂ
end Words

section
variable {α ρ : Type*} [Fintype α] [DecidableEq α]

/-- A letter matrix acting on word amplitudes, one copy per letter (the vector is multiplied by
the coordinatewise product `digitProd` of `f` copies), bundled as a monoid map from letter
matrices to linear endomorphisms of the amplitudes. -/
def letterwise (f : ℕ) : CMat α →* Module.End ℂ (Sky α f → ℂ) where
  toFun M := Matrix.toLin' (digitProd fun _ : Fin f => M)
  map_one' := by rw [digitProd_one, Matrix.toLin'_one, Module.End.one_eq_id]
  map_mul' M N := by rw [← digitProd_mul, Matrix.toLin'_mul, Module.End.mul_eq_comp]

lemma letterwise_apply (f : ℕ) (M : CMat α) (y : Sky α f → ℂ) :
    letterwise f M y = digitProd (fun _ : Fin f => M) *ᵥ y := Matrix.toLin'_apply _ _

/-- The pointwise form: a sum over words of letterwise products of entries. -/
lemma letterwise_sum (f : ℕ) (M : CMat α) (y : Sky α f → ℂ) (b : Sky α f) :
    letterwise f M y b = ∑ b', (∏ k, M (b k) (b' k)) * y b' := by
  rw [letterwise_apply]; rfl

@[simp] theorem matAct_mul (f : ℕ) (M N : CMat α) (x : Sky α f → ℂ) :
    letterwise f M (letterwise f N x) = letterwise f (M*N) x := by
  rw [map_mul, Module.End.mul_apply]

@[simp] theorem matAct_one (f : ℕ) (x : Sky α f → ℂ) : letterwise f (1 : CMat α) x = x := by
  rw [map_one, Module.End.one_apply]

def roleAct (f : ℕ) [DecidableEq ρ] (r : ρ) (M : CMat α) (x : Data α ρ f) : Data α ρ f :=
  fun j => if j = r then letterwise f M (x j) else x j

@[simp] lemma roleAct_mul (f : ℕ) [DecidableEq ρ] (r : ρ) (M N : CMat α) (x : Data α ρ f) :
    roleAct f r M (roleAct f r N x) = roleAct f r (M*N) x := by
  funext j
  unfold roleAct
  split_ifs
  · exact matAct_mul f M N (x j)
  · rfl

def point (f : ℕ) (g : (ρ→ℂ)→(ρ→ℂ)) (x : Data α ρ f) : Data α ρ f :=
  fun r i => g (fun r => x r i) r
end

section Address
variable {α : Type*}
abbrev Bits (k : ℕ) := Space (Fin k)

def bitLayout : Layout F := Layout.std 2

noncomputable def bits (k : ℕ) : Layout (Bits k) := (Layout.std k).digits bitLayout

@[simp] theorem bits_len (k : ℕ) : (bits k).n = 2^k := rfl

theorem bits_loc (k : ℕ) (x : Bits k) : (bits k).loc x = ∑ i : Fin k, (x i).val*2^i.val :=
  Layout.digits_code _ _ x

theorem bits_div (k : ℕ) (x : Bits k) (i : Fin k) : ((bits k).loc x / 2^i.val)%2 = (x i).val :=
  Layout.digits_entry _ _ x i

lemma bits_lt (k : ℕ) (a : Bits k) : (bits k).loc a < 2^k := (bits k).bd a

theorem bits_lit (k : ℕ) : (bits k).loc (fun _ => 1)+1 = 2^k := by
  rw [bits_loc]
  simp only [show (1:F).val = 1 from rfl, one_mul]
  rw [Fin.sum_univ_eq_sum_range (fun i => 2^i) k]
  induction k with
  | zero => rfl
  | succ k ih => rw [Finset.sum_range_succ, pow_succ]; omega

abbrev Grid (α : Type*) (r f : ℕ) := Bits r × Sky α f

def rows (α : Type*) (f : ℕ) : Sky α f ≃ (α → Bits f) := Equiv.piComm fun (_ : Fin f) (_ : α) => F

noncomputable def skyLayout (X : Layout α) (f : ℕ) : Layout (Sky α f) :=
  (X.digits (bits f)).comap (rows α f)

noncomputable def gridLayout (X : Layout α) (r f : ℕ) : Layout (Grid α r f) :=
  (bits r).pair (skyLayout X f)


lemma gridLayout_n (X : Layout α) (r f : ℕ) : (gridLayout X r f).n = (2^f)^X.n * 2^r := Nat.mul_comm _ _

@[simp] theorem gridLayout_len (X : Layout α) (r f) : (gridLayout X r f).n = 2^(X.n*f+r) := by
  rw [gridLayout_n, ← pow_mul, ← pow_add, Nat.mul_comm f]

lemma skyLayout_loc [Fintype α] (X : Layout α) (f : ℕ) (y : Sky α f) :
    (skyLayout X f).loc y = ∑ a, (bits f).loc (fun l => y l a) * (2^f)^(X.loc a) :=
  Layout.digits_code X (bits f) (rows α f y)

noncomputable def gridToBits (X : Layout α) (r f : ℕ) {k} (h : X.n*f+r=k) : Grid α r f ≃ Bits k :=
  (gridLayout X r f).index.trans ((finCongr (by rw [gridLayout_len, bits_len, h])).trans (bits k).index.symm)

lemma gridToBits_loc {α : Type*} [Fintype α] (X : Layout α) (r f) {k}
    (h : X.n*f+r=k) (x : Grid α r f) : (bits k).loc (gridToBits X r f h x) = (gridLayout X r f).loc x :=
  Layout.loc_atFin (bits k) _

/-- Lay the `r` bits of each of the `f` letters side by side: bit `a` of letter `l` goes to the
`Fin (r*f)` position of `(a, l)`. -/
def bitFlat (r f : ℕ) : Sky (Fin r) f ≃ Bits (r*f) where
  toFun y k := y (finProdFinEquiv.symm k).2 (finProdFinEquiv.symm k).1
  invFun b l a := b (finProdFinEquiv (a, l))
  left_inv y := by funext l a; simp only [Equiv.symm_apply_apply]
  right_inv b := by funext k; simp only [Prod.mk.eta, Equiv.apply_symm_apply]

lemma skyBits_at (r f : ℕ) (y : Sky (Fin r) f) (a : Fin r) (l : Fin f) :
    bitFlat r f y (finProdFinEquiv (a, l)) = y l a := by
  simp only [bitFlat, Equiv.coe_fn_mk, Equiv.symm_apply_apply]

/-- Inside a block of `f` binary digits, digit `l < f` of `M mod 2^f` is digit `l` of `M`. -/
lemma digit_in_block (M : ℕ) {f l : ℕ} (hl : l < f) : M % 2 ^ f / 2 ^ l % 2 = M / 2 ^ l % 2 := by
  have h : 2 ^ f = 2 ^ l * 2 ^ (f - l) := by rw [← pow_add, Nat.add_sub_cancel' hl.le]
  rw [h, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (Nat.sub_ne_zero_of_lt hl))]

/-- Unflattening an `r*f`-bit vector and reading it as a word under the standard letter layout
keeps its address: the two numbers have the same binary digits. -/
lemma bitFlat_skyLayout_loc (r f : ℕ) (u : Bits (r*f)) :
    (skyLayout (Layout.std r) f).loc ((bitFlat r f).symm u) = (bits (r*f)).loc u := by
  have hlt : (skyLayout (Layout.std r) f).loc ((bitFlat r f).symm u) < (bits (r*f)).n :=
    calc _ < (2 ^ f) ^ r := (skyLayout (Layout.std r) f).bd _
      _ = 2 ^ (r * f) := by rw [← pow_mul, Nat.mul_comm]
  let v := (bits (r*f)).atFin ⟨_, hlt⟩
  have hv : (bits (r*f)).loc v = (skyLayout (Layout.std r) f).loc ((bitFlat r f).symm u) :=
    Layout.loc_atFin _ _
  suffices v = u by rw [← hv, this]
  funext p
  obtain ⟨⟨a, l⟩, rfl⟩ := finProdFinEquiv.surjective p
  apply ZMod.val_injective
  have e1 : (skyLayout (Layout.std r) f).loc ((bitFlat r f).symm u) / (2 ^ f) ^ a.val % 2 ^ f =
      (bits f).loc (fun l' => ((bitFlat r f).symm u) l' a) :=
    Layout.digits_entry (Layout.std r) (bits f) (rows (Fin r) f _) a
  rw [← bits_div, hv, finProdFinEquiv_apply_val, pow_add, Nat.mul_comm (2 ^ l.val),
    ← Nat.div_div_eq_div_mul, pow_mul, ← digit_in_block _ l.isLt, e1, bits_div]
  rfl

/-- The ripple kernel on `r*f` bits, read along the flattening on rows and columns, is the
letterwise product of kernels on `r` bits. -/
lemma rippleMat_skyBits (r f : ℕ) :
    (rippleMat (Fin (r*f))).submatrix (bitFlat r f) (bitFlat r f) =
      digitProd fun _ : Fin f => rippleMat (Fin r) := by
  ext u v
  simp only [Matrix.submatrix_apply, rippleMat, digitProd_apply]
  rw [← finProdFinEquiv.prod_comp, Fintype.prod_prod_type, Finset.prod_comm]
  simp only [skyBits_at]

noncomputable def ripple (k : ℕ) (x : Bits k → ℂ) := rippleMat (Fin k) *ᵥ x
end Address

section
variable {α : Type*} [Fintype α] [DecidableEq α]

lemma dir_mulVec (z : Space α) (u : Space α → ℂ) (t : Space α) :
    (dir z *ᵥ u) t = ca * u t + cb * u (t + z) := by
  simp only [mulVec, dotProduct, dir, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero, shift, add_mul, ite_mul, zero_mul, sum_add_distrib,
    sum_ite_eq, mem_univ, ↓reduceIte]

end

def part (k lo b : ℕ) (x : Bits k) : ℂ := ∏ c : Fin k, if lo ≤ c.val ∧ c.val < b then phaseI (x c) else 1

noncomputable def rippleUpTo (k lo : ℕ) (u : Bits k → ℂ) (b : ℕ) : Bits k → ℂ := walshConj (part k lo b) *ᵥ u

lemma rippleUpTo_start (k lo : ℕ) (u : Bits k → ℂ) : rippleUpTo k lo u lo = u := by
  have : part k lo lo = fun _ => 1 := funext fun x =>
    Finset.prod_eq_one fun c _ => if_neg (by omega)
  rw [rippleUpTo, this, walshConj_one, one_mulVec]

lemma rippleUpTo_last (k : ℕ) (u : Bits k → ℂ) : rippleUpTo k 0 u k = ripple k u := by
  have : part k 0 k = phaseProd := funext fun x => by simp only [part, zero_le, Fin.is_lt, and_self, ↓reduceIte, phaseProd]
  simp only [rippleUpTo, this, walshConj_phaseProd, ripple]

lemma walshConj_part_succ {k lo b : ℕ} (hl : lo ≤ b) (hb : b < k) :
    walshConj (part k lo (b+1)) = dir (eu (⟨b, hb⟩ : Fin k)) * walshConj (part k lo b) := by
  rw [dir_phase, walshConj_mul]
  congr 1; funext x
  have key : ∀ c : Fin k, (if lo ≤ c.val ∧ c.val < b+1 then phaseI (x c) else 1) =
      (if c = ⟨b, hb⟩ then phaseI (x c) else 1) * (if lo ≤ c.val ∧ c.val < b then phaseI (x c) else 1) := by
    intro c
    rcases lt_trichotomy c.val b with h | h | h
    · by_cases hc : lo ≤ c.val
      · simp only [hc, show c.val < b + 1 by omega, and_self, ↓reduceIte, Fin.ext_iff, h.ne, h, one_mul]
      · simp only [hc, Order.lt_add_one_iff, false_and, ↓reduceIte, Fin.ext_iff, h.ne, mul_one]
    · simp only [h, hl, lt_add_iff_pos_right, Order.lt_one_iff, and_self, ↓reduceIte, Fin.ext_iff, lt_self_iff_false, and_false, mul_one]
    · simp only [show ¬c.val < b + 1 by omega, and_false, ↓reduceIte, Fin.ext_iff,
        show c.val ≠ b by omega, show ¬c.val < b by omega, mul_one]
  simp only [part, key, prod_mul_distrib]
  simp only [prod_ite_eq', mem_univ, ↓reduceIte, dot_eu_left]

lemma rippleUpTo_succ {k lo b : ℕ} (hl : lo ≤ b) (hb : b < k) (u : Bits k → ℂ) (t : Bits k) :
    rippleUpTo k lo u (b+1) t = ca * rippleUpTo k lo u b t + cb * rippleUpTo k lo u b (t + eu ⟨b, hb⟩) := by
  simp only [rippleUpTo, walshConj_part_succ hl hb, ← mulVec_mulVec, dir_mulVec]

lemma bits_flip (k : ℕ) (t : Bits k) {b : ℕ} (hb : b < k) : (bits k).loc (t + eu ⟨b, hb⟩) =
    (bits k).loc t + 2^b - 2 * 2^b * ((bits k).loc t / 2^b % 2) := by
  have hs : ∑ j ∈ (univ : Finset (Fin k)).erase (⟨b, hb⟩ : Fin k), ((t + eu (⟨b, hb⟩ : Fin k)) j).val * 2^j.val =
      ∑ j ∈ (univ : Finset (Fin k)).erase (⟨b, hb⟩ : Fin k), (t j).val * 2^j.val :=
    Finset.sum_congr rfl fun (j : Fin k) hj => by
      simp only [Pi.add_apply, eu, Ne.symm (Finset.ne_of_mem_erase hj), ↓reduceIte, add_zero]
  rw [bits_div k t ⟨b, hb⟩, bits_loc, bits_loc,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨b, hb⟩ : Fin k)),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨b, hb⟩ : Fin k)), hs]
  rcases bit_cases (t ⟨b, hb⟩) with h | h <;>
    simp only [Pi.add_apply, h, eu, ↓reduceIte, zero_add, show (1:F).val = 1 from rfl, one_mul,
      ZMod.val_zero, zero_mul, mul_zero, tsub_zero, cancel, mul_one] <;> omega

lemma add_step {k j : ℕ} (a b : Bits k) (hj : j < k) :
    (bits k).loc (a+b) % 2^(j+1) = (bits k).loc (a+b) % 2^j +
      2^j * (((bits k).loc a / 2^j % 2 + (bits k).loc b / 2^j % 2) % 2) := by
  rw [Nat.mod_pow_succ, bits_div k (a+b) ⟨j, hj⟩, bits_div k a ⟨j, hj⟩, bits_div k b ⟨j, hj⟩,
    Pi.add_apply, ZMod.val_add]
end PowerSaving.Binary

namespace PowerSaving.RAM
open Binary Matrix Ty Finset
noncomputable section
universe U V

section
variable {ι : Type U}
abbrev Has (m : Bool) (B : ι → ℕ) (s t : Ty) (x : ι → T s) (y : ι → T t) : Prop :=
  Can m B s t x y (fun _ => 0)
abbrev Knows (m : Bool) (B : ι → ℕ) (s : Ty) (x : ι → T s) (y : ι → ℕ) : Prop :=
  Has m B s w x y
end

lemma Able.branch {ι : Type U} {r : Port} {m : Bool} {b : Bank r ι} {s t : Ty} {x : ι → T s} {y : ι → T t}
    {n W Z : ι → ℕ} (hn : Can m b.B s w x n W) (P : ι → Prop) (hP : ∀ i, n i = 0 ↔ P i)
    (hz : Able m (b.comap fun i : {i // P i} => i.1) s t (fun i => x i.1) (fun i => y i.1) (fun i => W i.1) (fun i => Z i.1))
    (hnz : Able m (b.comap fun i : {i // ¬ P i} => i.1) s t (fun i => x i.1) (fun i => y i.1) (fun i => W i.1)
      (fun i => Z i.1)) : Able m b s t x y W Z := by
  have yes : Able m (b.comap fun i : {i // n i = 0} => i.1) s t (fun i => x i.1) (fun i => y i.1) (fun i => W i.1)
      (fun i => Z i.1) := hz.reindex fun i : {i // n i = 0} => (⟨i.1, (hP i.1).1 i.2⟩ : {i // P i})
  have no : Able m (b.comap fun i : {i // n i ≠ 0} => i.1) s t (fun i => x i.1) (fun i => y i.1) (fun i => W i.1)
      (fun i => Z i.1) := hnz.reindex fun i : {i // n i ≠ 0} => (⟨i.1, mt (hP i.1).2 i.2⟩ : {i // ¬ P i})
  exact ((Able.of_can hn).ifz yes no).weaken (Dom.two W) fun _ => (Nat.zero_add _).le

def xorTab (k : ℕ) : Tape ℕ := ((bits k).pair (bits k)).tape fun q => (bits k).loc (q.1 + q.2)

private abbrev XP {ι : Type U} (f : ι → ℕ) := Σ i, Bits (f i) × Bits (f i)
private abbrev XD {ι : Type U} (f : ι → ℕ) := During (fun d : XP f => f d.1)

section
variable {ι : Type U} {m : Bool} {s : Ty} {x : ι→T s} {B f : ι→ℕ}

private lemma xbit {κ : Type U} {m : Bool} {s : Ty} {y : κ → T s} {B A C Q R : κ → ℕ}
    (hA : Knows m B s y A) (hC : Knows m B s y C) (hQ : Knows m B s y Q) (hR : Knows m B s y R)
    (sA : Small B A) (sC : Small B C) (sQ : Small B Q) (sR : Small B R) :
    Knows m B s y fun d => R d + Q d * ((A d / Q d % 2 + C d / Q d % 2) % 2) :=
  have sb : Small B fun d => A d / Q d % 2 + C d / Q d % 2 := sA.div.mod.add sC.div.mod
  hR.plus (hQ.times ((((hA.dvdW hQ sA).modW (Can.wc 2) sA.div).plus ((hC.dvdW hQ sC).modW
    (Can.wc 2) sC.div) sA.div.mod sC.div.mod).modW (Can.wc 2) sb) sQ sb.mod) sR (sQ.mul sb.mod)

theorem Can.xor_prepare (hf : Can m B s w x f (fun _ => 0))
    (hg : Can m B s w x (fun i => 2^f i) (fun _ => 0))
    (hB : Small B f) (hd : Small B fun i => 2^f i) :
    Can m B s (a w) x (fun i => xorTab (f i)) (fun i => (2^f i)^3) := by
  have hD := hd.reindex fun D : XD f => D.i.1
  have sQ : Small (fun D : XD f => B D.i.1) fun D => 2^D.j :=
    hD.mono fun D => Nat.pow_le_pow_right two_pos D.hj.le
  have sL := fun (u : ∀ D : XD f, Bits (f D.i.1)) => Small.loc (x := u) (L := fun D => bits (f D.i.1)) hD
  have hs := (hd.mul hd).reindex (Sigma.fst : XP f → ι)
  have h3 : Has m (fun d : XP f => B d.1) (p s w) (p w (p w w))
      (fun d => (x d.1, ((bits (f d.1)).pair (bits (f d.1))).loc d.2))
      (fun d => (f d.1, (bits (f d.1)).loc d.2.1, (bits (f d.1)).loc d.2.2)) :=
    (Can.first.then_do (hf.reindex Sigma.fst)).pair ((Can.addr_high (u := fun d : XP f => d.2)
      (L := fun d : XP f => bits (f d.1)) (R := fun d : XP f => bits (f d.1)) Can.second
      (Can.first.then_do (hg.reindex Sigma.fst)) hs).pair (Can.addr_low (u := fun d : XP f => d.2)
      (L := fun d : XP f => bits (f d.1)) (R := fun d : XP f => bits (f d.1)) Can.second
      (Can.first.then_do (hg.reindex Sigma.fst)) hs))
  refine (Can.layout (t := w) (L := fun i => (bits (f i)).pair (bits (f i))) (P := f)
    (v := fun i q => (bits (f i)).loc (q.1 + q.2)) (hg.times hg hd hd)
    (((h3.pipe (Can.loop (n := fun d : XP f => f d.1) (t := p w w) (W := fun _ => 0) (W' := fun _ => 0)
      (v := fun (d : XP f) j => ((bits (f d.1)).loc (d.2.1 + d.2.2) % 2^j, 2^j)) (uB := fun _ _ => 0)
      Can.first (((Can.wc 0).pair (Can.wc 1)).congr fun _ => by simp [Nat.mod_one])
      ((Can.pair (xbit Can.first.snd.fst Can.first.snd.snd Can.second.snd.snd Can.second.snd.fst
        (sL _) (sL _) sQ (sQ.mono fun D => (Nat.mod_lt _ (pow_pos two_pos _)).le))
        (Can.second.snd.snd.plus Can.second.snd.snd sQ sQ)).congr fun D =>
          Prod.ext (add_step _ _ D.hj).symm ((pow_succ 2 D.j).trans (mul_two _)).symm)
      (hB.reindex Sigma.fst))).fst.congr fun d =>
      Nat.mod_eq_of_lt (bits_lt _ _)).mono fun _ => by simp)
    (hd.mul hd)).weaken ⟨2, fun i => ?_⟩
  have h1 := Nat.mul_le_mul (le_refl (2^f i * 2^f i)) (Nat.lt_two_pow_self (n := f i)).le
  have h2 := Nat.le_mul_of_pos_right (2^f i * 2^f i) (Nat.two_pow_pos (f i))
  show 0 + 2^f i * 2^f i + 2^f i * 2^f i * f i + 1 ≤ 2 * ((2^f i)^3 + 1)
  rw [pow_three']; omega
end

variable {ι : Type U}

theorem knows_pair_iff {m : Bool} {B : ι → ℕ} {s : Ty} {x : ι → T s} {β₁ β₂ : ι → Type*}
    {L₁ : ∀ i, Layout (β₁ i)} {L₂ : ∀ i, Layout (β₂ i)} {u : ∀ i, β₁ i × β₂ i}
    (n₂ : Knows m B s x fun i => (L₂ i).n) (s₁ : Small B fun i => (L₁ i).n) (s₂ : Small B fun i => (L₂ i).n) :
    (Knows m B s x fun i => ((L₁ i).pair (L₂ i)).loc (u i)) ↔
      (Knows m B s x fun i => (L₁ i).loc (u i).1) ∧ Knows m B s x fun i => (L₂ i).loc (u i).2 :=
  ⟨fun h => ⟨Can.addr_high h n₂ (s₁.mul s₂), Can.addr_low h n₂ (s₁.mul s₂)⟩, fun h => Can.addr_join h.1 h.2 n₂ s₁ s₂⟩

structure BitCtx (m : Bool) (B f : ι → ℕ) (s : Ty) (x : ι → T s) : Prop where
  power : Knows m B s x (fun i => 2^f i)
  given : Knows m B s x f
  table : Has m B s (a w) x (fun i => xorTab (f i))
  bound : Small B fun i => 2^f i

namespace BitCtx
variable {m : Bool} {B f : ι → ℕ} {s t : Ty} {x : ι → T s}
variable (g : BitCtx m B f s x)
include g

lemma descend {κ : Type V} (j : κ → ι) (y : κ → T t)
    (h : Has m (fun k => B (j k)) t s y (fun k => x (j k))) :
    BitCtx m (fun k => B (j k)) (fun k => f (j k)) t y where
  power := h.then_do (g.power.reindex j)
  given := h.then_do (g.given.reindex j)
  table := h.then_do (g.table.reindex j)
  bound := g.bound.reindex j

lemma span (e r : ℕ) :
    Knows m B s x (fun i => (2^f i)^e * 2^r) ∧ Small B fun i => (2^f i)^e * 2^r :=
  have S := (g.bound.pow e).mul (Small.const B (2^r))
  ⟨(Can.wpow_fixed e g.power g.bound).wmul (Can.wc _) S, S⟩

lemma knows_two_pow (e : ℕ) : Knows m B s x fun i => 2^(e * f i) :=
  (Can.wpow_fixed e g.power g.bound).congr fun i => by rw [← pow_mul, Nat.mul_comm]

lemma const_bits (c : F) : Knows m B s x fun i => (bits (f i)).loc (fun _ => c) := by
  rcases bit_cases c with rfl | rfl
  · exact (Can.wc 0).congr fun i => by simp [bits_loc]
  · exact (g.power.wsub (Can.wc 1) g.bound.sub).congr fun i =>
      (Nat.eq_sub_of_add_eq (bits_lit (f i))).symm

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
lemma grid_small (X : Layout α) (r : ℕ) : Small B fun i => (gridLayout X r (f i)).n :=
  (g.span X.n r).2.mono fun i => (gridLayout_n X r (f i)).le

omit [Fintype α] [DecidableEq α] in
lemma grid_size (X : Layout α) (r : ℕ) : Knows m B s x (fun i => (gridLayout X r (f i)).n) :=
  (g.span X.n r).1.congr fun i => (gridLayout_n X r (f i)).symm

omit [Fintype α] [DecidableEq α] in
private lemma skyLayout_size (X : Layout α) : Knows m B s x fun i => (skyLayout X (f i)).n :=
  (g.span X.n 0).1.congr fun _ => mul_one _

omit [Fintype α] [DecidableEq α] in
private lemma skyLayout_small (X : Layout α) : Small B fun i => (skyLayout X (f i)).n :=
  (g.span X.n 0).2.mono fun _ => (mul_one _).ge

lemma sky_get (X : Layout α) (v : ∀ i, Sky α (f i)) (j : α)
    (h : Knows m B s x fun i => (skyLayout X (f i)).loc (v i)) :
    Knows m B s x (fun i => (bits (f i)).loc (fun l => v i l j)) :=
  have hb : Small B fun i => (skyLayout X (f i)).loc (v i) :=
    (g.skyLayout_small X).mono fun i => ((skyLayout X (f i)).bd _).le
  ((h.dvdW (Can.wpow_fixed (X.loc j) g.power g.bound) hb).modW g.power hb.div).congr
    fun i => Layout.digits_entry X (bits (f i)) (rows α (f i) (v i)) j

lemma sky_set (X : Layout α) (v : ∀ i, Sky α (f i))
    (h : ∀ j : α, Knows m B s x fun i => (bits (f i)).loc (fun l => v i l j)) :
    Knows m B s x (fun i => (skyLayout X (f i)).loc (v i)) := by
  have hs : ∀ j : α, Small B fun i => (bits (f i)).loc (fun l => v i l j) * (2^f i)^(X.loc j) :=
    fun j => (g.bound.mono fun i => (bits_lt _ _).le).mul (g.bound.pow _)
  exact (Can.sum_wconst (fun j => (h j).wmul (Can.wpow_fixed (X.loc j) g.power g.bound) (hs j)) hs).congr
    fun i => (skyLayout_loc X (f i) (v i)).symm

omit [Fintype α] [DecidableEq α] in
private lemma gridLayout_iff {X : Layout α} {r : ℕ} {v : ∀ i, Grid α r (f i)} :
    (Knows m B s x fun i => (gridLayout X r (f i)).loc (v i)) ↔
      (Knows m B s x fun i => (bits r).loc (v i).1) ∧ Knows m B s x fun i => (skyLayout X (f i)).loc (v i).2 :=
  knows_pair_iff (L₁ := fun _ => bits r) (L₂ := fun i => skyLayout X (f i)) (g.skyLayout_size X) (Small.const B _)
    (g.skyLayout_small X)

omit [Fintype α] [DecidableEq α] in
lemma addr_xor (v : ∀ i, Bits (f i) × Bits (f i))
    (h : Knows m B s x (fun i => (bits (f i)).loc (v i).1))
    (k : Knows m B s x (fun i => (bits (f i)).loc (v i).2)) :
    Knows m B s x (fun i => (bits (f i)).loc ((v i).1+(v i).2)) :=
  Can.fetch (t := w) (L := fun i => (bits (f i)).pair (bits (f i)))
    (v := fun i q => (bits (f i)).loc (q.1 + q.2)) g.table
    ((knows_pair_iff (L₁ := fun i => bits (f i)) (L₂ := fun i => bits (f i)) g.power g.bound g.bound).2 ⟨h, k⟩)

lemma sky_add (X : Layout α) (v u : ∀ i, Sky α (f i))
    (hv : Knows m B s x fun i => (skyLayout X (f i)).loc (v i))
    (hu : Knows m B s x fun i => (skyLayout X (f i)).loc (u i)) :
    Knows m B s x fun i => (skyLayout X (f i)).loc (v i + u i) :=
  g.sky_set X _ fun j => g.addr_xor (fun i => (fun l => v i l j, fun l => u i l j)) (g.sky_get X v j hv)
    (g.sky_get X u j hu)
end BitCtx

abbrev RoleCell (α ρ : Type*) (r f : ℕ) := ρ × Grid α r f
abbrev RoleData (α ρ : Type*) (r f : ℕ) := RoleCell α ρ r f → ℂ
def roleLayout {α ρ : Type*} (X : Layout α) (R : Layout ρ) (r f : ℕ) := R.pair (gridLayout X r f)

structure RoleTapeCtx {α ρ : Type*} (m : Bool) (B f : ι → ℕ) (s : Ty) (x : ι → T s)
    (cl : Paint) (X : Layout α) (R : Layout ρ) (r : ℕ) (v : ∀ i, RoleData α ρ r (f i)) : Prop where
  gear : BitCtx m B f s x
  imag : Has m B s sc x fun _ => Complex.I
  items : Has m B s (a (c cl)) x fun i => (roleLayout X R r (f i)).tape (v i)

namespace RoleTapeCtx
variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
variable {m : Bool} {B f : ι → ℕ} {s t : Ty} {x : ι → T s}
    {cl : Paint} {X : Layout α} {R : Layout ρ} {r : ℕ} {v : ∀ i, RoleData α ρ r (f i)}
variable (h : RoleTapeCtx m B f s x cl X R r v)
include h

omit [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] in
lemma gather {κ : Type V} (j : κ → ι) (y : κ → T t)
    (g : Has m (fun k => B (j k)) t s y (fun k => x (j k))) :
    RoleTapeCtx m (fun k => B (j k)) (fun k => f (j k)) t y cl X R r (fun k => v (j k)) where
  gear := h.gear.descend j y g
  imag := g.then_do (h.imag.reindex j)
  items := g.then_do (h.items.reindex j)

omit [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] in
lemma addrs (u : ∀ i, RoleCell α ρ r (f i))
    (hg : Knows m B s x fun i => (roleLayout X R r (f i)).loc (u i)) :
    Knows m B s x (fun i => R.loc (u i).1) ∧ Knows m B s x (fun i => (gridLayout X r (f i)).loc (u i).2) :=
  (knows_pair_iff (L₁ := fun _ => R) (L₂ := fun i => gridLayout X r (f i)) (h.gear.grid_size X r) (Small.const B R.n)
    (h.gear.grid_small X r)).1 hg

omit [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] in
lemma read (u : ∀ i, RoleCell α ρ r (f i)) (ha : Knows m B s x fun i => R.loc (u i).1)
    (hb : Knows m B s x fun i => (gridLayout X r (f i)).loc (u i).2) :
    Has m B s (c cl) x (fun i => v i (u i)) :=
  Can.fetch (L := fun i => roleLayout X R r (f i)) h.items
    ((knows_pair_iff (L₁ := fun _ => R) (L₂ := fun i => gridLayout X r (f i)) (h.gear.grid_size X r) (Small.const B R.n)
      (h.gear.grid_small X r)).2 ⟨ha, hb⟩)

omit [Fintype α] [DecidableEq α] in
lemma mix (cf : ρ → ρ → ℂ) (hc : ∀ l j, Has m B s sc x fun _ => cf l j) (q : ∀ i, RoleCell α ρ r (f i))
    (g : Knows m B s x fun i => (roleLayout X R r (f i)).loc (q i)) :
    Has m B s (c cl) x fun i => ∑ j, cf (q i).1 j * v i (j, (q i).2) :=
  have hq := h.addrs q g
  Can.cases_code R hq.1 fun l =>
    (Can.sum_cconst fun j => ((hc l j).reindex Subtype.val).mul
      ((h.gather Subtype.val (fun i : {i // (q i).1 = l} => x i.1) Can.id).read (fun i => (j, (q i.1).2))
        (Can.wc (R.loc j)) (hq.2.reindex Subtype.val))).congr fun i => by rw [i.2]
end RoleTapeCtx

abbrev bundle := fun cl => a (c cl)
abbrev simIn := fun cl => p w (p sc (bundle cl))

section Direct
open Complex
variable {ι : Type U}

private lemma mixAt {κ : Type U} {m : Bool} {s : Ty} {cl : Paint} {y : κ → T s} {B J P : κ → ℕ}
    {tp : κ → Tape ℂ} (hJ : Knows m B s y J) (hP : Knows m B s y P) (hI : Has m B s sc y fun _ => I)
    (hT : Has m B s (a (c cl)) y tp) (sJ : Small B J) (sP : Small B P) :
    Has m B s (c cl) y fun d => ca * (tp d).look (J d) 0 +
      cb * (tp d).look (J d + P d - 2 * P d * (J d / P d % 2)) 0 :=
  ((((Can.rat (1/2)).mul (Can.one.add hI)).congr fun _ => by
    simp only [ca]; push_cast; ring).mul (hT.look hJ)).add
  ((((Can.rat (1/2)).mul (Can.one.sub hI)).congr fun _ => by
    simp only [cb]; push_cast; ring).mul (hT.look ((hJ.plus hP sJ sP).minus
      (((Can.wc 2).times hP (Small.const _ 2) sP).times ((hJ.dvdW hP sJ).modW (Can.wc 2) sJ.div)
        ((Small.const _ 2).mul sP) sJ.div.mod) (sJ.add sP))))

theorem naive_high_can (cl : Paint) (m : Bool) (k lo : ι→ℕ) (hlo : ∀ i, lo i ≤ k i)
    (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (p w (p w (p sc (a (c cl))))) (a (c cl))
      (fun i => ((k i - lo i, 2^lo i, Complex.I, (bits (k i)).tape (v i)) : T (p w (p w (p sc (a (c cl)))))))
      (fun i => (bits (k i)).tape (rippleUpTo (k i) (lo i) (v i) (k i)))
      (fun i => 2^k i * (2 * (k i - lo i) + 1)) := by
  let D : ι → ℕ := fun i => k i - lo i
  have sP : Small (fun E : During D => 2^k E.i) fun E => 2^(lo E.i + E.j) :=
    (Small.self _).mono fun E => Nat.pow_le_pow_right two_pos (by have : E.j < k E.i - lo E.i := E.hj; have := hlo E.i; omega)
  refine Can.weaken (W := fun i => 0 + 0 + D i + ∑ j ∈ range (D i), 2^k i) ?_ ⟨2, fun i => ?_⟩
  · exact ((Can.loop (B := fun i => 2^k i)
      (x := fun i => ((k i - lo i, 2^lo i, I, (bits (k i)).tape (v i)) : T (p w (p w (p sc (a (c cl)))))))
      (n := D) (s := p w (p w (p sc (a (c cl))))) (t := p w (a (c cl))) (W := fun _ => 0) (W' := fun _ => 0)
      (v := fun i j => (2^(lo i + j), (bits (k i)).tape (rippleUpTo (k i) (lo i) (v i) (lo i + j)))) (uB := fun i _ => 2^k i) Can.first
      ((Can.second.fst.pair Can.second.snd.snd).cong (fun _ => rfl) fun i => by simp only [add_zero, rippleUpTo_start])
      ((Can.pair (Can.second.snd.fst.plus Can.second.snd.fst sP sP) ((Can.layout
        (t := c cl) (W := fun _ => 0) (L := fun E : During D => bits (k E.i)) (P := fun _ => 0)
        (v := fun E t => rippleUpTo (k E.i) (lo E.i) (v E.i) (lo E.i + E.j + 1) t) (Can.second.snd.snd.len (Small.self _))
        ((mixAt (J := fun e : Σ E : During D, Bits (k E.i) => (bits (k e.1.i)).loc e.2)
          (P := fun e => 2^(lo e.1.i + e.1.j)) Can.second Can.first.snd.snd.fst Can.first.fst.snd.snd.fst
          Can.first.snd.snd.snd (Small.loc (L := fun e : Σ E : During D, Bits (k E.i) =>
            bits (k e.1.i)) (Small.self _)) (sP.reindex Sigma.fst)).cong (fun _ => rfl) fun e => by
          have hb : lo e.1.i + e.1.j < k e.1.i := by
            have : e.1.j < k e.1.i - lo e.1.i := e.1.hj; have := hlo e.1.i; omega
          simp only [← bits_flip _ e.2 hb, Layout.read, rippleUpTo_succ (Nat.le_add_right _ _) hb])
        (Small.self _)).mono fun E => by simp only [bits_len, zero_add, mul_zero, add_zero, Std.le_refl])).cong (fun _ => rfl)
        fun E => Prod.ext ((pow_succ 2 _).trans (mul_two _)).symm rfl)
      ((Small.self _).mono fun i => (Nat.sub_le _ _).trans Nat.lt_two_pow_self.le)).snd).cong (fun _ => rfl)
      fun i => by
        show (bits (k i)).tape (rippleUpTo (k i) (lo i) (v i) (lo i + (k i - lo i))) = _
        rw [Nat.add_sub_cancel' (hlo i)]
  have h1 := Nat.le_mul_of_pos_right (k i - lo i) (Nat.two_pow_pos (k i))
  show 0 + 0 + (k i - lo i) + ∑ j ∈ range (k i - lo i), 2^k i + 1 ≤ 2 * (2^k i * (2 * (k i - lo i) + 1) + 1)
  rw [sum_const, card_range, smul_eq_mul]
  generalize k i - lo i = d at *; generalize 2 ^ k i = P at *; nlinarith
end Direct

def givenBits (cl : Paint) (k : ℕ) (v : Bits k→ℂ) : T (simIn cl) := (k,Complex.I,(bits k).tape v)
end
end PowerSaving.RAM
end OAI

end
-- ===== end part 1 =====


-- ===== begin part 2: letter splittings and engine moves =====
section

/-! Letter splittings, the move language of the engine, and moves on role tables in tape form. -/
namespace OAI.PowerSaving
noncomputable def envelope (z : ℝ) (k : ℕ) : ℕ := ⌈((k : ℝ) + 1) ^ z⌉₊
lemma envelope_positive (z : ℝ) (k : ℕ) : 0 < envelope z k :=
  Nat.ceil_pos.2 (Real.rpow_pos_of_pos (by positivity) z)
lemma envelope_monotone {z : ℝ} (hz : 0 ≤ z) : Monotone (envelope z) := fun a b hab =>
  Nat.ceil_mono (Real.rpow_le_rpow (by positivity)
    (by have := (Nat.cast_le (α := ℝ)).2 hab; linarith) hz)
/-- For an exponent at most `1` the envelope at `k` stays below any `N ≥ k + 1`. -/
lemma envelope_le_of {z : ℝ} (hz : z ≤ 1) {k N : ℕ} (hN : k + 1 ≤ N) : envelope z k ≤ N := by
  have hb : (1 : ℝ) ≤ (k : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) k; linarith
  refine Nat.ceil_le.2 ((Real.rpow_le_rpow_of_exponent_le hb hz).trans ?_)
  rw [Real.rpow_one]; exact_mod_cast hN
/-- A real number at least `1` has natural ceiling at most twice itself. -/
lemma natCeil_le_double {x : ℝ} (hx : 1 ≤ x) : (⌈x⌉₊ : ℝ) ≤ 2 * x := by
  have h := Nat.ceil_lt_add_one (zero_le_one.trans hx)
  linarith
end OAI.PowerSaving

namespace OAI
namespace PowerSaving.Binary
open Matrix Finset
open scoped Kronecker
variable {α β γ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ]
noncomputable section
/-- A splitting of the `α`-bits into a `β`-part and a `γ`-part, as an additive equivalence. -/
abbrev Cleave (α β γ : Type*) := Space α ≃+ (Space β × Space γ)
namespace Cleave
variable (S : Cleave α β γ)
/-- `M` on the `γ`-part and the identity on the `β`-part: the Kronecker product `1 ⊗ₖ M` read
through `S` on rows and columns. Bundled as a monoid map. -/
def widen : CMat γ →* CMat α where
  toFun M := Matrix.reindex S.toEquiv.symm S.toEquiv.symm ((1 : CMat β) ⊗ₖ M)
  map_one' := by rw [Matrix.one_kronecker_one, Matrix.reindex_apply, Matrix.submatrix_one_equiv]
  map_mul' M N := by
    simp only [Matrix.reindex_apply]
    rw [Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul, Matrix.mul_one]

lemma widen_apply (M : CMat γ) (x y : Space α) :
    S.widen M x y = (1 : CMat β) (S x).1 (S y).1 * M (S x).2 (S y).2 := by
  simp only [widen, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, Matrix.kroneckerMap_apply]
  rfl
lemma widen_symm_apply (M : CMat γ) (p q : Space β × Space γ) :
    S.widen M (S.symm p) (S.symm q) = (1 : CMat β) p.1 q.1 * M p.2 q.2 := by
  rw [widen_apply, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
lemma widen_dir (c : Space γ) : S.widen (dir c) = dir (S.symm (0, c)) := by
  ext x y
  obtain ⟨p, rfl⟩ := S.symm.surjective x
  obtain ⟨q, rfl⟩ := S.symm.surjective y
  have e1 : S.symm p = S.symm q ↔ p.1 = q.1 ∧ p.2 = q.2 :=
    S.symm.injective.eq_iff.trans Prod.ext_iff
  have e2 : S.symm p + S.symm (0, c) = S.symm q ↔ p.1 = q.1 ∧ p.2 + c = q.2 := by
    rw [← map_add, S.symm.injective.eq_iff, Prod.ext_iff, Prod.fst_add, Prod.snd_add, add_zero]
  rw [widen_apply, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  simp only [dir, shift, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, e1, e2]
  by_cases h : p.1 = q.1 <;> simp [h]
end Cleave
/-- The phase of a family of letter directions: `x ↦ phaseProd (i ↦ dot (z i) x)`. -/
def phaseOf {κ : Type*} [Fintype κ] (z : κ → Space α) (x : Space α) : ℂ := phaseProd fun i => dot (z i) x

/-- The block matrix of a family of letter directions: the Walsh-diagonal matrix (`walshConj`) of its
phase. Since `dir c = walshConj (phaseI ∘ dot c)`, it is the product of the commuting `dir (z i)`. -/
def blockMat {κ : Type*} [Fintype κ] (z : κ → Space α) : CMat α := walshConj (phaseOf z)

/-- Reindexing a family along an equivalence of index types leaves its phase unchanged. -/
lemma phaseOf_comp_equiv {κ κ' : Type*} [Fintype κ] [Fintype κ'] (e : κ ≃ κ') (z : κ' → Space α) :
    phaseOf (z ∘ e) = phaseOf z :=
  funext fun x => e.prod_comp fun j => phaseI (dot (z j) x)

/-- The block matrix of a `Fin r` family is the ordered list product of its direction matrices. -/
lemma blockMat_eq_prod_ofFn : ∀ {r : ℕ} (z : Fin r → Space α),
    blockMat z = (List.ofFn fun i => dir (z i)).prod
  | 0, z => by
    rw [List.ofFn_zero, List.prod_nil, blockMat, ← walshConj_one]
    exact congrArg walshConj (funext fun x => Fin.prod_univ_zero fun i => phaseI (dot (z i) x))
  | r+1, z => by
    rw [List.ofFn_succ, List.prod_cons, ← blockMat_eq_prod_ofFn (fun i => z i.succ), dir_phase,
      blockMat, blockMat, walshConj_mul]
    exact congrArg walshConj (funext fun x => Fin.prod_univ_succ fun i => phaseI (dot (z i) x))
end
end PowerSaving.Binary

namespace PowerSaving.Binary
open Matrix Finset
noncomputable section
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
/-- A family running through all unit vectors (along an equivalence of index types) has the
full ripple kernel as block matrix. -/
lemma blockMat_units {κ : Type*} [Fintype κ] (e : κ ≃ α) : blockMat (fun i => eu (e i)) = rippleMat α := by
  rw [← walshConj_phaseProd, blockMat]
  congr 1; funext x
  simp only [phaseOf, phaseProd, dot_eu_left]
  exact e.prod_comp fun a => phaseI (x a)

/-- A splitting that sends the unit vectors of its `Fin r` side to `z` turns the lifted kernel
into the block matrix of the `z`. -/
lemma widen_kernel {r : ℕ} (S : Cleave α β (Fin r)) {z : Fin r → Space α}
    (hz : ∀ i, S.symm (0, eu i) = z i) : S.widen (rippleMat (Fin r)) = blockMat z := by
  rw [← blockMat_units (Equiv.refl (Fin r)), blockMat_eq_prod_ofFn, blockMat_eq_prod_ofFn, map_list_prod,
    List.map_ofFn]
  exact congrArg List.prod (congrArg List.ofFn (funext fun i => (S.widen_dir _).trans (congrArg dir (hz i))))
section Exists
lemma extend {r : ℕ} (z : Fin r → Space α) (hz : LinearIndependent F z) :
    ∀ k, k ≤ Fintype.card α - r → ∃ w : Fin k → Space α, LinearIndependent F (Fin.append z w)
  | 0, _ => ⟨Fin.elim0, by rw [Fin.append_right_nil _ _ rfl]; exact hz.comp _ (Fin.cast_injective _)⟩
  | k+1, hk => by
    obtain ⟨w, hw⟩ := extend z hz k (by omega)
    obtain ⟨v, hv⟩ : ∃ v, v ∉ Submodule.span F (Set.range (Fin.append z w)) := by
      by_contra! H
      have := Fintype.card_le_of_surjective _ fun v => (Submodule.mem_span_range_iff_exists_fun F).1 (H v)
      simp only [Fintype.card_pi, ZMod.card, prod_const, card_univ, Fintype.card_fin, Order.lt_two_iff, Std.le_refl, Nat.pow_le_pow_iff_right] at this; omega
    exact ⟨Fin.snoc w v, by rw [Fin.append_snoc]; exact linearIndependent_finSnoc.2 ⟨hw, hv⟩⟩
/-- Letters from two coordinate blocks: `(p, q) ↦ ∑ q j • z j + ∑ p j • w j`. -/
def assemble {r k : ℕ} (z : Fin r → Space α) (w : Fin k → Space α) : Space (Fin k) × Space (Fin r) →+ Space α :=
  AddMonoidHom.mk' (fun pq => ∑ j, pq.2 j • z j + ∑ j, pq.1 j • w j) fun a b => by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel

/-- Every independent family `z` of `r` letters is carried to the unit vectors of the block side by
some splitting whose complement side has the remaining `card α - r` coordinates: complete `z` by
`extend`, read the coordinates in the resulting sum-indexed basis, and split them by summand. -/
lemma Cleave.exists_adapted {r : ℕ} (z : Fin r → Space α) (hz : LinearIndependent F z) :
    ∃ S : Cleave α (Fin (Fintype.card α - r)) (Fin r), ∀ i, S (z i) = (0, eu i) := by
  have hr : r ≤ Fintype.card α := by
    simpa [Module.finrank_fintype_fun_eq_card] using hz.fintype_card_le_finrank
  obtain ⟨w, hw⟩ := extend z hz _ le_rfl
  have hu : LinearIndependent F (Sum.elim w z) := by
    have e : Sum.elim w z = Fin.append z w ∘ ((Equiv.sumComm _ _).trans finSumFinEquiv) := by
      funext j; rcases j with j | j <;> simp [Fin.append_left, Fin.append_right]
    rw [e]; exact hw.comp _ (Equiv.injective _)
  let b := basisOfLinearIndependentOfCardEqFinrank' _ hu
    (by simp only [Fintype.card_sum, Fintype.card_fin, Module.finrank_fintype_fun_eq_card]; omega)
  refine ⟨(b.equivFun.trans (LinearEquiv.sumArrowLequivProdArrow _ _ F F)).toAddEquiv, fun i => ?_⟩
  have hb : b (Sum.inr i) = z i := by simp [b]
  rw [← hb]
  ext j <;> simp [Module.Basis.equivFun_self, eu, Finsupp.single_apply]

/-- The splitting adapted to an independent family `z` of `r` letters (chosen once and for all):
complement side `Fin (card α - r)`, block side `Fin r`, with `z i ↦ (0, eu i)`. -/
def Cleave.adapted {r : ℕ} (z : Fin r → Space α) (hz : LinearIndependent F z) :
    Cleave α (Fin (Fintype.card α - r)) (Fin r) :=
  (Cleave.exists_adapted z hz).choose

lemma Cleave.adapted_unit {r : ℕ} (z : Fin r → Space α) (hz : LinearIndependent F z) :
    ∀ i, Cleave.adapted z hz (z i) = (0, eu i) :=
  (Cleave.exists_adapted z hz).choose_spec
end Exists
variable {γ : Type*} [Fintype γ] [DecidableEq γ] {r : ℕ}
/-- A splitting acts on words letter by letter: map every letter by `S`, then separate the word of
pairs into its word of `β`-parts and its word of `γ`-parts. -/
def Cleave.byLetter (S : Cleave α β γ) (f : ℕ) : Sky α f ≃ Sky β f × Sky γ f :=
  (Equiv.piCongrRight fun _ : Fin f => S.toEquiv).trans (Equiv.arrowProdEquivProdArrow _ _ _)

/-- Peeling a grid along a splitting with block side `Fin r`: keep the pad, split the word letter by
letter, regroup the pad with the complement word, and flatten the block word to `r * f` bits. -/
def Cleave.peel (S : Cleave α β (Fin r)) (pad f : ℕ) : Grid α pad f ≃ Grid β pad f × Bits (r * f) :=
  ((Equiv.refl (Bits pad)).prodCongr (S.byLetter f)).trans
    ((Equiv.prodAssoc _ _ _).symm.trans ((Equiv.refl _).prodCongr (bitFlat r f)))
end
end PowerSaving.Binary

namespace PowerSaving.RAM
open Binary Ty Finset
noncomputable section
universe U
variable {ι : Type U}
namespace BitCtx
variable {m : Bool} {B f : ι → ℕ} {s t : Ty} {x : ι → T s}
variable (g : BitCtx m B f s x)
include g
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

lemma sky_lin (X : Layout α) (L : Space α → F) (hL : ∀ p q, L (p+q) = L p + L q)
    (v : ∀ i, Sky α (f i)) (h : Knows m B s x fun i => (skyLayout X (f i)).loc (v i)) :
    Knows m B s x fun i => (bits (f i)).loc fun l => L (v i l) := by
  let Lh : Space α →+ F := AddMonoidHom.mk' L hL
  have hsm (c : F) (y : Space α) : L (c • y) = c * L y := by
    rcases bit_cases c with rfl | rfl
    · rw [zero_smul, zero_mul, show L 0 = 0 by simpa using hL 0 0]
    · rw [one_smul, one_mul]
  have hs (y : Space α) : L y = ∑ a, y a * L (eu a) := by
    conv_lhs => rw [pi_eq_sum_univ y]
    exact (map_sum Lh _ _).trans (Finset.sum_congr rfl fun a _ => hsm _ _)
  have key (d : Finset α) : Knows m B s x fun i => (bits (f i)).loc fun l => ∑ a ∈ d, v i l a * L (eu a) := by
    induction d using Finset.induction with
    | empty => exact (Can.wc 0).congr fun i => by simp [bits_loc]
    | insert a d ha ih =>
      simp only [Finset.sum_insert ha]
      rcases bit_cases (L (eu a)) with e | e
      · simp only [e, mul_zero, zero_add]; exact ih
      · simp only [e, mul_one]; exact g.addr_xor (fun i => (_, _)) (g.sky_get X v a h) ih
  exact (key univ).congr fun i => by simp only [← hs]

lemma sky_map (X : Layout α) (X' : Layout β) (Φ : Space α → Space β) (hΦ : ∀ p q, Φ (p+q) = Φ p + Φ q)
    (v : ∀ i, Sky α (f i)) (h : Knows m B s x fun i => (skyLayout X (f i)).loc (v i)) :
    Knows m B s x fun i => (skyLayout X' (f i)).loc fun l => Φ (v i l) :=
  g.sky_set X' _ fun j => g.sky_lin X (fun y => Φ y j) (fun p q => by rw [hΦ]; rfl) v h

lemma addr_and (v : ∀ i, Bits (f i) × Bits (f i))
    (h : Knows m B s x (fun i => (bits (f i)).loc (v i).1))
    (k : Knows m B s x (fun i => (bits (f i)).loc (v i).2)) :
    Knows m B s x (fun i => (bits (f i)).loc (fun j => (v i).1 j * (v i).2 j)) := by
  have sb : ∀ u : ∀ i, Bits (f i), Small B fun i => (bits (f i)).loc (u i) :=
    fun u => g.bound.mono fun i => (bits_lt _ _).le
  have hsum : ∀ (k : ℕ) (a b : Bits k), (bits _).loc a + (bits _).loc b =
      (bits _).loc (a + b) + 2 * (bits _).loc (fun j => a j * b j) := fun _ a b => by
    have hb : ∀ p q : F, p.val + q.val = (p + q).val + 2 * (p * q).val := by decide
    simp only [bits_loc, Finset.mul_sum, ← Finset.sum_add_distrib, ← add_mul, Pi.add_apply]
    exact Finset.sum_congr rfl fun j _ => by rw [hb, add_mul, mul_assoc]
  refine (((h.plus k (sb _) (sb _)).minus (g.addr_xor v h k) ((sb _).add (sb _))).dvdW (Can.wc 2)
    ((sb _).add (sb _)).sub).congr fun i => ?_
  have e := hsum _ (v i).1 (v i).2
  show ((bits (f i)).loc (v i).1 + (bits (f i)).loc (v i).2 - (bits (f i)).loc ((v i).1 + (v i).2)) / 2 = _
  omega

/-- Any fixed Boolean function of the α-bits, evaluated in every column of a body word. -/
lemma sky_bool (X : Layout α) (G : Space α → F)
    (v : ∀ i, Sky α (f i)) (h : Knows m B s x fun i => (skyLayout X (f i)).loc (v i)) :
    Knows m B s x fun i => (bits (f i)).loc fun l => G (v i l) := by
  have key1 (w : Space α) (d : Finset α) :
      Knows m B s x fun i => (bits (f i)).loc fun l => ∏ a ∈ d, (v i l a + (1 + w a)) := by
    induction d using Finset.induction with
    | empty => simpa only [prod_empty] using g.const_bits (1 : F)
    | insert a d ha ih =>
      simp only [Finset.prod_insert ha]
      exact g.addr_and (fun i => (_, _))
        (g.addr_xor (fun i => (_, fun _ => 1 + w a)) (g.sky_get X v a h) (g.const_bits _)) ih
  have key2 (S : Finset (Space α)) :
      Knows m B s x fun i => (bits (f i)).loc fun l => ∑ w ∈ S, ∏ a, (v i l a + (1 + w a)) := by
    induction S using Finset.induction with
    | empty => simpa only [sum_empty] using g.const_bits (0 : F)
    | insert w S hw ih =>
      simp only [Finset.sum_insert hw]
      exact g.addr_xor (fun i => (_, _)) (key1 w univ) ih
  have mt : ∀ y : Space α, ∑ w ∈ univ.filter (fun w => G w = 1), ∏ a, (y a + (1 + w a)) = G y := by
    intro y
    have hp : ∀ w : Space α, ∏ a, (y a + (1 + w a)) = if w = y then 1 else 0 := by
      intro w
      have e1 : ∀ p : F, p + (1 + p) = 1 := by decide
      have e0 : ∀ p q : F, p ≠ q → q + (1 + p) = 0 := by decide
      by_cases hw : w = y
      · subst hw; rw [ite_eq_left rfl]; exact Finset.prod_eq_one fun a _ => e1 _
      · rw [ite_eq_right hw]
        obtain ⟨a, ha⟩ : ∃ a, w a ≠ y a := by
          by_contra hc; exact hw (funext fun a => not_not.1 fun h => hc ⟨a, h⟩)
        exact Finset.prod_eq_zero (Finset.mem_univ a) (e0 _ _ ha)
    simp only [hp, Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ, true_and]
    rcases bit_cases (G y) with h1 | h1 <;> simp [h1]
  exact (key2 _).congr fun i => congrArg _ (funext fun l => mt _)

/-- Splitting every letter of a known body word along an additive equivalence gives two known
body words. -/
lemma sky_split {γ : Type*} [Fintype γ] [DecidableEq γ] (S : Space α ≃+ Space β × Space γ)
    (X : Layout α) (Y : Layout β) (Z : Layout γ) (v : ∀ i, Sky α (f i))
    (h : Knows m B s x fun i => (skyLayout X (f i)).loc (v i)) :
    (Knows m B s x fun i => (skyLayout Y (f i)).loc fun l => (S (v i l)).1) ∧
      Knows m B s x fun i => (skyLayout Z (f i)).loc fun l => (S (v i l)).2 :=
  ⟨g.sky_map X Y (fun y => (S y).1) (fun p q => by rw [map_add]; rfl) v h,
    g.sky_map X Z (fun y => (S y).2) (fun p q => by rw [map_add]; rfl) v h⟩

/-- Conversely, two known body words over `β` and `γ`, glued letter by letter through `S.symm`,
give a known body word over `α`. -/
lemma sky_glue {γ : Type*} [Fintype γ] [DecidableEq γ] (S : Space α ≃+ Space β × Space γ)
    (X : Layout α) (Y : Layout β) (Z : Layout γ) (b : ∀ i, Sky β (f i)) (c : ∀ i, Sky γ (f i))
    (hb : Knows m B s x fun i => (skyLayout Y (f i)).loc (b i))
    (hc : Knows m B s x fun i => (skyLayout Z (f i)).loc (c i)) :
    Knows m B s x fun i => (skyLayout X (f i)).loc fun l => S.symm (b i l, c i l) := by
  let U := Layout.someLayout (β ⊕ γ)
  let bc : ∀ i, Sky (β ⊕ γ) (f i) := fun i l => Sum.elim (b i l) (c i l)
  have hu : Knows m B s x fun i => (skyLayout U (f i)).loc (bc i) :=
    g.sky_set U bc fun j => match j with
      | .inl j => g.sky_get Y b j hb
      | .inr j => g.sky_get Z c j hc
  let Φ : Space (β ⊕ γ) → Space α := fun u => S.symm (fun j => u (.inl j), fun j => u (.inr j))
  have hΦ : ∀ u u', Φ (u + u') = Φ u + Φ u' := fun u u' => by
    simp only [Φ]; rw [← map_add]; rfl
  exact (g.sky_map U X Φ hΦ bc hu).congr fun i => congrArg (skyLayout X (f i)).loc (funext fun l => rfl)

/-- Peeling a known grid gives a known complement grid and a known flattened block. -/
lemma peel_known {k r : ℕ} (S : Cleave α β (Fin k)) (X : Layout α) (X' : Layout β)
    (v : ∀ i, Grid α r (f i)) (h : Knows m B s x fun i => (gridLayout X r (f i)).loc (v i)) :
    (Knows m B s x fun i => (gridLayout X' r (f i)).loc (S.peel r (f i) (v i)).1) ∧
      Knows m B s x fun i => (bits (k * f i)).loc (S.peel r (f i) (v i)).2 := by
  obtain ⟨hp, hb⟩ := g.gridLayout_iff.1 h
  obtain ⟨h1, h2⟩ := g.sky_split S X X' (Layout.std k) (fun i => (v i).2) hb
  exact ⟨g.gridLayout_iff.2 ⟨hp, h1⟩, h2.congr fun i => by
    rw [← bitFlat_skyLayout_loc]; exact congrArg _ ((bitFlat k (f i)).symm_apply_apply _).symm⟩

/-- A known pad and two known body words over `β` and `γ`, glued letter by letter through any
additive equivalence, give a known grid over `α`. -/
lemma gridLayout_glue {γ : Type*} [Fintype γ] [DecidableEq γ] (S : Space α ≃+ Space β × Space γ)
    (X : Layout α) (Y : Layout β) (Z : Layout γ) {r : ℕ} (q : ∀ i, Bits r) (b : ∀ i, Sky β (f i))
    (c : ∀ i, Sky γ (f i)) (hq : Knows m B s x fun i => (bits r).loc (q i))
    (hb : Knows m B s x fun i => (skyLayout Y (f i)).loc (b i))
    (hc : Knows m B s x fun i => (skyLayout Z (f i)).loc (c i)) :
    Knows m B s x fun i => (gridLayout X r (f i)).loc (q i, fun l => S.symm (b i l, c i l)) :=
  g.gridLayout_iff.2 ⟨hq, g.sky_glue S X Y Z b c hb hc⟩

end BitCtx
end
end PowerSaving.RAM

namespace PowerSaving.RAM
open Binary
noncomputable section
variable {α ρ : Type*} [Fintype α] [DecidableEq α]
/-- Apply a role-table map separately at every pad value of a grain. -/
def padwise {r f : ℕ} (T : Data α ρ f → Data α ρ f) (v : RoleData α ρ r f) : RoleData α ρ r f :=
  fun b => T (fun j y => v (j, b.2.1, y)) b.1 b.2.2
end
end PowerSaving.RAM
end OAI

namespace OAI
namespace PowerSaving.GenMove
open Binary Matrix Finset
noncomputable section
variable {α ρ : Type*}
/-- The instructions of the engine: a block of `k` independent letter directions on one role, a
rational mixing across roles, an additive permutation, an affine phase, or a Boolean sign on one
role. -/
inductive Move (α ρ : Type*) where
  | kern (l : ρ) (k : ℕ) (z : Fin k → Space α) (hz : LinearIndependent F z)
  | mix (gr gi : Matrix ρ ρ ℚ)
  | perm (l : ρ) (G : Space α ≃+ Space α)
  | phase (l : ρ) (z : Space α) (c : F)
  | sgn (l : ρ) (g : Space α → F)
/-- A program of moves, run left to right. -/
abbrev Script (α ρ : Type*) := List (Move α ρ)
namespace Move
def rk? : Move α ρ → Option ℕ
  | .kern _ k _ _ => some k
  | _ => none
/-- A block move fits under `u` when its rank lies in `[1, u)`; other moves always fit. -/
def Bounded (mv : Move α ρ) (u : ℕ) : Prop := ∀ k ∈ mv.rk?, 1 ≤ k ∧ k < u
lemma proper_iff (mv : Move α ρ) (u : ℕ) :
    mv.Bounded u ↔ ∀ r, mv.rk? = some r → 1 ≤ r ∧ r < u := Iff.rfl
end Move
namespace Script
/-- A script fits under `u` when every rank on its rank list lies in `[1, u)`. -/
def Fits (w : Script α ρ) (u : ℕ) : Prop := ∀ k ∈ w.filterMap Move.rk?, 1 ≤ k ∧ k < u
lemma Fits.kern {w : Script α ρ} {u : ℕ} (h : w.Fits u) {l : ρ} {k : ℕ} {z : Fin k → Space α}
    {hz : LinearIndependent F z} (hm : Move.kern l k z hz ∈ w) : 1 ≤ k ∧ k < u :=
  h k (List.mem_filterMap.2 ⟨_, hm, rfl⟩)
end Script
variable [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
def shuffleMat (G : Space α ≃+ Space α) : CMat α := fun x y => if G x = y then 1 else 0
def actPointG (gr gi : Matrix ρ ρ ℚ) (x : ρ → ℂ) (r : ρ) : ℂ :=
  ∑ j, ((gr r j : ℂ) + (gi r j : ℂ) * Complex.I) * x j
/-- One move on a role table of `f`-letter words. -/
def Move.act : Move α ρ → (f : ℕ) → Data α ρ f → Data α ρ f
  | .kern l _ z _, f => roleAct f l (blockMat z)
  | .mix gr gi, f => point f (actPointG gr gi)
  | .perm l G, f => roleAct f l (shuffleMat G)
  | .phase l z c, f => roleAct f l (Matrix.diagonal fun y => phaseI (dot z y + c))
  | .sgn l g, f => roleAct f l (Matrix.diagonal fun y => sign (g y))
/-- Run a script on a role table, first move first. -/
def Script.exec : Script α ρ → (f : ℕ) → Data α ρ f → Data α ρ f
  | [], _ => id
  | mv :: w, f => Script.exec w f ∘ mv.act f
@[simp] lemma exec_nil (f : ℕ) (x : Data α ρ f) : Script.exec ([] : Script α ρ) f x = x := rfl
lemma exec_cons (f : ℕ) (mv : Move α ρ) (w : Script α ρ) (x : Data α ρ f) :
    Script.exec (mv :: w) f x = Script.exec w f (mv.act f x) := rfl
lemma exec_append (f : ℕ) (w w' : Script α ρ) (x : Data α ρ f) :
    Script.exec (w ++ w') f x = Script.exec w' f (Script.exec w f x) := by
  induction w generalizing x with
  | nil => rfl
  | cons mv w ih => exact ih (mv.act f x)
omit [Fintype ρ] [DecidableEq ρ] in
lemma mulVec_apply' {n : Type*} [Fintype n] (M : Matrix n n ℂ) (y : n → ℂ) (b : n) :
    (M *ᵥ y) b = ∑ b', M b b' * y b' := rfl
omit [Fintype ρ] [DecidableEq ρ] in
lemma matAct_perm (f : ℕ) (G : Space α ≃+ Space α) (y : Sky α f → ℂ) (b : Sky α f) :
    letterwise f (shuffleMat G) y b = y (fun k => G (b k)) := by
  rw [letterwise_apply, mulVec_apply']
  simp only [digitProd_apply, shuffleMat]
  simp only [prod_delta, ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ, ↓reduceIte]
omit [Fintype ρ] [DecidableEq ρ] in
lemma matAct_diag (f : ℕ) (d : Space α → ℂ) (y : Sky α f → ℂ) (b : Sky α f) :
    letterwise f (Matrix.diagonal d) y b = (∏ k, d (b k)) * y b := by
  rw [letterwise_apply, digitProd_diagonal, Matrix.mulVec_diagonal]
omit [Fintype ρ] [DecidableEq ρ] in
lemma matAct_phase (f : ℕ) (z : Space α) (c : F) (y : Sky α f → ℂ) (b : Sky α f) :
    letterwise f (Matrix.diagonal fun x => phaseI (dot z x + c)) y b =
      (∏ k, phaseI (dot z (b k) + c)) * y b := matAct_diag ..
omit [Fintype ρ] [DecidableEq ρ] in
lemma matAct_bphase (f : ℕ) (g : Space α → F) (y : Sky α f → ℂ) (b : Sky α f) :
    letterwise f (Matrix.diagonal fun x => sign (g x)) y b = (∏ k, sign (g (b k))) * y b :=
  matAct_diag ..
end
end PowerSaving.GenMove
namespace PowerSaving.RAM
open Binary Ty Finset GenMove
noncomputable section
universe U V
variable {ι : Type U}
section
variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
variable {m : Bool} {B f : ι → ℕ} {s t : Ty} {x : ι → T s}
    {cl : Paint} {X : Layout α} {R : Layout ρ} {r : ℕ} {v : ∀ i, RoleData α ρ r (f i)}
lemma RoleTapeCtx.ferry_of (h : RoleTapeCtx m B f s x cl X R r v) (l : ρ) (N : CMat α)
    (q : ∀ i, RoleCell α ρ r (f i)) (g : Knows m B s x fun i => (roleLayout X R r (f i)).loc (q i)) {y : ι → ℂ}
    (hy : ∀ i, (q i).1 = l → y i = letterwise (f i) N (fun j => v i (l, (q i).2.1, j)) (q i).2.2)
    (hnew : Has m B s (c cl) x y) : Has m B s (c cl) x fun i => padwise (roleAct (f i) l N) (v i) (q i) := by
  obtain ⟨h1, h2⟩ := h.addrs q g
  refine (Can.branch (Can.eqbit h1 (Can.wc (R.loc l))) hnew (h.read q h1 h2)).congr fun i => ?_
  by_cases e : (q i).1 = l
  · simp [padwise, roleAct, e, hy i e]
  · have hne : R.loc (q i).1 ≠ R.loc l := fun h => e (R.inj h)
    simp [padwise, roleAct, e, hne]
end
section
variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
variable {m : Bool} {B f : ι → ℕ} {s : Ty} {x : ι → T s}
    {cl : Paint} {X : Layout α} {R : Layout ρ} {r : ℕ} {v : ∀ i, RoleData α ρ r (f i)}
lemma RoleTapeCtx.ferry_pointG (h : RoleTapeCtx m B f s x cl X R r v) (gr gi : Matrix ρ ρ ℚ)
    (q : ∀ i, RoleCell α ρ r (f i))
    (g : Knows m B s x fun i => (roleLayout X R r (f i)).loc (q i)) :
    Has m B s (c cl) x fun i => padwise ((Move.mix gr gi : Move α ρ).act (f i)) (v i) (q i) :=
  h.mix (fun l j => (gr l j : ℂ) + (gi l j : ℂ) * Complex.I)
    (fun l j => (Can.rat _).add ((Can.rat _).mul h.imag)) q g

/-- Every move without a block rank can be carried out on the grain tape, given the tape of
`phaseProd` over the `f`-bit vectors. -/
lemma RoleTapeCtx.ferry_free (h : RoleTapeCtx m B f s x cl X R r v)
    (hl : Has m B s (a sc) x fun i => (bits (f i)).tape fun y : Bits (f i) => phaseProd y)
    (mv : Move α ρ) (h0 : mv.rk? = none) (q : ∀ i, RoleCell α ρ r (f i))
    (g : Knows m B s x fun i => (roleLayout X R r (f i)).loc (q i)) :
    Has m B s (c cl) x fun i => padwise (mv.act (f i)) (v i) (q i) := by
  have h2 := (h.addrs q g).2
  obtain ⟨hpad, hbody⟩ := h.gear.gridLayout_iff.1 h2
  have here (l : ρ) : Has m B s (c cl) x fun i => v i (l, (q i).2) :=
    h.read (fun i => (l, (q i).2)) (Can.wc (R.loc l)) h2
  have tape {u : ∀ i, Bits (f i)} (hu : Knows m B s x fun i => (bits (f i)).loc (u i)) :
      Has m B s sc x fun i => phaseProd (u i) := Can.fetch (L := fun i => bits (f i)) hl hu
  cases mv with
  | kern => cases h0
  | mix gr gi => exact h.ferry_pointG gr gi q g
  | perm l G =>
    exact h.ferry_of l (shuffleMat G) q g (fun i _ => by rw [matAct_perm])
      (h.read (fun i => (l, (q i).2.1, fun k => G ((q i).2.2 k))) (Can.wc (R.loc l))
        (h.gear.gridLayout_iff.2 ⟨hpad, h.gear.sky_map X X G (map_add G) _ hbody⟩))
  | phase l z c' =>
    exact h.ferry_of l (Matrix.diagonal fun y => phaseI (dot z y + c')) q g (fun i _ => by rw [matAct_phase]; rfl)
      ((tape (h.gear.addr_xor (fun i => (fun k => dot z ((q i).2.2 k), fun _ => c'))
        (h.gear.sky_lin X (dot z) (dot_add_right z) _ hbody) (h.gear.const_bits c'))).mul (here l))
  | sgn l G =>
    have t := tape (h.gear.sky_bool X G _ hbody)
    refine h.ferry_of l (Matrix.diagonal fun y => sign (G y)) q g (fun i _ => ?_) ((t.mul t).mul (here l))
    rw [matAct_bphase]
    simp only [phaseProd, ← Finset.prod_mul_distrib, phaseI_sq]
end
end
end PowerSaving.RAM
namespace PowerSaving.RoleKernel
open Binary GenMove Matrix Finset
noncomputable section
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
/-- A script `w` drives the live slots `e` by the letter matrices `T`: for every letter count,
"run `w`, then read the role of slot `l`" equals "read that role, then act by `T l`", as maps on
the role tables that vanish outside the live roles. -/
structure Drives (e : σ → ρ) (T : σ → CMat α) (w : Script α ρ) : Prop where
  read_run : ∀ (f : ℕ) (l : σ),
    (fun x : {x : Data α ρ f // ∀ j, j ∉ Set.range e → x j = 0} => Script.exec w f x.1 (e l)) =
      fun x => letterwise f (T l) (x.1 (e l))
end
end PowerSaving.RoleKernel
end OAI
end
-- ===== end part 2 =====
