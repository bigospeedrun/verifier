-- Bench tools, weight tables, partial kernels and placements, jobs and the block engine's data
-- (`SlotEngine`), class setup. Notices and credits: texts/credits.lean.
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Submission.EngineMoves
import Submission.CostCalculus
import Mathlib.Logic.Equiv.Fintype
set_option linter.all false

section

namespace OAI

namespace PowerSaving.RAM
open Ty Finset Spectral
noncomputable section

namespace Bench
universe U V
variable {ι : Type U} {κ : Type V} {m : Bool} {b : Bench m ι}
  {n k S : ι→ℕ} {t : Ty}

lemma WordIn.branch {x y : ι→ℕ} (h : b.FreeWord n) (g : b.FreeWord x) (j : b.FreeWord y) :
    b.FreeWord fun i => if n i=0 then x i else y i :=
  ⟨PolyCan.branch h.dry g.dry j.dry, (g.small.add j.small).mono fun _ => by split <;> omega⟩
lemma tape_congr_sized {n : ℕ} {α : Type*} {f g : ℕ→α} (h : ∀ j<n,f j=g j) :
    Tape.tab n f=Tape.tab n g :=
  congrArg (Tape.mk n) (funext fun j => h j j.2)
lemma pick_all {n k : ι→ℕ} (x : ι→ℕ→T t)
    (h : b.Moves (fun _ => 0) (a t) fun i => Tape.tab (n i) (x i)) (g : b.FreeWord k) :
    b.Moves (fun _ => 0) t fun i => if k i<n i then x i (k i) else t.blank :=
  (Can.look h g.toMoves).congr fun _ => by simp [Tape.look_tab]
def tablePow (z : ℂ) (k : ℕ) : T (a sc) :=
  Tape.tab (2^k) fun i => z^i

lemma geom_two (k : ℕ) : ∑ j ∈ range k, 2^(j+1) + 2 = 2*2^k := by
  induction k with
  | zero => simp
  | succ k ih => rw [sum_range_succ, add_right_comm, ih]; ring

lemma doublingTable {f : ι → ℕ → ℕ → T t} {E O : ι → T t → T t} (h : b.FreeWord k)
    (g : Small b.size fun i => 2^k i) (h0 : b.Moves (fun _ => 0) t fun i => f i 0 0)
    (hE : ∀ {κ : Type U} (q : Bench m κ) (p : κ → ι), q.FreeReads b p → ∀ y : κ → T t,
      q.Moves (fun _ => 0) t y → q.Moves (fun _ => 0) t fun x => E (p x) (y x))
    (hO : ∀ {κ : Type U} (q : Bench m κ) (p : κ → ι), q.FreeReads b p → ∀ y : κ → T t,
      q.Moves (fun _ => 0) t y → q.Moves (fun _ => 0) t fun x => O (p x) (y x))
    (hstep : ∀ i j r, f i (j+1) r = if r%2=0 then E i (f i j (r/2)) else O i (f i j (r/2))) :
    b.Moves (fun i => 2^k i) (a t) fun i => Tape.tab (2^k i) (f i (k i)) := by
  let Tb : ι → ℕ → Tape (T t) := fun i j => Tape.tab (2^j) (f i j)
  let c := b.climbs k (a t) Tb
  have tk := tokenNow (t := a t) b k Tb
  have init : b.Moves (fun _ => 0) (a t) fun i => Tb i 0 :=
    Can.weaken (arrayNow (WordIn.wc 1) (fun i _ => f i 0 0) (Moves.transfer h0 (FreeReads.scan b _)))
      (Dom.const _ 1) |>.congr fun i => tape_congr_sized fun j hj => by
        rw [Nat.lt_one_iff.1 hj]
  have gs : Small c.size fun d => 2^d.j := (g.reindex During.i).mono fun d => Nat.pow_le_pow_right (by norm_num) d.hj.le
  have hn : c.FreeWord fun d => 2^(d.j+1) :=
    (WordIn.mul ⟨(Can.len tk gs).toPoly _, gs⟩ (WordIn.wc 2)).congr fun d => (pow_succ _ _).symm
  have inst := (FreeReads.scan c fun d => 2^(d.j+1)).next (FreeReads.climbs (t := a t) b k Tb)
  have rj := scanIndex hn
  have y := (Moves.transfer tk (FreeReads.scan c _)).pick (fun e r => f e.i.i e.i.j r)
    (rj.div (WordIn.wc 2)).toMoves fun e => by
      have : e.j < 2^(e.i.j+1) := e.hj; show e.j / 2 < 2^e.i.j; rw [pow_succ'] at this
      exact Nat.div_lt_of_lt_mul this
  have body : c.Moves (fun d => 2^(d.j+1)) (a t) fun d => Tb d.i (d.j+1) :=
    (arrayNow hn (fun d r => if r%2=0 then E d.i (f d.i d.j (r/2)) else O d.i (f d.i d.j (r/2))) (Can.branch (rj.residue (WordIn.wc 2)).toMoves (hE _ _ inst _ y) (hO _ _ inst _ y))).congr
      fun d => congrArg _ (funext fun r => (hstep d.i d.j r).symm)
  refine Can.weaken (repeatM (t := a t) (u := fun _ j => 2^(j+1)) h Tb init body) ⟨3, fun i => ?_⟩
  have h1 := geom_two (k i)
  have h2 : k i < 2^k i := Nat.lt_pow_self (by norm_num : 1 < 2) ..
  beta_reduce; omega
lemma powTable_moves (h : b.FreeWord k)
    (g : Small b.size fun i => 2^k i) {z : ι→ℂ} (hz : b.Moves (fun _ => 0) sc z) :
    b.Moves (fun i => 2^k i) (a sc) fun i => tablePow (z i) (k i) := by
  unfold tablePow; exact doublingTable (f := fun i _ r => z i ^ r) (E := fun _ y => y*y) (O := fun i y => z i * (y*y)) h g
    (Can.one.congr fun _ => (pow_zero _).symm)
    (fun _ _ _ _ hy => Can.mul hy hy) (fun _ _ hp _ hy => Can.mul (Moves.transfer hz hp) (Can.mul hy hy))
    fun i _ r => by
      beta_reduce
      obtain ⟨q, rfl | rfl⟩ := Nat.even_or_odd' r
      · rw [if_pos (Nat.mul_mod_right 2 q), Nat.mul_div_cancel_left q two_pos]; ring
      · rw [if_neg (by rw [Nat.mul_add_mod]; exact one_ne_zero),
          show (2*q+1)/2 = q from (Nat.mul_add_div two_pos q 1).trans (Nat.add_zero q)]; ring

lemma square_pow {z : ι→ℂ} {u : ι→ℕ}
    (g : b.Moves (fun _ => 0) (a sc) fun i => tablePow (z i) (k i)) (hk : b.FreeWord n)
    (hn : ∀ i,0<n i ∧ n i≤2^k i) (hz : ∀ i, z i^n i=1) (hu : b.FreeWord u) :
    b.Moves (fun _ => 0) sc fun i => chirp (z i) (u i) :=
  (Can.pick (fun i r => z i ^ r) g ((hu.mul hu).residue hk).toMoves fun i =>
    (Nat.mod_lt _ (hn i).1).trans_le (hn i).2).congr fun i => power_mod (hz i) _

end Bench
end
end PowerSaving.RAM

end OAI

namespace OAI
namespace PowerSaving
namespace WeightTable
noncomputable section
open RAM RAM.Ty Binary Finset
universe U

/-- A tabulated tape is the layout tape of its entries read at the locations. -/
theorem _root_.OAI.PowerSaving.Layout.tab_eq_tape {β μ : Type*} (L : Layout β) (g : ℕ → μ) :
    Tape.tab L.n g = L.tape fun a => g (L.loc a) :=
  congrArg (Tape.mk L.n) (funext fun j => (congrArg g (L.loc_atFin j)).symm)

/-- Weight of the number `r` read on its lowest `j` binary digits: each digit `0` contributes `e`,
each digit `1` contributes `o`. -/
def digitWeight (e o : ℂ) (j r : ℕ) : ℂ :=
  ∏ l ∈ range j, if r / 2 ^ l % 2 = 0 then e else o

/-- Appending one low binary digit `b` to `q` multiplies the weight by that digit's factor. -/
lemma digitWeight_bit (e o : ℂ) (j q : ℕ) (b : Bool) :
    digitWeight e o (j + 1) (Nat.bit b q) = cond b o e * digitWeight e o j q := by
  unfold digitWeight
  rw [Finset.prod_range_succ', pow_zero, Nat.div_one, Nat.bit_mod_two, mul_comm]
  congr 1
  · cases b <;> simp
  · refine Finset.prod_congr rfl fun l _ => ?_
    rw [pow_succ', ← Nat.div_div_eq_div_mul, Nat.bit_div_two]

section Programs

/-- Tables of a multiplicative digit recursion: if `g i 0 0 = 1` and appending one more low digit
`b` multiplies by a zero-cost factor (`E` for a `0`, `O` for a `1`), the table of `g i (k i)` on
`2^(k i)` entries costs `2^(k i)`. -/
theorem weightTable {m : Bool} {ι : Type U} {b : Bench m ι} {k : ι → ℕ} {E O : ι → ℂ}
    (g : ι → ℕ → ℕ → ℂ) (g0 : ∀ i, g i 0 0 = 1)
    (gs : ∀ i j q (b : Bool), g i (j + 1) (Nat.bit b q) = cond b (O i) (E i) * g i j q)
    (hE : b.Moves (fun _ => 0) sc E) (hO : b.Moves (fun _ => 0) sc O) (hk : b.FreeWord k)
    (hs : Small b.size fun i => 2 ^ k i) :
    b.Moves (fun i => 2 ^ k i) (a sc) fun i => Tape.tab (2 ^ k i) (g i (k i)) :=
  Bench.doublingTable (f := g) (E := fun i y => E i * y) (O := fun i y => O i * y) hk hs
    (Can.one.congr fun i => (g0 i).symm)
    (fun _ _ hp _ hy => (hE.transfer hp).mul hy) (fun _ _ hp _ hy => (hO.transfer hp).mul hy)
    fun i j r => by
      have h := gs i j r.div2 r.bodd
      rw [Nat.bit_bodd_div2, Nat.div2_val] at h
      rw [h, Nat.mod_two_of_bodd]
      cases r.bodd <;> simp

/-- In `Can` form, over the bit layout: the tape of the letterwise products
`∏ (e if the bit is 0 else o)`. -/
theorem digitWeight_tape {m : Bool} {ι : Type U} {B : ι → ℕ} {s : Ty} {x : ι → T s}
    {k : ι → ℕ} {e o : ι → ℂ} (hk : Knows m B s x k) (sk : Small B k)
    (s2 : Small B fun i => 2 ^ k i) (he : Has m B s sc x e) (ho : Has m B s sc x o) :
    Can m B s (a sc) x (fun i => (bits (k i)).tape fun y => ∏ j, if y j = 0 then e i else o i)
      (fun i => 2 ^ k i) :=
  (weightTable (b := ⟨B, s, x⟩) (fun i => digitWeight (e i) (o i)) (fun _ => Finset.prod_range_zero _)
    (fun _ => digitWeight_bit _ _) he ho ⟨hk.toPoly _, sk⟩ s2).congr fun i => by
    rw [← bits_len, Layout.tab_eq_tape]
    refine congrArg _ (funext fun y => ?_)
    unfold digitWeight
    rw [← Fin.prod_univ_eq_prod_range (fun l => if (bits (k i)).loc y / 2 ^ l % 2 = 0 then e i else o i)]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [bits_div, ZMod.val_eq_zero]

end Programs
end
end WeightTable
end PowerSaving
end OAI

namespace OAI
namespace PowerSaving.RAM
open Ty Binary
universe U V

section
variable {ι : Type U} {κ : Type V} {m : Bool} {B : ι → ℕ} {s t q : Ty} {x : ι → T s}

theorem Has.extE {v : ι → T (p s t)} {z : ι → T q} {W : ι → ℕ}
    (h : Can m B s q (fun i => (v i).1) z W) : Can m B (p s t) q v z W :=
  Can.first.then_do h

theorem Has.liftE {e : κ → T t} {z : ι → T q} {W : ι → ℕ} (f : κ → ι) (h : Can m B s q x z W) :
    Can m (fun k => B (f k)) (p s t) q (fun k => (x (f k), e k)) (fun k => z (f k)) (fun k => W (f k)) :=
  Has.extE (h.reindex f)

end

end PowerSaving.RAM
end OAI

namespace OAI
namespace PowerSaving.Binary
open Matrix Finset
noncomputable section
/-- The ripple kernel on the digit positions selected by `P` only (`littleC` there, the identity
at the other positions). -/
def partKer (n : ℕ) (P : Fin n → Prop) [DecidablePred P] : CMat (Fin n) :=
  digitProd fun i => if P i then littleC else 1
/-- `partKer` applied to a vector. -/
def partRip (n : ℕ) (P : Fin n → Prop) [DecidablePred P] (v : Bits n → ℂ) : Bits n → ℂ :=
  partKer n P *ᵥ v
/-- Two complementary partial kernels make up the full ripple. -/
theorem partRip_compl (n : ℕ) (P Q : Fin n → Prop) [DecidablePred P] [DecidablePred Q]
    (hQ : ∀ i, Q i ↔ ¬ P i) (v : Bits n → ℂ) : partRip n Q (partRip n P v) = ripple n v := by
  unfold partRip ripple
  rw [mulVec_mulVec, partKer, partKer, digitProd_mul, rippleMat]
  congr 2; funext i
  by_cases hp : P i
  · simp only [hp, (hQ i).trans (not_congr (iff_true_intro hp)), if_true, if_false, not_true, Matrix.one_mul]
  · simp only [hp, (hQ i).trans (not_congr (iff_false_intro hp)), if_true, if_false, not_false_eq_true,
      Matrix.mul_one]
/-- Bits on `a` positions followed by bits on `b` positions. -/
def bitsAppend (a b : ℕ) : Bits a × Bits b ≃ Bits (a + b) :=
  (Equiv.sumArrowEquivProdArrow (Fin a) (Fin b) F).symm.trans
    (Equiv.arrowCongr finSumFinEquiv (Equiv.refl F))
@[simp] lemma bitsAppend_low {a b : ℕ} (u : Bits a × Bits b) (i : Fin a) :
    bitsAppend a b u (Fin.castAdd b i) = u.1 i := by
  rcases u with ⟨p, q⟩
  simp [bitsAppend, Equiv.arrowCongr_apply, Equiv.sumArrowEquivProdArrow_symm_apply_inl]
@[simp] lemma bitsAppend_high {a b : ℕ} (u : Bits a × Bits b) (j : Fin b) :
    bitsAppend a b u (Fin.natAdd a j) = u.2 j := by
  rcases u with ⟨p, q⟩
  simp [bitsAppend, Equiv.arrowCongr_apply, Equiv.sumArrowEquivProdArrow_symm_apply_inr]
/-- Bit vectors of equal lengths, identified along the cast of positions. -/
def bitsCast {a b : ℕ} (h : a = b) : Bits a ≃ Bits b :=
  Equiv.arrowCongr (finCongr h) (Equiv.refl F)
@[simp] lemma bitsCast_rfl (a : ℕ) : bitsCast (rfl : a = a) = Equiv.refl _ := rfl
lemma bitsCast_loc {a b : ℕ} (h : a = b) (v : Bits a) : (bits b).loc (bitsCast h v) = (bits a).loc v := by
  subst h; rfl
/-- The address of a cast concatenation. -/
lemma cast_append_loc {a b n : ℕ} (h : a + b = n) (u : Bits a) (v : Bits b) :
    (bits n).loc (bitsCast h (bitsAppend a b (u, v))) = (bits a).loc u + 2 ^ a * (bits b).loc v := by
  rw [bitsCast_loc, bits_loc, bits_loc, bits_loc, Fin.sum_univ_add, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by rw [bitsAppend_low, Fin.val_castAdd]
  · exact Finset.sum_congr rfl fun j _ => by rw [bitsAppend_high, Fin.val_natAdd, pow_add]; ring
lemma partKer_append (a b : ℕ) (u u' : Bits a) (q q' : Bits b) :
    partKer (a + b) (fun i => i.val < a) (bitsAppend a b (u, q)) (bitsAppend a b (u', q')) =
      rippleMat (Fin a) u u' * if q = q' then 1 else 0 := by
  rw [partKer, digitProd_apply, Fin.prod_univ_add, rippleMat, digitProd_apply, ← prod_delta]
  congr 1
  · exact prod_congr rfl fun i _ => by simp
  · exact prod_congr rfl fun j _ => by simp [Matrix.one_apply]
/-- The low partial kernel only touches the low block of a cast concatenation: it is the ripple on
that block, the high block staying a parameter. -/
theorem partRip_low_append {a b n : ℕ} (hn : a + b = n) (w : Bits n → ℂ) (u : Bits a) (q : Bits b) :
    partRip n (fun i => i.val < a) w (bitsCast hn (bitsAppend a b (u, q))) =
      ripple a (fun u' => w (bitsCast hn (bitsAppend a b (u', q)))) u := by
  subst hn
  simp only [bitsCast_rfl, Equiv.refl_apply, partRip, ripple, mulVec, dotProduct]
  rw [← (bitsAppend a b).sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun u' _ => ?_
  simp only [partKer_append, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, sum_ite_eq, mem_univ, if_true]
section
/-- A word seen as a grid with the empty pad. -/
def padNone (α : Type*) (f : ℕ) : Sky α f ≃ Grid α 0 f where
  toFun y := (0, y)
  invFun g := g.2
  left_inv _ := rfl
  right_inv g := Prod.ext (Subsingleton.elim _ _) rfl
/-- Addresses of (pad, word) pairs for a splitting `S` of the letters: the flattened `Fin k` parts
lowest, the complement body above them, the pad on top. -/
def placeLayout {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {k : ℕ}
    (S : Cleave α β (Fin k)) (X' : Layout β) (r f : ℕ) : Layout (Bits r × Sky α f) :=
  ((bits r).pair ((skyLayout X' f).pair (bits (k * f)))).comap
    ((Equiv.refl (Bits r)).prodCongr ((S.byLetter f).trans ((Equiv.refl _).prodCongr (bitFlat k f))))

lemma skyLayout_len {β : Type*} (X : Layout β) (f : ℕ) : (skyLayout X f).n = 2 ^ (X.n * f) := by
  show (2 ^ f) ^ X.n = _
  rw [← pow_mul, Nat.mul_comm]

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {k : ℕ}

/-- `placeLayout` numbers exactly `2^n` pairs when the fit equation holds. -/
lemma placeLayout_n (S : Cleave α β (Fin k)) (X' : Layout β) {r f n : ℕ}
    (h : k * f + X'.n * f + r = n) : (placeLayout S X' r f).n = (bits n).n := by
  show 2 ^ r * ((skyLayout X' f).n * 2 ^ (k * f)) = 2 ^ n
  rw [skyLayout_len, ← pow_add, ← pow_add, ← h]
  exact congrArg (2 ^ ·) (by ring)

/-- The placement of (pad, word) pairs in `n` bits: number the pair by `placeLayout` and take the
`n`-bit vector carrying that number. -/
def placeEquiv (S : Cleave α β (Fin k)) (X' : Layout β) {r f n : ℕ}
    (h : k * f + X'.n * f + r = n) : Bits r × Sky α f ≃ Bits n :=
  (placeLayout S X' r f).index.trans ((finCongr (placeLayout_n S X' h)).trans (bits n).index.symm)

/-- The address of a placed pair as one three-digit number: the flattened `Fin k` block lowest
(base `2^(k f)`), the complement body next (base `2^(|X'| f)`), the pad on top. -/
theorem placeEquiv_loc (S : Cleave α β (Fin k)) (X' : Layout β) {r f n : ℕ}
    (h : k * f + X'.n * f + r = n) (q : Bits r) (y : Sky α f) :
    (bits n).loc (placeEquiv S X' h (q, y)) =
      (bits (k * f)).loc (bitFlat k f (S.byLetter f y).2) +
        2 ^ (k * f) * ((skyLayout X' f).loc (S.byLetter f y).1 + 2 ^ (X'.n * f) * (bits r).loc q) := by
  have e : (bits n).loc (placeEquiv S X' h (q, y)) = (placeLayout S X' r f).loc (q, y) :=
    Layout.loc_atFin (bits n) _
  rw [e]
  show (bits r).loc q * ((skyLayout X' f).n * 2 ^ (k * f)) +
      ((skyLayout X' f).loc (S.byLetter f y).1 * 2 ^ (k * f) +
        (bits (k * f)).loc (bitFlat k f (S.byLetter f y).2)) = _
  rw [skyLayout_len]
  ring

/-- A placed pair is the cast concatenation of the flattened `Fin k` block and the serial
number of the pad with the complement word. -/
lemma placeEquiv_join (S : Cleave α β (Fin k)) (X' : Layout β) {r f n : ℕ}
    (h : k * f + X'.n * f + r = n) (q : Bits r) (y : Sky α f) :
    placeEquiv S X' h (q, y) = bitsCast ((Nat.add_assoc _ _ _).symm.trans h)
      (bitsAppend (k * f) (X'.n * f + r) (bitFlat k f (S.byLetter f y).2,
        gridToBits X' r f rfl (q, (S.byLetter f y).1))) := by
  apply (bits n).inj
  rw [placeEquiv_loc, cast_append_loc, gridToBits_loc]
  show _ = _ + _ * ((bits r).loc q * (skyLayout X' f).n + (skyLayout X' f).loc (S.byLetter f y).1)
  rw [skyLayout_len]
  ring

/-- For a splitting sending each `z i` to the unit vector `i`, the low partial ripple (below
`k f`), read along the placement at a fixed pad, is the letterwise block matrix of `z`. The proof
computes both sides as one sum over the `Fin k` words: the ripple kernel on the flattened block
is the letterwise kernel (`rippleMat_skyBits`), and the widened kernel is diagonal on complement words. -/
theorem placeEquiv_lowRipple (S : Cleave α β (Fin k)) {z : Fin k → Space α}
    (hz : ∀ i, S (z i) = (0, eu i))
    (X' : Layout β) {r f n : ℕ} (h : k * f + X'.n * f + r = n) (w : Bits n → ℂ) (q : Bits r) :
    (fun y => partRip n (fun i => i.val < k * f) w (placeEquiv S X' h (q, y))) =
      letterwise f (blockMat z) fun y => w (placeEquiv S X' h (q, y)) := by
  funext y
  let G : Bits (k * f) → ℂ := fun u' => w (bitsCast ((Nat.add_assoc _ _ _).symm.trans h)
    (bitsAppend (k * f) (X'.n * f + r) (u', gridToBits X' r f rfl (q, (S.byLetter f y).1))))
  let T : ℂ := ∑ c : Sky (Fin k) f,
    (∏ l, rippleMat (Fin k) ((S.byLetter f y).2 l) (c l)) * G (bitFlat k f c)
  have left : partRip n (fun i => i.val < k * f) w (placeEquiv S X' h (q, y)) = T := by
    rw [placeEquiv_join, partRip_low_append]
    refine ((bitFlat k f).sum_comp
      (fun u' => rippleMat (Fin (k * f)) (bitFlat k f (S.byLetter f y).2) u' * G u')).symm.trans ?_
    exact Finset.sum_congr rfl fun c _ =>
      congrArg (· * G (bitFlat k f c)) (congrFun (congrFun (rippleMat_skyBits k f) (S.byLetter f y).2) c)
  rw [left, ← widen_kernel S fun i => (AddEquiv.symm_apply_eq S).2 (hz i).symm]
  have hW : ∀ (d : Sky β f) (c : Sky (Fin k) f) (l : Fin f),
      S.widen (rippleMat (Fin k)) (y l) ((S.byLetter f).symm (d, c) l) =
        (1 : CMat β) ((S.byLetter f y).1 l) (d l) * rippleMat (Fin k) ((S.byLetter f y).2 l) (c l) :=
    fun d c l => by
      show (1 : CMat β) (S (y l)).1 (S (S.symm (d l, c l))).1 *
        rippleMat (Fin k) (S (y l)).2 (S (S.symm (d l, c l))).2 = _
      rw [AddEquiv.apply_symm_apply]
      rfl
  refine Eq.trans ?_ (letterwise_sum f _ _ y).symm
  refine Eq.trans ?_ ((S.byLetter f).symm.sum_comp _)
  rw [Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_eq_single (S.byLetter f y).1]
  · refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun l _ => ?_) ?_
    · rw [hW, Matrix.one_apply_eq, one_mul]
    · show _ = w (placeEquiv S X' h (q, (S.byLetter f).symm ((S.byLetter f y).1, c)))
      rw [placeEquiv_join, Equiv.apply_symm_apply]
  · intro d _ hd
    obtain ⟨l, hl⟩ := Function.ne_iff.1 hd
    refine mul_eq_zero_of_left (Finset.prod_eq_zero (Finset.mem_univ l) ?_) _
    rw [hW, Matrix.one_apply_ne (Ne.symm hl), zero_mul]
  · exact fun hn => absurd (Finset.mem_univ _) hn
end
end
end PowerSaving.Binary
end OAI
namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset GenMove
noncomputable section
universe U
structure ClassCtx {ι : Type U} (m : Bool) (B : ι → ℕ) (s : Ty) (x : ι → T s) (mx : ℕ) (n μ : ι → ℕ) : Prop where
  (nK : Knows m B s x n) (p2n : Knows m B s x fun i => 2^(n i))
  imag :
    Has m B s sc x fun _ => Complex.I
  (μK : Knows m B s x μ) (p2μ : Knows m B s x fun i => 2^(μ i))
  p2restBits : Knows m B s x fun i => 2^(n i - mx * μ i)
  txr : Has m B s (a w) x fun i => xorTab (μ i)
  tlum : Has m B s (a sc) x fun i => (bits (μ i)).tape fun y : Bits (μ i) => phaseProd y
  (big : Small B fun i => 2^(n i))
  fit :
    ∀ i, mx * μ i ≤ n i
  mx1 : 1 ≤ mx
section
/-- Role `l` of a class state, read through a placement `P` of (pad, word) pairs in `n` bits. -/
def readThrough {α ρ : Type*} {r f n : ℕ} (P : Bits r × Sky α f ≃ Bits n)
    (V : Bits r → RoleData α ρ 0 f) (l : ρ) : Bits n → ℂ :=
  (fun u : Bits r × Sky α f => V u.1 (l, 0, u.2)) ∘ P.symm
/-- Reading through `P` at a placed pair reads the pair itself. -/
@[simp] lemma readThrough_place {α ρ : Type*} {r f n : ℕ} (P : Bits r × Sky α f ≃ Bits n)
    (V : Bits r → RoleData α ρ 0 f) (l : ρ) (q : Bits r) (y : Sky α f) :
    readThrough P V l (P (q, y)) = V q (l, 0, y) := by
  unfold readThrough
  rw [Function.comp_apply, Equiv.symm_apply_apply]
/-- Fit arithmetic: a complement of size `b` next to `k` split coordinates fills the `a f`
letter bits. -/
lemma fit_split {a b k f r n : ℕ} (h1 : b + k = a) (h2 : a * f + r = n) :
    k * f + b * f + r = n := by
  rw [← h1, Nat.add_mul] at h2
  linarith
/-- Rows of paint cells: the rack type of engine calls and answers. -/
abbrev rackTy (cl : Paint) : Ty := a (a (c cl))
/-- The header of an engine call: kind word (`0` top, `1` class), bit count, block parameter,
and the unit `I`. -/
abbrev callHead : Ty := p w (p w (p w sc))
/-- The engine port: (call input = header and own-jobs rack, answer rack). -/
abbrev enginePort (cl : Paint) : Ty × Ty := (p callHead (rackTy cl), rackTy cl)
/-- The header value of an engine call, with `I` as its scalar. -/
def headVal (kind n par : ℕ) : T callHead := (kind, n, par, Complex.I)
/-- `n` bits split at `k`: low `k` bits, high `n - k` bits. -/
def lowHigh (n k : ℕ) (hk : k ≤ n) : Bits k × Bits (n - k) ≃ Bits n :=
  (bitsAppend k (n - k)).trans (bitsCast (Nat.add_sub_cancel' hk))
/-- The `n`-bit vector with low part `u` and, as high part, the element of the bit layout at the
reduction of `t` into its index set. -/
def sliceAddr {k n : ℕ} (hk : k ≤ n) (t : ℕ) (u : Bits k) : Bits n :=
  lowHigh n k hk (u, (bits (n - k)).index.symm (@Fin.ofNat _ ⟨(Nat.two_pow_pos (n - k)).ne'⟩ t))
lemma sliceAddr_loc {k n : ℕ} (hk : k ≤ n) (t : ℕ) (u : Bits k) :
    (bits n).loc (sliceAddr hk t u) = (bits k).loc u + 2 ^ k * (t % 2 ^ (n - k)) := by
  rw [sliceAddr, lowHigh, Equiv.trans_apply, cast_append_loc]
  exact congrArg (fun j => (bits k).loc u + 2 ^ k * j) ((bits (n - k)).loc_atFin _)
/-- The low partial ripple of `R` at the join of `(u, v)`: the ripple, at `u`, of `R` read along
`sliceAddr` at the address of `v`. -/
theorem glueJob_ripple (n k : ℕ) (hk : k ≤ n) (R : Bits n → ℂ) (u : Bits k) (v : Bits (n - k)) :
    partRip n (fun i => i.val < k) R (lowHigh n k hk (u, v)) =
      ripple k (fun u' => R (sliceAddr hk ((bits (n - k)).loc v) u')) u := by
  rw [lowHigh, Equiv.trans_apply, partRip_low_append]
  have hv : (bits (n - k)).index.symm
      (@Fin.ofNat _ ⟨(Nat.two_pow_pos (n - k)).ne'⟩ ((bits (n - k)).loc v)) = v :=
    (bits (n - k)).index.symm_apply_eq.2 (Fin.ext (Nat.mod_eq_of_lt ((bits (n - k)).bd v)))
  refine congrArg (fun G => ripple k G u) (funext fun u' => ?_)
  rw [sliceAddr, hv]
  rfl
end
/-- An engine job: a top job (`cls = false`; ripple `par` vectors on `n` bits) or a class job
(`cls = true`; block parameter `par`, one vector per slot). -/
structure EJob where
  cls : Bool
  n : ℕ
  par : ℕ
  vec : ℕ → Bits n → ℂ
/-- A block engine on letters `α`, roles `ρ` and live slots `σ`. Each slot sits on a role and
carries a family of independent letter directions; the script acts on every live role as the
block matrix (`blockMat`) of its family. -/
structure SlotEngine (α ρ σ : Type*) [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
    [Fintype σ] [DecidableEq σ] where
  LL : Layout α
  RL : Layout ρ
  SL : Layout σ
  three_le : 3 ≤ LL.n
  slots_pos : 0 < SL.n
  role : σ → ρ
  role_inj : Function.Injective role
  rank : σ → ℕ
  rank_le : ∀ l, rank l ≤ LL.n
  vec : ∀ l, Fin (rank l) → Space α
  vec_indep : ∀ l, LinearIndependent F (vec l)
  prog : Script α ρ
  prog_bounded : prog.Fits LL.n
  drives : RoleKernel.Drives role (fun l => blockMat (vec l)) prog
lemma dom_mul {ι : Type*} {W F : ι → ℕ} (K : ℕ) (h : ∀ i, F i ≤ K * W i) : Dom W F :=
  ⟨K + 1, fun i => by
    rw [mul_add_one]
    exact Nat.add_le_add ((h i).trans (Nat.mul_le_mul_right _ (Nat.le_succ K))) (Nat.succ_pos K)⟩
lemma lay_n {α : Type*} [Fintype α] (X : Layout α) {r : ℕ} (L : Layout (Fin (Fintype.card α - r)))
    (hr : r ≤ X.n) : L.n + r = X.n := by
  have h1 := L.card; have := X.card; rw [Fintype.card_fin] at h1; omega
/-- The placement of a block of rank `r` adapted to `z` under a letter layout `L` with
`L.n * μ ≤ n`: complement on the standard layout of the remaining positions, pad on top. -/
def blockPlace {α : Type*} [Fintype α] [DecidableEq α] (L : Layout α) {r μ n : ℕ}
    (S : Cleave α (Fin (Fintype.card α - r)) (Fin r)) (hf : L.n * μ ≤ n) (hr : r ≤ L.n) :
    Bits (n - L.n * μ) × Sky α μ ≃ Bits n :=
  placeEquiv S (Layout.std (Fintype.card α - r)) (fit_split (lay_n L _ hr) (Nat.add_sub_cancel' hf))
namespace SlotEngine
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ] (E : SlotEngine α ρ σ)
abbrev W : ℕ := E.SL.n
/-- The target rank of the slot at position `a`, `0` past the last slot. -/
def rankAt (a : ℕ) : ℕ := if h : a < E.W then E.rank (E.SL.atFin ⟨a, h⟩) else 0
abbrev mx : ℕ := E.LL.n
lemma fitc {n μ : ℕ} (hf : E.mx * μ ≤ n) : E.LL.n * μ + (n - E.mx * μ) = n :=
  Nat.add_sub_cancel' hf
/-- Threshold of the low kernel of row `t` of a class job. -/
def lowLen (μ t : ℕ) : ℕ := E.rankAt (t % E.W) * μ
abbrev CState (n μ : ℕ) := Bits (n - E.mx * μ) → RoleData α ρ 0 μ
/-- The slot living on role `j`, if any: the partial inverse of the injective role map. -/
def roleSlot (j : ρ) : Option σ := Function.partialInv E.role j
lemma slotOf_role (l : σ) : E.roleSlot (E.role l) = some l := Function.partialInv_left E.role_inj l
lemma slotOf_none (j : ρ) (h : ∀ l, E.role l ≠ j) : E.roleSlot j = none := by
  unfold roleSlot Function.partialInv
  exact dif_neg fun ⟨l, hl⟩ => h l hl
/-- The placement used for slot `l`. -/
def slotPlace {n μ : ℕ} (hf : E.mx * μ ≤ n) (l : σ) : Bits (n - E.mx * μ) × Sky α μ ≃ Bits n :=
  blockPlace E.LL (Cleave.adapted (E.vec l) (E.vec_indep l)) hf (E.rank_le l)
/-- The class state loaded from a class family: role `e l` reads row `l` through slot `l`'s
placement, the other roles are zero. -/
def initState {n μ : ℕ} (hf : E.mx * μ ≤ n) (J : ℕ → Bits n → ℂ) : E.CState n μ := fun q b =>
  match E.roleSlot b.1 with
  | some l => J (E.SL.loc l) (E.slotPlace hf l (q, b.2.2))
  | none => 0
/-- One move on a class state, at every class index and pad value. -/
def stepState {n μ : ℕ} (V : E.CState n μ) (mv : Move α ρ) : E.CState n μ :=
  fun q => padwise (mv.act μ) (V q)
def runV {n μ : ℕ} (V : E.CState n μ) (rippleUpTo : Script α ρ) : E.CState n μ :=
  fun q => padwise (Script.exec rippleUpTo μ) (V q)
lemma rk_fit {n μ r : ℕ} (hf : E.mx * μ ≤ n) (hr : r ≤ E.LL.n) : r * μ ≤ n :=
  (Nat.mul_le_mul_right μ hr).trans hf
/-- The exit job of a block move read through a placement `P`: the top job on `r μ` bits whose
`2^(n - r μ)` vectors are the slices of role `l` of `V` read through `P`. -/
def sliceJob {n μ r : ℕ} (P : Bits (n - E.mx * μ) × Sky α μ ≃ Bits n) (V : E.CState n μ) (l : ρ)
    (hk : r * μ ≤ n) : EJob :=
  ⟨false, r * μ, 2 ^ (n - r * μ), fun t u => readThrough P V l (sliceAddr hk t u)⟩
/-- The jobs one move sends out. -/
def moveKids {n μ : ℕ} (hf : E.mx * μ ≤ n) (V : E.CState n μ) : Move α ρ → List EJob
  | .kern l r z ind => if hr : r ≤ E.LL.n then
      [E.sliceJob (blockPlace E.LL (Cleave.adapted z ind) hf hr) V l (E.rk_fit hf hr)] else []
  | _ => []
/-- The jobs of a script, the state running along. -/
def leafKids {n μ : ℕ} (hf : E.mx * μ ≤ n) : E.CState n μ → Script α ρ → List EJob
  | _, [] => []
  | V, mv :: rippleUpTo => E.moveKids hf V mv ++ leafKids hf (E.stepState V mv) rippleUpTo
def childJobs : EJob → List EJob
  | ⟨true, n, μ, J⟩ => if hf : E.mx * μ ≤ n then E.leafKids hf (E.initState hf J) E.prog else []
  | ⟨false, _, _, _⟩ => []
/-- The port input of a job (kind word `0` for a top job, `1` for a class job). -/
def jobEnc (cl : Paint) (d : EJob) : T (enginePort cl).1 :=
  (headVal d.cls.toNat d.n (cond d.cls d.par 0),
    Tape.tab (cond d.cls E.W d.par) fun t => (bits d.n).tape (d.vec t))
/-- The expected port output of a job: the rack of its answered rows. -/
def jobRes (cl : Paint) (d : EJob) : T (a (a (c cl))) :=
  cond d.cls (Tape.tab E.W fun t => (bits d.n).tape (partRip d.n (fun i => i.val < E.lowLen d.par t) (d.vec t)))
    (Tape.tab d.par fun t => (bits d.n).tape (ripple d.n (d.vec t)))
end SlotEngine
section
universe V
variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] {ι : Type U} {m : Bool} {B : ι → ℕ} {s t : Ty} {x : ι → T s} {cl : Paint} {n N : ι → ℕ}
/-- A tape over layouts of length zero costs nothing. -/
lemma Has.voidTape {β : ι → Type*} (L : ∀ i, Layout (β i)) (hL : ∀ i, (L i).n = 0) (v : ∀ i, β i → T t) :
    Has m B s (a t) x fun i => (L i).tape (v i) :=
  (Can.layout (W := fun _ => 0) (P := fun _ => 0) ((Can.wc 0).congr fun i => (hL i).symm)
    ⟨Code.inert _ _, 0, 0, fun d => absurd ((L d.1).bd d.2) (by rw [hL]; exact Nat.not_lt_zero _)⟩
    ((Small.const B 0).mono fun i => (hL i).le)).mono fun i => by simp [hL]
/-- A tabulated tape of length zero, over any cell type, is free. -/
lemma Has.emptyTab {g : ι → ℕ → T t} : Has m B s (a t) x fun i => Tape.tab 0 (g i) :=
  (Has.voidTape (fun _ => Layout.std 0) (fun _ => rfl) (fun i j => g i j.val)).congr fun i =>
    (Layout.tab_eq_tape (Layout.std 0) (g i)).symm
/-- The sizes a rack build needs: its row count and row length, known and small. -/
structure RackSize (m : Bool) (B : ι → ℕ) (s : Ty) (x : ι → T s) (N K : ι → ℕ) : Prop where
  rows : Knows m B s x N
  width : Knows m B s x K
  rowsSmall : Small B N
  widthSmall : Small B K
/-- A two-level array of layout tapes, rows on the standard layout of `Fin (N i)` and each row on
any layout `L i`, from its entries (available from the input, the row number and the entry's
location), at cost `N + N · (length of L)`. -/
theorem Can.rackOf {β : ι → Type*} {N : ι → ℕ} (L : ∀ i, Layout (β i)) {R : ∀ i, Fin (N i) → β i → ℂ}
    (hz : RackSize m B s x N fun i => (L i).n)
    (he : Has m (fun d : Σ c : (Σ i, Fin (N i)), β c.1 => B d.1.1) (p (p s w) w) (c cl)
      (fun d => ((x d.1.1, d.1.2.val), (L d.1.1).loc d.2)) fun d => R d.1.1 d.1.2 d.2) :
    Can m B s (a (a (c cl))) x (fun i => (Layout.std (N i)).tape fun t => (L i).tape (R i t))
      (fun i => N i + N i * (L i).n) :=
  (Can.layout (L := fun i => Layout.std (N i)) (P := fun i => 0 + (L i).n + (L i).n * 0) hz.rows
    (Can.layout (L := fun d : (Σ i, Fin (N i)) => L d.1) (P := fun _ => 0)
      (Has.extE (hz.width.reindex Sigma.fst)) he (hz.widthSmall.reindex Sigma.fst))
    hz.rowsSmall).mono fun i => by
    show 0 + N i + N i * (0 + (L i).n + (L i).n * 0) ≤ _
    simp
/-- One entry of one row of a table of layout tapes: pick row `k` (below the row count), then fetch
the entry at the known location of `q` in that row's layout. Adds no cost to the inputs. -/
theorem Can.rowEntry {β : ι → Type*} (L : ∀ i, Layout (β i)) {k : ι → ℕ} {R : ∀ i, ℕ → β i → T t}
    {q : ∀ i, β i} {W : ι → ℕ}
    (hT : Can m B s (a (a t)) x (fun i => Tape.tab (N i) fun j => (L i).tape (R i j)) W)
    (hk : Can m B s w x k W) (hlt : ∀ i, k i < N i) (hq : Can m B s w x (fun i => (L i).loc (q i)) W) :
    Can m B s t x (fun i => R i (k i) (q i)) W :=
  have row : Can m B s (a t) x (fun i => (L i).tape (R i (k i))) W :=
    Can.pick (t := a t) (fun i j => (L i).tape (R i j)) hT hk hlt
  Can.fetch (L := L) (v := fun i => R i (k i)) row hq
variable (X : Layout α) (R : Layout ρ)
lemma roleLayout_n (f : ℕ) : (roleLayout X R 0 f).n = R.n * 2^(X.n * f) := by simp [roleLayout]
def stateTab (c restBits : ℕ) (V : Bits restBits → RoleData α ρ 0 c) : Tape (Tape ℂ) :=
  (bits restBits).tape fun q => (roleLayout X R 0 c).tape (V q)
lemma can_stateTab {col restBits : ι → ℕ} {V' : ∀ i, Bits (restBits i) → RoleData α ρ 0 (col i)}
    (hib : Knows m B s x (fun i => 2^(restBits i))) (hibs : Small B (fun i => 2^(restBits i)))
    {P : ι → ℕ} (hP : ∀ i, 2^(restBits i) + 2^(restBits i) * (R.n * 2^(X.n * col i)) ≤ P i)
    (hin : Can m (fun v : Σ i, Bits (restBits i) => B v.1) (p s w) (a (c cl))
      (fun v => (x v.1, (bits (restBits v.1)).loc v.2))
      (fun v => (roleLayout X R 0 (col v.1)).tape (V' v.1 v.2))
      (fun v => R.n * 2^(X.n * col v.1))) :
    Can m B s (a (a (c cl))) x (fun i => stateTab X R (col i) (restBits i) (V' i)) P :=
  (Can.layout (L := fun i => bits (restBits i)) (P := fun i => R.n * 2^(X.n * col i)) hib hin hibs).mono
    fun i => by simpa using hP i
variable {κ : Type V} {Bk : κ → ℕ} {sk : Ty} {y : κ → T sk}
    {col restBits : κ → ℕ} {V' : ∀ k, Bits (restBits k) → RoleData α ρ 0 (col k)}
    (qu : ∀ k, Bits (restBits k)) (bu : ∀ k, RoleCell α ρ 0 (col k))
    (ht : Has m Bk sk (a (a (c cl))) y (fun k => stateTab X R (col k) (restBits k) (V' k)))
    (hq : Knows m Bk sk y (fun k => (bits (restBits k)).loc (qu k)))
include ht hq
lemma has_stateTabRow :
    Has m Bk sk (a (c cl)) y (fun k => (roleLayout X R 0 (col k)).tape (V' k (qu k))) :=
  Can.fetch (L := fun k => bits (restBits k)) ht hq
lemma has_stateTabRead (hb : Knows m Bk sk y (fun k => (roleLayout X R 0 (col k)).loc (bu k))) :
    Has m Bk sk (c cl) y (fun k => V' k (qu k) (bu k)) :=
  Can.fetch (has_stateTabRow X R qu ht hq) hb
end
namespace ClassCtx
variable {ι : Type U} {B n μ : ι → ℕ} {mx : ℕ} {m : Bool} {s : Ty} {x : ι → T s}
/-- A class context moves along any reindexing, given the old input from the new one for free. -/
lemma pull (c : ClassCtx m B s x mx n μ) {κ : Type*} {t : Ty} (j : κ → ι) (y : κ → T t)
    (g : Has m (fun k => B (j k)) t s y (fun k => x (j k))) :
    ClassCtx m (fun k => B (j k)) t y mx (fun k => n (j k)) (fun k => μ (j k)) where
  nK := g.then_do (c.nK.reindex j)
  p2n := g.then_do (c.p2n.reindex j)
  imag := g.then_do (c.imag.reindex j)
  μK := g.then_do (c.μK.reindex j)
  p2μ := g.then_do (c.p2μ.reindex j)
  p2restBits := g.then_do (c.p2restBits.reindex j)
  txr := g.then_do (c.txr.reindex j)
  tlum := g.then_do (c.tlum.reindex j)
  big := c.big.reindex j
  fit k := c.fit (j k)
  mx1 := c.mx1
lemma pow_restBits_le (c : ClassCtx m B s x mx n μ) (i : ι) : 2^(n i - mx * μ i) ≤ 2^(n i) :=
  Nat.pow_le_pow_right two_pos (Nat.sub_le _ _)
lemma μ_le (c : ClassCtx m B s x mx n μ) (i : ι) : μ i ≤ n i := by
  have := c.fit i; have := c.mx1
  have h1 : μ i ≤ mx * μ i := Nat.le_mul_of_pos_left _ (by omega)
  omega
lemma gear (c : ClassCtx m B s x mx n μ) : BitCtx m B μ s x :=
  ⟨c.p2μ, c.μK, c.txr, c.big.mono fun i => Nat.pow_le_pow_right two_pos (c.μ_le i)⟩
lemma padPowSmall (c : ClassCtx m B s x mx n μ) : Small B fun i => 2 ^ (n i - mx * μ i) :=
  c.big.mono c.pow_restBits_le
lemma unit_size (c : ClassCtx m B s x mx n μ) {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
    (X : Layout α) (R : Layout ρ) (hX : X.n = mx) (i : ι) :
    2^(n i - mx * μ i) * (roleLayout X R 0 (μ i)).n = R.n * 2^(n i) := by
  have e : 2^(n i) = 2^(n i - mx * μ i) * 2^(mx * μ i) := by
    rw [← pow_add, Nat.sub_add_cancel (c.fit i)]
  rw [roleLayout_n, hX, e]; ring
end ClassCtx
namespace Move
variable {α ρ : Type*}
lemma rk_cases (mv : Move α ρ) :
    mv.rk? = none ∨ ∃ l r z ind, mv = Move.kern l r z ind := by
  rcases mv with (⟨l, r, z, ind⟩|_|_|_|_)
  all_goals first | exact Or.inl rfl | exact Or.inr ⟨l, r, z, ind, rfl⟩
end Move
section Loops
lemma can_iter {ι : Type U} {m : Bool} {B : ι → ℕ} {s : Ty} {x : ι → T s} {t : Ty} {n Wt : ι → ℕ} {v : ι → ℕ → T t} (hn : Knows m B s x n) (hns : Small B n)
    (h0 : Has m B s t x (fun i => v i 0))
    (hs : Can m (fun d : During n => B d.i) (p s (p w t)) t (fun d => (x d.i, d.j, v d.i d.j))
      (fun d => v d.i (d.j + 1)) (fun d => Wt d.i)) :
    Can m B s t x (fun i => v i (n i)) (fun i => n i * (Wt i + 1) + 1) :=
  (Can.loop (uB := fun i _ => Wt i) hn h0 hs hns).mono fun i => by simp [Nat.mul_add]; omega
end Loops
structure ClassIn {ι : Type U} (m : Bool) (B : ι → ℕ) (s : Ty) (x : ι → T s) (n μ : ι → ℕ) : Prop where
  (nK : Knows m B s x n) (μK : Knows m B s x μ)
  p2n :
    Knows m B s x fun i => 2^(n i)
  (imag : Has m B s sc x fun _ => Complex.I)
  (big : Small B fun i => 2^(n i))
  μS : Small B μ
namespace ClassIn
variable {ι : Type U} {B n μ : ι → ℕ} {m : Bool} {s : Ty} {x : ι → T s}
lemma nSmall (c : ClassIn m B s x n μ) : Small B n := c.big.mono fun _ => Nat.lt_two_pow_self.le
/-- A class context carries a class input: every field but `μS` is a field of the context, and
`μ ≤ n < 2^n` bounds `μ`. -/
lemma ofCtx {mx : ℕ} (c : ClassCtx m B s x mx n μ) : ClassIn m B s x n μ :=
  ⟨c.nK, c.μK, c.p2n, c.imag, c.big, c.big.mono fun i => (c.μ_le i).trans Nat.lt_two_pow_self.le⟩
end ClassIn
namespace SlotEngine
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ] (E : SlotEngine α ρ σ) {ι : Type U} {m : Bool} {B : ι → ℕ} {s : Ty} {x : ι → T s}
variable {n μ : ι → ℕ}
abbrev UnitsTy : Ty := p w w
def unitVal (n μ : ℕ) : T UnitsTy := (2^μ, 2^(n - E.mx * μ))
lemma knows_restBits (c : ClassIn m B s x n μ) : Knows m B s x (fun i => n i - E.mx * μ i) :=
  c.nK.minus ((Can.wc E.mx).times c.μK (Small.const _ _) c.μS) c.nSmall
def gearVal (μ : ℕ) : T (p (a w) (a sc)) := (xorTab μ, (bits μ).tape fun y : Bits μ => phaseProd y)
/-- The xor table and the `phaseProd` tape on `μ` bits. -/
lemma gears_can (c : ClassIn m B s x n μ) (hfit : ∀ i, E.mx * μ i ≤ n i) :
    Can m B (p s UnitsTy) (p (a w) (a sc)) (fun i => (x i, E.unitVal (n i) (μ i))) (fun i => gearVal (μ i))
      (fun i => 2 * 2 ^ n i + 2) := by
  have hle : ∀ i, μ i ≤ n i := fun i =>
    (Nat.le_mul_of_pos_left _ (show 0 < E.LL.n by have := E.three_le; omega)).trans (hfit i)
  have s2 : Small B fun i => 2 ^ μ i := c.big.mono fun i => Nat.pow_le_pow_right two_pos (hle i)
  have xo := Can.xor_prepare (Has.extE c.μK)
    (Can.second.fst : Has m B (p s UnitsTy) w (fun i => (x i, E.unitVal (n i) (μ i))) fun i => 2 ^ μ i) c.μS s2
  have lu := WeightTable.digitWeight_tape (Has.extE c.μK) c.μS s2 Can.one
    (Has.extE (v := fun i => (x i, E.unitVal (n i) (μ i))) c.imag)
  refine (xo.fork lu).mono fun i => ?_
  have h3 : (2 ^ μ i) ^ 3 ≤ 2 ^ n i := by
    rw [← pow_mul, Nat.mul_comm]
    exact Nat.pow_le_pow_right two_pos ((Nat.mul_le_mul_right _ E.three_le).trans (hfit i))
  have := Nat.pow_le_pow_right (n := 2) two_pos (hle i)
  show (2 ^ μ i) ^ 3 + 2 ^ μ i ≤ 2 * 2 ^ n i + 2
  omega
/-- A class input with a fitting block parameter, extended by its units and gears, is a class
context of the engine. -/
lemma ctx_of_cin (c : ClassIn m B s x n μ) (hfit : ∀ i, E.mx * μ i ≤ n i) :
    ClassCtx m B (p (p s UnitsTy) (p (a w) (a sc))) (fun i => ((x i, E.unitVal (n i) (μ i)), gearVal (μ i))) E.LL.n n μ where
  nK := Has.extE (Has.extE c.nK)
  p2n := Has.extE (Has.extE c.p2n)
  imag := Has.extE (Has.extE c.imag)
  μK := Has.extE (Has.extE c.μK)
  p2μ := Can.first.snd.fst
  p2restBits := Can.first.snd.snd
  txr := Can.second.fst
  tlum := Can.second.snd
  big := c.big
  fit := hfit
  mx1 := by have := E.three_le; omega
end SlotEngine
end
end PowerSaving.RAM
end OAI
end
