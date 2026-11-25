import Submission.BinaryKernel.FixedRows
import Submission.BinaryKernel.ColumnTape
import Submission.BinaryKernel.AxisLayout
import Submission.Ripple.RoleMoves
import Mathlib.Tactic

namespace OAI.PowerSaving.RAM.ColumnLeaves
open OAI.Computability.NearSquareRoot.KernelPass ColumnTape Binary RAM.Ty Finset
noncomputable section

def pairLayout : Layout (Fin 2 → ZMod 2) := bits 2
def colLayout (A : ℕ) : Layout (Column A) := (Layout.std A).digits pairLayout
def packed (A h : ℕ) : Layout (Addr A h) := (Layout.std h).digits (colLayout A)
def axisLayout (A h : ℕ) : Layout (Addr A h) :=
  ((Layout.std A).digits ((Layout.std h).digits pairLayout)).comap (Equiv.piComm (fun (_ : Fin h) (_ : Fin A) => Fin 2 → ZMod 2))

@[simp] theorem pair_n : pairLayout.n = 4 := rfl
@[simp] theorem col_n (A) : (colLayout A).n = 4^A := rfl
@[simp] theorem packed_n (A h) : (packed A h).n = (4^A)^h := rfl
@[simp] theorem axis_n (A h) : (axisLayout A h).n = (4^A)^h := by
  change (4^h)^A = (4^A)^h
  rw [← pow_mul,← pow_mul,Nat.mul_comm]

lemma axis_loc (A h) (y : Addr A h) :
    (axisLayout A h).loc y =
      ∑ a : Fin A, (∑ j : Fin h, pairLayout.loc (y j a)*4^j.val)*(4^h)^a.val := by
  unfold axisLayout Layout.comap
  rw [Layout.digits_code]
  congr 1; funext a
  rw [Layout.digits_code]
  rfl

private lemma div_pow_next (x q j : ℕ) :
    x / q / q^j = x / q^(j+1) := by rw [Nat.div_div_eq_div_mul,pow_succ']

theorem fold_values (q r : ℕ) (g tag : ℕ → ℕ) (h x : ℕ) :
    let v := foldDigits q (0,0) (trans r g tag) h x
    v.1 = ∑ i : Fin h, g (x/q^i.val%q)*r^i.val ∧
    (v.2 : ZMod 2) = ∑ i : Fin h, (tag (x/q^i.val%q) : ZMod 2) := by
  induction h generalizing x with
  | zero => simp [foldDigits]
  | succ h ih =>
    dsimp only [foldDigits,ColumnTape.trans]; rcases ih (x/q) with ⟨a,b⟩
    constructor
    · rw [a, Fin.sum_univ_succ, Finset.mul_sum]
      simp only [Fin.val_zero,Nat.pow_zero,Nat.div_one,Nat.mul_one,Fin.val_succ]
      rw [Nat.add_comm]; congr 1; apply Finset.sum_congr rfl; intro i _
      rw [div_pow_next, pow_succ]; ring
    · rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero,Nat.pow_zero,Nat.div_one,Fin.val_succ]
      rw [ZMod.natCast_mod,Nat.cast_add,b,add_comm]
      congr 1; apply Finset.sum_congr rfl; intro i _
      rw [div_pow_next]

/-- Finite input alphabet decoder. In the RAM program only fixed small digit
tables are compiled from this mathematical definition. -/
def decode (A d : ℕ) : Column A :=
  (colLayout A).atFin ⟨d % (colLayout A).n, Nat.mod_lt _ (by simp)⟩

theorem decode_digit (A h) (y : Addr A h) (i : Fin h) :
    decode A ((packed A h).loc y / (4^A)^i.val % (4^A)) = y i := by
  have g := Layout.digits_entry (Layout.std h) (colLayout A) y i
  change (packed A h).loc y / (4^A)^i.val % (4^A) = (colLayout A).loc (y i) at g
  rw [g]; apply (colLayout A).inj
  unfold decode; rw [Layout.loc_atFin]; exact Nat.mod_eq_of_lt ((colLayout A).bd _)

def emitted {A : ℕ} (perm : Column A → Column A) (a : Fin A) (digit : ℕ) : Fin 4 :=
  pairLayout.toIx ((perm (decode A digit)) a)

def tagValue {A : ℕ} (T : Column A → ZMod 2) (digit : ℕ) : ℕ := (T (decode A digit)).val

theorem lane {A h : ℕ} (perm : Column A → Column A) (a : Fin A) (T : Column A → ZMod 2)
    (y : Addr A h) :
    let v := foldDigits (4^A) (0,0) (trans 4 (fun d => (emitted perm a d).val) (tagValue T)) h
      ((packed A h).loc y)
    v.1 = ∑ j : Fin h, pairLayout.loc (perm (y j) a)*4^j.val ∧
    (v.2 : ZMod 2) = ∑ j, T (y j) := by
  simpa [emitted,tagValue,decode_digit,Layout.toIx] using
    fold_values (4^A) 4 (fun d => (emitted perm a d).val) (tagValue T) h ((packed A h).loc y)

theorem same_code {A h} (y : Addr A h) :
    (axisLayout A h).loc y = DFTSpeedrun.AxisLayout.code y := by
  rw [axis_loc,DFTSpeedrun.AxisLayout.code_sum]
  apply Finset.sum_congr rfl; intro a _
  have lane := spread_loc (DFTSpeedrun.AxisLayout.bitOrder h) (fun z => y z.1 a z.2)
  change DFTSpeedrun.AxisLayout.digit (fun c => y c a) = _ at lane
  rw [lane,Fintype.sum_prod_type]
  have width : DFTSpeedrun.AxisLayout.stride a h = (4^h)^a.val := by
    unfold DFTSpeedrun.AxisLayout.stride DFTSpeedrun.AxisLayout.width
    rw [Nat.mul_comm h 2,pow_mul]; rfl
  rw [width]; congr 1; apply Finset.sum_congr rfl; intro j _
  change (bits 2).loc (y j a) * 4^j.val = _
  rw [bits_loc,Finset.sum_mul]; apply Finset.sum_congr rfl; intro t _
  change _ * 2^t.val * 4^j.val = _ * 2^(j.val*2+t.val)
  rw [pow_add,Nat.mul_comm j.val 2,pow_mul]; ring

private theorem major_value {A h} (perm : Column A → Column A) (T : Column A → ZMod 2)
    (y : Addr A h) {n : ℕ} (axes : Fin n → Fin A) :
    let v := majorRadix (4^A) 4 (tagValue T) h ((packed A h).loc y)
      (List.ofFn (fun j => emitted perm (axes j)))
    v.1 = ∑ j : Fin n, (∑ c : Fin h, pairLayout.loc (perm (y c) (axes j))*4^c.val)*(4^h)^j.val ∧
    (v.2 : ZMod 2) = ∑ c, T (y c) := by
  induction n with
  | zero =>
    simp only [List.ofFn_zero, majorRadix, Finset.univ_eq_empty,Finset.sum_empty]
    simpa [tagValue,decode_digit] using
      fold_values (4^A) 2 (fun _ => 0) (tagValue T) h ((packed A h).loc y)
  | succ n ih =>
    rw [List.ofFn_succ]; dsimp only [majorRadix]
    obtain ⟨hi,ht⟩ := ih (fun j => axes j.succ)
    refine ⟨?_,ht⟩
    rw [hi,(lane perm (axes 0) T y).1,Fin.sum_univ_succ,Finset.sum_mul]
    simp only [Fin.val_zero,pow_zero,mul_one,Fin.val_succ]
    rw [Nat.add_comm]; congr 1; apply Finset.sum_congr rfl; intro j _
    rw [pow_succ]; ring

theorem encode_image {A h} (perm : Column A → Column A) (T : Column A → ZMod 2)
    (y : Addr A h) :
    let v := majorRadix (4^A) 4 (tagValue T) h ((packed A h).loc y)
      (List.ofFn (emitted perm))
    v.1 = DFTSpeedrun.AxisLayout.code (perm ∘ y) ∧
    (v.2 : ZMod 2) = ∑ c, T (y c) := by
  rw [← same_code,axis_loc]
  exact major_value perm T y id

open DFTSpeedrun.AxisLayout
universe u

abbrev volume (A h : ℕ) := (4^A)^h

theorem size_eq (A h : ℕ) : (DFTSpeedrun.AxisLayout.shape A h).n = volume A h := by
  change (2^(h*2))^A = (4^A)^h
  rw [show 2^(h*2)=4^h by rw [Nat.mul_comm h 2,pow_mul]; rfl, ← pow_mul, ← pow_mul,Nat.mul_comm h A]

def image (A h : ℕ) (perm : Column A → Column A) (t : Column A → ZMod 2) (j : ℕ) :=
  majorRadix (4^A) 4 (tagValue t) h j (List.ofFn (emitted perm))

theorem image_cost {A : ℕ} (ha : 0 < A) {ι : Type u} {m : Bool} {b : Bench m ι}
    (h : ι → ℕ) (perm : Column A → Column A) (T : Column A → ZMod 2)
    (count : b.Nick h) (cap : Small b.size (fun i => volume A (h i)))
    (stride : b.Nick (fun i => 4^(h i))) :
    b.Moves (fun i => volume A (h i)) (a (p w w))
      (fun i => Tape.tab (volume A (h i)) (image A (h i) perm T)) := by
  have hr : 4 ≤ 4^A := by
    calc 4 = 4^1 := by simp
         _ ≤ _ := Nat.pow_le_pow_right (by decide) ha
  exact majorRadixTable (by omega) hr _ (fun i _ => (T (decode A i)).val_lt)
    _ count cap stride

def scatterEquiv (A h : ℕ) : Fin (volume A h) ≃ Fin (volume A h) :=
  (packed A h).index.symm.trans
    ((DFTSpeedrun.AxisLayout.shape A h).index.trans (finCongr (size_eq A h)))

theorem scatter_eq {A h : ℕ} (j : Fin (volume A h)) :
    (scatterEquiv A h j).val = code ((packed A h).atFin j) := rfl

theorem image_addr {A h : ℕ} (perm : Column A → Column A) (T : Column A → ZMod 2)
    (j : Fin (volume A h)) :
    (image A h perm T j.val).1 = code (perm ∘ (packed A h).atFin j) := by
  have g := (encode_image perm T ((packed A h).atFin j)).1
  rw [Layout.loc_atFin (packed A h) j] at g; exact g

theorem image_phase {A h : ℕ} (perm : Column A → Column A) (T : Column A → ZMod 2)
    (j : Fin (volume A h)) :
    ((image A h perm T j.val).2 : ZMod 2) = ∑ c, T (((packed A h).atFin j) c) := by
  have g := (encode_image perm T ((packed A h).atFin j)).2
  rw [Layout.loc_atFin (packed A h) j] at g; exact g

private def canon {A h : ℕ} (f : Addr A h → ℂ) (j : ℕ) : ℂ :=
  ((DFTSpeedrun.AxisLayout.shape A h).tape f).look j 0

private theorem canon_tab {A h : ℕ} (f : Addr A h → ℂ) :
    Tape.tab (volume A h) (canon f) = (DFTSpeedrun.AxisLayout.shape A h).tape f := by
  apply Tape.ext_look (by exact (size_eq A h).symm) 0
  intro j hj
  change j < volume A h at hj
  simp only [Tape.look_tab,if_pos hj]; rfl

/-- An address permutation selected column by column, on the actual axis-major
layout of the recursion. The column map need not be a bijection: the scatter
writes by the original address, and gathers from the transformed address. -/
theorem reindex {A : ℕ} (ha : 0 < A) {ι : Type u} {m : Bool} {b : Bench m ι}
    (cl : Paint) (h : ι → ℕ) (v : ∀ i, Addr A (h i) → ℂ) (perm : Column A → Column A)
    (count : b.Nick h) (cap : Small b.size (fun i => volume A (h i)))
    (stride : b.Nick (fun i => 4^(h i)))
    (inp : b.Moves (fun _ => 0) (a (c cl)) (fun i => (DFTSpeedrun.AxisLayout.shape A (h i)).tape (v i))) :
    b.Moves (fun i => volume A (h i)) (a (c cl))
      (fun i => (DFTSpeedrun.AxisLayout.shape A (h i)).tape (fun y => v i (perm ∘ y))) := by
  let N := fun i => volume A (h i)
  let X := fun i => (DFTSpeedrun.AxisLayout.shape A (h i)).tape (v i)
  let addr := fun (i : ι) j => (image A (h i) id (fun _ => 0) j).1
  let loc := fun (i : ι) j => (image A (h i) perm (fun _ => 0) j).1
  let e := fun i j => (addr i j,(X i).look (loc i j) 0)
  have z : b.Moves N (a (p w (c cl))) (fun i => Tape.tab (N i) (e i)) := by
    apply zipTables cap (image_cost ha h id (fun _ => 0) count cap stride)
      (image_cost ha h perm (fun _ => 0) count cap stride)
    intro c q left right
    exact left.fst.pair (Can.look (inp.transfer q) right.fst)
  have g := applyPermutation (t := c cl) cap (fun i => scatterEquiv A (h i))
    e (fun i => canon (fun y => v i (perm ∘ y))) z (fun i j => by
      simpa [e,addr,scatter_eq] using image_addr id (fun _ => 0) j)
    (fun i j => by
      change (X i).look (loc i j.val) 0 = _
      dsimp only [loc]; rw [image_addr,scatter_eq]
      simp [X,canon,code,Layout.read])
  exact g.congr fun i => canon_tab _

private theorem chooseScalar {ι : Type u} {m : Bool} {b : Bench m ι} {q : ℕ}
    (sig : ι → Fin q → ZMod 2) (table : (Fin q → ZMod 2) → ℚ)
    (bit : ∀ a, b.Moves (fun _ => 0) w fun i => (sig i a).val) :
    b.Moves (fun _ => 0) sc fun i => (table (sig i) : ℂ) := by
  have sm (a : Fin q) : Small b.size (fun i => (sig i a).val * 2^a.val) :=
    (Small.const _ (2*2^a.val)).mono (fun i => Nat.mul_le_mul_right _ (sig i a).val_lt.le)
  have e := Can.sum_wconst (fun a : Fin q => (bit a).wmul (Can.wc (2^a.val)) (sm a)) sm
  apply Can.cases_code (bits q) (q := sig) (e.cy (fun i => (bits_loc q (sig i)).symm))
  intro j
  exact (Can.rat (table j)).cy (fun i => by rw [i.property])

/-- Materialize all fixed parity tests once, then select the rational scalar
for each cell and scatter its scaled value into axis-major order. -/
theorem diagonal {A : ℕ} (ha : 0 < A) {ι : Type u} {m : Bool} {b : Bench m ι}
    (cl : Paint) (h : ι → ℕ) (v : ∀ i, Addr A (h i) → ℂ) {q : ℕ}
    (test : Column A → Fin q → ZMod 2) (table : (Fin q → ZMod 2) → ℚ)
    (count : b.Nick h) (cap : Small b.size (fun i => volume A (h i)))
    (stride : b.Nick (fun i => 4^(h i)))
    (inp : b.Moves (fun _ => 0) (a (c cl)) (fun i => (DFTSpeedrun.AxisLayout.shape A (h i)).tape (v i))) :
    b.Moves (fun i => volume A (h i)) (a (c cl))
      (fun i => (DFTSpeedrun.AxisLayout.shape A (h i)).tape
        (fun y => (table (∑ k, test (y k)) : ℂ) * v i y)) := by
  let N := fun i => volume A (h i)
  let X := fun i => (DFTSpeedrun.AxisLayout.shape A (h i)).tape (v i)
  let I := fun i => image A (h i) id (fun _ => 0)
  let F := fun i (a : Fin q) => image A (h i) id (fun y => test y a)
  let rows := fun i a => Tape.tab (N i) (F i a)
  let sig := fun i j (a : Fin q) => ((F i a j).2 : ZMod 2)
  let e := fun i j => ((I i j).1, (table (sig i j) : ℂ) * (X i).look (I i j).1 0)
  have allRows : b.Moves N (Ty.a (Ty.a (p w w))) (fun i => FixedRows.fixed (rows i)) :=
    FixedRows.assemble fun a => image_cost ha h id (fun y => test y a) count cap stride
  have z : b.Moves N (a (p w (c cl))) (fun i => Tape.tab (N i) (e i)) := by
    have addr := image_cost ha h id (fun _ => 0) count cap stride
    apply Bench.caseM (addr.pair allRows)
    let c' := b.extend (p (a (p w w)) (a (a (p w w))))
      (fun i => (Tape.tab (N i) (I i), FixedRows.fixed (rows i)))
    have cached : c'.Moves (fun _ => 0) (p (a (p w w)) (a (a (p w w))))
        (fun i => (Tape.tab (N i) (I i), FixedRows.fixed (rows i))) := Bench.cherry _ _
    have sz : c'.Nick N := ⟨cached.fst.len cap,cap⟩
    apply Bench.arrayNow sz
    let d := c'.scan N
    let transfer := Bench.Instant.scan c' N
    have jRead := (Bench.chop sz).close
    have codeRead : d.Moves (fun _ => 0) (p w w) (fun j => I j.i j.j) :=
      Bench.Moves.pick (t := p w w) (fun j : During N => I j.i) (cached.fst.transfer transfer) jRead (fun j => j.hj)
    have scalar : d.Moves (fun _ => 0) sc (fun j => (table (sig j.i j.j) : ℂ)) := by
      apply chooseScalar (fun (j : During N) => sig j.i j.j) table
      intro a
      have r : c'.Moves (fun _ => 0) (Ty.a (p w w)) (fun i => rows i a) :=
        FixedRows.row cached.snd a
      have field : d.Moves (fun _ => 0) (p w w) (fun j => F j.i a j.j) :=
        Bench.Moves.pick (t := p w w) (fun j : During N => F j.i a) (r.transfer transfer) jRead (fun j => j.hj)
      exact (field.snd.wmod (Can.wc 2) ((Small.const _ 2).mono
        (fun j => (Nat.mod_lt _ (by decide : 0 < 2)).le))).cy
          (fun j => (ZMod.val_natCast 2 _).symm)
    exact codeRead.fst.pair (scalar.mul (Can.look (inp.transfer
      (transfer.next (Bench.Instant.extend _ _))) codeRead.fst))
  apply (applyPermutation (t := c cl) cap (fun i => scatterEquiv A (h i))
    e (fun i => canon (fun y => (table (∑ k, test (y k)) : ℂ) * v i y)) z ?_ ?_).congr
  · intro i; exact canon_tab _
  · intro i j; simpa [e,I,scatter_eq] using image_addr id (fun _ => 0) j
  · intro i j
    have phase : sig i j.val = ∑ k, test (((packed A (h i)).atFin j) k) := by
      funext a
      simpa [sig,F,Finset.sum_apply] using image_phase id (fun y => test y a) j
    dsimp only [e,I]; rw [phase,image_addr,scatter_eq]
    simp [X,canon,code,Layout.read]

end
end OAI.PowerSaving.RAM.ColumnLeaves
#print axioms OAI.PowerSaving.RAM.ColumnLeaves.reindex

#print axioms OAI.PowerSaving.RAM.ColumnLeaves.diagonal
