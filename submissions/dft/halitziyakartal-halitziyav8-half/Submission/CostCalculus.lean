-- The program-building calculus, in two parts (judgments and benches; layouts and layout programs),
-- each with its own notices and credits; see texts/credits.lean.
import Submission.RAM
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.SuccPred
import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.Nat.Log
set_option linter.all false

-- ===== begin part 1: tapes, cost judgments (`Able`, `Can`, `PolyCan`) =====
section
--might be  containing modified Apache-2.0 codes pieces from one or several sources; notices and credits: Credits.lean
namespace OAI
namespace PowerSaving
universe u v U V Z
variable {α β : Type*}
namespace Tape
-- moved from OAI/Computability/FourierTransform/RAM.lean (OpenAI, Apache-2.0, texts/credits.lean item 1):
-- unreached by the challenge statement, used here; same full names.
@[simp] theorem look_of_lt (v : Tape α) (z : α) {i} (h : i < v.len) :
    v.look i z = v.pos ⟨i,h⟩ := by simp [look, h]

-- end moved from RAM.lean
lemma ext_look {a b : Tape α} (hlen : a.len = b.len) (z : α) (h : ∀ i, i<a.len → a.look i z = b.look i z) : a=b := by
  obtain ⟨n, f⟩ := a; obtain ⟨n', g⟩ := b
  obtain rfl : n = n' := hlen
  congr 1; funext j; simpa [Tape.look] using h j j.2
lemma look_tab (n : ℕ) (f : ℕ → α) (i z) : (tab n f).look i z = if i<n then f i else z := by
  by_cases h : i < n <;> simp [look, tab, h]
@[simp] lemma len_sow (n c : ℕ) (z : α) (f : ℕ → ℕ × α) : (sow n c z f).len = n := by
  induction c with
  | zero => rfl
  | succ c ih => exact ih
theorem sow_look_written {n k i j : ℕ} {z out : α} {f : ℕ → ℕ × α}
    (hin : i<n) (hj : j<k) (hf : (f j).1 = i)
    (hlast : ∀ s, j<s → s<k → (f s).1 ≠ i) :
    (sow n k z f).look i out = (f j).2 := by
  induction k with
  | zero => omega
  | succ k ih =>
    show ((sow n k z f).set (f k).1 (f k).2).look i out = _
    rcases (by omega : j < k ∨ j = k) with hj | rfl
    · rw [← ih hj fun s h1 _ => hlast s h1 (by omega)]; simp [look, set, (hlast k hj (by omega)).symm]
    · simp [look, set, hf, hin]
lemma sow_tab (n : ℕ) (z : α) (v : ℕ → α) : sow n n z (fun i => (i, v i)) = tab n v :=
  ext_look (len_sow ..) z fun i hi => by
    rw [len_sow] at hi
    rw [look_tab, if_pos hi, sow_look_written hi hi rfl fun s h1 _ => (Nat.ne_of_lt h1).symm]
end Tape
end PowerSaving
end OAI
end

section
--might be  containing modified Apache-2.0 codes pieces from one or several sources; notices and credits: Credits.lean
namespace OAI
namespace PowerSaving
open Finset
universe u v U V Z
variable {α β : Type*}
macro "ar" : tactic => `(tactic| (first | omega | ((try dsimp only); ring_nf; omega)))
namespace RAM
open Ty
namespace Bill
structure OK (b : Bill α) (x : α) (w p : ℕ) : Prop where
  result : b.val = x
  time : b.work ≤ w
  bound : b.peak ≤ p
  valid : b.valid
variable {x : α} {y : β} {w w' p p' z t : ℕ} {a b : ℕ → ℕ} {C P l k : ℕ}
lemma OK.mono {b : Bill α} (h : b.OK (x:α) w p) (u : w ≤ w') (v : p ≤ p') : b.OK x w' p' :=
  ⟨h.1, h.2.trans u, h.3.trans v, h.4⟩
lemma OK.pay {b : Bill α} (h : b.OK (x:α) w p) (h' : z ≤ p) : (b.pay t z).OK x (w+t) p :=
  ⟨h.1, Nat.add_le_add_right h.2 t, max_le h.3 h', h.4⟩
lemma OK.pass {b : Bill α} (h : b.OK (x:α) w p) {f : α → Bill β} (g : (f x).OK y w' p) : (b.pass f).OK y (w+w') p := by
  obtain ⟨rfl, h1, h2, h3⟩ := h
  exact ⟨g.1, Nat.add_le_add h1 g.2, max_le h2 g.3, And.intro h3 g.4⟩
lemma one_ok (x : α) (p : ℕ) : (one x).OK x 1 p := ⟨rfl, le_rfl, Nat.zero_le _, trivial⟩
lemma OK.tick {b : Bill α} (h : b.OK x w p) (u : w + 1 ≤ w') : (b.pay 1 0).OK x w' p := (h.pay (Nat.zero_le _)).mono u le_rfl
lemma sc (C k : ℕ) (a b : ℕ → ℕ) : ∀ n, ∑ j ∈ range n, (C*(a j+1)+b j+k) = C*(n+∑ j ∈ range n, a j)+∑ j ∈ range n, b j+k*n
  | 0 => by simp
  | n+1 => by simp only [sum_range_succ, sc C k a b n]; ring
lemma steps_ok {v : ℕ → α} {f : ℕ → α → Bill α} {A : ℕ → ℕ} {n p : ℕ} (hn : n ≤ p)
    (h : ∀ j < n, (f j (v j)).OK (v (j+1)) (A j) p) :
    (steps (v 0) f n).OK (v n) (1 + ∑ j ∈ range n, (A j + 1)) p := by
  induction n with
  | zero => exact ⟨rfl, by simp [steps, one], Nat.zero_le _, trivial⟩
  | succ n ih =>
    exact (((ih (by omega) fun j hj => h j (by omega)).pass (h n (by omega))).pay (t := 1) hn).mono
      (by rw [sum_range_succ]; omega) le_rfl
lemma sow_ok {g : ℕ → ℕ × α} {f : ℕ → Bill (ℕ × α)} (A : ℕ → ℕ) {len k p : ℕ} (z : α) (hl : len ≤ p)
    (hk : k ≤ p) (h : ∀ i < k, (f i).OK (g i) (A i) p) :
    (sow len k z f).OK (Tape.sow len k z g) (1 + ∑ i ∈ range k, (A i + 2) + (1+len)) p :=
  (steps_ok (v := fun j => Tape.sow len j z g) (f := fun i v => (f i).pass fun s => one (v.set s.1 s.2))
    (A := fun j => A j + 1) hk fun j hj => (h j hj).pass (one_ok _ _)).pay hl
lemma tab_ok {v : ℕ → α} {f : ℕ → Bill α} (W : ℕ → ℕ) (len p : ℕ) (z : α) (hl : len ≤ p) (h : ∀ i, i<len → (f i).OK (v i) (W i) p) : (tab len z f).OK (Tape.tab len v) ((1+∑ i ∈ range len, (W i+3))+(1+len)) p := by
  rw [← Tape.sow_tab len z v]
  exact sow_ok (fun i => W i + 1) z hl hl fun i hi => (h i hi).pass (f := fun y => one (i, y)) (one_ok _ _)
end Bill
lemma sum_const' (n c : ℕ) : ∑ _j ∈ range n, c = n*c := by simp
def Small {ι : Type u} (B F : ι → ℕ) : Prop := ∃ d : ℕ, ∀ i, F i ≤ (B i+2)^d
namespace Small
variable {ι : Type u} {κ : Type v} {B C F G : ι → ℕ}
lemma const (B : ι → ℕ) (n : ℕ) : Small B (fun _ => n) := ⟨n, fun i => (Nat.lt_pow_self (by omega : 1 < B i + 2) ..).le⟩
lemma self (B : ι → ℕ) : Small B B := ⟨1, fun i => by rw [pow_one]; omega⟩
lemma poly (B : ι → ℕ) (d : ℕ) : Small B (fun i => (B i+2)^d) := ⟨d, fun _ => le_rfl⟩
lemma reindex (h : Small B F) (f : κ → ι) : Small (fun j => B (f j)) (fun j => F (f j)) :=
  let ⟨d, h⟩ := h; ⟨d, fun j => h (f j)⟩
lemma mono (h : Small B F) (hh : ∀ i, G i ≤ F i) : Small B G :=
  let ⟨d, h⟩ := h; ⟨d, fun i => (hh i).trans (h i)⟩
lemma mul (h : Small B F) (g : Small B G) : Small B (fun i => F i * G i) :=
  let ⟨d, h⟩ := h; let ⟨e, g⟩ := g; ⟨d+e, fun i => by rw [pow_add]; exact Nat.mul_le_mul (h i) (g i)⟩
lemma pow_mono_degree (b : ℕ) {d e : ℕ} (h : d ≤ e) : (b+2)^d ≤ (b+2)^e := Nat.pow_le_pow_right (by omega) h
lemma max (h : Small B F) (g : Small B G) : Small B (fun i => Max.max (F i) (G i)) :=
  let ⟨d, h⟩ := h; let ⟨e, g⟩ := g
  ⟨d+e, fun i => max_le ((h i).trans (pow_mono_degree _ (Nat.le_add_right _ _)))
    ((g i).trans (pow_mono_degree _ (Nat.le_add_left _ _)))⟩
lemma add (h : Small B F) (g : Small B G) : Small B (fun i => F i + G i) :=
  ((h.max g).mul (const B 2)).mono fun i => by
    have := le_max_left (F i) (G i); have := le_max_right (F i) (G i); beta_reduce; omega
lemma pow (h : Small B F) (n : ℕ) : Small B (fun i => (F i)^n) :=
  let ⟨d, h⟩ := h; ⟨d*n, fun i => by rw [pow_mul]; exact Nat.pow_le_pow_left (h i) n⟩
lemma trans (h : Small B F) (g : Small C B) : Small C F :=
  let ⟨d, h⟩ := h; ((g.add (const C 2)).pow d).mono h
end Small
def Dom {ι : Type u} (W F : ι → ℕ) : Prop :=
  ∃ C : ℕ, ∀ i, F i+1 ≤ C*(W i+1)
namespace Dom
variable {ι : Type u} {W F G : ι → ℕ}
lemma of_le (h : ∀ i, F i ≤ W i) : Dom W F := ⟨1, fun i => by have := h i; omega⟩
lemma self (W : ι → ℕ) : Dom W W := of_le fun _ => le_rfl
lemma const (W : ι → ℕ) (n : ℕ) : Dom W (fun _ => n) := ⟨n+1, fun i => by ar⟩
lemma add (a : Dom W F) (b : Dom W G) : Dom W (fun i => F i + G i) := by
  obtain ⟨C, a⟩ := a; obtain ⟨D, b⟩ := b
  exact ⟨C+D, fun i => by have := a i; have := b i; rw [add_mul]; dsimp only; omega⟩
lemma trans (a : Dom W F) (b : Dom F G) : Dom W G := by
  obtain ⟨C, a⟩ := a; obtain ⟨D, b⟩ := b
  exact ⟨D*C, fun i => (b i).trans (by rw [mul_assoc]; exact Nat.mul_le_mul le_rfl (a i))⟩
lemma two (W : ι → ℕ) : Dom W (fun i => W i + W i) := (self W).add (self W)
end Dom
structure Bank (r : Port) (ι : Type U) where
  B : ι → ℕ
  ext : ι → ℕ
  use : ι → Handler r
section
variable {ι : Type U} {r : Port}
def Bank.cap (b : Bank r ι) (d : ℕ) (i : ι) : ℕ :=
  max ((b.B i+2)^d) (b.ext i)
def Bank.closed {ι : Type U} (B : ι → ℕ) : Bank none ι := ⟨B, fun _ => 0, fun _ => ()⟩
def Bank.comap {ι : Type U} {κ : Type V} (b : Bank r ι) (f : κ → ι) : Bank r κ :=
  ⟨fun i => b.B (f i), fun i => b.ext (f i), fun i => b.use (f i)⟩
def Able {r} {ι : Type U} (m : Bool) (b : Bank r ι) (s t)
    (x : ι → T s) (y : ι → T t) (W Z : ι → ℕ) : Prop :=
  ∃ (f : Code m r s t) (C d : ℕ), ∀ i,
    (f.run (b.use i) (x i)).OK (y i) (C*(W i+1)+Z i) (b.cap d i)
abbrev Can {ι : Type U} (m : Bool) (B : ι → ℕ) (s t)
    (x : ι → T s) (y : ι → T t) (W : ι → ℕ) : Prop :=
  Able m (Bank.closed B) s t x y W (fun _ => 0)
lemma Bank.cm (b : Bank r ι) {d e} (h : d ≤ e) (i : ι) : b.cap d i ≤ b.cap e i :=
  max_le ((Nat.pow_le_pow_right (by omega) h).trans (le_max_left _ _)) (le_max_right _ _)
lemma Bill.OK.up {γ} {c : Bill γ} {v : γ} {w d e} {b : Bank r ι} {i} (h : c.OK v w (b.cap d i))
    (hd : d ≤ e := by omega) : c.OK v w (b.cap e i) := h.mono le_rfl (b.cm hd i)
lemma Bank.le {b : Bank r ι} {i c d e} (h : c ≤ (b.B i+2)^d) (hd : d ≤ e := by omega) : c ≤ b.cap e i :=
  (h.trans (Nat.pow_le_pow_right (by omega) hd)).trans (le_max_left _ _)
end
structure During {ι : Type U} (n : ι → ℕ) where
  i : ι
  j : ℕ
  hj : j < n i
namespace Able
variable {ι : Type U} {κ : Type V} {r : Port} {m : Bool} {b : Bank r ι} {s t u : Ty}
  {x : ι → T s} {y : ι → T t} {z : ι → T u} {W W' Z Z' : ι → ℕ}
open Bill
lemma atom (op : Atom m s t) {d} (h : ∀ i, (op.run (x i)).OK (y i) 1 (b.cap d i)) : Able m b s t x y W Z :=
  ⟨.atom op, 1, d, fun i => (h i).mono (by ar) le_rfl⟩
lemma id : Able m b s s x x W Z := atom (d := 0) .id fun _ => one_ok _ _
section
variable (h : Able m b s t x y W Z)
include h
lemma reindex (f : κ → ι) : Able m (b.comap f) s t (fun i => x (f i)) (fun i => y (f i)) (fun i => W (f i)) (fun i => Z (f i)) :=
  let ⟨g, C, d, h⟩ := h; ⟨g, C, d, fun j => h (f j)⟩
lemma cong {x' y'} (hx : ∀ i, x i = x' i) (hy : ∀ i, y i = y' i) : Able m b s t x' y' W Z := by
  cases funext hx; cases funext hy; exact h
lemma weaken (hW : Dom W' W) (hZ : ∀ i, Z i ≤ Z' i) : Able m b s t x y W' Z' := by
  obtain ⟨f, C, d, h⟩ := h; obtain ⟨E, hE⟩ := hW
  exact ⟨f, C*E, d, fun i => (h i).mono (by
    rw [mul_assoc]; exact Nat.add_le_add (Nat.mul_le_mul le_rfl (hE i)) (hZ i)) le_rfl⟩
lemma mono (hW : ∀ i, W i ≤ W' i) (hZ : ∀ i, Z i ≤ Z' i) : Able m b s t x y W' Z' :=
  h.weaken (Dom.of_le hW) hZ
lemma comp (g : Able m b t u y z W' Z') : Able m b s u x z (fun i => W i + W' i) (fun i => Z i + Z' i) :=
  let ⟨f, C, d, h⟩ := h; let ⟨g, E, e, k⟩ := g
  ⟨.comp f g, C+E+1, d+e, fun i => .tick (.pass (h i).up (k i).up) (by simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]; omega)⟩
lemma fork (g : Able m b s u x z W' Z') : Able m b s (p t u) x (fun i => (y i,z i)) (fun i => W i+W' i) (fun i => Z i+Z' i) :=
  let ⟨f, C, d, h⟩ := h; let ⟨g, E, e, k⟩ := g
  ⟨.fork f g, C+E+1, d+e, fun i => .mono (.pass (h i).up (.pass (k i).up (one_ok _ _))) (by simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]; omega) le_rfl⟩
lemma save (g : Able m b (p s t) u (fun i => (x i,y i)) z W' Z') : Able m b s u x z (fun i => W i + W' i) (fun i => Z i + Z' i) :=
  ((fork (Able.id (W := fun _ => 0) (Z := fun _ => 0)) h).comp g).mono (fun _ => by simp) (fun _ => by simp)

lemma post (op : Atom m t u) (d : ℕ := 0) (g : ∀ i, (op.run (y i)).OK (z i) 1 (b.cap d i) := by exact fun _ => Bill.one_ok _ _) :
    Able m b s u x z W Z :=
  (h.comp (atom (W := fun _ => 0) (Z := fun _ => 0) op g)).mono (fun _ => by simp) fun _ => by simp
end
lemma use_call {b : Bank (some (s,t)) ι} (h : ∀ i, (b.use i (x i)).OK (y i) (Z i) (b.ext i)) : Able m b s t x y (fun _ => 0) Z :=
  ⟨.call, 1, 0, fun i => ((h i).tick (by ar)).mono le_rfl (le_max_right _ _)⟩
lemma of_can (h : Can m b.B s t x y W) : Able m b s t x y W (fun _ => 0) :=
  let ⟨f, C, d, h⟩ := h
  ⟨.importClosed f, C+1, d, fun i => ((h i).tick (by simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]; omega)).mono le_rfl (max_le (le_max_left _ _) (Nat.zero_le _))⟩
lemma ifz {n : ι → ℕ} (hx : Able m b s w x n W' Z') (hz : Able m (b.comap (fun i : {i // n i = 0} => i.val)) s t (fun i => x i.val) (fun i => y i.val) (fun i => W i.val) (fun i => Z i.val)) (hn : Able m (b.comap (fun i : {i // n i ≠ 0} => i.val)) s t (fun i => x i.val) (fun i => y i.val) (fun i => W i.val) (fun i => Z i.val)) : Able m b s t x y (fun i => W' i+W i) (fun i => Z' i+Z i) := by
  obtain ⟨q, C, d, hq⟩ := hx; obtain ⟨f, E, e, hf⟩ := hz; obtain ⟨g, F, k, hg⟩ := hn
  refine ⟨.ifz q f g, C+E+F+1, d+e+k, fun i => .tick (.pass (w' := (E+F)*(W i+1)+Z i) (hq i).up ?_) (by simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]; omega)⟩
  by_cases h0 : n i = 0
  · simp only [h0, ↓reduceIte]; exact (hf ⟨i, h0⟩).up.mono (by simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]; omega) le_rfl
  · simp only [h0, ↓reduceIte]; exact (hg ⟨i, h0⟩).up.mono (by simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]; omega) le_rfl
lemma loop {n : ι → ℕ} {v : ι → ℕ → T t} {Wb Zb : ι → ℕ → ℕ} (h : Able m b s w x n W Z) (hi : Able m b s t x (fun i => v i 0) W' Z') (hs : Able m (b.comap (During.i (n:=n))) (p s (p w t)) t (fun d => (x d.i,d.j,v d.i d.j)) (fun d => v d.i (d.j+1)) (fun d => Wb d.i d.j) (fun d => Zb d.i d.j)) (hc : Small b.B n) : Able m b s t x (fun i => v i (n i)) (fun i => W i + W' i + n i + ∑ j ∈ range (n i), Wb i j) (fun i => Z i + Z' i + ∑ j ∈ range (n i), Zb i j) :=
  let ⟨f, C, d, h⟩ := h; let ⟨g, E, e, hi⟩ := hi; let ⟨k, F, c₀, hs⟩ := hs; let ⟨q, hc⟩ := hc
  ⟨.loop f g k, C+E+F+3, d+e+c₀+q, fun i => .tick (.pass (h i).up (.pass (hi i).up
    (steps_ok (A := fun j => F*(Wb i j+1)+Zb i j) (Bank.le (hc i)) fun j hj => (hs ⟨i, j, hj⟩).up)))
    (by simp only [Bill.sc]; simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]; omega)⟩
lemma tab {n : ι → ℕ} {v : ι → ℕ → T t} {Wb Zb : ι → ℕ → ℕ} (h : Able m b s w x n W Z) (hs : Able m (b.comap (During.i (n:=n))) (p s w) t (fun d => (x d.i,d.j)) (fun d => v d.i d.j) (fun d => Wb d.i d.j) (fun d => Zb d.i d.j)) (hc : Small b.B n) : Able m b s (a t) x (fun i => Tape.tab (n i) (v i)) (fun i => W i + n i + ∑ j ∈ range (n i), Wb i j) (fun i => Z i + ∑ j ∈ range (n i), Zb i j) :=
  let ⟨f, C, d, h⟩ := h; let ⟨k, F, c₀, hs⟩ := hs; let ⟨q, hc⟩ := hc
  ⟨.tab f k, C+F+5, d+c₀+q, fun i => .tick (.pass (h i).up (tab_ok (fun j => F*(Wb i j+1)+Zb i j) _ _ _
    (Bank.le (hc i)) fun j hj => (hs ⟨i, j, hj⟩).up)) (by simp only [Bill.sc]; simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]; omega)⟩
lemma first {v : ι → T (p s t)} : Able m b (p s t) s v (fun i => (v i).1) W Z := atom (d := 0) .fst fun _ => one_ok _ _
lemma second {v : ι → T (p s t)} : Able m b (p s t) t v (fun i => (v i).2) W Z := atom (d := 0) .snd fun _ => one_ok _ _
lemma fst {v : ι → T (p t u)} (h : Able m b s (p t u) x v W Z) : Able m b s t x (fun i => (v i).1) W Z := h.post .fst
lemma snd {v : ι → T (p t u)} (h : Able m b s (p t u) x v W Z) : Able m b s u x (fun i => (v i).2) W Z := h.post .snd
lemma sow {n : ι → ℕ} {v : ι → ℕ → ℕ × T t} {len : ι → ℕ} {Wl Zl : ι → ℕ} {Wb Zb : ι → ℕ → ℕ} (hx : Able m b s w x len Wl Zl) (h : Able m b s w x n W Z) (hs : Able m (b.comap (During.i (n:=n))) (p s w) (p w t) (fun d => (x d.i,d.j)) (fun d => v d.i d.j) (fun d => Wb d.i d.j) (fun d => Zb d.i d.j)) (hg : Small b.B len) (hc : Small b.B n) : Able m b s (a t) x (fun i => Tape.sow (len i) (n i) t.blank (v i)) (fun i => Wl i + W i + len i + n i + ∑ j ∈ range (n i), Wb i j) (fun i => Zl i + Z i + ∑ j ∈ range (n i), Zb i j) :=
  let ⟨g, E, e, hl⟩ := hx; let ⟨f, C, d, h⟩ := h; let ⟨k, F, c₀, hs⟩ := hs; let ⟨q, hc⟩ := hc; let ⟨q', hg⟩ := hg
  ⟨.sow g f k, C+E+F+5, d+e+c₀+q+q', fun i => .tick (.pass (hl i).up (.pass (h i).up
    (sow_ok (fun j => F*(Wb i j+1)+Zb i j) _ (Bank.le (hg i)) (Bank.le (hc i)) fun j hj => (hs ⟨i, j, hj⟩).up)))
    (by simp only [Bill.sc]; simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]; omega)⟩
end Able
namespace Can
variable {ι : Type U} {κ : Type V} {m : Bool} {B B' : ι → ℕ} {s t u : Ty}
  {x : ι → T s} {y : ι → T t} {z : ι → T u} {W W' : ι → ℕ}
open Bill
section
variable (h : Can m B s t x y W)
include h
lemma unfold_bound : ∃ (f : Prog m s t) (C d : ℕ), ∀ i, (run f (x i)).OK (y i) (C*(W i+1)) ((B i+2)^d) :=
  let ⟨f, C, d, h⟩ := h
  ⟨f, C, d, fun i => (h i).mono (Nat.add_zero _).le (max_le le_rfl (Nat.zero_le _))⟩
lemma reindex (f : κ → ι) : Can m (fun j => B (f j)) s t (fun j => x (f j)) (fun j => y (f j)) (fun j => W (f j)) :=
  Able.reindex h f
lemma cong {x' y'} (hx : ∀ i, x i = x' i) (hy : ∀ i, y i = y' i) : Can m B s t x' y' W := Able.cong h hx hy
lemma weaken (h' : Dom W' W) : Can m B s t x y W' := Able.weaken h h' fun _ => le_rfl
lemma mono (h' : ∀ i, W i ≤ W' i) : Can m B s t x y W' := Able.mono h h' fun _ => le_rfl
lemma congr {y'} (hy : ∀ i, y i = y' i) : Can m B s t x y' W := Able.cong h (fun _ => rfl) hy
lemma ambient (h' : Small B' B) : Can m B' s t x y W := by
  obtain ⟨f, C, d, h⟩ := h; obtain ⟨e, he⟩ := (Small.poly B d).trans h'
  exact ⟨f, C, e, fun i => (h i).mono le_rfl (max_le ((he i).trans (le_max_left _ _)) (Nat.zero_le _))⟩
lemma pipe (g : Can m B t u y z W') : Can m B s u x z (fun i => W i+ W' i) := Able.comp h g
lemma then_do (g : Can m B t u y z W) : Can m B s u x z W := weaken (pipe h g) (Dom.two W)
lemma fork (g : Can m B s u x z W') : Can m B s (p t u) x (fun i => (y i,z i)) (fun i => W i+W' i) := Able.fork h g
lemma pair (g : Can m B s u x z W) : Can m B s (p t u) x (fun i => (y i,z i)) W := weaken (fork h g) (Dom.two W)
lemma save (g : Can m B (p s t) u (fun i => (x i,y i)) z W') : Can m B s u x z (fun i => W i+ W' i) := Able.save h g
lemma bind (g : Can m B (p s t) u (fun i => (x i,y i)) z W) : Can m B s u x z W := weaken (save h g) (Dom.two W)
end
lemma id : Can m B s s x x W := Able.id
lemma first {v : ι → T (p s t)} : Can m B (p s t) s v (fun i => (v i).1) W := Able.first
lemma second {v : ι → T (p s t)} : Can m B (p s t) t v (fun i => (v i).2) W := Able.second
lemma fst {v : ι → T (p t u)} (h : Can m B s (p t u) x v W) : Can m B s t x (fun i => (v i).1) W := Able.fst h
lemma snd {v : ι → T (p t u)} (h : Can m B s (p t u) x v W) : Can m B s u x (fun i => (v i).2) W := Able.snd h
lemma wc (n : ℕ) : Can m B s w x (fun _ => n) W :=
  let ⟨d, h⟩ := Small.const B n; Able.atom (d := d) (.lit n) fun i => ⟨rfl, le_rfl, (h i).trans (le_max_left _ _), trivial⟩
lemma zero {cl} : Can m B s (c cl) x (fun _ => 0) W := Able.atom (d := 0) (.cz cl) fun _ => one_ok _ _
lemma one : Can m B s sc x (fun _ => 1) W := Able.atom (d := 0) .cone fun _ => one_ok _ _
section
variable {cl : Paint} {f g : ι → ℂ}
lemma add (h : Can m B s (c cl) x f W) (k : Can m B s (c cl) x g W) : Can m B s (c cl) x (fun i => f i + g i) W :=
  Able.post (pair h k) (.add cl)
lemma sub (h : Can m B s (c cl) x f W) (k : Can m B s (c cl) x g W) : Can m B s (c cl) x (fun i => f i - g i) W :=
  Able.post (pair h k) (.sub cl)
lemma mul (h : Can m B s sc x f W) (k : Can m B s (c cl) x g W) : Can m B s (c cl) x (fun i => f i * g i) W :=
  Able.post (pair h k) (.scale cl)
lemma cross (h : Can true B s (c .left) x f W) (k : Can true B s (c .right) x g W) : Can true B s (c .both) x (fun i => f i * g i) W :=
  Able.post (pair h k) (.cross rfl)
lemma inv (h : Can m B s sc x f W) (k : ∀ i, f i ≠ 0) : Can m B s sc x (fun i => (f i)⁻¹) W :=
  Able.post h .inv 0 fun i => ⟨rfl, le_rfl, Nat.zero_le _, k i⟩
variable {n q : ι → ℕ} {v : ι → Tape (T t)}
lemma look (h : Can m B s (a t) x v W) (k : Can m B s w x n W) : Can m B s t x (fun i => (v i).look (n i) t.blank) W :=
  Able.post (pair h k) .look
lemma len (h : Can m B s (a t) x v W) (k : Small B fun i => (v i).len) : Can m B s w x (fun i => (v i).len) W :=
  let ⟨d, hd⟩ := k
  Able.post h .len d fun i => ⟨rfl, le_rfl, (hd i).trans (le_max_left _ _), trivial⟩
lemma word2 {F : ι → ℕ} (h : Can m B s w x n W) (k : Can m B s w x q W) (o : NOp)
    (hb : Small B F) (ho : ∀ i, (@Atom.int m o).run (n i, q i) = Bill.word (F i) := by exact fun _ => rfl) : Can m B s w x F W := by
  obtain ⟨d, hd⟩ := hb
  exact Able.post (pair h k) (.int o) d fun i => by rw [ho i]; exact ⟨rfl, le_rfl, (hd i).trans (le_max_left _ _), trivial⟩
section
variable (h : Can m B s w x n W) (k : Can m B s w x q W)
include h k
lemma wadd (hb : Small B (fun i => n i + q i)) : Can m B s w x (fun i => n i + q i) W := word2 h k .add hb
lemma wsub (hb : Small B (fun i => n i - q i)) : Can m B s w x (fun i => n i - q i) W := word2 h k .sub hb
lemma wmul (hb : Small B (fun i => n i * q i)) : Can m B s w x (fun i => n i * q i) W := word2 h k .mul hb
lemma wdiv (hb : Small B (fun i => n i / q i)) : Can m B s w x (fun i => n i / q i) W := word2 h k .div hb
lemma wmod (hb : Small B (fun i => n i % q i)) : Can m B s w x (fun i => n i % q i) W := word2 h k .mod hb
lemma wlt : Can m B s w x (fun i => if n i < q i then 1 else 0) W :=
  word2 h k .lt ((Small.const B 1).mono fun _ => by split <;> omega)
end
lemma testz (h : Can m B s w x n W) (g : Can m (fun i : {i // n i = 0} => B i.val) s t (fun i => x i.val) (fun i => y i.val) (fun i => W i.val)) (j : Can m (fun i : {i // n i ≠ 0} => B i.val) s t (fun i => x i.val) (fun i => y i.val) (fun i => W i.val)) : Can m B s t x y W :=
  Able.weaken (Able.ifz (Z := fun _ => 0) h g j) (Dom.two W) fun _ => le_rfl
lemma branch {n : ι → ℕ} {y₁ y₂ : ι → T t} (h : Can m B s w x n W) (g : Can m B s t x y₁ W) (j : Can m B s t x y₂ W) :
    Can m B s t x (fun i => if n i=0 then y₁ i else y₂ i) W :=
  testz h ((g.reindex Subtype.val).congr fun i => (if_pos i.2).symm) ((j.reindex Subtype.val).congr fun i => (if_neg i.2).symm)
lemma anyCost {V : ι → ℕ} (h : Can m B s t x y (fun _ => 0)) : Can m B s t x y V := mono h fun _ => Nat.zero_le _
lemma pick {n k : ι → ℕ} (v : ι → ℕ → T t) (h : Can m B s (a t) x (fun i => Tape.tab (n i) (v i)) W) (g : Can m B s w x k W) (hh : ∀ i, k i<n i) : Can m B s t x (fun i => v i (k i)) W :=
  (look h g).congr fun i => by simp [Tape.look_tab, hh i]
variable {uB : ι → ℕ → ℕ}
lemma loop {v : ι → ℕ → T t} (h : Can m B s w x n W) (hi : Can m B s t x (fun i => v i 0) W') (hs : Can m (fun d : During n => B d.i) (p s (p w t)) t (fun d => (x d.i,d.j,v d.i d.j)) (fun d => v d.i (d.j+1)) (fun d => uB d.i d.j)) (hc : Small B n) : Can m B s t x (fun i => v i (n i)) (fun i => W i + W' i + n i + ∑ j ∈ range (n i), uB i j) :=
  Able.mono (Able.loop (Wb := uB) (Zb := fun _ _ => 0) h hi hs hc) (fun _ => le_rfl) fun _ => by simp
lemma tab {v : ι → ℕ → T t} (h : Can m B s w x n W) (hs : Can m (fun d : During n => B d.i) (p s w) t (fun d => (x d.i,d.j)) (fun d => v d.i d.j) (fun d => uB d.i d.j)) (hc : Small B n) : Can m B s (a t) x (fun i => Tape.tab (n i) (v i)) (fun i => W i + n i + ∑ j ∈ range (n i), uB i j) :=
  Able.mono (Able.tab (Wb := uB) (Zb := fun _ _ => 0) h hs hc) (fun _ => le_rfl) fun _ => by simp
lemma sow {v : ι → ℕ → ℕ × T t} (hl : Can m B s w x q W') (h : Can m B s w x n W) (hs : Can m (fun d : During n => B d.i) (p s w) (p w t) (fun d => (x d.i,d.j)) (fun d => v d.i d.j) (fun d => uB d.i d.j)) (hg : Small B q) (hc : Small B n) : Can m B s (a t) x (fun i => Tape.sow (q i) (n i) t.blank (v i)) (fun i => W' i + W i + q i + n i + ∑ j ∈ range (n i), uB i j) :=
  Able.mono (Able.sow (Wb := uB) (Zb := fun _ _ => 0) hl h hs hg hc) (fun _ => le_rfl) fun _ => by simp
end
end Can
/-- `Can` at some degree `d` of a cost family `F d` (polynomial costs, budget costs); the lemmas that
need `F` to grow with `d` take that as a hypothesis `hF`. -/
def Can.Within {ι : Type U} (m : Bool) (B : ι → ℕ) (F : ℕ → ι → ℕ) (s t) (x : ι → T s) (y : ι → T t) : Prop :=
  ∃ d : ℕ, Can m B s t x y (F d)
namespace Can.Within
variable {ι : Type U} {m : Bool} {B : ι → ℕ} {F : ℕ → ι → ℕ} {s t : Ty} {x : ι → T s} {y : ι → T t}
lemma of_can {W : ι → ℕ} (h : Can m B s t x y W) (g : ∃ d, ∀ i, W i ≤ F d i) : Within m B F s t x y :=
  let ⟨d, g⟩ := g; ⟨d, Can.mono h g⟩
variable (hF : ∀ {d e : ℕ}, d ≤ e → ∀ i, F d i ≤ F e i)
include hF
lemma lift2 {s₁ t₁ s₂ t₂ x₁ y₁ x₂ y₂} (h : Within m B F s t x y) (g : Within m B F s₁ t₁ x₁ y₁)
    (R : ∀ {W}, Can m B s t x y W → Can m B s₁ t₁ x₁ y₁ W → Can m B s₂ t₂ x₂ y₂ W) : Within m B F s₂ t₂ x₂ y₂ :=
  let ⟨d, h⟩ := h; let ⟨e, g⟩ := g
  ⟨d+e, R (Can.mono h (hF (Nat.le_add_right _ _))) (Can.mono g (hF (Nat.le_add_left _ _)))⟩
lemma testz {n : ι → ℕ} (h : Within m B F s w x n)
    (g : Within m (fun i : {i // n i = 0} => B i.val) (fun d i => F d i.val) s t (fun i => x i.val) (fun i => y i.val))
    (j : Within m (fun i : {i // n i ≠ 0} => B i.val) (fun d i => F d i.val) s t (fun i => x i.val) (fun i => y i.val)) :
    Within m B F s t x y :=
  let ⟨d, h⟩ := h; let ⟨e, g⟩ := g; let ⟨k, j⟩ := j
  ⟨d+e+k, Can.testz (Can.mono h (hF (by omega))) (Can.mono g fun i => hF (by omega) i.val)
    (Can.mono j fun i => hF (by omega) i.val)⟩
end Can.Within
def PolyCan {ι : Type U} (m : Bool) (B S : ι → ℕ) (s t) (x : ι → T s) (y : ι → T t) : Prop :=
  Can.Within m B (fun d i => (S i+2)^d) s t x y
namespace PolyCan
variable {ι : Type U} {κ : Type V} {m : Bool} {B B' S S' : ι → ℕ} {s t u : Ty}
  {x : ι → T s} {y : ι → T t} {z : ι → T u} {W : ι → ℕ}
lemma up {S : ι → ℕ} {d e : ℕ} (h : Can m B s t x y (fun i => (S i+2)^d)) (hde : d ≤ e) : Can m B s t x y (fun i => (S i+2)^e) :=
  Can.mono h fun i => Small.pow_mono_degree (S i) hde
lemma lift2 {s₁ t₁ s₂ t₂ x₁ y₁ x₂ y₂} (h : PolyCan m B S s t x y) (g : PolyCan m B S s₁ t₁ x₁ y₁)
    (F : ∀ {W}, Can m B s t x y W → Can m B s₁ t₁ x₁ y₁ W → Can m B s₂ t₂ x₂ y₂ W) : PolyCan m B S s₂ t₂ x₂ y₂ :=
  Can.Within.lift2 (fun h i => Small.pow_mono_degree (S i) h) h g F
lemma of_can (h : Can m B s t x y W) (g : Small S W) : PolyCan m B S s t x y := Can.Within.of_can h g
section
variable (h : PolyCan m B S s t x y)
include h
lemma cong {x' y'} (hx : ∀ i, x i = x' i) (hy : ∀ i, y i = y' i) : PolyCan m B S s t x' y' :=
  let ⟨d, h⟩ := h; ⟨d, Can.cong h hx hy⟩
lemma reindex (f : κ → ι) : PolyCan m (fun j => B (f j)) (fun j => S (f j)) s t (fun j => x (f j)) (fun j => y (f j)) :=
  let ⟨d, h⟩ := h; ⟨d, Can.reindex h f⟩
lemma weaken (a : Small B' B) (b : Small S' S) : PolyCan m B' S' s t x y :=
  let ⟨d, h⟩ := h; of_can (Can.ambient h a) ((Small.poly S d).trans b)
lemma pipe (g : PolyCan m B S t u y z) : PolyCan m B S s u x z := lift2 h g Can.then_do
lemma pair (g : PolyCan m B S s u x z) : PolyCan m B S s (p t u) x (fun i => (y i,z i)) := lift2 h g Can.pair
end
lemma fst {v : ι → T (p t u)} (h : PolyCan m B S s (p t u) x v) : PolyCan m B S s t x (fun i => (v i).1) := let ⟨d, h⟩ := h; ⟨d, Can.fst h⟩
lemma snd {v : ι → T (p t u)} (h : PolyCan m B S s (p t u) x v) : PolyCan m B S s u x (fun i => (v i).2) := let ⟨d, h⟩ := h; ⟨d, Can.snd h⟩
lemma second {x : ι → T (p t u)} : PolyCan m B S (p t u) u x (fun i => (x i).2) := ⟨0, Can.second⟩
lemma id : PolyCan m B S s s x x := ⟨0, Can.id⟩
lemma first {x : ι → T (p t u)} : PolyCan m B S (p t u) t x (fun i => (x i).1) := ⟨0, Can.first⟩
lemma wc (n : ℕ) : PolyCan m B S s w x (fun _ => n) := ⟨0, Can.wc n⟩
lemma zero {cl} : PolyCan m B S s (c cl) x (fun _ => 0) := ⟨0, Can.zero⟩
lemma one : PolyCan m B S s sc x (fun _ => 1) := ⟨0, Can.one⟩
section
variable {cl : Paint} {f g : ι → ℂ}
lemma mul (h : PolyCan m B S s sc x f) (k : PolyCan m B S s (c cl) x g) : PolyCan m B S s (c cl) x (fun i => f i * g i) := lift2 h k Can.mul
lemma sub (h : PolyCan m B S s (c cl) x f) (k : PolyCan m B S s (c cl) x g) : PolyCan m B S s (c cl) x (fun i => f i - g i) := lift2 h k Can.sub
lemma add (h : PolyCan m B S s (c cl) x f) (k : PolyCan m B S s (c cl) x g) : PolyCan m B S s (c cl) x (fun i => f i + g i) := lift2 h k Can.add
lemma inv (h : PolyCan m B S s sc x f) (hk : ∀ i, f i ≠ 0) : PolyCan m B S s sc x (fun i => (f i)⁻¹) := let ⟨d, h⟩ := h; ⟨d, Can.inv h hk⟩
variable {n q : ι → ℕ} {v : ι → Tape (T t)}
lemma wsub (h : PolyCan m B S s w x n) (k : PolyCan m B S s w x q) (hb : Small B (fun i => n i - q i)) : PolyCan m B S s w x (fun i => n i - q i) := lift2 h k (Can.wsub · · hb)
lemma look (h : PolyCan m B S s (a t) x v) (k : PolyCan m B S s w x n) : PolyCan m B S s t x (fun i => (v i).look (n i) t.blank) := lift2 h k Can.look
section
variable (h : PolyCan m B S s w x n) (k : PolyCan m B S s w x q)
include h k
lemma wadd (hb : Small B (fun i => n i + q i)) : PolyCan m B S s w x (fun i => n i + q i) := lift2 h k (Can.wadd · · hb)
lemma wmul (hb : Small B (fun i => n i * q i)) : PolyCan m B S s w x (fun i => n i * q i) := lift2 h k (Can.wmul · · hb)
lemma wdiv (hb : Small B (fun i => n i / q i)) : PolyCan m B S s w x (fun i => n i / q i) := lift2 h k (Can.wdiv · · hb)
lemma wmod (hb : Small B (fun i => n i % q i)) : PolyCan m B S s w x (fun i => n i % q i) := lift2 h k (Can.wmod · · hb)
lemma wlt : PolyCan m B S s w x (fun i => if n i < q i then 1 else 0) := lift2 h k Can.wlt
end
lemma loop {v : ι → ℕ → T t} (h : PolyCan m B S s w x n) (hi : PolyCan m B S s t x (fun i => v i 0)) (hs : PolyCan m (fun d : During n => B d.i) (fun d => S d.i) (p s (p w t)) t (fun d => (x d.i,d.j,v d.i d.j)) (fun d => v d.i (d.j+1))) (hc : Small B n) (hd : Small S n) : PolyCan m B S s t x (fun i => v i (n i)) :=
  let ⟨d, h⟩ := h; let ⟨e, hi⟩ := hi; let ⟨k, hs⟩ := hs
  of_can (Can.loop (uB := fun i _ => (S i+2)^k) h hi hs hc)
    ((((Small.poly S d).add (Small.poly S e)).add hd).add ((hd.mul (Small.poly S k)).mono fun _ => (sum_const' _ _).le))
lemma tab {v : ι → ℕ → T t} (h : PolyCan m B S s w x n) (hs : PolyCan m (fun d : During n => B d.i) (fun d => S d.i) (p s w) t (fun d => (x d.i,d.j)) (fun d => v d.i d.j)) (hc : Small B n) (hd : Small S n) : PolyCan m B S s (a t) x (fun i => Tape.tab (n i) (v i)) :=
  let ⟨d, h⟩ := h; let ⟨k, hs⟩ := hs
  of_can (Can.tab (uB := fun i _ => (S i+2)^k) h hs hc) (((Small.poly S d).add hd).add ((hd.mul (Small.poly S k)).mono fun _ => (sum_const' _ _).le))
lemma testz (h : PolyCan m B S s w x n) (g : PolyCan m (fun i : {i // n i = 0} => B i.val) (fun i => S i.val) s t (fun i => x i.val) (fun i => y i.val)) (j : PolyCan m (fun i : {i // n i ≠ 0} => B i.val) (fun i => S i.val) s t (fun i => x i.val) (fun i => y i.val)) : PolyCan m B S s t x y :=
  Can.Within.testz (fun h i => Small.pow_mono_degree (S i) h) h g j
lemma congr {y'} (h : PolyCan m B S s t x y) (H : ∀ i, y i = y' i) : PolyCan m B S s t x y' := h.cong (fun _ => rfl) H
lemma neg {cl} {f : ι → ℂ} (h : PolyCan m B S s (c cl) x f) : PolyCan m B S s (c cl) x (fun i => -f i) :=
  (sub zero h).congr fun _ => zero_sub _
lemma branch {n : ι → ℕ} {y₁ y₂ : ι → T t} (h : PolyCan m B S s w x n) (g : PolyCan m B S s t x y₁) (j : PolyCan m B S s t x y₂) :
    PolyCan m B S s t x (fun i => if n i = 0 then y₁ i else y₂ i) :=
  lift2 h (pair g j) fun u v => Can.branch u (Can.fst v) (Can.snd v)
lemma pick {n k : ι→ℕ} (v : ι→ℕ→T t) (h : PolyCan m B S s (a t) x fun i => Tape.tab (n i) (v i)) (g : PolyCan m B S s w x k) (hk : ∀ i,k i<n i) : PolyCan m B S s t x fun i => v i (k i) :=
  lift2 h g (Can.pick v · · hk)
end
end PolyCan
lemma Can.toPoly {ι : Type U} {m B s t x y} (h : @Can ι m B s t x y fun _ => 0) (S : ι → ℕ) : PolyCan m B S s t x y := ⟨0, h.anyCost⟩
end RAM
end PowerSaving
end OAI
namespace OAI.PowerSaving.RAM
open Ty
/-- A placeholder program of any shape: zero literals and zero scalars, assembled along the
output type; it never calls the port, so it also serves as the base of `descend`. -/
def Code.inert {m : Bool} {r : Port} : (s t : Ty) → Code m r s t
  | _, w => .atom (.lit 0)
  | _, c q => .atom (.cz q)
  | s, p t₁ t₂ => .fork (Code.inert s t₁) (Code.inert s t₂)
  | s, a t₁ => .tab (.atom (.lit 0)) (Code.inert (p s w) t₁)
end OAI.PowerSaving.RAM

end
-- ===== end part 1 =====

-- ===== begin part 2: digit arithmetic, layouts, layout programs, benches =====
section
--might be  containing modified Apache-2.0 codes pieces from one or several sources; notices and credits: Credits.lean

namespace OAI.PowerSaving.DigitArith

theorem div_join {a b n : Nat} (hb : b < n) : (a * n + b) / n = a := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) hb
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hb, Nat.zero_add]

theorem mod_join {a b n : Nat} (hb : b < n) : (a * n + b) % n = b := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]

theorem lt_join {a b m n : Nat} (h : a < m) (g : b < n) : a * n + b < m * n :=
  Nat.lt_of_lt_of_le (Nat.add_lt_add_left g _) (by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ h)

theorem div_join' {a b n : Nat} (hb : b < n) : (b + n * a) / n = a := by
  rw [Nat.mul_comm, Nat.add_comm]; exact div_join hb

theorem mod_join' {a b n : Nat} (hb : b < n) : (b + n * a) % n = b := by
  rw [Nat.mul_comm, Nat.add_comm]; exact mod_join hb

theorem split3_eq (a b c P Q : Nat) : a + P * b + P * Q * c = a + P * (b + Q * c) := by
  rw [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

theorem split3_mod {a b c P Q : Nat} (ha : a < P) : (a + P * b + P * Q * c) % P = a := by
  rw [split3_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]

theorem split3_mid {a b c P Q : Nat} (ha : a < P) (hb : b < Q) :
    (a + P * b + P * Q * c) / P % Q = b := by
  have hP : 0 < P := Nat.lt_of_le_of_lt (Nat.zero_le _) ha
  rw [split3_eq, Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt ha, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]

end OAI.PowerSaving.DigitArith

end

section
--might be  containing modified Apache-2.0 codes pieces from one or several sources; notices and credits: Credits.lean
namespace OAI.PowerSaving
open Finset
structure Layout (α : Type*) where
  n : ℕ
  loc : α → ℕ
  bd : ∀ i, loc i < n
  inj : Function.Injective loc
  onto : ∀ j : Fin n, ∃ i, loc i = j.val
namespace Layout
variable {α β μ : Type*}
noncomputable def atFin (L : Layout α) (j : Fin L.n) : α := Classical.choose (L.onto j)
@[simp] lemma loc_atFin (L : Layout α) (j : Fin L.n) : L.loc (L.atFin j) = j.val := Classical.choose_spec (L.onto j)
def toIx (L : Layout α) (i : α) : Fin L.n := ⟨L.loc i,L.bd i⟩
noncomputable def index (L : Layout α) : α ≃ Fin L.n :=
  ⟨L.toIx,L.atFin,fun _ => L.inj (L.loc_atFin _),fun j => Fin.ext (L.loc_atFin j)⟩
noncomputable def tape (L : Layout α) (x : α → μ) : Tape μ :=
  ⟨L.n, fun j => x (L.atFin j)⟩
@[simp] lemma read (L : Layout α) (x : α → μ) (i : α) (z : μ) : (L.tape x).look (L.loc i) z = x i := by
  rw [Tape.look_of_lt (L.tape x) z (L.bd i)]; exact congrArg x (L.inj (L.loc_atFin _))
def std (n : ℕ) : Layout (Fin n) :=
  ⟨n,Fin.val, Fin.isLt, fun _ _ => Fin.ext, fun j => ⟨j, rfl⟩⟩
lemma card [Fintype α] (X : Layout α) : Fintype.card α = X.n :=
  (Fintype.card_congr X.index).trans (Fintype.card_fin _)
def comap (L : Layout α) (f : β ≃ α) : Layout β where
  n := L.n
  loc := fun j => L.loc (f j)
  bd := fun j => L.bd (f j)
  inj := fun _ _ h => f.injective (L.inj h)
  onto j := (L.onto j).elim fun i hi => ⟨f.symm i, (congrArg L.loc (f.apply_symm_apply i)).trans hi⟩
noncomputable def someLayout (α : Type*) [Fintype α] : Layout α :=
  (std _).comap (Fintype.equivFin α)
open DigitArith in
def pair (X : Layout α) (Y : Layout β) : Layout (α × β) where
  n := X.n * Y.n
  loc := fun i => X.loc i.1*Y.n + Y.loc i.2
  bd i := lt_join (X.bd i.1) (Y.bd i.2)
  inj a b h := Prod.ext (X.inj ((div_join (Y.bd a.2)).symm.trans ((congrArg (· / Y.n) h).trans (div_join (Y.bd b.2)))))
    (Y.inj ((mod_join (Y.bd a.2)).symm.trans ((congrArg (· % Y.n) h).trans (mod_join (Y.bd b.2)))))
  onto j := by
    have hy := Nat.pos_of_mul_pos_left (Nat.zero_lt_of_lt j.2)
    obtain ⟨a, ha⟩ := X.onto ⟨j / Y.n, (Nat.div_lt_iff_lt_mul hy).2 j.2⟩
    obtain ⟨b, hb⟩ := Y.onto ⟨j % Y.n, Nat.mod_lt _ hy⟩
    exact ⟨(a,b), by rw [ha, hb]; exact Nat.div_add_mod' _ _⟩
@[simp] lemma pair_len (X : Layout α) (Y : Layout β) : (X.pair Y).n = X.n * Y.n := rfl
lemma pair_div (X : Layout α) (Y : Layout β) (i) : (X.pair Y).loc i / Y.n = X.loc i.1 := DigitArith.div_join (Y.bd _)
lemma pair_mod (X : Layout α) (Y : Layout β) (i) : (X.pair Y).loc i % Y.n = Y.loc i.2 := DigitArith.mod_join (Y.bd _)
def permFn (e : α ≃ β) (μ : Type*) : (α → μ) ≃ (β → μ) where
  toFun f := f ∘ e.symm
  invFun f := f ∘ e
  left_inv f := funext fun x => congrArg f (e.symm_apply_apply x)
  right_inv f := funext fun x => congrArg f (e.apply_symm_apply x)
lemma vec_code (X : Layout α) (k : ℕ) (x : Fin k → α) :
    ∑ i, X.loc (x i)*X.n^i.val = finFunctionFinEquiv (fun i => X.toIx (x i)) := by
  rw [finFunctionFinEquiv_apply]; try rfl
def vecFin (X : Layout α) (k : ℕ) : Layout (Fin k → α) where
  n := X.n^k
  loc := fun x => ∑ i, X.loc (x i)*X.n^i.val
  bd x := by show ∑ i, X.loc (x i)*X.n^i.val < X.n^k; rw [vec_code]; exact Fin.isLt _
  inj a b h := funext fun i => X.inj (congrArg Fin.val (congrFun (finFunctionFinEquiv.injective
    (Fin.ext (by rw [← vec_code, ← vec_code]; exact h) :
      finFunctionFinEquiv (fun i => X.toIx (a i)) = finFunctionFinEquiv fun i => X.toIx (b i))) i))
  onto j := ⟨fun i => X.atFin (finFunctionFinEquiv.symm j i), by
    show ∑ i : Fin k, X.loc (X.atFin _) * X.n^i.val = j.val
    simp only [loc_atFin]; rw [← finFunctionFinEquiv_apply, Equiv.apply_symm_apply]⟩
noncomputable def digits (J : Layout β) (X : Layout α) : Layout (β → α) :=
  (vecFin X J.n).comap (permFn J.index α)
lemma digits_code [Fintype β] (J : Layout β) (X : Layout α) (x : β→α) : (digits J X).loc x = ∑ j, X.loc (x j)*X.n^(J.loc j) := by
  show ∑ i, X.loc (x (J.index.symm i)) * X.n^i.val = _
  exact (Fintype.sum_equiv J.index _ _ fun j => by
    first | (simp only [Equiv.symm_apply_apply]; done) | (simp only [Equiv.symm_apply_apply]; rfl)).symm
lemma digits_entry (J : Layout β) (X : Layout α) (x : β→α) (j : β) : (digits J X).loc x / X.n^(J.loc j) % X.n=X.loc (x j) := by
  have h := finFunctionFinEquiv_symm_apply_val (finFunctionFinEquiv fun i => X.toIx (x (J.index.symm i))) (J.index j)
  rw [Equiv.symm_apply_apply, ← vec_code] at h
  exact h.symm.trans (congrArg X.loc (congrArg x (J.index.symm_apply_apply j)))
end Layout
end OAI.PowerSaving
end

section
--might be  containing modified Apache-2.0 codes pieces from one or several sources; notices and credits: Credits.lean
namespace OAI.PowerSaving
open Finset
namespace RAM
open Ty
noncomputable section
universe U V Z
section
variable {ι : Type U} {α : ι → Type V}
namespace Able
variable {m : Bool} {r : Port} {b : Bank r ι} {s t : Ty}
  {x : ι → T s} {W Z P H : ι → ℕ}
lemma layout {L : ∀ i, Layout (α i)} {v : ∀ i, α i → T t} (h : Able m b s w x (fun i => (L i).n) W Z) (hs : Able m (b.comap (Sigma.fst (β:=α))) (p s w) t (fun d => (x d.1,(L d.1).loc d.2)) (fun d => v d.1 d.2) (fun d => P d.1) (fun d => H d.1)) (hc : Small b.B fun i => (L i).n) : Able m b s (a t) x (fun i => (L i).tape (v i)) (fun i => W i+(L i).n+(L i).n*P i) (fun i => Z i+(L i).n*H i) := by
  have := Able.tab (v := fun i j => if hj : j < (L i).n then v i ((L i).atFin ⟨j, hj⟩) else t.blank)
    (Wb := fun i _ => P i) (Zb := fun i _ => H i) h
    ((Able.reindex hs fun d : During (fun i => (L i).n) => (⟨d.i, (L d.i).atFin ⟨d.j, d.hj⟩⟩ : Σ i, α i)).cong
      (fun _ => by simp) fun d => by simp [d.hj]) hc
  exact (this.cong (fun _ => rfl) fun i => congrArg (Tape.mk _) (funext fun j => dif_pos j.2)).mono
    (fun _ => by simp) fun _ => by simp
end Able
namespace Small
lemma loc {B : ι → ℕ} {x : ∀ i, α i} {L : ∀ i, Layout (α i)} (h : Small B fun i => (L i).n) : Small B fun i => (L i).loc (x i) :=
  h.mono fun i => ((L i).bd _).le
end Small
namespace Can
variable {m : Bool} {s t : Ty} {x : ι → T s}
  {B W P : ι → ℕ} {L : ∀ i, Layout (α i)} {v : ∀ i, α i → T t}
lemma layout (h : Can m B s w x (fun i => (L i).n) W) (g : Can m (fun d : Σ i, α i => B d.1) (p s w) t (fun d => (x d.1,(L d.1).loc d.2)) (fun d => v d.1 d.2) (fun d => P d.1)) (hn : Small B fun i => (L i).n) : Can m B s (a t) x (fun i => (L i).tape (v i)) (fun i => W i+(L i).n+(L i).n*P i) :=
  Able.mono (Able.layout (P := P) (H := fun _ => 0) h g hn) (fun _ => le_rfl) fun _ => by simp
lemma fetch {i : ∀ d, α d} (h : Can m B s (a t) x (fun i => (L i).tape (v i)) W) (g : Can m B s w x (fun d => (L d).loc (i d)) W) : Can m B s t x (fun d => v d (i d)) W :=
  (look h g).congr fun d => Layout.read _ _ _ _
variable {μ : Type V}
lemma eqbit {n q : ι → ℕ} (h : Can m B s w x n W) (k : Can m B s w x q W) : Can m B s w x (fun i => if n i = q i then 0 else 1) W :=
  (wadd (wlt h k) (wlt k h) ((Small.const B 2).mono fun _ => by split_ifs <;> omega)).congr fun i => by
    rcases lt_trichotomy (n i) (q i) with e | e | e
    · simp [e, e.ne, Nat.lt_asymm e]
    · simp [e]
    · simp [e, e.ne', Nat.lt_asymm e]
lemma cases_code [DecidableEq μ] [Fintype μ] {y : ι → T t} {q : ι→μ} (D : Layout μ) (h : Can m B s w x (fun i => D.loc (q i)) W) (g : ∀ f : μ, Can m (fun i : {i // q i=f} => B i.1) s t (fun i => x i.1) (fun i => y i.1) (fun i => W i.1)) : Can m B s t x y W := by
  suffices ∀ k {κ : Type U} (e : κ → ι), (∀ j, D.loc (q (e j)) < k) →
      Can m (fun j => B (e j)) s t (fun j => x (e j)) (fun j => y (e j)) (fun j => W (e j)) from
    this D.n (·) fun _ => D.bd _
  intro k; induction k with
  | zero => exact fun _ hk => ⟨Code.inert s t, 0, 0, fun j => absurd (hk j) (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro κ e hk
    refine testz (eqbit (reindex h e) (wc k)) ?_ (ih (fun j : Subtype _ => e j.1) fun j => ?_)
    · by_cases hn : k < D.n
      · exact reindex (g (D.atFin ⟨k, hn⟩)) fun j : Subtype _ =>
          ⟨e j.1, D.inj ((by simpa using j.2 : D.loc (q (e j.1)) = k).trans (D.loc_atFin ⟨k, hn⟩).symm)⟩
      · exact ⟨Code.inert s t, 0, 0, fun j => absurd (by
          have : D.loc (q (e j.1)) = k := (by simpa using j.2); have := D.bd (q (e j.1)); omega) hn⟩
    · have h1 : D.loc (q (e j.1)) ≠ k := fun h' => j.2 (by simp [h'])
      have := hk j.1; show D.loc (q (e j.1)) < k; omega
lemma sumP {X} [AddCommMonoid X] (P : (ι → X) → Prop) {v : μ → ι → X} (h : ∀ i, P (v i))
    (z : P fun _ => 0) (ad : ∀ {f g}, P f → P g → P fun j => f j + g j) (S : Finset μ) : P fun j => ∑ i ∈ S, v i j := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using z
  | insert a S ha ih => simpa [sum_insert ha] using ad (h a) ih
lemma sum_wconst [Fintype μ] {v : μ → ι → ℕ} (h : ∀ i : μ, Can m B s w x (v i) W) (g : ∀ i : μ, Small B (v i)) : Can m B s w x (fun j => ∑ i, v i j) W :=
  (sumP (fun f => Can m B s w x f W ∧ Small B f) (fun i => ⟨h i, g i⟩) ⟨wc 0, Small.const B 0⟩
    (fun a b => ⟨wadd a.1 b.1 (a.2.add b.2), a.2.add b.2⟩) univ).1
lemma sum_cconst [Fintype μ] {cl} {v : μ → ι → ℂ} (h : ∀ i : μ, Can m B s (c cl) x (v i) W) : Can m B s (c cl) x (fun j => ∑ i, v i j) W :=
  sumP (fun f => Can m B s (c cl) x f W) h zero add univ
end Can
end
lemma log_step (A j : ℕ) : (A/2^j/2, Nat.log 2 A - Nat.log 2 (A/2^j) + (if 1 < A/2^j then 1 else 0)) =
    (A/2^(j+1), Nat.log 2 A - Nat.log 2 (A/2^(j+1))) := by
  rw [pow_succ, ← Nat.div_div_eq_div_mul, Nat.log_div_base]
  have : Nat.log 2 (A/2^j) ≤ Nat.log 2 A := Nat.log_mono_right (Nat.div_le_self _ _)
  split_ifs with h
  · have := Nat.le_log_of_pow_le (by norm_num : 1 < 2) (show 2^1 ≤ A/2^j by rw [pow_one]; omega)
    exact Prod.ext rfl (by omega)
  · rw [Nat.log_of_lt (show A/2^j < 2 by omega)]; exact Prod.ext rfl (by omega)
section
variable {ι : Type U} {m : Bool}
namespace Small
variable {B P Q : ι → ℕ}
lemma sub (h : Small B P) : Small B (fun i => P i-Q i) := h.mono fun _ => Nat.sub_le _ _
lemma div (h : Small B P) : Small B (fun i => P i/Q i) := h.mono fun _ => Nat.div_le_self _ _
lemma mod (h : Small B P) : Small B (fun i => P i%Q i) := h.mono fun _ => Nat.mod_le _ _
end Small
namespace Can
variable {s t : Ty} {x : ι → T s} {B W A Q : ι → ℕ}
lemma neg {cl} {z : ι→ℂ} (h : Can m B s (c cl) x z W) : Can m B s (c cl) x (fun i => -(z i)) W :=
  (sub zero h).congr fun _ => zero_sub _
section
variable (h : Can m B s w x A W) (k : Can m B s w x Q W) (hh : Small B A)
include h k hh
lemma minus : Can m B s w x (fun i => A i - Q i) W := wsub h k hh.sub
lemma times (gg : Small B Q) : Can m B s w x (fun i => A i * Q i) W := wmul h k (hh.mul gg)
lemma plus (gg : Small B Q) : Can m B s w x (fun i => A i + Q i) W := wadd h k (hh.add gg)
lemma dvdW : Can m B s w x (fun i => A i / Q i) W := wdiv h k hh.div
lemma modW : Can m B s w x (fun i => A i % Q i) W := wmod h k hh.mod
end
-- Bound the completed address rather than each of its operands.
lemma joinBounded {P : ι → ℕ} (ha : Can m B s w x A W)
    (hp : Can m B s w x P W) (hq : Can m B s w x Q W)
    (hb : Small B fun i => A i + P i * Q i) :
    Can m B s w x (fun i => A i + P i * Q i) W :=
  wadd ha (wmul hp hq (hb.mono fun i => Nat.le_add_left _ _)) hb

lemma wpow_fixed (n : ℕ) (h : Can m B s w x A W) (hh : Small B A) : Can m B s w x (fun i => (A i)^n) W := by
  induction n with
  | zero => exact (wc 1).congr fun _ => (pow_zero _).symm
  | succ n ih => exact (times ih h (hh.pow n) hh).congr fun _ => (pow_succ _ _).symm
lemma wTwo (h : Can m B s w x A W) (hh : Small B A) (hq : Small B fun i => 2^A i) (ha : Dom W A) : Can m B s w x (fun i => 2^A i) W :=
  weaken (loop (W' := W) (uB := fun _ _ => 0) (v := fun _ j => 2^j) h (wc 1)
    ((wmul (snd second) (wc 2) ((hq.reindex During.i).mono fun d => by
      rw [← pow_succ]; exact Nat.pow_le_pow_right (by norm_num) d.hj)).congr fun _ => (pow_succ _ _).symm) hh)
    ((((Dom.self W).add (Dom.self W)).add ha).trans (Dom.of_le fun i => by simp))
lemma logC (h : Can m B s w x A W) (hh : Small B A) (ha : Dom W A) : Can m B s w x (fun i => Nat.log 2 (A i)) W := by
  have hA := hh.reindex (During.i (n := A))
  exact weaken (congr (snd (loop (uB := fun _ _ => 0)
    (v := fun i j => (A i / 2^j, Nat.log 2 (A i) - Nat.log 2 (A i / 2^j))) h (congr (pair h (wc 0)) fun i => by simp)
    (congr (pair (wdiv (fst (snd second)) (wc 2) (hA.mono fun d => (Nat.div_le_self _ _).trans (Nat.div_le_self _ _)))
      (wadd (snd (snd second)) (wlt (wc 1) (fst (snd second))) (hA.mono fun d =>
        (congrArg Prod.snd (log_step (A d.i) d.j)).le.trans ((Nat.sub_le _ _).trans (Nat.log_le_self _ _)))))
      fun d => log_step (A d.i) d.j) hh)) fun i => by
        simp [Nat.div_eq_of_lt (Nat.lt_pow_self (by norm_num : 1 < 2) .. : A i < 2 ^ A i)])
    ((((Dom.self W).add (Dom.self W)).add ha).trans (Dom.of_le fun i => by simp))
lemma natC (n : ℕ) : Can m B s sc x (fun _ => (n:ℂ)) W := by
  induction n with
  | zero => exact zero.congr fun _ => Nat.cast_zero.symm
  | succ n ih => exact (add ih one).congr fun _ => (Nat.cast_succ n).symm
lemma rat (z : ℚ) : Can m B s sc x (fun _ => (z:ℂ)) W := by
  have hn : Can m B s sc x (fun _ => ((z.num : ℤ) : ℂ)) W := by
    cases z.num with
    | ofNat n => exact (natC n).congr fun _ => (Int.cast_natCast n).symm
    | negSucc n => exact (neg (natC (n+1))).congr fun _ => (Int.cast_negSucc n).symm
  exact (mul hn (inv (natC z.den) fun _ => by simp)).congr
    fun _ => by rw [Rat.cast_def, div_eq_mul_inv]
section
variable {α β : ι → Type*} {L : ∀ i, Layout (α i)} {R : ∀ i, Layout (β i)}
  {u : ∀ i, α i × β i}
lemma addr_join (h : Can m B s w x (fun i => (L i).loc (u i).1) W) (k : Can m B s w x (fun i => (R i).loc (u i).2) W) (d : Can m B s w x (fun i => (R i).n) W) (hl : Small B fun i => (L i).n) (hr : Small B fun i => (R i).n) : Can m B s w x (fun i => ((L i).pair (R i)).loc (u i)) W :=
  wadd (wmul h d ((Small.loc hl).mul hr)) k (((Small.loc hl).mul hr).add (Small.loc hr))
variable (h : Can m B s w x (fun i => ((L i).pair (R i)).loc (u i)) W) (k : Can m B s w x (fun i => (R i).n) W) (hs : Small B fun i => (L i).n*(R i).n)
include h k hs
lemma addr_high : Can m B s w x (fun i => (L i).loc (u i).1) W :=
  (wdiv h k (hs.mono fun i => (Nat.div_le_self _ _).trans (((L i).pair (R i)).bd (u i)).le)).congr fun i => Layout.pair_div _ _ _
lemma addr_low : Can m B s w x (fun i => (R i).loc (u i).2) W :=
  (wmod h k (hs.mono fun i => (Nat.mod_le _ _).trans (((L i).pair (R i)).bd (u i)).le)).congr fun i => Layout.pair_mod _ _ _
end
end Can
end
lemma Small.during {ι : Type U} {B n : ι → ℕ} (h : Small B n) : Small (fun d : During n => B d.i) During.j :=
  let ⟨e, he⟩ := h; ⟨e, fun d => d.hj.le.trans (he d.i)⟩
end
end RAM
end OAI.PowerSaving
end

section
--might be  containing modified Apache-2.0 codes pieces from one or several sources; notices and credits: Credits.lean
namespace OAI.PowerSaving
open Finset
namespace RAM
open Ty
noncomputable section
universe U V Z
structure Bench (m : Bool) (ι : Type U) where
  size : ι→ℕ
  tray : Ty
  env : ι → T tray
namespace Bench
section
variable {m : Bool} {ι : Type U} {κ : Type V} {μ : Type Z}
abbrev Moves (b : Bench m ι) (W : ι→ℕ) (t : Ty) (f : ι→T t) : Prop :=
  Can m b.size b.tray t b.env f W
abbrev PolyMoves (b : Bench m ι) (S : ι→ℕ) (t : Ty) (f : ι→T t) : Prop :=
  PolyCan m b.size S b.tray t b.env f
abbrev Computes (b : Bench m ι) := b.PolyMoves b.size
structure WordIn (b : Bench m ι) (S f : ι→ℕ) : Prop where
  dry : b.PolyMoves S w f
  small : Small b.size f
abbrev FreeWord (b : Bench m ι) := b.WordIn fun _ => 0
abbrev PolyWord (b : Bench m ι) := b.WordIn b.size
structure FreeReads (b : Bench m ι) (q : Bench m κ) (f : ι→κ) : Prop where
  prep : b.Moves (fun _ => 0) q.tray fun i => q.env (f i)
  covers : Small b.size fun i => q.size (f i)
structure PolyReads (b : Bench m ι) (q : Bench m κ) (f : ι→κ) : Prop where
  whtInputs : b.Computes q.tray (fun i => q.env (f i))
  size : Small b.size (fun i => q.size (f i))
def along (b : Bench m ι) (f : κ → ι) : Bench m κ :=
  ⟨fun i => b.size (f i), b.tray, fun i => b.env (f i)⟩
def extend (b : Bench m ι) (t : Ty) (x : ι→T t) : Bench m ι :=
  ⟨b.size,p b.tray t,fun i => (b.env i,x i)⟩
def onlyWhere (b : Bench m ι) (P : ι→Prop) : Bench m {i // P i} :=
  b.along Subtype.val
def scan (b : Bench m ι) (n : ι→ℕ) : Bench m (During n) :=
  (b.along During.i).extend w During.j
def climbs (b : Bench m ι) (n : ι→ℕ) (t : Ty) (x : ι → ℕ → T t) :
    Bench m (During n) :=
  (b.along During.i).extend (p w t) fun d => (d.j,x d.i d.j)
variable {b : Bench m ι} {q : Bench m κ} {z : Bench m μ} {s t : Ty} {S n : ι→ℕ} {f : ι→κ}
lemma Moves.transfer {P : κ→ℕ} {x : κ→T t} (h : q.Moves P t x) (g : b.FreeReads q f) : b.Moves (fun i => P (f i)) t fun i => x (f i) :=
  Can.mono (Can.pipe g.prep (Can.ambient (Can.reindex h f) g.covers)) fun _ => (Nat.zero_add _).le
lemma PolyMoves.transfer {S : κ→ℕ} {x : κ→T t} (h : q.PolyMoves S t x) (g : b.FreeReads q f) : b.PolyMoves (fun i => S (f i)) t fun i => x (f i) :=
  let ⟨d, h⟩ := h; ⟨d, Moves.transfer h g⟩
lemma pull (h : b.PolyReads q f) {x : κ→T t} (g : q.Computes t x) : b.Computes t (fun i => x (f i)) :=
  PolyCan.pipe h.whtInputs (PolyCan.weaken (PolyCan.reindex g f) h.size h.size)
lemma draw (h : b.PolyReads q f) {x} (g : q.PolyWord x) : b.PolyWord (fun i => x (f i)) :=
  ⟨pull h g.dry, (g.small.reindex f).trans h.size⟩
namespace FreeReads
lemma next (h : b.FreeReads q f) {p : κ→μ} (g : q.FreeReads z p) : b.FreeReads z fun i => p (f i) :=
  ⟨Moves.transfer g.prep h, (g.covers.reindex f).trans h.covers⟩
lemma extend (b : Bench m ι) (x : ι→T t) : (b.extend t x).FreeReads b id := ⟨Can.first, Small.self _⟩
lemma along (b : Bench m ι) (f : κ→ι) : (b.along f).FreeReads b f := ⟨Can.id, Small.self _⟩
lemma scan (b : Bench m ι) (n : ι→ℕ) : (b.scan n).FreeReads b During.i := ⟨Can.first, Small.self _⟩
lemma climbs (b : Bench m ι) (n : ι→ℕ) (x : ι → ℕ → T t) : (b.climbs n t x).FreeReads b During.i := ⟨Can.first, Small.self _⟩
lemma supply (h : b.FreeReads q f) (x : κ→T t) (hx : b.Moves (fun _ => 0) t (fun i => x (f i))) : b.FreeReads (q.extend t x) f :=
  ⟨Can.pair h.prep hx, h.covers⟩
lemma select {n : κ→ℕ} {f : ι→During n} (h : b.FreeReads q (fun i => (f i).i)) (g : b.Moves (fun _ => 0) w (fun i => (f i).j)) : b.FreeReads (q.scan n) f :=
  ⟨Can.pair h.prep g, h.covers⟩
end FreeReads
namespace PolyReads
lemma along (b : Bench m ι) (f : κ→ι) : (b.along f).PolyReads b f := ⟨PolyCan.id, Small.self _⟩
lemma next {g : κ→μ} (h : b.PolyReads q f) (j : q.PolyReads z g) : b.PolyReads z (fun i => g (f i)) :=
  ⟨pull h j.whtInputs, (j.size.reindex f).trans h.size⟩
lemma scan (b : Bench m ι) (n : ι→ℕ) : (b.scan n).PolyReads b During.i := ⟨PolyCan.first, Small.self _⟩
lemma climbs (b : Bench m ι) (n : ι→ℕ) (x : ι → ℕ → T t) : (b.climbs n t x).PolyReads b During.i := ⟨PolyCan.first, Small.self _⟩
lemma select {n : κ→ℕ} {f : ι → During n} (h : b.PolyReads q (fun i => (f i).i)) (g : b.Computes w (fun i => (f i).j)) : b.PolyReads (q.scan n) f :=
  ⟨PolyCan.pair h.whtInputs g, h.size⟩
end PolyReads
namespace WordIn
variable {x y : ι→ℕ}
lemma wc (n : ℕ) : b.WordIn S fun _ => n := ⟨PolyCan.wc n, Small.const _ n⟩
lemma congr (h : b.WordIn S x) (g : ∀ i,x i=y i) : b.WordIn S y := by cases funext g; exact h
lemma toMoves (h : b.FreeWord x) : b.Moves (fun _ => 0) w x := let ⟨_, h⟩ := h.dry; h.weaken (Dom.const _ _)
lemma grain (h : b.FreeWord x) (S : ι→ℕ) : b.WordIn S x := ⟨h.toMoves.toPoly S, h.small⟩
lemma transfer {S x : κ→ℕ} (h : q.WordIn S x) (g : b.FreeReads q f) : b.WordIn (fun i => S (f i)) fun i => x (f i) :=
  ⟨PolyMoves.transfer h.dry g, (h.small.reindex f).trans g.covers⟩
lemma lin {F : ι → ℕ} (h : b.WordIn S x) (g : Small S x) (G : ∀ W, b.Moves W w x → Dom W x → b.Moves W w F)
    (hF : Small b.size F) : b.WordIn S F := by
  obtain ⟨d, hd⟩ := h.dry; obtain ⟨e, he⟩ := g
  exact ⟨⟨d+e, G _ (PolyCan.up hd (Nat.le_add_right _ _))
    (Dom.of_le fun i => (he i).trans (Small.pow_mono_degree _ (Nat.le_add_left _ _)))⟩, hF⟩
lemma logtwo (h : b.WordIn S x) (g : Small S x) : b.WordIn S fun i => Nat.log 2 (x i) :=
  h.lin g (fun _ a => Can.logC a h.small) (h.small.mono fun _ => Nat.log_le_self _ _)
lemma twoPow (h : b.WordIn S n) (k : Small S n) (j : Small b.size fun i => 2^n i) : b.WordIn S fun i => 2^n i :=
  h.lin k (fun _ a => Can.wTwo a h.small j) j
section
variable (h : b.WordIn S x) (g : b.WordIn S y)
include h g
lemma add : b.WordIn S fun i => x i+y i := let hs := h.small.add g.small; ⟨PolyCan.wadd h.dry g.dry hs, hs⟩
lemma sub : b.WordIn S fun i => x i-y i := ⟨PolyCan.wsub h.dry g.dry h.small.sub, h.small.sub⟩
lemma mul : b.WordIn S fun i => x i*y i := let hs := h.small.mul g.small; ⟨PolyCan.wmul h.dry g.dry hs, hs⟩
lemma div : b.WordIn S fun i => x i/y i := ⟨PolyCan.wdiv h.dry g.dry h.small.div, h.small.div⟩
lemma residue : b.WordIn S fun i => x i%y i := ⟨PolyCan.wmod h.dry g.dry h.small.mod, h.small.mod⟩
lemma cmp : b.WordIn S fun i => if x i<y i then 1 else 0 :=
  ⟨PolyCan.wlt h.dry g.dry, (Small.const _ 1).mono fun _ => by split <;> omega⟩
lemma minimum : b.WordIn S fun i => min (x i) (y i) := ((h.sub (h.sub g)).congr fun _ => Nat.sub_sub_eq_min _ _)
end
end WordIn
lemma scanIndex (h : b.WordIn S n) : (b.scan n).WordIn (fun i => S i.i) During.j := ⟨PolyCan.second, h.small.during⟩
lemma climbIndex (h : b.WordIn S n) (x : ι → ℕ → T t) : (b.climbs n t x).WordIn (fun i => S i.i) During.j := ⟨PolyCan.fst PolyCan.second, h.small.during⟩
lemma PolyMoves.token (b : Bench m ι) (n S : ι→ℕ) (x : ι → ℕ → T t) : (b.climbs n t x).PolyMoves (fun i => S i.i) t fun i => x i.i i.j :=
  PolyCan.snd PolyCan.second
lemma newestMoves {W} (b : Bench m ι) (x : ι→T t) : (b.extend t x).Moves W t x := Can.second
lemma tokenNow (b : Bench m ι) (n : ι→ℕ) (x : ι → ℕ → T t) : (b.climbs n t x).Moves (fun _ => 0) t (fun i => x i.i i.j) :=
  Can.snd Can.second
section
variable (h : b.WordIn S n) (k : Small S n)
include h k
lemma loopPoly (x : ι → ℕ → T t) (g : b.PolyMoves S t fun i => x i 0) (j : (b.climbs n t x).PolyMoves (fun i => S i.i) t fun i => x i.i (i.j+1)) : b.PolyMoves S t fun i => x i (n i) :=
  PolyCan.loop h.dry g j h.small k
lemma tabPoly (x : ι→ℕ→T t) (g : (b.scan n).PolyMoves (fun i => S i.i) t fun i => x i.i i.j) : b.PolyMoves S (a t) fun i => Tape.tab (n i) (x i) :=
  PolyCan.tab h.dry g h.small k
end
lemma tab (h : b.PolyWord n) (x : ι→ℕ→T t) (g : (b.scan n).Computes t fun i => x i.i i.j) : b.Computes (a t) fun i => Tape.tab (n i) (x i) := tabPoly h h.2 x g
lemma loop (h : b.PolyWord n) (x : ι → ℕ → T t) (g : b.Computes t fun i => x i 0) (k : (b.climbs n t x).Computes t fun d => x d.i (d.j+1)) : b.Computes t fun i => x i (n i) := loopPoly h h.2 x g k
section
variable {u : ι → ℕ → ℕ} (h : b.FreeWord n)
include h
lemma arrayM (f : ι→ℕ→T t) (hs : (b.scan n).Moves (fun d => u d.i d.j) t (fun d => f d.i d.j)) : b.Moves (fun i => n i + ∑ j ∈ range (n i), u i j) (a t) (fun i => Tape.tab (n i) (f i)) :=
  Can.mono (Can.tab (uB := u) h.toMoves hs h.small) fun _ => by simp
lemma arrayNow (f : ι→ℕ→T t) (hs : (b.scan n).Moves (fun _ => 0) t (fun d => f d.i d.j)) : b.Moves n (a t) (fun i => Tape.tab (n i) (f i)) :=
  Can.mono (Can.tab (uB := fun _ _ => 0) h.toMoves hs h.small) fun _ => by simp
lemma scatterNow (f : ι → ℕ → ℕ × T t) (hs : (b.scan n).Moves (fun _ => 0) (p w t) (fun d => f d.i d.j)) : b.Moves n (a t) (fun i => Tape.sow (n i) (n i) t.blank (f i)) :=
  Can.weaken (Can.sow (uB := fun _ _ => 0) h.toMoves h.toMoves hs h.small h.small) ⟨3, fun i => by simp; omega⟩
lemma repeatM (f : ι → ℕ → T t) (hb : b.Moves (fun _ => 0) t fun i => f i 0) (hh : (b.climbs n t f).Moves (fun d => u d.i d.j) t fun d => f d.i (d.j+1)) : b.Moves (fun i => n i+∑ j ∈ range (n i), u i j) t fun i => f i (n i) :=
  Can.mono (Can.loop (uB := u) h.toMoves hb hh h.small) fun _ => by simp
lemma FreeWord.logM : b.Moves n w fun i => Nat.log 2 (n i) := Can.logC (h.toMoves.anyCost (V := n)) h.small (Dom.self n)
lemma FreeWord.numeralM : b.Moves n sc fun i => (n i:ℂ) :=
  Can.mono (repeatM (u := fun _ _ => 0) h (fun _ j => (j : T sc)) (Can.zero.congr fun _ => Nat.cast_zero.symm)
    ((Can.add (tokenNow (t := sc) b n fun _ j => (j : ℂ)) Can.one).congr fun _ => (Nat.cast_succ _).symm)) fun _ => by simp
end
lemma restricted (b : Bench m ι) (p : ι→Prop) : (b.onlyWhere p).PolyReads b Subtype.val := PolyReads.along b Subtype.val
def Decides (b : Bench m ι) (P : ι→Prop) : Prop :=
  ∃ x : ι→ℕ, b.PolyWord x ∧ ∀ i, P i ↔ x i ≠ 0
namespace Decides
variable {P Q : ι→Prop}
lemma of_iff (h : b.Decides P) (e : ∀ i, Q i ↔ P i) : b.Decides Q :=
  let ⟨z, hz, hz'⟩ := h; ⟨z, hz, fun i => (e i).trans (hz' i)⟩
lemma lt {x y} (h : b.PolyWord x) (g : b.PolyWord y) : b.Decides (fun i => x i < y i) :=
  ⟨_, h.cmp g, fun _ => by beta_reduce; split_ifs with hl <;> simp [hl]⟩
lemma neg (h : b.Decides P) : b.Decides (fun i => ¬ P i) :=
  let ⟨z, hz, hz'⟩ := h
  ⟨_, (WordIn.wc 1).sub hz, fun i => by beta_reduce; rw [hz' i]; constructor <;> intro <;> omega⟩
lemma le {x y} (h : b.PolyWord x) (g : b.PolyWord y) : b.Decides (fun i => x i ≤ y i) :=
  (neg (lt g h)).of_iff fun _ => Nat.not_lt.symm
lemma both (h : b.Decides P) (g : b.Decides Q) : b.Decides (fun i => P i ∧ Q i) :=
  let ⟨z, hz, hz'⟩ := h; let ⟨z', gz, gz'⟩ := g
  ⟨_, hz.mul gz, fun i => (and_congr (hz' i) (gz' i)).trans mul_ne_zero_iff.symm⟩
lemma eq {x y} (h : b.PolyWord x) (g : b.PolyWord y) : b.Decides (fun i => x i=y i) :=
  (both (le h g) (le g h)).of_iff fun _ => le_antisymm_iff
end Decides
lemma branchM {P : ι→Prop} [DecidablePred P] {x y : ι→T t} (h : b.Decides P) (a : (b.onlyWhere P).Computes t (fun i => x i.val)) (c : (b.onlyWhere (fun i => ¬ P i)).Computes t (fun i => y i.val)) : b.Computes t (fun i => if P i then x i else y i) := by
  obtain ⟨z, hz, hP⟩ := h
  refine PolyCan.testz hz.dry ?_ ?_
  · exact PolyCan.cong (PolyCan.reindex c fun i : {i // z i = 0} => ⟨i.1, fun h => (hP i.1).1 h i.2⟩)
      (fun _ => rfl) fun i => (if_neg fun h => (hP i.1).1 h i.2).symm
  · exact PolyCan.cong (PolyCan.reindex a fun i : {i // z i ≠ 0} => ⟨i.1, (hP i.1).2 i.2⟩)
      (fun _ => rfl) fun i => (if_pos ((hP i.1).2 i.2)).symm
lemma branchN {P : ι→Prop} [DecidablePred P] {x y : ι→ℕ} (h : b.Decides P) (a : (b.onlyWhere P).PolyWord (fun i => x i.val)) (c : (b.onlyWhere (fun i => ¬ P i)).PolyWord (fun i => y i.val)) : b.PolyWord (fun i => if P i then x i else y i) := by
  obtain ⟨d, hd⟩ := a.small; obtain ⟨e, he⟩ := c.small
  refine ⟨branchM h a.dry c.dry, d+e, fun i => ?_⟩
  beta_reduce; split_ifs with hp
  · exact (hd ⟨i, hp⟩).trans (Small.pow_mono_degree _ (Nat.le_add_right _ _))
  · exact (he ⟨i, hp⟩).trans (Small.pow_mono_degree _ (Nat.le_add_left _ _))
lemma iteN {P : ι→Prop} [DecidablePred P] {x y : ι→ℕ} (h : b.Decides P) (a : b.PolyWord x) (c : b.PolyWord y) : b.PolyWord (fun i => if P i then x i else y i) :=
  branchN h (draw (restricted b P) a) (draw (restricted b _) c)
end
end Bench
end
end RAM
end OAI.PowerSaving
end
-- ===== end part 2 =====
