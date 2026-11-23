--might be  containing modified Apache-2.0 codes pieces from one or several sources; notices and credits: Credits.lean
import Submission.OAI.Computability.FourierTransform.RAM
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
namespace OAI
namespace PowerSaving
open Finset
universe u v U V Z
variable {α β : Type*}
macro "ar" : tactic => `(tactic| (first | omega | ((try dsimp only); ring_nf; omega)))
namespace Tape
lemma ext_look {a b : Tape α} (hlen : a.len = b.len) (z : α) (h : ∀ i, i<a.len → a.look i z = b.look i z) : a=b := by
  obtain ⟨n, f⟩ := a; obtain ⟨n', g⟩ := b
  obtain rfl : n = n' := hlen
  congr 1; funext j; simpa [Tape.look] using h j j.2
@[simp] lemma len_tab (n : ℕ) (f : ℕ → α) : (tab n f).len = n := rfl
@[simp] lemma len_set (v : Tape α) (i : ℕ) (x : α) : (v.set i x).len = v.len := rfl
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
  ⟨.comp f g, C+E+1, d+e, fun i => .tick (.pass (h i).up (k i).up) (by ar)⟩
lemma fork (g : Able m b s u x z W' Z') : Able m b s (p t u) x (fun i => (y i,z i)) (fun i => W i+W' i) (fun i => Z i+Z' i) :=
  let ⟨f, C, d, h⟩ := h; let ⟨g, E, e, k⟩ := g
  ⟨.fork f g, C+E+1, d+e, fun i => .mono (.pass (h i).up (.pass (k i).up (one_ok _ _))) (by ar) le_rfl⟩
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
  ⟨.importClosed f, C+1, d, fun i => ((h i).tick (by ar)).mono le_rfl (max_le (le_max_left _ _) (Nat.zero_le _))⟩
lemma ifz {n : ι → ℕ} (hx : Able m b s w x n W' Z') (hz : Able m (b.comap (fun i : {i // n i = 0} => i.val)) s t (fun i => x i.val) (fun i => y i.val) (fun i => W i.val) (fun i => Z i.val)) (hn : Able m (b.comap (fun i : {i // n i ≠ 0} => i.val)) s t (fun i => x i.val) (fun i => y i.val) (fun i => W i.val) (fun i => Z i.val)) : Able m b s t x y (fun i => W' i+W i) (fun i => Z' i+Z i) := by
  obtain ⟨q, C, d, hq⟩ := hx; obtain ⟨f, E, e, hf⟩ := hz; obtain ⟨g, F, k, hg⟩ := hn
  refine ⟨.ifz q f g, C+E+F+1, d+e+k, fun i => .tick (.pass (w' := (E+F)*(W i+1)+Z i) (hq i).up ?_) (by ar)⟩
  by_cases h0 : n i = 0
  · simp only [h0, ↓reduceIte]; exact (hf ⟨i, h0⟩).up.mono (by ar) le_rfl
  · simp only [h0, ↓reduceIte]; exact (hg ⟨i, h0⟩).up.mono (by ar) le_rfl
lemma loop {n : ι → ℕ} {v : ι → ℕ → T t} {Wb Zb : ι → ℕ → ℕ} (h : Able m b s w x n W Z) (hi : Able m b s t x (fun i => v i 0) W' Z') (hs : Able m (b.comap (During.i (n:=n))) (p s (p w t)) t (fun d => (x d.i,d.j,v d.i d.j)) (fun d => v d.i (d.j+1)) (fun d => Wb d.i d.j) (fun d => Zb d.i d.j)) (hc : Small b.B n) : Able m b s t x (fun i => v i (n i)) (fun i => W i + W' i + n i + ∑ j ∈ range (n i), Wb i j) (fun i => Z i + Z' i + ∑ j ∈ range (n i), Zb i j) :=
  let ⟨f, C, d, h⟩ := h; let ⟨g, E, e, hi⟩ := hi; let ⟨k, F, c₀, hs⟩ := hs; let ⟨q, hc⟩ := hc
  ⟨.loop f g k, C+E+F+3, d+e+c₀+q, fun i => .tick (.pass (h i).up (.pass (hi i).up
    (steps_ok (A := fun j => F*(Wb i j+1)+Zb i j) (Bank.le (hc i)) fun j hj => (hs ⟨i, j, hj⟩).up)))
    (by simp only [Bill.sc]; ar)⟩
lemma tab {n : ι → ℕ} {v : ι → ℕ → T t} {Wb Zb : ι → ℕ → ℕ} (h : Able m b s w x n W Z) (hs : Able m (b.comap (During.i (n:=n))) (p s w) t (fun d => (x d.i,d.j)) (fun d => v d.i d.j) (fun d => Wb d.i d.j) (fun d => Zb d.i d.j)) (hc : Small b.B n) : Able m b s (a t) x (fun i => Tape.tab (n i) (v i)) (fun i => W i + n i + ∑ j ∈ range (n i), Wb i j) (fun i => Z i + ∑ j ∈ range (n i), Zb i j) :=
  let ⟨f, C, d, h⟩ := h; let ⟨k, F, c₀, hs⟩ := hs; let ⟨q, hc⟩ := hc
  ⟨.tab f k, C+F+5, d+c₀+q, fun i => .tick (.pass (h i).up (tab_ok (fun j => F*(Wb i j+1)+Zb i j) _ _ _
    (Bank.le (hc i)) fun j hj => (hs ⟨i, j, hj⟩).up)) (by simp only [Bill.sc]; ar)⟩
lemma first {v : ι → T (p s t)} : Able m b (p s t) s v (fun i => (v i).1) W Z := atom (d := 0) .fst fun _ => one_ok _ _
lemma second {v : ι → T (p s t)} : Able m b (p s t) t v (fun i => (v i).2) W Z := atom (d := 0) .snd fun _ => one_ok _ _
lemma fst {v : ι → T (p t u)} (h : Able m b s (p t u) x v W Z) : Able m b s t x (fun i => (v i).1) W Z := h.post .fst
lemma snd {v : ι → T (p t u)} (h : Able m b s (p t u) x v W Z) : Able m b s u x (fun i => (v i).2) W Z := h.post .snd
lemma sow {n : ι → ℕ} {v : ι → ℕ → ℕ × T t} {len : ι → ℕ} {Wl Zl : ι → ℕ} {Wb Zb : ι → ℕ → ℕ} (hx : Able m b s w x len Wl Zl) (h : Able m b s w x n W Z) (hs : Able m (b.comap (During.i (n:=n))) (p s w) (p w t) (fun d => (x d.i,d.j)) (fun d => v d.i d.j) (fun d => Wb d.i d.j) (fun d => Zb d.i d.j)) (hg : Small b.B len) (hc : Small b.B n) : Able m b s (a t) x (fun i => Tape.sow (len i) (n i) t.blank (v i)) (fun i => Wl i + W i + len i + n i + ∑ j ∈ range (n i), Wb i j) (fun i => Zl i + Z i + ∑ j ∈ range (n i), Zb i j) :=
  let ⟨g, E, e, hl⟩ := hx; let ⟨f, C, d, h⟩ := h; let ⟨k, F, c₀, hs⟩ := hs; let ⟨q, hc⟩ := hc; let ⟨q', hg⟩ := hg
  ⟨.sow g f k, C+E+F+5, d+e+c₀+q+q', fun i => .tick (.pass (hl i).up (.pass (h i).up
    (sow_ok (fun j => F*(Wb i j+1)+Zb i j) _ (Bank.le (hg i)) (Bank.le (hc i)) fun j hj => (hs ⟨i, j, hj⟩).up)))
    (by simp only [Bill.sc]; ar)⟩
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
lemma cy {y'} (hy : ∀ i, y i = y' i) : Can m B s t x y' W := Able.cong h (fun _ => rfl) hy
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
variable {uB : ι → ℕ → ℕ}
lemma loop {v : ι → ℕ → T t} (h : Can m B s w x n W) (hi : Can m B s t x (fun i => v i 0) W') (hs : Can m (fun d : During n => B d.i) (p s (p w t)) t (fun d => (x d.i,d.j,v d.i d.j)) (fun d => v d.i (d.j+1)) (fun d => uB d.i d.j)) (hc : Small B n) : Can m B s t x (fun i => v i (n i)) (fun i => W i + W' i + n i + ∑ j ∈ range (n i), uB i j) :=
  Able.mono (Able.loop (Wb := uB) (Zb := fun _ _ => 0) h hi hs hc) (fun _ => le_rfl) fun _ => by simp
lemma tab {v : ι → ℕ → T t} (h : Can m B s w x n W) (hs : Can m (fun d : During n => B d.i) (p s w) t (fun d => (x d.i,d.j)) (fun d => v d.i d.j) (fun d => uB d.i d.j)) (hc : Small B n) : Can m B s (a t) x (fun i => Tape.tab (n i) (v i)) (fun i => W i + n i + ∑ j ∈ range (n i), uB i j) :=
  Able.mono (Able.tab (Wb := uB) (Zb := fun _ _ => 0) h hs hc) (fun _ => le_rfl) fun _ => by simp
lemma sow {v : ι → ℕ → ℕ × T t} (hl : Can m B s w x q W') (h : Can m B s w x n W) (hs : Can m (fun d : During n => B d.i) (p s w) (p w t) (fun d => (x d.i,d.j)) (fun d => v d.i d.j) (fun d => uB d.i d.j)) (hg : Small B q) (hc : Small B n) : Can m B s (a t) x (fun i => Tape.sow (q i) (n i) t.blank (v i)) (fun i => W' i + W i + q i + n i + ∑ j ∈ range (n i), uB i j) :=
  Able.mono (Able.sow (Wb := uB) (Zb := fun _ _ => 0) hl h hs hg hc) (fun _ => le_rfl) fun _ => by simp
end
end Can
def PolyCan {ι : Type U} (m : Bool) (B S : ι → ℕ) (s t) (x : ι → T s) (y : ι → T t) : Prop :=
  ∃ d : ℕ, Can m B s t x y (fun i => (S i+2)^d)
namespace PolyCan
variable {ι : Type U} {κ : Type V} {m : Bool} {B B' S S' : ι → ℕ} {s t u : Ty}
  {x : ι → T s} {y : ι → T t} {z : ι → T u} {W : ι → ℕ}
lemma up {S : ι → ℕ} {d e : ℕ} (h : Can m B s t x y (fun i => (S i+2)^d)) (hde : d ≤ e) : Can m B s t x y (fun i => (S i+2)^e) :=
  Can.mono h fun _ => Nat.pow_le_pow_right (by omega) hde
lemma lift2 {s₁ t₁ s₂ t₂ x₁ y₁ x₂ y₂} (h : PolyCan m B S s t x y) (g : PolyCan m B S s₁ t₁ x₁ y₁)
    (F : ∀ {W}, Can m B s t x y W → Can m B s₁ t₁ x₁ y₁ W → Can m B s₂ t₂ x₂ y₂ W) : PolyCan m B S s₂ t₂ x₂ y₂ :=
  let ⟨d, h⟩ := h; let ⟨e, g⟩ := g
  ⟨d+e, F (up h (Nat.le_add_right _ _)) (up g (Nat.le_add_left _ _))⟩
lemma of_can (h : Can m B s t x y W) (g : Small S W) : PolyCan m B S s t x y :=
  let ⟨d, g⟩ := g; ⟨d, Can.mono h g⟩
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
lemma bind (h : PolyCan m B S s t x y) (g : PolyCan m B S (p s t) u (fun i => (x i,y i)) z) : PolyCan m B S s u x z :=
  lift2 h g Can.bind
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
  let ⟨d, h⟩ := h; let ⟨e, g⟩ := g; let ⟨k, j⟩ := j
  ⟨d+e+k, Can.testz (up h (by omega)) (up g (by omega)) (up j (by omega))⟩
end
end PolyCan
lemma Small.during {ι : Type U} {B n : ι → ℕ} (h : Small B n) : Small (fun d : During n => B d.i) During.j :=
  let ⟨e, he⟩ := h; ⟨e, fun d => d.hj.le.trans (he d.i)⟩
structure Bench (m : Bool) (ι : Type U) where
  size : ι→ℕ
  tray : Ty
  env : ι → T tray
namespace Bench
variable {m : Bool} {ι : Type U} {κ : Type V}
def Makes (b : Bench m ι) (t : Ty) (f : ι → T t) : Prop :=
  PolyCan m b.size b.size b.tray t b.env f
structure Digit (b : Bench m ι) (f : ι→ℕ) : Prop where
  run : b.Makes w f
  small : Small b.size f
def along (b : Bench m ι) (f : κ → ι) : Bench m κ :=
  ⟨fun i => b.size (f i), b.tray, fun i => b.env (f i)⟩
def extend (b : Bench m ι) (t : Ty) (x : ι→T t) : Bench m ι :=
  ⟨b.size,p b.tray t,fun i => (b.env i,x i)⟩
def scrutin (b : Bench m ι) (P : ι→Prop) : Bench m {i // P i} :=
  b.along Subtype.val
def scan (b : Bench m ι) (n : ι→ℕ) : Bench m (During n) :=
  (b.along During.i).extend w During.j
def climbs (b : Bench m ι) (n : ι→ℕ) (t : Ty) (x : ι → ℕ → T t) :
    Bench m (During n) :=
  (b.along During.i).extend (p w t) fun d => (d.j,x d.i d.j)
structure Feeds (b : Bench m ι) (q : Bench m κ) (f : ι→κ) : Prop where
  inputs : b.Makes q.tray (fun i => q.env (f i))
  size : Small b.size (fun i => q.size (f i))
variable {b : Bench m ι} {q : Bench m κ} {s t : Ty}
namespace Makes
lemma congr {x y : ι→T t} (h : b.Makes t x) (H : ∀ i, x i=y i) : b.Makes t y := PolyCan.cong h (fun _ => rfl) H
lemma pair {x : ι→T s} {y : ι→T t} (h : b.Makes s x) (g : b.Makes t y) : b.Makes (p s t) (fun i => (x i,y i)) := PolyCan.pair h g
lemma fst {x : ι→T (p s t)} (h : b.Makes (p s t) x) : b.Makes s (fun i => (x i).1) := PolyCan.fst h
lemma snd {x : ι→T (p s t)} (h : b.Makes (p s t) x) : b.Makes t (fun i => (x i).2) := PolyCan.snd h
lemma wc (n : ℕ) : b.Makes w (fun _ => n) := PolyCan.wc n
lemma zero {cl} : b.Makes (c cl) (fun _ => 0) := PolyCan.zero
lemma one : b.Makes sc (fun _ => 1) := PolyCan.one
lemma add {cl} {x y : ι→ℂ} (h : b.Makes (c cl) x) (g : b.Makes (c cl) y) : b.Makes (c cl) (fun i => x i+y i) := PolyCan.add h g
lemma sub {cl} {x y : ι→ℂ} (h : b.Makes (c cl) x) (g : b.Makes (c cl) y) : b.Makes (c cl) (fun i => x i-y i) := PolyCan.sub h g
lemma neg {cl} {x : ι→ℂ} (h : b.Makes (c cl) x) : b.Makes (c cl) (fun i => -x i) :=
  (sub zero h).congr fun _ => zero_sub _
lemma mul {cl} {x y : ι→ℂ} (h : b.Makes sc x) (g : b.Makes (c cl) y) : b.Makes (c cl) (fun i => x i*y i) := PolyCan.mul h g
lemma inv {x : ι→ℂ} (h : b.Makes sc x) (g : ∀ i, x i ≠ 0) : b.Makes sc (fun i => (x i)⁻¹) := PolyCan.inv h g
lemma look {x : ι→Tape (T t)} {n} (h : b.Makes (a t) x) (g : b.Makes w n) : b.Makes t (fun i => (x i).look (n i) t.blank) := PolyCan.look h g
end Makes
lemma prepares (b : Bench m ι) : b.Makes b.tray b.env := PolyCan.id
lemma pull {f : ι→κ} (h : b.Feeds q f) {x : κ→T t} (g : q.Makes t x) : b.Makes t (fun i => x (f i)) :=
  PolyCan.pipe h.inputs (PolyCan.weaken (PolyCan.reindex g f) h.size h.size)
lemma draw {f : ι→κ} (h : b.Feeds q f) {x} (g : q.Digit x) : b.Digit (fun i => x (f i)) :=
  ⟨pull h g.run, (g.small.reindex f).trans h.size⟩
lemma Feeds.along (b : Bench m ι) (f : κ→ι) : (b.along f).Feeds b f := ⟨PolyCan.id, Small.self _⟩
lemma Feeds.extend (b : Bench m ι) (t : Ty) (f : ι→T t) : (b.extend t f).Feeds b id := ⟨PolyCan.first, Small.self _⟩
lemma toppings (b : Bench m ι) (f : ι→T t) : (b.extend t f).Makes t f := PolyCan.second
lemma Feeds.next {μ : Type Z} {a : Bench m μ} {f : ι→κ} {g : κ→μ} (h : b.Feeds q f) (j : q.Feeds a g) : b.Feeds a (fun i => g (f i)) :=
  ⟨pull h j.inputs, (j.size.reindex f).trans h.size⟩
namespace Digit
variable {x y : ι→ℕ}
lemma wc (n : ℕ) : b.Digit (fun _ => n) := ⟨Makes.wc n, Small.const _ n⟩
lemma congr (h : b.Digit x) (g : ∀ i, x i=y i) : b.Digit y := by cases funext g; exact h
section
variable (h : b.Digit x) (g : b.Digit y)
include h g
lemma add : b.Digit (fun i => x i + y i) := let hs := h.small.add g.small; ⟨PolyCan.wadd h.run g.run hs, hs⟩
lemma sub : b.Digit (fun i => x i-y i) :=
  have hs : Small b.size (fun i => x i - y i) := h.small.mono fun _ => Nat.sub_le _ _
  ⟨PolyCan.wsub h.run g.run hs, hs⟩
lemma mul : b.Digit (fun i => x i * y i) := let hs := h.small.mul g.small; ⟨PolyCan.wmul h.run g.run hs, hs⟩
lemma minimum : b.Digit (fun i => min (x i) (y i)) :=
  (h.sub (h.sub g)).congr fun _ => Nat.sub_sub_eq_min _ _
end
end Digit
variable {n : ι→ℕ}
lemma Feeds.scan (b : Bench m ι) (n : ι→ℕ) : (b.scan n).Feeds b During.i := ⟨PolyCan.first, Small.self _⟩
lemma Feeds.climbs (b : Bench m ι) (n : ι→ℕ) (x : ι → ℕ → T t) : (b.climbs n t x).Feeds b During.i := ⟨PolyCan.first, Small.self _⟩
lemma slot (h : b.Digit n) : (b.scan n).Digit During.j := ⟨PolyCan.second, h.small.during⟩
lemma tab (h : b.Digit n) (x : ι→ℕ→T t) (g : (b.scan n).Makes t (fun d => x d.i d.j)) : b.Makes (a t) (fun i => Tape.tab (n i) (x i)) :=
  PolyCan.tab h.run g h.small h.small
lemma stepi (h : b.Digit n) (x : ι → ℕ → T t) : (b.climbs n t x).Digit During.j := ⟨PolyCan.fst PolyCan.second, h.small.during⟩
lemma stepsum (b : Bench m ι) (n : ι→ℕ) (x : ι → ℕ → T t) : (b.climbs n t x).Makes t (fun d => x d.i d.j) := PolyCan.snd PolyCan.second
lemma loop (h : b.Digit n) (x : ι → ℕ → T t) (g : b.Makes t (fun i => x i 0)) (k : (b.climbs n t x).Makes t (fun d => x d.i (d.j+1))) : b.Makes t (fun i => x i (n i)) :=
  PolyCan.loop h.run g k h.small h.small
lemma Feeds.select {n : κ→ℕ} {f : ι → During n} (h : b.Feeds q (fun i => (f i).i)) (g : b.Makes w (fun i => (f i).j)) : b.Feeds (q.scan n) f :=
  ⟨PolyCan.pair h.inputs g, h.size⟩
end Bench
end RAM
end PowerSaving
end OAI
namespace OAI.PowerSaving.RAM
open Ty
def Code.blank {m : Bool} {r : Port} : (s t : Ty) → Code m r s t
  | _, .w => .atom (.lit 0)
  | _, .c cl => .atom (.cz cl)
  | s, .p x y => .fork (Code.blank s x) (Code.blank s y)
  | s, .a x => .tab (.atom (.lit 0)) (Code.blank (.p s .w) x)
end OAI.PowerSaving.RAM

namespace OAI
namespace PowerSaving.RAM
open Ty
noncomputable section
universe U V
namespace Bench
variable {m : Bool} {ι : Type U} {κ : Type V} {b : Bench m ι} {q : Bench m κ}
lemma restricted (b : Bench m ι) (p : ι→Prop) : (b.scrutin p).Feeds b Subtype.val := Feeds.along b Subtype.val
def Study (b : Bench m ι) (P : ι→Prop) : Prop :=
  ∃ x : ι→ℕ, b.Digit x ∧ ∀ i, P i ↔ x i ≠ 0
namespace Study
variable {P Q : ι→Prop}
lemma of_iff (h : b.Study P) (e : ∀ i, Q i ↔ P i) : b.Study Q :=
  let ⟨z, hz, hz'⟩ := h; ⟨z, hz, fun i => (e i).trans (hz' i)⟩
lemma lt {x y} (h : b.Digit x) (g : b.Digit y) : b.Study (fun i => x i < y i) :=
  ⟨_, ⟨PolyCan.wlt h.run g.run, (Small.const _ 1).mono fun _ => by split <;> omega⟩,
    fun _ => by beta_reduce; split_ifs with hl <;> simp [hl]⟩
lemma neg (h : b.Study P) : b.Study (fun i => ¬ P i) :=
  let ⟨z, hz, hz'⟩ := h
  ⟨_, (Digit.wc 1).sub hz, fun i => by beta_reduce; rw [hz' i]; constructor <;> intro <;> omega⟩
lemma le {x y} (h : b.Digit x) (g : b.Digit y) : b.Study (fun i => x i ≤ y i) :=
  (neg (lt g h)).of_iff fun _ => Nat.not_lt.symm
lemma both (h : b.Study P) (g : b.Study Q) : b.Study (fun i => P i ∧ Q i) :=
  let ⟨z, hz, hz'⟩ := h; let ⟨z', gz, gz'⟩ := g
  ⟨_, hz.mul gz, fun i => (and_congr (hz' i) (gz' i)).trans mul_ne_zero_iff.symm⟩
lemma eq {x y} (h : b.Digit x) (g : b.Digit y) : b.Study (fun i => x i=y i) :=
  (both (le h g) (le g h)).of_iff fun _ => le_antisymm_iff
end Study
lemma branchM {t : Ty} {P : ι→Prop} [DecidablePred P] {x y : ι→T t} (h : b.Study P) (a : (b.scrutin P).Makes t (fun i => x i.val)) (c : (b.scrutin (fun i => ¬ P i)).Makes t (fun i => y i.val)) : b.Makes t (fun i => if P i then x i else y i) := by
  obtain ⟨z, hz, hP⟩ := h
  refine PolyCan.testz hz.run ?_ ?_
  · exact PolyCan.cong (PolyCan.reindex c fun i : {i // z i = 0} => ⟨i.1, fun h => (hP i.1).1 h i.2⟩)
      (fun _ => rfl) fun i => (if_neg fun h => (hP i.1).1 h i.2).symm
  · exact PolyCan.cong (PolyCan.reindex a fun i : {i // z i ≠ 0} => ⟨i.1, (hP i.1).2 i.2⟩)
      (fun _ => rfl) fun i => (if_pos ((hP i.1).2 i.2)).symm
lemma branchN {P : ι→Prop} [DecidablePred P] {x y : ι→ℕ} (h : b.Study P) (a : (b.scrutin P).Digit (fun i => x i.val)) (c : (b.scrutin (fun i => ¬ P i)).Digit (fun i => y i.val)) : b.Digit (fun i => if P i then x i else y i) := by
  obtain ⟨d, hd⟩ := a.small; obtain ⟨e, he⟩ := c.small
  refine ⟨branchM h a.run c.run, d+e, fun i => ?_⟩
  beta_reduce; split_ifs with hp
  · exact (hd ⟨i, hp⟩).trans (Small.pow_mono_degree _ (Nat.le_add_right _ _))
  · exact (he ⟨i, hp⟩).trans (Small.pow_mono_degree _ (Nat.le_add_left _ _))
lemma iteN {P : ι→Prop} [DecidablePred P] {x y : ι→ℕ} (h : b.Study P) (a : b.Digit x) (c : b.Digit y) : b.Digit (fun i => if P i then x i else y i) :=
  branchN h (draw (restricted b P) a) (draw (restricted b _) c)
end Bench
end
end PowerSaving.RAM
end OAI
