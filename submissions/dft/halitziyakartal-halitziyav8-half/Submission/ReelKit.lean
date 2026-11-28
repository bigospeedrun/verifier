-- Reels (straight-line in-place programs) and their meaning, axis tensors, block covers, CRT indexing.
import Submission.BinaryKernel
import Submission.CostCalculus
import Submission.DFTIdentities
set_option linter.all false

section

namespace OAI
namespace PowerSaving.ReelKit
open Binary Spectral Matrix Finset
noncomputable section

structure Stroke where
  ix : ℕ → ℕ
  dye : Line
  partner : ℕ → ℕ

namespace Stroke

def applyM (u : Stroke) (x : Line) : Line := fun i => u.dye i * x (u.ix i)

def applyC (u : Stroke) (x : Line) : Line := fun i =>
  if u.partner i = i then x i else ca * x i + cb * x (u.partner i)

def send (u : Stroke) (x : Line) := u.applyC (u.applyM x)

structure Sound (u : Stroke) (n : ℕ) : Prop where
  bdix : ∀ i < n, u.ix i < n
  bdp : ∀ i < n, u.partner i < n
  pair : ∀ i, u.partner (u.partner i)=i
  awayix : ∀ i, n ≤ i → u.ix i=i
  awayp : ∀ i, n ≤ i → u.partner i=i
  awayd : ∀ i, n ≤ i → u.dye i=1

namespace Sound
variable {u : Stroke} {n n' : ℕ}

lemma wider (h : u.Sound n) (hn : n ≤ n') : u.Sound n' :=
  ⟨fun i hi => if g : i < n then (h.bdix i g).trans_le hn else by rw [h.awayix i (by omega)]; exact hi,
   fun i hi => if g : i < n then (h.bdp i g).trans_le hn else by rw [h.awayp i (by omega)]; exact hi,
   h.pair, fun i _ => h.awayix i (by omega), fun i _ => h.awayp i (by omega),
   fun i _ => h.awayd i (by omega)⟩

lemma send_away (h : u.Sound n) (x : Line) {i : ℕ} (hi : n ≤ i) : u.send x i = x i := by
  simp [send, applyC, applyM, h.awayp i hi, h.awayix i hi, h.awayd i hi]

lemma send_congr (h : u.Sound n) {x y : Line} (e : ∀ k < n, x k = y k) {i : ℕ} (hi : i < n) :
    u.send x i = u.send y i := by
  simp only [send, applyC, applyM, e _ (h.bdix i hi), e _ (h.bdix _ (h.bdp i hi))]

end Sound

def idStroke : Stroke := ⟨id,fun _ => 1,id⟩

lemma sound_idStroke (n : ℕ) : idStroke.Sound n :=
  ⟨fun _ hi => hi, fun _ hi => hi, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

def plain (n : ℕ) (l : ℕ→ℕ) (d : Line) : Stroke :=
  ⟨fun i => if i < n then l i else i, fun i => if i < n then d i else 1, id⟩

lemma plain_sound {n : ℕ} {l : ℕ → ℕ} (d : Line) (h : ∀ i < n, l i < n) : (plain n l d).Sound n :=
  ⟨fun i hi => by simp [plain, hi, h i hi], fun _ hi => hi, fun _ => rfl,
   fun i hi => by simp [plain, show ¬ i < n by omega], fun _ _ => rfl,
   fun i hi => by simp [plain, show ¬ i < n by omega]⟩

lemma plain_send (n : ℕ) (l : ℕ → ℕ) (d x : Line) (i : ℕ) :
    (plain n l d).send x i = if i < n then d i * x (l i) else x i := by
  by_cases h : i < n <;> simp [send, applyC, applyM, plain, h]

def sideBySide (p : ℕ) (u v : Stroke) : Stroke where
  ix i := if i<p then u.ix i else p+v.ix (i-p)
  dye i := if i<p then u.dye i else v.dye (i-p)
  partner i := if i<p then u.partner i else p+v.partner (i-p)

lemma Sound.sideBySide {p q : ℕ} {a b : Stroke} (h : a.Sound p) (g : b.Sound q) :
    (sideBySide p a b).Sound (p+q) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i => ?_, fun i hi => ?_, fun i hi => ?_,
    fun i hi => ?_⟩ <;> simp only [Stroke.sideBySide]
  · by_cases c : i < p
    · rw [if_pos c]; exact lt_of_lt_of_le (h.bdix i c) (Nat.le_add_right _ _)
    · rw [if_neg c]
      exact Nat.add_lt_add_left (g.bdix (i-p) (Nat.sub_lt_left_of_lt_add (not_lt.mp c) hi)) p
  · by_cases c : i < p
    · rw [if_pos c]; exact lt_of_lt_of_le (h.bdp i c) (Nat.le_add_right _ _)
    · rw [if_neg c]
      exact Nat.add_lt_add_left (g.bdp (i-p) (Nat.sub_lt_left_of_lt_add (not_lt.mp c) hi)) p
  · by_cases c : i < p
    · rw [if_pos c, if_pos (h.bdp i c), h.pair]
    · rw [if_neg c, if_neg (Nat.not_lt.mpr (Nat.le_add_right _ _)),
        Nat.add_sub_cancel_left, g.pair]; exact Nat.add_sub_cancel' (not_lt.mp c)
  · have hp : p ≤ i := le_trans (Nat.le_add_right p q) hi
    rw [if_neg (not_lt.mpr hp), g.awayix (i-p) (Nat.le_sub_of_add_le' hi)]
    exact Nat.add_sub_cancel' hp
  · have hp : p ≤ i := le_trans (Nat.le_add_right p q) hi
    rw [if_neg (not_lt.mpr hp), g.awayp (i-p) (Nat.le_sub_of_add_le' hi)]
    exact Nat.add_sub_cancel' hp
  · have hp : p ≤ i := le_trans (Nat.le_add_right p q) hi
    rw [if_neg (not_lt.mpr hp), g.awayd (i-p) (Nat.le_sub_of_add_le' hi)]

lemma send_sideBySide {p : ℕ} {a : Stroke} (b : Stroke) (h : a.Sound p) (x : Line) (i : ℕ) :
    (sideBySide p a b).send x i = if i < p then a.send x i else b.send (fun k => x (p+k)) (i-p) := by
  by_cases hi : i < p
  · simp [send, applyC, applyM, sideBySide, hi, h.bdp i hi]
  · have e : (p + b.partner (i-p) = i) ↔ (b.partner (i-p) = i-p) := by omega
    simp [send, applyC, applyM, sideBySide, hi, e]

end Stroke
open Stroke

structure Reel where
  beats : ℕ
  atBeat : ℕ → Stroke

namespace Reel

def reach (p : Reel) (x : Line) : ℕ → Line
  | 0 => x
  | t+1 => (p.atBeat t).send (reach p x t)

def go (p : Reel) (x : Line) := p.reach x p.beats

def Sound (p : Reel) (n : ℕ) : Prop := ∀ t<p.beats, (p.atBeat t).Sound n

namespace Sound
variable {u : Reel} {n n' : ℕ}
lemma wider (h : u.Sound n) (hn : n ≤ n') : u.Sound n' := fun t ht => (h t ht).wider hn
end Sound

def wait (d : ℕ) : Reel := ⟨d,fun _ => idStroke⟩

lemma sound_wait (d n : ℕ) : (wait d).Sound n := fun _ _ => sound_idStroke n

def tick (s : Stroke) : Reel := ⟨1,fun _ => s⟩

lemma sound_tick {s : Stroke} {n : ℕ} (h : s.Sound n) : (tick s).Sound n := fun _ _ => h

def stack (a b : Reel) : Reel :=
  ⟨a.beats+b.beats,fun i => if i<a.beats then a.atBeat i else b.atBeat (i-a.beats)⟩

lemma Sound.stack {n : ℕ} {a b : Reel} (h : a.Sound n) (g : b.Sound n) :
    (a.stack b).Sound n := fun t ht => by
  simp only [Reel.stack] at ht ⊢
  split_ifs with c
  · exact h t c
  · exact g _ (by omega)

def parallel (p : ℕ) (a b : Reel) : Reel :=
  ⟨a.beats, fun i => sideBySide p (a.atBeat i) (b.atBeat i)⟩

theorem Sound.parallel {p q : ℕ} {a b : Reel} (h : a.Sound p) (g : b.Sound q)
    (hl : a.beats=b.beats) :
    (Reel.parallel p a b).Sound (p+q) :=
  fun t ht => (h t ht).sideBySide (g t (hl ▸ ht))

def atOffset (p : ℕ) (a : Reel) : Reel := parallel p (wait a.beats) a

def scaleReel (n : ℕ) (d : Line) : Reel :=
  tick (Stroke.plain n id d)

def permReel (n : ℕ) (q : ℕ→ℕ) : Reel :=
  tick (Stroke.plain n q (fun _ => 1))

variable {p a b : Reel} {n : ℕ}

@[simp] lemma go_tick (s : Stroke) (x : Line) : (tick s).go x = s.send x := rfl

lemma go_stack (a b : Reel) (x : Line) : (a.stack b).go x = b.go (a.go x) := by
  have h1 : ∀ t ≤ a.beats, (a.stack b).reach x t = a.reach x t := fun t ht => by
    induction t with
    | zero => rfl
    | succ t ih => simp only [reach]; rw [ih (Nat.le_of_succ_le ht)]; simp [stack, show t < a.beats from ht]
  have h2 : ∀ s, (a.stack b).reach x (a.beats + s) = b.reach (a.go x) s := fun s => by
    induction s with
    | zero => exact h1 _ le_rfl
    | succ s ih => rw [← add_assoc]; simp only [reach]; rw [ih]; simp [stack]
  exact h2 b.beats

@[simp] lemma go_wait (d : ℕ) (x : Line) : (wait d).go x = x := by
  have : ∀ t, (wait d).reach x t = x := fun t => by
    induction t with
    | zero => rfl
    | succ t ih => show idStroke.send _ = _; rw [ih]; funext i; simp [send, applyC, applyM, idStroke]
  exact this d

lemma go_away (h : p.Sound n) (x : Line) {i : ℕ} (hi : n ≤ i) : p.go x i = x i := by
  have : ∀ t ≤ p.beats, p.reach x t i = x i := fun t ht => by
    induction t with
    | zero => rfl
    | succ t ih => simp only [reach]; rw [(h t (by omega)).send_away _ hi, ih (by omega)]
  exact this _ le_rfl

lemma go_parallel {q : ℕ} (h : a.Sound q) (hl : a.beats = b.beats) (x : Line) (i : ℕ) :
    (parallel q a b).go x i = if i < q then a.go x i else b.go (fun k => x (q+k)) (i-q) := by
  have H : ∀ t ≤ a.beats, (parallel q a b).reach x t =
      fun i => if i < q then a.reach x t i else b.reach (fun k => x (q+k)) t (i-q) := fun t ht => by
    induction t with
    | zero => funext i; split_ifs <;> simp only [reach]; congr 1; omega
    | succ t ih =>
      funext i
      show (sideBySide q (a.atBeat t) (b.atBeat t)).send _ i = _
      rw [send_sideBySide _ (h t ht), ih (Nat.le_of_succ_le ht)]
      split_ifs with c
      · exact (h t ht).send_congr (fun k hk => if_pos hk) c
      · congr 1; funext k; simp
  show _ = if i < q then a.reach x a.beats i else b.reach _ b.beats (i - q)
  rw [← hl]; exact congrFun (H _ le_rfl) i

lemma go_atOffset (o : ℕ) (r : Reel) (x : Line) (i : ℕ) :
    (atOffset o r).go x i = if i < o then x i else r.go (fun k => x (o+k)) (i-o) := by
  rw [atOffset, go_parallel (b := r) (sound_wait r.beats o) rfl, go_wait]

lemma scaleReel_go (n : ℕ) (d x : Line) (i : ℕ) :
    (scaleReel n d).go x i = if i < n then d i * x i else x i := plain_send n id d x i

lemma permReel_go (n : ℕ) (q : ℕ → ℕ) (x : Line) (i : ℕ) :
    (permReel n q).go x i = if i < n then x (q i) else x i := by simp [permReel, plain_send]

lemma sound_scaleReel (n : ℕ) (d : Line) : (scaleReel n d).Sound n :=
  sound_tick (plain_sound d fun _ hi => hi)

@[simp] lemma beats_stack (a b : Reel) : (a.stack b).beats = a.beats + b.beats := rfl
@[simp] lemma beats_tick (s : Stroke) : (tick s).beats = 1 := rfl
@[simp] lemma beats_parallel (q : ℕ) (a b : Reel) : (parallel q a b).beats = a.beats := rfl

end Reel
end
end PowerSaving.ReelKit
end OAI

namespace OAI
namespace PowerSaving.ReelKit
open Reel Stroke Spectral
noncomputable section

structure Zone where
  lo : ℕ
  wide : ℕ

namespace Zone

def has (u : Zone) (i : ℕ) : Prop := u.lo ≤ i ∧ i < u.lo+u.wide

instance instDecidableHas (u : Zone) (i : ℕ) : Decidable (u.has i) :=
  inferInstanceAs (Decidable (_ ∧ _))

def Fits (u : Zone) (n : ℕ) : Prop := ∀ i, u.has i → i < n

def Sep (u v : Zone) : Prop := ∀ i, u.has i → ¬ v.has i

lemma Sep.symm {u v : Zone} (h : u.Sep v) : v.Sep u := fun i h1 h2 => h i h2 h1

def peek (u : Zone) (x : Line) : Line := fun k => x (u.lo + k)

def enter (u : Zone) (T : Line → Line) (x : Line) : Line :=
  fun j => if u.has j then T (u.peek x) (j - u.lo) else x j

def slim (u : Zone) (n : ℕ) : Zone := ⟨u.lo,n⟩

lemma slim_has {u : Zone} {n i : ℕ} (hn : n ≤ u.wide) (h : (u.slim n).has i) : u.has i :=
  ⟨h.1, lt_of_lt_of_le h.2 (Nat.add_le_add_left hn _)⟩

lemma Fits.slim {u : Zone} {v n : ℕ} (h : u.Fits v) (hn : n ≤ u.wide) :
    (u.slim n).Fits v := fun i hi => h i (slim_has hn hi)

lemma has_add {u : Zone} {k : ℕ} (hk : k < u.wide) : u.has (u.lo + k) := ⟨by omega, by omega⟩

lemma not_has {u v : Zone} (h : u.Sep v) {k : ℕ} (hk : k < v.wide) : ¬ u.has (v.lo + k) :=
  fun hh => h _ hh (has_add hk)

lemma has_cases {u : Zone} {j : ℕ} (h : u.has j) : ∃ k < u.wide, j = u.lo + k :=
  ⟨j - u.lo, by have := h.1; have := h.2; omega, by have := h.1; omega⟩

end Zone
open Zone

def conjugateReel (a b c d : Reel) : Reel := ((a.stack b).stack c).stack d

def lift (D : Zone) (T : Line → Line) (x : Line) : Line :=
  fun j => if D.has j then T x (j - D.lo) else 0

lemma lift_app (Z : Zone) (T : Line → Line) (y : Line) (j : ℕ) :
    lift Z T y j = if Z.has j then T y (j - Z.lo) else 0 := rfl

def Adds (r : Reel) (D : Zone) (T : Line → Line) : Prop :=
  ∀ x j, r.go x j = if D.has j then x j + T x (j - D.lo) else x j

theorem Adds.go {r : Reel} {D : Zone} {T : Line → Line} (h : Adds r D T) (x : Line) :
    r.go x = x + lift D T x := by
  funext j; rw [h x j]; simp only [Pi.add_apply, lift]; split_ifs <;> simp

structure Acts (r : Reel) (rd wr : ℕ → Prop) (D : Line → Line) : Prop where
  go : ∀ x, r.go x = x + D x
  add : ∀ x y, D (x + y) = D x + D y
  reads : ∀ x y, (∀ j, rd j → x j = y j) → D x = D y
  writes : ∀ x j, ¬ wr j → D x j = 0

lemma lift_congr {Z : Zone} {T T' : Line → Line} (h : ∀ x k, k < Z.wide → T x k = T' x k)
    (x : Line) : lift Z T x = lift Z T' x := by
  funext j; simp only [lift]; split_ifs with hj
  · exact h _ _ (by have := hj.1; have := hj.2; omega)
  · rfl

lemma lift_neg {Z : Zone} {T T' : Line → Line} (e : ∀ x k, T' x k = -T x k) (x : Line) :
    lift Z T' x = -lift Z T x := by
  funext j; simp only [lift_app, Pi.neg_apply, e]; split_ifs <;> simp

namespace Acts
variable {r a b c d : Reel} {rd wr r2 w2 : ℕ → Prop} {D D2 : Line → Line}

theorem congr {D' : Line → Line} (h : Acts r rd wr D) (e : ∀ x, D x = D' x) : Acts r rd wr D' := by
  obtain rfl : D = D' := funext e
  exact h

theorem of {S Z : Zone} (G : Line → Line)
    (hg : Adds r Z fun x => G (S.peek x))
    (ha : ∀ x y, G (x + y) = G x + G y)
    (hr : ∀ x y, (∀ k < S.wide, x k = y k) → ∀ k < Z.wide, G x k = G y k) :
    Acts r S.has Z.has (lift Z fun x => G (S.peek x)) where
  go := hg.go
  add x y := by
    funext j; simp only [lift, Pi.add_apply]; split_ifs
    · exact congrFun (ha (S.peek x) (S.peek y)) _
    · simp
  reads x y hxy := by
    funext j; simp only [lift]; split_ifs with hj
    · exact hr _ _ (fun k hk => hxy _ (has_add hk)) _ (by have := hj.1; have := hj.2; omega)
    · rfl
  writes x j hj := if_neg hj

lemma keep (h : Acts r rd wr D) {y E : Line} (hE : ∀ j, rd j → E j = 0) : D (y + E) = D y :=
  h.reads _ _ fun j hj => by rw [Pi.add_apply, hE j hj, add_zero]

theorem conjugateReel (ha : Acts a rd wr D) (hb : Acts b r2 w2 D2)
    (hc : Acts c rd wr fun x => -D x) (hd : Acts d r2 w2 fun x => -D2 x)
    (h1 : ∀ j, rd j → ¬ wr j) (h2 : ∀ j, rd j → ¬ w2 j) (h3 : ∀ j, r2 j → ¬ w2 j) :
    Acts (ReelKit.conjugateReel a b c d) rd w2 (fun x => D2 (D x)) where
  go x := by
    have k1 : D (x + D x) = D x := ha.keep fun j hj => ha.writes x j (h1 j hj)
    have k2 : ∀ y, D (y + D2 y) = D y := fun y => ha.keep fun j hj => hb.writes y j (h2 j hj)
    have k3 : ∀ y, D2 (x + D2 y) = D2 x := fun y => hb.keep fun j hj => hb.writes y j (h3 j hj)
    simp only [ReelKit.conjugateReel, go_stack, ha.go, hb.go, hc.go, hd.go]
    rw [k2, k1, show x + D x + D2 (x + D x) + -D x = x + D2 (x + D x) by abel, k3, hb.add]; abel
  add x y := by rw [ha.add, hb.add]
  reads x y h := by rw [ha.reads x y h]
  writes x j h := hb.writes _ j h

end Acts
end
end PowerSaving.ReelKit
end OAI

namespace OAI
namespace PowerSaving.ReelKit
open Zone Reel Stroke Spectral Binary Complex Finset
noncomputable section

lemma Sep.slim_left {u v : Zone} (h : u.Sep v) {n : ℕ} (hn : n ≤ u.wide) : (u.slim n).Sep v :=
  fun i hi => h i (slim_has hn hi)

lemma enter_on (Z : Zone) (T : Line → Line) (x : Line) {k : ℕ} (hk : k < Z.wide) :
    Z.enter T x (Z.lo + k) = T (Z.peek x) k := by
  rw [enter, if_pos (has_add hk), Nat.add_sub_cancel_left]

lemma enter_off {Z Y : Zone} (h : Z.Sep Y) (T : Line → Line) (x : Line) {k : ℕ}
    (hk : k < Y.wide) : Z.enter T x (Y.lo + k) = x (Y.lo + k) := if_neg (not_has h hk)

lemma enter_off' {Z : Zone} {T : Line → Line} {x : Line} {j : ℕ} (h : ¬ Z.has j) :
    Z.enter T x j = x j := if_neg h

lemma freq_add' (n : ℕ) (u : ℂ) (a b : Line) (i : ℕ) :
    freq n u (fun m => a m + b m) i = freq n u a i + freq n u b i := by
  simp only [freq, mul_add, sum_add_distrib]

def scaleZones (u v : Zone) (f g : Line) : Reel :=
  tick ⟨id, (fun i => if u.has i then f (i-u.lo) else if v.has i then g (i-v.lo)
          else 1),id⟩

def zoneSwap (u v : Zone) (i : ℕ) :=
  if u.has i then v.lo+(i-u.lo)
  else if v.has i then u.lo+(i-v.lo) else i

def mixZones (u v : Zone) : Reel := tick ⟨id,fun _ => 1,zoneSwap u v⟩

lemma zoneSwap_u {u v : Zone} {k : ℕ} (hk : k < u.wide) : zoneSwap u v (u.lo+k) = v.lo+k := by
  rw [zoneSwap, if_pos (has_add hk), Nat.add_sub_cancel_left]

lemma zoneSwap_v {u v : Zone} (h : u.Sep v) {k : ℕ} (hk : k < v.wide) :
    zoneSwap u v (v.lo+k) = u.lo+k := by
  rw [zoneSwap, if_neg (not_has h hk), if_pos (has_add hk), Nat.add_sub_cancel_left]

lemma zoneSwap_off {u v : Zone} {j : ℕ} (h1 : ¬ u.has j) (h2 : ¬ v.has j) : zoneSwap u v j = j := by
  rw [zoneSwap, if_neg h1, if_neg h2]

lemma sound_scaleZones {u v : Zone} {n : ℕ} {f g : Line} (hu : u.Fits n) (hv : v.Fits n) :
    (scaleZones u v f g).Sound n :=
  sound_tick ⟨fun _ hi => hi, fun _ hi => hi, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun i hi => by
      simp only; rw [if_neg fun c => by have := hu i c; omega, if_neg fun c => by have := hv i c; omega]⟩

lemma sound_mixZones {u v : Zone} {n : ℕ} (hu : u.Fits n) (hv : v.Fits n) (hw : u.Sep v)
    (he : u.wide = v.wide) : (mixZones u v).Sound n := by
  refine sound_tick ⟨fun _ hi => hi, fun i hi => ?_, fun i => ?_, fun _ _ => rfl,
    fun i hi => zoneSwap_off (fun c => by have := hu i c; omega) (fun c => by have := hv i c; omega),
    fun _ _ => rfl⟩
  · show zoneSwap u v i < n
    by_cases a : u.has i
    · obtain ⟨k, hk, rfl⟩ := has_cases a; rw [zoneSwap_u hk]; exact hv _ (has_add (by omega))
    · by_cases b : v.has i
      · obtain ⟨k, hk, rfl⟩ := has_cases b; rw [zoneSwap_v hw hk]; exact hu _ (has_add (by omega))
      · rwa [zoneSwap_off a b]
  · show zoneSwap u v (zoneSwap u v i) = i
    by_cases a : u.has i
    · obtain ⟨k, hk, rfl⟩ := has_cases a; rw [zoneSwap_u hk, zoneSwap_v hw (by omega)]
    · by_cases b : v.has i
      · obtain ⟨k, hk, rfl⟩ := has_cases b; rw [zoneSwap_v hw hk, zoneSwap_u (by omega)]
      · rw [zoneSwap_off a b, zoneSwap_off a b]


def butterflyReel (u v : Zone) : Reel :=
  ((scaleZones u v (fun _ => 1) (fun _ => I)).stack (mixZones u v)).stack
    (scaleZones u v (fun _ => 1-I) (fun _ => 1+I))

def brickReel (u v : Zone) : Reel :=
  ((((butterflyReel u v).stack (scaleZones u v (fun _ => -3) (fun _ => 1))).stack
      (butterflyReel u v)).stack (scaleZones u v (fun _ => 2) (fun _ => 1))).stack (butterflyReel u v)

def addMulReel (u v : Zone) (f : Line) : Reel :=
  ((scaleZones u v (fun i => (4*f i/5)⁻¹) (fun _ => 1)).stack (brickReel u v)).stack
    (scaleZones u v (fun i => (-1/8)*(4*f i/5)) (fun _ => -1/6))

def onePlusNormSq (f : Line) : Line := fun i => 1+ f i * starRingEnd ℂ (f i)

def addScaledReel (dst src : Zone) (f : Line) : Reel :=
  (addMulReel dst src (onePlusNormSq f)).stack (addMulReel dst src (fun i => f i-onePlusNormSq f i))

lemma onePlusNormSq_ne (f : Line) (i : ℕ) : onePlusNormSq f i ≠ 0 := fun e => by
  have := congrArg Complex.re e
  simp only [onePlusNormSq, add_re, one_re, mul_conj, ofReal_re, zero_re] at this
  linarith [normSq_nonneg (f i)]

lemma sub_onePlusNormSq_ne (f : Line) (i : ℕ) : f i-onePlusNormSq f i ≠ 0 := fun e => by
  have := congrArg Complex.re e
  simp only [onePlusNormSq, sub_re, add_re, one_re, mul_conj, ofReal_re, zero_re, normSq_apply] at this
  linarith [sq_nonneg (2*(f i).re - 1), sq_nonneg (f i).im]

def PairMap (r : Reel) (u v : Zone) (f : ℕ → ℂ → ℂ → ℂ × ℂ) : Prop :=
  ∀ x, (∀ k < u.wide, r.go x (u.lo+k) = (f k (x (u.lo+k)) (x (v.lo+k))).1 ∧
      r.go x (v.lo+k) = (f k (x (u.lo+k)) (x (v.lo+k))).2) ∧
    ∀ j, ¬ u.has j → ¬ v.has j → r.go x j = x j

section
variable {u v : Zone} (hv : u.wide=v.wide) (hw : u.Sep v)
include hv hw

theorem PairMap.stack {a b : Reel} {f g : ℕ → ℂ → ℂ → ℂ × ℂ} (ha : PairMap a u v f)
    (hb : PairMap b u v g) : PairMap (a.stack b) u v (fun i p q => g i (f i p q).1 (f i p q).2) :=
  fun x => ⟨fun k hk => by
    rw [go_stack, ((hb _).1 k hk).1, ((hb _).1 k hk).2, ((ha x).1 k hk).1, ((ha x).1 k hk).2]
    exact ⟨rfl, rfl⟩, fun j h1 h2 => by rw [go_stack, (hb _).2 j h1 h2, (ha x).2 j h1 h2]⟩

omit hv hw in
theorem PairMap.congr {r : Reel} {f g : ℕ → ℂ → ℂ → ℂ × ℂ} (h : PairMap r u v f)
    (e : ∀ i p q, f i p q = g i p q) : PairMap r u v g := by
  obtain rfl : f = g := funext fun i => funext fun p => funext fun q => e i p q
  exact h

lemma scaleZones_pair (f g : Line) :
    PairMap (scaleZones u v f g) u v (fun k p q => (f k * p, g k * q)) := fun x => by
  have e : ∀ j, (scaleZones u v f g).go x j =
      (if u.has j then f (j-u.lo) else if v.has j then g (j-v.lo) else 1) * x j := fun j => by
    simp [scaleZones, send, applyC, applyM]
  refine ⟨fun k hk => ⟨?_, ?_⟩, fun j h1 h2 => ?_⟩ <;> rw [e]
  · rw [if_pos (has_add hk), Nat.add_sub_cancel_left]
  · rw [if_neg (not_has hw (by omega)), if_pos (has_add (by omega)), Nat.add_sub_cancel_left]
  · rw [if_neg h1, if_neg h2, one_mul]

lemma mixZones_pair : PairMap (mixZones u v) u v (fun _ p q => (ca*p + cb*q, ca*q + cb*p)) := fun x => by
  have e : ∀ j, (mixZones u v).go x j =
      if zoneSwap u v j = j then x j else ca * x j + cb * x (zoneSwap u v j) := fun j => by
    simp [mixZones, send, applyC, applyM]
  have d : ∀ k < u.wide, v.lo + k ≠ u.lo + k := fun k hk c =>
    hw _ (has_add hk) (by rw [← c]; exact has_add (by omega))
  refine ⟨fun k hk => ⟨?_, ?_⟩, fun j h1 h2 => ?_⟩ <;> rw [e]
  · rw [zoneSwap_u hk, if_neg (d k hk)]
  · rw [zoneSwap_v hw (by omega), if_neg (d k hk).symm]
  · rw [zoneSwap_off h1 h2, if_pos rfl]

lemma butterflyReel_pair : PairMap (butterflyReel u v) u v (fun _ p q => (p+q, p-q)) :=
  (((scaleZones_pair hv hw _ _).stack hv hw (mixZones_pair hv hw)).stack hv hw (scaleZones_pair hv hw _ _)).congr
    fun i p q => by
      simp only [ca, cb, Prod.mk.injEq]
      exact ⟨by linear_combination (-p/2 + (I-2)*q/2) * I_sq,
        by linear_combination ((I+2)*q/2 - p/2) * I_sq⟩

lemma brickReel_pair : PairMap (brickReel u v) u v (fun _ p q => (-8*p - 10*q, -6*q)) :=
  (((((butterflyReel_pair hv hw).stack hv hw (scaleZones_pair hv hw _ _)).stack hv hw (butterflyReel_pair hv hw)).stack
    hv hw (scaleZones_pair hv hw _ _)).stack hv hw (butterflyReel_pair hv hw)).congr fun i p q => by
      simp only [Prod.mk.injEq]; constructor <;> ring

lemma addMulReel_pair {f : Line} (hf : ∀ i, f i ≠ 0) :
    PairMap (addMulReel u v f) u v (fun i p q => (p + f i * q, q)) :=
  (((scaleZones_pair hv hw _ _).stack hv hw (brickReel_pair hv hw)).stack hv hw (scaleZones_pair hv hw _ _)).congr
    fun i p q => by
      simp only [Prod.mk.injEq]; have := hf i
      constructor <;> field_simp <;> ring

theorem addScaled_adds (f : Line) : Adds (addScaledReel u v f) u (fun x k => f k * v.peek x k) := by
  intro x j
  rw [addScaledReel]
  obtain ⟨h1, h2⟩ := ((addMulReel_pair hv hw (onePlusNormSq_ne f)).stack hv hw (addMulReel_pair hv hw (sub_onePlusNormSq_ne f))) x
  split_ifs with hj
  · obtain ⟨k, hk, rfl⟩ := has_cases hj
    rw [(h1 k hk).1, Nat.add_sub_cancel_left]; simp only [Zone.peek]; ring
  · by_cases c : v.has j
    · obtain ⟨k, hk, rfl⟩ := has_cases c; exact (h1 k (by omega)).2
    · exact h2 j hj c

theorem addScaled_acts (f : Line) :
    Acts (addScaledReel u v f) v.has u.has (lift u fun x k => f k * v.peek x k) :=
  Acts.of (fun z k => f k * z k) (addScaled_adds hv hw f) (fun x y => funext fun k => mul_add _ _ _)
    fun x y e k hk => by show f k * x k = f k * y k; rw [e k (by omega)]

end

section
variable {u v : Zone} {n : ℕ} (h : u.Fits n) (g : v.Fits n) (hv : u.wide=v.wide) (hw : u.Sep v)
include h g hv hw
lemma sound_butterflyReel : (butterflyReel u v).Sound n :=
  ((sound_scaleZones h g).stack (sound_mixZones h g hw hv)).stack (sound_scaleZones h g)
lemma sound_addScaled (f : Line) : (addScaledReel u v f).Sound n :=
  have hb := sound_butterflyReel h g hv hw
  have hk : (brickReel u v).Sound n :=
    ((((hb.stack (sound_scaleZones h g)).stack hb).stack (sound_scaleZones h g)).stack hb)
  have hs : ∀ f, (addMulReel u v f).Sound n := fun _ =>
    ((sound_scaleZones h g).stack hk).stack (sound_scaleZones h g)
  (hs _).stack (hs _)
end

@[simp] lemma beats_addScaled (u v : Zone) (f : Line) : (addScaledReel u v f).beats = 26 := rfl

def lowHalf (n : ℕ) : Zone := ⟨0,n⟩
def highHalf (n : ℕ) : Zone := ⟨n,n⟩

lemma lowHalf_sep (n : ℕ) : (lowHalf n).Sep (highHalf n) :=
  fun i (h1 : 0 ≤ i ∧ i < 0 + n) (h2 : n ≤ i ∧ i < n + n) => by omega

def evenOddIndex (n i : ℕ) := if i<n then 2*i else 2*(i-n)+1

def fftCombine (n : ℕ) (u : ℂ) : Reel :=
  (scaleZones (lowHalf n) (highHalf n) (fun _ => 1) (fun i => u^i)).stack
    (butterflyReel (lowHalf n) (highHalf n))

def fftStep (n : ℕ) (u : ℂ) (r : Reel) : Reel :=
  ((permReel (n+n) (evenOddIndex n)).stack (parallel n r r)).stack (fftCombine n u)

def fftReel : ℕ → ℂ → Reel
  | 0,_ => wait 0
  | d+1,u => fftStep (2^d) u (fftReel d (u^2))

lemma sound_fftReel (d : ℕ) (u : ℂ) : (fftReel d u).Sound (2^d) := by
  induction d generalizing u with
  | zero => exact sound_wait 0 _
  | succ d ih =>
    rw [pow_succ, mul_two]
    have h1 : (lowHalf (2^d)).Fits (2^d+2^d) := fun i hi => by simp only [Zone.has, lowHalf] at hi; omega
    have h2 : (highHalf (2^d)).Fits (2^d+2^d) := fun i hi => by simp only [Zone.has, highHalf] at hi; omega
    exact ((sound_tick (plain_sound _ fun i hi => by unfold evenOddIndex; split <;> omega)).stack
      (Sound.parallel (ih _) (ih _) rfl)).stack
      ((sound_scaleZones h1 h2).stack (sound_butterflyReel h1 h2 rfl (lowHalf_sep _)))

lemma beats_fftReel (d : ℕ) (u : ℂ) : (fftReel d u).beats=5*d := by
  induction d generalizing u with
  | zero => rfl
  | succ d ih =>
    show (fftStep (2^d) u (fftReel d (u^2))).beats = _
    simp only [fftStep, fftCombine, butterflyReel, permReel, scaleZones, mixZones, beats_stack, beats_tick,
      beats_parallel, ih]; ring

def inverseFftReel (d : ℕ) (u : ℂ) : Reel :=
  (fftReel d u⁻¹).stack (scaleReel (2^d) (fun _ => (((2^d:ℕ):ℂ))⁻¹))

lemma fftReel_go {d : ℕ} {u : ℂ} (hu : PrimRoot u (2^d)) (x : Line) {i : ℕ} (hi : i < 2^d) :
    (fftReel d u).go x i = freq (2^d) u x i := by
  induction d generalizing u x i with
  | zero =>
    obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
    simp [fftReel, freq]
  | succ d ih =>
    rw [pow_succ, mul_two] at hu hi ⊢
    rw [fftReel, fftStep, go_stack, go_stack]
    have hs := sound_fftReel d (u^2)
    have hpos : 0 < 2^d := Nat.two_pow_pos d
    have hu2 := even_prim hu
    generalize 2^d = n at *
    set Y := (parallel n (fftReel d (u^2)) (fftReel d (u^2))).go ((permReel (n+n) (evenOddIndex n)).go x) with hY
    have E : ∀ k < n, Y k = freq n (u^2) (fun j => x (2*j)) k := fun k hk => by
      rw [hY, go_parallel hs rfl, if_pos hk, ih hu2 _ hk]
      exact congrFun (freq_congr (fun j hj => by rw [permReel_go, if_pos (by omega)]; simp [evenOddIndex, hj]) _) k
    have O : ∀ k < n, Y (n+k) = freq n (u^2) (fun j => x (2*j+1)) k := fun k hk => by
      rw [hY, go_parallel hs rfl, if_neg (Nat.not_lt.mpr (Nat.le_add_right _ _)), Nat.add_sub_cancel_left, ih hu2 _ hk]
      exact congrFun (freq_congr (fun j hj => by rw [permReel_go, if_pos (by omega)]; simp [evenOddIndex]) _) k
    have T := (PairMap.stack (u := lowHalf n) (v := highHalf n) rfl (lowHalf_sep n)
      (scaleZones_pair (u := lowHalf n) (v := highHalf n) rfl (lowHalf_sep n) (fun _ => 1) (fun i => u^i))
      (butterflyReel_pair rfl (lowHalf_sep n)) Y).1
    by_cases c : i < n
    · have := (T i c).1; simp only [lowHalf, highHalf, zero_add] at this
      refine this.trans ?_; rw [E i c, O i c, freq_eo]; ring
    · obtain ⟨k, rfl⟩ : ∃ k, i = n + k := ⟨i - n, (Nat.add_sub_cancel' (not_lt.mp c)).symm⟩
      have hk : k < n := Nat.lt_of_add_lt_add_left hi
      have := (T k hk).2; simp only [lowHalf, highHalf, zero_add] at this
      refine this.trans ?_; rw [E k hk, O k hk, freq_eo' hpos hu]; ring

lemma sound_inverseFftReel (d : ℕ) (u : ℂ) : (inverseFftReel d u).Sound (2^d) :=
  (sound_fftReel d _).stack (sound_scaleReel _ _)

lemma inverseFftReel_go {d : ℕ} {u : ℂ} (hu : PrimRoot u (2^d)) (x : Line) {i : ℕ} (hi : i < 2^d) :
    (inverseFftReel d u).go x i = ((2^d:ℕ):ℂ)⁻¹ * freq (2^d) u⁻¹ x i := by
  rw [inverseFftReel, go_stack, scaleReel_go, if_pos hi, fftReel_go hu.inv x hi]

lemma atOffset_enter {P : Reel} {Z : Zone} {T : Line → Line} (hP : P.Sound Z.wide)
    (hT : ∀ y i, i < Z.wide → P.go y i = T y i) (x : Line) :
    (atOffset Z.lo P).go x = Z.enter T x := by
  funext j; rw [go_atOffset, Zone.enter]
  by_cases a : j < Z.lo
  · rw [if_pos a, if_neg (show ¬ Z.has j from fun h => by have := h.1; omega)]
  · rw [if_neg a]
    by_cases c : j < Z.lo + Z.wide
    · rw [if_pos (show Z.has j from ⟨by omega, c⟩)]; exact hT _ _ (by omega)
    · rw [if_neg (show ¬ Z.has j from fun h => by have := h.2; omega), go_away hP _ (by omega)]
      show x (Z.lo + (j - Z.lo)) = x j; congr 1; omega

def cyclicConvReel (d : ℕ) (r : ℂ) (u v : Zone) (h : Line) : Reel :=
  let p := fftReel d r; let b := inverseFftReel d r
  let f := addScaledReel v u (freq (2^d) r h)
  ((((atOffset u.lo p).stack (atOffset v.lo p)).stack f).stack (atOffset u.lo b)).stack
    (atOffset v.lo b)

lemma cyclic_neg (n : ℕ) (h x : Line) : cyclic n (fun i => -h i) x = -cyclic n h x := by
  funext i; simp [cyclic, sum_neg_distrib]

section
variable {d : ℕ} {r : ℂ} {u v : Zone} (hr : PrimRoot r (2^d)) (hu : u.wide = 2^d)
  (hv : v.wide = 2^d) (huv : u.Sep v)
include hr hu hv huv

lemma conv_acts (h : Line) :
    Acts (cyclicConvReel d r u v h) u.has v.has (lift v fun x => cyclic (2^d) h (u.peek x)) := by
  have hB : ∀ {Z : Zone}, Z.wide = 2^d → ∀ y, (atOffset Z.lo (fftReel d r)).go y =
      Z.enter (freq (2^d) r) y ∧ (atOffset Z.lo (inverseFftReel d r)).go y =
      Z.enter (fun z i => ((2^d:ℕ):ℂ)⁻¹ * freq (2^d) r⁻¹ z i) y := fun hZ y =>
    ⟨atOffset_enter (hZ ▸ sound_fftReel d r) (fun y i hi => fftReel_go hr y (hZ ▸ hi)) y,
     atOffset_enter (hZ ▸ sound_inverseFftReel d r) (fun y i hi => inverseFftReel_go hr y (hZ ▸ hi)) y⟩
  have hF := addScaled_adds (hv.trans hu.symm) huv.symm (freq (2^d) r h)
  refine Acts.of (fun z => cyclic (2^d) h z) (fun x j => ?_)
    (fun x y => by funext i; simp only [cyclic, Pi.add_apply, mul_add, sum_add_distrib])
    (fun x y e k _ => sum_congr rfl fun j hj => by
      rw [e j ((mem_range.mp hj).trans_eq hu.symm)])
  simp only [cyclicConvReel, go_stack, (hB hu _).1, (hB hv _).1, (hB hu _).2, (hB hv _).2]
  set IF := fun z i => ((2^d:ℕ):ℂ)⁻¹ * freq (2^d) r⁻¹ z i
  set s2 := v.enter (freq (2^d) r) (u.enter (freq (2^d) r) x) with hs2
  set s3 := (addScaledReel v u (freq (2^d) r h)).go s2 with hs3
  have f1 : ∀ m < 2^d, s2 (u.lo + m) = freq (2^d) r (u.peek x) m := fun m hm => by
    rw [hs2, enter_off huv.symm _ _ (hm.trans_eq hu.symm), enter_on _ _ _ (hm.trans_eq hu.symm)]
  have f2 : ∀ m < 2^d, s2 (v.lo + m) = freq (2^d) r (v.peek x) m := fun m hm => by
    rw [hs2, enter_on _ _ _ (hm.trans_eq hv.symm)]
    exact congrFun (freq_congr (fun i hi => enter_off huv _ _ (hi.trans_eq hv.symm)) _) m
  have f3 : ∀ m < 2^d, s3 (v.lo + m) = s2 (v.lo + m) + freq (2^d) r h m * s2 (u.lo + m) :=
    fun m hm => by rw [hs3, hF, if_pos (has_add (hm.trans_eq hv.symm)), Nat.add_sub_cancel_left] <;> rfl
  have f4 : ∀ m < 2^d, s3 (u.lo + m) = s2 (u.lo + m) := fun m hm => by
    rw [hs3, hF, if_neg (not_has huv.symm (hm.trans_eq hu.symm))]
  by_cases hvj : v.has j
  · obtain ⟨k, hk, rfl⟩ := has_cases hvj
    have e : ∀ m < 2^d, v.peek (u.enter IF s3) m =
        freq (2^d) r (v.peek x) m + freq (2^d) r h m * freq (2^d) r (u.peek x) m := fun m hm => by
      show u.enter IF s3 (v.lo + m) = _
      rw [enter_off huv _ _ (hm.trans_eq hv.symm), f3 m hm, f2 m hm, f1 m hm]
    rw [if_pos hvj, enter_on _ _ _ hk, Nat.add_sub_cancel_left]
    show _ * freq _ _ _ k = _
    rw [freq_congr e, freq_add', mul_add, freq_inv hr _ k (hk.trans_eq hv),
      Spectral.cyc_formula hr _ h (i := k) (hk.trans_eq hv)] <;> rfl
  · rw [if_neg hvj, enter_off' hvj]
    by_cases huj : u.has j
    · obtain ⟨k, hk, rfl⟩ := has_cases huj
      rw [enter_on _ _ _ hk]
      show _ * freq _ _ _ k = _
      rw [freq_congr (x := u.peek s3) (fun m hm => (f4 m hm).trans (f1 m hm)),
        freq_inv hr _ k (hk.trans_eq hu)] <;> rfl
    · rw [enter_off' huj, hs3, hF, if_neg hvj, hs2, enter_off' hvj, enter_off' huj]

lemma conv_neg (h : Line) : Acts (cyclicConvReel d r u v (fun i => -h i)) u.has v.has
    (fun x => -lift v (fun x => cyclic (2^d) h (u.peek x)) x) :=
  (conv_acts hr hu hv huv _).congr (lift_neg fun _ _ => by simp [cyclic_neg])

end
end
end PowerSaving.ReelKit
end OAI

namespace OAI
namespace PowerSaving.ReelKit
open Reel Stroke Zone Spectral Finset Matrix
noncomputable section

def copyInReel (u a : Zone) (t : ℂ) : Reel :=
  addScaledReel (a.slim u.wide) u (fun _ => t)

def copyOutReel (a v : Zone) (t : ℂ) : Reel :=
  addScaledReel v (a.slim v.wide) (fun _ => t)

def pad (w : ℕ) (z : Line) : Line := fun k => if k < w then z k else 0

def paddedConvReel (d : ℕ) (r : ℂ) (u a b : Zone) (h : Line) : Reel :=
  conjugateReel (copyInReel u a 1) (cyclicConvReel d r a b h) (copyInReel u a (-1))
    (cyclicConvReel d r a b (fun i => -h i))

def blockConvReel (d : ℕ) (r : ℂ) (u v a b : Zone) (h : Line) : Reel :=
  conjugateReel (paddedConvReel d r u a b h) (copyOutReel b v 1)
    (paddedConvReel d r u a b (fun i => -h i)) (copyOutReel b v (-1))

def blockFilter (b e s l m : ℕ) (h : Line) : Line :=
  fun k =>
    if k<b then
      if k<s then rise h (m+k) l else 0
    else
      if 0<s ∧ 2*b-k<e then rise h m (l+(2*b-k)) else 0

def toeplitzBlockReel (k : ℕ) (r : ℂ) (u v a b : Zone) (l m : ℕ) (h : Line) : Reel :=
  blockConvReel (k+1) r u v a b (blockFilter (2^k) u.wide v.wide l m h)

lemma rise_neg (h : Line) (i j : ℕ) : rise (fun i => -h i) i j = -rise h i j := by
  unfold rise; split_ifs <;> simp

lemma copyInReel_acts {u a : Zone} (hu : u.wide ≤ a.wide) (hua : u.Sep a) (t : ℂ) :
    Acts (copyInReel u a t) u.has (a.slim u.wide).has (lift (a.slim u.wide) fun x k => t * u.peek x k) :=
  addScaled_acts (u := a.slim u.wide) (v := u) rfl (Sep.slim_left hua.symm hu) (fun _ => t)

lemma copyOutReel_acts {b v : Zone} (hv : v.wide ≤ b.wide) (hvb : v.Sep b) (t : ℂ) :
    Acts (copyOutReel b v t) (b.slim v.wide).has v.has (lift v fun x k => t * (b.slim v.wide).peek x k) :=
  addScaled_acts (u := v) (v := b.slim v.wide) rfl (Sep.slim_left hvb.symm hv).symm (fun _ => t)

section
variable {d : ℕ} {r : ℂ} {u v a b : Zone} (hr : PrimRoot r (2^d)) (ha : a.wide = 2^d)
  (hb : b.wide = 2^d) (hab : a.Sep b) (hu : u.wide ≤ a.wide) (hua : u.Sep a) (hub : u.Sep b)
include hr ha hb hab hu hua hub

lemma paddedConvReel_acts (h : Line) : Acts (paddedConvReel d r u a b h) u.has b.has
    (lift b fun x => cyclic (2^d) h (pad u.wide (u.peek x))) := by
  refine (Acts.conjugateReel (copyInReel_acts hu hua 1) (conv_acts hr ha hb hab h)
    ((copyInReel_acts hu hua (-1)).congr (lift_neg fun _ _ => by ring)) (conv_neg hr ha hb hab h)
    (Sep.slim_left hua.symm hu).symm hub hab).congr fun x => ?_
  beta_reduce
  have e : a.peek (lift (a.slim u.wide) (fun x k => 1 * u.peek x k) x) = pad u.wide (u.peek x) := by
    funext k; by_cases hk : k < u.wide <;> simp [Zone.peek, lift, Zone.slim, Zone.has, pad, hk]
  funext j; rw [lift_app, lift_app, e]

lemma paddedConvReel_neg (h : Line) : Acts (paddedConvReel d r u a b (fun i => -h i)) u.has b.has
    (fun x => -lift b (fun x => cyclic (2^d) h (pad u.wide (u.peek x))) x) :=
  (paddedConvReel_acts hr ha hb hab hu hua hub _).congr (lift_neg fun _ _ => by simp [cyclic_neg])

lemma blockConvReel_acts (hv : v.wide ≤ b.wide) (hvb : v.Sep b) (huv : u.Sep v) (h : Line) :
    Acts (blockConvReel d r u v a b h) u.has v.has
      (lift v fun x => cyclic (2^d) h (pad u.wide (u.peek x))) := by
  refine (Acts.conjugateReel (paddedConvReel_acts hr ha hb hab hu hua hub h) (copyOutReel_acts hv hvb 1)
    (paddedConvReel_neg hr ha hb hab hu hua hub h) ((copyOutReel_acts hv hvb (-1)).congr (lift_neg fun _ _ => by ring))
    hub huv (Sep.slim_left hvb.symm hv)).congr fun x => ?_
  beta_reduce
  funext j; rw [lift_app, lift_app]; split_ifs with hj
  · have hk : j - v.lo < b.wide := by have := hj.1; have := hj.2; omega
    show 1 * lift b _ x (b.lo + (j - v.lo)) = _
    rw [lift_app, if_pos (has_add hk), Nat.add_sub_cancel_left, one_mul]
  · rfl

end

lemma blockFilter_cyclic {b e s l m i : ℕ} (h : Line) (he : e ≤ b) (hi : i < s) (hs : s ≤ b) (z : Line) :
    cyclic (2*b) (blockFilter b e s l m h) (pad e z) i = ∑ j ∈ range e, rise h (m+i) (l+j) * z j := by
  unfold cyclic pad
  simp only [mul_ite, mul_zero]
  rw [Spectral.range_pad e (2*b) (le_trans he (Nat.le_mul_of_pos_left b (by norm_num)))]
  refine sum_congr rfl fun j hj => ?_
  have hj := mem_range.mp hj
  congr 1
  unfold predAt blockFilter
  by_cases hji : j ≤ i
  · have c : (l ≤ m + (i-j)) ↔ (l + j ≤ m + i) := by
      rw [← Nat.add_sub_assoc hji, Nat.le_sub_iff_add_le (le_trans hji (Nat.le_add_left _ _))]
    have e1 : m + (i-j) - l = m + i - (l+j) := by
      rw [← Nat.add_sub_assoc hji, Nat.sub_sub, add_comm j l]
    have hb : i - j < b := lt_of_le_of_lt (Nat.sub_le _ _) (lt_of_lt_of_le hi hs)
    have hs' : i - j < s := lt_of_le_of_lt (Nat.sub_le _ _) hi
    simp only [hji, ↓reduceIte, hb, hs', rise, c, e1]
  · have hij : i ≤ j := (Nat.lt_of_not_le hji).le
    have c : (l + (j-i) ≤ m) ↔ (l + j ≤ m + i) := by
      rw [← Nat.add_sub_assoc hij, Nat.sub_le_iff_le_add]
    have hjb : j ≤ b := hj.le.trans he
    have h2 : b + j ≤ i + 2*b := by
      rw [two_mul]; exact (Nat.add_le_add_left hjb b).trans (Nat.le_add_left _ _)
    have h2' : j ≤ i + 2*b := le_trans (Nat.le_add_left j b) h2
    have e1 : m - (l + (j-i)) = m + i - (l+j) := by
      rw [← Nat.add_sub_assoc hij, tsub_tsub_eq_add_tsub_of_le (le_trans hij (Nat.le_add_left _ _))]
    have e2 : 2*b - (i + 2*b - j) = j - i := by
      rw [tsub_tsub_eq_add_tsub_of_le h2', add_comm i, Nat.add_sub_add_left]
    simp only [hji, ↓reduceIte, show ¬ i + 2*b - j < b from not_lt.mpr ((Nat.le_sub_iff_add_le h2').mpr h2), e2,
      show (0 < s ∧ j - i < e) ↔ True from ⟨fun _ => trivial, fun _ => ⟨lt_of_le_of_lt (Nat.zero_le _) hi,
        lt_of_le_of_lt (Nat.sub_le _ _) hj⟩⟩,
      rise, c, e1]

def blockOp (w l m : ℕ) (h : Line) (z : Line) (i : ℕ) : ℂ :=
  ∑ j ∈ range w, rise h (m+i) (l+j) * z j

section
variable {k : ℕ} {r : ℂ} {u v a b : Zone} (hr : PrimRoot r (2^(k+1))) (ha : a.wide = 2^(k+1))
  (hb : b.wide = 2^(k+1)) (hab : a.Sep b) (hu : u.wide ≤ 2^k) (hua : u.Sep a) (hub : u.Sep b)
  (hv : v.wide ≤ 2^k) (hvb : v.Sep b) (huv : u.Sep v)
include hr ha hb hab hu hua hub hv hvb huv

lemma block_acts (l m : ℕ) (h : Line) : Acts (toeplitzBlockReel k r u v a b l m h) u.has v.has
    (lift v fun x => blockOp u.wide l m h (u.peek x)) := by
  have h2 : 2^k ≤ 2^(k+1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine (blockConvReel_acts hr ha hb hab (by omega) hua hub (by omega) hvb huv _).congr
    fun x => lift_congr (fun x i hi => ?_) x
  rw [pow_succ']; exact blockFilter_cyclic h hu hi hv _

lemma block_neg (l m : ℕ) (h : Line) :
    Acts (toeplitzBlockReel k r u v a b l m (fun i => -h i)) u.has v.has
    (fun x => -lift v (fun x => blockOp u.wide l m h (u.peek x)) x) :=
  (block_acts hr ha hb hab hu hua hub hv hvb huv l m _).congr (lift_neg fun _ _ => by
    simp [blockOp, rise_neg])

end

def concatReels (a : ℕ → Reel) : ℕ → Reel
  | 0 => wait 0
  | i+1 => (concatReels a i).stack (a i)

lemma beats_concatReels {a : ℕ→Reel} (n d : ℕ) (h : ∀ i<n,(a i).beats=d) :
    (concatReels a n).beats=n*d := by
  induction n with
  | zero => simp [concatReels, wait]
  | succ n ih =>
    show (concatReels a n).beats + (a n).beats = _
    rw [ih (fun i hi => h i (by omega)), h n (by omega)]; ring

lemma sound_concatReels {a : ℕ → Reel} {n N : ℕ} (h : ∀ i < n, (a i).Sound N) : (concatReels a n).Sound N := by
  induction n with
  | zero => exact sound_wait 0 N
  | succ n ih => exact (ih fun i hi => h i (by omega)).stack (h n (by omega))

def blockZone (b j : ℕ) : Zone := ⟨j*b,b⟩
def outZone (p w b s : ℕ) : Zone := ⟨p+s*b,min b (w-s*b)⟩

def tripleConcat (a : ℕ → ℕ → ℕ → Reel) (l : ℕ) : Reel :=
  concatReels (fun s => concatReels (fun c => concatReels (fun j => a s c j) l) l) l

def Gains (r : Reel) (P : ℕ) (D : Line → Line) : Prop :=
  ∀ x, r.go x = x + D x ∧ (∀ i < P, D x i = 0) ∧ ∀ y, (∀ i < P, x i = y i) → D x = D y

theorem Gains.congr {r : Reel} {P : ℕ} {D D' : Line → Line} (h : Gains r P D)
    (e : ∀ x, D x = D' x) : Gains r P D' := by
  obtain rfl : D = D' := funext e
  exact h

lemma Acts.gains {r : Reel} {rd wr : ℕ → Prop} {D : Line → Line} {P : ℕ} (h : Acts r rd wr D)
    (hr : ∀ j, rd j → j < P) (hw : ∀ j, wr j → P ≤ j) : Gains r P D := fun x =>
  ⟨h.go x, fun i hi => h.writes x i (fun hh => by have := hw i hh; omega),
    fun y hy => h.reads x y (fun j hj => hy j (hr j hj))⟩

lemma concatReels_gains {a : ℕ → Reel} {D : ℕ → Line → Line} {P n : ℕ}
    (h : ∀ i < n, Gains (a i) P (D i)) : Gains (concatReels a n) P (fun x => ∑ i ∈ range n, D i x) := by
  induction n with
  | zero => exact fun x => ⟨by simp [concatReels], fun _ _ => by simp, fun _ _ => by simp⟩
  | succ n ih =>
    intro x
    obtain ⟨g1, g2, g3⟩ := ih (fun i hi => h i (by omega)) x
    obtain ⟨f1, f2, f3⟩ := h n (by omega) x
    simp only at g1 g2 g3
    simp only [sum_range_succ]
    refine ⟨?_, fun i hi => by rw [Pi.add_apply, g2 i hi, f2 i hi, add_zero],
      fun y e => by rw [g3 y e, f3 y e]⟩
    rw [concatReels, go_stack, (h n (by omega) _).1, g1, (h n (by omega) (x + ∑ i ∈ range n, D i x)).2.2 x
      fun i hi => by rw [Pi.add_apply, g2 i hi, add_zero], add_assoc]

lemma tripleConcat_gains {a : ℕ → ℕ → ℕ → Reel} {l P : ℕ} {D : ℕ → ℕ → ℕ → Line → Line}
    (h : ∀ s < l, ∀ c < l, ∀ j < l, Gains (a s c j) P (D s c j)) :
    Gains (tripleConcat a l) P (fun x => ∑ s ∈ range l, ∑ c ∈ range l, ∑ j ∈ range l, D s c j x) :=
  concatReels_gains fun s hs => concatReels_gains fun c hc => concatReels_gains fun j hj => h s hs c hc j hj


def scratchBase (b j : ℕ) := if j<8 then 8*b else 0
def scratchZone (b j : ℕ) : Zone := ⟨scratchBase b j, b⟩
def convZoneA (b j : ℕ) : Zone := ⟨scratchBase b j + b, 2*b⟩
def convZoneB (b j : ℕ) : Zone := ⟨scratchBase b j + 3*b,2*b⟩

structure ZonesApart (p : ℕ) (u v z l m : Zone) : Prop where
  fitsU : u.Fits p
  fitsV : v.Fits p
  fitsZ : z.Fits p
  fitsL : l.Fits p
  fitsM : m.Fits p
  uz : u.Sep z
  ul : u.Sep l
  um : u.Sep m
  lm : l.Sep m
  zl : z.Sep l
  zm : z.Sep m
  uv : u.Sep v
  zv : z.Sep v
  vm : v.Sep m

def toeplitzPairReel (k : ℕ) (r : ℂ) (u v z l m : Zone) (b e y : ℕ) (h g : Line) : Reel :=
  conjugateReel (toeplitzBlockReel k r u z l m b e g) (toeplitzBlockReel k r z v l m e y h)
    (toeplitzBlockReel k r u z l m b e (fun i => -g i)) (toeplitzBlockReel k r z v l m e y (fun i => -h i))

structure ZoneWidths (k : ℕ) (u v z l m : Zone) : Prop where
  uw : u.wide ≤ 2^k
  vw : v.wide ≤ 2^k
  zw : z.wide ≤ 2^k
  lw : l.wide=2^(k+1)
  mw : m.wide=2^(k+1)

lemma pairReel_acts {k n : ℕ} {r : ℂ} {u v z l m : Zone} (b e y : ℕ) (h g : Line)
    (hr : PrimRoot r (2^(k+1))) (H : ZoneWidths k u v z l m) (hf : ZonesApart n u v z l m) :
    Acts (toeplitzPairReel k r u v z l m b e y h g) u.has v.has (lift v fun x i =>
      ∑ c ∈ range z.wide, rise h (y+i) (e+c) * ∑ j ∈ range u.wide, rise g (e+c) (b+j) * u.peek x j) := by
  refine (Acts.conjugateReel (block_acts hr H.lw H.mw hf.lm H.uw hf.ul hf.um H.zw hf.zm hf.uz b e g)
    (block_acts hr H.lw H.mw hf.lm H.zw hf.zl hf.zm H.vw hf.vm hf.zv e y h)
    (block_neg hr H.lw H.mw hf.lm H.uw hf.ul hf.um H.zw hf.zm hf.uz b e g)
    (block_neg hr H.lw H.mw hf.lm H.zw hf.zl hf.zm H.vw hf.vm hf.zv e y h)
    hf.uz hf.uv hf.zv).congr fun x => ?_
  beta_reduce
  funext j; rw [lift_app, lift_app]; split_ifs
  · refine sum_congr rfl fun c hc => ?_
    show _ * lift z _ x (z.lo + c) = _
    rw [lift_app, if_pos (has_add (mem_range.mp hc)), Nat.add_sub_cancel_left] <;> rfl
  · rfl

def toeplitzGridCell (k : ℕ) (r : ℂ) (w : ℕ) (h g : Line) (s c j : ℕ) : Reel :=
  let b := 2^k
  let p := 16*b
  toeplitzPairReel k r (blockZone b j) (outZone p w b s) (scratchZone b j) (convZoneA b j)
    (convZoneB b j) (j*b) (c*b) (p+s*b) h g

def toeplitzGridReel (k : ℕ) (r : ℂ) (w : ℕ) (h g : Line) : Reel :=
  tripleConcat (toeplitzGridCell k r w h g) 16

lemma beats_conv (d : ℕ) (r : ℂ) (u v : Zone) (h : Line) :
    (cyclicConvReel d r u v h).beats = 20*d+28 := by
  show (fftReel d r).beats + (fftReel d r).beats + 26 + ((fftReel d r⁻¹).beats + 1)
    + ((fftReel d r⁻¹).beats + 1) = _
  rw [beats_fftReel, beats_fftReel]; ring

lemma beats_blockConvReel (d : ℕ) (r : ℂ) (u v a b : Zone) (h : Line) :
    (blockConvReel d r u v a b h).beats = 80*d+268 := by
  simp only [blockConvReel, paddedConvReel, conjugateReel, copyInReel, copyOutReel, beats_stack, beats_addScaled, beats_conv]; ring

lemma beats_toeplitzGridCell (k : ℕ) (r : ℂ) (w : ℕ) (h g : Line) (s c j : ℕ) :
    (toeplitzGridCell k r w h g s c j).beats=4*(80*k+348) := by
  simp only [toeplitzGridCell, toeplitzPairReel, toeplitzBlockReel, conjugateReel, beats_stack, beats_blockConvReel]
  ring

def naiveToeplitzCell (p w : ℕ) (h g : Line) (s c j : ℕ) : Reel :=
  if s<w then addScaledReel (outZone p w 1 s) (blockZone 1 j) (fun _ => rise h (p+s) c*rise g c j)
  else wait 26

def naiveToeplitzReel (p w : ℕ) (h g : Line) : Reel := tripleConcat (naiveToeplitzCell p w h g) p

lemma beats_naiveToeplitzCell (p w : ℕ) (h g : Line) (s c j : ℕ) :
    (naiveToeplitzCell p w h g s c j).beats=26 := by
  unfold naiveToeplitzCell; split_ifs <;> rfl

lemma beats_tripleConcat {a : ℕ → ℕ → ℕ → Reel} {l d : ℕ} (h : ∀ s c j, (a s c j).beats = d) :
    (tripleConcat a l).beats = l*(l*(l*d)) :=
  beats_concatReels _ _ fun _ _ => beats_concatReels _ _ fun _ _ => beats_concatReels _ _ fun _ _ => h _ _ _

def bridgeOp (p w : ℕ) (h g : Line) (x : Line) (i : ℕ) : ℂ :=
  if p ≤ i ∧ i < p + w then toeplitzApply p h (toeplitzApply p g x) i else 0

lemma naive_gains {p w : ℕ} (h g : Line) (hw : w ≤ p) :
    Gains (naiveToeplitzReel p w h g) p (bridgeOp p w h g) := by
  have cell : ∀ s < p, ∀ c < p, ∀ j < p, Gains (naiveToeplitzCell p w h g s c j) p
      (fun x i => if s < w ∧ i = p + s then rise h (p+s) c * rise g c j * x j else 0) := by
    intro s _ c _ j hj
    unfold naiveToeplitzCell; split_ifs with hs
    · have hm : min 1 (w - s) = 1 := min_eq_left (Nat.sub_pos_of_lt hs)
      have hj1 : j*1 + 1 ≤ p := by rw [mul_one]; exact hj
      refine ((addScaled_acts (u := outZone p w 1 s) (v := blockZone 1 j)
        (show min 1 (w - s*1) = 1 by rw [mul_one]; exact hm)
        (fun i (h1 : p + s*1 ≤ i ∧ _) (h2 : j*1 ≤ i ∧ i < j*1 + 1) =>
          absurd (le_trans (Nat.le_add_right _ _) h1.1) (Nat.not_le_of_lt (lt_of_lt_of_le h2.2 hj1))) _).gains
        (fun i (q : j*1 ≤ i ∧ i < j*1 + 1) => lt_of_lt_of_le q.2 hj1)
        (fun i (q : p + s*1 ≤ i ∧ _) => le_trans (Nat.le_add_right _ _) q.1)).congr
        fun x => funext fun i => ?_
      simp only [lift, Zone.has, outZone, blockZone, Zone.peek, mul_one]
      by_cases hi : i = p + s
      · subst hi; rw [if_pos ⟨le_rfl, by rw [hm]; exact Nat.lt_succ_self _⟩, if_pos ⟨hs, rfl⟩]; simp
      · rw [if_neg fun h => hi (le_antisymm (Nat.le_of_lt_succ (by rw [hm] at h; exact h.2)) h.1),
          if_neg fun h => hi h.2]
    · exact fun x => ⟨by funext i; simp [hs], fun _ _ => by simp [hs],
        fun _ _ => by funext i; simp [hs]⟩
  refine (tripleConcat_gains cell).congr fun x => funext fun i => ?_
  simp only [Finset.sum_apply, bridgeOp]
  split_ifs with hi
  · rw [sum_eq_single (i - p) (fun s _ hs => sum_eq_zero fun c _ =>
      sum_eq_zero fun j _ => if_neg fun h => hs (by rw [h.2, Nat.add_sub_cancel_left]))
      (fun h' => absurd (mem_range.2
      (Nat.sub_lt_left_of_lt_add hi.1 (lt_of_lt_of_le hi.2 (Nat.add_le_add_left hw p)))) h')]
    simp only [toeplitzApply, Finset.mul_sum]
    refine sum_congr rfl fun c _ => sum_congr rfl fun j _ => ?_
    rw [if_pos (show i - p < w ∧ i = p + (i - p) from
      ⟨Nat.sub_lt_left_of_lt_add hi.1 hi.2, (Nat.add_sub_cancel' hi.1).symm⟩), Nat.add_sub_cancel' hi.1]; ring
  · exact sum_eq_zero fun s _ => sum_eq_zero fun c _ => sum_eq_zero
      fun j _ => if_neg fun h => hi (by rw [h.2]; exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left h.1 _⟩)

lemma fits_of {u : Zone} {n : ℕ} (h : u.lo + u.wide ≤ n) : u.Fits n :=
  fun i hi => by have := hi.2; omega

lemma cell_zones {k w s j : ℕ} (hs : s < 16) (hj : j < 16) (hw : w ≤ 16*2^k) :
    ZoneWidths k (blockZone (2^k) j) (outZone (16*2^k) w (2^k) s) (scratchZone (2^k) j) (convZoneA (2^k) j)
      (convZoneB (2^k) j) ∧
    ZonesApart (16*2^k + w) (blockZone (2^k) j) (outZone (16*2^k) w (2^k) s) (scratchZone (2^k) j)
      (convZoneA (2^k) j) (convZoneB (2^k) j) := by
  refine ⟨⟨le_rfl, min_le_left _ _, le_rfl, by show 2 * 2^k = 2^(k+1); ring,
    by show 2 * 2^k = 2^(k+1); ring⟩, ?_⟩
  generalize 2^k = b at hw ⊢
  have sep : ∀ {u v : Zone}, u.lo + u.wide ≤ v.lo ∨ v.lo + v.wide ≤ u.lo → u.Sep v :=
    fun h i h1 h2 => by unfold Zone.has at h1 h2; omega
  have fV : (outZone (16*b) w b s).Fits (16*b + w) :=
    fun i (hi : 16*b + s*b ≤ i ∧ i < 16*b + s*b + min b (w - s*b)) => by clear hs hj hw; omega
  obtain ⟨M1, M2, M4, M6, M7, M8, M9, M10⟩ : b ≤ 3*b ∧ b+2*b ≤ 3*b ∧ b ≤ 5*b ∧ b+2*b ≤ 5*b ∧
      3*b+2*b ≤ 5*b ∧ 5*b ≤ 8*b ∧ 8*b+5*b ≤ 16*b ∧ 5*b ≤ 16*b := by clear hs hj hw; omega
  have q3 : j*b + b ≤ 16*b := by
    have := Nat.mul_le_mul_right b (show j + 1 ≤ 16 by omega); rwa [add_mul, one_mul] at this
  have hf : (j*b + b ≤ 8*b ∧ scratchBase b j = 8*b) ∨ (8*b ≤ j*b ∧ scratchBase b j = 0) := by
    rcases Nat.lt_or_ge j 8 with h8 | h8
    · refine .inl ⟨?_, if_pos h8⟩
      have := Nat.mul_le_mul_right b (show j + 1 ≤ 8 by omega); rwa [add_mul, one_mul] at this
    · exact .inr ⟨Nat.mul_le_mul_right b h8, if_neg (by omega)⟩
  have hF : scratchBase b j + 5*b ≤ 16*b := by
    rcases hf with h | h <;> rw [h.2]
    · exact M9
    · rw [zero_add]; exact M10
  have hU : j*b + b ≤ scratchBase b j ∨ scratchBase b j + 5*b ≤ j*b := by
    rcases hf with h | h <;> rw [h.2]
    · exact .inl h.1
    · rw [zero_add]; exact .inr (M8.trans h.1)
  have hF' : ∀ {x}, x ≤ 5*b → scratchBase b j + x ≤ 16*b + w := fun h =>
    (Nat.add_le_add_left h _).trans (hF.trans (Nat.le_add_right _ _))
  have hZ' : ∀ {x}, x ≤ 5*b → scratchBase b j + x ≤ 16*b + s*b := fun h =>
    (Nat.add_le_add_left h _).trans (hF.trans (Nat.le_add_right _ _))
  exact ⟨fits_of (q3.trans (Nat.le_add_right _ _)), fV,
    fits_of (hF' M4),
    fits_of ((add_assoc _ _ _).trans_le (hF' M6)),
    fits_of ((add_assoc _ _ _).trans_le (hF' M7)),
    sep (hU.imp id fun h => (Nat.add_le_add_left M4 _).trans h),
    sep (hU.imp (fun h => h.trans (Nat.le_add_right _ _))
      fun h => ((add_assoc _ _ _).trans_le (Nat.add_le_add_left M6 _)).trans h),
    sep (hU.imp (fun h => h.trans (Nat.le_add_right _ _))
      fun h => ((add_assoc _ _ _).trans_le (Nat.add_le_add_left M7 _)).trans h),
    sep (.inl ((add_assoc _ _ _).trans_le (Nat.add_le_add_left M2 _))),
    sep (.inl le_rfl),
    sep (.inl (Nat.add_le_add_left M1 _)),
    sep (.inl (q3.trans (Nat.le_add_right _ _))),
    sep (.inl (hZ' M4)),
    sep (.inr ((add_assoc _ _ _).trans_le (hZ' M7)))⟩

lemma grid_gains {k w : ℕ} {r : ℂ} (h g : Line) (hr : PrimRoot r (2^(k+1))) (hw : w ≤ 16*2^k) :
    Gains (toeplitzGridReel k r w h g) (16*2^k) (bridgeOp (16*2^k) w h g) := by
  have hb : 0 < 2^k := Nat.two_pow_pos k
  have H1 : ∀ {b s i : ℕ}, 16*b + s*b ≤ i → i < 16*b + s*b + min b (w - s*b) →
      s*b ≤ i - 16*b ∧ i - 16*b < s*b + b ∧ 16*b ≤ i ∧ i < 16*b + w := by
    intro b s i q1 q2; clear hw hb hr; omega
  have H2 : ∀ {b S i : ℕ}, 16*b ≤ i → i < 16*b + w → S ≤ i - 16*b → i - 16*b < S + b →
      16*b + S ≤ i ∧ i < 16*b + S + min b (w - S) := by
    intro b S i q1 q2 q3 q4; clear hw hb hr; omega
  refine (tripleConcat_gains fun s hs c _ j hj => (pairReel_acts (j*2^k) (c*2^k) (16*2^k+s*2^k) h g hr
    (cell_zones hs hj hw).1 (cell_zones hs hj hw).2).gains (fun i q => ?_) fun i q => ?_).congr
    fun x => funext fun i => ?_
  · have := Nat.mul_le_mul_right (2^k) (show j+1 ≤ 16 by omega)
    rw [add_mul, one_mul] at this; exact lt_of_lt_of_le q.2 this
  · exact le_trans (Nat.le_add_right _ _) q.1
  simp only [Finset.sum_apply, bridgeOp, lift_app]
  by_cases hi : 16*2^k ≤ i ∧ i < 16*2^k + w
  · rw [if_pos hi]
    set s0 := (i - 16*2^k)/2^k
    have d1 : s0*2^k ≤ i - 16*2^k := Nat.div_mul_le_self _ _
    have d2 : i - 16*2^k < s0*2^k + 2^k := Nat.lt_div_mul_add hb
    rw [sum_eq_single s0 (fun s _ hs => sum_eq_zero fun c _ =>
      sum_eq_zero fun j _ => if_neg fun q => by
        have := H1 q.1 q.2
        exact hs (Nat.div_eq_of_lt_le this.1 (by rw [add_mul, one_mul]; exact this.2.1)).symm)
      (fun h' => absurd (mem_range.2 (show (i - 16*2^k)/2^k < 16 from
        (Nat.div_lt_iff_lt_mul hb).2 (by omega))) h')]
    have hc : (outZone (16*2^k) w (2^k) s0).has i := H2 hi.1 hi.2 d1 d2
    have e : 16*2^k + s0*2^k + (i - (16*2^k + s0*2^k)) = i := Nat.add_sub_cancel' hc.1
    simp only [hc, if_true]
    simp only [outZone, e, Zone.peek, blockZone, scratchZone, toeplitzApply, sum_blocks 16 (2^k)]
    refine sum_congr rfl fun c _ => ?_
    rw [sum_comm]; exact sum_congr rfl fun c' _ => (Finset.mul_sum _ _ _).symm
  · rw [if_neg hi]
    exact sum_eq_zero fun s _ => sum_eq_zero fun c _ => sum_eq_zero
      fun j _ => if_neg fun q => hi (H1 q.1 q.2).2.2

def bridgeBeats (e : ℕ) : ℕ :=
  if e<4 then let p := 2^e; p*(p*(p*26))
  else 16*(16*(16*(4*(80*(e-4)+348))))

def toeplitzBridge (e w : ℕ) (h g r : Line) : Reel :=
  if e<4 then naiveToeplitzReel (2^e) w h g else toeplitzGridReel (e-4) (r (e-4+1)) w h g

def Springs (e : ℕ) (r : Line) : Prop :=
  ∀ i ≤ e, Spectral.PrimRoot (r i) (2^i)

def toeplitzBeats : ℕ → ℕ
  | 0 => 1
  | e+1 => toeplitzBeats e + bridgeBeats e

def toeplitzStep (e v : ℕ) (h g r : Line) (a b : Reel) : Reel :=
  let n := 2^e
  (parallel (min n v) a b).stack
    (if n<v then toeplitzBridge e (v-n) h g r else wait (bridgeBeats e))

def toeplitzReel (h g r : Line) : ℕ → ℕ → Reel
  | 0,v => scaleReel v (fun _ => h 0)
  | e+1,v => toeplitzStep e v h g r (toeplitzReel h g r e (min (2^e) v)) (toeplitzReel h g r e (v-2^e))

lemma beats_toeplitzReel (h g r : Line) (e v : ℕ) :
    (toeplitzReel h g r e v).beats=toeplitzBeats e := by
  induction e generalizing v with
  | zero => rfl
  | succ e ih =>
    simp only [toeplitzReel, toeplitzStep, beats_stack, beats_parallel, ih, toeplitzBeats]
    congr 1
    split_ifs
    · unfold toeplitzBridge bridgeBeats; split_ifs
      · exact beats_tripleConcat fun _ _ _ => beats_naiveToeplitzCell _ _ _ _ _ _ _
      · exact beats_tripleConcat fun _ _ _ => beats_toeplitzGridCell _ _ _ _ _ _ _ _
    · rfl

lemma toeplitzBeats_le (e : ℕ) :
    toeplitzBeats e ≤ 10000000*(e+1)^2 := by
  induction e with
  | zero => simp [toeplitzBeats]
  | succ e ih =>
    have : bridgeBeats e ≤ 10000000*(2*e+3) := by
      unfold bridgeBeats; split_ifs with h4
      · have hp : 2^e ≤ 8 := (Nat.pow_le_pow_right two_pos (Nat.le_of_lt_succ h4)).trans (by norm_num)
        show 2^e*(2^e*(2^e*26)) ≤ _
        exact (Nat.mul_le_mul hp (Nat.mul_le_mul hp (Nat.mul_le_mul_right 26 hp))).trans
          ((by norm_num : 8*(8*(8*26)) ≤ 10000000*3).trans (Nat.mul_le_mul_left _ (Nat.le_add_left 3 (2*e))))
      · obtain ⟨t, rfl⟩ : ∃ t, e = t + 4 := ⟨e - 4, (Nat.sub_add_cancel (not_lt.mp h4)).symm⟩
        rw [Nat.add_sub_cancel]; clear ih; omega
    have e2 : (e+1+1)^2 = (e+1)^2 + (2*e+3) := by ring
    simp only [toeplitzBeats]; rw [e2, mul_add]; exact Nat.add_le_add ih this

lemma sound_atOffset {o N : ℕ} {P : Reel} (h : P.Sound N) (n : ℕ) (hn : o + N ≤ n) :
    (atOffset o P).Sound n := (Sound.parallel (sound_wait _ o) h rfl).wider hn

lemma sound_conv {n d : ℕ} {r : ℂ} {u v : Zone} {h : Line} (hu : u.Fits n) (hv : v.Fits n)
    (huw : u.wide = 2^d) (hvw : v.wide = 2^d) (huv : u.Sep v) : (cyclicConvReel d r u v h).Sound n := by
  have e : ∀ {z : Zone}, z.Fits n → z.wide = 2^d → z.lo + 2^d ≤ n := fun hz hw => by
    have := hz (_ + (2^d - 1)) ⟨Nat.le_add_right _ _, by have := Nat.two_pow_pos d; omega⟩; omega
  exact ((((sound_atOffset (sound_fftReel d r) n (e hu huw)).stack (sound_atOffset (sound_fftReel d r) n
    (e hv hvw))).stack (sound_addScaled hv hu (by omega) huv.symm _)).stack (sound_atOffset
    (sound_inverseFftReel d r) n (e hu huw))).stack (sound_atOffset (sound_inverseFftReel d r) n (e hv hvw))

lemma sound_blockConvReel {n d : ℕ} {r : ℂ} {u v a b : Zone} {h : Line} (ha : a.Fits n) (hb : b.Fits n)
    (haw : a.wide = 2^d) (hbw : b.wide = 2^d) (hab : a.Sep b) (hu : u.Fits n) (hv : v.Fits n)
    (hua : u.Sep a) (hu' : u.wide ≤ a.wide) (hv' : v.wide ≤ b.wide) (hvb : v.Sep b) :
    (blockConvReel d r u v a b h).Sound n := by
  have ta : ∀ t, (copyInReel u a t).Sound n := fun t =>
    sound_addScaled (ha.slim hu') hu rfl (Sep.slim_left hua.symm hu') _
  have sb : ∀ t, (copyOutReel b v t).Sound n := fun t =>
    sound_addScaled hv (hb.slim hv') rfl (Sep.slim_left hvb.symm hv').symm _
  have c : ∀ h, (cyclicConvReel d r a b h).Sound n := fun _ => sound_conv ha hb haw hbw hab
  exact ((((((ta 1).stack (c _)).stack (ta _)).stack (c _)).stack (sb 1)).stack
    ((((ta 1).stack (c _)).stack (ta _)).stack (c _))).stack (sb _)

lemma sound_pair {n k : ℕ} {r : ℂ} {u v z l m : Zone} {b e y : ℕ} {h g : Line}
    (H : ZoneWidths k u v z l m) (hf : ZonesApart n u v z l m) :
    (toeplitzPairReel k r u v z l m b e y h g).Sound n := by
  have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (Nat.le_succ k)
  have ⟨H1, H2, H3, H4, H5⟩ := H
  have b1 : ∀ g, (toeplitzBlockReel k r u z l m b e g).Sound n := fun g =>
    sound_blockConvReel hf.fitsL hf.fitsM H4 H5 hf.lm hf.fitsU hf.fitsZ hf.ul (by omega) (by omega) hf.zm
  have b2 : ∀ h, (toeplitzBlockReel k r z v l m e y h).Sound n := fun h =>
    sound_blockConvReel hf.fitsL hf.fitsM H4 H5 hf.lm hf.fitsZ hf.fitsV hf.zl (by omega) (by omega) hf.vm
  exact (((b1 g).stack (b2 h)).stack (b1 _)).stack (b2 _)

lemma two_pow_eq_sixteen_mul {e : ℕ} (h : ¬ e < 4) : 2^e = 16*2^(e-4) := by
  rw [show (16:ℕ) = 2^4 by norm_num, ← pow_add]; congr 1; omega

lemma sound_bridge {e w : ℕ} (h g r : Line) (hw : w ≤ 2^e) :
    (toeplitzBridge e w h g r).Sound (2^e + w) := by
  unfold toeplitzBridge; split_ifs with he
  · refine sound_concatReels fun s _ => sound_concatReels fun c _ => sound_concatReels fun j hj => ?_
    unfold naiveToeplitzCell; split_ifs with hs
    · have hm : min 1 (w - s*1) = 1 := by rw [mul_one]; exact min_eq_left (Nat.sub_pos_of_lt hs)
      have hj1 : j*1 + 1 ≤ 2^e := by rw [mul_one]; exact hj
      exact sound_addScaled (u := outZone (2^e) w 1 s) (v := blockZone 1 j)
        (fits_of (show 2^e + s*1 + min 1 (w - s*1) ≤ 2^e + w by
          rw [hm, mul_one, add_assoc]; exact Nat.add_le_add_left hs _))
        (fits_of (le_trans hj1 (Nat.le_add_right _ _))) hm
        (fun i (h1 : 2^e + s*1 ≤ i ∧ _) (h2 : j*1 ≤ i ∧ i < j*1 + 1) =>
          absurd (le_trans (Nat.le_add_right _ _) h1.1) (Nat.not_le_of_lt (lt_of_lt_of_le h2.2 hj1))) _
    · exact sound_wait _ _
  · rw [two_pow_eq_sixteen_mul he] at hw ⊢
    exact sound_concatReels fun s hs => sound_concatReels fun c _ => sound_concatReels fun j hj =>
      sound_pair (cell_zones hs hj hw).1 (cell_zones hs hj hw).2

lemma bridge_gains {e w : ℕ} (h g r : Line) (hw : w ≤ 2^e) (hr : Springs e r) :
    Gains (toeplitzBridge e w h g r) (2^e) (bridgeOp (2^e) w h g) := by
  unfold toeplitzBridge; split_ifs with he
  · exact naive_gains h g hw
  · rw [two_pow_eq_sixteen_mul he] at hw ⊢; exact grid_gains h g (hr _ (by omega)) hw

lemma sound_toeplitzReel (h g r : Line) (e v : ℕ) (hv : v ≤ 2^e) :
    (toeplitzReel h g r e v).Sound v := by
  induction e generalizing v with
  | zero => exact sound_scaleReel _ _
  | succ e ih =>
    rw [pow_succ] at hv
    have hB : v - 2^e ≤ 2^e := by rw [Nat.sub_le_iff_le_add, ← mul_two]; exact hv
    have hp := Sound.parallel (ih (min (2^e) v) (min_le_left _ _)) (ih (v - 2^e) hB)
      (by rw [beats_toeplitzReel, beats_toeplitzReel])
    rw [show min (2^e) v + (v - 2^e) = v by
      rcases le_total (2^e) v with c | c
      · rw [min_eq_left c, Nat.add_sub_cancel' c]
      · rw [min_eq_right c, Nat.sub_eq_zero_of_le c, add_zero]] at hp
    refine hp.stack ?_
    split_ifs with c
    · have := sound_bridge (e := e) (w := v - 2^e) h g r hB
      rwa [Nat.add_sub_cancel' c.le] at this
    · exact sound_wait _ _

lemma toeplitzReel_go {h r : Line} (h0 : h 0 ≠ 0) : ∀ e v, v ≤ 2^e → Springs e r → ∀ x, ∀ i < v,
    (toeplitzReel h (toeplitzInv h) r e v).go x i = toeplitzApply v h x i
  | 0, v, hv, _, x, i, hi => by
    rw [toeplitzReel, scaleReel_go, if_pos hi]
    obtain rfl : v = 1 := le_antisymm hv (Nat.one_le_of_lt hi)
    obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
    simp [toeplitzApply, rise]
  | e+1, v, hv, hr, x, i, hi => by
    rw [pow_succ] at hv
    have hr' : Springs e r := fun i hi => hr i (Nat.le_succ_of_le hi)
    have hB : v - 2^e ≤ 2^e := by rw [Nat.sub_le_iff_le_add, ← mul_two]; exact hv
    have A := toeplitzReel_go h0 e _ (min_le_left (2^e) v) hr'
    have B := toeplitzReel_go h0 e (v - 2^e) hB hr'
    have P := go_parallel (sound_toeplitzReel h (toeplitzInv h) r e _ (min_le_left (2^e) v))
      ((beats_toeplitzReel ..).trans (beats_toeplitzReel h (toeplitzInv h) r e (v - 2^e)).symm) x
    simp only [toeplitzReel, toeplitzStep, go_stack]
    split_ifs with c
    · rw [min_eq_left c.le] at A P ⊢
      have Y := fun j (hj : j < 2^e) => (P j).trans (by rw [if_pos hj, A x j hj])
      rw [((bridge_gains h (toeplitzInv h) r hB hr') _).1, Pi.add_apply, bridgeOp,
        stencil_congr _ _ Y, stencil_congr _ _ fun c hc => toeplitzInv_left_inv _ h x h0 c hc]
      have e1 := stencil_left (2^e) (v - 2^e) h x
      have e2 := stencil_right (2^e) (v - 2^e) h x
      rw [Nat.add_sub_cancel' c.le] at e1 e2
      by_cases ci : i < 2^e
      · rw [if_neg fun h => absurd h.1 (not_le.mpr ci), add_zero, Y i ci, e1 i ci]
      · obtain ⟨k, rfl⟩ : ∃ k, i = 2^e + k := ⟨i - 2^e, (Nat.add_sub_cancel' (not_lt.mp ci)).symm⟩
        have hk : k < v - 2^e := Nat.lt_sub_of_add_lt (by rw [add_comm]; exact hi)
        rw [if_pos ⟨Nat.le_add_right _ _, by rw [Nat.add_sub_cancel' c.le]; exact hi⟩, P,
          if_neg (Nat.not_lt.mpr (Nat.le_add_right _ _)), Nat.add_sub_cancel_left, B _ _ hk, e2]
        exact add_comm _ _
    · rw [min_eq_right (not_lt.mp c)] at A P ⊢
      rw [go_wait, P, if_pos hi, A x i hi]

def Creates (p : Reel) (n : ℕ) (M : RootMat n) : Prop :=
  ∀ x, front n (p.go x)=M *ᵥ front n x

def reverseReel (n : ℕ) : Reel := permReel n fun i => n-1-i

def reversedReel (n : ℕ) (u : Reel) : Reel := ((reverseReel n).stack u).stack (reverseReel n)

def lowerPassReel (n : ℕ) (u : ℂ) (p : Reel) : Reel :=
  ((scaleReel n (roof u)).stack p).stack (scaleReel n (gap u))

def upperPassReel (n : ℕ) (u : ℂ) (p : Reel) : Reel :=
  ((scaleReel n (gap u)).stack (reversedReel n p)).stack (scaleReel n (roof u))

def vandermondeSteps (n : ℕ) (u : ℂ) (p : Reel) : Reel :=
  ((upperPassReel n u p).stack (scaleReel n (fun i => (vandDiag u i)⁻¹))).stack (lowerPassReel n u p)

def vandermondeReel (n : ℕ) (e : ℕ) (u : ℂ) (r : Line) : Reel :=
  let h := floorH u
  vandermondeSteps n u (toeplitzReel h (toeplitzInv h) r e n)

lemma sound_vandermondeReel (n e : ℕ) (u : ℂ) (r : Line) (h : n ≤ 2^e) :
    (vandermondeReel n e u r).Sound n := by
  have hT := sound_toeplitzReel (floorH u) (toeplitzInv (floorH u)) r e n h
  have he : (reverseReel n).Sound n := sound_tick (plain_sound _ fun i hi => by omega)
  exact ((((sound_scaleReel n _).stack ((he.stack hT).stack he)).stack (sound_scaleReel n _)).stack
    (sound_scaleReel n _)).stack (((sound_scaleReel n _).stack hT).stack (sound_scaleReel n _))

lemma creates_stack {a b : Reel} {n : ℕ} {M N : RootMat n} (ha : Creates a n M)
    (hb : Creates b n N) : Creates (a.stack b) n (N * M) := fun x => by
  rw [go_stack, hb, ha, Matrix.mulVec_mulVec]

lemma creates_scaleReel (n : ℕ) (d : Line) : Creates (scaleReel n d) n (fade n d) := fun x => by
  funext i; simp [front, scaleReel_go, fade, Matrix.mulVec_diagonal]

lemma creates_T {n : ℕ} {T : Reel} {h : Line} (hT : ∀ x i, i < n → T.go x i = toeplitzApply n h x i) :
    Creates T n (lowerToeplitz n h) := fun x => by
  rw [← front_stencil]; funext i; exact hT x i i.isLt

lemma creates_reversedReel {n : ℕ} {T : Reel} {h : Line}
    (hT : ∀ x i, i < n → T.go x i = toeplitzApply n h x i) :
    Creates (reversedReel n T) n (lowerToeplitz n h)ᵀ := fun x => by
  rw [← front_stencilT]; funext i
  have hi := i.isLt
  simp only [front, reversedReel, go_stack, reverseReel, permReel_go, if_pos hi]
  rw [hT _ (n - 1 - i) (by omega), stencil_congr n h (y := fun j => x (n-1-j))
    (fun j hj => by rw [permReel_go, if_pos hj])]
  exact stencil_reversed n h x i hi

lemma vandermondeReel_creates (n e : ℕ) (u : ℂ) (r : Line) (h : n ≤ 2^e) (hr : Springs e r)
    (hu : Spectral.PrimRoot u n) :
    Creates (vandermondeReel n e u r) n (rootVandermonde n u) := by
  have h0 : floorH u 0 ≠ 0 := by simp [floorH, gap]
  have hT := toeplitzReel_go h0 e n h hr
  have key : Creates (vandermondeReel n e u r) n _ :=
    creates_stack (creates_stack (creates_stack (creates_stack (creates_scaleReel n (gap u))
      (creates_reversedReel hT)) (creates_scaleReel n (roof u))) (creates_scaleReel n fun i => (vandDiag u i)⁻¹))
      (creates_stack (creates_stack (creates_scaleReel n (roof u)) (creates_T hT))
        (creates_scaleReel n (gap u)))
  intro x
  rw [key x, rootVandermonde_factor n u hu]
  refine congrArg (fun M => M *ᵥ front n x) ?_
  simp only [vandLower, fade, transpose_mul, diagonal_transpose, Matrix.mul_assoc]

def vandermondeBeats (e : ℕ) := 2*toeplitzBeats e+7

lemma beats_vandermondeReel (n e : ℕ) (u : ℂ) (r : Line) :
    (vandermondeReel n e u r).beats=vandermondeBeats e := by
  simp only [vandermondeReel, vandermondeSteps, upperPassReel, lowerPassReel, reversedReel, reverseReel, permReel, scaleReel, beats_stack,
    beats_tick, beats_toeplitzReel, vandermondeBeats]
  ring

lemma vandermondeBeats_le (e : ℕ) : vandermondeBeats e ≤ 20000000*(e+1)^2+7 := by
  unfold vandermondeBeats
  exact Nat.add_le_add_right ((Nat.mul_le_mul_left 2 (toeplitzBeats_le e)).trans_eq (by ring)) 7

end
end PowerSaving.ReelKit
end OAI

namespace OAI
namespace PowerSaving
noncomputable section
namespace AxisTensor
open ReelKit Stroke Reel Spectral Matrix Finset Binary

abbrev Axes := ℕ → ℕ

def extent (r : Axes) : ℕ → ℕ
  | 0 => 1
  | j+1 => extent r j*r j

def Splits (r : Axes) (l : ℕ) := ∀ t<l, 2≤r t

namespace Splits
variable {r : Axes} {l : ℕ}

lemma cut (h : Splits r l) {j : ℕ} (g : j ≤ l) :
    Splits r j := fun t ht => h t (by omega)

lemma extent_pos (h : Splits r l) :
    0<extent r l := by
  induction l with
  | zero => exact Nat.one_pos
  | succ l ih => exact Nat.mul_pos (ih (h.cut (by omega))) (by have := h l (by omega); omega)

lemma extent_le {j : ℕ} (h : Splits r l) (hj : j≤l) :
    extent r j ≤ extent r l := by
  induction l with
  | zero =>
    obtain rfl : j = 0 := by omega
    exact le_rfl
  | succ l ih =>
    rcases Nat.lt_or_ge j (l+1) with hj' | hj'
    · exact (ih (h.cut (by omega)) (by omega)).trans
        (le_mul_of_one_le_right (Nat.zero_le _) (by have := h l (by omega); omega))
    · obtain rfl : j = l+1 := by omega
      exact le_rfl

lemma axes_le (h : Splits r l) :
    l < extent r l := by
  induction l with
  | zero => exact Nat.one_pos
  | succ l ih =>
    have := ih (h.cut (by omega)); have := Nat.mul_le_mul_left (extent r l) (h l (by omega))
    show l + 1 < extent r l * r l; omega

lemma tree_bound (h : Splits r l) :
    ∑ j ∈ range (l+1), extent r j < 2*extent r l := by
  induction l with
  | zero => simp [extent]
  | succ l ih =>
    rw [sum_range_succ]
    have := ih (h.cut (by omega)); have := Nat.mul_le_mul_left (extent r l) (h l (by omega))
    have : 2 * extent r l ≤ extent r (l+1) := by show _ ≤ extent r l * r l; omega
    omega

lemma div_lt (h : Splits r (l+1)) {i} (hi : i<extent r (l+1)) :
    i / r l < extent r l := (Nat.div_lt_iff_lt_mul (by have := h l (by omega); omega)).2 hi

lemma mod_lt (h : Splits r (l+1)) (i : ℕ) :
    i%r l < r l := Nat.mod_lt _ (by have := h l (by omega); omega)

lemma join_lt (_h : Splits r (l+1)) {a b} (ha : a < extent r l) (hb : b < r l) :
    a*r l+b < extent r (l+1) := DigitArith.lt_join ha hb

end Splits

abbrev IdxMat := ℕ → ℕ → ℂ

def idxMul (n : ℕ) (A B : IdxMat) : IdxMat := fun i k => ∑ j ∈ range n, A i j * B j k

def idxApply (r : ℕ) (X : IdxMat) (v : Line) : Line := fun i =>
  ∑ k ∈ range r, X i k*v k

def idxOne : IdxMat := fun i j => if j=i then 1 else 0

def frame (n : ℕ) (X : IdxMat) : RootMat n := fun i j => X i.val j.val

def axisKron (r : Axes) (X : ℕ → IdxMat) : ℕ → IdxMat
  | 0 => fun _ _ => 1
  | j+1 => fun i k => axisKron r X j (i/r j) (k/r j) * X j (i%r j) (k%r j)

def leafM (u : Stroke) : IdxMat :=
  fun i j => if j=u.ix i then u.dye i else 0

def leafC (u : Stroke) : IdxMat :=
  fun i j =>
    if u.partner i=i then idxOne i j
    else (if j=i then ca else 0)+(if j=u.partner i then cb else 0)

def reelMat (q : Reel) (n : ℕ) : ℕ → IdxMat
  | 0 => idxOne
  | t+1 => idxMul n (leafC (q.atBeat t)) (idxMul n (leafM (q.atBeat t)) (reelMat q n t))

def axisRun (r : Axes) (l : ℕ) (p : ℕ → Reel) (x : Line) : ℕ → Line
  | 0 => x
  | t+1 =>
    let M := axisKron r (fun i => leafM ((p i).atBeat t)) l
    let C := axisKron r (fun i => leafC ((p i).atBeat t)) l
    idxApply (extent r l) C (idxApply (extent r l) M (axisRun r l p x t))

lemma idxApply_idxApply (n : ℕ) (A B : IdxMat) (x : Line) :
    idxApply n A (idxApply n B x) = idxApply n (idxMul n A B) x := by
  funext i
  simp only [idxApply, idxMul, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact sum_comm

lemma idxApply_congr {n : ℕ} (A : IdxMat) {x y : Line} (e : ∀ j < n, x j = y j) (i : ℕ) :
    idxApply n A x i = idxApply n A y i :=
  sum_congr rfl fun j hj => by rw [e j (mem_range.mp hj)]

lemma idxApply_idxOne {n i : ℕ} (x : Line) (hi : i < n) : idxApply n idxOne x i = x i := by
  simp [idxApply, idxOne, hi]

lemma idxApply_ext {n : ℕ} {A B : IdxMat} (h : ∀ y, ∀ i < n, idxApply n A y i = idxApply n B y i)
    {i k : ℕ} (hi : i < n) (hk : k < n) : A i k = B i k := by
  simpa [idxApply, hk] using h (fun j => if j = k then 1 else 0) i hi

lemma send_idxApply {u : Stroke} {n : ℕ} (h : u.Sound n) (x : Line) {i : ℕ} (hi : i < n) :
    u.send x i = idxApply n (leafC u) (idxApply n (leafM u) x) i := by
  rw [idxApply_congr _ (x := idxApply n (leafM u) x) (y := applyM u x) (fun j hj => by
    simp [idxApply, leafM, applyM, h.bdix j hj])]
  show applyC u (applyM u x) i = _
  by_cases hp : u.partner i = i
  · simp [applyC, idxApply, leafC, idxOne, hp, hi]
  · simp [applyC, idxApply, leafC, hp, add_mul, sum_add_distrib, hi, h.bdp i hi]

lemma reach_idxApply {q : Reel} {n : ℕ} (h : q.Sound n) (x : Line) :
    ∀ t ≤ q.beats, ∀ i < n, q.reach x t i = idxApply n (reelMat q n t) x i := by
  intro t; induction t with
  | zero => intro _ i hi; exact (idxApply_idxOne x hi).symm
  | succ t ih =>
    intro ht i hi
    show (q.atBeat t).send (q.reach x t) i = _
    rw [send_idxApply (h t (by omega)) _ hi,
      idxApply_congr _ (fun k hk => idxApply_congr _ (fun j hj => ih (by omega) j hj) k),
      idxApply_idxApply n (leafM (q.atBeat t)) (reelMat q n t) x, idxApply_idxApply] <;> rfl

lemma axisKron_idxMul (r : Axes) (A B : ℕ → IdxMat) (l : ℕ) :
    idxMul (extent r l) (axisKron r A l) (axisKron r B l) = axisKron r (fun j => idxMul (r j) (A j) (B j)) l := by
  induction l with
  | zero => funext i k; simp [idxMul, axisKron, extent]
  | succ l ih =>
    funext i k
    simp only [axisKron]
    rw [← ih]
    simp only [idxMul, extent]
    rw [sum_blocks, Finset.sum_mul]
    refine sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine sum_congr rfl fun c hc => ?_
    rw [DigitArith.div_join (mem_range.mp hc), DigitArith.mod_join (mem_range.mp hc)]; ring

lemma axisKron_congr {r : Axes} {l : ℕ} (h : Splits r l) {A B : ℕ → IdxMat}
    (e : ∀ j < l, ∀ a < r j, ∀ c < r j, A j a c = B j a c) :
    ∀ i < extent r l, ∀ k < extent r l, axisKron r A l i k = axisKron r B l i k := by
  induction l with
  | zero => intro i _ k _; rfl
  | succ l ih =>
    intro i hi k hk
    simp only [axisKron]
    rw [ih (h.cut (by omega)) (fun j hj => e j (by omega)) _ (h.div_lt hi) _ (h.div_lt hk),
      e l (by omega) _ (h.mod_lt i) _ (h.mod_lt k)]

lemma axisKron_idxOne {r : Axes} {l : ℕ} (h : Splits r l) :
    ∀ i < extent r l, ∀ k < extent r l, axisKron r (fun _ => idxOne) l i k = idxOne i k := by
  induction l with
  | zero =>
    intro i hi k hk
    simp only [extent, Nat.lt_one_iff] at hi hk; subst hi; subst hk; simp [axisKron, idxOne]
  | succ l ih =>
    intro i hi k hk
    simp only [axisKron]
    rw [ih (h.cut (by omega)) _ (h.div_lt hi) _ (h.div_lt hk)]
    simp only [idxOne]
    by_cases e : k = i
    · subst e; simp
    · rw [if_neg e]
      have : ¬ (k / r l = i / r l ∧ k % r l = i % r l) := fun ⟨h1, h2⟩ =>
        e (by rw [← Nat.div_add_mod k (r l), ← Nat.div_add_mod i (r l), h1, h2])
      by_cases h1 : k / r l = i / r l
      · rw [if_neg (fun h2 => this ⟨h1, h2⟩), mul_zero]
      · rw [if_neg h1, zero_mul]

theorem axisRun_eq_kron (r : Axes) (l : ℕ) (p : ℕ → Reel) (h : Splits r l) (b : ℕ)
    (hs : ∀ j<l, (p j).Sound (r j)) (hb : ∀ j<l, (p j).beats=b)
    (X : ℕ → IdxMat) (hx : ∀ j<l, Creates (p j) (r j) (frame (r j) (X j)))
    (x : Line) (i : ℕ) (hi : i<extent r l) :
    axisRun r l p x b i = idxApply (extent r l) (axisKron r X l) x i := by
  have run : ∀ t ≤ b, ∀ i < extent r l, axisRun r l p x t i =
      idxApply (extent r l) (axisKron r (fun j => reelMat (p j) (r j) t) l) x i := by
    intro t; induction t with
    | zero =>
      intro _ i hi
      refine (idxApply_idxOne x hi).symm.trans (sum_congr rfl fun k hk => ?_)
      rw [show axisKron r (fun j => reelMat (p j) (r j) 0) l i k = idxOne i k from
        axisKron_idxOne h i hi k (mem_range.mp hk)]
    | succ t ih =>
      intro ht i hi
      show idxApply _ _ (idxApply _ _ (axisRun r l p x t)) i = _
      rw [idxApply_congr _ (fun k hk => idxApply_congr _ (fun j hj => ih (by omega) j hj) k),
        idxApply_idxApply (extent r l) (axisKron r (fun j => leafM ((p j).atBeat t)) l), idxApply_idxApply,
        axisKron_idxMul, axisKron_idxMul] <;> rfl
  rw [run b le_rfl i hi]
  refine sum_congr rfl fun k hk => congrArg (· * x k) (axisKron_congr h (fun j hj a ha c hc =>
    idxApply_ext (fun y i hi => ?_) ha hc) i hi k (mem_range.1 hk))
  have := congrFun (hx j hj y) ⟨i, hi⟩
  simp only [front, AxisTensor.frame, Matrix.mulVec, dotProduct] at this
  rw [← reach_idxApply (hs j hj) y b (hb j hj).ge i hi, show (p j).reach y b i = (p j).go y i by
    unfold Reel.go; rw [hb j hj], this]
  exact Fin.sum_univ_eq_sum_range (fun c => X j i c * y c) _

end AxisTensor
end
end PowerSaving
end OAI

namespace OAI
namespace PowerSaving.AxisTensor
open ReelKit Finset
noncomputable section

structure Reloc (n : ℕ) (q : ℕ → ℕ) : Prop where
  bd : ∀ j<n, q j<n
  inj : ∀ i<n, ∀ j<n, q i=q j → i=j

def seek (n : ℕ) (q : ℕ → ℕ) (i : ℕ) : ℕ := by
  classical
  exact if h : ∃ j : ℕ, j<n ∧ q j=i then Classical.choose h else 0

namespace Reloc
variable {n : ℕ} {q : ℕ→ℕ}

lemma image (h : Reloc n q) {i : ℕ} (hi : i < n) : ∃ j, j < n ∧ q j = i := by
  obtain ⟨j, hj, e⟩ := surj_on_of_inj_on_of_card_le (s := range n) (t := range n)
    (fun j _ => q j) (fun j hj => mem_range.2 (h.bd j (mem_range.1 hj)))
    (fun a b ha hb e => h.inj a (mem_range.1 ha) b (mem_range.1 hb) e) le_rfl i (mem_range.2 hi)
  exact ⟨j, mem_range.1 hj, e.symm⟩

lemma seeks (h : Reloc n q) {i : ℕ} (hi : i<n) :
    seek n q i < n ∧ q (seek n q i) = i := by
  have he := h.image hi
  unfold seek; rw [dif_pos he]; exact Classical.choose_spec he

lemma seeks_at (h : Reloc n q) {i : ℕ} (hi : i<n) :
    seek n q (q i) = i := by
  obtain ⟨h1, h2⟩ := h.seeks (h.bd i hi)
  exact h.inj _ h1 _ hi h2

lemma sum {A : Type*} [AddCommMonoid A] (h : Reloc n q) (f : ℕ → A) :
    ∑ i ∈ range n, f (q i) = ∑ i ∈ range n, f i :=
  sum_nbij q (fun a ha => mem_range.2 (h.bd a (mem_range.1 ha)))
    (fun a ha b hb e => h.inj a (mem_range.1 ha) b (mem_range.1 hb) e)
    (fun i hi => let ⟨j, hj, e⟩ := h.image (mem_range.1 hi); ⟨j, mem_range.2 hj, e⟩)
    (fun _ _ => rfl)

lemma sow {A : Type*} (h : Reloc n q) (f : ℕ → A) (z : A) :
    Tape.sow n n z (fun i => (q i,f i)) = Tape.tab n (fun i => f (seek n q i)) := by
  refine Tape.ext_look (by simp [Tape.tab]) z fun i hi => ?_
  simp only [Tape.len_sow] at hi
  obtain ⟨h1, h2⟩ := h.seeks hi
  rw [Tape.sow_look_written hi h1 h2 (fun s hs1 hs2 e => by
    have := h.inj s hs2 _ h1 (e.trans h2.symm); omega), Tape.look_tab, if_pos hi]

end Reloc

structure PowBlock where
  start : ℕ
  width : ℕ
  height : ℕ
  seat : ℕ
deriving DecidableEq

namespace PowBlock

def blockEnd (s : PowBlock) := s.start+s.width
def addr (s : PowBlock) := s.start+s.seat

structure Mark (s : PowBlock) (n l : ℕ) : Prop where
  endsBy : s.blockEnd ≤ n
  size : s.width=2^s.height
  tall : s.height ≤ l
  place : s.seat < s.width

namespace Mark
variable {s : PowBlock} {n l : ℕ}
lemma positive (h : Mark s n l) : 0<s.width := by rw [h.size]; positivity
lemma starts (h : Mark s n l) : s.start < s.blockEnd := by
  have := h.positive; unfold blockEnd; omega
end Mark

def same (s t : PowBlock) : Prop :=
  s.start=t.start ∧ s.width=t.width ∧ s.height=t.height

def fits (s t : PowBlock) : Prop :=
  same s t ∨ s.blockEnd ≤ t.start ∨ t.blockEnd ≤ s.start

structure PowBlockCover (n l : ℕ) (f : ℕ → PowBlock) : Prop where
  mark : ∀ i<n, (f i).Mark n l
  seam : ∀ i<n, ∀ j<n, (f i).fits (f j)
  fiber : ∀ i<n, ∀ j<n, (f i).addr=(f j).addr → i=j

def blockAt (n : ℕ) (f : ℕ → PowBlock) (j : ℕ) :=
  f (seek n (fun i => (f i).addr) j)

namespace PowBlockCover
variable {n l : ℕ} {f : ℕ → PowBlock}

lemma reloc (h : PowBlockCover n l f) : Reloc n fun i => (f i).addr :=
  ⟨fun j hj => by
    show (f j).addr < n
    have := (h.mark j hj).endsBy; have := (h.mark j hj).place; unfold addr; unfold blockEnd at *; omega,
   h.fiber⟩

lemma matches_of_eq (h : PowBlockCover n l f) {i j : ℕ} (hi : i<n) (hj : j<n)
    (H : (f i).start=(f j).start) :
    (f i).same (f j) := by
  have := (h.mark i hi).starts; have := (h.mark j hj).starts
  rcases h.seam i hi j hj with e | e | e
  · exact e
  · omega
  · omega

lemma blockAt_addr (h : PowBlockCover n l f) {i : ℕ} (hi : i<n) :
    (blockAt n f i).addr=i := (h.reloc.seeks hi).2

lemma blockAt_mark (h : PowBlockCover n l f) {i : ℕ} (hi : i<n) :
    (blockAt n f i).Mark n l := h.mark _ (h.reloc.seeks hi).1

lemma blockAt_align (h : PowBlockCover n l f) {i j : ℕ} (hi : i<n) (H : (f i).start ≤ j)
    (G : j < (f i).blockEnd) : (blockAt n f j).same (f i) ∧ (blockAt n f j).seat=j-(f i).start := by
  obtain ⟨h1, h2⟩ := h.reloc.seeks (lt_of_lt_of_le G (h.mark i hi).endsBy)
  set t := seek n (fun i => (f i).addr) j
  have hp := (h.mark _ h1).place
  have e : (f t).start + (f t).seat = j := h2
  have hs : (f t).same (f i) := by
    rcases h.seam _ h1 i hi with s | s | s
    · exact s
    all_goals unfold blockEnd at s G; omega
  exact ⟨hs, show (f t).seat = _ by rw [← hs.1]; omega⟩

end PowBlockCover

def blockMul (r : ℕ) (s t : PowBlock) : PowBlock :=
  ⟨s.start*r + s.width*t.start, s.width*t.width, s.height+t.height,
    s.seat*t.width + t.seat⟩

lemma Mark.blockMul {s t : PowBlock} {n i r j : ℕ} (h : Mark s n i) (g : Mark t r j) :
    Mark (blockMul r s t) (n*r) (i+j) where
  endsBy := by
    have a := Nat.mul_le_mul_left s.width (show t.start + t.width ≤ r from g.endsBy)
    have b := Nat.mul_le_mul_right r (show s.start + s.width ≤ n from h.endsBy)
    show s.start*r + s.width*t.start + s.width*t.width ≤ n*r
    rw [Nat.mul_add] at a; rw [Nat.add_mul] at b; omega
  size := by show s.width*t.width = 2^(s.height+t.height); rw [h.size, g.size, pow_add]
  tall := by show s.height+t.height ≤ i+j; have := h.tall; have := g.tall; omega
  place := by
    show s.seat*t.width + t.seat < s.width*t.width
    have := h.place; have := g.place
    have := Nat.mul_le_mul_right t.width (show s.seat + 1 ≤ s.width by omega)
    rw [Nat.add_mul, Nat.one_mul] at this; omega

lemma blockMul_unique {s t s' t' : PowBlock} (r j : ℕ) (hg : Mark t r j) (hg' : Mark t' r j)
    {n i : ℕ} (_ha : Mark s n i) (_ha' : Mark s' n i) (hs : s.fits s') (ht : t.fits t')
    (H : (blockMul r s t).start < (blockMul r s' t').blockEnd)
    (G : (blockMul r s' t').start < (blockMul r s t).blockEnd) :
    s.same s' ∧ t.same t' := by
  simp only [blockMul, blockEnd] at H G
  have e1 : t.start + t.width ≤ r := hg.endsBy
  have e2 : t'.start + t'.width ≤ r := hg'.endsBy
  rcases hs with hs | hs | hs
  · refine ⟨hs, ?_⟩
    obtain ⟨a1, a2, -⟩ := hs
    rw [← a1, ← a2] at H G
    rcases ht with ht | ht | ht
    · exact ht
    · exfalso; have := Nat.mul_le_mul_left s.width (show t.start + t.width ≤ t'.start from ht)
      rw [Nat.mul_add] at this; omega
    · exfalso; have := Nat.mul_le_mul_left s.width (show t'.start + t'.width ≤ t.start from ht)
      rw [Nat.mul_add] at this; omega
  · exfalso
    have := Nat.mul_le_mul_left s.width e1
    have := Nat.mul_le_mul_right r (show s.start + s.width ≤ s'.start from hs)
    rw [Nat.mul_add] at *; rw [Nat.add_mul] at this; omega
  · exfalso
    have := Nat.mul_le_mul_left s'.width e2
    have := Nat.mul_le_mul_right r (show s'.start + s'.width ≤ s.start from hs)
    rw [Nat.mul_add] at *; rw [Nat.add_mul] at this; omega

def blockProduct (r : ℕ) (u v : ℕ → PowBlock) : ℕ → PowBlock := fun i =>
  blockMul r (u (i/r)) (v (i%r))

lemma blockProduct_cover {n r i j : ℕ} {f g : ℕ → PowBlock} (hr : 0 < r) (hf : PowBlockCover n i f)
    (hg : PowBlockCover r j g) : PowBlockCover (n*r) (i+j) (blockProduct r f g) := by
  have dv : ∀ k < n*r, k / r < n := fun k hk => (Nat.div_lt_iff_lt_mul hr).2 hk
  have md : ∀ k, k % r < r := fun k => Nat.mod_lt _ hr
  have mk : ∀ k < n*r, (blockProduct r f g k).Mark (n*r) (i+j) := fun k hk =>
    (hf.mark _ (dv k hk)).blockMul (hg.mark _ (md k))
  have ov : ∀ k < n*r, ∀ k' < n*r, (blockProduct r f g k).start < (blockProduct r f g k').blockEnd →
      (blockProduct r f g k').start < (blockProduct r f g k).blockEnd →
      (f (k/r)).same (f (k'/r)) ∧ (g (k%r)).same (g (k'%r)) := fun k hk k' hk' H G =>
    blockMul_unique r j (hg.mark _ (md k)) (hg.mark _ (md k')) (hf.mark _ (dv k hk))
      (hf.mark _ (dv k' hk')) (hf.seam _ (dv k hk) _ (dv k' hk')) (hg.seam _ (md k) _ (md k')) H G
  refine ⟨mk, fun k hk k' hk' => ?_, fun k hk k' hk' e => ?_⟩
  · by_cases H : (blockProduct r f g k).start < (blockProduct r f g k').blockEnd
    · by_cases G : (blockProduct r f g k').start < (blockProduct r f g k).blockEnd
      · obtain ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩⟩ := ov k hk k' hk' H G
        left
        refine ⟨?_, ?_, ?_⟩ <;> simp only [blockProduct, blockMul, a1, a2, a3, b1, b2, b3]
      · right; left; omega
    · right; right; omega
  · have pk := (mk k hk).place; have pk' := (mk k' hk').place
    have H : (blockProduct r f g k).start < (blockProduct r f g k').blockEnd := by
      unfold addr at e; unfold blockEnd; omega
    have G : (blockProduct r f g k').start < (blockProduct r f g k).blockEnd := by
      unfold addr at e; unfold blockEnd; omega
    obtain ⟨⟨a1, a2, -⟩, ⟨b1, b2, -⟩⟩ := ov k hk k' hk' H G
    have pt := (hg.mark _ (md k)).place; have pt' := (hg.mark _ (md k')).place
    simp only [blockProduct, blockMul, addr] at e
    rw [← a1, ← a2, ← b1, ← b2] at e
    rw [← b2] at pt'
    have e2 : (f (k/r)).seat * (g (k%r)).width + (g (k%r)).seat =
        (f (k'/r)).seat * (g (k%r)).width + (g (k'%r)).seat := by omega
    have s1 := DigitArith.div_join (a := (f (k/r)).seat) pt
    have s2 := DigitArith.mod_join (a := (f (k/r)).seat) pt
    rw [e2, DigitArith.div_join pt'] at s1
    rw [e2, DigitArith.mod_join pt'] at s2
    have q1 := hf.fiber _ (dv k hk) _ (dv k' hk') (by unfold addr; rw [a1, s1])
    have q2 := hg.fiber _ (md k) _ (md k') (by unfold addr; rw [b1, s2])
    rw [← Nat.div_add_mod k r, ← Nat.div_add_mod k' r, q1, q2]

end PowBlock

namespace PairBlocks
open ReelKit Stroke PowBlock
variable (u : Stroke)
def pairLead (i : ℕ) := min i (u.partner i)
def pairSize (i : ℕ) := if i=u.partner i then 1 else 2
def up (i : ℕ) := if i=u.partner i then 0 else 1
def leadSize (i : ℕ) := if i=pairLead u i then pairSize u i else 0
def pairSeat (i : ℕ) := if i=pairLead u i then 0 else 1
def leadOffset (i : ℕ) := ∑ a ∈ range i, leadSize u a
def block (i : ℕ) : PowBlock :=
  ⟨leadOffset u (pairLead u i), pairSize u i, up u i, pairSeat u i⟩
variable {u}

lemma pairLead_partner {n i : ℕ} (h : u.Sound n) : pairLead u (u.partner i)=pairLead u i := by
  unfold pairLead; rw [h.pair, min_comm]

lemma pairLead_class {n i j : ℕ} (h : u.Sound n) (g : pairLead u i=pairLead u j) :
    j=i ∨ j=u.partner i := by
  unfold pairLead at g
  rcases min_choice i (u.partner i) with a|a <;> rcases min_choice j (u.partner j) with b|b <;>
    rw [a, b] at g
  · exact .inl g.symm
  · right; rw [g, h.pair]
  · exact .inr g.symm
  · left; rw [← h.pair j, ← g, h.pair]

lemma pairLead_idem {n a : ℕ} (h : u.Sound n) : pairLead u (pairLead u a) = pairLead u a := by
  rcases min_choice a (u.partner a) with e|e <;> rw [show pairLead u a = _ from e]
  · exact e
  · rw [pairLead_partner h]; exact e

lemma pairSize_eq {n i j : ℕ} (h : u.Sound n) (g : pairLead u i=pairLead u j) :
    pairSize u j = pairSize u i ∧ up u j = up u i := by
  rcases pairLead_class h g with rfl|rfl
  · exact ⟨rfl, rfl⟩
  · unfold pairSize up; rw [h.pair]; constructor <;> split_ifs <;> first | rfl | omega

lemma leadSize_pairLead {n a : ℕ} (h : u.Sound n) : leadSize u (pairLead u a) = pairSize u a := by
  unfold leadSize; rw [if_pos (pairLead_idem h).symm]; exact (pairSize_eq h (pairLead_idem (a := a) h).symm).1

lemma leadOffset_total {n : ℕ} (h : u.Sound n) : leadOffset u n = n := by
  have key : ∀ a < n, leadSize u a = ((range n).filter fun b => pairLead u b = a).card := fun a ha => by
    unfold leadSize; split_ifs with c
    · have : (range n).filter (fun b => pairLead u b = a) = {a, u.partner a} := by
        ext b; simp only [mem_filter, mem_range, mem_insert, mem_singleton]
        constructor
        · rintro ⟨-, e⟩; exact pairLead_class h (c.symm.trans e.symm)
        · rintro (rfl|rfl)
          · exact ⟨ha, c.symm⟩
          · exact ⟨h.bdp _ ha, by rw [pairLead_partner h, ← c]⟩
      rw [this, pairSize]; split_ifs with d
      · rw [← d]; simp
      · exact (card_pair d).symm
    · refine (card_eq_zero.2 (filter_eq_empty_iff.2 fun b _ e => c ?_)).symm
      rw [← e, pairLead_idem h]
  unfold leadOffset
  rw [sum_congr rfl fun a ha => key a (mem_range.mp ha), ← card_eq_sum_card_fiberwise (f := pairLead u)
    fun b hb => mem_range.2 ((min_le_left _ _).trans_lt (mem_range.1 hb)), card_range]

theorem blockEnd_le_of_lead_lt {n a b : ℕ} (h : u.Sound n) (lt : pairLead u a < pairLead u b) :
    (block u a).blockEnd ≤ (block u b).start := by
  have m := sum_le_sum_of_subset (f := leadSize u) (range_mono (show pairLead u a + 1 ≤ pairLead u b by omega))
  rw [sum_range_succ, leadSize_pairLead h] at m; exact m

lemma marked {n i : ℕ} (h : u.Sound n) (hi : i<n) : (block u i).Mark n 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have m := sum_le_sum_of_subset (f := leadSize u) (range_mono (show pairLead u i + 1 ≤ n by
      have := min_le_left i (u.partner i); unfold pairLead; omega))
    rw [sum_range_succ, leadSize_pairLead h, show ∑ a ∈ range n, leadSize u a = n from leadOffset_total h] at m; exact m
  · show pairSize u i = 2^(up u i); unfold pairSize up; split_ifs <;> rfl
  · show up u i ≤ 1; unfold up; split_ifs <;> omega
  · show pairSeat u i < pairSize u i; unfold pairSeat pairSize pairLead; split_ifs <;> omega

lemma pairLead_of_start {n i j : ℕ} (h : u.Sound n) (hi : i<n) (hj : j<n)
    (g : (block u i).start=(block u j).start) :
    pairLead u i=pairLead u j := by
  have p1 := (marked h hi).starts; have p2 := (marked h hj).starts
  rcases lt_trichotomy (pairLead u i) (pairLead u j) with c|c|c
  · have := blockEnd_le_of_lead_lt h c; omega
  · exact c
  · have := blockEnd_le_of_lead_lt h c; omega

lemma pairSeat_partner_ne {n i : ℕ} (h : u.Sound n) (g : u.partner i ≠ i) :
    pairSeat u (u.partner i) ≠ pairSeat u i := by
  unfold pairSeat; rw [pairLead_partner h]; unfold pairLead; split_ifs <;> omega

lemma pairBlocks_cover {n : ℕ} (h : u.Sound n) : PowBlockCover n 1 (block u) := by
  refine ⟨fun i hi => marked h hi, fun i hi j hj => ?_, fun i hi j hj e => ?_⟩
  · rcases lt_trichotomy (pairLead u i) (pairLead u j) with c|c|c
    · exact .inr (.inl (blockEnd_le_of_lead_lt h c))
    · obtain ⟨a, b⟩ := pairSize_eq h c
      exact .inl ⟨by show leadOffset u _ = leadOffset u _; rw [c], a.symm, b.symm⟩
    · exact .inr (.inr (blockEnd_le_of_lead_lt h c))
  · have pi := (marked h hi).place; have pj := (marked h hj).place
    unfold addr at e
    rcases lt_trichotomy (pairLead u i) (pairLead u j) with c|c|c
    · have := blockEnd_le_of_lead_lt h c; unfold blockEnd at *; omega
    · rcases pairLead_class h c with d|d
      · exact d.symm
      · by_cases q : u.partner i = i
        · rw [d, q]
        · have := pairSeat_partner_ne h q; rw [← d] at this
          simp only [block] at e; rw [c] at e; omega
    · have := blockEnd_le_of_lead_lt h c; unfold blockEnd at *; omega

end PairBlocks
open PowBlock PairBlocks

def unitBlock : PowBlock := ⟨0,1,0,0⟩

def strokeBlocks (r : Axes) (u : ℕ → Stroke) : ℕ → ℕ → PowBlock
  | 0 => fun _ => unitBlock
  | l+1 => blockProduct (r l) (strokeBlocks r u l) (block (u l))

lemma strokeBlocks_cover (r : Axes) (l : ℕ) (u : ℕ→Stroke)
    (h : Splits r l) (g : ∀ i<l, (u i).Sound (r i)) :
    PowBlockCover (extent r l) l (strokeBlocks r u l) := by
  induction l with
  | zero =>
    refine ⟨fun i hi => ⟨?_, rfl, le_rfl, Nat.one_pos⟩, fun i _ j _ => Or.inl ⟨rfl, rfl, rfl⟩,
      fun i hi j hj _ => ?_⟩
    · show 0 + 1 ≤ 1; omega
    · simp only [extent] at hi hj; omega
  | succ l ih =>
    exact blockProduct_cover (by have := h l (by omega); omega) (ih (h.cut (by omega))
      (fun i hi => g i (by omega))) (pairBlocks_cover (g l (by omega)))

end
end PowerSaving.AxisTensor
end OAI

namespace OAI
namespace PowerSaving.AxisTensor
open Finset Spectral
noncomputable section

structure CoprimeAxes (r : Axes) (l : ℕ) : Prop where
  good : Splits r l
  apart : ∀ i<l, (r i).Coprime (extent r i)

lemma CoprimeAxes.cut {r : Axes} {l : ℕ} (h : CoprimeAxes r l) {i : ℕ} (hi : i ≤ l) :
    CoprimeAxes r i := ⟨h.good.cut hi, fun j hj => h.apart j (by omega)⟩

def crtJoin (p r a b : ℕ) := (a*r+b*p)%(p*r)

def crtIndex (r : Axes) : ℕ → ℕ → ℕ
  | 0 => fun _ => 0
  | l+1 => fun i =>
    crtJoin (extent r l) (r l) (crtIndex r l (i/r l)) (i%r l)

def axisRoot (Z : ℂ) (N q : ℕ) := Z^((N/q)*(N/q))

def powMat (Z : ℂ) : IdxMat := fun i j => Z^(i*j)

lemma split_axis {r : Axes} {l : ℕ} (h : CoprimeAxes r l) :
    ∀ i < l, r i ∣ extent r l ∧ (r i).Coprime (extent r l / r i) := by
  induction l with
  | zero => intro i hi; omega
  | succ l ih =>
    intro i hi
    have hr : 0 < r l := by have := h.good l (by omega); omega
    rcases Nat.lt_or_ge i l with hil | hil
    · obtain ⟨d, c⟩ := ih (h.cut (by omega)) i hil
      refine ⟨Dvd.dvd.mul_right d _, ?_⟩
      show (r i).Coprime (extent r l * r l / r i)
      rw [← Nat.div_mul_right_comm d]
      exact c.mul_right (Nat.Coprime.coprime_dvd_right d (h.apart l (by omega))).symm
    · obtain rfl : i = l := by omega
      refine ⟨dvd_mul_left _ _, ?_⟩
      show (r i).Coprime (extent r i * r i / r i)
      rw [Nat.mul_div_cancel _ hr]; exact h.apart i (by omega)

lemma prim_pow_coprime {ζ : ℂ} {k m : ℕ} (h : PrimRoot ζ k) (hc : m.Coprime k) :
    PrimRoot (ζ^m) k :=
  ⟨by rw [← pow_mul, mul_comm, pow_mul, h.pow_eq_one, one_pow],
   fun l hl => hc.symm.dvd_mul_left.mp (h.dvd_of_pow_eq_one _ (by rw [pow_mul, hl]))⟩

lemma axisRoot_primitive {Z : ℂ} {r : Axes} {l : ℕ} (h : CoprimeAxes r l)
    (hh : Spectral.PrimRoot Z (extent r l)) :
    ∀ i<l, Spectral.PrimRoot (axisRoot Z (extent r l) (r i)) (r i) := fun i hi => by
  obtain ⟨d, c⟩ := split_axis h i hi
  have hE := h.good.extent_pos
  have hri : 0 < r i := by have := h.good i hi; omega
  have hp : 0 < extent r l / r i := Nat.div_pos (Nat.le_of_dvd hE d) hri
  have h1 := hh.pow_of_dvd (Nat.pos_iff_ne_zero.mp hp) (Nat.div_dvd_of_dvd d)
  rw [Nat.div_div_self d (by omega)] at h1
  unfold axisRoot; rw [pow_mul]
  exact prim_pow_coprime h1 c.symm

lemma crtJoin_inj {p r a b a' b' : ℕ} (hc : p.Coprime r) (ha : a < p) (ha' : a' < p) (hb : b < r)
    (hb' : b' < r) (e : crtJoin p r a b = crtJoin p r a' b') : a = a' ∧ b = b' := by
  unfold crtJoin at e
  have e1 : (a*r+b*p) % (p*r) % p = (a'*r+b'*p) % (p*r) % p := by rw [e]
  have e2 : (a*r+b*p) % (p*r) % r = (a'*r+b'*p) % (p*r) % r := by rw [e]
  rw [Nat.mod_mod_of_dvd _ (dvd_mul_right p r), Nat.mod_mod_of_dvd _ (dvd_mul_right p r),
    Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right] at e1
  rw [Nat.mod_mod_of_dvd _ (dvd_mul_left r p), Nat.mod_mod_of_dvd _ (dvd_mul_left r p),
    add_comm (a*r), add_comm (a'*r), Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right] at e2
  have f1 := Nat.ModEq.cancel_right_of_coprime hc e1
  have f2 := Nat.ModEq.cancel_right_of_coprime hc.symm e2
  unfold Nat.ModEq at f1 f2
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha'] at f1
  rw [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hb'] at f2
  exact ⟨f1, f2⟩

theorem crtIndex_reloc {r : Axes} {l : ℕ} (h : CoprimeAxes r l) :
    Reloc (extent r l) (crtIndex r l) := by
  induction l with
  | zero => exact ⟨fun _ _ => Nat.one_pos, fun i hi j hj _ => by simp only [extent] at hi hj; omega⟩
  | succ l ih =>
    have R := ih (h.cut (by omega))
    have g := h.good
    have hr : 0 < r l := by have := g l (by omega); omega
    have hE := (g.cut (Nat.le_succ l)).extent_pos
    refine ⟨fun j _ => Nat.mod_lt _ (Nat.mul_pos hE hr), fun i hi j hj e => ?_⟩
    obtain ⟨e1, e2⟩ := crtJoin_inj (h.apart l (by omega)).symm (R.bd _ (g.div_lt hi))
      (R.bd _ (g.div_lt hj)) (g.mod_lt i) (g.mod_lt j) e
    have := R.inj _ (g.div_lt hi) _ (g.div_lt hj) e1
    rw [← Nat.div_add_mod i (r l), ← Nat.div_add_mod j (r l), this, e2]

lemma pow_eq_of_mod {z : ℂ} {N a b : ℕ} (hz : z^N = 1) (h : a % N = b % N) : z^a = z^b := by
  rw [← power_mod hz a, h, power_mod hz]

lemma axisKron_powMat {r : Axes} {E : ℕ} {z : ℂ} (hz : z^E = 1) : ∀ l Q, E = Q * extent r l →
    (∀ j < l, 0 < r j) → ∀ i k, axisKron r (fun j => powMat (axisRoot z E (r j))) l i k =
      z^(Q*Q*(crtIndex r l i * crtIndex r l k))
  | 0, _, _, _, _, _ => by simp [axisKron, crtIndex]
  | l+1, Q, hE, hp, i, k => by
    have hr := hp l (Nat.lt_succ_self l)
    simp only [extent] at hE
    have hd : E / r l = Q * extent r l := by rw [hE, ← mul_assoc, Nat.mul_div_cancel _ hr]
    show axisKron r _ l (i / r l) (k / r l) * powMat (axisRoot z E (r l)) (i % r l) (k % r l) =
      z^(Q*Q*(crtJoin (extent r l) (r l) (crtIndex r l (i / r l)) (i % r l) *
        crtJoin (extent r l) (r l) (crtIndex r l (k / r l)) (k % r l)))
    rw [axisKron_powMat hz l (Q * r l) (by rw [hE]; ring) fun j hj => hp j (Nat.lt_succ_of_lt hj)]
    simp only [powMat, axisRoot, crtJoin, hd]
    rw [← pow_mul, ← pow_add]
    refine pow_eq_of_mod hz ?_
    generalize crtIndex r l (i / r l) = a; generalize crtIndex r l (k / r l) = a'
    generalize i % r l = b; generalize k % r l = b'
    generalize extent r l = P at hE ⊢; generalize r l = R at hE ⊢
    subst hE
    have M := ((Nat.mod_modEq (a*R+b*P) (P*R)).mul (Nat.mod_modEq (a'*R+b'*P) (P*R))).mul_left'
      (Q*Q)
    rw [show Q*Q*(P*R) = Q*(Q*(P*R)) by ring] at M
    refine ((M.of_mul_left Q).trans ?_).symm
    rw [show Q*Q*((a*R+b*P)*(a'*R+b'*P)) = Q*R*(Q*R)*(a*a') + Q*P*(Q*P)*(b*b') +
      Q*(P*R)*(Q*(a*b'+a'*b)) by ring]
    exact Nat.add_mul_mod_self_left _ _ _

lemma crt_freq {r : Axes} {l : ℕ} {z : ℂ} (h : CoprimeAxes r l)
    (hh : Spectral.PrimRoot z (extent r l)) (x : Line) (i : ℕ) (hi : i<extent r l) :
    idxApply (extent r l) (axisKron r (fun i => powMat (axisRoot z (extent r l) (r i))) l)
      (fun j => x (crtIndex r l j)) i =
    freq (extent r l) z x (crtIndex r l i) := by
  simp only [idxApply, axisKron_powMat hh.pow_eq_one l 1 (one_mul _).symm fun j hj => by
    have := h.good j hj; omega, one_mul]
  exact (crtIndex_reloc h).sum (fun m => z^(crtIndex r l i * m) * x m)

end
end PowerSaving.AxisTensor
end OAI
end
