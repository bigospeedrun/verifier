--might be  containing modified Apache-2.0 codes pieces from one or several sources; notices and credits: Credits.lean
import Submission.Compiler.Judgment
import Submission.Ripple.RoleMoves
namespace OAI
namespace PowerSaving.AxisTensor
open ReelKit
def climb {α : Type*} (r : Axes) (x : α)
    (step : ℕ → ℕ → ℕ → α → α) : ℕ → ℕ → α
  | 0 => fun _ => x
  | l+1 => fun i => step l (i/r l) (i%r l) (climb r x step l (i/r l))
def survey (r : Axes) (u : ℕ → Stroke) : ℕ → ℕ → ℕ × ℂ :=
  climb r (0,1) fun i _ a s => (s.1*r i+(u i).ix a,s.2*(u i).dye a)
end PowerSaving.AxisTensor
namespace PowerSaving.RAM
open Ty ReelKit ReelKit.Stroke
noncomputable section
abbrev arrowTy := p w (p sc w)
abbrev stripeTy := a arrowTy
abbrev filmTy := a stripeTy
def emboss (s : Stroke) (i : ℕ) : T arrowTy := (s.ix i,s.dye i,s.partner i)
def stripe (n : ℕ) (s : Stroke) : T stripeTy := Tape.tab n (emboss s)
def film (n : ℕ) (r : Reel) : T filmTy := Tape.tab r.beats fun i => stripe n (r.atBeat i)
def tickCount {ι : Type*} (r : ι→Reel) := fun i => (r i).beats
section
open AxisTensor PowBlock ReelKit PairBlocks
abbrev chipTy := p w (p w (p w w))
abbrev sapTy := p w sc
abbrev blossomTy := p sapTy chipTy
abbrev leafTy := a blossomTy
abbrev treeTy := a leafTy
def chip (s : PowBlock) : T chipTy := (s.start,s.width,s.height,s.seat)
def blossom (u : Stroke) (i : ℕ) : T blossomTy := ((u.ix i,u.dye i),chip (block u i))
def leavesT (n : ℕ) (u : Stroke) : T leafTy := Tape.tab n (blossom u)
def treeT (n : ℕ) (u : Reel) : T treeTy := Tape.tab u.beats fun i => leavesT n (u.atBeat i)
end
universe U V
namespace Bench
variable {m : Bool} {ι : Type U} {κ : Type V} {b : Bench m ι} {q : Bench m κ}
lemma Makes.pick {t : Ty} {n : ι→ℕ} (x : ι→ℕ→T t)
    (h : b.Makes (a t) (fun i => Tape.tab (n i) (x i)))
    {k} (g : b.Makes w k) (hk : ∀ i, k i<n i) :
    b.Makes t (fun i => x i (k i)) :=
  (h.look g).congr fun i => by rw [Tape.look_tab, if_pos (hk i)]
section
open Complex
structure Hue (b : Bench m ι) (f : ι→ℂ) : Prop where
  bright : b.Makes sc f
  dull : b.Makes sc (fun i => starRingEnd ℂ (f i))
variable {f : ι→ℂ}
lemma Hue.transfer {p : ι→κ} {f : κ→ℂ} (h : q.Hue f) (g : b.Feeds q p) :
    b.Hue (fun i => f (p i)) := ⟨pull g h.1, pull g h.2⟩
lemma Hue.letterI (h : b.Makes sc fun _ => I) : b.Hue (fun _ => I) := ⟨h, h.neg.congr fun _ => conj_I.symm⟩
lemma Hue.of_root {n : ι→ℕ} (h : b.Makes sc f) (hn : ∀ i, 0<n i)
    (hf : ∀ i, f i ^ n i = 1) : b.Hue f :=
  ⟨h, (h.inv fun i e => by simpa [e, zero_pow (hn i).ne'] using hf i).congr fun i => (Spectral.conj_of_root (hn i) (hf i)).symm⟩
end
def Fabric (b : Bench m ι) (n : ι→ℕ) (x : ι → Line) : Prop :=
  (b.scan n).Hue (fun i => x i.i i.j)
lemma Fabric.transfer {n : κ→ℕ} {x : κ→Line} (h : q.Fabric n x) {f} (g : b.Feeds q f) :
    b.Fabric (fun i => n (f i)) (fun i => x (f i)) :=
  Hue.transfer (p := fun d : During _ => (⟨f d.i, d.j, d.hj⟩ : During n)) h (((Feeds.scan b _).next g).select (toppings _ _))
structure Engrave (b : Bench m ι) (n : ι→ℕ) (r : ι→Reel) : Prop where
  sound : ∀ i,(r i).Sound (n i)
  count : b.Digit (tickCount r)
  width : b.Digit n
  layers : b.Makes filmTy (fun i => film (n i) (r i))
variable {n : ι→ℕ}
lemma sums_le (u : Stroke) (k : ℕ) : AxisTensor.PairBlocks.sums u k ≤ 2*k :=
  (Finset.sum_le_card_nsmul _ _ 2 fun a _ => by unfold AxisTensor.PairBlocks.trim AxisTensor.PairBlocks.thickness; split_ifs <;> omega).trans (by simp [mul_comm])
open AxisTensor
structure Fen (b : Bench m ι) (l : ι→ℕ) (r : ι→Axes) : Prop where
  high : b.Nick l
  good : ∀ i,Splits (r i) (l i)
  span : Small b.size fun i => extent (r i) (l i)
  part : (b.scan l).Nick fun d => r d.i d.j
abbrev routes {ι : Type*} (l : ι→ℕ) (r : ι→Axes) (d : During l) :=
  extent (r d.i) (d.j+1)
abbrev Forks (l : ι→ℕ) (r : ι→Axes) := During (routes l r)
namespace Forks
variable {l : ι→ℕ} {r : ι→Axes}
def tUp (d : Forks l r) := d.j/r d.i.i d.i.j
def tOff (d : Forks l r) := d.j%r d.i.i d.i.j
end Forks
namespace Fen
open Forks
variable {l : ι→ℕ} {r : ι→Axes} {s : Ty}
lemma scanInstant {l : κ→ℕ} {f} (g : b.Instant q f) :
    (b.scan fun i => l (f i)).Instant (q.scan l) fun d => ⟨f d.i, d.j, d.hj⟩ := ((Instant.scan _ _).next g).select (cherry _ _)
lemma transfer {l : κ→ℕ} {r : κ→Axes} (h : q.Fen l r) {f} (g : b.Instant q f) :
    b.Fen (fun i => l (f i)) (fun i => r (f i)) :=
  ⟨h.1.transfer g, fun i => h.2 (f i), (h.3.reindex f).trans g.2, h.4.transfer (scanInstant g)⟩
lemma midst (h : b.Fen l r) :
    Small (fun d : During l => b.size d.i) fun d => extent (r d.i) d.j :=
  (h.3.reindex During.i).mono fun d => (h.2 d.i).extent_le d.hj.le
lemma smaller (h : b.Fen l r) (d : Forks l r) : tUp d<extent (r d.i.i) d.i.j :=
  ((h.2 _).cut d.i.hj).div_lt d.hj
lemma lower (h : b.Fen l r) (d : Forks l r) : tOff d<r d.i.i d.i.j :=
  ((h.2 _).cut d.i.hj).mod_lt _
def stalk (b : Bench m ι) (l : ι→ℕ) (r : ι→Axes) (s : Ty) (S : ι → ℕ → ℕ → T s) :
    Bench m (Forks l r) :=
  ((b.scan l).along During.i).extend (p w (p w s))
    (fun i => (tUp i,tOff i,S i.i.i i.i.j (tUp i)))
lemma stalkFeeds (b : Bench m ι) (l : ι→ℕ) (r : ι→Axes) (s : Ty) (S : ι → ℕ → ℕ → T s) :
    (stalk b l r s S).Instant (b.scan l) During.i := (Instant.extend _ _).next (Instant.along _ _)
lemma stalkReads (h : b.Fen l r) (S : ι → ℕ → ℕ → T s) :
    let B := stalk b l r s S
    B.Nick tUp ∧ B.Nick tOff ∧ B.Moves (fun _ => 0) s (fun i => S i.i.i i.i.j (tUp i)) :=
  have M := cherry ((b.scan l).along During.i) (t := p w (p w s)) _
  ⟨⟨M.fst, (h.3.reindex fun d : Forks l r => d.i.i).mono fun d => ((h.smaller d).trans_le ((h.2 _).extent_le d.i.hj.le)).le⟩,
   ⟨M.snd.fst, (h.4.2.reindex During.i).mono fun d => (h.lower d).le⟩, M.snd.snd⟩
theorem visit (h : b.Fen l r) (S : ι → ℕ → ℕ → T s)
    (hS : b.Moves (fun _ => 0) s fun i => S i 0 0)
    (hs : (stalk b l r s S).Moves (fun _ => 0) s fun d => S d.i.i (d.i.j+1) d.j) :
    b.Moves (fun i => extent (r i) (l i)) (a s) fun i =>
      Tape.tab (extent (r i) (l i)) (S i (l i)) := by
  let f : ι → ℕ → T (a s) := fun i k => Tape.tab (extent (r i) k) (S i k)
  have I0 : (b.climbs l (a s) f).Instant (b.scan l) id := (Instant.climbs ..).select (stride h.1 f).1
  have T0 := tokenNow b l f
  have Nr := h.4.transfer I0
  have NE : (b.climbs l (a s) f).Nick fun d => extent (r d.i) d.j * r d.i d.j :=
    Nick.mul ⟨T0.len h.midst, h.midst⟩ Nr
  have I1 := Instant.scan (b.climbs l (a s) f) fun d => extent (r d.i) d.j * r d.i d.j
  have Nj := chop NE; have Nr' := Nr.transfer I1
  have IA : (b.climbs l (a s) f |>.scan fun d => extent (r d.i) d.j * r d.i d.j).Instant
      ((b.scan l).along During.i) (fun e => (⟨e.i, e.j, e.hj⟩ : Forks l r)) := ⟨(I1.next I0).1, (I1.next I0).2⟩
  have B := hs.transfer (IA.supply _ ((Nj.div Nr').1.pair ((Nj.residue Nr').1.pair
    ((T0.transfer I1).pick _ (Nj.div Nr').1 fun e => ((h.2 _).cut e.i.hj).div_lt e.hj))))
  refine ((repeatM (u := fun i k => extent (r i) k * r i k) h.1 f ((arrayNow (Nick.wc 1) (fun i j => S i 0 j) ((hS.transfer (Instant.scan _ _)).congr fun d => by
    rw [show d.j = 0 by have := d.hj; omega])).weaken (Dom.const _ 1)) (arrayNow NE (fun d j => S d.i (d.j+1) j) B)).weaken ⟨3, fun i => ?_⟩)
  have := (h.2 i).tree_bound; have := (h.2 i).axes_le; have := Finset.sum_range_succ' (fun j => extent (r i) j) (l i)
  dsimp only [extent] at *; omega
end Fen
structure Arch (b : Bench m ι) (e : ι→ℕ) : Prop where
  ep : b.Digit e
  span : b.Digit (fun i => 2^e i)
variable {e : ι→ℕ}
lemma Arch.transfer {e : κ→ℕ} (h : q.Arch e) {f : ι→κ} (F : b.Feeds q f) :
    b.Arch (fun i => e (f i)) := ⟨draw F h.1, draw F h.2⟩
lemma Digit.pow2 (h : b.Digit e) (g : Small b.size (fun i => 2^e i)) : b.Digit (fun i => 2^e i) :=
  ⟨loop h _ (Makes.wc 1) (let D : (b.climbs e w fun _ j => 2^j).Digit fun d => 2^d.j :=
    ⟨stepsum .., (g.reindex During.i).mono fun d => Nat.pow_le_pow_right two_pos d.hj.le⟩
    (D.add D).1.congr fun d => by rw [pow_succ, mul_two]), g⟩
lemma Arch.fromSmall (h : b.Digit e) (g : Small b.size (fun i => 2^e i)) : b.Arch e := ⟨h, h.pow2 g⟩
lemma reachD (h : b.Digit e) : b.Digit fun i => reachSize (e i) :=
  let p := (h.minimum (.wc 3)).pow2 ((Small.const _ 8).mono fun i => Nat.pow_le_pow_right two_pos (min_le_right _ 3))
  (iteN (Study.lt h (.wc 4)) (p.mul (p.mul (p.mul (.wc 26)))) ((Digit.wc 16).mul ((Digit.wc 16).mul ((Digit.wc 16).mul
    ((Digit.wc 4).mul (((Digit.wc 80).mul (h.sub (.wc 4))).add (.wc 348))))))).congr fun i => by
    unfold reachSize; split_ifs with c
    · rw [Nat.min_eq_left (by omega : e i ≤ 3)]
    · rfl
lemma chorusDigit {e : ι→ℕ} (h : b.Digit e) : b.Digit fun k => chorus (e k) :=
  have S : Small b.size fun i => 10000000*(e i+1)^2 := (Small.const _ _).mul ((h.2.add (.const _ 1)).pow 2)
  ⟨loop (t := w) h (fun _ j => chorus j) (Makes.wc 1) (Digit.add ⟨stepsum .., (S.reindex During.i).mono fun d =>
    (chorus_le _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (show d.j+1 ≤ e d.i+1 by have := d.hj; omega) 2))⟩ (reachD (stepi h _))).1,
    S.mono fun _ => chorus_le _⟩
lemma chorus_digit {e : ι→ℕ} (h : b.Arch e) : b.Digit (fun i => chorus (e i)) := chorusDigit h.1
section
open Complex Spectral Finset
variable {c : Bench m ι} {μ : Type U} {c' : Bench m μ} {f : μ→ι}
def Lit (c : Bench m ι) (F : ι→ℕ→ℂ) : Prop :=
  ∀ (μ : Type U) (c' : Bench m μ) (f : μ→ι) (j : μ→ℕ), c'.Feeds c f → c'.Digit j →
    c'.Makes sc fun k => F (f k) (j k)
namespace Play
variable {R A B : ι→Reel}
lemma strand_at (a : ℕ→Reel) (B : ℕ) : ∀ L t, (∀ i<L, (a i).beats=B) → t<L*B →
    (strand a L).atBeat t = (a (t/B)).atBeat (t%B) := by
  intro L; induction L with
  | zero => intro t _ ht; simp at ht
  | succ L ih =>
    intro t h ht
    have hB := beat_strand L B fun i hi => h i (by omega)
    show ((strand a L).stack (a L)).atBeat t = _
    simp only [Reel.stack, hB]; rw [Nat.succ_mul] at ht; split_ifs with c
    · exact ih t (fun i hi => h i (by omega)) c
    · have q : t / B = L := Nat.div_eq_of_lt_le (by omega) (by rw [Nat.succ_mul]; omega)
      rw [Nat.mod_def, q, mul_comm]
end Play
namespace Lit
variable {F G : ι→ℕ→ℂ}
lemma at_ {j : ι→ℕ} (h : c.Lit F) (hj : c.Digit j) : c.Makes sc fun k => F k (j k) := h _ c id j ⟨c.prepares, Small.self _⟩ hj
lemma pow {z : ι→ℂ} (h : c.Makes sc z) : c.Lit fun k i => z k^i := fun _ _ _ _ hf hj =>
  loop hj _ (Makes.one.congr fun _ => (pow_zero _).symm) (((stepsum ..).mul (pull ((Feeds.climbs ..).next hf) h)).congr fun _ => (pow_succ ..).symm)
end Lit
lemma blaze_ne (z : ℂ) : 1+z*starRingEnd ℂ z ≠ 0 := ReelKit.blaze_ne (fun _ => z) 0
lemma blaze_sub_ne (z : ℂ) : z-(1+z*starRingEnd ℂ z) ≠ 0 := after_ne (fun _ => z) 0
lemma gap_zero {z : ℂ} {n i : ℕ} (hp : Spectral.PrimRoot z n) (hn : 0<n) (hi : n ≤ i) : gap z i = 0 :=
  prod_eq_zero (mem_range.2 (show n-1 < i by omega)) (by rw [Nat.sub_add_cancel hn, hp.pow_eq_one, sub_self])
lemma recoil_succ (H : Line) (k : ℕ) :
    toeplitzInv H (k+1) = -(∑ x ∈ range (k+1), toeplitzInv H (k-x)*H (x+1))/H 0 := by
  simp [toeplitzInv, recoilTo, recoilTo_stable H k _ (Nat.sub_le k _)]
lemma conj_recoil (H : Line) (j : ℕ) :
    starRingEnd ℂ (toeplitzInv H j) = toeplitzInv (fun i => starRingEnd ℂ (H i)) j := by
  induction j using Nat.strong_induction_on with
  | _ j ih => cases j with
    | zero => simp [toeplitzInv, recoilTo]
    | succ k => simp [recoil_succ, map_sum, ih _ (Nat.lt_succ_of_le (Nat.sub_le k _))]
lemma mod_two (v e : ℕ) : v%2^(e+1) = if v%2^(e+1)<2^e then v%2^e else v%2^e+2^e := by
  rw [Nat.mod_pow_succ]; have := Nat.mod_lt (v/2^e) two_pos; have := Nat.mod_lt v (Nat.two_pow_pos e)
  rcases (show v/2^e%2 = 0 ∨ v/2^e%2 = 1 by omega) with e|e <;> simp [e, this]
end
section
open Complex Finset Spectral
variable {ν : Type U} {c : Bench m ι} {d : Bench m ν} {A B : ι → Reel} {x y : ι → ℕ} {F G : ι → Line}
local notation "FS" => Feeds.scan _ _
local notation "RS" => restricted _ _
lemma Digit.div (h : c.Digit x) (g : c.Digit y) : c.Digit fun k => x k / y k := ⟨PolyCan.wdiv h.1 g.1 h.2.div, h.2.div⟩
lemma Digit.mod (h : c.Digit x) (g : c.Digit y) : c.Digit fun k => x k % y k := ⟨PolyCan.wmod h.1 g.1 h.2.mod, h.2.mod⟩
lemma Feeds.into {P : ι → Prop} {g : ν → {i // P i}} (h : d.Feeds c fun k => (g k).1) : d.Feeds (c.scrutin P) g := ⟨h.1, h.2⟩
lemma Feeds.res {P : ν → Prop} {f : ν → ι} (hf : d.Feeds c f) : (d.scrutin P).Feeds c fun k => f k.1 := (restricted d P).next hf
lemma Study.on {P : ι → Prop} (h : c.Study P) {f : ν → ι} (hf : d.Feeds c f) : d.Study fun k => P (f k) :=
  let ⟨_, hx, e⟩ := h; ⟨_, draw hf hx, fun _ => e _⟩
lemma Makes.ite {P : ι → Prop} [DecidablePred P] {t} {x y : ι → T t} (h : c.Study P) (a : c.Makes t x) (b : c.Makes t y) :
    c.Makes t fun k => if P k then x k else y k := branchM h (pull RS a) (pull RS b)
lemma Makes.sum {N : ι → ℕ} {F : ι → ℕ → ℂ} (hN : c.Digit N) (hF : (c.scan N).Makes sc fun e => F e.i e.j) :
    c.Makes sc fun k => ∑ j ∈ range (N k), F k j :=
  loop (t := sc) hN (fun k i => ∑ j ∈ range i, F k j) (Makes.zero.congr fun _ => rfl)
    (((stepsum ..).add (pull ((Feeds.climbs ..).select (stepi hN _).1) hF)).congr fun _ => (sum_range_succ ..).symm)
lemma Makes.prod {N : ι → ℕ} {F : ι → ℕ → ℂ} (hN : c.Digit N) (hF : (c.scan N).Makes sc fun e => F e.i e.j) :
    c.Makes sc fun k => ∏ j ∈ range (N k), F k j :=
  loop (t := sc) hN (fun k i => ∏ j ∈ range i, F k j) (Makes.one.congr fun _ => rfl)
    (((stepsum ..).mul (pull ((Feeds.climbs ..).select (stepi hN _).1) hF)).congr fun _ => (prod_range_succ ..).symm)
lemma Makes.cast {N : ι → ℕ} (hN : c.Digit N) : c.Makes sc fun k => (N k : ℂ) :=
  loop (t := sc) hN (fun _ i => (i : ℂ)) (Makes.zero.congr fun _ => Nat.cast_zero.symm) (((stepsum ..).add Makes.one).congr fun _ => (Nat.cast_succ _).symm)
lemma Digit.sum {M : ι → ℕ} {F : ι → ℕ → ℕ} (hM : c.Digit M) (hF : (c.scan M).Digit fun e => F e.i e.j)
    (hs : Small c.size fun k => ∑ a ∈ range (M k), F k a) : c.Digit fun k => ∑ a ∈ range (M k), F k a :=
  ⟨loop (t := w) hM (fun k i => ∑ a ∈ range i, F k a) ((Makes.wc 0).congr fun _ => rfl)
    ((Digit.add ⟨stepsum .., (hs.reindex During.i).mono fun e => sum_le_sum_of_subset (range_mono e.hj.le)⟩
      (draw ((Feeds.climbs ..).select (stepi hM _).1) hF)).1.congr fun _ => (sum_range_succ ..).symm), hs⟩
open AxisTensor.PairBlocks in
lemma hemChip {S : ι → Stroke} {N j : ι → ℕ} (hP : ∀ (ν : Type U) (d : Bench m ν) (f : ν → ι) (j : ν → ℕ), d.Feeds c f →
    d.Digit j → (∀ k, j k < N (f k)) → d.Digit fun k => (S (f k)).partner (j k)) (hN : Small c.size N) (hj : c.Digit j)
    (hjN : ∀ k, j k < N k) : c.Makes chipTy fun k => chip (block (S k) (j k)) :=
  have hP' := hP _ c id j ⟨c.prepares, Small.self _⟩ hj hjN
  have cr := hj.minimum hP'; have s := slot cr
  have hP := hP _ _ _ _ FS s fun e => by have := e.hj; have := hjN e.i; unfold crown at *; omega
  have E := Study.eq hj hP'
  (Digit.sum (F := fun k a => trim (S k) a) cr (iteN (Study.eq s (s.minimum hP)) (iteN (Study.eq s hP) (.wc 1) (.wc 2)) (.wc 0))
    ((hN.add hN).mono fun k => (sums_le _ _).trans (by have := hjN k; omega))).1.pair
    ((iteN E (.wc 1) (.wc 2)).1.pair ((iteN E (.wc 0) (.wc 1)).1.pair (iteN (Study.eq hj cr) (.wc 0) (.wc 1)).1))
namespace Lit
lemma congr (h : c.Lit F) (e : ∀ k i, F k i = G k i) : c.Lit G := fun _ _ _ _ hf hj => (h _ _ _ _ hf hj).congr fun _ => e _ _
lemma const {z : ι → ℂ} (h : c.Makes sc z) : c.Lit fun k _ => z k := fun _ _ _ _ hf _ => pull hf h
lemma rat (z : ℚ) : c.Lit fun _ _ => (z : ℂ) := fun _ _ _ _ _ _ => ⟨0, Can.rat z⟩
lemma on (h : c.Lit F) {f : ν → ι} (hf : d.Feeds c f) : d.Lit fun k => F (f k) := fun _ _ _ _ hg => h _ _ _ _ (hg.next hf)
lemma one : c.Lit fun _ _ => 1 := fun _ _ _ _ _ _ => Makes.one
lemma lift (o : ℂ → ℂ → ℂ) (p : ∀ {ν : Type U} {d : Bench m ν} {x y}, d.Makes sc x → d.Makes sc y → d.Makes sc fun k => o (x k) (y k))
    (h : c.Lit F) (g : c.Lit G) : c.Lit fun k i => o (F k i) (G k i) := fun _ _ _ _ hf hj => p (h _ _ _ _ hf hj) (g _ _ _ _ hf hj)
lemma add : c.Lit F → c.Lit G → c.Lit fun k i => F k i + G k i := lift _ Makes.add
lemma sub : c.Lit F → c.Lit G → c.Lit fun k i => F k i - G k i := lift _ Makes.sub
lemma mul : c.Lit F → c.Lit G → c.Lit fun k i => F k i * G k i := lift _ Makes.mul
lemma inv (h : c.Lit F) (nz : ∀ k i, F k i ≠ 0) : c.Lit fun k i => (F k i)⁻¹ := fun _ _ _ _ hf hj => (h _ _ _ _ hf hj).inv fun _ => nz _ _
lemma invZ (h : c.Lit F) {N : ι → ℕ} (hN : c.Digit N) (hz : ∀ k i, F k i = 0 ↔ N k ≤ i) : c.Lit fun k i => (F k i)⁻¹ :=
  fun _ d f j hf hj => (branchM (x := fun k => (F (f k) (j k))⁻¹) (y := fun _ => 0) (Study.lt hj (draw hf hN)) ((h _ _ _ _ hf.res
    (draw RS hj)).inv fun k => mt (hz _ _).1 (not_le.2 k.2)) (Makes.zero (cl := .scalar))).congr fun k => by
    dsimp only; split_ifs with e; rfl; rw [(hz _ _).2 (not_lt.1 e), inv_zero]
lemma gap {z : ι → ℂ} (h : c.Makes sc z) : c.Lit fun k i => gap (z k) i := fun _ _ _ _ hf hj =>
  Makes.prod hj (Makes.one.sub (pow h _ _ _ _ (Feeds.next FS hf) ((slot hj).add (.wc 1))))
lemma roof {z : ι → ℂ} (h : c.Makes sc z) : c.Lit fun k i => roof (z k) i := fun _ _ _ _ hf hj =>
  Makes.prod hj (pow h _ _ _ _ (Feeds.next FS hf) (slot hj)).neg
lemma freq {N : ι → ℕ} {z : ι → ℂ} (hN : c.Digit N) (hz : c.Makes sc z) (h : c.Lit F) : c.Lit fun k i => freq (N k) (z k) (F k) i :=
  fun _ _ _ _ hf hj => have hN := draw hf hN; have g := Feeds.next FS hf
    Makes.sum hN ((pow hz _ _ _ _ g ((draw FS hj).mul (slot hN))).mul (h _ _ _ _ g (slot hN)))
lemma rise (h : c.Lit F) (hx : c.Digit x) (hy : c.Digit y) : c.Makes sc fun k => Spectral.rise (F k) (x k) (y k) :=
  Makes.ite (Study.le hy hx) (h.at_ (hx.sub hy)) Makes.zero
lemma skirt {B E S L M : ι → ℕ} (hB : c.Digit B) (hE : c.Digit E) (hS : c.Digit S) (hL : c.Digit L) (hM : c.Digit M) (h : c.Lit F) :
    c.Lit fun k i => skirt (B k) (E k) (S k) (L k) (M k) (F k) i := fun _ _ _ _ hf hj =>
  have g := fun {x : ι → ℕ} (h : c.Digit x) => draw hf h; have h := h.on hf; have b := ((Digit.wc 2).mul (g hB)).sub hj
  Makes.ite (Study.lt hj (g hB)) (Makes.ite (Study.lt hj (g hS)) (h.rise ((g hM).add hj) (g hL)) Makes.zero)
    (Makes.ite ((Study.lt (.wc 0) (g hS)).both (Study.lt b (g hE))) (h.rise (g hM) ((g hL).add b)) Makes.zero)
lemma toeplitzInv {H : ι → Line} (h : c.Lit H) (h0 : ∀ k, H k 0 ≠ 0) : c.Lit fun k j => Spectral.toeplitzInv (H k) j := by
  intro _ d f j hf hj
  have h := h.on hf
  let X : _ → ℕ → T (a sc) := fun k i => Tape.tab (i+1) (Spectral.toeplitzInv (H (f k)))
  have step : (d.climbs j (a sc) X).Makes (a sc) fun e => X e.i (e.j+1) := by
    have hi := stepi hj X
    refine tab (hi.add (.wc 2)) _ ?_
    have hx := slot (hi.add (.wc 2)); have hi := draw (Feeds.scan _ fun e => e.j + 2) hi
    have T := pull (Feeds.scan _ fun e => e.j + 2) (stepsum d j X)
    have hE := h.on ((Feeds.scan _ fun e => e.j + 2).next (Feeds.climbs d j X))
    have S := Makes.sum (F := fun g y => (X g.i.i g.i.j).look (g.i.j - y) sc.blank * H (f g.i.i) (y+1)) (hi.add (.wc 1))
      (((pull FS T).look ((draw FS hi).sub (slot (hi.add (.wc 1)))).1).mul ((hE.on FS).at_ ((slot (hi.add (.wc 1))).add (.wc 1))))
    refine (Makes.ite (Study.le hx hi) (T.look hx.1) (((hE.at_ (.wc 0)).inv fun _ => h0 _).mul S.neg)).congr fun e => ?_
    have := e.hj; dsimp only [X]; split_ifs with x
    · rw [Tape.look_tab, if_pos (by omega)]
    · rw [show e.j = e.i.j + 1 by omega, recoil_succ, div_eq_inv_mul]
      congr 2; exact sum_congr rfl fun y hy => by rw [Tape.look_tab, if_pos (by simp at hy; omega)]
  exact ((loop hj X (tab (.wc 1) _ (((h.on FS).at_ (.wc 0) |>.inv fun _ => h0 _).congr fun e => by
    rw [show e.j = 0 by have := e.hj; omega]; simp [Spectral.toeplitzInv, recoilTo])) step).look hj.1).congr fun k => by
    rw [Tape.look_tab, if_pos (Nat.lt_succ_self _)]
end Lit
abbrev Ii (c : Bench m ι) := c.Lit fun _ _ => I
def Glow (c : Bench m ι) (F : ι → Line) : Prop := c.Lit F ∧ c.Lit fun k i => starRingEnd ℂ (F k i)
namespace Glow
lemma congr (h : c.Glow F) (e : ∀ k i, F k i = G k i) : c.Glow G := ⟨h.1.congr e, h.2.congr fun _ _ => by rw [e]⟩
lemma on (h : c.Glow F) {f : ν → ι} (hf : d.Feeds c f) : d.Glow fun k => F (f k) := ⟨h.1.on hf, h.2.on hf⟩
lemma rat (z : ℚ) : c.Glow fun _ _ => (z : ℂ) := ⟨Lit.rat z, (Lit.rat z).congr fun _ _ => (map_ratCast _ _).symm⟩
lemma neg (h : c.Glow F) : c.Glow fun k i => -F k i := ⟨((Lit.rat 0).sub h.1).congr fun _ _ => by simp, ((Lit.rat 0).sub h.2).congr fun _ _ => by simp⟩
lemma freq {N : ι → ℕ} {z : ι → ℂ} (hN : c.Digit N) (hz : c.Makes sc z) (hz' : c.Makes sc fun k => starRingEnd ℂ (z k)) (h : c.Glow F) :
    c.Glow fun k i => freq (N k) (z k) (F k) i := ⟨Lit.freq hN hz h.1, (Lit.freq hN hz' h.2).congr fun _ _ => by simp [Spectral.freq, map_sum]⟩
lemma skirt {B E S L M : ι → ℕ} (hB : c.Digit B) (hE : c.Digit E) (hS : c.Digit S) (hL : c.Digit L) (hM : c.Digit M) (h : c.Glow F) :
    c.Glow fun k i => skirt (B k) (E k) (S k) (L k) (M k) (F k) i :=
  ⟨Lit.skirt hB hE hS hL hM h.1, (Lit.skirt hB hE hS hL hM h.2).congr fun _ _ => by simp only [ReelKit.skirt, Spectral.rise]; split_ifs <;> simp⟩
end Glow
def Zd (c : Bench m ι) (U : ι → Zone) : Prop := c.Digit (fun i => (U i).lo) ∧ c.Digit fun i => (U i).wide
lemma Zd.on {U : ι → Zone} (h : c.Zd U) {f : ν → ι} (hf : d.Feeds c f) : d.Zd fun k => U (f k) := ⟨draw hf h.1, draw hf h.2⟩
lemma Zd.has {U : ι → Zone} {j : ι → ℕ} (h : c.Zd U) (hj : c.Digit j) : c.Study fun k => (U k).has (j k) :=
  Study.both (Study.le h.1 hj) (Study.lt hj (h.1.add h.2))
def Rt (c : Bench m ι) (D : ι → ℕ) (z : ι → ℂ) : Prop :=
  c.Digit D ∧ c.Digit (fun i => 2^D i) ∧ c.Makes sc z ∧ c.Makes sc (fun i => starRingEnd ℂ (z i)) ∧ ∀ i, z i ≠ 0
lemma Rt.on {D : ι → ℕ} {z : ι → ℂ} (h : c.Rt D z) {f : ν → ι} (hf : d.Feeds c f) : d.Rt (fun k => D (f k)) fun k => z (f k) :=
  ⟨draw hf h.1, draw hf h.2.1, pull hf h.2.2.1, pull hf h.2.2.2.1, fun _ => h.2.2.2.2 _⟩
lemma harp_succ (h g r : Line) (k v : ℕ) : ReelKit.toeplitzReel h g r (k+1) v = hoop k v h g r (ReelKit.toeplitzReel h g r k (min (2^k) v)) (ReelKit.toeplitzReel h g r k (v - 2^k)) := rfl
def Ink (c : Bench m ι) (S : ι → Stroke) (j : ι → ℕ) : Prop :=
  c.Digit (fun k => (S k).ix (j k)) ∧ c.Makes sc (fun k => (S k).dye (j k)) ∧ c.Digit fun k => (S k).partner (j k)
def Play (c : Bench m ι) (R : ι → Reel) : Prop :=
  c.Digit (fun i => (R i).beats) ∧ ∀ (ν : Type U) (d : Bench m ν) (f : ν → ι) (t j : ν → ℕ), d.Feeds c f → d.Digit t → d.Digit j →
    (∀ k, t k < (R (f k)).beats) → d.Ink (fun k => (R (f k)).atBeat (t k)) j
abbrev tri (c : Bench m ι) (L : ι → ℕ) := ((c.scan L).scan fun e => L e.i).scan fun e => L e.i.i
lemma Ink.ite {P : ι → Prop} [DecidablePred P] {S S' : ι → Stroke} {j} (h : c.Study P)
    (a : (c.scrutin P).Ink (fun k => S k.1) (fun k => j k.1)) (b : (c.scrutin fun k => ¬P k).Ink (fun k => S' k.1) (fun k => j k.1)) :
    c.Ink (fun k => if P k then S k else S' k) j :=
  ⟨(branchN (x := fun k => (S k).ix (j k)) (y := fun k => (S' k).ix (j k)) h a.1 b.1).congr fun k => by by_cases p : P k <;> simp [p],
   (branchM (x := fun k => (S k).dye (j k)) (y := fun k => (S' k).dye (j k)) h a.2.1 b.2.1).congr fun k => by by_cases p : P k <;> simp [p],
   (branchN (x := fun k => (S k).partner (j k)) (y := fun k => (S' k).partner (j k)) h a.2.2 b.2.2).congr fun k => by by_cases p : P k <;> simp [p]⟩
lemma Ink.congr {S S' : ι → Stroke} {j} (h : c.Ink S j) (e : ∀ k, S k = S' k) : c.Ink S' j := funext e ▸ h
namespace Play
lemma congr (h : c.Play A) (e : ∀ i, A i = B i) : c.Play B := funext e ▸ h
lemma on (h : c.Play A) {f : ν → ι} (hf : d.Feeds c f) : d.Play fun k => A (f k) :=
  ⟨draw hf h.1, fun _ _ _ _ _ hg => h.2 _ _ _ _ _ (hg.next hf)⟩
lemma wait {D : ι → ℕ} (h : c.Digit D) : c.Play fun i => Reel.wait (D i) := ⟨h, fun _ _ _ _ _ _ _ hj _ => ⟨hj, Makes.one, hj⟩⟩
lemma stack (ha : c.Play A) (hb : c.Play B) : c.Play fun i => (A i).stack (B i) :=
  ⟨ha.1.add hb.1, fun _ _ f t _ hf ht hj hb' => Ink.ite (Study.lt ht (draw hf ha.1))
    (ha.2 _ _ _ _ _ hf.res (draw RS ht) (draw RS hj) fun k => k.2) (hb.2 _ _ _ (fun k => t k.1 - (A (f k.1)).beats) _
      hf.res (draw RS (ht.sub (draw hf ha.1))) (draw RS hj) fun k => by have := hb' k.1; have := k.2; simp only [Reel.stack] at *; omega)⟩
lemma par {p : ι → ℕ} (ha : c.Play A) (hb : c.Play B) (e : ∀ i, (A i).beats = (B i).beats) (hp : c.Digit p) :
    c.Play fun i => Reel.parallel (p i) (A i) (B i) :=
  ⟨ha.1, fun _ _ _ _ _ hf ht hj hb' => have hp := draw hf hp; have a := ha.2 _ _ _ _ _ hf ht hj hb'
    have b := hb.2 _ _ _ _ _ hf ht (hj.sub hp) fun k => e _ ▸ hb' k; have h := Study.lt hj hp
    ⟨iteN h a.1 (hp.add b.1), Makes.ite h a.2.1 b.2.1, iteN h a.2.2 (hp.add b.2.2)⟩⟩
lemma ite {P : ι → Prop} [DecidablePred P] (h : c.Study P) (ha : (c.scrutin P).Play fun k => A k.1)
    (hb : (c.scrutin fun k => ¬P k).Play fun k => B k.1) : c.Play fun i => if P i then A i else B i :=
  ⟨(branchN (x := fun i => (A i).beats) (y := fun i => (B i).beats) h ha.1 hb.1).congr fun k => by by_cases p : P k <;> simp [p],
   fun _ _ f t j hf ht hj hb' => (Ink.ite (S := fun k => (A (f k)).atBeat (t k)) (S' := fun k => (B (f k)).atBeat (t k)) (h.on hf)
      (ha.2 _ _ (fun k : {k // P (f k)} => ⟨f k.1, k.2⟩) _ _ (Feeds.into hf.res) (draw RS ht) (draw RS hj) fun k => by
        have := hb' k.1; simp only [k.2] at this; exact this)
      (hb.2 _ _ (fun k : {k // ¬P (f k)} => ⟨f k.1, k.2⟩) _ _ (Feeds.into hf.res) (draw RS ht) (draw RS hj) fun k => by
        have := hb' k.1; simp only [k.2] at this; exact this)).congr fun k => by by_cases p : P (f k) <;> simp [p]⟩
lemma sel {P : ι → Prop} [DecidablePred P] (h : c.Study P) (ha : c.Play A) (hb : c.Play B) : c.Play fun i => if P i then A i else B i :=
  ite h (ha.on RS) (hb.on RS)
lemma strand {A : ι → ℕ → Reel} {L B : ι → ℕ} (hL : c.Digit L) (hB : c.Digit B) (hb : ∀ i s, s < L i → (A i s).beats = B i)
    (h : (c.scan L).Play fun d => A d.i d.j) : c.Play fun i => ReelKit.strand (A i) (L i) :=
  have e := fun i => beat_strand (a := A i) _ _ fun s hs => hb i s hs
  ⟨(hL.mul hB).congr fun i => (e i).symm, fun _ d f t j hf ht hj hb' => have hB' := draw hf hB
    have q := fun k => show t k / B (f k) < L (f k) from Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm, ← e]; exact hb' k)
    (h.2 _ d (fun k => ⟨f k, _, q k⟩) (fun k => t k % B (f k)) j (hf.select (ht.div hB').1) (ht.mod hB') hj fun k => by
      rw [hb _ _ (q k)]; exact Nat.mod_lt _ (Nat.pos_of_ne_zero fun z => by have := e (f k) ▸ hb' k; simp [z] at this)).congr
      fun k => (strand_at _ _ _ _ (fun s hs => hb _ s hs) (e _ ▸ hb' k)).symm⟩
lemma riprap {A : ι → ℕ → ℕ → ℕ → Reel} {L B : ι → ℕ} (hL : c.Digit L) (hB : c.Digit B)
    (hb : ∀ i s c j, s < L i → c < L i → j < L i → (A i s c j).beats = B i)
    (h : (tri c L).Feeds c (fun e => e.i.i.i) → (tri c L).Digit (fun e => e.i.i.j) → (tri c L).Digit (fun e => e.i.j) →
      (tri c L).Digit During.j → (tri c L).Play fun e => A e.i.i.i e.i.i.j e.i.j e.j) :
    c.Play fun i => riprap (A i) (L i) :=
  have F := Feeds.scan c L; have L1 := draw F hL; have B1 := draw F hB; have G := Feeds.scan (c.scan L) fun e => L e.i
  have H := Feeds.scan ((c.scan L).scan fun e => L e.i) fun e => L e.i.i
  strand hL (hL.mul (hL.mul hB)) (fun i s hs => beat_strand _ _ fun c hc => beat_strand _ _ fun j hj => hb i s c j hs hc hj)
    (strand L1 (L1.mul B1) (fun (e : During L) c hc => beat_strand _ _ fun j hj => hb _ _ c j e.hj hc hj) (strand (draw G L1) (draw G B1)
      (fun (e : During fun e : During L => L e.i) j hj => hb _ _ _ j e.i.hj e.hj hj) (h (H.next (G.next F)) (draw (H.next G) (slot hL)) (draw H (slot L1)) (slot (draw G L1)))))
lemma plain {N : ι → ℕ} {L : ι → ℕ → ℕ} {D : ι → Line} (hN : c.Digit N)
    (hL : ∀ (ν : Type U) (d : Bench m ν) (f : ν → ι) (j : ν → ℕ), d.Feeds c f → d.Digit j → d.Digit fun k => L (f k) (j k))
    (hD : c.Lit D) : c.Play fun i => Reel.tick (Stroke.plain (N i) (L i) (D i)) :=
  ⟨.wc 1, fun _ _ _ _ _ hf _ hj _ => have h := Study.lt hj (draw hf hN); ⟨iteN h (hL _ _ _ _ hf hj) hj, Makes.ite h (hD _ _ _ _ hf hj) Makes.one, hj⟩⟩
lemma swatch {N : ι → ℕ} (hN : c.Digit N) (hD : c.Lit F) : c.Play fun i => Reel.swatch (N i) (F i) :=
  plain (L := fun _ => id) hN (fun _ _ _ _ _ hj => hj) hD
lemma shade {U V : ι → Zone} (hU : c.Zd U) (hV : c.Zd V) (hF : c.Lit F) (hG : c.Lit G) : c.Play fun i => shade (U i) (V i) (F i) (G i) :=
  ⟨.wc 1, fun _ _ _ _ _ hf _ hj _ => have hU := hU.on hf; have hV := hV.on hf
    ⟨hj, Makes.ite (hU.has hj) (hF _ _ _ _ hf (hj.sub hU.1)) (Makes.ite (hV.has hj) (hG _ _ _ _ hf (hj.sub hV.1)) Makes.one), hj⟩⟩
lemma snap {U V : ι → Zone} (hU : c.Zd U) (hV : c.Zd V) : c.Play fun i => snap (U i) (V i) :=
  ⟨.wc 1, fun _ _ _ _ _ hf _ hj _ => have hU := hU.on hf; have hV := hV.on hf
    ⟨hj, Makes.one, iteN (hU.has hj) (hV.1.add (hj.sub hU.1)) (iteN (hV.has hj) (hU.1.add (hj.sub hV.1)) hj)⟩⟩
lemma film {N : ι → ℕ} (h : c.Play A) (hN : c.Digit N) : c.Makes filmTy fun i => RAM.film (N i) (A i) :=
  tab h.1 _ (tab (draw FS hN) _ (
    let I := h.2 _ _ (fun e : During (fun d : During (fun i => (A i).beats) => N d.i) => e.i.i) (fun e => e.i.j) During.j
      (Feeds.next FS FS) (draw FS (slot h.1)) (slot (draw FS hN)) fun e => e.i.hj
    I.1.1.pair (I.2.1.pair I.2.2.1)))
lemma ofFilm {N : ι → ℕ} (hF : c.Makes filmTy fun i => RAM.film (N i) (A i)) (hb : c.Digit fun i => (A i).beats)
    (hN : c.Digit N) (hs : ∀ i, (A i).Sound (N i)) : c.Play A :=
  ⟨hb, fun _ d f t j hf ht hj hb' => have hN' := draw hf hN
    (Ink.ite (Study.lt hj hN') (have r := restricted d fun k => j k < N (f k)
      let E := ((pull (r.next hf) hF).pick _ (draw r ht).1 fun k => hb' k.1).pick _ (draw r hj).1 fun k => k.2
      ⟨⟨E.fst, (draw r hN').2.mono fun k => ((hs _ _ (hb' k.1)).bdix _ k.2).le⟩, E.snd.fst,
       ⟨E.snd.snd, (draw r hN').2.mono fun k => ((hs _ _ (hb' k.1)).bdp _ k.2).le⟩⟩)
      (have r := restricted d fun k => ¬ j k < N (f k); have s := fun k : {k // ¬ j k < N (f k)} => hs _ _ (hb' k.1)
       ⟨(draw r hj).congr fun k => ((s k).awayix _ (not_lt.1 k.2)).symm, Makes.one.congr fun k => ((s k).awayd _ (not_lt.1 k.2)).symm,
       (draw r hj).congr fun k => ((s k).awayp _ (not_lt.1 k.2)).symm⟩)).congr fun _ => ite_self _⟩
section
variable {U V : ι → Zone} (hU : c.Zd U) (hV : c.Zd V) (hI : c.Ii)
include hU hV hI
lemma butterflyReel : c.Play fun i => butterflyReel (U i) (V i) :=
  ((shade hU hV Lit.one hI).stack (snap hU hV)).stack (shade hU hV (Lit.one.sub hI) (Lit.one.add hI))
lemma brick : c.Play fun i => brick (U i) (V i) :=
  have q := fun (z : ℚ) (w : ℂ) (e : (z : ℂ) = w) => shade (G := fun _ _ => 1) hU hV ((Lit.rat z).congr fun _ _ => e) Lit.one
  (((((butterflyReel hU hV hI).stack (q (-3) (-3) (by norm_num))).stack (butterflyReel hU hV hI)).stack (q 2 2 (by norm_num))).stack (butterflyReel hU hV hI))
lemma spark (hF : c.Lit F) (nz : ∀ k i, F k i ≠ 0) : c.Play fun i => spark (U i) (V i) (F i) :=
  (((shade hU hV ((((Lit.rat (4/5)).mul hF).inv fun _ _ => mul_ne_zero (by norm_num) (nz _ _)).congr fun _ _ => by push_cast; ring_nf) Lit.one).stack
    (brick hU hV hI)).stack (shade hU hV (((Lit.rat (-1/10)).mul hF).congr fun _ _ => by push_cast; ring) ((Lit.rat (-1/6)).congr fun _ _ => by push_cast; ring)))
lemma addScaledReel (hF : c.Glow F) : c.Play fun i => addScaledReel (U i) (V i) (F i) :=
  have B : c.Lit fun k i => blaze (F k) i := Lit.one.add (hF.1.mul hF.2)
  (spark hU hV hI B fun _ _ => blaze_ne _).stack (spark hU hV hI (hF.1.sub B) fun _ _ => blaze_sub_ne _)
lemma flash1 (t : ℚ) (x : ℂ) (e : (t : ℂ) = x) : c.Play fun i => ReelKit.addScaledReel (U i) (V i) fun _ => x := addScaledReel hU hV hI ((Glow.rat t).congr fun _ _ => e)
end
lemma fftReel {D : ι → ℕ} {z : ι → ℂ} (hD : c.Digit D) (h2 : Small c.size fun i => 2^D i) (hz : c.Makes sc z)
    (hI : c.Ii) : c.Play fun i => fftReel (D i) (z i) := by
  let X : ι → ℕ → T filmTy := fun i k => RAM.film (2^k) (ReelKit.fftReel k (z i ^ 2^(D i - k)))
  have step : (c.climbs D filmTy X).Makes filmTy fun e => X e.i (e.j+1) := by
    have F := Feeds.climbs c D X; have hk := stepi hD X
    have sm : ∀ {x : During D → ℕ}, (∀ e, x e ≤ D e.i) → Small (c.climbs D filmTy X).size fun e => 2^x e :=
      fun h => (h2.reindex During.i).mono fun e => Nat.pow_le_pow_right two_pos (h e)
    have hp := hk.pow2 (sm fun e => e.hj.le)
    have P : (c.climbs D filmTy X).Play fun e => ReelKit.fftReel e.j ((z e.i ^ 2^(D e.i - (e.j+1)))^2) :=
      (ofFilm (stepsum ..) (((Digit.wc 5).mul hk).congr fun _ => (beats_pulse _ _).symm) hp fun _ => sound_pulse _ _).congr fun e => by
        rw [← pow_mul, ← pow_succ, show D e.i - (e.j+1) + 1 = D e.i - e.j by have := e.hj; omega]
    have w := (Lit.pow (pull F hz)).at_ (((draw F hD).sub (hk.add (.wc 1))).pow2 (sm fun e => by omega))
    have hI := hI.on F
    have Zi : Zd _ fun e : During D => initial (2^e.j) := ⟨.wc 0, hp⟩
    have Ze : Zd _ fun e : During D => ending (2^e.j) := ⟨hp, hp⟩
    refine film ((((plain (hp.add hp) (fun _ _ _ _ _ hj => iteN (Study.lt hj (draw ‹_› hp)) ((Digit.wc 2).mul hj)
      (((Digit.wc 2).mul (hj.sub (draw ‹_› hp))).add (.wc 1))) Lit.one).stack (P.par P (fun _ => rfl) hp)).stack
      ((shade Zi Ze Lit.one (Lit.pow w)).stack (butterflyReel Zi Ze hI))) : Play _ fun e => _)
      ((hp.add hp).congr fun _ => (two_mul _).symm.trans (pow_succ' _ _).symm)
  exact ofFilm ((loop hD X (film (wait (D := fun _ => 0) (.wc 0)) (.wc 1)) step).congr fun i => by simp [X])
    (((Digit.wc 5).mul hD).congr fun _ => (beats_pulse _ _).symm) (hD.pow2 h2) fun _ => sound_pulse _ _
section
variable {D : ι → ℕ} {z : ι → ℂ} (hR : c.Rt D z) (hI : c.Ii) {U V A B : ι → Zone}
  (hU : c.Zd U) (hV : c.Zd V) (hA : c.Zd A) (hB : c.Zd B)
include hR hI
include hU hV in
lemma cyclicConvReel (hH : c.Glow F) : c.Play fun i => cyclicConvReel (D i) (z i) (U i) (V i) (F i) :=
  have p := fftReel hR.1 hR.2.1.2 hR.2.2.1 hI
  have b : Play _ fun i => backPulse (D i) (z i) := (fftReel hR.1 hR.2.1.2 (hR.2.2.1.inv hR.2.2.2.2) hI).stack
    (swatch hR.2.1 (Lit.const ((Makes.cast hR.2.1).inv fun _ => Nat.cast_ne_zero.2 (by positivity))))
  (((((wait p.1).par p (fun _ => rfl) hU.1).stack ((wait p.1).par p (fun _ => rfl) hV.1)).stack (addScaledReel hV hU hI (Glow.freq hR.2.1 hR.2.2.1 hR.2.2.2.1 hH))).stack
    ((wait b.1).par b (fun _ => rfl) hU.1)).stack ((wait b.1).par b (fun _ => rfl) hV.1)
include hU hA hB in
lemma duct (hH : c.Glow F) : c.Play fun i => duct (D i) (z i) (U i) (A i) (B i) (F i) :=
  have S : c.Zd fun i => (A i).slim (U i).wide := ⟨hA.1, hU.2⟩
  (((flash1 S hU hI 1 1 Rat.cast_one).stack (cyclicConvReel hR hI hA hB hH)).stack (flash1 S hU hI (-1) (-1) (by push_cast; rfl))).stack (cyclicConvReel hR hI hA hB hH.neg)
include hU hV hA hB in
lemma well (hH : c.Glow F) : c.Play fun i => well (D i) (z i) (U i) (V i) (A i) (B i) (F i) :=
  have S : c.Zd fun i => (B i).slim (V i).wide := ⟨hB.1, hV.2⟩
  (((duct hR hI hU hA hB hH).stack (flash1 hV S hI 1 1 Rat.cast_one)).stack (duct hR hI hU hA hB hH.neg)).stack (flash1 hV S hI (-1) (-1) (by push_cast; rfl))
end
lemma toeplitzGridCell {K Wd S C J : ι → ℕ} {z : ι → ℂ} (hR : c.Rt (fun i => K i + 1) z) (hI : c.Ii)
    (hW : c.Digit Wd) (hS : c.Digit S) (hC : c.Digit C) (hJ : c.Digit J) (hH : c.Glow F) (hG : c.Glow G) :
    c.Play fun i => toeplitzGridCell (K i) (z i) (Wd i) (F i) (G i) (S i) (C i) (J i) := by
  have b : c.Digit fun i => 2^K i := (hR.2.1.div (.wc 2)).congr fun _ => by rw [pow_succ, Nat.mul_div_cancel _ two_pos]
  have p := ((Digit.wc 16).mul b).add (hS.mul b)
  have fr : c.Digit fun i => far (2^K i) (J i) := iteN (Study.lt hJ (.wc 8)) ((Digit.wc 8).mul b) (.wc 0)
  have b2 := (Digit.wc 2).mul b
  have Q : c.Zd fun i => quay (2^K i) (J i) := ⟨hJ.mul b, b⟩
  have Je : c.Zd fun i => jetty (16*2^K i) (Wd i) (2^K i) (S i) := ⟨p, b.minimum (hW.sub (hS.mul b))⟩
  have Tr : c.Zd fun i => trestle (2^K i) (J i) := ⟨fr, b⟩
  have Ba : c.Zd fun i => barrier (2^K i) (J i) := ⟨fr.add b, b2⟩
  have Lo : c.Zd fun i => lockBay (2^K i) (J i) := ⟨fr.add ((Digit.wc 3).mul b), b2⟩
  have bo := fun {U V : ι → Zone} {L M : ι → ℕ} {H : ι → Line} (hU : c.Zd U) (hV : c.Zd V) (hL : c.Digit L) (hM : c.Digit M)
    (hH : c.Glow H) => well hR hI hU hV Ba Lo (hH.skirt b hU.2 hV.2 hL hM)
  exact (((bo Q Tr (hJ.mul b) (hC.mul b) hG).stack (bo Tr Je (hC.mul b) p hH)).stack (bo Q Tr (hJ.mul b) (hC.mul b) hG.neg)).stack
    (bo Tr Je (hC.mul b) p hH.neg)
lemma naiveToeplitzCell {P Wd S C J : ι → ℕ} (hP : c.Digit P) (hW : c.Digit Wd) (hS : c.Digit S) (hC : c.Digit C)
    (hJ : c.Digit J) (hH : c.Glow F) (hG : c.Glow G) (hI : c.Ii) :
    c.Play fun i => naiveToeplitzCell (P i) (Wd i) (F i) (G i) (S i) (C i) (J i) :=
  sel (Study.lt hS hW) (addScaledReel (U := fun i => jetty (P i) (Wd i) 1 (S i)) (V := fun i => quay 1 (J i))
    ⟨hP.add (hS.mul (.wc 1)), (Digit.wc 1).minimum (hW.sub (hS.mul (.wc 1)))⟩ ⟨hJ.mul (.wc 1), .wc 1⟩ hI
    ⟨Lit.const ((hH.1.rise (hP.add hS) hC).mul (hG.1.rise hC hJ)), Lit.const (((hH.2.rise (hP.add hS) hC).mul (hG.2.rise hC hJ)).congr
      fun _ => by simp only [Spectral.rise]; split_ifs <;> simp)⟩) (wait (.wc 26))
lemma toeplitzGridReel {K Wd : ι → ℕ} {z : ι → ℂ} (hR : c.Rt (fun i => K i + 1) z) (hW : c.Digit Wd) (hH : c.Glow F)
    (hG : c.Glow G) (hI : c.Ii) : c.Play fun i => toeplitzGridReel (K i) (z i) (Wd i) (F i) (G i) :=
  riprap (.wc 16) ((Digit.wc 4).mul (((Digit.wc 80).mul (hR.1.sub (.wc 1))).add (.wc 348)) |>.congr fun _ => by simp)
    (fun _ _ _ _ _ _ _ => beats_gravel ..) fun T hs hc hj => toeplitzGridCell (hR.on T) (hI.on T) (draw T hW) hs hc hj (hH.on T) (hG.on T)
lemma bridge {E Wd : ι → ℕ} {R : ι → Line} (hE : c.Digit E) (h2 : c.Digit fun i => 2^E i) (hW : c.Digit Wd)
    (hH : c.Glow F) (hG : c.Glow G) (hR : (c.scrutin fun i => ¬ E i < 4).Rt (fun k => E k.1 - 4 + 1) (fun k => R k.1 (E k.1 - 4 + 1)))
    (hI : c.Ii) : c.Play fun i => toeplitzBridge (E i) (Wd i) (F i) (G i) (R i) :=
  ite (Study.lt hE (.wc 4)) ((riprap (A := fun i => ReelKit.naiveToeplitzCell (2^E i) (Wd i) (F i) (G i)) h2 (.wc 26)
    (fun _ _ _ _ _ _ _ => beats_speck ..) fun T hs hc hj => naiveToeplitzCell (draw T h2) (draw T hW) hs hc hj (hH.on T) (hG.on T) (hI.on T)).on
      (restricted c _)) (toeplitzGridReel hR (draw (restricted c _) hW) (hH.on (restricted c _)) (hG.on (restricted c _)) (hI.on (restricted c _)))
lemma hoop {K Wd : ι → ℕ} {R : ι → Line} (ha : c.Play A) (hb : c.Play B) (e : ∀ i, (A i).beats = (B i).beats)
    (hK : c.Digit K) (h2 : c.Digit fun i => 2^K i) (hW : c.Digit Wd)
    (hBr : (c.scrutin fun i => 2^K i < Wd i).Play fun k => toeplitzBridge (K k.1) (Wd k.1 - 2^K k.1) (F k.1) (G k.1) (R k.1)) :
    c.Play fun i => hoop (K i) (Wd i) (F i) (G i) (R i) (A i) (B i) :=
  (ha.par hb e (h2.minimum hW)).stack (ite (Study.lt h2 hW) hBr ((wait (reachD hK)).on (restricted c _)))
lemma toeplitzReel {E N : ι → ℕ} {R : ι → Line} (hE : c.Digit E) (h2 : c.Digit fun i => 2^E i) (hN : c.Digit N)
    (hNE : ∀ i, N i ≤ 2^E i) (hH : c.Glow F) (hG : c.Glow G)
    (hR : (c.scan E).Rt (fun e => e.j - 4 + 1) (fun e => R e.i (e.j - 4 + 1))) (hI : c.Ii) :
    c.Play fun i => ReelKit.toeplitzReel (F i) (G i) (R i) (E i) (N i) := by
  let Y : ι → ℕ → ℕ → T filmTy := fun i k w => RAM.film w (ReelKit.toeplitzReel (F i) (G i) (R i) k w)
  let X : ι → ℕ → T (p filmTy (p filmTy filmTy)) := fun i k => (Y i k (2^k), Y i k (N i % 2^k), Y i k 0)
  have sw := fun {W : ι → ℕ} (hW : c.Digit W) => film (swatch (F := fun i _ => F i 0) hW (Lit.const (hH.1.at_ (.wc 0)))) hW
  have step : (c.climbs E _ X).Makes _ fun e => X e.i (e.j+1) := by
    have Fc := Feeds.climbs c E X; have hk := stepi hE X; have hN := draw Fc hN; have St := stepsum c E X
    have hp := hk.pow2 ((h2.2.reindex During.i).mono fun e => Nat.pow_le_pow_right two_pos e.hj.le)
    have hp2 : Digit _ fun e : During E => 2^(e.j+1) := (hp.add hp).congr fun _ => by rw [pow_succ]; ring
    have O := fun {w : During E → ℕ} (h : Makes _ _ fun e => RAM.film (w e) (ReelKit.toeplitzReel (F e.i) (G e.i) (R e.i) e.j (w e)))
      (hw : Digit _ w) (b : ∀ e, w e ≤ 2^e.j) => ofFilm h ((chorusDigit hk).congr fun e => (beats_harp ..).symm) hw fun e => sound_harp _ _ _ _ _ (b e)
    have Pf := O St.fst hp fun _ => le_rfl
    have Pm := O St.snd.fst (hN.mod hp) fun _ => (Nat.mod_lt _ (by positivity)).le
    have Pz := O St.snd.snd (.wc 0) fun _ => Nat.zero_le _
    have hR := hR.on ((Feeds.climbs c E X).select hk.1 : Feeds _ (c.scan E) id)
    have Hp := fun {W : During E → ℕ} {A B : During E → Reel} (ha : Play _ A) (hb : Play _ B) (e : ∀ i, (A i).beats = (B i).beats)
      (hW : Digit _ W) => hoop (F := fun e : During E => F e.i) (G := fun e => G e.i) (R := fun e => R e.i) (K := During.j) ha hb e hk hp hW
        (have r := restricted (c.climbs E _ X) fun e => 2^e.j < W e
        bridge (R := fun e : {e : During E // 2^e.j < W e} => R e.1.i) (draw r hk) (draw r hp) ((draw r hW).sub (draw r hp))
          (hH.on (r.next Fc)) (hG.on (r.next Fc)) (hR.on ((restricted _ _).next r)) (hI.on (r.next Fc)))
    have be := fun (e : During E) (a b : ℕ) => (beats_harp (F e.i) (G e.i) (R e.i) e.j a).trans (beats_harp (F e.i) (G e.i) (R e.i) e.j b).symm
    have ht := Study.lt (hN.mod hp2) hp
    exact (film ((Hp Pf Pf (fun e => be e _ _) hp2).congr fun e => by
      rw [harp_succ, min_eq_left (Nat.pow_le_pow_right two_pos (Nat.le_succ _)), pow_succ, mul_two, Nat.add_sub_cancel]) hp2).pair
      ((film ((Hp (sel ht Pm Pf) (sel ht Pz Pm) (fun e => by split_ifs <;> simp only [beats_harp]) (hN.mod hp2)).congr fun e => by
      rw [harp_succ]; have := mod_two (N e.i) e.j; congr 1 <;> split_ifs at this ⊢ <;> congr 1 <;> omega) (hN.mod hp2)).pair
      (film ((Hp Pz Pz (fun e => be e _ _) (.wc 0)).congr fun e => by rw [harp_succ, Nat.min_zero, Nat.zero_sub]) (.wc 0)))
  have L := loop hE X ((sw (.wc 1)).pair ((sw (hN.mod (.wc 1))).pair (sw (.wc 0)))) step
  exact ofFilm ((Makes.ite (Study.eq hN h2) L.fst L.snd.fst).congr fun i => by
      dsimp only [X, Y]; split_ifs with x; rw [x]; rw [Nat.mod_eq_of_lt (lt_of_le_of_ne (hNE i) x)])
    ((chorusDigit hE).congr fun i => (beats_harp ..).symm) hN fun i => sound_harp _ _ _ _ _ (hNE i)
lemma vandermondeReel {N E : ι → ℕ} {u : ι → ℂ} {R : ι → Line} (hN : c.Digit N) (hE : c.Digit E) (h2 : c.Digit fun i => 2^E i)
    (hNE : ∀ i, N i ≤ 2^E i) (hn : ∀ i, 0 < N i) (hu : ∀ i, Spectral.PrimRoot (u i) (N i)) (hU : c.Hue u)
    (hR : (c.scan E).Rt (fun e => e.j - 4 + 1) (fun e => R e.i (e.j - 4 + 1))) (hI : c.Ii) :
    c.Play fun i => vandermondeReel (N i) (E i) (u i) (R i) := by
  have z : ∀ {v : ι → ℂ}, (∀ i, Spectral.PrimRoot (v i) (N i)) → ∀ k i, gap (v k) i = 0 ↔ N k ≤ i :=
    fun hv k i => ⟨fun h => not_lt.1 fun l => gap_ne_zero _ (hv k) _ l h, gap_zero (hv k) (hn k)⟩
  have hF : c.Glow fun i => floorH (u i) := ⟨(Lit.gap hU.1).invZ hN (z hu), ((Lit.gap hU.2).invZ hN (z fun i => by
    rw [Spectral.conj_of_root (hn i) (hu i).pow_eq_one]; exact (hu i).inv)).congr fun _ _ => by simp [floorH, Spectral.gap, map_prod]⟩
  have P := toeplitzReel hE h2 hN hNE hF ⟨hF.1.toeplitzInv fun _ => by simp [floorH, Spectral.gap], (hF.2.toeplitzInv fun _ => by
    simp [floorH, Spectral.gap]).congr fun _ _ => (conj_recoil _ _).symm⟩ hR hI
  have Ec : c.Play fun i => echo (N i) := plain hN (fun _ _ _ _ hf hj => ((draw hf hN).sub (.wc 1)).sub hj) Lit.one
  exact ((((swatch hN (Lit.gap hU.1)).stack ((Ec.stack P).stack Ec)).stack (swatch hN (Lit.roof hU.1))).stack
    (swatch hN (((Lit.gap hU.1).mul (Lit.roof hU.1)).invZ hN fun k i => by
      rw [mul_eq_zero, z hu, or_iff_left (by unfold Spectral.roof; exact prod_ne_zero_iff.2 fun j _ => neg_ne_zero.2 (pow_ne_zero _ ((hu k).ne_zero (hn k).ne')))]))).stack
    (((swatch hN (Lit.roof hU.1)).stack P).stack (swatch hN (Lit.gap hU.1)))
end Play
end
lemma Engrave.tree {u : ι → Reel} (h : b.Engrave n u) :
    b.Makes treeTy fun i => treeT (n i) (u i) :=
  have R := fun {ν : Type U} (d : Bench m ν) (f : ν → ι) (t j : ν → ℕ) (hf : d.Feeds b f) (ht : d.Digit t) (hj : d.Digit j)
    (htb : ∀ k, t k < (u (f k)).beats) (hjb : ∀ k, j k < n (f k)) => ((pull hf h.4).pick _ ht.1 htb).pick _ hj.1 hjb
  have F1 := (Feeds.scan (b.scan fun i => (u i).beats) fun e => n e.i).next (Feeds.scan b _)
  have T1 := draw (Feeds.scan _ fun e : During (fun i => (u i).beats) => n e.i) (slot h.2)
  have J1 := slot (draw (Feeds.scan b fun i => (u i).beats) h.3)
  have E := R _ _ _ _ F1 T1 J1 (fun e => e.i.hj) fun e => e.hj
  tab h.2 _ (tab (draw (Feeds.scan b _) h.3) _ ((E.fst.pair E.snd.fst).pair (hemChip (S := fun e : During fun e : During (fun i => (u i).beats) => n e.i => (u e.i.i).atBeat e.i.j)
    (fun _ d f j hf hj hjb => ⟨(R d _ _ j (hf.next F1) (draw hf T1) hj (fun k => (f k).i.hj) hjb).snd.snd,
      (draw (hf.next F1) h.3).2.mono fun k => ((h.1 _ _ (f k).i.hj).bdp _ (hjb k)).le⟩) (draw F1 h.3).2 J1 fun e => e.hj)))
open Complex Finset Spectral in
theorem publish {n d : ι→ℕ} {u : ι→ℂ} {r : ι→Line}
    (hd : b.Arch d) (hh : b.Digit n) (hn : ∀ i,0<n i) (hv : ∀ i,n i ≤ 2^d i)
    (hr : b.Fabric (fun i => d i+1) r) (hy : ∀ i, Springs (d i) (r i))
    (h : b.Hue u) (hu : ∀ i, Spectral.PrimRoot (u i) (n i))
    (hI : b.Hue fun _ => I) :
    b.Engrave n (fun i => vandermondeReel (n i) (d i) (u i) (r i)) :=
  have J : (b.scan d).Digit fun e => e.j - 4 + 1 := ((slot hd.1).sub (.wc 4)).add (.wc 1)
  have F := (Feeds.scan b d).select (n := fun i => d i + 1) (f := fun e : During d => ⟨e.i, e.j - 4 + 1, by have := e.hj; omega⟩) J.1
  have H := Hue.transfer (f := fun g : During fun i => d i + 1 => r g.i g.j) hr F
  have P := Play.vandermondeReel hh hd.1 hd.2 hv hn hu h ⟨J, J.pow2 ((hd.2.2.reindex During.i).mono fun e => Nat.pow_le_pow_right two_pos
      (by have := e.hj; omega)), H.1, H.2, fun e => ((hy _ _ (by have := e.hj; omega)).ne_zero (by positivity))⟩
    (Lit.const hI.1)
  ⟨fun i => sound_ballad _ _ _ _ (hv i), P.1, hh, P.film hh⟩
end Bench
end
end PowerSaving.RAM
namespace PowerSaving.AxisTensor
open ReelKit PowBlock PairBlocks Binary Finset Matrix
noncomputable section
def fleck (i j : ℕ) : ℂ := if i=j then ca else cb
def blockRippleMat : ℕ → Wood
  | 0 => fun _ _ => 1
  | k+1 => fun i j => blockRippleMat k (i/2) (j/2) * fleck (i%2) (j%2)
def blockRipple (k : ℕ) (x : Line) : Line := graft (2^k) (blockRippleMat k) x
lemma prism_prod (k a b : ℕ) :
    blockRippleMat k a b = ∏ t ∈ range k, fleck (a / 2^t % 2) (b / 2^t % 2) := by
  induction k generalizing a b with
  | zero => rfl
  | succ k ih => simp [blockRippleMat, ih, prod_range_succ', Nat.div_div_eq_div_mul, pow_succ', mul_comm]
lemma prism_mul (a b x x' y y' : ℕ) (hy : y < 2^b) (hy' : y' < 2^b) :
    blockRippleMat (a+b) (x*2^b+y) (x'*2^b+y') = blockRippleMat a x x' * blockRippleMat b y y' := by
  induction b generalizing y y' with
  | zero => simp_all [blockRippleMat]
  | succ b ih =>
    have p : 2^(b+1) = 2^b*2 := pow_succ ..
    have e : ∀ z w, (z*2^(b+1)+w)/2 = z*2^b+w/2 ∧ (z*2^(b+1)+w)%2 = w%2 := fun z w => by
      rw [p, ← mul_assoc]; omega
    show blockRippleMat (a+b) _ _ * _ = _
    rw [(e _ _).1, (e _ _).1, (e _ _).2, (e _ _).2, ih _ _ (by omega) (by omega), mul_assoc]; rfl
lemma gleam_loc (k : ℕ) (v : Line) (x : Bits k) :
    blockRipple k v ((bits k).loc x) = ripple k (fun j => v ((bits k).loc j)) x := by
  have e : ∀ g : ℕ → ℂ, ∑ m ∈ range (2^k), g m = ∑ y, g ((bits k).loc y) := fun g => by
    rw [← Fin.sum_univ_eq_sum_range, ← (bits k).index.symm.sum_comp]
    exact sum_congr rfl fun i _ => congrArg g (Layout.loc_atFin (bits k) i).symm
  simp only [blockRipple, graft, ripple, mulVec, dotProduct, kernel, e, digitProd_apply, prism_prod]
  refine sum_congr rfl fun y _ => congrArg (· * _) ?_
  rw [← Fin.prod_univ_eq_prod_range]
  refine prod_congr rfl fun t _ => ?_
  simp only [bits_div k _ t, littleC, fleck, (ZMod.val_injective 2).eq_iff]
def gleans (f g : PowBlock) : ℂ := if f.start=g.start then blockRippleMat f.height f.seat g.seat else 0
def stow (n : ℕ) (f : ℕ → PowBlock) (x : Line) : Line := fun j => x (seek n (fun i => (f i).addr) j)
def slit (n : ℕ) (f : ℕ → PowBlock) (x : Line) (s : ℕ) : Line := fun j => stow n f x (s+j)
def patchRipple (n : ℕ) (f : ℕ → PowBlock) (x : Line) (j : ℕ) : Line :=
  blockRipple (patch n f j).height (slit n f x j)
lemma leafC_hem {n : ℕ} {u : Stroke} (h : u.Sound n) {a k : ℕ} (ha : a<n) (hk : k<n) :
    leafC u a k = gleans (block u a) (block u k) := by
  have q : ∀ i, tier u i < 2 := fun i => by unfold tier; split_ifs <;> omega
  have p1 : ∀ s s', s < 2 → s' < 2 → blockRippleMat 1 s s' = if s = s' then ca else cb := fun s s' hs hs' => by
    simp [blockRippleMat, fleck, Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hs']
  unfold gleans
  by_cases g : crown u a = crown u k
  · rw [if_pos (by simp only [block, g] : _ = _)]
    simp only [block, up, leafC, white]
    obtain e|e := crown_class h g <;> subst e
    · by_cases e : u.partner k = k <;> simp [e, eq_comm (a := k), p1 _ _ (q _) (q _)]; rfl
    · have := h.pair a; by_cases e : u.partner a = a
      · simp [e]; rfl
      · simp [e, eq_comm (a := a), p1 _ _ (q _) (q _)]; exact fun x => (tier_partner_ne h e x.symm).elim
  · rw [if_neg fun e => g (class_of_start h ha hk e)]
    have : k ≠ a ∧ k ≠ u.partner a := ⟨fun e => g (e ▸ rfl), fun e => g (e ▸ crown_partner h).symm⟩
    simp [leafC, white, this]
lemma gleans_fringe {R n i j : ℕ} {s s' t t' : PowBlock} (ha : s.Mark n i) (ha' : s'.Mark n i)
    (hs : s.fits s') (hg : t.Mark R j) (hg' : t'.Mark R j) (ht : t.fits t') :
    gleans (fringe R s t) (fringe R s' t') = gleans s s' * gleans t t' := by
  have sm : ∀ {a b : PowBlock}, a.fits b → 0 < a.width → 0 < b.width → a.start = b.start → a.same b :=
    fun f p q e => by rcases f with f|f|f; exact f; all_goals (unfold tip at f; omega)
  have p := Nat.mul_pos ha.positive hg.positive; have p' := Nat.mul_pos ha'.positive hg'.positive
  unfold gleans
  by_cases H : (fringe R s t).start = (fringe R s' t').start
  · obtain ⟨⟨a1, -, a3⟩, ⟨b1, b2, b3⟩⟩ := fr_unique R j hg hg' ha ha' hs ht
      (by unfold tip; simp only [fringe] at *; omega) (by unfold tip; simp only [fringe] at *; omega)
    rw [if_pos H, if_pos a1, if_pos b1]; simp only [fringe]
    rw [← b2, hg.size, prism_mul _ _ _ _ _ _ (hg.size ▸ hg.place) (b3 ▸ hg'.size ▸ hg'.place)]
  · rw [if_neg H]; split_ifs with a b <;> simp
    refine (H ?_).elim; exact (by simp only [fringe]; rw [a, b, (sm hs ha.positive ha'.positive a).2.1])
lemma canopyC (r : Axes) (u : ℕ → Stroke) (l : ℕ) (h : Splits r l) (g : ∀ i<l, (u i).Sound (r i))
    (i : ℕ) (hi : i<extent r l) (k : ℕ) (hk : k<extent r l) :
    axisKron r (fun t => leafC (u t)) l i k = gleans (strokeBlocks r u l i) (strokeBlocks r u l k) := by
  induction l generalizing i k with
  | zero => simp [axisKron, strokeBlocks, gleans]; rfl
  | succ l ih =>
    have c := h.cut l.le_succ; have g' := fun i (hi : i < l) => g i (by omega)
    have Q := mosaic_quilt r l u c g'; have W := quilt (g l l.lt_succ_self)
    have := h.div_lt hi; have := h.div_lt hk; have := h.mod_lt i; have := h.mod_lt k
    show axisKron r _ l (i / r l) (k / r l) * leafC (u l) (i % r l) (k % r l) = gleans (fringe _ _ _) (fringe _ _ _)
    rw [ih c g' _ ‹_› _ ‹_›, leafC_hem (g l l.lt_succ_self) ‹_› ‹_›,
      gleans_fringe (Q.mark _ ‹_›) (Q.mark _ ‹_›) (Q.seam _ ‹_› _ ‹_›) (W.mark _ ‹_›) (W.mark _ ‹_›) (W.seam _ ‹_› _ ‹_›)]
lemma mix_eq_patchRipple (r : Axes) (l : ℕ) (u : ℕ→Stroke)
    (h : Splits r l) (g : ∀ i<l, (u i).Sound (r i)) (x : Line)
    (i : ℕ) (hi : i<extent r l) :
    let f := strokeBlocks r u l
    graft (extent r l) (axisKron r (fun i => leafC (u i)) l) x i =
      patchRipple (extent r l) f x (f i).start (f i).seat := by
  intro f
  have Q : PowBlockCover _ l f := mosaic_quilt r l u h g
  have M := Q.mark i hi; have P := M.positive
  set N := extent r l; set S := (f i).start
  have A := Q.patch_align hi le_rfl (show S < (f i).tip by unfold tip; omega)
  have e1 : ∀ k ∈ range N, axisKron r (fun i => leafC (u i)) l i k * x k =
      (fun a => gleans (f i) (patch N f a) * x (seek N (fun i => (f i).addr) a)) (f k).addr := fun k hk => by
    simp only [patch, Q.reloc.seeks_at (mem_range.1 hk), canopyC r u l h g i hi k (mem_range.1 hk)]; rfl
  have e2 : ∀ a ∈ range N, a ∉ Ico S (S+(f i).width) → gleans (f i) (patch N f a) * x (seek N (fun i => (f i).addr) a) = 0 :=
    fun a ha hn => by
    have := Q.patch_addr (mem_range.1 ha); have := (Q.patch_mark (mem_range.1 ha)).place
    rw [gleans, if_neg, zero_mul]; intro e
    have := Q.matches_of_eq hi (Q.reloc.seeks (mem_range.1 ha)).1 e
    simp only [mem_Ico, same, patch, addr] at *; omega
  simp only [graft, patchRipple, blockRipple, slit, stow]
  rw [sum_congr rfl e1, Q.reloc.sum (fun a => gleans (f i) (patch N f a) * x (seek N (fun i => (f i).addr) a)), ← sum_subset (fun a ha => mem_range.2 (by
    have := M.endsBy; unfold tip at this; simp at ha; omega)) e2, sum_Ico_eq_sum_range, Nat.add_sub_cancel_left,
    A.1.2.2, M.size]
  refine sum_congr rfl fun m hm => ?_
  have B := Q.patch_align hi (Nat.le_add_right S m) (by unfold tip; simp at hm; rw [M.size]; omega)
  rw [gleans, if_pos B.1.1.symm, B.2, Nat.add_sub_cancel_left]
def seatfare (n : ℕ) (f : ℕ→PowBlock) (j : ℕ) :=
  if (patch n f j).seat=0 then (patch n f j).width else 0
lemma seatfare_sum (n l : ℕ) (f : ℕ → PowBlock) (h : PowBlockCover n l f) :
    ∑ j ∈ range n, seatfare n f j = n := by
  have st : ∀ a < n, (patch n f a).start < n ∧ (patch n f (patch n f a).start).seat = 0 := fun a ha => by
    have M := h.patch_mark ha; have := M.positive; have := M.endsBy; unfold tip at this
    have A := h.patch_align (h.reloc.seeks ha).1 le_rfl (show (patch n f a).start < (patch n f a).tip by unfold tip; omega)
    exact ⟨by omega, A.2.trans (Nat.sub_self _)⟩
  conv_rhs => rw [← card_range n, card_eq_sum_card_fiberwise (f := fun a => (patch n f a).start) (t := range n)
    fun a ha => mem_range.2 (st a (mem_range.1 ha)).1]
  refine sum_congr rfl fun j hj => ?_
  rw [mem_range] at hj
  have M := h.patch_mark hj; have := h.patch_addr hj; have := M.place; have := M.endsBy; unfold tip addr at *
  unfold seatfare; split_ifs with e
  · rw [show (patch n f j).width = (Ico j (j + (patch n f j).width)).card by simp]; congr 1; ext a
    simp only [mem_filter, mem_range, mem_Ico]; constructor
    · rintro ⟨h1, h2⟩
      have B := h.patch_align (h.reloc.seeks hj).1 (j := a) (by change (patch n f j).start ≤ a; omega)
        (by change a < (patch n f j).start + (patch n f j).width; omega)
      change (patch n f a).same (patch n f j) ∧ _ at B; unfold same at B; omega
    · rintro ⟨ha, e'⟩
      have B := h.matches_of_eq (h.reloc.seeks hj).1 (h.reloc.seeks ha).1 (by change (patch n f j).start = (patch n f a).start; omega)
      change (patch n f j).same (patch n f a) at B; unfold same at B
      have := h.patch_addr ha; have := (h.patch_mark ha).place; unfold addr at *; omega
  · symm; rw [card_eq_zero, filter_eq_empty_iff]; intro a ha e'
    exact e (e' ▸ (st a (mem_range.1 ha)).2)
end
end PowerSaving.AxisTensor
namespace PowerSaving.RAM.Bench
open Ty AxisTensor PowBlock ReelKit PairBlocks
universe U V
variable {m : Bool} {ι : Type U} {κ : Type V} {b : Bench m ι} {q : Bench m κ}
  {l : ι→ℕ} {r : ι→Axes} {u : ι→ℕ→Stroke} {n : ι→ℕ} {Y : ι→PowBlock}
structure Spring (b : Bench m ι) (n : ι→ℕ) (s : ι→Stroke) : Prop where
  good : ∀ i, (s i).Sound (n i)
  tree : b.Moves (fun _ => 0) leafTy fun i => leavesT (n i) (s i)
structure AxisStroke (b : Bench m ι) (l : ι→ℕ) (r : ι→Axes) (u : ι→ℕ→Stroke) : Prop where
  fen : b.Fen l r
  leaf : (b.scan l).Spring (fun i => r i.i i.j) (fun i => u i.i i.j)
lemma AxisStroke.good (h : b.AxisStroke l r u) (i : ι) (j : ℕ) (hj : j<l i) : (u i j).Sound (r i j) := h.2.1 ⟨i, j, hj⟩
lemma AxisStroke.transfer {l : κ→ℕ} {r : κ→Axes} {u : κ→ℕ→Stroke} (h : q.AxisStroke l r u) {f}
    (g : b.Instant q f) :
    b.AxisStroke (fun i => l (f i)) (fun i => r (f i)) (fun i => u (f i)) :=
  ⟨h.1.transfer g, fun d => h.2.1 ⟨f d.i, d.j, d.hj⟩, h.2.2.transfer (Fen.scanInstant g)⟩
structure ShardFields (b : Bench m ι) (Y : ι→PowBlock) : Prop where
  starts : b.Nick fun i => (Y i).start
  widths : b.Nick fun i => (Y i).width
  tall : b.Nick fun i => (Y i).height
  seat : b.Nick fun i => (Y i).seat
lemma ShardFields.chip_moves (h : b.ShardFields Y) : b.Moves (fun _ => 0) chipTy fun i => chip (Y i) := h.1.1.pair (h.2.1.pair (h.3.1.pair h.4.1))
lemma ShardFields.addr (h : b.ShardFields Y) : b.Nick fun i => (Y i).addr := h.1.add h.4
lemma ShardFields.of_chip {l : ι→ℕ} (h : Small b.size n) (hh : ∀ i,(Y i).Mark (n i) (l i))
    (hg : b.Moves (fun _ => 0) chipTy fun i => chip (Y i)) : b.ShardFields Y :=
  have M := fun i => hh i; have T := fun i => (Y i).height.lt_two_pow_self
  ⟨⟨hg.fst, h.mono fun i => by have := (M i).1; unfold tip at this; omega⟩,
   ⟨hg.snd.fst, h.mono fun i => by have := (M i).1; unfold tip at this; omega⟩,
   ⟨hg.snd.snd.fst, h.mono fun i => by have := (M i).1; have := (M i).2; have := T i; unfold tip at *; omega⟩,
   ⟨hg.snd.snd.snd, h.mono fun i => by have := (M i).1; have := (M i).4; unfold tip at *; omega⟩⟩
lemma survey_lt {r : Axes} {u : ℕ → Stroke} {L : ℕ} (h : Splits r L)
    (g : ∀ i<L, (u i).Sound (r i)) (j : ℕ) (hj : j ≤ L) (k : ℕ) (hk : k<extent r j) :
    (survey r u j k).1 < extent r j := by
  induction j generalizing k with
  | zero => show 0 < 1; omega
  | succ j ih =>
    have c := h.cut hj
    exact c.join_lt (ih (by omega) _ (c.div_lt hk)) ((g j hj).bdix _ (c.mod_lt k))
lemma canopyM (r : Axes) (u : ℕ → Stroke) {L : ℕ} (h : Splits r L) (g : ∀ i<L, (u i).Sound (r i))
    (j : ℕ) (hj : j ≤ L) (i : ℕ) (hi : i<extent r j) (k : ℕ) (hk : k<extent r j) :
    axisKron r (fun t => leafM (u t)) j i k =
      if k = (survey r u j i).1 then (survey r u j i).2 else 0 := by
  induction j generalizing i k with
  | zero => simp_all [extent, axisKron, survey, climb]
  | succ j ih =>
    have c := h.cut hj
    have hx := (g j hj).bdix _ (c.mod_lt i); have hr : 0 < r j := by omega
    show axisKron r _ j (i/r j) (k/r j) * leafM (u j) (i%r j) (k%r j) = if k = (survey r u j (i/r j)).1*r j+_ then (survey r u j (i/r j)).2*_ else 0
    rw [ih (by omega) _ (c.div_lt hi) _ (c.div_lt hk), leafM]
    by_cases e : k = (survey r u j (i/r j)).1*r j + (u j).ix (i%r j)
    · have e1 : k/r j = (survey r u j (i/r j)).1 := by rw [e, Nat.add_comm, Nat.add_mul_div_right _ _ hr, Nat.div_eq_of_lt hx, zero_add]
      have e2 : k%r j = (u j).ix (i%r j) := by rw [e, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]
      rw [if_pos e, e1, e2]; simp
    · have := Nat.div_add_mod k (r j)
      rw [if_neg e]; split_ifs with a b <;> simp_all; rw [mul_comm] at this; omega
lemma graftM (r : Axes) (u : ℕ → Stroke) {L : ℕ} (h : Splits r L) (g : ∀ i<L, (u i).Sound (r i))
    (x : Line) (k : ℕ) (hk : k<extent r L) :
    graft (extent r L) (axisKron r (fun t => leafM (u t)) L) x k =
      (survey r u L k).2 * x (survey r u L k).1 := by
  rw [graft, Finset.sum_eq_single (survey r u L k).1 (fun b hb e => by rw [canopyM r u h g L le_rfl k hk b (Finset.mem_range.1 hb), if_neg e, zero_mul])
    (fun e => (e (Finset.mem_range.2 (survey_lt h g L le_rfl k hk))).elim), canopyM r u h g L le_rfl k hk _ (survey_lt h g L le_rfl k hk), if_pos rfl]
lemma AxisStroke.climbing (h : b.AxisStroke l r u) {s : Ty} (S : ι → ℕ → ℕ → T s)
    (hS : b.Moves (fun _ => 0) s fun i => S i 0 0)
    (step : (Fen.stalk b l r s S).Moves (fun _ => 0) blossomTy
        (fun d => blossom (u d.i.i d.i.j) (Forks.tOff d)) →
      (Fen.stalk b l r s S).Moves (fun _ => 0) s fun d => S d.i.i (d.i.j+1) d.j) :
    b.Moves (fun i => extent (r i) (l i)) (a s) fun i =>
      Tape.tab (extent (r i) (l i)) (S i (l i)) :=
  h.1.visit S hS (step (((h.2.2.transfer (Fen.stalkFeeds ..)).pick _ (Fen.stalkReads h.1 S).2.1.1 h.1.lower)))
theorem AxisStroke.survey_moves (h : b.AxisStroke l r u) :
    b.Moves (fun i => extent (r i) (l i)) (a sapTy) fun i =>
      Tape.tab (extent (r i) (l i)) (survey (r i) (u i) (l i)) :=
  h.climbing (s := sapTy) (fun i k j => survey (r i) (u i) k j) ((Moves.wc 0).pair Moves.one) fun hb =>
    have R := Fen.stalkReads (s := sapTy) h.1 (fun i k j => survey (r i) (u i) k j)
    have Nr := h.1.4.transfer (Fen.stalkFeeds ..)
    have N1 : (Fen.stalk b l r sapTy _).Nick fun d => (survey (r d.i.i) (u d.i.i) d.i.j (Forks.tUp d)).1 :=
      ⟨R.2.2.fst, (h.1.3.reindex fun d : Forks l r => d.i.i).mono fun d => (survey_lt (h.1.2 _) (fun i hi => h.good _ i hi)
        d.i.j d.i.hj.le _ (h.1.smaller d) |>.trans_le ((h.1.2 _).extent_le d.i.hj.le)).le⟩
    ((N1.mul Nr).add ⟨hb.fst.fst, Nr.2.mono fun d => ((h.good _ _ d.i.hj).bdix _ (h.1.lower d)).le⟩).1.pair (R.2.2.snd.mul hb.fst.snd)
theorem AxisStroke.blocks_moves (h : b.AxisStroke l r u) :
    b.Moves (fun i => extent (r i) (l i)) (a chipTy) fun i =>
      Tape.tab (extent (r i) (l i)) fun j => chip (strokeBlocks (r i) (u i) (l i) j) :=
  h.climbing (s := chipTy) (fun i k j => chip (strokeBlocks (r i) (u i) k j)) ((Moves.wc 0).pair ((Moves.wc 1).pair ((Moves.wc 0).pair (Moves.wc 0)))) fun hb =>
    have R := Fen.stalkReads (s := chipTy) h.1 (fun i k j => chip (strokeBlocks (r i) (u i) k j))
    have Nr := h.1.4.transfer (Fen.stalkFeeds ..)
    have Ks := ShardFields.of_chip (l := fun d : Forks l r => d.i.j) (h.1.midst.reindex During.i) (fun d => (mosaic_quilt (r d.i.i) d.i.j (u d.i.i) ((h.1.2 _).cut d.i.hj.le)
      fun i hi => h.good _ i (by have := d.i.hj; omega)).mark _ (h.1.smaller d)) R.2.2
    have Kt := ShardFields.of_chip (l := fun _ => 1) Nr.2 (fun d => PairBlocks.marked (h.good _ _ d.i.hj) (h.1.lower d)) hb.snd
    ShardFields.chip_moves (Y := fun d => fringe (r d.i.i d.i.j) (strokeBlocks (r d.i.i) (u d.i.i) d.i.j (Forks.tUp d)) (block (u d.i.i d.i.j) (Forks.tOff d)))
      ⟨(Ks.1.mul Nr).add (Ks.2.mul Kt.1), Ks.2.mul Kt.2, Ks.3.add Kt.3, (Ks.4.mul Kt.2).add Kt.4⟩
theorem AxisStroke.perm_moves (h : b.AxisStroke l r u) (cl : Paint) (x : ι → Line)
    (hx : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (extent (r i) (l i)) (x i)) :
    b.Moves (fun i => extent (r i) (l i)) (a (c cl)) fun i =>
      Tape.tab (extent (r i) (l i)) (graft (extent (r i) (l i))
        (axisKron (r i) (fun j => leafM (u i j)) (l i)) (x i)) :=
  caseM h.survey_moves <|
    have I := Instant.extend (t := a sapTy) b fun i => Tape.tab (extent (r i) (l i)) (survey (r i) (u i) (l i))
    have X := hx.transfer I
    have NE : (b.extend _ _).Nick fun i => extent (r i) (l i) := ⟨X.len h.1.3, h.1.3⟩
    have I1 := Instant.scan (b.extend _ _) fun i => extent (r i) (l i)
    have P := ((cherry (W := fun _ => 0) b _).transfer I1).pick _ (chop NE).1 fun d => d.hj
    (arrayNow (t := c cl) NE (fun i k => (survey (r i) (u i) (l i) k).2 * x i (survey (r i) (u i) (l i) k).1) (P.snd.mul ((X.transfer I1).pick _ P.fst fun d =>
      survey_lt (h.1.2 d.i) (fun j hj => h.good _ j hj) _ le_rfl d.j d.hj))).congr fun i =>
      congrArg (Tape.mk _) (funext fun k => (graftM (r i) (u i) (h.1.2 i) (fun j hj => h.good i j hj) (x i) k k.2).symm)
end PowerSaving.RAM.Bench
end OAI
