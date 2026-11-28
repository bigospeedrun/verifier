-- Reels as computable tables, axis strokes (part 1); the ripple engine statement `RippleEngine` and its
-- use on block covers and axis reels (part 2). Each part has its own notices and credits; see texts/credits.lean.
import Submission.CostCalculus
import Submission.EngineMoves
import Submission.ReelKit
import Submission.EngineSetup
set_option linter.all false

-- ===== begin part 1: reels as computable tables; axis strokes =====
section
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
abbrev strokeCellTy := p w (p sc w)
abbrev strokeTapeTy := a strokeCellTy
abbrev reelTapeTy := a strokeTapeTy
def strokeCell (s : Stroke) (i : ℕ) : T strokeCellTy := (s.ix i,s.dye i,s.partner i)
def strokeTape (n : ℕ) (s : Stroke) : T strokeTapeTy := Tape.tab n (strokeCell s)
def reelTape (n : ℕ) (r : Reel) : T reelTapeTy := Tape.tab r.beats fun i => strokeTape n (r.atBeat i)
section
open AxisTensor PowBlock ReelKit PairBlocks
abbrev blockCellTy := p w (p w (p w w))
abbrev surveyCellTy := p w sc
abbrev strokeBlockCellTy := p surveyCellTy blockCellTy
abbrev strokeBlocksTy := a strokeBlockCellTy
abbrev reelBlocksTy := a strokeBlocksTy
def blockCell (s : PowBlock) : T blockCellTy := (s.start,s.width,s.height,s.seat)
def strokeBlockCell (u : Stroke) (i : ℕ) : T strokeBlockCellTy := ((u.ix i,u.dye i),blockCell (block u i))
def strokeBlocksT (n : ℕ) (u : Stroke) : T strokeBlocksTy := Tape.tab n (strokeBlockCell u)
def reelBlocksT (n : ℕ) (u : Reel) : T reelBlocksTy := Tape.tab u.beats fun i => strokeBlocksT n (u.atBeat i)
end
universe U V
namespace Bench
variable {m : Bool} {ι : Type U} {κ : Type V} {b : Bench m ι} {q : Bench m κ}
section
open Complex
structure ConjComputes (b : Bench m ι) (f : ι→ℂ) : Prop where
  bright : b.Computes sc f
  dull : b.Computes sc (fun i => starRingEnd ℂ (f i))
variable {f : ι→ℂ}
lemma ConjComputes.transfer {p : ι→κ} {f : κ→ℂ} (h : q.ConjComputes f) (g : b.PolyReads q p) :
    b.ConjComputes (fun i => f (p i)) := ⟨pull g h.1, pull g h.2⟩
lemma ConjComputes.letterI (h : b.Computes sc fun _ => I) : b.ConjComputes (fun _ => I) := ⟨h, h.neg.congr fun _ => conj_I.symm⟩
lemma ConjComputes.of_root {n : ι→ℕ} (h : b.Computes sc f) (hn : ∀ i, 0<n i)
    (hf : ∀ i, f i ^ n i = 1) : b.ConjComputes f :=
  ⟨h, (h.inv fun i e => by simpa [e, zero_pow (hn i).ne'] using hf i).congr fun i => (Spectral.conj_of_root (hn i) (hf i)).symm⟩
end
def LineConjComputes (b : Bench m ι) (n : ι→ℕ) (x : ι → Line) : Prop :=
  (b.scan n).ConjComputes (fun i => x i.i i.j)
lemma LineConjComputes.transfer {n : κ→ℕ} {x : κ→Line} (h : q.LineConjComputes n x) {f} (g : b.PolyReads q f) :
    b.LineConjComputes (fun i => n (f i)) (fun i => x (f i)) :=
  ConjComputes.transfer (p := fun d : During _ => (⟨f d.i, d.j, d.hj⟩ : During n)) h (((PolyReads.scan b _).next g).select (PolyCan.second))
variable {n : ι→ℕ}
lemma leadOffset_le (u : Stroke) (k : ℕ) : AxisTensor.PairBlocks.leadOffset u k ≤ 2*k :=
  (Finset.sum_le_card_nsmul _ _ 2 fun a _ => by unfold AxisTensor.PairBlocks.leadSize AxisTensor.PairBlocks.pairSize; split_ifs <;> omega).trans (by simp [mul_comm])
open AxisTensor
structure AxisCtx (b : Bench m ι) (l : ι→ℕ) (r : ι→Axes) : Prop where
  high : b.FreeWord l
  good : ∀ i,Splits (r i) (l i)
  span : Small b.size fun i => extent (r i) (l i)
  part : (b.scan l).FreeWord fun d => r d.i d.j
abbrev axisSteps {ι : Type*} (l : ι→ℕ) (r : ι→Axes) (d : During l) :=
  extent (r d.i) (d.j+1)
abbrev AxisStep (l : ι→ℕ) (r : ι→Axes) := During (axisSteps l r)
namespace AxisStep
variable {l : ι→ℕ} {r : ι→Axes}
def stepHigh (d : AxisStep l r) := d.j/r d.i.i d.i.j
def stepLow (d : AxisStep l r) := d.j%r d.i.i d.i.j
end AxisStep
namespace AxisCtx
open AxisStep
variable {l : ι→ℕ} {r : ι→Axes} {s : Ty}
lemma scanInstant {l : κ→ℕ} {f} (g : b.FreeReads q f) :
    (b.scan fun i => l (f i)).FreeReads (q.scan l) fun d => ⟨f d.i, d.j, d.hj⟩ := ((FreeReads.scan _ _).next g).select (Can.second)
lemma transfer {l : κ→ℕ} {r : κ→Axes} (h : q.AxisCtx l r) {f} (g : b.FreeReads q f) :
    b.AxisCtx (fun i => l (f i)) (fun i => r (f i)) :=
  ⟨h.1.transfer g, fun i => h.2 (f i), (h.3.reindex f).trans g.2, h.4.transfer (scanInstant g)⟩
lemma extent_small (h : b.AxisCtx l r) :
    Small (fun d : During l => b.size d.i) fun d => extent (r d.i) d.j :=
  (h.3.reindex During.i).mono fun d => (h.2 d.i).extent_le d.hj.le
lemma smaller (h : b.AxisCtx l r) (d : AxisStep l r) : stepHigh d<extent (r d.i.i) d.i.j :=
  ((h.2 _).cut d.i.hj).div_lt d.hj
lemma lower (h : b.AxisCtx l r) (d : AxisStep l r) : stepLow d<r d.i.i d.i.j :=
  ((h.2 _).cut d.i.hj).mod_lt _
def stepBench (b : Bench m ι) (l : ι→ℕ) (r : ι→Axes) (s : Ty) (S : ι → ℕ → ℕ → T s) :
    Bench m (AxisStep l r) :=
  ((b.scan l).along During.i).extend (p w (p w s))
    (fun i => (stepHigh i,stepLow i,S i.i.i i.i.j (stepHigh i)))
lemma stepBench_reads (b : Bench m ι) (l : ι→ℕ) (r : ι→Axes) (s : Ty) (S : ι → ℕ → ℕ → T s) :
    (stepBench b l r s S).FreeReads (b.scan l) During.i := (FreeReads.extend _ _).next (FreeReads.along _ _)
lemma stepBench_words (h : b.AxisCtx l r) (S : ι → ℕ → ℕ → T s) :
    let B := stepBench b l r s S
    B.FreeWord stepHigh ∧ B.FreeWord stepLow ∧ B.Moves (fun _ => 0) s (fun i => S i.i.i i.i.j (stepHigh i)) :=
  have M := newestMoves ((b.scan l).along During.i) (t := p w (p w s)) _
  ⟨⟨M.fst.toPoly _, (h.3.reindex fun d : AxisStep l r => d.i.i).mono fun d => ((h.smaller d).trans_le ((h.2 _).extent_le d.i.hj.le)).le⟩,
   ⟨M.snd.fst.toPoly _, (h.4.2.reindex During.i).mono fun d => (h.lower d).le⟩, M.snd.snd⟩
theorem climbAxes (h : b.AxisCtx l r) (S : ι → ℕ → ℕ → T s)
    (hS : b.Moves (fun _ => 0) s fun i => S i 0 0)
    (hs : (stepBench b l r s S).Moves (fun _ => 0) s fun d => S d.i.i (d.i.j+1) d.j) :
    b.Moves (fun i => extent (r i) (l i)) (a s) fun i =>
      Tape.tab (extent (r i) (l i)) (S i (l i)) := by
  let f : ι → ℕ → T (a s) := fun i k => Tape.tab (extent (r i) k) (S i k)
  have I0 : (b.climbs l (a s) f).FreeReads (b.scan l) id := (FreeReads.climbs ..).select (climbIndex h.1 f).toMoves
  have T0 := tokenNow b l f
  have Nr := h.4.transfer I0
  have NE : (b.climbs l (a s) f).FreeWord fun d => extent (r d.i) d.j * r d.i d.j :=
    WordIn.mul ⟨(T0.len h.extent_small).toPoly _, h.extent_small⟩ Nr
  have I1 := FreeReads.scan (b.climbs l (a s) f) fun d => extent (r d.i) d.j * r d.i d.j
  have Nj := scanIndex NE; have Nr' := Nr.transfer I1
  have IA : (b.climbs l (a s) f |>.scan fun d => extent (r d.i) d.j * r d.i d.j).FreeReads
      ((b.scan l).along During.i) (fun e => (⟨e.i, e.j, e.hj⟩ : AxisStep l r)) := ⟨(I1.next I0).1, (I1.next I0).2⟩
  have B := hs.transfer (IA.supply _ ((Nj.div Nr').toMoves.pair ((Nj.residue Nr').toMoves.pair
    ((T0.transfer I1).pick _ (Nj.div Nr').toMoves fun e => ((h.2 _).cut e.i.hj).div_lt e.hj))))
  refine ((repeatM (u := fun i k => extent (r i) k * r i k) h.1 f ((arrayNow (WordIn.wc 1) (fun i j => S i 0 j) ((hS.transfer (FreeReads.scan _ _)).congr fun d => by
    rw [show d.j = 0 by have := d.hj; omega])).weaken (Dom.const _ 1)) (arrayNow NE (fun d j => S d.i (d.j+1) j) B)).weaken ⟨3, fun i => ?_⟩)
  have := (h.2 i).tree_bound; have := (h.2 i).axes_le; have := Finset.sum_range_succ' (fun j => extent (r i) j) (l i)
  dsimp only [extent] at *; omega
end AxisCtx
structure ExpWords (b : Bench m ι) (e : ι→ℕ) : Prop where
  ep : b.PolyWord e
  span : b.PolyWord (fun i => 2^e i)
variable {e : ι→ℕ}
lemma ExpWords.transfer {e : κ→ℕ} (h : q.ExpWords e) {f : ι→κ} (F : b.PolyReads q f) :
    b.ExpWords (fun i => e (f i)) := ⟨draw F h.1, draw F h.2⟩
lemma WordIn.pow2 (h : b.PolyWord e) : Small b.size (fun i => 2^e i) → b.PolyWord (fun i => 2^e i) := h.twoPow h.2
lemma ExpWords.fromSmall (h : b.PolyWord e) (g : Small b.size (fun i => 2^e i)) : b.ExpWords e := ⟨h, h.pow2 g⟩
lemma bridgeBeats_word (h : b.PolyWord e) : b.PolyWord fun i => bridgeBeats (e i) :=
  let p := (h.minimum (.wc 3)).pow2 ((Small.const _ 8).mono fun i => Nat.pow_le_pow_right two_pos (min_le_right _ 3))
  (iteN (Decides.lt h (.wc 4)) (p.mul (p.mul (p.mul (.wc 26)))) ((WordIn.wc 16).mul ((WordIn.wc 16).mul ((WordIn.wc 16).mul
    ((WordIn.wc 4).mul (((WordIn.wc 80).mul (h.sub (.wc 4))).add (.wc 348))))))).congr fun i => by
    unfold bridgeBeats; split_ifs with c
    · rw [Nat.min_eq_left (by omega : e i ≤ 3)]
    · rfl
lemma toeplitzBeats_word {e : ι→ℕ} (h : b.PolyWord e) : b.PolyWord fun k => toeplitzBeats (e k) :=
  have S : Small b.size fun i => 10000000*(e i+1)^2 := (Small.const _ _).mul ((h.2.add (.const _ 1)).pow 2)
  ⟨loop (t := w) h (fun _ j => toeplitzBeats j) (PolyCan.wc 1) (WordIn.add ⟨PolyMoves.token .., (S.reindex During.i).mono fun d =>
    (toeplitzBeats_le _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (show d.j+1 ≤ e d.i+1 by have := d.hj; omega) 2))⟩ (bridgeBeats_word (climbIndex h _))).1,
    S.mono fun _ => toeplitzBeats_le _⟩
section
open Complex Spectral Finset
variable {c : Bench m ι} {μ : Type U} {c' : Bench m μ} {f : μ→ι}
def LineComputes (c : Bench m ι) (F : ι→ℕ→ℂ) : Prop :=
  ∀ (μ : Type U) (c' : Bench m μ) (f : μ→ι) (j : μ→ℕ), c'.PolyReads c f → c'.PolyWord j →
    c'.Computes sc fun k => F (f k) (j k)
namespace ReelComputes
variable {R A B : ι→Reel}
lemma concatReels_at (a : ℕ→Reel) (B : ℕ) : ∀ L t, (∀ i<L, (a i).beats=B) → t<L*B →
    (concatReels a L).atBeat t = (a (t/B)).atBeat (t%B) := by
  intro L; induction L with
  | zero => intro t _ ht; simp at ht
  | succ L ih =>
    intro t h ht
    have hB := beats_concatReels L B fun i hi => h i (by omega)
    show ((concatReels a L).stack (a L)).atBeat t = _
    simp only [Reel.stack, hB]; rw [Nat.succ_mul] at ht; split_ifs with c
    · exact ih t (fun i hi => h i (by omega)) c
    · have q : t / B = L := Nat.div_eq_of_lt_le (by omega) (by rw [Nat.succ_mul]; omega)
      rw [Nat.mod_def, q, mul_comm]
end ReelComputes
namespace LineComputes
variable {F G : ι→ℕ→ℂ}
lemma at_ {j : ι→ℕ} (h : c.LineComputes F) (hj : c.PolyWord j) : c.Computes sc fun k => F k (j k) := h _ c id j ⟨PolyCan.id, Small.self _⟩ hj
lemma pow {z : ι→ℂ} (h : c.Computes sc z) : c.LineComputes fun k i => z k^i := fun _ _ _ _ hf hj =>
  loop hj _ (PolyCan.one.congr fun _ => (pow_zero _).symm) (((PolyMoves.token ..).mul (pull ((PolyReads.climbs ..).next hf) h)).congr fun _ => (pow_succ ..).symm)
end LineComputes
lemma gap_zero {z : ℂ} {n i : ℕ} (hp : Spectral.PrimRoot z n) (hn : 0<n) (hi : n ≤ i) : gap z i = 0 :=
  prod_eq_zero (mem_range.2 (show n-1 < i by omega)) (by rw [Nat.sub_add_cancel hn, hp.pow_eq_one, sub_self])
lemma toeplitzInv_succ (H : Line) (k : ℕ) :
    toeplitzInv H (k+1) = -(∑ x ∈ range (k+1), toeplitzInv H (k-x)*H (x+1))/H 0 := by
  simp only [toeplitzInv, toeplitzInvUpTo, add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero, ↓reduceIte,
    toeplitzInvUpTo_stable H k _ (Nat.sub_le k _)]
lemma conj_toeplitzInv (H : Line) (j : ℕ) :
    starRingEnd ℂ (toeplitzInv H j) = toeplitzInv (fun i => starRingEnd ℂ (H i)) j := by
  induction j using Nat.strong_induction_on with
  | _ j ih => cases j with
    | zero => simp [toeplitzInv, toeplitzInvUpTo]
    | succ k => simp only [toeplitzInv_succ, map_div₀, map_neg, map_sum, map_mul, ih _ (Nat.lt_succ_of_le (Nat.sub_le k _))]
lemma mod_two (v e : ℕ) : v%2^(e+1) = if v%2^(e+1)<2^e then v%2^e else v%2^e+2^e := by
  rw [Nat.mod_pow_succ]; have := Nat.mod_lt (v/2^e) two_pos; have := Nat.mod_lt v (Nat.two_pow_pos e)
  rcases (show v/2^e%2 = 0 ∨ v/2^e%2 = 1 by omega) with e|e <;> simp [e, this]
end
section
open Complex Finset Spectral
variable {ν : Type U} {c : Bench m ι} {d : Bench m ν} {A B : ι → Reel} {x y : ι → ℕ} {F G : ι → Line}
local notation "FS" => PolyReads.scan _ _
local notation "RS" => restricted _ _
lemma PolyReads.into {P : ι → Prop} {g : ν → {i // P i}} (h : d.PolyReads c fun k => (g k).1) : d.PolyReads (c.onlyWhere P) g := ⟨h.1, h.2⟩
lemma PolyReads.res {P : ν → Prop} {f : ν → ι} (hf : d.PolyReads c f) : (d.onlyWhere P).PolyReads c fun k => f k.1 := (restricted d P).next hf
lemma Decides.on {P : ι → Prop} (h : c.Decides P) {f : ν → ι} (hf : d.PolyReads c f) : d.Decides fun k => P (f k) :=
  let ⟨_, hx, e⟩ := h; ⟨_, draw hf hx, fun _ => e _⟩
lemma Computes.ite {P : ι → Prop} [DecidablePred P] {t} {x y : ι → T t} (h : c.Decides P) (a : c.Computes t x) (b : c.Computes t y) :
    c.Computes t fun k => if P k then x k else y k := branchM h (pull RS a) (pull RS b)
lemma Computes.sum {N : ι → ℕ} {F : ι → ℕ → ℂ} (hN : c.PolyWord N) (hF : (c.scan N).Computes sc fun e => F e.i e.j) :
    c.Computes sc fun k => ∑ j ∈ range (N k), F k j :=
  loop (t := sc) hN (fun k i => ∑ j ∈ range i, F k j) (PolyCan.zero.congr fun _ => rfl)
    (((PolyMoves.token ..).add (pull ((PolyReads.climbs ..).select (climbIndex hN _).1) hF)).congr fun _ => (sum_range_succ ..).symm)
lemma Computes.prod {N : ι → ℕ} {F : ι → ℕ → ℂ} (hN : c.PolyWord N) (hF : (c.scan N).Computes sc fun e => F e.i e.j) :
    c.Computes sc fun k => ∏ j ∈ range (N k), F k j :=
  loop (t := sc) hN (fun k i => ∏ j ∈ range i, F k j) (PolyCan.one.congr fun _ => rfl)
    (((PolyMoves.token ..).mul (pull ((PolyReads.climbs ..).select (climbIndex hN _).1) hF)).congr fun _ => (prod_range_succ ..).symm)
lemma Computes.cast {N : ι → ℕ} (hN : c.PolyWord N) : c.Computes sc fun k => (N k : ℂ) :=
  loop (t := sc) hN (fun _ i => (i : ℂ)) (PolyCan.zero.congr fun _ => Nat.cast_zero.symm) (((PolyMoves.token ..).add PolyCan.one).congr fun _ => (Nat.cast_succ _).symm)
lemma WordIn.sum {M : ι → ℕ} {F : ι → ℕ → ℕ} (hM : c.PolyWord M) (hF : (c.scan M).PolyWord fun e => F e.i e.j)
    (hs : Small c.size fun k => ∑ a ∈ range (M k), F k a) : c.PolyWord fun k => ∑ a ∈ range (M k), F k a :=
  ⟨loop (t := w) hM (fun k i => ∑ a ∈ range i, F k a) ((PolyCan.wc 0).congr fun _ => rfl)
    ((WordIn.add ⟨PolyMoves.token .., (hs.reindex During.i).mono fun e => sum_le_sum_of_subset (range_mono e.hj.le)⟩
      (draw ((PolyReads.climbs ..).select (climbIndex hM _).1) hF)).1.congr fun _ => (sum_range_succ ..).symm), hs⟩
open AxisTensor.PairBlocks in
lemma blockCell_computes {S : ι → Stroke} {N j : ι → ℕ} (hP : ∀ (ν : Type U) (d : Bench m ν) (f : ν → ι) (j : ν → ℕ), d.PolyReads c f →
    d.PolyWord j → (∀ k, j k < N (f k)) → d.PolyWord fun k => (S (f k)).partner (j k)) (hN : Small c.size N) (hj : c.PolyWord j)
    (hjN : ∀ k, j k < N k) : c.Computes blockCellTy fun k => blockCell (block (S k) (j k)) :=
  have hP' := hP _ c id j ⟨PolyCan.id, Small.self _⟩ hj hjN
  have cr := hj.minimum hP'; have s := scanIndex cr
  have hP := hP _ _ _ _ FS s fun e => by have := e.hj; have := hjN e.i; unfold pairLead at *; omega
  have E := Decides.eq hj hP'
  (WordIn.sum (F := fun k a => leadSize (S k) a) cr (iteN (Decides.eq s (s.minimum hP)) (iteN (Decides.eq s hP) (.wc 1) (.wc 2)) (.wc 0))
    ((hN.add hN).mono fun k => (leadOffset_le _ _).trans (by have := hjN k; omega))).1.pair
    ((iteN E (.wc 1) (.wc 2)).1.pair ((iteN E (.wc 0) (.wc 1)).1.pair (iteN (Decides.eq hj cr) (.wc 0) (.wc 1)).1))
namespace LineComputes
lemma congr (h : c.LineComputes F) (e : ∀ k i, F k i = G k i) : c.LineComputes G := fun _ _ _ _ hf hj => (h _ _ _ _ hf hj).congr fun _ => e _ _
lemma const {z : ι → ℂ} (h : c.Computes sc z) : c.LineComputes fun k _ => z k := fun _ _ _ _ hf _ => pull hf h
lemma rat (z : ℚ) : c.LineComputes fun _ _ => (z : ℂ) := fun _ _ _ _ _ _ => ⟨0, Can.rat z⟩
lemma on (h : c.LineComputes F) {f : ν → ι} (hf : d.PolyReads c f) : d.LineComputes fun k => F (f k) := fun _ _ _ _ hg => h _ _ _ _ (hg.next hf)
lemma one : c.LineComputes fun _ _ => 1 := fun _ _ _ _ _ _ => PolyCan.one
lemma lift (o : ℂ → ℂ → ℂ) (p : ∀ {ν : Type U} {d : Bench m ν} {x y}, d.Computes sc x → d.Computes sc y → d.Computes sc fun k => o (x k) (y k))
    (h : c.LineComputes F) (g : c.LineComputes G) : c.LineComputes fun k i => o (F k i) (G k i) := fun _ _ _ _ hf hj => p (h _ _ _ _ hf hj) (g _ _ _ _ hf hj)
lemma add : c.LineComputes F → c.LineComputes G → c.LineComputes fun k i => F k i + G k i := lift _ PolyCan.add
lemma sub : c.LineComputes F → c.LineComputes G → c.LineComputes fun k i => F k i - G k i := lift _ PolyCan.sub
lemma mul : c.LineComputes F → c.LineComputes G → c.LineComputes fun k i => F k i * G k i := lift _ PolyCan.mul
lemma inv (h : c.LineComputes F) (nz : ∀ k i, F k i ≠ 0) : c.LineComputes fun k i => (F k i)⁻¹ := fun _ _ _ _ hf hj => (h _ _ _ _ hf hj).inv fun _ => nz _ _
lemma invZ (h : c.LineComputes F) {N : ι → ℕ} (hN : c.PolyWord N) (hz : ∀ k i, F k i = 0 ↔ N k ≤ i) : c.LineComputes fun k i => (F k i)⁻¹ :=
  fun _ d f j hf hj => (branchM (x := fun k => (F (f k) (j k))⁻¹) (y := fun _ => 0) (Decides.lt hj (draw hf hN)) ((h _ _ _ _ hf.res
    (draw RS hj)).inv fun k => mt (hz _ _).1 (not_le.2 k.2)) (PolyCan.zero (cl := .scalar))).congr fun k => by
    dsimp only; split_ifs with e; rfl; rw [(hz _ _).2 (not_lt.1 e), inv_zero]
lemma gap {z : ι → ℂ} (h : c.Computes sc z) : c.LineComputes fun k i => gap (z k) i := fun _ _ _ _ hf hj =>
  Computes.prod hj (PolyCan.one.sub (pow h _ _ _ _ (PolyReads.next FS hf) ((scanIndex hj).add (.wc 1))))
lemma roof {z : ι → ℂ} (h : c.Computes sc z) : c.LineComputes fun k i => roof (z k) i := fun _ _ _ _ hf hj =>
  Computes.prod hj (pow h _ _ _ _ (PolyReads.next FS hf) (scanIndex hj)).neg
lemma freq {N : ι → ℕ} {z : ι → ℂ} (hN : c.PolyWord N) (hz : c.Computes sc z) (h : c.LineComputes F) : c.LineComputes fun k i => freq (N k) (z k) (F k) i :=
  fun _ _ _ _ hf hj => have hN := draw hf hN; have g := PolyReads.next FS hf
    Computes.sum hN ((pow hz _ _ _ _ g ((draw FS hj).mul (scanIndex hN))).mul (h _ _ _ _ g (scanIndex hN)))
lemma rise (h : c.LineComputes F) (hx : c.PolyWord x) (hy : c.PolyWord y) : c.Computes sc fun k => Spectral.rise (F k) (x k) (y k) :=
  Computes.ite (Decides.le hy hx) (h.at_ (hx.sub hy)) PolyCan.zero
lemma blockFilter {B E S L M : ι → ℕ} (hB : c.PolyWord B) (hE : c.PolyWord E) (hS : c.PolyWord S) (hL : c.PolyWord L) (hM : c.PolyWord M) (h : c.LineComputes F) :
    c.LineComputes fun k i => blockFilter (B k) (E k) (S k) (L k) (M k) (F k) i := fun _ _ _ _ hf hj =>
  have g := fun {x : ι → ℕ} (h : c.PolyWord x) => draw hf h; have h := h.on hf; have b := ((WordIn.wc 2).mul (g hB)).sub hj
  Computes.ite (Decides.lt hj (g hB)) (Computes.ite (Decides.lt hj (g hS)) (h.rise ((g hM).add hj) (g hL)) PolyCan.zero)
    (Computes.ite ((Decides.lt (.wc 0) (g hS)).both (Decides.lt b (g hE))) (h.rise (g hM) ((g hL).add b)) PolyCan.zero)
lemma toeplitzInv {H : ι → Line} (h : c.LineComputes H) (h0 : ∀ k, H k 0 ≠ 0) : c.LineComputes fun k j => Spectral.toeplitzInv (H k) j := by
  intro _ d f j hf hj
  have h := h.on hf
  let X : _ → ℕ → T (a sc) := fun k i => Tape.tab (i+1) (Spectral.toeplitzInv (H (f k)))
  have step : (d.climbs j (a sc) X).Computes (a sc) fun e => X e.i (e.j+1) := by
    have hi := climbIndex hj X
    refine tab (hi.add (.wc 2)) _ ?_
    have hx := scanIndex (hi.add (.wc 2)); have hi := draw (PolyReads.scan _ fun e => e.j + 2) hi
    have T := pull (PolyReads.scan _ fun e => e.j + 2) (PolyMoves.token d j _ X)
    have hE := h.on ((PolyReads.scan _ fun e => e.j + 2).next (PolyReads.climbs d j X))
    have S := Computes.sum (F := fun (g : During (fun e : During j => e.j + 2)) y => (X g.i.i g.i.j).look (g.i.j - y) sc.blank * H (f g.i.i) (y+1)) (hi.add (.wc 1))
      (((pull FS T).look ((draw FS hi).sub (scanIndex (hi.add (.wc 1)))).1).mul ((hE.on FS).at_ ((scanIndex (hi.add (.wc 1))).add (.wc 1))))
    refine (Computes.ite (Decides.le hx hi) (T.look hx.1) (((hE.at_ (.wc 0)).inv fun _ => h0 _).mul S.neg)).congr fun e => ?_
    have := e.hj; dsimp only [X]; split_ifs with x
    · rw [Tape.look_tab, if_pos (by omega)]
    · rw [show e.j = e.i.j + 1 by omega, toeplitzInv_succ, div_eq_inv_mul]
      congr 2; exact sum_congr rfl fun y hy => by rw [Tape.look_tab, if_pos (by simp only [mem_range, Order.lt_add_one_iff] at hy; omega)]
  exact ((loop hj X (tab (.wc 1) _ (((h.on FS).at_ (.wc 0) |>.inv fun _ => h0 _).congr fun e => by
    rw [show e.j = 0 by have := e.hj; omega]; simp only [Spectral.toeplitzInv, toeplitzInvUpTo])) step).look hj.1).congr fun k => by
    rw [Tape.look_tab, if_pos (Nat.lt_succ_self _)]
end LineComputes
abbrev HasIConst (c : Bench m ι) := c.LineComputes fun _ _ => I
def LineConj (c : Bench m ι) (F : ι → Line) : Prop := c.LineComputes F ∧ c.LineComputes fun k i => starRingEnd ℂ (F k i)
namespace LineConj
lemma congr (h : c.LineConj F) (e : ∀ k i, F k i = G k i) : c.LineConj G := ⟨h.1.congr e, h.2.congr fun _ _ => by rw [e]⟩
lemma on (h : c.LineConj F) {f : ν → ι} (hf : d.PolyReads c f) : d.LineConj fun k => F (f k) := ⟨h.1.on hf, h.2.on hf⟩
lemma rat (z : ℚ) : c.LineConj fun _ _ => (z : ℂ) := ⟨LineComputes.rat z, (LineComputes.rat z).congr fun _ _ => (map_ratCast _ _).symm⟩
lemma neg (h : c.LineConj F) : c.LineConj fun k i => -F k i := ⟨((LineComputes.rat 0).sub h.1).congr fun _ _ => by simp, ((LineComputes.rat 0).sub h.2).congr fun _ _ => by simp⟩
lemma freq {N : ι → ℕ} {z : ι → ℂ} (hN : c.PolyWord N) (hz : c.Computes sc z) (hz' : c.Computes sc fun k => starRingEnd ℂ (z k)) (h : c.LineConj F) :
    c.LineConj fun k i => freq (N k) (z k) (F k) i := ⟨LineComputes.freq hN hz h.1, (LineComputes.freq hN hz' h.2).congr fun _ _ => by simp only [Spectral.freq, map_sum, map_mul, map_pow]⟩
lemma blockFilter {B E S L M : ι → ℕ} (hB : c.PolyWord B) (hE : c.PolyWord E) (hS : c.PolyWord S) (hL : c.PolyWord L) (hM : c.PolyWord M) (h : c.LineConj F) :
    c.LineConj fun k i => blockFilter (B k) (E k) (S k) (L k) (M k) (F k) i :=
  ⟨LineComputes.blockFilter hB hE hS hL hM h.1, (LineComputes.blockFilter hB hE hS hL hM h.2).congr fun _ _ => by simp only [ReelKit.blockFilter, Spectral.rise, apply_ite (starRingEnd ℂ), map_zero]⟩
end LineConj
def ZoneWords (c : Bench m ι) (U : ι → Zone) : Prop := c.PolyWord (fun i => (U i).lo) ∧ c.PolyWord fun i => (U i).wide
lemma ZoneWords.on {U : ι → Zone} (h : c.ZoneWords U) {f : ν → ι} (hf : d.PolyReads c f) : d.ZoneWords fun k => U (f k) := ⟨draw hf h.1, draw hf h.2⟩
lemma ZoneWords.has {U : ι → Zone} {j : ι → ℕ} (h : c.ZoneWords U) (hj : c.PolyWord j) : c.Decides fun k => (U k).has (j k) :=
  Decides.both (Decides.le h.1 hj) (Decides.lt hj (h.1.add h.2))
def RootData (c : Bench m ι) (D : ι → ℕ) (z : ι → ℂ) : Prop :=
  c.PolyWord D ∧ c.PolyWord (fun i => 2^D i) ∧ c.Computes sc z ∧ c.Computes sc (fun i => starRingEnd ℂ (z i)) ∧ ∀ i, z i ≠ 0
lemma RootData.on {D : ι → ℕ} {z : ι → ℂ} (h : c.RootData D z) {f : ν → ι} (hf : d.PolyReads c f) : d.RootData (fun k => D (f k)) fun k => z (f k) :=
  ⟨draw hf h.1, draw hf h.2.1, pull hf h.2.2.1, pull hf h.2.2.2.1, fun _ => h.2.2.2.2 _⟩
lemma toeplitzReel_succ (h g r : Line) (k v : ℕ) : ReelKit.toeplitzReel h g r (k+1) v = toeplitzStep k v h g r (ReelKit.toeplitzReel h g r k (min (2^k) v)) (ReelKit.toeplitzReel h g r k (v - 2^k)) := rfl
def StrokeAt (c : Bench m ι) (S : ι → Stroke) (j : ι → ℕ) : Prop :=
  c.PolyWord (fun k => (S k).ix (j k)) ∧ c.Computes sc (fun k => (S k).dye (j k)) ∧ c.PolyWord fun k => (S k).partner (j k)
def ReelComputes (c : Bench m ι) (R : ι → Reel) : Prop :=
  c.PolyWord (fun i => (R i).beats) ∧ ∀ (ν : Type U) (d : Bench m ν) (f : ν → ι) (t j : ν → ℕ), d.PolyReads c f → d.PolyWord t → d.PolyWord j →
    (∀ k, t k < (R (f k)).beats) → d.StrokeAt (fun k => (R (f k)).atBeat (t k)) j
abbrev scan3 (c : Bench m ι) (L : ι → ℕ) := ((c.scan L).scan fun e => L e.i).scan fun e => L e.i.i
lemma StrokeAt.ite {P : ι → Prop} [DecidablePred P] {S S' : ι → Stroke} {j} (h : c.Decides P)
    (a : (c.onlyWhere P).StrokeAt (fun k => S k.1) (fun k => j k.1)) (b : (c.onlyWhere fun k => ¬P k).StrokeAt (fun k => S' k.1) (fun k => j k.1)) :
    c.StrokeAt (fun k => if P k then S k else S' k) j :=
  ⟨(branchN (x := fun k => (S k).ix (j k)) (y := fun k => (S' k).ix (j k)) h a.1 b.1).congr fun k => by by_cases p : P k <;> simp [p],
   (branchM (x := fun k => (S k).dye (j k)) (y := fun k => (S' k).dye (j k)) h a.2.1 b.2.1).congr fun k => by by_cases p : P k <;> simp [p],
   (branchN (x := fun k => (S k).partner (j k)) (y := fun k => (S' k).partner (j k)) h a.2.2 b.2.2).congr fun k => by by_cases p : P k <;> simp [p]⟩
lemma StrokeAt.congr {S S' : ι → Stroke} {j} (h : c.StrokeAt S j) (e : ∀ k, S k = S' k) : c.StrokeAt S' j := funext e ▸ h
namespace ReelComputes
lemma congr (h : c.ReelComputes A) (e : ∀ i, A i = B i) : c.ReelComputes B := funext e ▸ h
lemma on (h : c.ReelComputes A) {f : ν → ι} (hf : d.PolyReads c f) : d.ReelComputes fun k => A (f k) :=
  ⟨draw hf h.1, fun _ _ _ _ _ hg => h.2 _ _ _ _ _ (hg.next hf)⟩
lemma wait {D : ι → ℕ} (h : c.PolyWord D) : c.ReelComputes fun i => Reel.wait (D i) := ⟨h, fun _ _ _ _ _ _ _ hj _ => ⟨hj, PolyCan.one, hj⟩⟩
lemma stack (ha : c.ReelComputes A) (hb : c.ReelComputes B) : c.ReelComputes fun i => (A i).stack (B i) :=
  ⟨ha.1.add hb.1, fun _ _ f t _ hf ht hj hb' => StrokeAt.ite (Decides.lt ht (draw hf ha.1))
    (ha.2 _ _ _ _ _ hf.res (draw RS ht) (draw RS hj) fun k => k.2) (hb.2 _ _ _ (fun k => t k.1 - (A (f k.1)).beats) _
      hf.res (draw RS (ht.sub (draw hf ha.1))) (draw RS hj) fun k => by have := hb' k.1; have := k.2; simp only [Reel.stack] at *; omega)⟩
lemma par {p : ι → ℕ} (ha : c.ReelComputes A) (hb : c.ReelComputes B) (e : ∀ i, (A i).beats = (B i).beats) (hp : c.PolyWord p) :
    c.ReelComputes fun i => Reel.parallel (p i) (A i) (B i) :=
  ⟨ha.1, fun _ _ _ _ _ hf ht hj hb' => have hp := draw hf hp; have a := ha.2 _ _ _ _ _ hf ht hj hb'
    have b := hb.2 _ _ _ _ _ hf ht (hj.sub hp) fun k => e _ ▸ hb' k; have h := Decides.lt hj hp
    ⟨iteN h a.1 (hp.add b.1), Computes.ite h a.2.1 b.2.1, iteN h a.2.2 (hp.add b.2.2)⟩⟩
lemma ite {P : ι → Prop} [DecidablePred P] (h : c.Decides P) (ha : (c.onlyWhere P).ReelComputes fun k => A k.1)
    (hb : (c.onlyWhere fun k => ¬P k).ReelComputes fun k => B k.1) : c.ReelComputes fun i => if P i then A i else B i :=
  ⟨(branchN (x := fun i => (A i).beats) (y := fun i => (B i).beats) h ha.1 hb.1).congr fun k => by by_cases p : P k <;> simp [p],
   fun _ _ f t j hf ht hj hb' => (StrokeAt.ite (S := fun k => (A (f k)).atBeat (t k)) (S' := fun k => (B (f k)).atBeat (t k)) (h.on hf)
      (ha.2 _ _ (fun k : {k // P (f k)} => ⟨f k.1, k.2⟩) _ _ (PolyReads.into hf.res) (draw RS ht) (draw RS hj) fun k => by
        have := hb' k.1; simp only [k.2] at this; exact this)
      (hb.2 _ _ (fun k : {k // ¬P (f k)} => ⟨f k.1, k.2⟩) _ _ (PolyReads.into hf.res) (draw RS ht) (draw RS hj) fun k => by
        have := hb' k.1; simp only [k.2] at this; exact this)).congr fun k => by by_cases p : P (f k) <;> simp [p]⟩
lemma sel {P : ι → Prop} [DecidablePred P] (h : c.Decides P) (ha : c.ReelComputes A) (hb : c.ReelComputes B) : c.ReelComputes fun i => if P i then A i else B i :=
  ite h (ha.on RS) (hb.on RS)
lemma concatReels {A : ι → ℕ → Reel} {L B : ι → ℕ} (hL : c.PolyWord L) (hB : c.PolyWord B) (hb : ∀ i s, s < L i → (A i s).beats = B i)
    (h : (c.scan L).ReelComputes fun d => A d.i d.j) : c.ReelComputes fun i => ReelKit.concatReels (A i) (L i) :=
  have e := fun i => beats_concatReels (a := A i) _ _ fun s hs => hb i s hs
  ⟨(hL.mul hB).congr fun i => (e i).symm, fun _ d f t j hf ht hj hb' => have hB' := draw hf hB
    have q := fun k => show t k / B (f k) < L (f k) from Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm, ← e]; exact hb' k)
    (h.2 _ d (fun k => ⟨f k, _, q k⟩) (fun k => t k % B (f k)) j (hf.select (ht.div hB').1) (ht.residue hB') hj fun k => by
      rw [hb _ _ (q k)]; exact Nat.mod_lt _ (Nat.pos_of_ne_zero fun z => by have := e (f k) ▸ hb' k; simp [z] at this)).congr
      fun k => (concatReels_at _ _ _ _ (fun s hs => hb _ s hs) (e _ ▸ hb' k)).symm⟩
lemma tripleConcat {A : ι → ℕ → ℕ → ℕ → Reel} {L B : ι → ℕ} (hL : c.PolyWord L) (hB : c.PolyWord B)
    (hb : ∀ i s c j, s < L i → c < L i → j < L i → (A i s c j).beats = B i)
    (h : (scan3 c L).PolyReads c (fun e => e.i.i.i) → (scan3 c L).PolyWord (fun e => e.i.i.j) → (scan3 c L).PolyWord (fun e => e.i.j) →
      (scan3 c L).PolyWord During.j → (scan3 c L).ReelComputes fun e => A e.i.i.i e.i.i.j e.i.j e.j) :
    c.ReelComputes fun i => tripleConcat (A i) (L i) :=
  have F := PolyReads.scan c L; have L1 := draw F hL; have B1 := draw F hB; have G := PolyReads.scan (c.scan L) fun e => L e.i
  have H := PolyReads.scan ((c.scan L).scan fun e => L e.i) fun e => L e.i.i
  concatReels hL (hL.mul (hL.mul hB)) (fun i s hs => beats_concatReels _ _ fun c hc => beats_concatReels _ _ fun j hj => hb i s c j hs hc hj)
    (concatReels L1 (L1.mul B1) (fun (e : During L) c hc => beats_concatReels _ _ fun j hj => hb _ _ c j e.hj hc hj) (concatReels (draw G L1) (draw G B1)
      (fun (e : During fun e : During L => L e.i) j hj => hb _ _ _ j e.i.hj e.hj hj) (h (H.next (G.next F)) (draw (H.next G) (scanIndex hL)) (draw H (scanIndex L1)) (scanIndex (draw G L1)))))
lemma plain {N : ι → ℕ} {L : ι → ℕ → ℕ} {D : ι → Line} (hN : c.PolyWord N)
    (hL : ∀ (ν : Type U) (d : Bench m ν) (f : ν → ι) (j : ν → ℕ), d.PolyReads c f → d.PolyWord j → d.PolyWord fun k => L (f k) (j k))
    (hD : c.LineComputes D) : c.ReelComputes fun i => Reel.tick (Stroke.plain (N i) (L i) (D i)) :=
  ⟨.wc 1, fun _ _ _ _ _ hf _ hj _ => have h := Decides.lt hj (draw hf hN); ⟨iteN h (hL _ _ _ _ hf hj) hj, Computes.ite h (hD _ _ _ _ hf hj) PolyCan.one, hj⟩⟩
lemma scaleReel {N : ι → ℕ} (hN : c.PolyWord N) (hD : c.LineComputes F) : c.ReelComputes fun i => Reel.scaleReel (N i) (F i) :=
  plain (L := fun _ => id) hN (fun _ _ _ _ _ hj => hj) hD
lemma scaleZones {U V : ι → Zone} (hU : c.ZoneWords U) (hV : c.ZoneWords V) (hF : c.LineComputes F) (hG : c.LineComputes G) : c.ReelComputes fun i => scaleZones (U i) (V i) (F i) (G i) :=
  ⟨.wc 1, fun _ _ _ _ _ hf _ hj _ => have hU := hU.on hf; have hV := hV.on hf
    ⟨hj, Computes.ite (hU.has hj) (hF _ _ _ _ hf (hj.sub hU.1)) (Computes.ite (hV.has hj) (hG _ _ _ _ hf (hj.sub hV.1)) PolyCan.one), hj⟩⟩
lemma mixZones {U V : ι → Zone} (hU : c.ZoneWords U) (hV : c.ZoneWords V) : c.ReelComputes fun i => mixZones (U i) (V i) :=
  ⟨.wc 1, fun _ _ _ _ _ hf _ hj _ => have hU := hU.on hf; have hV := hV.on hf
    ⟨hj, PolyCan.one, iteN (hU.has hj) (hV.1.add (hj.sub hU.1)) (iteN (hV.has hj) (hU.1.add (hj.sub hV.1)) hj)⟩⟩
lemma reelTape {N : ι → ℕ} (h : c.ReelComputes A) (hN : c.PolyWord N) : c.Computes reelTapeTy fun i => RAM.reelTape (N i) (A i) :=
  tab h.1 _ (tab (draw FS hN) _ (
    let I := h.2 _ _ (fun e : During (fun d : During (fun i => (A i).beats) => N d.i) => e.i.i) (fun e => e.i.j) During.j
      (PolyReads.next FS FS) (draw FS (scanIndex h.1)) (scanIndex (draw FS hN)) fun e => e.i.hj
    I.1.1.pair (I.2.1.pair I.2.2.1)))
theorem tree {N : ι → ℕ} (h : c.ReelComputes A) (hN : c.PolyWord N) :
    c.Computes reelBlocksTy fun i => reelBlocksT (N i) (A i) :=
  have G := PolyReads.next FS FS; have T := draw FS (scanIndex h.1)
  have I := h.2 _ _ (fun e : During (fun d : During (fun i => (A i).beats) => N d.i) => e.i.i) (fun e => e.i.j) During.j G T (scanIndex (draw FS hN)) fun e => e.i.hj
  tab h.1 _ (tab (draw FS hN) _ ((I.1.1.pair I.2.1).pair (blockCell_computes (S := fun e : During (fun d : During (fun i => (A i).beats) => N d.i) => (A e.i.i).atBeat e.i.j) (fun _ _ f _ hf hj _ =>
    (h.2 _ _ _ _ _ (hf.next G) (draw hf T) hj fun k => (f k).i.hj).2.2) (draw G hN).2 (scanIndex (draw FS hN)) fun e => e.hj)))
lemma of_reelTape {N : ι → ℕ} (hF : c.Computes reelTapeTy fun i => RAM.reelTape (N i) (A i)) (hb : c.PolyWord fun i => (A i).beats)
    (hN : c.PolyWord N) (hs : ∀ i, (A i).Sound (N i)) : c.ReelComputes A :=
  ⟨hb, fun _ d f t j hf ht hj hb' => have hN' := draw hf hN
    (StrokeAt.ite (Decides.lt hj hN') (have r := restricted d fun k => j k < N (f k)
      let E := ((pull (r.next hf) hF).pick _ (draw r ht).1 fun k => hb' k.1).pick _ (draw r hj).1 fun k => k.2
      ⟨⟨E.fst, (draw r hN').2.mono fun k => ((hs _ _ (hb' k.1)).bdix _ k.2).le⟩, E.snd.fst,
       ⟨E.snd.snd, (draw r hN').2.mono fun k => ((hs _ _ (hb' k.1)).bdp _ k.2).le⟩⟩)
      (have r := restricted d fun k => ¬ j k < N (f k); have s := fun k : {k // ¬ j k < N (f k)} => hs _ _ (hb' k.1)
       ⟨(draw r hj).congr fun k => ((s k).awayix _ (not_lt.1 k.2)).symm, PolyCan.one.congr fun k => ((s k).awayd _ (not_lt.1 k.2)).symm,
       (draw r hj).congr fun k => ((s k).awayp _ (not_lt.1 k.2)).symm⟩)).congr fun _ => ite_self _⟩
section
variable {U V : ι → Zone} (hU : c.ZoneWords U) (hV : c.ZoneWords V) (hI : c.HasIConst)
include hU hV hI
lemma butterflyReel : c.ReelComputes fun i => butterflyReel (U i) (V i) :=
  ((scaleZones hU hV LineComputes.one hI).stack (mixZones hU hV)).stack (scaleZones hU hV (LineComputes.one.sub hI) (LineComputes.one.add hI))
lemma brickReel : c.ReelComputes fun i => brickReel (U i) (V i) :=
  have q := fun (z : ℚ) (w : ℂ) (e : (z : ℂ) = w) => scaleZones (G := fun _ _ => 1) hU hV ((LineComputes.rat z).congr fun _ _ => e) LineComputes.one
  (((((butterflyReel hU hV hI).stack (q (-3) (-3) (by norm_num))).stack (butterflyReel hU hV hI)).stack (q 2 2 (by norm_num))).stack (butterflyReel hU hV hI))
lemma addMulReel (hF : c.LineComputes F) (nz : ∀ k i, F k i ≠ 0) : c.ReelComputes fun i => addMulReel (U i) (V i) (F i) :=
  (((scaleZones hU hV ((((LineComputes.rat (4/5)).mul hF).inv fun _ _ => mul_ne_zero (by norm_num) (nz _ _)).congr fun _ _ => by push_cast; ring_nf) LineComputes.one).stack
    (brickReel hU hV hI)).stack (scaleZones hU hV (((LineComputes.rat (-1/10)).mul hF).congr fun _ _ => by push_cast; ring) ((LineComputes.rat (-1/6)).congr fun _ _ => by push_cast; ring)))
lemma addScaledReel (hF : c.LineConj F) : c.ReelComputes fun i => addScaledReel (U i) (V i) (F i) :=
  have B : c.LineComputes fun k i => onePlusNormSq (F k) i := LineComputes.one.add (hF.1.mul hF.2)
  (addMulReel hU hV hI B fun k i => ReelKit.onePlusNormSq_ne (F k) i).stack (addMulReel hU hV hI (hF.1.sub B) fun k i => sub_onePlusNormSq_ne (F k) i)
lemma addScaledConst (t : ℚ) (x : ℂ) (e : (t : ℂ) = x) : c.ReelComputes fun i => ReelKit.addScaledReel (U i) (V i) fun _ => x := addScaledReel hU hV hI ((LineConj.rat t).congr fun _ _ => e)
end
lemma fftReel {D : ι → ℕ} {z : ι → ℂ} (hD : c.PolyWord D) (h2 : Small c.size fun i => 2^D i) (hz : c.Computes sc z)
    (hI : c.HasIConst) : c.ReelComputes fun i => fftReel (D i) (z i) := by
  let X : ι → ℕ → T reelTapeTy := fun i k => RAM.reelTape (2^k) (ReelKit.fftReel k (z i ^ 2^(D i - k)))
  have step : (c.climbs D reelTapeTy X).Computes reelTapeTy fun e => X e.i (e.j+1) := by
    have F := PolyReads.climbs c D X; have hk := climbIndex hD X
    have sm : ∀ {x : During D → ℕ}, (∀ e, x e ≤ D e.i) → Small (c.climbs D reelTapeTy X).size fun e => 2^x e :=
      fun h => (h2.reindex During.i).mono fun e => Nat.pow_le_pow_right two_pos (h e)
    have hp := hk.pow2 (sm fun e => e.hj.le)
    have P : (c.climbs D reelTapeTy X).ReelComputes fun e => ReelKit.fftReel e.j ((z e.i ^ 2^(D e.i - (e.j+1)))^2) :=
      (of_reelTape (PolyMoves.token ..) (((WordIn.wc 5).mul hk).congr fun _ => (beats_fftReel _ _).symm) hp fun _ => sound_fftReel _ _).congr fun e => by
        rw [← pow_mul, ← pow_succ, show D e.i - (e.j+1) + 1 = D e.i - e.j by have := e.hj; omega]
    have w := (LineComputes.pow (pull F hz)).at_ (((draw F hD).sub (hk.add (.wc 1))).pow2 (sm fun e => by omega))
    have hI := hI.on F
    have Zi : ZoneWords _ fun e : During D => lowHalf (2^e.j) := ⟨.wc 0, hp⟩
    have Ze : ZoneWords _ fun e : During D => highHalf (2^e.j) := ⟨hp, hp⟩
    refine reelTape ((((plain (hp.add hp) (fun _ _ _ _ _ hj => iteN (Decides.lt hj (draw ‹_› hp)) ((WordIn.wc 2).mul hj)
      (((WordIn.wc 2).mul (hj.sub (draw ‹_› hp))).add (.wc 1))) LineComputes.one).stack (P.par P (fun _ => rfl) hp)).stack
      ((scaleZones Zi Ze LineComputes.one (LineComputes.pow w)).stack (butterflyReel Zi Ze hI))) : ReelComputes _ fun e => _)
      ((hp.add hp).congr fun _ => (two_mul _).symm.trans (pow_succ' _ _).symm)
  exact of_reelTape ((loop hD X (reelTape (wait (D := fun _ => 0) (.wc 0)) (.wc 1)) step).congr fun i => by simp [X])
    (((WordIn.wc 5).mul hD).congr fun _ => (beats_fftReel _ _).symm) (hD.pow2 h2) fun _ => sound_fftReel _ _
section
variable {D : ι → ℕ} {z : ι → ℂ} (hR : c.RootData D z) (hI : c.HasIConst) {U V A B : ι → Zone}
  (hU : c.ZoneWords U) (hV : c.ZoneWords V) (hA : c.ZoneWords A) (hB : c.ZoneWords B)
include hR hI
include hU hV in
lemma cyclicConvReel (hH : c.LineConj F) : c.ReelComputes fun i => cyclicConvReel (D i) (z i) (U i) (V i) (F i) :=
  have p := fftReel hR.1 hR.2.1.2 hR.2.2.1 hI
  have b : ReelComputes _ fun i => inverseFftReel (D i) (z i) := (fftReel hR.1 hR.2.1.2 (hR.2.2.1.inv hR.2.2.2.2) hI).stack
    (scaleReel hR.2.1 (LineComputes.const ((Computes.cast hR.2.1).inv fun _ => Nat.cast_ne_zero.2 (by positivity))))
  (((((wait p.1).par p (fun _ => rfl) hU.1).stack ((wait p.1).par p (fun _ => rfl) hV.1)).stack (addScaledReel hV hU hI (LineConj.freq hR.2.1 hR.2.2.1 hR.2.2.2.1 hH))).stack
    ((wait b.1).par b (fun _ => rfl) hU.1)).stack ((wait b.1).par b (fun _ => rfl) hV.1)
include hU hA hB in
lemma paddedConvReel (hH : c.LineConj F) : c.ReelComputes fun i => paddedConvReel (D i) (z i) (U i) (A i) (B i) (F i) :=
  have S : c.ZoneWords fun i => (A i).slim (U i).wide := ⟨hA.1, hU.2⟩
  (((addScaledConst S hU hI 1 1 Rat.cast_one).stack (cyclicConvReel hR hI hA hB hH)).stack (addScaledConst S hU hI (-1) (-1) (by push_cast; rfl))).stack (cyclicConvReel hR hI hA hB hH.neg)
include hU hV hA hB in
lemma blockConvReel (hH : c.LineConj F) : c.ReelComputes fun i => blockConvReel (D i) (z i) (U i) (V i) (A i) (B i) (F i) :=
  have S : c.ZoneWords fun i => (B i).slim (V i).wide := ⟨hB.1, hV.2⟩
  (((paddedConvReel hR hI hU hA hB hH).stack (addScaledConst hV S hI 1 1 Rat.cast_one)).stack (paddedConvReel hR hI hU hA hB hH.neg)).stack (addScaledConst hV S hI (-1) (-1) (by push_cast; rfl))
end
lemma toeplitzGridCell {K Wd S C J : ι → ℕ} {z : ι → ℂ} (hR : c.RootData (fun i => K i + 1) z) (hI : c.HasIConst)
    (hW : c.PolyWord Wd) (hS : c.PolyWord S) (hC : c.PolyWord C) (hJ : c.PolyWord J) (hH : c.LineConj F) (hG : c.LineConj G) :
    c.ReelComputes fun i => toeplitzGridCell (K i) (z i) (Wd i) (F i) (G i) (S i) (C i) (J i) := by
  have b : c.PolyWord fun i => 2^K i := (hR.2.1.div (.wc 2)).congr fun _ => by rw [pow_succ, Nat.mul_div_cancel _ two_pos]
  have p := ((WordIn.wc 16).mul b).add (hS.mul b)
  have fr : c.PolyWord fun i => scratchBase (2^K i) (J i) := iteN (Decides.lt hJ (.wc 8)) ((WordIn.wc 8).mul b) (.wc 0)
  have b2 := (WordIn.wc 2).mul b
  have Q : c.ZoneWords fun i => blockZone (2^K i) (J i) := ⟨hJ.mul b, b⟩
  have Je : c.ZoneWords fun i => outZone (16*2^K i) (Wd i) (2^K i) (S i) := ⟨p, b.minimum (hW.sub (hS.mul b))⟩
  have Tr : c.ZoneWords fun i => scratchZone (2^K i) (J i) := ⟨fr, b⟩
  have Ba : c.ZoneWords fun i => convZoneA (2^K i) (J i) := ⟨fr.add b, b2⟩
  have Lo : c.ZoneWords fun i => convZoneB (2^K i) (J i) := ⟨fr.add ((WordIn.wc 3).mul b), b2⟩
  have bo := fun {U V : ι → Zone} {L M : ι → ℕ} {H : ι → Line} (hU : c.ZoneWords U) (hV : c.ZoneWords V) (hL : c.PolyWord L) (hM : c.PolyWord M)
    (hH : c.LineConj H) => blockConvReel hR hI hU hV Ba Lo (hH.blockFilter b hU.2 hV.2 hL hM)
  unfold ReelKit.toeplitzGridCell ReelKit.toeplitzPairReel ReelKit.toeplitzBlockReel
  exact (((bo Q Tr (hJ.mul b) (hC.mul b) hG).stack (bo Tr Je (hC.mul b) p hH)).stack (bo Q Tr (hJ.mul b) (hC.mul b) hG.neg)).stack
    (bo Tr Je (hC.mul b) p hH.neg)
lemma naiveToeplitzCell {P Wd S C J : ι → ℕ} (hP : c.PolyWord P) (hW : c.PolyWord Wd) (hS : c.PolyWord S) (hC : c.PolyWord C)
    (hJ : c.PolyWord J) (hH : c.LineConj F) (hG : c.LineConj G) (hI : c.HasIConst) :
    c.ReelComputes fun i => naiveToeplitzCell (P i) (Wd i) (F i) (G i) (S i) (C i) (J i) :=
  sel (Decides.lt hS hW) (addScaledReel (U := fun i => outZone (P i) (Wd i) 1 (S i)) (V := fun i => blockZone 1 (J i))
    ⟨hP.add (hS.mul (.wc 1)), (WordIn.wc 1).minimum (hW.sub (hS.mul (.wc 1)))⟩ ⟨hJ.mul (.wc 1), .wc 1⟩ hI
    ⟨LineComputes.const ((hH.1.rise (hP.add hS) hC).mul (hG.1.rise hC hJ)), LineComputes.const (((hH.2.rise (hP.add hS) hC).mul (hG.2.rise hC hJ)).congr
      fun _ => by simp only [Spectral.rise, map_mul, apply_ite (starRingEnd ℂ), map_zero])⟩) (wait (.wc 26))
lemma toeplitzGridReel {K Wd : ι → ℕ} {z : ι → ℂ} (hR : c.RootData (fun i => K i + 1) z) (hW : c.PolyWord Wd) (hH : c.LineConj F)
    (hG : c.LineConj G) (hI : c.HasIConst) : c.ReelComputes fun i => toeplitzGridReel (K i) (z i) (Wd i) (F i) (G i) :=
  tripleConcat (.wc 16) ((WordIn.wc 4).mul (((WordIn.wc 80).mul (hR.1.sub (.wc 1))).add (.wc 348)) |>.congr fun _ => by simp)
    (fun _ _ _ _ _ _ _ => beats_toeplitzGridCell ..) fun T hs hc hj => toeplitzGridCell (hR.on T) (hI.on T) (draw T hW) hs hc hj (hH.on T) (hG.on T)
lemma bridge {E Wd : ι → ℕ} {R : ι → Line} (hE : c.PolyWord E) (h2 : c.PolyWord fun i => 2^E i) (hW : c.PolyWord Wd)
    (hH : c.LineConj F) (hG : c.LineConj G) (hR : (c.onlyWhere fun i => ¬ E i < 4).RootData (fun k => E k.1 - 4 + 1) (fun k => R k.1 (E k.1 - 4 + 1)))
    (hI : c.HasIConst) : c.ReelComputes fun i => toeplitzBridge (E i) (Wd i) (F i) (G i) (R i) :=
  ite (Decides.lt hE (.wc 4)) ((tripleConcat (A := fun i => ReelKit.naiveToeplitzCell (2^E i) (Wd i) (F i) (G i)) h2 (.wc 26)
    (fun _ _ _ _ _ _ _ => beats_naiveToeplitzCell ..) fun T hs hc hj => naiveToeplitzCell (draw T h2) (draw T hW) hs hc hj (hH.on T) (hG.on T) (hI.on T)).on
      (restricted c _)) (toeplitzGridReel hR (draw (restricted c _) hW) (hH.on (restricted c _)) (hG.on (restricted c _)) (hI.on (restricted c _)))
lemma toeplitzStep {K Wd : ι → ℕ} {R : ι → Line} (ha : c.ReelComputes A) (hb : c.ReelComputes B) (e : ∀ i, (A i).beats = (B i).beats)
    (hK : c.PolyWord K) (h2 : c.PolyWord fun i => 2^K i) (hW : c.PolyWord Wd)
    (hBr : (c.onlyWhere fun i => 2^K i < Wd i).ReelComputes fun k => toeplitzBridge (K k.1) (Wd k.1 - 2^K k.1) (F k.1) (G k.1) (R k.1)) :
    c.ReelComputes fun i => toeplitzStep (K i) (Wd i) (F i) (G i) (R i) (A i) (B i) :=
  (ha.par hb e (h2.minimum hW)).stack (ite (Decides.lt h2 hW) hBr ((wait (bridgeBeats_word hK)).on (restricted c _)))
lemma toeplitzReel {E N : ι → ℕ} {R : ι → Line} (hE : c.PolyWord E) (h2 : c.PolyWord fun i => 2^E i) (hN : c.PolyWord N)
    (hNE : ∀ i, N i ≤ 2^E i) (hH : c.LineConj F) (hG : c.LineConj G)
    (hR : (c.scan E).RootData (fun e => e.j - 4 + 1) (fun e => R e.i (e.j - 4 + 1))) (hI : c.HasIConst) :
    c.ReelComputes fun i => ReelKit.toeplitzReel (F i) (G i) (R i) (E i) (N i) := by
  let Y : ι → ℕ → ℕ → T reelTapeTy := fun i k w => RAM.reelTape w (ReelKit.toeplitzReel (F i) (G i) (R i) k w)
  let X : ι → ℕ → T (p reelTapeTy (p reelTapeTy reelTapeTy)) := fun i k => (Y i k (2^k), Y i k (N i % 2^k), Y i k 0)
  have sw := fun {W : ι → ℕ} (hW : c.PolyWord W) => reelTape (scaleReel (F := fun i _ => F i 0) hW (LineComputes.const (hH.1.at_ (.wc 0)))) hW
  have step : (c.climbs E _ X).Computes _ fun e => X e.i (e.j+1) := by
    have Fc := PolyReads.climbs c E X; have hk := climbIndex hE X; have hN := draw Fc hN; have St := PolyMoves.token c E c.size X
    have hp := hk.pow2 ((h2.2.reindex During.i).mono fun e => Nat.pow_le_pow_right two_pos e.hj.le)
    have hp2 : PolyWord _ fun e : During E => 2^(e.j+1) := (hp.add hp).congr fun _ => by rw [pow_succ]; ring
    have O := fun {w : During E → ℕ} (h : Computes _ _ fun e => RAM.reelTape (w e) (ReelKit.toeplitzReel (F e.i) (G e.i) (R e.i) e.j (w e)))
      (hw : PolyWord _ w) (b : ∀ e, w e ≤ 2^e.j) => of_reelTape h ((toeplitzBeats_word hk).congr fun e => (beats_toeplitzReel ..).symm) hw fun e => sound_toeplitzReel _ _ _ _ _ (b e)
    have Pf := O St.fst hp fun _ => le_rfl
    have Pm := O St.snd.fst (hN.residue hp) fun _ => (Nat.mod_lt _ (by positivity)).le
    have Pz := O St.snd.snd (.wc 0) fun _ => Nat.zero_le _
    have hR := hR.on ((PolyReads.climbs c E X).select hk.1 : PolyReads _ (c.scan E) id)
    have Hp := fun {W : During E → ℕ} {A B : During E → Reel} (ha : ReelComputes _ A) (hb : ReelComputes _ B) (e : ∀ i, (A i).beats = (B i).beats)
      (hW : PolyWord _ W) => toeplitzStep (F := fun e : During E => F e.i) (G := fun e => G e.i) (R := fun e => R e.i) (K := During.j) ha hb e hk hp hW
        (have r := restricted (c.climbs E _ X) fun e => 2^e.j < W e
        bridge (R := fun e : {e : During E // 2^e.j < W e} => R e.1.i) (draw r hk) (draw r hp) ((draw r hW).sub (draw r hp))
          (hH.on (r.next Fc)) (hG.on (r.next Fc)) (hR.on ((restricted _ _).next r)) (hI.on (r.next Fc)))
    have be := fun (e : During E) (a b : ℕ) => (beats_toeplitzReel (F e.i) (G e.i) (R e.i) e.j a).trans (beats_toeplitzReel (F e.i) (G e.i) (R e.i) e.j b).symm
    have ht := Decides.lt (hN.residue hp2) hp
    exact (reelTape ((Hp Pf Pf (fun e => be e _ _) hp2).congr fun e => by
      rw [toeplitzReel_succ, min_eq_left (Nat.pow_le_pow_right two_pos (Nat.le_succ _)), pow_succ, mul_two, Nat.add_sub_cancel]) hp2).pair
      ((reelTape ((Hp (sel ht Pm Pf) (sel ht Pz Pm) (fun e => by split_ifs <;> simp only [beats_toeplitzReel]) (hN.residue hp2)).congr fun e => by
      rw [toeplitzReel_succ]; have := mod_two (N e.i) e.j
      by_cases hc : N e.i % 2^(e.j+1) < 2^e.j
      · rw [if_pos hc] at this
        rw [if_pos hc, if_pos hc, min_eq_right hc.le, Nat.sub_eq_zero_of_le hc.le, ← this]
      · rw [if_neg hc] at this
        rw [if_neg hc, if_neg hc, min_eq_left (not_lt.1 hc), this, Nat.add_sub_cancel]) (hN.residue hp2)).pair
      (reelTape ((Hp Pz Pz (fun e => be e _ _) (.wc 0)).congr fun e => by rw [toeplitzReel_succ, Nat.min_zero, Nat.zero_sub]) (.wc 0)))
  have L := loop hE X ((sw (.wc 1)).pair ((sw (hN.residue (.wc 1))).pair (sw (.wc 0)))) step
  exact of_reelTape ((Computes.ite (Decides.eq hN h2) L.fst L.snd.fst).congr fun i => by
      dsimp only [X, Y]; split_ifs with x; rw [x]; rw [Nat.mod_eq_of_lt (lt_of_le_of_ne (hNE i) x)])
    ((toeplitzBeats_word hE).congr fun i => (beats_toeplitzReel ..).symm) hN fun i => sound_toeplitzReel _ _ _ _ _ (hNE i)
lemma vandermondeReel {N E : ι → ℕ} {u : ι → ℂ} {R : ι → Line} (hN : c.PolyWord N) (hE : c.PolyWord E) (h2 : c.PolyWord fun i => 2^E i)
    (hNE : ∀ i, N i ≤ 2^E i) (hn : ∀ i, 0 < N i) (hu : ∀ i, Spectral.PrimRoot (u i) (N i)) (hU : c.ConjComputes u)
    (hR : (c.scan E).RootData (fun e => e.j - 4 + 1) (fun e => R e.i (e.j - 4 + 1))) (hI : c.HasIConst) :
    c.ReelComputes fun i => vandermondeReel (N i) (E i) (u i) (R i) := by
  have z : ∀ {v : ι → ℂ}, (∀ i, Spectral.PrimRoot (v i) (N i)) → ∀ k i, gap (v k) i = 0 ↔ N k ≤ i :=
    fun hv k i => ⟨fun h => not_lt.1 fun l => gap_ne_zero _ (hv k) _ l h, gap_zero (hv k) (hn k)⟩
  have hF : c.LineConj fun i => floorH (u i) := ⟨(LineComputes.gap hU.1).invZ hN (z hu), ((LineComputes.gap hU.2).invZ hN (z fun i => by
    rw [Spectral.conj_of_root (hn i) (hu i).pow_eq_one]; exact (hu i).inv)).congr fun _ _ => by simp only [gap, floorH, map_inv₀, map_prod, map_sub, map_one, map_pow]⟩
  have P := toeplitzReel hE h2 hN hNE hF ⟨hF.1.toeplitzInv fun _ => by simp only [floorH, gap, range_zero, prod_empty, inv_one, ne_eq, one_ne_zero, not_false_eq_true], (hF.2.toeplitzInv fun _ => by
    simp only [floorH, gap, range_zero, prod_empty, inv_one, map_one, ne_eq, one_ne_zero,
      not_false_eq_true]).congr fun _ _ => (conj_toeplitzInv _ _).symm⟩ hR hI
  have Ec : c.ReelComputes fun i => reverseReel (N i) := plain hN (fun _ _ _ _ hf hj => ((draw hf hN).sub (.wc 1)).sub hj) LineComputes.one
  exact ((((scaleReel hN (LineComputes.gap hU.1)).stack ((Ec.stack P).stack Ec)).stack (scaleReel hN (LineComputes.roof hU.1))).stack
    (scaleReel hN (((LineComputes.gap hU.1).mul (LineComputes.roof hU.1)).invZ hN fun k i => by
      rw [mul_eq_zero, z hu, or_iff_left (by unfold Spectral.roof; exact prod_ne_zero_iff.2 fun j _ => neg_ne_zero.2 (pow_ne_zero _ ((hu k).ne_zero (hn k).ne')))]))).stack
    (((scaleReel hN (LineComputes.roof hU.1)).stack P).stack (scaleReel hN (LineComputes.gap hU.1)))
end ReelComputes
end
open Complex Finset Spectral in
theorem vandermondeReel_blocks {n d : ι→ℕ} {u : ι→ℂ} {r : ι→Line}
    (hd : b.ExpWords d) (hh : b.PolyWord n) (hn : ∀ i,0<n i) (hv : ∀ i,n i ≤ 2^d i)
    (hr : b.LineConjComputes (fun i => d i+1) r) (hy : ∀ i, Springs (d i) (r i))
    (h : b.ConjComputes u) (hu : ∀ i, Spectral.PrimRoot (u i) (n i))
    (hI : b.ConjComputes fun _ => I) :
    b.Computes reelBlocksTy fun i => reelBlocksT (n i) (vandermondeReel (n i) (d i) (u i) (r i)) :=
  have J : (b.scan d).PolyWord fun e => e.j - 4 + 1 := ((scanIndex hd.1).sub (.wc 4)).add (.wc 1)
  have F := (PolyReads.scan b d).select (n := fun i => d i + 1) (f := fun e : During d => ⟨e.i, e.j - 4 + 1, by have := e.hj; omega⟩) J.1
  have H := ConjComputes.transfer (f := fun g : During fun i => d i + 1 => r g.i g.j) hr F
  have P := ReelComputes.vandermondeReel hh hd.1 hd.2 hv hn hu h ⟨J, J.pow2 ((hd.2.2.reindex During.i).mono fun e => Nat.pow_le_pow_right two_pos
      (by have := e.hj; omega)), H.1, H.2, fun e => ((hy _ _ (by have := e.hj; omega)).ne_zero (by positivity))⟩
    (LineComputes.const hI.1)
  P.tree hh
end Bench
end
end PowerSaving.RAM
namespace PowerSaving.AxisTensor
open ReelKit PowBlock PairBlocks Binary Finset Matrix
noncomputable section
def rippleEntry (i j : ℕ) : ℂ := if i=j then ca else cb
def blockRippleMat : ℕ → IdxMat
  | 0 => fun _ _ => 1
  | k+1 => fun i j => blockRippleMat k (i/2) (j/2) * rippleEntry (i%2) (j%2)
def blockRipple (k : ℕ) (x : Line) : Line := idxApply (2^k) (blockRippleMat k) x
lemma blockRippleMat_prod (k a b : ℕ) :
    blockRippleMat k a b = ∏ t ∈ range k, rippleEntry (a / 2^t % 2) (b / 2^t % 2) := by
  induction k generalizing a b with
  | zero => rfl
  | succ k ih => simp only [blockRippleMat, ih, Nat.div_div_eq_div_mul, mul_comm, prod_range_succ', pow_succ', pow_zero,
    Nat.div_one]
lemma blockRippleMat_mul (a b x x' y y' : ℕ) (hy : y < 2^b) (hy' : y' < 2^b) :
    blockRippleMat (a+b) (x*2^b+y) (x'*2^b+y') = blockRippleMat a x x' * blockRippleMat b y y' := by
  induction b generalizing y y' with
  | zero => simp_all [blockRippleMat]
  | succ b ih =>
    have p : 2^(b+1) = 2^b*2 := pow_succ ..
    have e : ∀ z w, (z*2^(b+1)+w)/2 = z*2^b+w/2 ∧ (z*2^(b+1)+w)%2 = w%2 := fun z w => by
      rw [p, ← mul_assoc, show z*2^b*2+w = w+2*(z*2^b) by ring, Nat.add_mul_div_left _ _ two_pos,
        Nat.add_mul_mod_self_left]; exact ⟨Nat.add_comm _ _, rfl⟩
    show blockRippleMat (a+b) _ _ * _ = _
    rw [(e _ _).1, (e _ _).1, (e _ _).2, (e _ _).2,
      ih _ _ (Nat.div_lt_of_lt_mul (by rw [← pow_succ']; exact hy))
        (Nat.div_lt_of_lt_mul (by rw [← pow_succ']; exact hy')), mul_assoc]; rfl
lemma blockRipple_loc (k : ℕ) (v : Line) (x : Bits k) :
    blockRipple k v ((bits k).loc x) = ripple k (fun j => v ((bits k).loc j)) x := by
  have e : ∀ g : ℕ → ℂ, ∑ m ∈ range (2^k), g m = ∑ y, g ((bits k).loc y) := fun g => by
    rw [← Fin.sum_univ_eq_sum_range, ← (bits k).index.symm.sum_comp]
    exact sum_congr rfl fun i _ => congrArg g (Layout.loc_atFin (bits k) i).symm
  simp only [blockRipple, idxApply, ripple, mulVec, dotProduct, rippleMat, e, digitProd_apply, blockRippleMat_prod]
  refine sum_congr rfl fun y _ => congrArg (· * _) ?_
  rw [← Fin.prod_univ_eq_prod_range]
  refine prod_congr rfl fun t _ => ?_
  simp only [bits_div k _ t, littleC, rippleEntry, (ZMod.val_injective 2).eq_iff]
def blockKernel (f g : PowBlock) : ℂ := if f.start=g.start then blockRippleMat f.height f.seat g.seat else 0
def permLine (n : ℕ) (f : ℕ → PowBlock) (x : Line) : Line := fun j => x (seek n (fun i => (f i).addr) j)
def lineFrom (n : ℕ) (f : ℕ → PowBlock) (x : Line) (s : ℕ) : Line := fun j => permLine n f x (s+j)
def blockAtRipple (n : ℕ) (f : ℕ → PowBlock) (x : Line) (j : ℕ) : Line :=
  blockRipple (blockAt n f j).height (lineFrom n f x j)
lemma leafC_hem {n : ℕ} {u : Stroke} (h : u.Sound n) {a k : ℕ} (ha : a<n) (hk : k<n) :
    leafC u a k = blockKernel (block u a) (block u k) := by
  have q : ∀ i, pairSeat u i < 2 := fun i => by unfold pairSeat; split_ifs <;> omega
  have p1 : ∀ s s', s < 2 → s' < 2 → blockRippleMat 1 s s' = if s = s' then ca else cb := fun s s' hs hs' => by
    simp [blockRippleMat, rippleEntry, Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hs']
  unfold blockKernel
  by_cases g : pairLead u a = pairLead u k
  · rw [if_pos (by simp only [block, g] : _ = _)]
    simp only [block, up, leafC, idxOne]
    obtain e|e := pairLead_class h g <;> subst e
    · by_cases e : u.partner k = k <;> simp [e, eq_comm (a := k), p1 _ _ (q _) (q _)]; rfl
    · have := h.pair a; by_cases e : u.partner a = a
      · simp [e]; rfl
      · simp [e, eq_comm (a := a), p1 _ _ (q _) (q _)]; exact fun x => (pairSeat_partner_ne h e x.symm).elim
  · rw [if_neg fun e => g (pairLead_of_start h ha hk e)]
    have : k ≠ a ∧ k ≠ u.partner a := ⟨fun e => g (e ▸ rfl), fun e => g (e ▸ pairLead_partner h).symm⟩
    simp [leafC, idxOne, this]
lemma blockKernel_blockMul {R n i j : ℕ} {s s' t t' : PowBlock} (ha : s.Mark n i) (ha' : s'.Mark n i)
    (hs : s.fits s') (hg : t.Mark R j) (hg' : t'.Mark R j) (ht : t.fits t') :
    blockKernel (blockMul R s t) (blockMul R s' t') = blockKernel s s' * blockKernel t t' := by
  have sm : ∀ {a b : PowBlock}, a.fits b → 0 < a.width → 0 < b.width → a.start = b.start → a.same b :=
    fun f p q e => by rcases f with f|f|f; exact f; all_goals (unfold blockEnd at f; omega)
  have p := Nat.mul_pos ha.positive hg.positive; have p' := Nat.mul_pos ha'.positive hg'.positive
  unfold blockKernel
  by_cases H : (blockMul R s t).start = (blockMul R s' t').start
  · obtain ⟨⟨a1, -, a3⟩, ⟨b1, b2, b3⟩⟩ := blockMul_unique R j hg hg' ha ha' hs ht
      (by unfold blockEnd; simp only [blockMul] at *; omega) (by unfold blockEnd; simp only [blockMul] at *; omega)
    rw [if_pos H, if_pos a1, if_pos b1]; simp only [blockMul]
    rw [← b2, hg.size, blockRippleMat_mul _ _ _ _ _ _ (hg.size ▸ hg.place) (b3 ▸ hg'.size ▸ hg'.place)]
  · rw [if_neg H]; split_ifs with a b <;> simp
    refine (H ?_).elim; exact (by simp only [blockMul]; rw [a, b, (sm hs ha.positive ha'.positive a).2.1])
lemma axisKron_leafC (r : Axes) (u : ℕ → Stroke) (l : ℕ) (h : Splits r l) (g : ∀ i<l, (u i).Sound (r i))
    (i : ℕ) (hi : i<extent r l) (k : ℕ) (hk : k<extent r l) :
    axisKron r (fun t => leafC (u t)) l i k = blockKernel (strokeBlocks r u l i) (strokeBlocks r u l k) := by
  induction l generalizing i k with
  | zero => simp [axisKron, strokeBlocks, blockKernel]; rfl
  | succ l ih =>
    have c := h.cut l.le_succ; have g' := fun i (hi : i < l) => g i (by omega)
    have Q := strokeBlocks_cover r l u c g'; have W := pairBlocks_cover (g l l.lt_succ_self)
    have := h.div_lt hi; have := h.div_lt hk; have := h.mod_lt i; have := h.mod_lt k
    show axisKron r _ l (i / r l) (k / r l) * leafC (u l) (i % r l) (k % r l) = blockKernel (blockMul _ _ _) (blockMul _ _ _)
    rw [ih c g' _ ‹_› _ ‹_›, leafC_hem (g l l.lt_succ_self) ‹_› ‹_›,
      blockKernel_blockMul (Q.mark _ ‹_›) (Q.mark _ ‹_›) (Q.seam _ ‹_› _ ‹_›) (W.mark _ ‹_›) (W.mark _ ‹_›) (W.seam _ ‹_› _ ‹_›)]
lemma idxApply_eq_blockAtRipple (r : Axes) (l : ℕ) (u : ℕ→Stroke)
    (h : Splits r l) (g : ∀ i<l, (u i).Sound (r i)) (x : Line)
    (i : ℕ) (hi : i<extent r l) :
    let f := strokeBlocks r u l
    idxApply (extent r l) (axisKron r (fun i => leafC (u i)) l) x i =
      blockAtRipple (extent r l) f x (f i).start (f i).seat := by
  intro f
  have Q : PowBlockCover _ l f := strokeBlocks_cover r l u h g
  have M := Q.mark i hi; have P := M.positive
  set N := extent r l; set S := (f i).start
  have A := Q.blockAt_align hi le_rfl (show S < (f i).blockEnd by unfold blockEnd; omega)
  have e1 : ∀ k ∈ range N, axisKron r (fun i => leafC (u i)) l i k * x k =
      (fun a => blockKernel (f i) (blockAt N f a) * x (seek N (fun i => (f i).addr) a)) (f k).addr := fun k hk => by
    simp only [blockAt, Q.reloc.seeks_at (mem_range.1 hk), axisKron_leafC r u l h g i hi k (mem_range.1 hk)]; rfl
  have e2 : ∀ a ∈ range N, a ∉ Ico S (S+(f i).width) → blockKernel (f i) (blockAt N f a) * x (seek N (fun i => (f i).addr) a) = 0 :=
    fun a ha hn => by
    have := Q.blockAt_addr (mem_range.1 ha); have := (Q.blockAt_mark (mem_range.1 ha)).place
    rw [blockKernel, if_neg, zero_mul]; intro e
    have := Q.matches_of_eq hi (Q.reloc.seeks (mem_range.1 ha)).1 e
    simp only [mem_Ico, same, blockAt, addr] at *; omega
  simp only [idxApply, blockAtRipple, blockRipple, lineFrom, permLine]
  rw [sum_congr rfl e1, Q.reloc.sum (fun a => blockKernel (f i) (blockAt N f a) * x (seek N (fun i => (f i).addr) a)), ← sum_subset (fun a ha => mem_range.2 (by
    have := M.endsBy; unfold blockEnd at this; simp at ha; omega)) e2, sum_Ico_eq_sum_range, Nat.add_sub_cancel_left,
    A.1.2.2, M.size]
  refine sum_congr rfl fun m hm => ?_
  have B := Q.blockAt_align hi (Nat.le_add_right S m) (by unfold blockEnd; simp at hm; rw [M.size]; omega)
  rw [blockKernel, if_pos B.1.1.symm, B.2, Nat.add_sub_cancel_left]
def headWidth (n : ℕ) (f : ℕ→PowBlock) (j : ℕ) :=
  if (blockAt n f j).seat=0 then (blockAt n f j).width else 0
lemma headWidth_sum (n l : ℕ) (f : ℕ → PowBlock) (h : PowBlockCover n l f) :
    ∑ j ∈ range n, headWidth n f j = n := by
  have st : ∀ a < n, (blockAt n f a).start < n ∧ (blockAt n f (blockAt n f a).start).seat = 0 := fun a ha => by
    have M := h.blockAt_mark ha; have := M.positive; have := M.endsBy; unfold blockEnd at this
    have A := h.blockAt_align (h.reloc.seeks ha).1 le_rfl (show (blockAt n f a).start < (blockAt n f a).blockEnd by unfold blockEnd; omega)
    exact ⟨by omega, A.2.trans (Nat.sub_self _)⟩
  conv_rhs => rw [← card_range n, card_eq_sum_card_fiberwise (f := fun a => (blockAt n f a).start) (t := range n)
    fun a ha => mem_range.2 (st a (mem_range.1 ha)).1]
  refine sum_congr rfl fun j hj => ?_
  rw [mem_range] at hj
  have M := h.blockAt_mark hj; have := h.blockAt_addr hj; have := M.place; have := M.endsBy; unfold blockEnd addr at *
  unfold headWidth; split_ifs with e
  · rw [show (blockAt n f j).width = (Ico j (j + (blockAt n f j).width)).card by simp]; congr 1; ext a
    simp only [mem_filter, mem_range, mem_Ico]; constructor
    · rintro ⟨h1, h2⟩
      have B := h.blockAt_align (h.reloc.seeks hj).1 (j := a) (by change (blockAt n f j).start ≤ a; omega)
        (by change a < (blockAt n f j).start + (blockAt n f j).width; omega)
      change (blockAt n f a).same (blockAt n f j) ∧ _ at B; unfold same at B; omega
    · rintro ⟨ha, e'⟩
      have B := h.matches_of_eq (h.reloc.seeks hj).1 (h.reloc.seeks ha).1 (by change (blockAt n f j).start = (blockAt n f a).start; omega)
      change (blockAt n f j).same (blockAt n f a) at B; unfold same at B
      have := h.blockAt_addr ha; have := (h.blockAt_mark ha).place; unfold addr at *; omega
  · symm; rw [card_eq_zero, filter_eq_empty_iff]; intro a ha e'
    exact e (e' ▸ (st a (mem_range.1 ha)).2)
end
end PowerSaving.AxisTensor
namespace PowerSaving.RAM.Bench
open Ty AxisTensor PowBlock ReelKit PairBlocks
universe U V
variable {m : Bool} {ι : Type U} {κ : Type V} {b : Bench m ι} {q : Bench m κ}
  {l : ι→ℕ} {r : ι→Axes} {u : ι→ℕ→Stroke} {n : ι→ℕ} {Y : ι→PowBlock}
structure StrokeBlocks (b : Bench m ι) (n : ι→ℕ) (s : ι→Stroke) : Prop where
  good : ∀ i, (s i).Sound (n i)
  tree : b.Moves (fun _ => 0) strokeBlocksTy fun i => strokeBlocksT (n i) (s i)
structure AxisStroke (b : Bench m ι) (l : ι→ℕ) (r : ι→Axes) (u : ι→ℕ→Stroke) : Prop where
  axisCtx : b.AxisCtx l r
  leaf : (b.scan l).StrokeBlocks (fun i => r i.i i.j) (fun i => u i.i i.j)
lemma AxisStroke.good (h : b.AxisStroke l r u) (i : ι) (j : ℕ) (hj : j<l i) : (u i j).Sound (r i j) := h.2.1 ⟨i, j, hj⟩
lemma AxisStroke.transfer {l : κ→ℕ} {r : κ→Axes} {u : κ→ℕ→Stroke} (h : q.AxisStroke l r u) {f}
    (g : b.FreeReads q f) :
    b.AxisStroke (fun i => l (f i)) (fun i => r (f i)) (fun i => u (f i)) :=
  ⟨h.1.transfer g, fun d => h.2.1 ⟨f d.i, d.j, d.hj⟩, h.2.2.transfer (AxisCtx.scanInstant g)⟩
structure BlockFields (b : Bench m ι) (Y : ι→PowBlock) : Prop where
  starts : b.FreeWord fun i => (Y i).start
  widths : b.FreeWord fun i => (Y i).width
  tall : b.FreeWord fun i => (Y i).height
  seat : b.FreeWord fun i => (Y i).seat
lemma BlockFields.blockCell_moves (h : b.BlockFields Y) : b.Moves (fun _ => 0) blockCellTy fun i => blockCell (Y i) := h.1.toMoves.pair (h.2.toMoves.pair (h.3.toMoves.pair h.4.toMoves))
lemma BlockFields.addr (h : b.BlockFields Y) : b.FreeWord fun i => (Y i).addr := h.1.add h.4
lemma BlockFields.of_blockCell {l : ι→ℕ} (h : Small b.size n) (hh : ∀ i,(Y i).Mark (n i) (l i))
    (hg : b.Moves (fun _ => 0) blockCellTy fun i => blockCell (Y i)) : b.BlockFields Y :=
  have M := fun i => hh i; have T := fun i => (Y i).height.lt_two_pow_self
  ⟨⟨hg.fst.toPoly _, h.mono fun i => by have := (M i).1; unfold blockEnd at this; omega⟩,
   ⟨hg.snd.fst.toPoly _, h.mono fun i => by have := (M i).1; unfold blockEnd at this; omega⟩,
   ⟨hg.snd.snd.fst.toPoly _, h.mono fun i => by have := (M i).1; have := (M i).2; have := T i; unfold blockEnd at *; omega⟩,
   ⟨hg.snd.snd.snd.toPoly _, h.mono fun i => by have := (M i).1; have := (M i).4; unfold blockEnd at *; omega⟩⟩
lemma survey_lt {r : Axes} {u : ℕ → Stroke} {L : ℕ} (h : Splits r L)
    (g : ∀ i<L, (u i).Sound (r i)) (j : ℕ) (hj : j ≤ L) (k : ℕ) (hk : k<extent r j) :
    (survey r u j k).1 < extent r j := by
  induction j generalizing k with
  | zero => show 0 < 1; omega
  | succ j ih =>
    have c := h.cut hj
    exact c.join_lt (ih (by omega) _ (c.div_lt hk)) ((g j hj).bdix _ (c.mod_lt k))
lemma axisKron_leafM (r : Axes) (u : ℕ → Stroke) {L : ℕ} (h : Splits r L) (g : ∀ i<L, (u i).Sound (r i))
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
      rw [if_neg e]; split_ifs with a b
      · exact absurd (by rw [← this, a, b, Nat.mul_comm]) e
      all_goals simp only [mul_zero, zero_mul]
lemma idxApply_leafM (r : Axes) (u : ℕ → Stroke) {L : ℕ} (h : Splits r L) (g : ∀ i<L, (u i).Sound (r i))
    (x : Line) (k : ℕ) (hk : k<extent r L) :
    idxApply (extent r L) (axisKron r (fun t => leafM (u t)) L) x k =
      (survey r u L k).2 * x (survey r u L k).1 := by
  rw [idxApply, Finset.sum_eq_single (survey r u L k).1 (fun b hb e => by rw [axisKron_leafM r u h g L le_rfl k hk b (Finset.mem_range.1 hb), if_neg e, zero_mul])
    (fun e => (e (Finset.mem_range.2 (survey_lt h g L le_rfl k hk))).elim), axisKron_leafM r u h g L le_rfl k hk _ (survey_lt h g L le_rfl k hk), if_pos rfl]
lemma AxisStroke.climbing (h : b.AxisStroke l r u) {s : Ty} (S : ι → ℕ → ℕ → T s)
    (hS : b.Moves (fun _ => 0) s fun i => S i 0 0)
    (step : (AxisCtx.stepBench b l r s S).Moves (fun _ => 0) strokeBlockCellTy
        (fun d => strokeBlockCell (u d.i.i d.i.j) (AxisStep.stepLow d)) →
      (AxisCtx.stepBench b l r s S).Moves (fun _ => 0) s fun d => S d.i.i (d.i.j+1) d.j) :
    b.Moves (fun i => extent (r i) (l i)) (a s) fun i =>
      Tape.tab (extent (r i) (l i)) (S i (l i)) :=
  h.1.climbAxes S hS (step (((h.2.2.transfer (AxisCtx.stepBench_reads ..)).pick _ (AxisCtx.stepBench_words h.1 S).2.1.toMoves h.1.lower)))
theorem AxisStroke.survey_moves (h : b.AxisStroke l r u) :
    b.Moves (fun i => extent (r i) (l i)) (a surveyCellTy) fun i =>
      Tape.tab (extent (r i) (l i)) (survey (r i) (u i) (l i)) :=
  h.climbing (s := surveyCellTy) (fun i k j => survey (r i) (u i) k j) ((Can.wc 0).pair Can.one) fun hb =>
    have R := AxisCtx.stepBench_words (s := surveyCellTy) h.1 (fun i k j => survey (r i) (u i) k j)
    have Nr := h.1.4.transfer (AxisCtx.stepBench_reads ..)
    have N1 : (AxisCtx.stepBench b l r surveyCellTy _).FreeWord fun d => (survey (r d.i.i) (u d.i.i) d.i.j (AxisStep.stepHigh d)).1 :=
      ⟨R.2.2.fst.toPoly _, (h.1.3.reindex fun d : AxisStep l r => d.i.i).mono fun d => (survey_lt (h.1.2 _) (fun i hi => h.good _ i hi)
        d.i.j d.i.hj.le _ (h.1.smaller d) |>.trans_le ((h.1.2 _).extent_le d.i.hj.le)).le⟩
    ((N1.mul Nr).add ⟨hb.fst.fst.toPoly _, Nr.2.mono fun d => ((h.good _ _ d.i.hj).bdix _ (h.1.lower d)).le⟩).toMoves.pair (R.2.2.snd.mul hb.fst.snd)
theorem AxisStroke.blocks_moves (h : b.AxisStroke l r u) :
    b.Moves (fun i => extent (r i) (l i)) (a blockCellTy) fun i =>
      Tape.tab (extent (r i) (l i)) fun j => blockCell (strokeBlocks (r i) (u i) (l i) j) :=
  h.climbing (s := blockCellTy) (fun i k j => blockCell (strokeBlocks (r i) (u i) k j)) ((Can.wc 0).pair ((Can.wc 1).pair ((Can.wc 0).pair (Can.wc 0)))) fun hb =>
    have R := AxisCtx.stepBench_words (s := blockCellTy) h.1 (fun i k j => blockCell (strokeBlocks (r i) (u i) k j))
    have Nr := h.1.4.transfer (AxisCtx.stepBench_reads ..)
    have Ks := BlockFields.of_blockCell (l := fun d : AxisStep l r => d.i.j) (h.1.extent_small.reindex During.i) (fun d => (strokeBlocks_cover (r d.i.i) d.i.j (u d.i.i) ((h.1.2 _).cut d.i.hj.le)
      fun i hi => h.good _ i (by have := d.i.hj; omega)).mark _ (h.1.smaller d)) R.2.2
    have Kt := BlockFields.of_blockCell (l := fun _ => 1) Nr.2 (fun d => PairBlocks.marked (h.good _ _ d.i.hj) (h.1.lower d)) hb.snd
    BlockFields.blockCell_moves (b := AxisCtx.stepBench b l r blockCellTy fun i k j => blockCell (strokeBlocks (r i) (u i) k j)) (Y := fun d => blockMul (r d.i.i d.i.j) (strokeBlocks (r d.i.i) (u d.i.i) d.i.j (AxisStep.stepHigh d)) (block (u d.i.i d.i.j) (AxisStep.stepLow d)))
      ⟨(Ks.1.mul Nr).add (Ks.2.mul Kt.1), Ks.2.mul Kt.2, Ks.3.add Kt.3, (Ks.4.mul Kt.2).add Kt.4⟩
theorem AxisStroke.perm_moves (h : b.AxisStroke l r u) (cl : Paint) (x : ι → Line)
    (hx : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (extent (r i) (l i)) (x i)) :
    b.Moves (fun i => extent (r i) (l i)) (a (c cl)) fun i =>
      Tape.tab (extent (r i) (l i)) (idxApply (extent (r i) (l i))
        (axisKron (r i) (fun j => leafM (u i j)) (l i)) (x i)) :=
  Can.bind h.survey_moves <|
    have I := FreeReads.extend (t := a surveyCellTy) b fun i => Tape.tab (extent (r i) (l i)) (survey (r i) (u i) (l i))
    have X := hx.transfer I
    have NE : (b.extend _ _).FreeWord fun i => extent (r i) (l i) := ⟨(X.len h.1.3).toPoly _, h.1.3⟩
    have I1 := FreeReads.scan (b.extend _ _) fun i => extent (r i) (l i)
    have P := ((newestMoves (W := fun _ => 0) b _).transfer I1).pick _ (scanIndex NE).toMoves fun d => d.hj
    (arrayNow (t := c cl) NE (fun i k => (survey (r i) (u i) (l i) k).2 * x i (survey (r i) (u i) (l i) k).1) (P.snd.mul ((X.transfer I1).pick _ P.fst fun d =>
      survey_lt (h.1.2 d.i) (fun j hj => h.good _ j hj) _ le_rfl d.j d.hj))).congr fun i =>
      congrArg (Tape.mk _) (funext fun k => (idxApply_leafM (r i) (u i) (h.1.2 i) (fun j hj => h.good i j hj) (x i) k k.2).symm)
end PowerSaving.RAM.Bench
end OAI
end
-- ===== end part 1 =====

-- ===== part 2: the ripple engine and its use (to the end of the file) =====

section

namespace OAI.PowerSaving
noncomputable section

abbrev RippleEngine.{U} (z : ℝ) : Prop :=
  0 ≤ z ∧ ∀ (pt : RAM.Paint) (mode : Bool) {Idx : Type U} (dim : Idx → ℕ) (vals : ∀ i, Binary.Bits (dim i) → ℂ),
    RAM.Can mode (fun i => 2 ^ dim i) (RAM.simIn pt) (RAM.bundle pt) (fun i => RAM.givenBits pt (dim i) (vals i))
      (fun i => (Binary.bits (dim i)).tape (Binary.ripple (dim i) (vals i))) fun i => 2 ^ dim i * envelope z (dim i)

end

/-
Front end over an engine. The engine `hE : RippleEngine z` is the only fast step; this file
lays the data out for it. The plan (one block-ripple pass per beat: pack the entries block by block, call the
engine once per block head, read each entry back from its head's answer) is the one of OpenAI's
SectorAlgorithm/SynchronizedAlgorithm (github.com/openai/math, commit fd4aeeb, Apache-2.0); the code here is
this tree's own: one general cover theorem `cover_ripple` (in place of OpenAI's sequence of cover notions), the engine
call on plain tables (`engine_tab`), and the whole beat loop inside `AxisReels.kron_moves`.
-/
namespace RAM
open Ty Finset AxisTensor PowBlock Binary ReelKit
noncomputable section

universe U V

/-- Answer kept at a block head: the ripple of that block (an empty tape off the heads). -/
def headRun (n : ℕ) (f : ℕ → PowBlock) (x : Line) (a : ℕ) : Tape ℂ :=
  if (blockAt n f a).seat = 0 then Tape.tab (blockAt n f a).width (blockAtRipple n f x a) else Tape.tab 0 fun _ => 0

namespace Bench
variable {cl : Paint} {z : ℝ} {m : Bool} {ι : Type U} {κ : Type V} {b : Bench m ι}

/-- A batch of complex tables (row `i` has length `N i`) made at cost `W`. -/
abbrev Tables (b : Bench m ι) (W : ι → ℕ) (cl : Paint) (N : ι → ℕ) (v : ι → Line) : Prop :=
  b.Moves W (a (c cl)) fun i => Tape.tab (N i) (v i)

/-- The unit `I` is at hand for free. -/
abbrev HasI (b : Bench m ι) : Prop := b.Moves (fun _ => 0) sc fun _ => Complex.I

/-- One engine call per instance on a table of length `n = 2^k`, paid at the envelope of any `l ≥ k`. -/
theorem engine_tab (hE : RippleEngine.{U} z) {k l n : ι → ℕ} {y : ι → Line}
    (hw : ∀ i, n i = 2^k i) (hkl : ∀ i, k i ≤ l i) (hn : b.FreeWord n) (hk : b.FreeWord k)
    (hI : b.HasI) (hy : b.Tables n cl n y) :
    b.Tables (fun i => n i * envelope z (l i)) cl n fun i => blockRipple (k i) (y i) := by
  have tb : ∀ i (g : Line), Tape.tab (n i) g = (bits (k i)).tape fun e => g ((bits (k i)).loc e) :=
    fun i g => by rw [hw i, ← bits_len, Layout.tab_eq_tape]
  have call := ((hE.2 cl m k fun i e => y i ((bits (k i)).loc e)).ambient
    (hn.small.mono fun i => (hw i).ge)).mono fun i => Nat.mul_le_mul (hw i).ge (envelope_monotone hE.1 (hkl i))
  refine Can.congr (Can.then_do (hk.toMoves.anyCost.pair (hI.anyCost.pair ((hy.weaken (Dom.of_le fun i =>
    Nat.le_mul_of_pos_right _ (envelope_positive z _))).congr fun i => tb i _))) call) fun i => ?_
  rw [tb i]; congr 1; funext e; exact (blockRipple_loc _ _ e).symm

lemma BlockFields.transfer {q : Bench m κ} {Y : κ → PowBlock} (h : q.BlockFields Y) {g : ι → κ}
    (hg : b.FreeReads q g) : b.BlockFields fun i => Y (g i) :=
  ⟨h.1.transfer hg, h.2.transfer hg, h.3.transfer hg, h.4.transfer hg⟩

/-- The four fields of a block read from a tape at a position. -/
lemma blockFields_of_tape {t : Ty} {n l j : ι → ℕ} {g : ι → ℕ → PowBlock} {e : ι → ℕ → T t} (pr : T t → T blockCellTy)
    (hpr : ∀ i a, pr (e i a) = blockCell (g i a)) (hs : Small b.size n) (hm : ∀ i, (g i (j i)).Mark (n i) (l i))
    (he : b.Moves (fun _ => 0) (a t) fun i => Tape.tab (n i) (e i)) (hj : b.FreeWord j) (hl : ∀ i, j i < n i)
    (hp : ∀ {v : ι → T t}, b.Moves (fun _ => 0) t v → b.Moves (fun _ => 0) blockCellTy fun i => pr (v i)) :
    b.BlockFields fun i => g i (j i) :=
  BlockFields.of_blockCell hs hm ((hp (Can.pick e he hj.toMoves hl)).congr fun i => hpr _ _)

/-- Block ripple over any power-of-two block cover, given its chip table: entry `j` gets the ripple
of its block, read at its seat. Cost `n · envelope(l)`. -/
theorem cover_ripple (hE : RippleEngine.{U} z) {n l : ι → ℕ} {f : ι → ℕ → PowBlock} {x : ι → Line}
    (hn : b.FreeWord n) (hf : ∀ i, PowBlockCover (n i) (l i) (f i))
    (hc : b.Moves (fun _ => 0) (a blockCellTy) fun i => Tape.tab (n i) fun j => blockCell (f i j))
    (hx : b.Tables (fun _ => 0) cl n x) (hI : b.HasI) :
    b.Tables (fun i => n i * envelope z (l i)) cl n fun i j =>
      blockAtRipple (n i) (f i) (x i) (f i j).start (f i j).seat := by
  have dom : Dom (fun i => n i * envelope z (l i)) n :=
    Dom.of_le fun i => Nat.le_mul_of_pos_right _ (envelope_positive z _)
  -- step 1: the entries in address order, each with the chip of its block
  let P : ι → T (a (p blockCellTy (c cl))) := fun i =>
    Tape.tab (n i) fun e => (blockCell (blockAt (n i) (f i) e), permLine (n i) (f i) (x i) e)
  have hP : b.Moves n _ P := by
    have S := FreeReads.scan b n
    have fj := blockFields_of_tape id (fun _ _ => rfl) (hn.transfer S).small (fun d => (hf d.i).mark _ d.hj)
      (hc.transfer S) (scanIndex hn) During.hj id
    exact (scatterNow hn (fun i j => ((f i j).addr, blockCell (f i j), x i j)) (fj.addr.toMoves.pair
      (fj.blockCell_moves.pair (Can.pick (t := c cl) (n := fun d : During n => n d.i) (fun d j => x d.i j) (hx.transfer S) (scanIndex hn).toMoves During.hj)))).congr
      fun i => (hf i).reloc.sow (fun j => (blockCell (f i j), x i j)) _
  refine Can.bind (hP.weaken dom) ?_
  -- step 2: one engine call per block head
  have E := FreeReads.extend b (t := a (p blockCellTy (c cl))) P
  let B1 := b.extend (a (p blockCellTy (c cl))) P
  have hn1 : B1.FreeWord n := hn.transfer E
  let R : ι → T (a (a (c cl))) := fun i => Tape.tab (n i) (headRun (n i) (f i) (x i))
  have hR : B1.Moves (fun i => n i * envelope z (l i)) _ R := by
    have S := FreeReads.scan B1 n
    have pa := fun (d : During n) => (hf d.i).blockAt_mark d.hj
    have fa := blockFields_of_tape (b := B1.scan n) Prod.fst (fun _ _ => rfl) (hn1.transfer S).small pa
      ((newestMoves (W := fun _ => 0) b P).transfer S) (scanIndex hn1) During.hj fun h => h.fst
    refine (arrayM hn1 _ (u := fun i e => headWidth (n i) (f i) e * envelope z (l i))
      (Can.testz fa.seat.toMoves.anyCost ?_ ?_)).weaken ⟨3, fun i => ?_⟩
    · let Z := (B1.scan n).along (Subtype.val (p := fun d : During n => (blockAt (n d.i) (f d.i) d.j).seat = 0))
      have A : Z.FreeReads (B1.scan n) Subtype.val := FreeReads.along _ _
      have fz := fa.transfer A
      have fit : ∀ d : {d : During n // (blockAt (n d.i) (f d.i) d.j).seat = 0},
          d.1.j + (blockAt (n d.1.i) (f d.1.i) d.1.j).width ≤ n d.1.i := fun d => by
        have h1 := (pa d.1).endsBy; have h2 := (hf d.1.i).blockAt_addr d.1.hj; have h3 := d.2
        unfold blockEnd at h1; unfold addr at h2; omega
      let wd : {d : During n // (blockAt (n d.i) (f d.i) d.j).seat = 0} → ℕ :=
        fun d => (blockAt (n d.1.i) (f d.1.i) d.1.j).width
      have S' := FreeReads.scan Z wd
      have hj := (((scanIndex hn1).transfer A).transfer S').add (scanIndex fz.widths)
      have rd := Can.pick (t := p blockCellTy (c cl)) (n := fun e : During wd => n e.i.1.i) (fun (e : During wd) a => (blockCell (blockAt (n e.i.1.i) (f e.i.1.i) a), permLine (n e.i.1.i) (f e.i.1.i) (x e.i.1.i) a))
        ((newestMoves (W := fun _ => 0) b P).transfer ((S'.next A).next S)) (k := fun e : During wd => e.i.1.j + e.j) hj.toMoves fun e => by have := fit e.i; have := e.hj; simp only [wd] at *; omega
      have rd' : (Z.scan wd).Moves (fun _ => 0) (c cl) fun e => lineFrom (n e.i.1.i) (f e.i.1.i) (x e.i.1.i) e.i.1.j e.j :=
        rd.snd
      have sl : Z.Moves wd (a (c cl)) fun d => Tape.tab (wd d) (lineFrom (n d.1.i) (f d.1.i) (x d.1.i) d.1.j) :=
        arrayNow (fz.widths : Z.FreeWord wd) _ rd'
      have run := engine_tab hE (fun d => (pa d.1).size) (fun d => (pa d.1).tall) fz.widths fz.tall
        (((hI.transfer E).transfer S).transfer A) sl
      refine (run.congr fun d => ?_).weaken (Dom.of_le fun d => ?_)
      · simp only [headRun, d.2, ↓reduceIte]; rfl
      · simp only [headWidth, d.2, ↓reduceIte]; exact le_rfl
    · let M := (B1.scan n).along (Subtype.val (p := fun d : During n => (blockAt (n d.i) (f d.i) d.j).seat ≠ 0))
      exact ((arrayNow (b := M) (t := c cl) (WordIn.wc 0) (fun _ _ => (0 : ℂ)) Can.zero).weaken (Dom.const _ 0)).congr
        fun (d : {d : During n // (blockAt (n d.i) (f d.i) d.j).seat ≠ 0}) => by simp only [headRun, d.2, ↓reduceIte]
    · dsimp only; rw [← sum_mul, headWidth_sum _ _ _ (hf i)]
      have := Nat.le_mul_of_pos_right (n i) (envelope_positive z (l i)); omega
  refine Can.bind hR ?_
  -- step 3: entry `j` reads its head's answer at its seat
  have E2 := FreeReads.extend B1 (t := a (a (c cl))) R
  have hn2 : (B1.extend _ R).FreeWord n := hn1.transfer E2
  have S := FreeReads.scan (B1.extend _ R) n
  have fb := blockFields_of_tape id (fun _ _ => rfl) (hn2.transfer S).small (fun d => (hf d.i).mark _ d.hj)
    (((hc.transfer E).transfer E2).transfer S) (scanIndex hn2) During.hj id
  have row := Can.pick (t := a (c cl)) (n := fun d : During n => n d.i) (fun d e => headRun (n d.i) (f d.i) (x d.i) e) ((newestMoves (W := fun _ => 0) B1 R).transfer S) fb.starts.toMoves
    fun d => ((hf d.i).mark _ d.hj).starts.trans_le ((hf d.i).mark _ d.hj).endsBy
  have row' : ((B1.extend _ R).scan n).Moves (fun _ => 0) (a (c cl)) fun d =>
      Tape.tab (f d.i d.j).width (blockAtRipple (n d.i) (f d.i) (x d.i) (f d.i d.j).start) := row.congr fun d => by
      have M := (hf d.i).blockAt_align d.hj le_rfl ((hf d.i).mark _ d.hj).starts
      simp only [headRun, M.2, Nat.sub_self, ↓reduceIte, M.1.2.1]
  have hs : ((B1.extend _ R).scan n).Moves (fun _ => 0) (c cl) fun d =>
      blockAtRipple (n d.i) (f d.i) (x d.i) (f d.i d.j).start (f d.i d.j).seat :=
    (Can.pick (t := c cl) (n := fun d : During n => (f d.i d.j).width)
      (fun d e => blockAtRipple (n d.i) (f d.i) (x d.i) (f d.i d.j).start e) row' fb.seat.toMoves
      fun d => ((hf d.i).mark _ d.hj).place)
  exact (arrayNow hn2 _ hs).weaken dom

variable {l d : ι → ℕ} {r : ι → Axes} {x : ι → Line}

/-- One beat on all axes at once: every axis' permutation with its dyes, then every axis' pairwise mix,
the mix done as one block ripple over the stroke blocks. -/
theorem AxisStroke.step_moves (hE : RippleEngine.{U} z) {u : ι → ℕ → Stroke} (h : b.AxisStroke l r u)
    (hI : b.HasI) (hx : b.Tables (fun _ => 0) cl (fun i => extent (r i) (l i)) x) :
    let N := fun i => extent (r i) (l i)
    b.Tables (fun i => N i * envelope z (l i)) cl N fun i =>
      idxApply (N i) (AxisTensor.axisKron (r i) (fun j => leafC (u i j)) (l i))
        (idxApply (N i) (AxisTensor.axisKron (r i) (fun j => leafM (u i j)) (l i)) (x i)) := by
  intro N
  have dom : Dom (fun i => N i * envelope z (l i)) N :=
    Dom.of_le fun i => Nat.le_mul_of_pos_right _ (envelope_positive z _)
  let Y : ι → T (a (c cl)) := fun i =>
    Tape.tab (N i) (idxApply (N i) (AxisTensor.axisKron (r i) (fun j => leafM (u i j)) (l i)) (x i))
  refine Can.bind ((h.perm_moves cl x hx).weaken dom) ?_
  have E := FreeReads.extend b (t := a (c cl)) Y
  let K : ι → T (a blockCellTy) := fun i => Tape.tab (N i) fun j => blockCell (strokeBlocks (r i) (u i) (l i) j)
  refine Can.bind ((h.transfer E).blocks_moves.weaken dom) ?_
  have E2 := FreeReads.extend (b.extend _ Y) (t := a blockCellTy) K
  have hN : (b.extend _ Y).extend _ K |>.FreeWord N := (show b.FreeWord N from ⟨(hx.len h.axisCtx.span).toPoly _, h.axisCtx.span⟩).transfer (E2.next E)
  exact (cover_ripple hE hN (fun i => strokeBlocks_cover _ _ _ (h.axisCtx.good i) (h.good i)) (newestMoves _ K)
    ((newestMoves b Y).transfer E2) ((hI.transfer E).transfer E2)).congr fun i =>
      tape_congr_sized fun j hj => (idxApply_eq_blockAtRipple _ _ _ (h.axisCtx.good i) (h.good i) _ _ hj).symm

/-- The stroke trees of all axes of one instance, one tape cell per axis. -/
def axisReelBlocks (ax : Axes) (len : ℕ) (reel : ℕ → Reel) : T (a reelBlocksTy) := Tape.tab len fun j => reelBlocksT (ax j) (reel j)

/-- Reels for every axis, all with `ticks` beats, their trees on a tape. -/
structure AxisReels (b : Bench m ι) (len ticks : ι → ℕ) (ax : ι → Axes) (reel : ι → ℕ → Reel) : Prop where
  axisCtx : b.AxisCtx len ax
  count : b.FreeWord ticks
  sound : ∀ i j, j < len i → (reel i j).Sound (ax i j)
  even : ∀ i j, j < len i → (reel i j).beats = ticks i
  trees : b.Moves (fun _ => 0) (a reelBlocksTy) fun i => axisReelBlocks (ax i) (len i) (reel i)

lemma AxisReels.transfer {q : Bench m κ} {l d : κ→ℕ} {r : κ→Axes} {u : κ → ℕ→Reel} (h : q.AxisReels l d r u)
    {g} (hg : b.FreeReads q g) :
    b.AxisReels (fun i => l (g i)) (fun i => d (g i)) (fun i => r (g i)) (fun i => u (g i)) :=
  ⟨h.1.transfer hg, h.2.transfer hg, fun i => h.3 (g i), fun i => h.4 (g i), h.5.transfer hg⟩

/-- All axes' reels run in lockstep for their `d` beats, one `step_moves` per beat; when each axis' reel
creates the matrix `X i j`, the result is the Kronecker product applied to the input. -/
theorem AxisReels.kron_moves (hE : RippleEngine.{U} z) {pV : ι → ℕ → Reel} (h : b.AxisReels l d r pV)
    (hI : b.HasI) (hx : b.Tables (fun _ => 0) cl (fun i => extent (r i) (l i)) x)
    (X : ι→ℕ→IdxMat) (hg : ∀ i, ∀ j<l i, Creates (pV i j) (r i j) (AxisTensor.frame _ (X i j))) :
    b.Tables (fun i => d i * (extent (r i) (l i) * envelope z (l i))) cl (fun i => extent (r i) (l i))
      fun i => idxApply (extent (r i) (l i)) (AxisTensor.axisKron (r i) (X i) (l i)) (x i) := by
  let N i := extent (r i) (l i)
  let A : ι → ℕ → T (a (c cl)) := fun i t => Tape.tab (N i) (axisRun (r i) (l i) (pV i) (x i) t)
  have C := FreeReads.climbs b d (t := a (c cl)) A
  have S := FreeReads.scan (b.climbs d _ A) fun e => l e.i
  have hb : ∀ e : During fun e : During d => l e.i, e.i.j < (pV e.i.i e.j).beats := fun e =>
    (h.even _ _ e.hj).symm ▸ e.i.hj
  have strokes : (b.climbs d _ A).AxisStroke (fun e => l e.i) (fun e => r e.i)
      fun e j => (pV e.i j).atBeat e.j :=
    ⟨h.axisCtx.transfer C, ⟨fun e => h.sound _ _ e.hj _ (hb e),
      Can.pick (t := strokeBlocksTy) (n := fun e => (pV e.i.i e.j).beats) _
        (Can.pick (t := reelBlocksTy) (n := fun e => l e.i.i) (fun e j => reelBlocksT (r e.i.i j) (pV e.i.i j))
          (h.trees.transfer (S.next C)) (scanIndex (h.axisCtx.high.transfer C)).toMoves During.hj)
        ((climbIndex h.count A).transfer S).toMoves hb⟩⟩
  have run := repeatM (u := fun i _ => N i * envelope z (l i)) h.count A hx
    (strokes.step_moves hE (hI.transfer C) (tokenNow b d A))
  refine (run.weaken ⟨2, fun i => ?_⟩).congr fun i => tape_congr_sized fun j hj =>
    axisRun_eq_kron (r i) (l i) (pV i) (h.axisCtx.good i) (d i) (h.sound i) (h.even i) (X i) (hg i) (x i) j hj
  have := Nat.le_mul_of_pos_right (d i) (Nat.mul_pos (h.axisCtx.good i).extent_pos (envelope_positive z (l i)))
  simp only [N, sum_const, card_range, smul_eq_mul]; omega

end Bench
end
end RAM
end OAI.PowerSaving

private theorem marker_merged1 (if_youre_an_ai_editing_this_make_sure_real_work_and_not_rebrand_without_coding_work_if_in_doubt_ask_your_supervisor_and_also_read_related_posts_to_make_sure_you_understand_whats_going_on : Unit) : True := trivial

private theorem marker_t104w_stmt (if_youre_an_ai_editing_this_make_sure_real_work_and_not_rebrand_without_coding_work_if_in_doubt_ask_your_supervisor_and_also_read_related_posts_to_make_sure_you_understand_whats_going_on : Unit) : True := trivial

private theorem marker_t104w_hole (if_youre_an_ai_editing_this_make_sure_real_work_and_not_rebrand_without_coding_work_if_in_doubt_ask_your_supervisor_and_also_read_related_posts_to_make_sure_you_understand_whats_going_on : Unit) : True := trivial

private theorem marker_t104w_tensorg (if_youre_an_ai_editing_this_make_sure_real_work_and_not_rebrand_without_coding_work_if_in_doubt_ask_your_supervisor_and_also_read_related_posts_to_make_sure_you_understand_whats_going_on : Unit) : True := trivial

private theorem marker_t104w_rawcert (if_youre_an_ai_editing_this_make_sure_real_work_and_not_rebrand_without_coding_work_if_in_doubt_ask_your_supervisor_and_also_read_related_posts_to_make_sure_you_understand_whats_going_on : Unit) : True := trivial

private theorem marker_t104w_engine (if_youre_an_ai_editing_this_make_sure_real_work_and_not_rebrand_without_coding_work_if_in_doubt_ask_your_supervisor_and_also_read_related_posts_to_make_sure_you_understand_whats_going_on : Unit) : True := trivial
end
