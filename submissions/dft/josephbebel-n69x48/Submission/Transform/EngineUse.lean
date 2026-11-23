--might be  containing modified Apache-2.0 codes pieces from one or several sources; notices and credits: Credits.lean
import Submission.Transform.ReelCompile
import Submission.Engine.TensorPower
import Submission.Cert.Batch.Word

namespace OAI.PowerSaving
noncomputable section

def baseEngineExp : ℝ := 1 - 7835230765108121/(2*(10:ℝ)^18)

theorem baseEngineExp_pos : 0 < baseEngineExp := by norm_num [baseEngineExp]
theorem baseEngineExp_lt_one : baseEngineExp < 1 := by norm_num [baseEngineExp]

abbrev baseEnvelope := envelope baseEngineExp

open Binary RAM RAM.Ty in

abbrev RippleEngine.{U} (z : ℝ) : Prop := 0 ≤ z ∧ ∀ (cl : Paint) (m : Bool) {ι : Type U} (k : ι→ℕ) (v : ∀ i, Bits (k i) → ℂ),
  Can m (fun i => 2^k i) (simIn cl) (bundle cl)
    (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i))) (fun i => 2^k i*envelope z (k i))

lemma envelope_baseEngineExp_le (k : ℕ) : (baseEnvelope k:ℝ) ≤ 2*((k:ℝ)+1)^baseEngineExp := envelope_real baseEngineExp baseEngineExp_pos.le k

namespace RAM
open Binary Matrix Ty Finset
universe U

set_option maxRecDepth 100000 in

theorem rippleEngine_base : RippleEngine.{U} baseEngineExp := ⟨baseEngineExp_pos.le, fun cl m _ k v => by
  obtain ⟨α, ρ, σ, i1, i2, i3, i4, i5, i6, e, tr, tz, wd, G, he, hind, hP, hw, hG, hα, htr, hcnt, hhist⟩ :=
    Batch48.rawCert_exists_B48
  exact @TensorPower.ripple_program_of_rawCert α ρ σ i1 i2 i3 i4 i5 i6 e tr tz wd G he hind hP hw hG hα htr hcnt hhist
    baseEngineExp (by norm_num [baseEngineExp]) (by norm_num [baseEngineExp]) m cl _ k v⟩

end RAM

lemma envelope_mono_z {z z' : ℝ} (h : z ≤ z') (k : ℕ) : envelope z k ≤ envelope z' k :=
  Nat.ceil_mono (Real.rpow_le_rpow_of_exponent_le (by simp only [le_add_iff_nonneg_left, Nat.cast_nonneg]) h)

theorem RippleEngine.mono.{U} {z z' : ℝ} (h : RippleEngine.{U} z) (hz : z ≤ z') : RippleEngine.{U} z' :=
  ⟨h.1.trans hz, fun cl m _ k v => (h.2 cl m k v).mono fun _ => Nat.mul_le_mul_left _ (envelope_mono_z hz _)⟩

end

/-
Derived from lean/OAI/Computability/FourierTransform/SectorAlgorithm.lean of github.com/openai/math
(commit fd4aeeb, Apache-2.0), modified for this repository:
  * merged into this file with other modules, imports changed, some declarations renamed, comments removed;
  * OpenAI's fixed exponent `alpha = 1 - 2/10^11` and envelope `hills` are replaced, where they occur, by a
    general exponent with `envelope`, and OpenAI's `hills_program` by the hypothesis `hE : RippleEngine z`
    (Transform/EngineUse.lean; instance `rippleEngine_base` at `baseEngineExp = 1 - 7835230765108121/(2·10^18)`);
  * proofs changed to match.
-/
namespace RAM
open Ty Finset AxisTensor PowBlock Binary
noncomputable section

universe U V

def blockChips (n : ℕ) (f : ℕ→PowBlock) :=
  Tape.tab n fun i => chip (f i)

abbrev stowedEntryTy (cl : Paint) := p chipTy (c cl)

def stowedEntry (n : ℕ) (f : ℕ→PowBlock) (x : Line) (j : ℕ) :=
  (chip (patch n f j),stow n f x j)

def patchRuns (n : ℕ) (f : ℕ→PowBlock) (x : Line) (j : ℕ) :=
  if (patch n f j).seat=0 then Tape.tab (patch n f j).width (patchRipple n f x j)
  else Tape.tab 0 (fun _ => (0:ℂ))

namespace Bench
section
variable {m : Bool} {ι : Type U} {κ : Type V} {b : Bench m ι} {q : Bench m κ}
  {cl : Paint} {k l n : ι → ℕ} {x : ι→Line} {f : ι → ℕ→PowBlock} {z : ℝ} (hE : RippleEngine.{U} z)

include hE in
theorem blockRipple_moves (hw : ∀ i,n i=2^k i) (hg : ∀ i,k i≤l i) (hn : b.Nick n) (hk : b.Nick k)
    (hI : b.Moves (fun _ => 0) sc fun _ => Complex.I)
    (hx : b.Moves n (a (c cl)) fun i => Tape.tab (n i) (x i)) :
    b.Moves (fun i => n i*envelope z (l i)) (a (c cl)) fun i =>
      Tape.tab (n i) (blockRipple (k i) (x i)) := by
  let W i := n i*envelope z (l i)
  let v i (d : Bits (k i)) := x i ((bits (k i)).loc d)
  have ht : Dom W n := Dom.of_le (fun i => Nat.le_mul_of_pos_right _ (envelope_pos z _))
  have hx' : b.Moves W (a (c cl)) fun i => (bits (k i)).tape (v i) := by
    exact (hx.weaken ht).congr fun i => Layout.verify _ _ 0 (v i) (hw i) fun d => by
      rw [Tape.look_tab, hw,ite_eq_left (show (bits (k i)).loc d < 2^k i from (bits _).bd d)]
  have he : b.Moves W (a (c cl)) fun i => (bits (k i)).tape (ripple (k i) (v i)) := by
    have hu : Small b.size (fun i => 2^k i) := hn.small.mono fun i => (hw i).ge
    have hj : ∀ i, 2^k i*envelope z (k i) ≤ W i := fun i => Nat.mul_le_mul (by rw [hw])
      (envelope_mono z hE.1 (hg i))
    exact Can.then_do ((hk.close.ease W).pair ((hI.ease W).pair hx')) (((hE.2 cl m k v).ambient hu).mono hj)
  exact he.congr fun i => (Layout.verify _ _ 0 (ripple (k i) (v i)) (hw i) fun d => by
    rw [Tape.look_tab, hw,ite_eq_left (show (bits (k i)).loc d < 2^k i from (bits _).bd d)]
    exact gleam_loc _ _ d).symm

structure BlockCover (b : Bench m ι) (n l : ι→ℕ) (f : ι → ℕ→PowBlock) : Prop where
  length : b.Nick n
  shape : ∀ i, PowBlockCover (n i) (l i) (f i)
  cover : b.Moves (fun _ => 0) (a chipTy) fun i => blockChips (n i) (f i)

namespace BlockCover
variable {j : ι→ℕ}

lemma transfer {n l : κ→ℕ} {f : κ→ℕ→PowBlock} (h : q.BlockCover n l f) {p}
    (g : b.Instant q p) :
    b.BlockCover (fun i => n (p i)) (fun i => l (p i)) (fun i => f (p i)) :=
  ⟨h.length.transfer g,fun _ => h.shape _,h.cover.transfer g⟩

lemma kitOf (h : b.BlockCover n l f) (hj : b.Nick j) (hg : ∀ i,j i<n i) :
    b.ShardFields fun i => f i (j i) :=
  ShardFields.of_chip h.length.small (fun i => (h.shape i).mark _ (hg i))
    (Moves.pick (n:=n) (t:=chipTy) _ h.cover hj.close hg)

lemma stow_moves (h : b.BlockCover n l f)
    (hx : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (n i) (x i)) :
    b.Moves n (a (stowedEntryTy cl)) fun i => Tape.tab (n i) (stowedEntry (n i) (f i) (x i)) := by
  let Tchip (i : ι) (j : ℕ) : T (stowedEntryTy cl) := (chip (f i j),x i j)
  have F := Instant.scan b n
  have hh := chop h.length
  have hp := (h.transfer F).kitOf hh During.hj
  have hs : (b.scan n).Moves (fun _ => 0) (c cl) fun i => x i.i i.j :=
    Moves.pick (n:=fun i => n i.i) (t:=c cl) _ (hx.transfer F) hh.close During.hj
  have ht := scatterNow (t:=stowedEntryTy cl) h.length
    (fun i j => ((f i j).addr,Tchip i j)) (hp.addr.close.pair (hp.chip_moves.pair hs))
  exact ht.congr (fun i => (h.shape i).reloc.sow (Tchip i) _)

end BlockCover

variable (cl) in
structure StowedCover (b : Bench m ι) (n l : ι→ℕ) (f : ι → ℕ→PowBlock) (x : ι → Line) : Prop where
  mat : b.BlockCover n l f
  packed : b.Moves (fun _ => 0) (a (stowedEntryTy cl)) fun i =>
    Tape.tab (n i) (stowedEntry (n i) (f i) (x i))
  unitI : b.Moves (fun _ => 0) sc fun _ => Complex.I

namespace StowedCover
variable {j : ι→ℕ}

lemma transfer {n l : κ→ℕ} {f : κ→ℕ→PowBlock} {x : κ→Line}
    (h : q.StowedCover cl n l f x) {p} (g : b.Instant q p) :
    b.StowedCover cl (fun i => n (p i)) (fun i => l (p i)) (fun i => f (p i)) (fun i => x (p i)) :=
  ⟨h.mat.transfer g,h.packed.transfer g,h.unitI.transfer g⟩

lemma kitOf (h : b.StowedCover cl n l f x) (hj : b.Nick j) (hg : ∀ i,j i<n i) :
    b.ShardFields fun i => patch (n i) (f i) (j i) :=
  ShardFields.of_chip h.mat.length.small (fun i => (h.mat.shape i).patch_mark (hg i))
    (Moves.pick (n:=n) (t:=stowedEntryTy cl) _ h.packed hj.close hg).fst
lemma stowOf (h : b.StowedCover cl n l f x) (hj : b.Nick j) (hg : ∀ i,j i<n i) :
    b.Moves (fun _ => 0) (c cl) fun i => stow (n i) (f i) (x i) (j i) :=
  (Moves.pick (n:=n) (t:=stowedEntryTy cl) _ h.packed hj.close hg).snd

include hE in
lemma run_moves (h : b.StowedCover cl n l f x) (hj : b.Nick j) (hg : ∀ i,j i<n i)
    (hz : ∀ i,(patch (n i) (f i) (j i)).seat=0) :
    b.Moves (fun i => seatfare (n i) (f i) (j i) * envelope z (l i)) (a (c cl))
      fun i => patchRuns (n i) (f i) (x i) (j i) := by
  let B i := patch (n i) (f i) (j i)
  let Q i := (B i).width
  have HK := h.kitOf hj hg
  have he (i : ι) : (B i).Mark (n i) (l i) := (h.mat.shape i).patch_mark (hg i)
  have hh (i : ι) : j i+Q i ≤ n i := by
    have A : (B i).tip ≤ n i := (he i).endsBy
    have hx : (B i).addr=j i := (h.mat.shape i).patch_addr (hg i)
    have hy : (B i).seat=0 := hz i
    unfold tip at A; unfold addr at hx; dsimp only [Q]; omega
  let S i := slit (n i) (f i) (x i) (j i)
  have ht : b.Moves Q (a (c cl)) fun i => Tape.tab (Q i) (S i) := by
    have F := Instant.scan b Q
    have hi := chop HK.widths
    have hw := (hj.transfer F).add hi
    exact arrayNow HK.widths (t:=c cl) S ((h.transfer F).stowOf hw fun i =>
      lt_of_lt_of_le (Nat.add_lt_add_left i.hj _) (hh _))
  simp only [seatfare,patchRuns,hz,ite_true]
  exact blockRipple_moves hE (fun i => (he i).size) (fun i => (he i).tall)
    HK.widths HK.tall h.unitI ht

include hE in
lemma runs_moves (h : b.StowedCover cl n l f x) :
    b.Moves (fun i => n i*envelope z (l i)) (a (a (c cl)))
      fun i => Tape.tab (n i) (patchRuns (n i) (f i) (x i)) := by
  let W (i : ι) := n i*envelope z (l i)
  let D := b.scan n
  let C (i : ι) j := seatfare (n i) (f i) j*envelope z (l i)
  let Y (i : ι) := patchRuns (n i) (f i) (x i)
  have hn := h.mat.length
  have F := Instant.scan b n
  have hk := h.transfer F
  have hs := chop hn
  have hb := (hk.kitOf hs During.hj).seat
  have ht : D.Moves (fun d => C d.i d.j) (a (c cl)) fun d => Y d.i d.j := by
    let Q (i : During n) := (patch (n i.i) (f i.i) i.j).seat
    refine inspectz (n:=Q) hb ?_ ?_
    · have ha := Instant.along D (Subtype.val (p:=fun i => Q i=0))
      exact (hk.transfer ha).run_moves hE (hs.transfer ha) (fun i => i.val.hj)
        (fun i => i.property)
    · let A := {i // Q i ≠ 0}
      let M := D.along (Subtype.val (p:=fun i => Q i≠0))
      have hh := arrayNow (b:=M) (t:=c cl) (Nick.wc 0) (fun _ _ => 0) Moves.zero
      exact (hh.weaken (Dom.const _ _)).congr fun i => by
        simp only [Y,patchRuns,show (patch _ _ _).seat ≠ 0 from i.2,↓reduceIte]
  refine (arrayM (t:=a (c cl)) hn Y ht (u:=C)).weaken ⟨3,fun i => ?_⟩
  dsimp only [C]
  rw [← sum_mul, seatfare_sum _ _ _ (h.mat.shape i)]
  have hm := Nat.le_mul_of_pos_right (n i) (envelope_pos z (l i))
  omega

include hE in
lemma patchRipple_moves (h : b.StowedCover cl n l f x) :
    b.Moves (fun i => n i*envelope z (l i)) (a (c cl))
      fun i => Tape.tab (n i) fun j =>
        patchRipple (n i) (f i) (x i) (f i j).start (f i j).seat := by
  let W i := n i*envelope z (l i)
  let T i := patchRuns (n i) (f i) (x i)
  let V i := Tape.tab (n i) (T i)
  let D := b.extend (a (a (c cl))) V
  have F := Instant.extend b (t:=a (a (c cl))) V
  have G := Instant.scan D n
  have HK : Dom W n := Dom.of_le (fun i => Nat.le_mul_of_pos_right _ (envelope_pos z _))
  let B (d : During n) := f d.i d.j
  have hn := (h.mat.length.transfer F)
  have hh := (h.mat.transfer (G.next F)).kitOf (chop hn) During.hj
  have hg (d : During n) := (h.mat.shape d.i).mark d.j d.hj
  have hm (d : During n) : (B d).start < n d.i := (hg d).starts.trans_le (hg d).endsBy
  have ht := Moves.pick (t:=a (c cl)) (n:=fun d : During n => n d.i) (fun d j => T d.i j)
    ((cherry (W:=fun _ => 0) b (t:=a (a (c cl))) V).transfer G)
    hh.starts.close hm
  have he (d : During n) :
      T d.i (B d).start = Tape.tab (B d).width
        (patchRipple (n d.i) (f d.i) (x d.i) (B d).start) := by
    have hM := (h.mat.shape d.i).patch_align d.hj (le_refl (B d).start) (hg d).starts
    have he : (patch (n d.i) (f d.i) (B d).start).seat=0 := hM.2.trans (Nat.sub_self _)
    simp only [T,patchRuns,he,ite_true]
    rw [hM.1.2.1]
  have hj := Moves.pick (b:=D.scan n) (n:=fun d => (B d).width) (t:=c cl)
    (fun d => patchRipple (n d.i) (f d.i) (x d.i) (B d).start) (ht.congr he) hh.seat.close
    (fun d => (hg d).place)
  exact caseM (h.runs_moves hE) ((arrayNow (t:=c cl) hn (fun i j => patchRipple (n i) (f i) (x i) (f i j).start (f i j).seat) hj).weaken HK)

end StowedCover

include hE in
lemma BlockCover.patchRipple_moves (h : b.BlockCover n l f)
    (hx : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (n i) (x i))
    (hI : b.Moves (fun _ => 0) sc fun _ => Complex.I) :
    b.Moves (fun i => n i*envelope z (l i)) (a (c cl))
      fun i => Tape.tab (n i) fun j =>
        patchRipple (n i) (f i) (x i) (f i j).start (f i j).seat := by
  let V i := Tape.tab (n i) (stowedEntry (n i) (f i) (x i))
  let D := b.extend (a (stowedEntryTy cl)) V
  have F := Instant.extend b (t:=a (stowedEntryTy cl)) V
  have hk : D.StowedCover cl n l f x := ⟨h.transfer F,cherry (t:=a (stowedEntryTy cl)) b V,hI.transfer F⟩
  refine caseM ((h.stow_moves hx).weaken (Dom.of_le (fun i =>
    Nat.le_mul_of_pos_right _ (envelope_pos z _)))) (hk.patchRipple_moves hE)

end
section

-- modified from github.com/openai/math lean/OAI/Computability/FourierTransform/SynchronizedAlgorithm.lean (commit fd4aeeb, Apache-2.0)
/-
Derived from lean/OAI/Computability/FourierTransform/SynchronizedAlgorithm.lean of github.com/openai/math
(commit fd4aeeb, Apache-2.0), modified for this repository:
  * merged into this file with other modules, imports changed, some declarations renamed, comments removed;
  * OpenAI's fixed exponent `alpha = 1 - 2/10^11` and envelope `hills` are replaced, where they occur, by a
    general exponent with `envelope`, and OpenAI's `hills_program` by the hypothesis `hE : RippleEngine z`
    (Transform/EngineUse.lean; instance `rippleEngine_base` at `baseEngineExp = 1 - 7835230765108121/(2·10^18)`);
  * `axisKron` is written `AxisTensor.axisKron`, since the short name is shadowed in this environment;
  * proofs changed to match.
-/
open ReelKit
variable {m : Bool} {ι : Type U} {κ : Type V} {b : Bench m ι} {q : Bench m κ}
  {cl : Paint} {l d : ι → ℕ} {r : ι→Axes} {u : ι→ℕ→Stroke} {x : ι→Line} {z : ℝ} (hE : RippleEngine.{U} z)

namespace AxisStroke

include hE in
theorem mix_moves (h : b.AxisStroke l r u) (hI : b.Moves (fun _ => 0) sc fun _ => Complex.I)
    (hx : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (extent (r i) (l i)) (x i)) :
    b.Moves (fun i => extent (r i) (l i)*envelope z (l i)) (a (c cl)) fun i =>
      Tape.tab (extent (r i) (l i))
        (graft (extent (r i) (l i)) (AxisTensor.axisKron (r i) (fun j => leafC (u i j)) (l i)) (x i)) := by
  let n i := extent (r i) (l i)
  let V i := strokeBlocks (r i) (u i) (l i)
  let Y i := blockChips (n i) (V i)
  let D := b.extend (a chipTy) Y
  have F := Instant.extend b Y (t:=a chipTy)
  have hn : b.Nick n := ⟨hx.len h.fen.span,h.fen.span⟩
  have he : D.BlockCover n l V :=
    ⟨hn.transfer F,fun i => mosaic_quilt _ _ _ (h.fen.good i) (h.good i),
      cherry b Y (t:=a chipTy)⟩
  have hd : Dom (fun i => n i*envelope z (l i)) n :=
    Dom.of_le (fun i => Nat.le_mul_of_pos_right _ (envelope_pos z _))
  have ht := caseM (h.blocks_moves.weaken hd) (he.patchRipple_moves hE (hx.transfer F) (hI.transfer F))
  exact ht.congr fun i => tape_congr_sized fun j hj =>
    (mix_eq_patchRipple _ _ _ (h.fen.good i) (h.good i) _ _ hj).symm

include hE in
theorem beat_moves (h : b.AxisStroke l r u) (hI : b.Moves (fun _ => 0) sc fun _ => Complex.I)
    (hx : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (extent (r i) (l i)) (x i)) :
    b.Moves (fun i => extent (r i) (l i)*envelope z (l i)) (a (c cl)) fun i =>
      Tape.tab (extent (r i) (l i))
        (graft (extent (r i) (l i)) (AxisTensor.axisKron (r i) (fun j => leafC (u i j)) (l i))
          (graft (extent (r i) (l i)) (AxisTensor.axisKron (r i) (fun j => leafM (u i j)) (l i))
            (x i))) := by
  let n i := extent (r i) (l i)
  let f i := graft (n i) (AxisTensor.axisKron (r i) (fun j => leafM (u i j)) (l i)) (x i)
  let y i := Tape.tab (n i) (f i)
  let D := b.extend (a (c cl)) y
  have F := Instant.extend b y (t:=a (c cl))
  have ht := (h.transfer F).mix_moves hE (x:=f) (hI.transfer F)
    (cherry b y (t:=a (c cl)))
  exact caseM ((h.perm_moves cl x hx).weaken (Dom.of_le (fun i => Nat.le_mul_of_pos_right _
    (envelope_pos z _)))) ht
end AxisStroke

structure AxisReels (b : Bench m ι) (l d : ι→ℕ) (r : ι→Axes) (u : ι → ℕ → Reel) : Prop where
  fen : b.Fen l r
  beats : b.Nick d
  sounds : ∀ i, ∀ j<l i, (u i j).Sound (r i j)
  length : ∀ i, ∀ j<l i, (u i j).beats=d i
  atlas : b.Moves (fun _ => 0) (a treeTy) fun i =>
    Tape.tab (l i) fun j => treeT (r i j) (u i j)

variable {pV : ι → ℕ → Reel}
namespace AxisReels

lemma transfer {l d : κ→ℕ} {r : κ→Axes} {u : κ → ℕ→Reel} (h : q.AxisReels l d r u)
    {f} (g : b.Instant q f) :
    b.AxisReels (fun i => l (f i)) (fun i => d (f i)) (fun i => r (f i)) (fun i => u (f i)) :=
  ⟨h.fen.transfer g,h.beats.transfer g,fun _ => h.sounds _,fun _ => h.length _,
    h.atlas.transfer g⟩

lemma beat_axisStroke (h : b.AxisReels l d r pV) {t} (ht : b.Nick t) (hk : ∀ i,t i<d i) :
    b.AxisStroke l r (fun i j => (pV i j).atBeat (t i)) := by
  let T i j := treeT (r i j) (pV i j)
  let D := b.scan l
  have F := Instant.scan b l
  have hh (i : During l) : t i.i < (pV i.i i.j).beats := by rw [h.length _ _ i.hj]; exact hk _
  refine ⟨h.fen,fun i => h.sounds i.i i.j i.hj (t i.i) (hh i),?_⟩
  have hx := Moves.pick (t:=treeTy) (n:=fun i : During l => l i.i)
    (fun i => T i.i) (h.atlas.transfer F) (chop h.fen.high).close During.hj
  exact Moves.pick (t:=leafTy) (n:=fun i => (pV i.i i.j).beats) _ hx (ht.transfer F).close hh

include hE in

theorem run_moves (h : b.AxisReels l d r pV) (hI : b.Moves (fun _ => 0) sc fun _ => Complex.I)
    (hx : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (extent (r i) (l i)) (x i)) :
    b.Moves (fun i => d i* (extent (r i) (l i)*envelope z (l i)))
      (a (c cl)) fun i => Tape.tab (extent (r i) (l i))
        (axisRun (r i) (l i) (pV i) (x i) (d i)) := by
  let n i := extent (r i) (l i)
  let T i := axisRun (r i) (l i) (pV i) (x i)
  let A i j := Tape.tab (n i) (T i j)
  have F := Instant.climbs b d (t:=a (c cl)) A
  have ht := (h.transfer F).beat_axisStroke (stride h.beats (t:=a (c cl)) A) During.hj
  have he := ht.beat_moves hE (x:=fun i => T i.i i.j) (hI.transfer F) (tokenNow b d (t:=a (c cl)) A)
  have hu := repeatM h.beats A hx he (u:=fun i _ => n i*envelope z (l i)) (t:=a (c cl))
  refine hu.weaken ⟨2,fun i => ?_⟩
  have hh := Nat.le_mul_of_pos_right (d i) (Nat.mul_pos (h.fen.good i).extent_pos
    (envelope_pos z (l i)))
  simp only [sum_const,card_range,smul_eq_mul]
  unfold n
  omega

include hE in
theorem kron_moves (h : b.AxisReels l d r pV) (hI : b.Moves (fun _ => 0) sc fun _ => Complex.I)
    (hx : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (extent (r i) (l i)) (x i))
    (X : ι→ℕ→Wood) (hg : ∀ i, ∀ j<l i, Creates (pV i j) (r i j) (AxisTensor.frame _ (X i j))) :
    b.Moves (fun i => d i*(extent (r i) (l i)*envelope z (l i)))
      (a (c cl)) fun i => Tape.tab (extent (r i) (l i))
        (graft (extent (r i) (l i)) (AxisTensor.axisKron (r i) (X i) (l i)) (x i)) :=
  (h.run_moves hE hI hx).congr fun i =>
    tape_congr_sized fun j hj => axisRun_eq_kron (r i) (l i) (pV i) (h.fen.good i)
      (d i) (h.sounds i) (h.length i) (X i) (hg i) (x i) j hj

end AxisReels
end
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
