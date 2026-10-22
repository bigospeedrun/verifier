import Submission.OAI.Computability.FourierTransform.PowerTables
import Submission.OAI.Computability.FourierTransform.WorkingPreparation

/-! Merged module written by bos_merge.py for the 500-file limit of the Big O Speedrun
pull-request route.  It is the concatenation, in import order, of the 5 modules below; each one
is copied verbatim after its import header, inside `section` ... `end`, with the scopes it leaves
open closed before that `end`.  Members (module, sha256 of the original file):
* `Submission.OAI.Computability.FourierTransform.ArbitraryLength` 8c9294761c1be4bc5a243ce938ee7c1df76cb54c8eea0c114634dbdd7f3c82f1
* `Submission.OAI.Computability.FourierTransform.TransformProgram` fe75b6ba89030156c99566305a5418729c0f4d417f8ee832dcda0098b2c032a0
* `Submission.OAI.Computability.FourierTransform.ConvolutionProgram` 2ab7a81fc0375358e9eca43c06f000f64c6e049021e3a656e39265501aa4212e
* `Submission.OAI.Computability.FourierTransform.UniformBounds` 53dc0e4abf76b60c84bfa1e6068ccb1b08014c138f04ee39de0b6833db9aa9f1
* `Submission.OAI.Computability.FourierTransform.Asymptotics` 9c35f18f2b8812dcc78ff3150dbc2f8f046d76e3758a56c9db171926b8b8385b
-/

-- bos_merge: begin Submission.OAI.Computability.FourierTransform.ArbitraryLength
section

namespace OAI

/- The working length chirp algorithm. Broad branch. -/
namespace PowerSaving.RAM
open Ty Selection Spectral
noncomputable section
namespace Bench
universe U V
variable {ι : Type U} {κ : Type V} {m : Bool} {b : Bench m ι} {q : Bench m κ}
  {s t : Ty} {S n N : ι→ℕ} {ret : Bool}

def surf (d n s : ℕ) := n+leg n+(s+2)^d
lemma surf_deg (s n : ℕ) {c d : ℕ} (h : c≤d) : surf c n s ≤ surf d n s :=
  Nat.add_le_add_left (Small.pow_mono_degree _ h) _

def Swift (b : Bench m ι) (n S : ι→ℕ) (t : Ty) (x : ι→T t) : Prop :=
  ∃ d : ℕ,b.Moves (fun i => surf d (n i) (S i)) t x

namespace Swift
variable {x y : ι→T t}
lemma of_moves {W} (h : b.Moves W t x) (g : Dom n W) :
    b.Swift n S t x :=
  ⟨0,h.weaken ((Dom.of_le fun i => by unfold surf; omega).trans g)⟩
lemma of_dry (h : b.Dry S t x) : b.Swift n S t x :=
  let ⟨d,hd⟩ := h
  ⟨d, hd.mono fun _ => Nat.le_add_left _ _⟩
lemma pair {v : ι→T s} (h : b.Swift n S t x) (g : b.Swift n S s v) :
    b.Swift n S (p t s) fun i => (x i,v i) :=
  let ⟨d,hd⟩ := h
  let ⟨l,hl⟩ := g
  ⟨d+l, (hd.weaken (Dom.of_le fun i => surf_deg (S i) (n i) (by omega))).pair
    (hl.weaken (Dom.of_le fun i => surf_deg (S i) (n i) (by omega)))⟩
lemma bind {v : ι→T s} (h : b.Swift n S t x) (g : (b.extend t x).Swift n S s v) :
    b.Swift n S s v :=
  let ⟨d,hd⟩ := h
  let ⟨l,hl⟩ := g
  ⟨d+l, caseM (hd.weaken (Dom.of_le fun i => surf_deg (S i) (n i) (by omega)))
    (hl.weaken (Dom.of_le fun i => surf_deg (S i) (n i) (by omega)))⟩
end Swift

def tailVol (n : ℕ) : ℕ := (barge n).vol

structure Cruise (b : Bench m ι) (n S N : ι→ℕ) : Prop where
  dims : b.Neaps S n
  port : ∀ i, Ports (n i)
  rootP : b.Dry S sc fun i => root (receipt (n i))
  ac : ∀ i, tailVol (n i)=N i
  sizeL : b.Nick N

lemma signP (ret : Bool) (h : ∀ i,0<n i) (g : b.Dry S sc fun i => root (n i)) :
    b.Dry S sc fun i => pr ret (n i) := by
  cases ret
  · exact g
  · exact g.inv fun i => (root_primitive _ (h i)).ne_zero (Nat.ne_of_gt (h i))

lemma table_scale {x y : ι→Line} {cl} (h : b.Nick N)
    (hx : b.Moves (fun _ => 0) (a sc) fun i => Tape.tab (N i) (x i))
    (hy : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (N i) (y i)) :
    b.Moves N (a (c cl)) fun i => Tape.tab (N i) fun j => x i j*y i j := by
  have F := Instant.scan b N
  refine arrayNow h _ ((Moves.pick (t:=sc) (n:=fun i : During N => N i.i)
    (k:=During.j) (fun i j => x i.i j) (hx.transfer F) (chop h).close During.hj).mul
    (Moves.pick (t:=c cl) (n:=fun i : During N => N i.i) (k:=During.j) (fun i j => y i.i j)
      (hy.transfer F) (chop h).close During.hj))

namespace Cruise
variable {cl : Paint} {x y : ι→Line}

lemma transfer {S n N : κ→ℕ} (h : q.Cruise n S N) {f} (g : b.Instant q f) :
    b.Cruise (fun i => n (f i)) (fun i => S (f i)) (fun i => N (f i)) :=
  ⟨h.dims.transfer g,fun _ => h.port _,h.rootP.transfer g,fun _ => h.ac _,h.sizeL.transfer g⟩

lemma volume_ge (h : b.Cruise n S N) (i) : 2*n i ≤ N i :=
  h.ac i ▸ (barge_spec _ (h.dims.pos i)).lower
lemma volume_lt (h : b.Cruise n S N) (i) : N i < 4*n i :=
  h.ac i ▸ (barge_spec _ (h.dims.pos i)).upper
lemma volume_pos (h : b.Cruise n S N) (i) : 0<N i := by
  have hh := h.volume_ge i; have hk := h.dims.pos i; omega

lemma dom (h : b.Cruise n S N) : Dom n N :=
  ⟨4,fun i => by have := h.volume_lt i; omega⟩

lemma flood (h : b.Cruise n S N) (r : Bool)
    (hx : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (N i) (x i)) :
    b.Swift n S (a (c cl)) fun i => Tape.tab (N i) (freq (N i) (pr r (N i)) (x i)) := by
  let z (i) := pr r (N i)
  have H (i) : (barge (n i)).vol=N i := h.ac i
  have hu := signP r h.volume_pos ((h.dims.mediumP h.port h.rootP).congr fun i =>
    congrArg root (H i))
  obtain ⟨d,hd⟩ := h.dims.streamP h.port h.rootP (z:=z) (x:=x) hu
    (fun i => (H i).symm ▸ show IsPrimitiveRoot (z i) (N i) from primitive_pr _ (h.volume_pos i) r)
    (hx.congr fun i => congrArg (fun u => Tape.tab u (x i)) (H i).symm)
  refine ⟨d,?_⟩
  refine (hd.weaken (Dom.of_le fun i => ?_)).congr fun i => ?_
  · unfold surf; omega
  · rw [H]

lemma flood' (h : b.Cruise n S N) (r : Bool) (hx : b.Swift n S (a (c cl)) fun i =>
    Tape.tab (N i) (x i)) :
    b.Swift n S (a (c cl)) fun i => Tape.tab (N i) (freq (N i) (pr r (N i)) (x i)) := by
  let V (i : ι) : T (a (c cl)) := Tape.tab (N i) (x i)
  exact hx.bind ((h.transfer (Instant.extend b V)).flood r (x:=x) (cherry b V (t:=a (c cl))))

lemma posts (h : b.Cruise n S N) (r : Bool) :
    b.Swift n S (a sc) fun i => tablePow (pr r (2*n i)) (S i) := by
  let z (i) : T sc := pr r (2*n i)
  have hh : b.Swift n S sc z :=
    Swift.of_dry (signP r (fun i => by have := h.dims.pos i; omega)
      (h.dims.etaP h.port h.rootP))
  have F := Instant.extend b z (t:=sc)
  exact hh.bind (Swift.of_moves (pylon (h.dims.tidal.transfer F)
    (g:=h.dims.stackPow) (cherry b z (t:=sc))) ⟨4,fun i => by
    dsimp only [id]
    have hh : 2^S i ≤ 4*n i := h.dims.stack_eq i ▸ stack_pow (n i) (h.dims.pos i); omega⟩)

lemma pearl (h : b.Cruise n S N) (r : Bool)
    (hp : b.Moves (fun _ => 0) (a sc) fun i => tablePow (pr r (2*n i)) (S i))
    {k} (hk : b.Nick k) :
    b.Moves (fun _ => 0) sc fun i => epschirp (pr r (2*n i)) (k i) :=
  square_pow h.dims.stackPow hp ((Nick.wc 2).mul h.dims.num)
    (fun i => ⟨by have := h.dims.pos i; omega,h.dims.stack_eq i ▸ (stack_above (n i)).le⟩)
    (fun i => (primitive_pr (2*n i) (by have := h.dims.pos i; omega) r).pow_eq_one) hk

-- two prep arrays
lemma risen (h : b.Cruise n S N) (r : Bool)
    (hp : b.Moves (fun _ => 0) (a sc) fun i => tablePow (pr r (2*n i)) (S i))
    (hx : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (n i) (x i)) :
    b.Swift n S (a (c cl)) fun i => Tape.tab (N i) (chirp_seed (n i) (pr r (2*n i)) (x i)) := by
  have F := Instant.scan b N
  have hh := h.transfer F
  have hj := chop h.sizeL
  have H := (hh.pearl r (hp.transfer F) hj).mul (pick_all (t:=c cl)
    (n:=fun i : During N => n i.i) (fun (i : During N) j => x i.i j) (hx.transfer F) hj)
  refine Swift.of_moves (arrayNow h.sizeL _ (H.congr fun i => ?_)) h.dom
  simp only [chirp_seed,mul_ite]; congr 1
  exact mul_zero _

lemma fallen (h : b.Cruise n S N) (r : Bool)
    (hp : b.Moves (fun _ => 0) (a sc) fun i => tablePow (pr r (2*n i)) (S i)) :
    b.Swift n S (a sc) fun i => Tape.tab (N i) (fall (n i) (N i) (pr r (2*n i))) := by
  let z i := pr r (2*n i)
  have F := Instant.scan b N
  have hh := h.transfer F
  have hj := chop h.sizeL
  have hg := hh.sizeL.sub hj
  have hk := (((hj.cmp hh.dims.num).branch hg hj)).congr
    (y:=fun i => legdist (n i.i) (N i.i) i.j) (fun i => by
    by_cases e : i.j < n i.i <;> simp [legdist,e])
  refine Swift.of_moves (arrayNow h.sizeL _ ((hh.pearl r (hp.transfer F) hk).inv fun i => ?_)) h.dom
  have Hu : 0<2*n i.i := by have := h.dims.pos i.i; omega
  exact pow_ne_zero _ ((primitive_pr _ Hu r).ne_zero (Nat.ne_of_gt Hu))

lemma pyramid (h : b.Cruise n S N) (r : Bool)
    (hp : b.Moves (fun _ => 0) (a sc) fun i => tablePow (pr r (2*n i)) (S i))
    (hx : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (n i) (x i)) :
    b.Swift n S (a (c cl)) fun i =>
      Tape.tab (N i) (fetchC (N i) (pr false (N i))
        (fall (n i) (N i) (pr r (2*n i)))
        (chirp_seed (n i) (pr r (2*n i)) (x i))) := by
  let z i := pr r (2*n i)
  let A i := freq (N i) (pr false (N i)) (fall (n i) (N i) (z i))
  let B i := freq (N i) (pr false (N i)) (chirp_seed (n i) (z i) (x i))
  let V (i) : T (p (a sc) (a (c cl))) := (Tape.tab (N i) (A i),Tape.tab (N i) (B i))
  have H := (h.flood' false (h.fallen r hp)).pair (h.flood' false (h.risen r hp hx))
  have F := Instant.extend b V
  have hk := cherry b V (W:=fun _ => 0)
  exact h.flood' true (x:=fun i => pointC (N i) (pr false (N i))
        (fall (n i) (N i) (z i)) (chirp_seed (n i) (z i) (x i)))
    (H.bind (Swift.of_moves (table_scale (h.sizeL.transfer F) (x:=A) (y:=B) hk.fst hk.snd) h.dom))

lemma singing (h : b.Cruise n S N) (r : Bool)
    (hp : b.Moves (fun _ => 0) (a sc) fun i => tablePow (pr r (2*n i)) (S i))
    (hx : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (n i) (x i)) :
    b.Swift n S (a (c cl)) fun i =>
      Tape.tab (n i) (freq (n i) (pr r (n i)) (x i)) := by
  let z i := pr r (2*n i)
  let B i := fetchC (N i) (pr false (N i)) (fall (n i) (N i) (z i))
    (chirp_seed (n i) (z i) (x i))
  have H := Swift.pair (h.pyramid r hp hx) (Swift.of_moves h.sizeL.numeralM h.dom)
  let V (i : ι) : T (p (a (c cl)) sc) := (Tape.tab (N i) (B i),(N i:ℂ))
  have F := Instant.extend b V
  have G := Instant.scan (b.extend _ V) n
  have hh := h.transfer (G.next F)
  have hk := Moves.transfer (cherry b V (W:=fun _ => 0)) G
  have hj := h.dims.num.transfer F
  have HL := chop hj
  have HS := Moves.pick (n:=fun i : During n => N i.i) (k:=During.j) (t:=c cl)
    (fun i => B i.i) hk.fst HL.close (fun i => by
      have hh := h.volume_ge i.i; have hk := i.hj; omega)
  have hd := (hh.pearl r (hp.transfer (G.next F)) HL).mul
    ((hk.snd.inv fun i => Nat.cast_ne_zero.mpr (Nat.ne_of_gt (h.volume_pos i.i))).mul HS)
  exact H.bind (Swift.of_moves (arrayNow hj _ (hd.congr fun i =>
    chirps _ _ (h.dims.pos i.i) (h.volume_ge i.i) r _ _ i.hj)) (Dom.self n))

lemma deliver (h : b.Cruise n S N) (r : Bool)
    (hx : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (n i) (x i)) :
    b.Swift n S (a (c cl)) fun i =>
      Tape.tab (n i) (freq (n i) (pr r (n i)) (x i)) := by
  let V i := tablePow (pr r (2*n i)) (S i)
  have F := Instant.extend b V (t:=a sc)
  exact (h.posts r).bind ((h.transfer F).singing r (cherry b V (t:=a sc)) (hx.transfer F))

end Cruise

lemma Neaps.swift (h : b.Neaps S n) (g : ∀ i,Ports (n i))
    (hz : b.Dry S sc fun i => root (receipt (n i))) (r : Bool)
    {x : ι→Line} {cl} (hx : b.Moves (fun _ => 0) (a (c cl)) fun i =>
      Tape.tab (n i) (x i)) :
    b.Swift n S (a (c cl)) fun i =>
      Tape.tab (n i) (freq (n i) (pr r (n i)) (x i)) := by
  let N i := tailVol (n i)
  have F := Instant.extend b N (t:=w)
  have hh : (b.extend w N).Cruise n S N :=
    ⟨h.transfer F,g,hz.transfer F,fun i => rfl,⟨cherry b N (t:=w),h.bargeL.volume⟩⟩
  exact (Swift.of_dry h.bargeL.volL.dry).bind (hh.deliver r (hx.transfer F))

end Bench
end
end PowerSaving.RAM

end OAI

end
-- bos_merge: end Submission.OAI.Computability.FourierTransform.ArbitraryLength

-- bos_merge: begin Submission.OAI.Computability.FourierTransform.TransformProgram
section

namespace OAI

/- All-length including direct initial. -/
namespace PowerSaving.RAM
open Ty Selection Spectral Finset
noncomputable section
namespace Bench
universe U V
variable {ι : Type U} {κ : Type V} {m : Bool} {b : Bench m ι} {q : Bench m κ}
  {s t : Ty} {n N k : ι→ℕ} {ret : Bool}

lemma Dry.linearPow (h : b.Grain N k) (g : Small N k) {z : ι→ℂ} (hz : b.Dry N sc z) :
    b.Dry N sc fun i => z i^k i := by
  let V (i : ι) (j : ℕ) : T sc := z i^j
  have F := Instant.climbs b k V (t:=sc)
  refine cycleG h g V (one.congr fun i => (pow_zero _).symm)
    (((Dry.token b k N V (t:=sc)).mul (hz.transfer F)).congr fun i => (pow_succ _ _).symm)

-- polynomial direct branch, N^d
lemma Dry.dire (h : b.Nick N)
    {x : ι→Line} {cl} (hx : b.Dry N (a (c cl)) fun i => Tape.tab (N i) (x i))
    {z : ι→ℂ} (hz : b.Dry N sc z) :
    b.Dry N (a (c cl)) fun i => Tape.tab (N i) (freq (N i) (z i) (x i)) := by
  let D := b.scan N
  have H := Small.self N
  have F := Instant.scan b N
  let K (i : During N) := N i.i
  let V (i : During N) (j : ℕ) : T (c cl) :=
    ∑ k ∈ range j, z i.i^(i.j*k)*x i.i k
  have hk : D.Grain K K := (h.transfer F).grain _
  have G := Instant.climbs D K V (t:=c cl)
  have hj := ((chop h).grain K).transfer G
  have hp := strideG hk V
  have hA : Small (fun i : During K => K i.i) fun i => i.i.j*i.j :=
    (((Small.self K).pow 2).reindex _).mono fun i => by
      rw [pow_two]
      exact Nat.mul_le_mul i.i.hj.le i.hj.le
  have ht := (linearPow (hj.mul hp) hA (hz.transfer (G.next F))).mul
    (Dry.pick (t:=c cl) (x:=fun (i : During K) j => x i.i.i j)
      (n:=fun i : During K => N i.i.i) (k:=During.j)
      (hx.transfer (G.next F)) hp.dry During.hj)
  exact arrayG (h.grain N) H _ (cycleG hk (Small.self K) V (by
    simp only [V,range_zero,sum_empty]; exact PolyCan.zero)
    (Dry.congr (b:=D.climbs K _ V) (S:=fun (i : During K) => K i.i) (t:=c cl)
      (PolyCan.add (Dry.token D K K V (t:=c cl)) ht) fun i => (sum_range_succ ..).symm))

def fairwind (d n : ℕ) := surf d n (stackN n) +
  (if Ports n then 0 else (n+2)^d)

lemma fairwind_deg {c d : ℕ} (n : ℕ) (h : c≤d) : fairwind c n≤fairwind d n := by
  unfold fairwind
  refine add_le_add (surf_deg _ _ h) ?_
  split
  · exact le_rfl
  · exact Small.pow_mono_degree n h
lemma fairwind_left (n d : ℕ) : n + (stackN n+2)^d ≤ fairwind d n := by unfold fairwind surf; omega
lemma fairwind_n (n d : ℕ) : n≤fairwind d n := (Nat.le_add_right _ _).trans (fairwind_left n d)

def Breezy (b : Bench m ι) (n : ι→ℕ) (t : Ty) (x : ι→T t) : Prop :=
  ∃ d : ℕ,b.Moves (fun i => fairwind d (n i)) t x

namespace Breezy
variable {x y : ι→T t}
lemma of_moves {W} (h : b.Moves W t x) (g : Dom n W) : b.Breezy n t x :=
  ⟨0,h.weaken ((Dom.of_le fun i => fairwind_n (n i) 0).trans g)⟩
lemma congr (h : b.Breezy n t x) (g : ∀ i, x i=y i) : b.Breezy n t y :=
  let ⟨d,hd⟩ := h
  ⟨d,hd.congr g⟩
lemma pair {v : ι→T s} (h : b.Breezy n t x) (g : b.Breezy n s v) :
    b.Breezy n (p t s) fun i => (x i,v i) :=
  let ⟨d,hd⟩ := h
  let ⟨l,hl⟩ := g
  ⟨d+l, (hd.weaken (Dom.of_le fun i => fairwind_deg (n i) (by omega))).pair
    (hl.weaken (Dom.of_le fun i => fairwind_deg (n i) (by omega)))⟩
lemma bind {v : ι→T s} (h : b.Breezy n t x) (g : (b.extend t x).Breezy n s v) :
    b.Breezy n s v :=
  let ⟨d,hd⟩ := h
  let ⟨l,hl⟩ := g
  ⟨d+l, caseM (hd.weaken (Dom.of_le fun i => fairwind_deg (n i) (by omega)))
    (hl.weaken (Dom.of_le fun i => fairwind_deg (n i) (by omega)))⟩
lemma flagtest {f : ι→ℕ} (h : b.Breezy n w f)
    (g : (b.along (Subtype.val (p:=fun i => f i = 0))).Breezy (fun i => n i.val) t fun i => x i.val)
    (j : (b.along (Subtype.val (p:=fun i => f i ≠ 0))).Breezy (fun i => n i.val) t fun i => x i.val) :
    b.Breezy n t x := by
  obtain ⟨d,hd⟩ := h
  obtain ⟨l,hl⟩ := g
  obtain ⟨k,hk⟩ := j
  let s := d+l+k
  refine ⟨s,Can.testz (W:=fun i => fairwind s (n i)) (n:=f) ?_ ?_ ?_⟩
  · exact Can.mono hd (fun i => fairwind_deg _ (by unfold s; omega))
  · exact Can.mono hl (fun i => fairwind_deg _ (by unfold s; omega))
  · exact Can.mono hk (fun i => fairwind_deg _ (by unfold s; omega))
end Breezy

lemma Neaps.course (h : b.Neaps (fun i => stackN (n i)) n)
    (hz : b.Moves (fun _ => 0) sc fun i => root (receipt (n i)))
    (r : Bool) {x : ι→Line} {cl} (hx : b.Moves (fun _ => 0) (a (c cl)) fun i =>
      Tape.tab (n i) (x i)) :
    b.Breezy n (a (c cl)) fun i => Tape.tab (n i) (freq (n i) (pr r (n i)) (x i)) := by
  let f (i : ι) := if Ports (n i) then 0 else 1
  have HH : b.Breezy n w f := by
    obtain ⟨d,hd⟩ := h.portG.dry
    exact ⟨d,hd.mono fun i => (Nat.le_add_left _ _).trans (fairwind_left _ d)⟩
  refine Breezy.flagtest HH ?_ ?_
  · let P i := f i=0
    have F := Instant.along b (Subtype.val (p:=P))
    have hp : ∀ i : Subtype P, Ports (n i.val) := fun i => by
      by_contra k; have hi : f i.val=0 := i.property; simp [f,k] at hi
    obtain ⟨d,hd⟩ := (h.transfer F).swift hp ((hz.transfer F).dunes _) r (hx.transfer F)
    exact ⟨d,hd.weaken (Dom.of_le fun i => Nat.le_add_right _ _)⟩
  · let P i := f i≠0
    have F := Instant.along b (Subtype.val (p:=P))
    have hp : ∀ i : Subtype P, ¬ Ports (n i.val) := fun i g => i.property (by simp [f,g])
    let H := h.transfer F
    have ht := signP r H.pos ((hz.transfer F).dunes (fun i => n i.val) |>.congr
      (y:=fun i : Subtype P => root (n i.val)) fun i => by rw [receipt,ite_eq_right (hp i)])
    obtain ⟨d,hd⟩ := Dry.dire H.num ((hx.transfer F).dunes _) ht
    exact ⟨d,Can.mono hd (fun i => by unfold fairwind; rw [ite_eq_right (hp i)]; exact Nat.le_add_left _ _)⟩

lemma Nick.landOrder (h : b.Nick N) (g : ∀ i, 0<N i) :
    b.Breezy N w fun i => receipt (N i) :=
  let ⟨d,hd⟩ := h.planOrder g
  ⟨d, hd.weaken (Dom.of_le fun i => fairwind_left (N i) d)⟩
lemma Nick.land (h : b.Nick N) (g : ∀ i, 0<N i)
    (hz : b.Moves (fun _ => 0) sc fun i => root (receipt (N i)))
    (r : Bool) {x : ι→Line} {cl} (hx : b.Moves (fun _ => 0) (a (c cl)) fun i =>
      Tape.tab (N i) (x i)) :
    b.Breezy N (a (c cl)) fun i => Tape.tab (N i) (freq (N i) (pr r (N i)) (x i)) := by
  obtain ⟨hu,hk⟩ := h.stackH g
  have H := Instant.extend b (fun i => stackN (N i)) (t:=w)
  exact (Breezy.of_moves hu (Dom.self N)).bind (hk.course (hz.transfer H) r (hx.transfer H))
lemma Nick.land' (h : b.Nick N) (g : ∀ i, 0<N i)
    (hz : b.Moves (fun _ => 0) sc fun i => root (receipt (N i)))
    (r : Bool) {x : ι→Line} {cl} (hx : b.Breezy N (a (c cl)) fun i =>
      Tape.tab (N i) (x i)) :
    b.Breezy N (a (c cl)) fun i => Tape.tab (N i) (freq (N i) (pr r (N i)) (x i)) := by
  let V (i : ι) : T (a (c cl)) := Tape.tab (N i) (x i)
  have F := Instant.extend b V (t:=a (c cl))
  exact hx.bind ((h.transfer F).land g (hz.transfer F) r (x:=x) (cherry b V (t:=a (c cl))))
end Bench
end
end PowerSaving.RAM

end OAI

end
-- bos_merge: end Submission.OAI.Computability.FourierTransform.TransformProgram

-- bos_merge: begin Submission.OAI.Computability.FourierTransform.ConvolutionProgram
section

namespace OAI

/- All-length bilinear convolution. -/
namespace PowerSaving
open RAM Ty Selection Spectral Finset
noncomputable section

-- correspondence lemma for polynomials in dense coefficient representation
def polyOf (n : ℕ) (x : Vec n) : Polynomial ℂ :=
  ∑ i : Fin n, Polynomial.monomial i.val (x i)

lemma polyOf_mul (n : ℕ) (x y : Vec n) :
    polyOf (2*n-1) (conv n x y)=polyOf n x * polyOf n y := by
  open Polynomial in
    simp only [polyOf,conv,map_sum,sum_mul,mul_sum,monomial_mul_monomial]
  let q (k : Fin (2*n-1)) (r s : Fin n) :=
    Polynomial.monomial k.val (if r.val+s.val=k.val then x r*y s else 0)
  change ∑ k,∑ r,∑ s,q k r s=_
  rw [sum_comm]
  conv_rhs => rw [sum_comm]
  refine sum_congr rfl ?_
  intro i _
  rw [sum_comm]
  refine sum_congr rfl ?_
  intro j _
  let k : Fin (2*n-1) := ⟨i.val+j.val,by have := i.isLt; have := j.isLt; omega⟩
  rw [sum_eq_single k]
  · simp [q,k]
  · intro b _ hb
    have H : i.val+j.val≠b.val := fun hg => hb (Fin.ext hg.symm)
    simp [q,H]
  · simp

lemma polyOf_coeff_exact (n : ℕ) (x : Polynomial ℂ) (hx : x.natDegree<n) :
    polyOf n (fun i => x.coeff i.val)=x := by
  rw [polyOf,Fin.sum_univ_eq_sum_range (fun j => Polynomial.monomial j (x.coeff j)) n]
  exact (Polynomial.as_sum_range' x n hx).symm

namespace RAM.Bench
universe U V
variable {ι : Type U} {κ : Type V} {b : Bench true ι} {n N : ι→ℕ}

lemma crossT (h : b.Nick N) {x y : ι→Line}
    (hx : b.Moves (fun _ => 0) (a (c Paint.left)) fun i => Tape.tab (N i) (x i))
    (hy : b.Moves (fun _ => 0) (a (c Paint.right)) fun i => Tape.tab (N i) (y i)) :
    b.Moves N convOutKind fun i => Tape.tab (N i) fun j => x i j*y i j := by
  have F := Instant.scan b N
  refine arrayNow h _ (Can.cross
    (Moves.pick (t:=c Paint.left) (n:=fun i : During N => N i.i)
      (k:=During.j) (fun i j => x i.i j) (hx.transfer F) (chop h).close During.hj)
    (Moves.pick (t:=c Paint.right) (n:=fun i : During N => N i.i) (k:=During.j) (fun i j => y i.i j)
      (hy.transfer F) (chop h).close During.hj))

def stretch (n : ℕ) := 2*n-1

lemma stretch_pos {n : ℕ} (h : 0<n) : 0<stretch n := by unfold stretch; omega

lemma fusing (h : b.Nick n) (g : ∀ i, 0<n i) {x y : ι→Line}
    (hx : b.Moves (fun _ => 0) (a (c Paint.left)) fun i => Tape.tab (n i) (x i))
    (hy : b.Moves (fun _ => 0) (a (c Paint.right)) fun i => Tape.tab (n i) (y i))
    (hz : b.Moves (fun _ => 0) sc fun i => root (receipt (stretch (n i)))) :
    b.Breezy (fun i => stretch (n i)) convOutKind fun i => Tape.tab (stretch (n i))
      (cyclic (stretch (n i)) (padline (n i) (y i)) (padline (n i) (x i))) := by
  let N i := stretch (n i)
  let U i := padline (n i) (x i)
  let V i := padline (n i) (y i)
  let X i := freq (N i) (pr false (N i)) (U i)
  let Y i := freq (N i) (pr false (N i)) (V i)
  have H : b.Nick N := ((Nick.wc 2).mul h).sub (Nick.wc 1)
  have he : ∀ i,0<N i := fun i => stretch_pos (g i)
  have Hp := H.land' he hz false (Breezy.of_moves (padM h H hx) (Dom.self N))
  have Hq := H.land' he hz false (Breezy.of_moves (padM h H hy) (Dom.self N))
  let f (i : ι) : T (p (a (c Paint.left)) (a (c Paint.right))) :=
    (Tape.tab (N i) (X i),Tape.tab (N i) (Y i))
  have F := Instant.extend b f
  have Hb := cherry b f (W:=fun _ => 0)
  let A i := pointC (N i) (pr false (N i)) (U i) (V i)
  let B i := freq (N i) (pr true (N i)) (A i)
  have ha := H.land' he hz true (x:=A)
    ((Hp.pair Hq).bind (Breezy.of_moves (crossT (H.transfer F) (x:=X) (y:=Y) Hb.fst Hb.snd)
      (Dom.self N)))
  have hb := ha.pair (Breezy.of_moves H.numeralM (Dom.self N))
  let gg (i : ι) : T (p convOutKind sc) := (Tape.tab (N i) (B i),(N i:ℂ))
  have G := Instant.extend b gg
  have HH := H.transfer G
  have J := Instant.scan (b.extend _ gg) N
  have hj := Moves.transfer (cherry b gg (W:=fun _ => 0)) J
  have h1 := Moves.pick (t:=c Paint.both) (n:=fun i : During N => N i.i)
    (k:=During.j) (fun i => B i.i) hj.fst (chop HH).close During.hj
  have h2 := hj.snd.inv fun i => Nat.cast_ne_zero.mpr (Nat.ne_of_gt (he i.i))
  exact hb.bind (Breezy.of_moves (arrayNow HH _ ((h2.mul h1).congr (fun i =>
    freq_pad_row (n i.i) _ _ _ i.hj))) (Dom.self N))
end RAM.Bench

end
end PowerSaving

end OAI

end
-- bos_merge: end Submission.OAI.Computability.FourierTransform.ConvolutionProgram

-- bos_merge: begin Submission.OAI.Computability.FourierTransform.UniformBounds
section

namespace OAI

/- Static allowance to programs. -/
namespace PowerSaving
open RAM Ty Selection Spectral Slant
noncomputable section

namespace RAM.Bench
universe U
variable {ι : Type U} {κ : Type*} {m : Bool} {b : Bench m ι}
  {n : ι→ℕ} {t : Ty}

lemma fairwind_small (N : ι→ℕ) (hn : ∀ i,0<N i) (d : ℕ) :
    Small N fun i => fairwind d (N i) := by
  have H := Small.self N
  have hX i := barge_spec (N i) (hn i)
  have h4 := (Small.const _ 4).mul H
  have hu := h4.mono (fun (i : ι) => stack_le (N i) (hn i))
  have hk : Small N fun i => harvestN (N i) :=
    (((Small.const _ 16).mul (hu.add (Small.const _ 4))).pow 2)
  have hh := ((Small.const _ 8).mul hk).mono
    (fun i => Nat.lt_two_pow_self.le.trans (orderE_small (N i)))
  have hi := ((((Small.const _ 20000000).mul ((hh.add (Small.const _ 1)).pow 2)).add
    (Small.const _ 7))).mono (fun i => score_le (orderE (N i)))
  have hp : Small N fun i => hills (barge (N i)).l :=
    (hu.add (Small.const _ 1)).mono fun i => (hills_le _).trans
      (Nat.add_le_add_right (hX i).count _)
  have hj := (hi.add (Small.const _ 1)).mul
    ((h4.mono fun i => (hX i).upper.le).mul hp)
  have hl := H.add hj |>.add ((hu.add (Small.const _ 2)).pow d)
  exact hl.add (((H.add (Small.const _ 2)).pow d).mono fun i => by split <;> omega)

-- package extracted charges
abbrev Sizes := {n : ℕ // 0<n}
abbrev entry : Sizes→ℕ := Subtype.val

structure Ration where
  d : ℕ
  c : ℕ
  p : ℕ
def calorie (a : Ration) (n : ℕ) := a.c*(fairwind a.d n+1)

lemma Breezy.ration {x : ι→T t} (h : b.Breezy n t x) :
    ∃ (s : Prog m b.tray t) (a : Ration), ∀ i,
      (run s (b.env i)).OK (x i) (calorie a (n i)) ((b.size i+2)^a.p) := by
  obtain ⟨d,hd⟩ := h
  obtain ⟨s,c,p,hc⟩ := Can.unfold_bound hd
  exact ⟨s,⟨d,c,p⟩,hc⟩

def lunch (a b : Ration) (N : ℕ→ℕ) (n : ℕ) :=
  calorie a (N n)+1+calorie b (N n)

lemma storehouse (N : ℕ→ℕ) (h : ∀ n,0<n → 0<N n) (g : Small entry (fun i => N (entry i)))
    (a b : Ration) : ∃ c : ℕ, ∀ n : ℕ, 0<n →
    let cap := (n+2)^c
    lunch a b N n + 10*(n+2) ≤ cap ∧ (n+2)^a.p ≤ cap ∧ (n+2)^b.p ≤ cap ∧
    receipt (N n) ≤ cap := by
  let M i := N (entry i)
  have H (a : Ration) : Small entry (fun i => calorie a (M i)) :=
    (Small.const _ a.c).mul (((fairwind_small M (fun i => h _ i.property) a.d).trans g).add
      (Small.const _ 1))
  have hu := (Small.self entry).add (Small.const _ 2)
  have hh := (Small.const _ 10).mul hu
  have hp := ((Small.const _ 8).mul (g.pow 3)).mono
    (fun i => (receipt_bound _ (h _ i.property)).2.le)
  have ht := ((((H a).add (Small.const _ 1)).add (H b)).add hh)
  obtain ⟨c,hc⟩ := (((ht.max (hu.pow a.p)).max (hu.pow b.p)).max hp)
  refine ⟨c,fun n hn => ?_⟩
  specialize hc (⟨n,hn⟩:Sizes)
  have hx :
      max (max (max (lunch a b N n + 10*(n+2)) ((n+2)^a.p)) ((n+2)^b.p)) (receipt (N n)) ≤
        (n+2)^c := hc
  have h1 := max_le_iff.mp hx
  have h2 := max_le_iff.mp h1.1
  have h3 := max_le_iff.mp h2.1
  exact ⟨h3.1,h3.2,h2.2,h1.2⟩

-- order environments
def onlyLength : Bench false Sizes := ⟨entry,w,entry⟩
lemma onlyLength_num : onlyLength.Nick entry := ⟨Can.id,Small.self _⟩

lemma orders1 : ∃ (s : Prog false w w) (a : Ration), ∀ n,0<n →
    (run s n).OK (receipt n) (calorie a n) ((n+2)^a.p) := by
  obtain ⟨s,a,ha⟩ := (onlyLength_num.landOrder (fun i => i.property)).ration
  exact ⟨s,a,fun i hi => ha ⟨i,hi⟩⟩
lemma orders2 : ∃ (s : Prog false w w) (a : Ration), ∀ n,0<n →
    (run s n).OK (receipt (stretch n)) (calorie a (stretch n)) ((n+2)^a.p) := by
  have H : onlyLength.Nick fun i => stretch (entry i) :=
    ((Nick.wc 2).mul onlyLength_num).sub (Nick.wc 1)
  obtain ⟨s,a,ha⟩ := (H.landOrder (fun i => stretch_pos i.property)).ration
  exact ⟨s,a,fun i hi => ha ⟨i,hi⟩⟩

def towerOne : Bench false (Sizes×Line) :=
  ⟨fun i => entry i.1,dftInKind,fun i =>
    (entry i.1, root (receipt (entry i.1)),Tape.tab (entry i.1) i.2)⟩

lemma executeOne : ∃ (s : Prog false dftInKind dftOutKind) (a : Ration),
    ∀ (n : ℕ),0<n → ∀ x : Vec n,
    (run s (n, root (receipt n), (⟨n,x⟩ : Tape ℂ))).OK
      (⟨n, dft n x⟩ : Tape ℂ) (calorie a n) ((n+2)^a.p) := by
  let K := towerOne
  have ht : K.Moves (fun _ => 0) dftInKind K.env := envNow K
  let n (i : Sizes × Line) := entry i.1
  have hk : K.Nick n := ⟨ht.fst,Small.self _⟩
  have H := hk.land (fun i => i.1.property) (ht.snd.fst) false (x:=Prod.snd) (cl:=Paint.left)
    (ht.snd.snd)
  obtain ⟨s,a,ha⟩ := H.ration
  refine ⟨s,a,fun n hn x => ?_⟩
  specialize ha ((⟨n,hn⟩:Sizes),extendLine x)
  change (run s (n,root (receipt n),(⟨n,front n (extendLine x)⟩:Tape ℂ))).OK
    (⟨n,front n (freq n (pr false n) (extendLine x))⟩ : Tape ℂ) _ _ at ha
  rw [← dft_front n,front_exact] at ha
  exact ha

def towerBoth : Bench true (Sizes×Line×Line) :=
  ⟨fun i => entry i.1,convInKind,fun i =>
    (entry i.1, root (receipt (stretch (entry i.1))),Tape.tab (entry i.1) i.2.1,
      Tape.tab (entry i.1) i.2.2)⟩

lemma executeBoth : ∃ (s : Prog true convInKind convOutKind) (a : Ration),
    ∀ (n : ℕ),0<n → ∀ x y : Vec n,
    (run s (n, root (receipt (stretch n)), (⟨n,x⟩ : Tape ℂ),(⟨n,y⟩ : Tape ℂ))).OK
      (⟨stretch n, conv n x y⟩ : Tape ℂ) (calorie a (stretch n)) ((n+2)^a.p) := by
  let K := towerBoth
  have ht : K.Moves (fun _ => 0) convInKind K.env := envNow K
  let n (i : Sizes × Line×Line) := entry i.1
  have hk : K.Nick n := ⟨ht.fst,Small.self _⟩
  have H := fusing hk (fun i => i.1.property) (x:=fun i => i.2.1) (y:=fun i => i.2.2)
    ht.snd.snd.fst ht.snd.snd.snd ht.snd.fst
  obtain ⟨s,a,ha⟩ := H.ration
  refine ⟨s,a,fun n hn x y => ?_⟩
  specialize ha ((⟨n,hn⟩:Sizes),extendLine x,extendLine y)
  change (run s (n,root (receipt (stretch n)),
    (⟨n,front n (extendLine x)⟩:Tape ℂ),(⟨n,front n (extendLine y)⟩:Tape ℂ))).OK
    (⟨2*n-1,front (2*n-1)
      (cyclic (2*n-1) (padline n (extendLine y)) (padline n (extendLine x)))⟩ : Tape ℂ) _ _ at ha
  rw [cyclic_pad_front,front_exact,front_exact] at ha
  exact ha

theorem flagshipOne : ∃ order solve a b,
    DFTProgram order solve (lunch a b id) ∧
    ∀ n, 0<n → (run order n).val = receipt n := by
  obtain ⟨o,a,ho⟩ := orders1
  obtain ⟨s,b,hs⟩ := executeOne
  obtain ⟨c,hc⟩ := storehouse id (fun _ h => h) (Small.self entry) a b
  refine ⟨o,s,a,b,⟨c,fun n hn => ?_⟩,fun n hn => (ho n hn).result⟩
  obtain ⟨hu,hA,hB,hR⟩ := hc n hn
  have H := ho n hn
  have HH := receipt_bound n hn
  have he := H.result
  refine ⟨hu,H.bound.trans hA,H.valid,he.symm ▸ HH.1,he.symm ▸ ?_,he.symm ▸ hR,fun x => ?_⟩
  · exact HH.2.trans_le (by omega)
  dsimp only
  rw [he]
  have hj := hs n hn x
  exact ⟨hj.valid,hj.bound.trans hB,add_le_add (add_le_add_left H.time 1) hj.time,hj.result⟩

theorem flagshipBoth : ∃ order solve a b,
    ConvProgram order solve (lunch a b stretch) ∧
    ∀ n, 0<n → (run order n).val = receipt (stretch n) := by
  obtain ⟨o,a,ho⟩ := orders2
  obtain ⟨s,b,hs⟩ := executeBoth
  obtain ⟨c,hc⟩ := storehouse stretch (fun _ h => stretch_pos h)
    (((Small.const _ 2).mul (Small.self entry)).sub (Q:=fun _ => 1)) a b
  refine ⟨o,s,a,b,⟨c,fun n hn => ?_⟩,fun n hn => (ho n hn).result⟩
  obtain ⟨hu,hA,hB,hR⟩ := hc n hn
  have H := ho n hn
  have HH := receipt_bound _ (stretch_pos hn)
  have he := H.result
  refine ⟨hu,H.bound.trans hA,H.valid,he.symm ▸ HH.1,he.symm ▸ ?_,he.symm ▸ hR,fun x y => ?_⟩
  · exact HH.2.trans_le (by unfold stretch; omega)
  dsimp only
  rw [he]
  have hj := hs n hn x y
  exact ⟨hj.valid,hj.bound.trans hB,add_le_add (add_le_add_left H.time 1) hj.time,hj.result⟩

end RAM.Bench
end
end PowerSaving

end OAI

end
-- bos_merge: end Submission.OAI.Computability.FourierTransform.UniformBounds

-- bos_merge: begin Submission.OAI.Computability.FourierTransform.Asymptotics
section

namespace OAI

/- asymptotic analysis, one n for both length functions -/
namespace PowerSaving
open RAM Bench Selection Slant Filter Asymptotics Real
noncomputable section

namespace Skies

abbrev Tm (n : ℕ) : ℝ := log (n:ℝ)
abbrev Qm (n : ℕ) : ℝ := log (Tm n)

lemma Ttop : Tendsto Tm atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
lemma Qtop : Tendsto Qm atTop atTop := Real.tendsto_log_atTop.comp Ttop
lemma log2_min : 2/3 ≤ log (2:ℝ) := by
  have hh := le_log_one_add_of_nonneg (show (0:ℝ)≤1 by norm_num)
  norm_num at *
  exact hh

-- n is problem size, N allowed between n and 2n
lemma stack_lim (n N : ℕ) (hn : 0<n) (h : n≤N) (hk : N ≤ 2*n) (ht : 1≤Tm n) :
    (stackN N:ℝ) ≤ 10 * Tm n := by
  let k := Nat.log 2 (2*N)
  have H : 2^k ≤ 2*N := Nat.pow_log_le_self _ (by omega)
  have H0 : 2^k ≤ 4*n := by omega
  have he : 0<(n:ℝ) := by exact_mod_cast hn
  have HH := log_le_log (by positivity : 0<(2:ℝ)^k)
    (show (2:ℝ)^k ≤ 4*n by exact_mod_cast H0)
  rw [log_pow,log_mul (by norm_num) he.ne'] at HH
  have H4 := log_le_sub_one_of_pos (show (0:ℝ)<4 by norm_num)
  change (((k+1:ℕ):ℝ)) ≤ _
  push_cast
  unfold Tm at *
  nlinarith [log2_min,show 0≤(k:ℝ) by positivity]

lemma order_pow_lim (n N : ℕ) (hn : 0<n) (h : n≤N) (hk : N ≤ 2*n) (ht : 1 ≤ Tm n) :
    (2:ℝ)^orderE N ≤ 10^6*Tm n^2 := by
  have hh : (2:ℝ)^orderE N ≤ 8*harvestN N := by exact_mod_cast orderE_small N
  refine hh.trans ?_
  unfold harvestN silo; push_cast
  have hg := stack_lim n N hn h hk ht
  calc
    _ ≤ 8*(16*(14*Tm n))^2 := by gcongr; linarith
    _ ≤ _ := by nlinarith [sq_nonneg (Tm n)]

lemma order_lim (n N : ℕ) (hn : 0<n) (h : n≤N) (hk : N ≤ 2*n) (ht : 1 ≤ Tm n) (hu : 1 ≤ Qm n) :
    (orderE N:ℝ) ≤ 3*10^6 * Qm n := by
  have H := log_le_log (by positivity : 0<(2:ℝ)^orderE N) (order_pow_lim n N hn h hk ht)
  have he : 0<Tm n := by linarith
  rw [log_pow,log_mul (by norm_num) (by positivity),log_pow,log_pow] at H
  have H4 := log_le_sub_one_of_pos (show 0 < (10:ℝ) by norm_num)
  unfold Qm at *
  have h0 : 0 ≤ (orderE N:ℝ) := by positivity
  push_cast at H
  nlinarith [log2_min]

lemma score_lim (n N : ℕ) (hn : 0<n) (h : n≤N) (hk : N ≤ 2*n) (ht : 1 ≤ Tm n) (hu : 1 ≤ Qm n) :
    (score (orderE N):ℝ)+1 ≤ 10^32*Qm n^2 := by
  have H := order_lim n N hn h hk ht hu
  have hk : (score (orderE N):ℝ) ≤ 20000000*((orderE N:ℝ)+1)^2+7 := by
    exact_mod_cast score_le (orderE N)
  calc
    _ ≤ (20000000*((orderE N:ℝ)+1)^2+7)+1 := by gcongr
    _ ≤ (20000000*(4*10^6*Qm n)^2+7)+1 := by gcongr; linarith
    _ ≤ _ := by nlinarith

lemma hills_lim (n N : ℕ) (hn : 0<n) (h : n≤N) (hk : N ≤ 2*n) (ht : 1 ≤ Tm n) :
    (hills (barge N).l:ℝ) ≤ 100*Tm n^alpha := by
  have he : 0<Tm n := by linarith
  have H := stack_lim n N hn h hk ht
  have G : ((barge N).l:ℝ) ≤ stackN N := by
    exact_mod_cast (barge_spec N (lt_of_lt_of_le hn h)).count
  have hg := alpha_pos
  refine (hills_real _).trans ?_
  calc
    _ ≤ 2*(11*Tm n)^alpha := by gcongr; linarith
    _ = 2*(11^alpha*Tm n^alpha) := by rw [mul_rpow (by norm_num) he.le]
    _ ≤ 2*(11^(1:ℝ)*Tm n^alpha) := by gcongr <;> first | exact alpha_lt.le | norm_num
    _ ≤ _ := by
      rw [rpow_one]
      have hTT : 0 < Tm n^alpha := by positivity
      linarith

def flight (n : ℕ) := (n:ℝ)*(Tm n)^alpha*Qm n^2

lemma leg_lim (n N : ℕ) (hn : 0<n) (h : n≤N) (hk : N ≤ 2*n) (ht : 1 ≤ Tm n) (hu : 1 ≤ Qm n) :
    (leg N:ℝ) ≤ 10^40*flight n := by
  have hg : (barge N).vol ≤ 8*n := by
    have hh := (barge_spec N (by omega)).upper
    omega
  have hh : ((barge N).vol:ℝ) ≤ 8*n := by exact_mod_cast hg
  have hT : 0 < Tm n := by linarith
  unfold leg; push_cast
  calc
    _ ≤ (10^32 * Qm n^2)*((8*n)*(100*Tm n^alpha)) :=
      mul_le_mul (score_lim n N hn h hk ht hu)
        (mul_le_mul hh (hills_lim n N hn h hk ht) (by positivity) (by positivity))
        (by positivity) (by positivity)
    _ = 8*100*10^32*flight n := by unfold flight; ring
    _ ≤ _ := by
      have hh : 0 ≤ flight n := by unfold flight; positivity
      gcongr; norm_num

lemma flight_big (n : ℕ) (ht : 1 ≤ Tm n) (hu : 1 ≤ Qm n) :
    (n:ℝ) ≤ flight n := by
  have H := Real.one_le_rpow ht alpha_pos.le
  unfold flight
  calc
    (n:ℝ) = n*1*1 := by ring
    _ ≤ _ := by gcongr; nlinarith

-- little o fournishes eventual caps.
lemma dwarf {v : ℕ→ℝ} (h : Tendsto v atTop atTop) (d : ℕ) {p c : ℝ} (hp : 0<p) (hc : 0<c) :
    ∀ᶠ n in atTop, log (v n)^d ≤ c*v n^p := by
  have H := (isLittleO_log_rpow_rpow_atTop (d:ℝ) hp).comp_tendsto h
  have hg := H.def hc
  filter_upwards [hg,h.eventually_ge_atTop 1] with n hn he
  have he' : 0<v n := by linarith
  change ‖log (v n)^(d:ℝ)‖ ≤ c*‖v n^p‖ at hn
  rw [rpow_natCast,Real.norm_of_nonneg (pow_nonneg (Real.log_nonneg he) _),
    Real.norm_of_nonneg (by positivity)] at hn
  exact hn

variable {N : ℕ→ℕ}
-- initial branch disappears
lemma docks_ev (h : ∀ n:ℕ,n ≤ N n ∧ N n ≤ 2*n) :
    ∀ᶠ n in atTop, Ports (N n) := by
  have H := dwarf (v:=fun n => (n:ℝ)) tendsto_natCast_atTop_atTop 2
    (c:=1/10^6) (p:=1) (by norm_num) (by norm_num)
  filter_upwards [H,eventually_gt_atTop 0,Ttop.eventually_ge_atTop 1] with n hh hn ht
  rw [rpow_one] at hh
  have hh' : (Tm n)^2 ≤ 1/10^6*n := hh
  have hh1 := order_pow_lim n (N n) hn (h n).1 (h n).2 ht
  have hh2 : (2:ℝ)^(orderE (N n)) ≤ n := by linarith
  exact (show 2^orderE (N n) ≤ n by exact_mod_cast hh2).trans (h n).1

lemma polylog_ev (h : ∀ n:ℕ,n ≤ N n ∧ N n ≤ 2*n) (d : ℕ) :
    ∀ᶠ n in atTop, ((stackN (N n):ℝ)+2)^d ≤ n := by
  have h0 : 0< (12:ℝ)^d := by positivity
  have H := dwarf (v:=fun n => (n:ℝ)) tendsto_natCast_atTop_atTop d
    (c:=((12:ℝ)^d)⁻¹) (p:=1) (by norm_num) (by positivity)
  filter_upwards [H,eventually_gt_atTop 0,Ttop.eventually_ge_atTop 1] with n hh hn ht
  rw [rpow_one] at hh
  have hh' : (Tm n)^d ≤ ((12:ℝ)^d)⁻¹*n := hh
  have hh1 := stack_lim n (N n) hn (h n).1 (h n).2 ht
  calc
    _ ≤ (12*Tm n)^d := by gcongr; linarith
    _ ≤ _ := by
      rw [mul_pow]
      calc
        _ ≤ _ := mul_le_mul_of_nonneg_left hh' h0.le
        _ = _ := by rw [← mul_assoc,mul_inv_cancel₀ h0.ne',one_mul]

lemma wind_ev (h : ∀ n:ℕ,n ≤ N n ∧ N n ≤ 2*n) (d : ℕ) :
    ∀ᶠ n in atTop,(fairwind d (N n):ℝ)+1 ≤ 10^41*flight n := by
  filter_upwards [docks_ev h,polylog_ev h d,eventually_gt_atTop 0,Ttop.eventually_ge_atTop 1,
    Qtop.eventually_ge_atTop 1] with n hh hk hn ht hu
  unfold fairwind Bench.surf
  rw [ite_eq_left hh,Nat.add_zero]
  push_cast
  have hp := leg_lim n (N n) hn (h n).1 (h n).2 ht hu
  have he := flight_big n ht hu
  have he' : 1≤(n:ℝ) := by exact_mod_cast hn
  have hx : (N n:ℝ) ≤ 2*n := by exact_mod_cast (h n).2
  linarith

lemma lunch_big (a b : Ration) (h : ∀ n:ℕ,n ≤ N n ∧ N n ≤ 2*n) :
    (fun n : ℕ => (lunch a b N n:ℝ)) =O[atTop] flight := by
  let W := lunch a b N
  refine isBigO_iff.mpr ⟨(a.c:ℝ)*10^41+1+(b.c:ℝ)*10^41,?_⟩
  filter_upwards [wind_ev h a.d,wind_ev h b.d,eventually_gt_atTop 0,Ttop.eventually_ge_atTop 1,
    Qtop.eventually_ge_atTop 1] with n hh hk hn ht hu
  have he := flight_big n ht hu
  have h1 : 1≤(n:ℝ) := by exact_mod_cast hn
  rw [Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg (by linarith)]
  unfold lunch calorie
  push_cast; simp only [add_mul,one_mul,mul_assoc]
  gcongr
  exact h1.trans he

end Skies
end
end PowerSaving

end OAI

end
-- bos_merge: end Submission.OAI.Computability.FourierTransform.Asymptotics
