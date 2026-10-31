import Submission.Work.Mixed.Prog.ClassTabs

/-! Merged module written by bos_merge.py for the 500-file limit of the Big O Speedrun
pull-request route.  It is the concatenation, in import order, of the 10 modules below; each one
is copied verbatim after its import header, inside `section` ... `end`, with the scopes it leaves
open closed before that `end`.  Members (module, sha256 of the original file):
* `Submission.Work.Mixed.Prog.RouteTabs` 8f5458c554432ac202332452656de8d35e07837dc58bd9cec80e965a498f221e
* `Submission.Work.Mixed.Prog.Unload` ffcb2e56f8564a3d50c5297d07187da4b2f28f35dca2631c102b2c964a841cb3
* `Submission.Work.Mixed.Prog.LoadRAM` 7eeb6c5fe959d273ad221b52123853fef20c254d9d0baaf542bf800cb5a5440a
* `Submission.Work.Mixed.Prog.Acc` d0e7f647ecc16d8988528f44c8268569e1beff9a1a73c64f98e4eb5d64ca1fa3
* `Submission.Work.Mixed.Prog.SweepMath` dd27d53020f0adb2edf641311ab80a272021f73fe47486aff2028a8d435e51cd
* `Submission.Work.Mixed.Prog.Sweep` f0f966923d1e5f6480938c91f8c2ebd15bae2ef837b7f39d543ac08b6a21eb41
* `Submission.Work.Mixed.Prog.SweepUp` c7eb9bc1b458b513c7960850ed60704b67d4d9590f4f7511771dc9fc87bbaacc
* `Submission.Work.Mixed.Prog.SweepLeaf` 7f86e993672b816aaa552a75ec4ac2f7cd127b3749aff53a2c053c316afd9600
* `Submission.Work.Mixed.Prog.ClassBody` 0b38ad7782f990589611b1f3289c444b574b14d0ad530bc4605072da7248cb9e
* `Submission.Work.Mixed.Prog.Valid` 9beddb97d3b64909f939638419faec8903a0520d107abc6edb4740a5b23719c3
-/

-- bos_merge: begin Submission.Work.Mixed.Prog.RouteTabs
section

/-!
# Mixed engine, R3 program part 9: the routing tables of a block letter (agent e-r3prog)

For a block letter of rank `r` of a class `(n, h+1, μ)` the class computes (brute force,
polynomial bookkeeping) the index part of its child `(n, h, μ*r)` and the tables the block letter
reads (`Route.lean`): fed flags, parent units, supply indices, the child slot of each parent unit,
and, for the source accumulator, the source slots in order and their sizes.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset GF MXR
noncomputable section

universe U

/-- A table of `N` entries, each computed at cost `P`: work `N*(P+1)`. -/
lemma tabC {ι : Type U} {m : Bool} {B : ι → ℕ} {s t : Ty} {x : ι → T s} {N P : ι → ℕ}
    (g : ∀ i, Fin (N i) → T t) (hN : Knows m B s x N) (hNs : Small B N)
    (hg : Can m (fun u : UnitF N => B u.1) (p s w) t (fun u => (x u.1, u.2.val)) (fun u => g u.1 u.2)
      (fun u => P u.1)) :
    Can m B s (a t) x (fun i => (Layout.std (N i)).tape (g i)) (fun i => N i * (P i + 1)) := by
  have H := Can.layout (t:=t) (L:=fun i => Layout.std (N i)) (v:=g) (P:=P) (W:=fun _ => 0) hN hg hNs
  refine H.mono (fun i => ?_)
  change 0 + N i + N i * P i ≤ N i * (P i + 1)
  nlinarith

/-- The child's knowledge from the parent's. -/
lemma CIn.child {ι : Type U} {m : Bool} {B : ι → ℕ} {s : Ty} {x : ι → T s} {n h μ : ι → ℕ}
    (c : CIn m B s x n (fun i => h i + 1) μ) (r : ℕ) :
    CIn m B s x n h (fun i => μ i * r) :=
  ⟨c.nK, (c.hK.wsub (Can.wc 1) (c.hS.sub)).cong (fun _ => rfl) (fun i => by simp), c.μK.times (Can.wc r)
    c.μS (Small.const _ r), c.p2n, c.imag, c.big, fun i => by have := c.hle i; omega,
    c.μS.mul (Small.const _ r)⟩

namespace Eng
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]
variable (E : Eng α ρ σ)
variable {ι : Type U} {m : Bool} {B : ι → ℕ} {s : Ty} {x : ι → T s} {n h μ : ι → ℕ}

lemma parCode_lt (n h μ r t : ℕ) (ht : t < E.NUc n h (μ * r) * E.W) : E.parCode n h μ r t < E.W^(h+1) := by
  unfold parCode
  have hp : t / E.W < E.NUc n h (μ * r) := (Nat.div_lt_iff_lt_mul E.W_pos).2 ht
  exact lt_of_cons E.W h _ _ (Nat.mod_lt _ E.W_pos) (MXR.U_lt hp)

/-- The routing tables of a block letter of rank `r` (child `(n, h, μ*r)` of `(n, h+1, μ)`). -/
abbrev RtT : Ty := p IdxT (p (a w) (p (a w) (p (a w) (p (a w) (p (a w) (a w))))))
def rtVal (n h μ r o : ℕ) : T RtT :=
  (E.idxVal n h (μ * r),
   (Layout.std (E.NUc n h (μ * r) * E.W)).tape (fun t => E.flR n h μ r t),
   (Layout.std (E.NUc n h (μ * r) * E.W)).tape (fun t => E.ppR n h μ r t),
   (Layout.std (E.NUc n h (μ * r) * E.W)).tape (fun t => E.siR n h μ r o t),
   (Layout.std (E.NUc n (h+1) μ)).tape (fun p => E.slotR n h μ r p),
   (Layout.std (Nat.count (E.srcP n h μ r) (E.NUc n h (μ * r) * E.W))).tape
      (fun k => Nat.nth (E.srcP n h μ r) k),
   (Layout.std (Nat.count (E.srcP n h μ r) (E.NUc n h (μ * r) * E.W))).tape
      (fun k => E.slotSize n h (μ * r) (Nat.nth (E.srcP n h μ r) k)))

/-- Cost of the routing tables. -/
def rtCost (n h μ r : ℕ) : ℕ :=
  E.idxCost n h (μ * r) + 8 * (E.W^(h+1) + 1) * (E.W^(h+1) + 1) * (h + 3) + 8

/-- **The routing tables of a block letter.** -/
lemma can_route (c : CIn m B s x n (fun i => h i + 1) μ) (r : ℕ) {o : ι → ℕ} (ho : Knows m B s x o)
    (hos : Small B o)
    (hWp : Knows m B s x (fun i => E.W^(h i + 1)))
    (hNUp : Knows m B s x (fun i => E.NUc (n i) (h i + 1) (μ i)))
    (hPCp : Has m B s (a w) x (fun i => (Layout.std (E.W^(h i + 1))).tape (fun t => E.PCc (n i) (h i + 1) (μ i) t)))
    (hUp : Has m B s (a w) x (fun i => (Layout.std (E.NUc (n i) (h i + 1) (μ i))).tape
      (fun p => E.Uc (n i) (h i + 1) (μ i) p))) :
    Can m B s RtT x (fun i => E.rtVal (n i) (h i) (μ i) r (o i)) (fun i => E.rtCost (n i) (h i) (μ i) r) := by
  have c' := c.child r
  have Hidx := E.can_index c'
  -- environment x1 = (x, child index tables)
  let x1 (i : ι) : T (p s IdxT) := (x i, E.idxVal (n i) (h i) (μ i * r))
  let NU' (i : ι) := E.NUc (n i) (h i) (μ i * r)
  let NJ (i : ι) := NU' i * E.W
  have c1 := c.ext (t:=IdxT) (fun i => E.idxVal (n i) (h i) (μ i * r))
  have F1 : ∀ {t : Ty} {y : ι → T t}, Has m B s t x y → Has m B (p s IdxT) t x1 y :=
    fun g => Can.first.then_do g
  have hNU' : Knows m B (p s IdxT) x1 NU' := Can.fst (Can.snd Can.second)
  have hPC' : Has m B (p s IdxT) (a w) x1
      (fun i => (Layout.std (E.W^(h i))).tape (fun t => E.PCc (n i) (h i) (μ i * r) t)) :=
    Can.fst (Can.snd (Can.snd Can.second))
  have hU' : Has m B (p s IdxT) (a w) x1
      (fun i => (Layout.std (NU' i)).tape (fun p => E.Uc (n i) (h i) (μ i * r) p)) :=
    Can.snd (Can.snd (Can.snd Can.second))
  have hNU's : Small B NU' := (c'.powS E.W).mono (fun i => E.NU_le' _ _ _)
  have hNJ : Knows m B (p s IdxT) x1 NJ := hNU'.times (Can.wc E.W) hNU's (Small.const _ _)
  have hNJs : Small B NJ := hNU's.mul (Small.const _ _)
  have hWps : Small B (fun i => E.W^(h i + 1)) := c.powS E.W
  -- the parent code of a child slot, at any index below NJ
  have pcAt : ∀ {κ : Type U} {sy : Ty} (jx : κ → ι) (y : κ → T sy) (jj : κ → ℕ),
      Has m (fun k => B (jx k)) sy (p s IdxT) y (fun k => x1 (jx k)) →
      Knows m (fun k => B (jx k)) sy y jj → (∀ k, jj k < NJ (jx k)) →
      Knows m (fun k => B (jx k)) sy y (fun k => E.parCode (n (jx k)) (h (jx k)) (μ (jx k)) r (jj k)) := by
    intro κ sy jx y jj hy hj hlt
    have hjs : Small (fun k => B (jx k)) jj := (hNJs.reindex jx).mono (fun k => (hlt k).le)
    have hq : Knows m (fun k => B (jx k)) sy y (fun k => jj k / E.W) := hj.dvdW (Can.wc E.W) hjs
    have hqlt : ∀ k, jj k / E.W < NU' (jx k) := fun k => (Nat.div_lt_iff_lt_mul E.W_pos).2 (hlt k)
    have hUq := Can.fetch (t:=w) (L:=fun k => Layout.std (NU' (jx k)))
      (v:=fun k p => E.Uc (n (jx k)) (h (jx k)) (μ (jx k) * r) p) (i:=fun k => ⟨jj k / E.W, hqlt k⟩)
      (hy.then_do (hU'.reindex jx)) hq
    have hUs : Small (fun k => B (jx k)) (fun k => E.Uc (n (jx k)) (h (jx k)) (μ (jx k) * r) (jj k / E.W)) :=
      ((c'.powS E.W).reindex jx).mono (fun k => (MXR.U_lt (hqlt k)).le)
    exact (hj.modW (Can.wc E.W) hjs).plus ((Can.wc E.W).times hUq (Small.const _ _) hUs) hjs.mod
      ((Small.const _ _).mul hUs)
  have pcAt_s : ∀ {κ : Type U} (jx : κ → ι) (jj : κ → ℕ), (∀ k, jj k < NJ (jx k)) →
      Small (fun k => B (jx k)) (fun k => E.parCode (n (jx k)) (h (jx k)) (μ (jx k)) r (jj k)) := by
    intro κ jx jj hlt
    exact ((hWps.reindex jx)).mono (fun k => (E.parCode_lt _ _ _ _ _ (hlt k)).le)
  -- the region test of the parent at a parent code
  have inAt : ∀ {κ : Type U} {sy : Ty} (jx : κ → ι) (y : κ → T sy) (jj : κ → ℕ),
      Has m (fun k => B (jx k)) sy (p s IdxT) y (fun k => x1 (jx k)) →
      Knows m (fun k => B (jx k)) sy y jj → (∀ k, jj k < NJ (jx k)) →
      Can m (fun k => B (jx k)) sy w y
        (fun k => if inRS E.W E.tq E.mx (n (jx k)) (h (jx k) + 1) (μ (jx k))
          (E.parCode (n (jx k)) (h (jx k)) (μ (jx k)) r (jj k)) then 1 else 0) (fun k => h (jx k) + 1 + 1) := by
    intro κ sy jx y jj hy hj hlt
    have cK := c1.reindex jx y hy
    exact E.knows_inR cK (pcAt jx y jj hy hj hlt) (pcAt_s jx jj hlt) (hy.then_do ((F1 hWp).reindex jx))
  -- slots
  let SL := UnitF NJ
  let yS (u : SL) : T (p (p s IdxT) w) := (x1 u.1, u.2.val)
  have hfl : Can m (fun u : SL => B u.1) (p (p s IdxT) w) w yS
      (fun u => E.flR (n u.1) (h u.1) (μ u.1) r u.2.val) (fun u => h u.1 + 2) := by
    refine (inAt (fun u : SL => u.1) yS (fun u => u.2.val) Can.first Can.second (fun u => u.2.2)).cong
      (fun _ => rfl) (fun u => ?_)
    have h1 : u.2.val < NJ u.1 := u.2.2
    unfold flR
    by_cases h2 : inRS E.W E.tq E.mx (n u.1) (h u.1 + 1) (μ u.1) (E.parCode (n u.1) (h u.1) (μ u.1) r u.2.val)
    · rw [if_pos h2, if_pos (show E.fedP (n u.1) (h u.1) (μ u.1) r u.2.val from ⟨h1, h2⟩)]
    · rw [if_neg h2, if_neg (show ¬ E.fedP (n u.1) (h u.1) (μ u.1) r u.2.val from fun hh => h2 hh.2)]
  have hpp : Knows m (fun u : SL => B u.1) (p (p s IdxT) w) yS (fun u => E.ppR (n u.1) (h u.1) (μ u.1) r u.2.val) :=
    Can.fetch (t:=w) (L:=fun u : SL => Layout.std (E.W^(h u.1 + 1)))
      (v:=fun u t => E.PCc (n u.1) (h u.1 + 1) (μ u.1) t)
      (i:=fun u => ⟨E.parCode (n u.1) (h u.1) (μ u.1) r u.2.val, E.parCode_lt _ _ _ _ _ u.2.2⟩)
      (Can.first.then_do ((F1 hPCp).reindex (fun u : SL => u.1)))
      (pcAt (fun u : SL => u.1) yS (fun u => u.2.val) Can.first Can.second (fun u => u.2.2))
  -- supply index: the running offset plus the source slots before
  have hsrc : ∀ {κ : Type U} {sy : Ty} (jx : κ → ι) (y : κ → T sy) (jj : κ → ℕ),
      Has m (fun k => B (jx k)) sy (p s IdxT) y (fun k => x1 (jx k)) →
      Knows m (fun k => B (jx k)) sy y jj → (∀ k, jj k < NJ (jx k)) →
      Can m (fun k => B (jx k)) sy w y
        (fun k => if E.srcP (n (jx k)) (h (jx k)) (μ (jx k)) r (jj k) then 1 else 0) (fun k => h (jx k) + 2) := by
    intro κ sy jx y jj hy hj hlt
    refine ((Can.wc 1).wsub (inAt jx y jj hy hj hlt) ((Small.const _ 1).mono (fun _ => Nat.sub_le _ _))).cong
      (fun _ => rfl) (fun k => ?_)
    by_cases h2 : inRS E.W E.tq E.mx (n (jx k)) (h (jx k) + 1) (μ (jx k)) (E.parCode (n (jx k)) (h (jx k)) (μ (jx k)) r (jj k))
    · rw [if_pos h2, if_neg (show ¬ E.srcP (n (jx k)) (h (jx k)) (μ (jx k)) r (jj k) from fun hh => hh.2 h2)]
    · rw [if_neg h2, if_pos (show E.srcP (n (jx k)) (h (jx k)) (μ (jx k)) r (jj k) from ⟨hlt k, h2⟩)]
  have hsi : Can m (fun u : SL => B u.1) (p (p s IdxT) w) w yS
      (fun u => E.siR (n u.1) (h u.1) (μ u.1) r (o u.1) u.2.val) (fun u => NJ u.1 * (h u.1 + 3) + 2) := by
    let DD := During (fun u : SL => u.2.val)
    have hyD : Has m (fun d : DD => B d.i.1) (p (p (p s IdxT) w) w) (p s IdxT) (fun d => (yS d.i, d.j))
        (fun d => x1 d.i.1) := Can.first.then_do Can.first
    have hjD : Knows m (fun d : DD => B d.i.1) (p (p (p s IdxT) w) w) (fun d => (yS d.i, d.j)) (fun d => d.j) :=
      Can.second
    have hcnt := can_count (P:=fun u : SL => E.srcP (n u.1) (h u.1) (μ u.1) r) (Wt:=fun u => h u.1 + 2)
      (T:=fun u : SL => u.2.val) (x:=yS) Can.second ((hNJs.reindex (fun u : SL => u.1)).mono (fun u => u.2.2.le))
      (hsrc (sy:=p (p (p s IdxT) w) w) (fun d : DD => d.i.1) (fun d => (yS d.i, d.j)) (fun d => d.j)
        hyD hjD (fun d => lt_trans d.hj d.i.2.2))
    refine ((Can.first.then_do ((F1 ho).reindex (fun u : SL => u.1))).mono (fun _ => Nat.zero_le _) |>.plus
      hcnt ((hos.reindex (fun u : SL => u.1))) (((hNJs.reindex (fun u : SL => u.1))).mono
        (fun u => le_trans (MXR.count_le_self _) u.2.2.le))).mono (fun u => ?_)
    have := u.2.2
    change u.2.val * (h u.1 + 2 + 1) + 1 ≤ NJ u.1 * (h u.1 + 3) + 2
    nlinarith
  -- child slot of each parent unit
  let NUp (i : ι) := E.NUc (n i) (h i + 1) (μ i)
  let UP := UnitF NUp
  let yP (u : UP) : T (p (p s IdxT) w) := (x1 u.1, u.2.val)
  have hUpp : Knows m (fun u : UP => B u.1) (p (p s IdxT) w) yP (fun u => E.Uc (n u.1) (h u.1 + 1) (μ u.1) u.2) :=
    unit_fetch (m:=m) (B:=B) (s:=p s IdxT) (t:=w) (NU:=NUp) (x:=x1)
      (fun i (p : Fin (NUp i)) => E.Uc (n i) (h i + 1) (μ i) p) (F1 hUp)
  have hUps : Small (fun u : UP => B u.1) (fun u => E.Uc (n u.1) (h u.1 + 1) (μ u.1) u.2) :=
    ((hWps.reindex (fun u : UP => u.1))).mono (fun u => (MXR.U_lt u.2.2).le)
  have hτlt : ∀ u : UP, E.Uc (n u.1) (h u.1 + 1) (μ u.1) u.2 / E.W < E.W^(h u.1) := fun u => by
    rw [Nat.div_lt_iff_lt_mul E.W_pos, ← pow_succ]; exact MXR.U_lt u.2.2
  have hPCτ := Can.fetch (t:=w) (L:=fun u : UP => Layout.std (E.W^(h u.1)))
    (v:=fun u t => E.PCc (n u.1) (h u.1) (μ u.1 * r) t)
    (i:=fun u => ⟨E.Uc (n u.1) (h u.1 + 1) (μ u.1) u.2 / E.W, hτlt u⟩)
    (Can.first.then_do (hPC'.reindex (fun u : UP => u.1))) (hUpp.dvdW (Can.wc E.W) hUps)
  have hPCτs : Small (fun u : UP => B u.1) (fun u => E.PCc (n u.1) (h u.1) (μ u.1 * r)
      (E.Uc (n u.1) (h u.1 + 1) (μ u.1) u.2 / E.W)) :=
    ((c'.powS E.W).reindex (fun u : UP => u.1)).mono (fun u => le_trans (MXR.count_le_self _) (hτlt u).le)
  have hslot : Knows m (fun u : UP => B u.1) (p (p s IdxT) w) yP (fun u => E.slotR (n u.1) (h u.1) (μ u.1) r u.2) :=
    (hPCτ.times (Can.wc E.W) hPCτs (Small.const _ _)).plus (hUpp.modW (Can.wc E.W) hUps)
      (hPCτs.mul (Small.const _ _)) hUps.mod
  have hNUps : Small B NUp := hWps.mono (fun i => E.NU_le' _ _ _)
  have Tslot := tabC (t:=w) (P:=fun _ => 0) (fun i (p : Fin (NUp i)) => E.slotR (n i) (h i) (μ i) r p)
    (F1 hNUp) hNUps hslot
  -- tables over slots
  have Tfl := tabC (t:=w) (P:=fun i => h i + 2) (fun i (t : Fin (NJ i)) => E.flR (n i) (h i) (μ i) r t)
    hNJ hNJs hfl
  have Tpp := tabC (t:=w) (P:=fun _ => 0) (fun i (t : Fin (NJ i)) => E.ppR (n i) (h i) (μ i) r t) hNJ hNJs hpp
  have Tsi := tabC (t:=w) (P:=fun i => NJ i * (h i + 3) + 2)
    (fun i (t : Fin (NJ i)) => E.siR (n i) (h i) (μ i) r (o i) t) hNJ hNJs hsi
  -- number of source slots
  let ns (i : ι) := Nat.count (E.srcP (n i) (h i) (μ i) r) (NJ i)
  have hns : Can m B (p s IdxT) w x1 ns (fun i => NJ i * (h i + 2 + 1) + 1) := by
    let DD := During NJ
    have hyD : Has m (fun d : DD => B d.i) (p (p s IdxT) w) (p s IdxT) (fun d => (x1 d.i, d.j))
        (fun d => x1 d.i) := Can.first
    have hjD : Knows m (fun d : DD => B d.i) (p (p s IdxT) w) (fun d => (x1 d.i, d.j)) (fun d => d.j) := Can.second
    exact can_count (P:=fun i => E.srcP (n i) (h i) (μ i) r) (Wt:=fun i => h i + 2) hNJ hNJs
      (hsrc (sy:=p (p s IdxT) w) (fun d : DD => d.i) (fun d => (x1 d.i, d.j)) (fun d => d.j) hyD hjD
        (fun d => d.hj))
  have hnsle : ∀ i, ns i ≤ NJ i := fun i => MXR.count_le_self _
  have hnss : Small B ns := hNJs.mono hnsle
  -- environment x2 = (x1, ns)
  let x2 (i : ι) : T (p (p s IdxT) w) := (x1 i, ns i)
  let SK := UnitF ns
  let yK (u : SK) : T (p (p (p s IdxT) w) w) := (x2 u.1, u.2.val)
  have hnth : Can m (fun u : SK => B u.1) (p (p (p s IdxT) w) w) w yK
      (fun u => Nat.nth (E.srcP (n u.1) (h u.1) (μ u.1) r) u.2.val) (fun u => NJ u.1 * (h u.1 + 2 + 1) + 1) := by
    let DD := During (fun u : SK => NJ u.1)
    have hyD : Has m (fun d : DD => B d.i.1) (p (p (p (p s IdxT) w) w) w) (p s IdxT) (fun d => (yK d.i, d.j))
        (fun d => x1 d.i.1) := Can.first.then_do (Can.first.then_do Can.first)
    have hjD : Knows m (fun d : DD => B d.i.1) (p (p (p (p s IdxT) w) w) w) (fun d => (yK d.i, d.j))
        (fun d => d.j) := Can.second
    have H := can_nthc (P:=fun u : SK => E.srcP (n u.1) (h u.1) (μ u.1) r) (Wt:=fun u => h u.1 + 2)
      (T:=fun u : SK => NJ u.1) (q:=fun u => u.2.val) (x:=yK)
      (Can.first.then_do (Can.first.then_do (hNJ.reindex (fun u : SK => u.1))))
      (hNJs.reindex (fun u : SK => u.1)) Can.second
      (hsrc (sy:=p (p (p (p s IdxT) w) w) w) (fun d : DD => d.i.1) (fun d => (yK d.i, d.j)) (fun d => d.j)
        hyD hjD (fun d => d.hj))
    refine H.cong (fun _ => rfl) (fun u => ?_)
    have : u.2.val < Nat.count (E.srcP (n u.1) (h u.1) (μ u.1) r) (NJ u.1) := u.2.2
    rw [if_pos this]
  have hnthlt : ∀ u : SK, Nat.nth (E.srcP (n u.1) (h u.1) (μ u.1) r) u.2.val < NJ u.1 := fun u =>
    (MXR.nth_spec u.2.2).2.1
  have hnths : Small (fun u : SK => B u.1) (fun u => Nat.nth (E.srcP (n u.1) (h u.1) (μ u.1) r) u.2.val) :=
    (hNJs.reindex (fun u : SK => u.1)).mono (fun u => (hnthlt u).le)
  -- the size of the k-th source slot
  have hsz : Can m (fun u : SK => B u.1) (p (p (p s IdxT) w) w) w yK
      (fun u => E.slotSize (n u.1) (h u.1) (μ u.1 * r) (Nat.nth (E.srcP (n u.1) (h u.1) (μ u.1) r) u.2.val))
      (fun u => NJ u.1 * (h u.1 + 3) + h u.1 + 2) := by
    let tt (u : SK) := Nat.nth (E.srcP (n u.1) (h u.1) (μ u.1) r) u.2.val
    have hsave := hnth.save (t:=w) (u:=w) (z:=fun u => E.slotSize (n u.1) (h u.1) (μ u.1 * r) (tt u))
      (W':=fun u => h u.1 + 1) (by
        let yT (u : SK) : T (p (p (p (p s IdxT) w) w) w) := (yK u, tt u)
        have ht : Knows m (fun u : SK => B u.1) (p (p (p (p s IdxT) w) w) w) yT tt := Can.second
        have hq : Knows m (fun u : SK => B u.1) (p (p (p (p s IdxT) w) w) w) yT (fun u => tt u / E.W) :=
          ht.dvdW (Can.wc E.W) hnths
        have hqlt : ∀ u : SK, tt u / E.W < NU' u.1 := fun u => (Nat.div_lt_iff_lt_mul E.W_pos).2 (hnthlt u)
        have hUq := Can.fetch (t:=w) (L:=fun u : SK => Layout.std (NU' u.1))
          (v:=fun u p => E.Uc (n u.1) (h u.1) (μ u.1 * r) p) (i:=fun u => ⟨tt u / E.W, hqlt u⟩)
          (Can.first.then_do (Can.first.then_do (Can.first.then_do (hU'.reindex (fun u : SK => u.1))))) hq
        have hUs : Small (fun u : SK => B u.1) (fun u => E.Uc (n u.1) (h u.1) (μ u.1 * r) (tt u / E.W)) :=
          ((c'.powS E.W).reindex (fun u : SK => u.1)).mono (fun u => (MXR.U_lt (hqlt u)).le)
        have cK := c'.reindex (fun u : SK => u.1) (t:=p (p (p (p s IdxT) w) w) w) yT
          (Can.first.then_do (Can.first.then_do (Can.first.then_do Can.first)))
        have hcol := E.can_colS cK.hK cK.hS hUq hUs (cK.powS E.mx)
        have hcs : Small (fun u : SK => B u.1) (fun u => colS E.W E.tq (h u.1) (E.Uc (n u.1) (h u.1) (μ u.1 * r) (tt u / E.W))) :=
          (cK.powS E.mx).mono (fun u => (E.stepC_iter_le _ _).1)
        have hcU := (cK.μK.mono (fun _ => Nat.zero_le _)).times hcol cK.μS hcs
        have htq := E.knows_tq (ht.modW (Can.wc E.W) hnths) (fun u => Nat.mod_lt _ E.W_pos)
        refine (htq.mono (fun _ => Nat.zero_le _) |>.times hcU ((Small.const _ E.mx).mono (fun u => E.tq_le _))
          (cK.μS.mul hcs)).cong (fun _ => rfl) (fun u => ?_)
        rfl)
    exact hsave.mono (fun u => by have := u.2.2; nlinarith)
  have hnsK : Knows m B (p (p s IdxT) w) x2 ns := Can.second
  have TN := tabC (t:=w) (P:=fun i => NJ i * (h i + 2 + 1) + 1)
    (fun i (k : Fin (ns i)) => Nat.nth (E.srcP (n i) (h i) (μ i) r) k) hnsK hnss hnth
  have TS := tabC (t:=w) (P:=fun i => NJ i * (h i + 3) + h i + 2)
    (fun i (k : Fin (ns i)) => E.slotSize (n i) (h i) (μ i * r) (Nat.nth (E.srcP (n i) (h i) (μ i) r) k))
    hnsK hnss hsz
  have Tns := hns.save (TN.fork TS)
  have hidx1 : Has m B (p s IdxT) IdxT x1 (fun i => E.idxVal (n i) (h i) (μ i * r)) := Can.second
  have Hrest := hidx1.fork (Tfl.fork (Tpp.fork (Tsi.fork (Tslot.fork Tns))))
  have H := Hidx.save Hrest
  refine H.weaken ⟨20, fun i => ?_⟩
  have e1 : NJ i ≤ E.W^(h i + 1) := by
    have := E.NU_le' (n i) (h i) (μ i * r)
    calc NJ i = NU' i * E.W := rfl
      _ ≤ E.W^(h i) * E.W := Nat.mul_le_mul_right _ this
      _ = E.W^(h i + 1) := (pow_succ _ _).symm
  have e2 : NUp i ≤ E.W^(h i + 1) := E.NU_le' _ _ _
  have e3 : ns i ≤ NJ i := hnsle i
  simp only [rtCost]
  set X := E.W^(h i + 1) with hX
  set Y := E.idxCost (n i) (h i) (μ i * r)
  change Y + (0 + (NJ i * (h i + 2 + 1) + (NJ i * (0 + 1) + (NJ i * (NJ i * (h i + 3) + 2 + 1) +
    (NUp i * (0 + 1) + (NJ i * (h i + 2 + 1) + 1 + (ns i * (NJ i * (h i + 2 + 1) + 1 + 1) +
      ns i * (NJ i * (h i + 3) + h i + 2 + 1)))))))) + 1 ≤ 20 * (Y + 8 * (X + 1) * (X + 1) * (h i + 3) + 8 + 1)
  have f1 : NJ i * (NJ i * (h i + 3) + 2 + 1) ≤ X * X * (h i + 3) + 3 * X := by
    have := Nat.mul_le_mul e1 (Nat.add_le_add_right (Nat.mul_le_mul_right (h i + 3) e1) 3)
    calc _ = NJ i * (NJ i * (h i + 3) + 3) := by ring
      _ ≤ X * (X * (h i + 3) + 3) := this
      _ = _ := by ring
  have f2 : ns i * (NJ i * (h i + 2 + 1) + 1 + 1) ≤ X * X * (h i + 3) + 2 * X := by
    have := Nat.mul_le_mul (le_trans e3 e1) (Nat.add_le_add_right (Nat.mul_le_mul_right (h i + 3) e1) 2)
    calc _ = ns i * (NJ i * (h i + 3) + 2) := by ring
      _ ≤ X * (X * (h i + 3) + 2) := this
      _ = _ := by ring
  have f3 : ns i * (NJ i * (h i + 3) + h i + 2 + 1) ≤ X * X * (h i + 3) + X * (h i + 3) := by
    have := Nat.mul_le_mul (le_trans e3 e1) (Nat.add_le_add_right (Nat.mul_le_mul_right (h i + 3) e1) (h i + 3))
    calc _ = ns i * (NJ i * (h i + 3) + (h i + 3)) := by ring
      _ ≤ X * (X * (h i + 3) + (h i + 3)) := this
      _ = _ := by ring
  have f4 : NJ i * (h i + 2 + 1) ≤ X * (h i + 3) := Nat.mul_le_mul_right _ e1
  have f5 : NJ i * (0 + 1) ≤ X := by simpa using e1
  have f6 : NUp i * (0 + 1) ≤ X := by simpa using e2
  have f7 : 8 * (X + 1) * (X + 1) * (h i + 3) = 8 * (X * X * (h i + 3)) + 16 * (X * (h i + 3)) + 8 * (h i + 3) := by
    ring
  have f8 : X ≤ X * (h i + 3) := Nat.le_mul_of_pos_right _ (by omega)
  rw [f7]
  omega


end Eng

end
end PowerSaving.RAM
end OAI

end
-- bos_merge: end Submission.Work.Mixed.Prog.RouteTabs

-- bos_merge: begin Submission.Work.Mixed.Prog.Unload
section

/-!
# Mixed engine, R3 program part 10: loading a class from its jobs, and answering them (agent e-r3prog)

* `Eng.unl`         own slot `t = p*W + a` read from unit `p`'s live role `a` through the target placement;
* `Eng.unl_run`     **correctness of a class**: after the whole word, `unl` is `hlow` of the slot's job on its
                    `tq a * cU p` H-bits (the mixed certificate + `hlow_placeS`);
* `CCtx.load`, `CCtx.unload`   the two RAM passes (linear work).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset GF MXR
noncomputable section

universe U

namespace Eng
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]
variable (E : Eng α ρ σ)

/-- The live role at position `t % W`. -/
def roleAt (t : ℕ) : σ := E.Q.atFin ⟨t % E.W, Nat.mod_lt _ E.W_pos⟩

lemma loc_roleAt (t : ℕ) : E.Q.loc (E.roleAt t) = t % E.W := by
  unfold roleAt; rw [Layout.loc_atFin]

lemma tq_roleAt (t : ℕ) : E.tq (t % E.W) = E.tr (E.roleAt t) := by
  unfold tq roleAt; rw [dif_pos (Nat.mod_lt _ E.W_pos)]

/-- Own slot `t` read from the class state. -/
def unl (n h μ : ℕ) (V : E.CState n h μ) (t : ℕ) (e : Bits n) : ℂ :=
  if hp : t / E.W < E.NUc n h μ then
    V ⟨t / E.W, hp⟩ ((E.placeT n h μ ⟨t / E.W, hp⟩ (E.roleAt t)).symm e).1
      (E.e (E.roleAt t), (0, ((E.placeT n h μ ⟨t / E.W, hp⟩ (E.roleAt t)).symm e).2))
  else 0

lemma slot_decomp (t : ℕ) : t / E.W * E.W + E.Q.loc (E.roleAt t) = t := by
  rw [loc_roleAt, Nat.mul_comm]; exact Nat.div_add_mod t E.W

/-- **Correctness of a class**: after the word, every own slot holds `hlow` of its job. -/
theorem unl_run (n h μ : ℕ) (J : ℕ → Bits n → ℂ) (t : ℕ) (ht : t < E.NUc n h μ * E.W) :
    E.unl n h μ (E.runV (E.V0 n h μ J) E.wd) t = hlow n (E.slotSize n h μ t) (J t) := by
  funext e
  have hp : t / E.W < E.NUc n h μ := (Nat.div_lt_iff_lt_mul E.W_pos).2 ht
  unfold unl
  rw [dif_pos hp]
  obtain ⟨⟨q, y⟩, hqy⟩ : ∃ z, E.placeT n h μ ⟨t / E.W, hp⟩ (E.roleAt t) z = e := ⟨_, Equiv.apply_symm_apply _ e⟩
  subst hqy
  rw [Equiv.symm_apply_apply]
  -- the word on one instance
  have hv : ∀ s, (∀ l', E.e l' ≠ s) →
      (fun i j => E.V0 n h μ J ⟨t / E.W, hp⟩ q (i, (0 : Bits 0), j) : Data α ρ (E.cUc n h μ (t / E.W))) s = 0 := by
    intro s hs; funext j
    unfold V0
    dsimp only
    rw [E.liveOf_none s hs]
    rfl
  have key := E.hw _ _ hv (E.roleAt t)
  change gwalk (E.cUc n h μ (t / E.W)) E.wd (fun i j => E.V0 n h μ J ⟨t / E.W, hp⟩ q (i, (0 : Bits 0), j))
    (E.e (E.roleAt t)) y = _
  rw [key]
  have hT : blockMat (E.tz (E.roleAt t)) = (E.St (E.roleAt t)).lift (kernel (Fin (E.tr (E.roleAt t)))) :=
    blockMat_eq_lift (E.St (E.roleAt t)) (E.tz (E.roleAt t)) (E.St_spec (E.roleAt t))
  rw [hT]
  have hJ : (fun j => E.V0 n h μ J ⟨t / E.W, hp⟩ q (E.e (E.roleAt t), (0 : Bits 0), j)) =
      fun j => J t (E.placeT n h μ ⟨t / E.W, hp⟩ (E.roleAt t) (q, j)) := by
    funext j
    unfold V0
    dsimp only
    rw [E.liveOf_e (E.roleAt t)]
    dsimp only
    rw [E.slot_decomp t]
  rw [hJ]
  have hsz : E.slotSize n h μ t = E.tr (E.roleAt t) * E.cUc n h μ (t / E.W) := by
    unfold slotSize; rw [E.tq_roleAt]
  rw [hsz]
  exact (hlow_placeS (E.St (E.roleAt t)) (E.Xt (E.roleAt t)) _ _ n _ (J t) q y).symm

end Eng

end
end PowerSaving.RAM
end OAI

end
-- bos_merge: end Submission.Work.Mixed.Prog.Unload

-- bos_merge: begin Submission.Work.Mixed.Prog.LoadRAM
section

/-!
# Mixed engine, R3 program part 11: the load and unload passes (agent e-r3prog)

* `CCtx.egear`    the gear of every element (from the per-unit tables; no data needed);
* `Eng.load`      the class table `V0` from the own jobs (live roles through the target placement, scratch 0);
* `Eng.unload`    the own answers `unl` from the class table.
Both are one pass, work `O(NU * 2^n)`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset GF MXR
noncomputable section

universe U

namespace CCtx
variable {ι : Type U} {m : Bool} {B : ι → ℕ} {s : Ty} {x : ι → T s} {mx : ℕ}
  {n NU : ι → ℕ} {col ib : ι → ℕ → ℕ}

/-- The gear of every element. -/
lemma egear (h : CCtx m B s x mx n NU col ib) :
    Gear m (fun e : ElemF NU ib => B e.1.1) (fun e => col e.1.1 e.1.2) (p (p s w) w)
      (fun e => ((x e.1.1, e.1.2.val), (bits (ib e.1.1 e.1.2)).loc e.2)) :=
  ⟨h.elem_unit (ib:=ib) (unit_fetch _ h.tpc), h.elem_unit (ib:=ib) (unit_fetch _ h.tc),
    h.elem_unit (ib:=ib) (unit_fetch _ h.txr), h.uBig.reindex (fun e : ElemF NU ib => e.1)⟩

end CCtx

namespace Eng
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]
variable (E : Eng α ρ σ)
variable {ι : Type U} {m : Bool} {B : ι → ℕ} {s : Ty} {x : ι → T s} {cl : Paint}
variable {n hh μ : ι → ℕ}

/-- **Loading the class table from the own jobs.** -/
lemma load
    (h : CCtx m B s x E.X.n n (fun i => E.NUc (n i) (hh i) (μ i)) (fun i p => E.cUc (n i) (hh i) (μ i) p)
      (fun i p => E.iUc (n i) (hh i) (μ i) p))
    {J : ∀ i, ℕ → Bits (n i) → ℂ}
    (tJ : Has m B s (jobsT cl) x (fun i => jobsTape (n i) (E.NUc (n i) (hh i) (μ i) * E.W) (J i))) :
    Can m B s (a (a (a (c cl)))) x
      (fun i => ctab E.X E.R (E.NUc (n i) (hh i) (μ i)) (fun p => E.cUc (n i) (hh i) (μ i) p)
        (fun p => E.iUc (n i) (hh i) (μ i) p) (E.V0 (n i) (hh i) (μ i) (J i)))
      (fun i => E.NUc (n i) (hh i) (μ i) * 2^(n i)) := by
  let NU (i : ι) := E.NUc (n i) (hh i) (μ i)
  let col (i : ι) (p : ℕ) := E.cUc (n i) (hh i) (μ i) p
  let ib (i : ι) (p : ℕ) := E.iUc (n i) (hh i) (μ i) p
  have g := h.egear
  apply h.ctab_build _ rfl
  let yE (e : ElemF NU ib) : T (p (p s w) w) := ((x e.1.1, e.1.2.val), (bits (ib e.1.1 e.1.2)).loc e.2)
  let BE (e : ElemF NU ib) := B e.1.1
  have hsize : Knows m BE (p (p s w) w) yE (fun e => (fleet E.X E.R 0 (col e.1.1 e.1.2)).n) :=
    (Can.wc E.R.n).times (g.grid_size E.X 0) (Small.const _ _) (g.grid_small E.X 0)
  have hlarge : Small BE (fun e => (fleet E.X E.R 0 (col e.1.1 e.1.2)).n) :=
    (Small.const _ E.R.n).mul (g.grid_small E.X 0)
  -- one beach
  let D := Σ e : ElemF NU ib, Beach α ρ 0 (col e.1.1 e.1.2)
  let yD (d : D) : T (p (p (p s w) w) w) := (yE d.1, (fleet E.X E.R 0 (col d.1.1.1 d.1.1.2)).loc d.2)
  let BD (d : D) := BE d.1
  have gD := g.descend (fun d : D => d.1) yD (t:=p (p (p s w) w) w) Can.first
  have hl : Knows m BD (p (p (p s w) w) w) yD (fun d => E.R.loc d.2.1) :=
    Can.addr_high (u:=fun d : D => d.2) (L:=fun _ => E.R) (R:=fun d => book E.X 0 (col d.1.1.1 d.1.1.2))
      Can.second (gD.grid_size E.X 0) (hlarge.reindex (fun d : D => d.1))
  have hk : Knows m BD (p (p (p s w) w) w) yD (fun d => (book E.X 0 (col d.1.1.1 d.1.1.2)).loc d.2.2) :=
    Can.addr_low (u:=fun d : D => d.2) (L:=fun _ => E.R) (R:=fun d => book E.X 0 (col d.1.1.1 d.1.1.2))
      Can.second (gD.grid_size E.X 0) (hlarge.reindex (fun d : D => d.1))
  have hv : Has m BD (p (p (p s w) w) w) (c cl) yD
      (fun d => E.V0 (n d.1.1.1) (hh d.1.1.1) (μ d.1.1.1) (J d.1.1.1) d.1.1.2 d.1.2 d.2) := by
    apply Can.cases_code (q:=fun d : D => d.2.1) E.R hl
    intro r'
    let K := {d : D // d.2.1 = r'}
    let BK (κ : K) := BD κ.1
    cases hL : E.liveOf r' with
    | none =>
      refine (Can.zero (cl:=cl)).cong (fun _ => rfl) (fun κ => ?_)
      show (0 : ℂ) = E.V0 _ _ _ _ κ.1.1.1.2 κ.1.1.2 κ.1.2
      unfold V0
      rw [κ.2, hL]
    | some l0 =>
      let gK := gD.descend (fun κ : K => κ.1) (fun κ => yD κ.1) (t:=p (p (p s w) w) w) Can.id
      obtain ⟨hrest, hfib⟩ := gK.from_gridB E.X 0 (E.St l0) (E.Xt l0) (fun κ => κ.1.2.2)
        (hk.reindex (fun κ : K => κ.1))
      let i_ (κ : K) := κ.1.1.1.1
      let p_ (κ : K) := κ.1.1.1.2
      let c_ (κ : K) := col (i_ κ) (p_ κ)
      have hbig : Small BK (fun κ => 2^(n (i_ κ))) := h.big.reindex (fun κ : K => i_ κ)
      have hk1 : Knows m BK (p (p (p s w) w) w) (fun κ => yD κ.1) (fun κ => 2^(E.tr l0 * c_ κ)) :=
        gK.powerB (E.tr l0)
      have hk3 : Knows m BK (p (p (p s w) w) w) (fun κ => yD κ.1)
          (fun κ => 2^(E.tr l0 * c_ κ + (E.Xt l0).n * c_ κ)) :=
        (gK.powerB E.X.n).cong (fun _ => rfl) (fun κ => by simp only [c_, col, i_, p_]; rw [← E.Xt_n l0]; ring_nf)
      have hs1 : Small BK (fun κ => 2^(E.tr l0 * c_ κ)) := gK.boundB _
      have hs3 : Small BK (fun κ => 2^(E.tr l0 * c_ κ + (E.Xt l0).n * c_ κ)) :=
        (gK.boundB E.X.n).mono (fun κ => le_of_eq (by simp only [c_, col, i_, p_]; rw [← E.Xt_n l0]; ring_nf))
      have hsr : Small BK (fun κ => (book (E.Xt l0) 0 (c_ κ)).loc (E.St l0 |>.peel 0 (c_ κ) κ.1.2.2).1) :=
        (gK.grid_small (E.Xt l0) 0).mono (fun κ => ((book _ 0 _).bd _).le)
      have hsf : Small BK (fun κ => (bits (E.tr l0 * c_ κ)).loc (E.St l0 |>.peel 0 (c_ κ) κ.1.2.2).2) :=
        hs1.mono (fun κ => ((bits _).bd _).le)
      have hq : Knows m BK (p (p (p s w) w) w) (fun κ => yD κ.1)
          (fun κ => (bits (ib (i_ κ) (p_ κ))).loc κ.1.1.2) :=
        ((Can.first.then_do Can.second : Knows m BD (p (p (p s w) w) w) yD
          (fun d => (bits (ib d.1.1.1 d.1.1.2)).loc d.1.2))).reindex (fun κ : K => κ.1)
      have hsq : Small BK (fun κ => (bits (ib (i_ κ) (p_ κ))).loc κ.1.1.2) :=
        hbig.mono (fun κ => le_trans ((bits _).bd _).le (h.two_ib_le _ _))
      have haddr : Knows m BK (p (p (p s w) w) w) (fun κ => yD κ.1)
          (fun κ => (bits (n (i_ κ))).loc (E.placeT (n (i_ κ)) (hh (i_ κ)) (μ (i_ κ)) (p_ κ) l0
            (κ.1.1.2, κ.1.2.2.2))) := by
        refine ((hfib.plus (hk1.times hrest hs1 hsr) hsf (hs1.mul hsr)).plus (hk3.times hq hs3 hsq)
          (hsf.add (hs1.mul hsr)) (hs3.mul hsq)).cong (fun _ => rfl) (fun κ => ?_)
        unfold placeT
        rw [placeS_loc]
        have hb0 : κ.1.2.2 = ((0 : Bits 0), κ.1.2.2.2) := Prod.ext (Subsingleton.elim _ _) rfl
        rw [hb0]
      -- the job of the slot `p*W + loc l0`
      have hpv : Knows m BK (p (p (p s w) w) w) (fun κ => yD κ.1) (fun κ => (p_ κ).val) :=
        ((Can.first.then_do (Can.first.then_do Can.second) : Knows m BD (p (p (p s w) w) w) yD
          (fun d => d.1.1.2.val))).reindex (fun κ : K => κ.1)
      have hNUs : Small BK (fun κ => NU (i_ κ)) := h.nuS.reindex (fun κ : K => i_ κ)
      have hpvs : Small BK (fun κ => (p_ κ).val) := hNUs.mono (fun κ => (p_ κ).2.le)
      have hjix : Knows m BK (p (p (p s w) w) w) (fun κ => yD κ.1) (fun κ => (p_ κ).val * E.W + E.Q.loc l0) :=
        (hpv.times (Can.wc E.W) hpvs (Small.const _ _)).plus (Can.wc _) (hpvs.mul (Small.const _ _))
          (Small.const _ _)
      have hjlt : ∀ κ : K, (p_ κ).val * E.W + E.Q.loc l0 < NU (i_ κ) * E.W := fun κ => by
        have h1 := (p_ κ).2
        have h2 : E.Q.loc l0 < E.W := E.Q.bd l0
        calc (p_ κ).val * E.W + E.Q.loc l0 < (p_ κ).val * E.W + E.W := by omega
          _ = ((p_ κ).val + 1) * E.W := by ring
          _ ≤ NU (i_ κ) * E.W := Nat.mul_le_mul_right _ h1
      have tJE : Has m BE (p (p s w) w) (jobsT cl) yE
          (fun e => jobsTape (n e.1.1) (NU e.1.1 * E.W) (J e.1.1)) :=
        (Can.first.then_do Can.first).then_do (tJ.reindex (fun e : ElemF NU ib => e.1.1))
      have tJD : Has m BK (p (p (p s w) w) w) (jobsT cl) (fun κ => yD κ.1)
          (fun κ => jobsTape (n (i_ κ)) (NU (i_ κ) * E.W) (J (i_ κ))) :=
        ((Can.first.then_do (tJE.reindex (fun d : D => d.1)) : Has m BD (p (p (p s w) w) w) (jobsT cl) yD
          (fun d => jobsTape (n d.1.1.1) (NU d.1.1.1 * E.W) (J d.1.1.1)))).reindex (fun κ : K => κ.1)
      have hJt := Can.fetch (t:=a (c cl)) (L:=fun κ : K => Layout.std (NU (i_ κ) * E.W))
        (v:=fun κ t => (bits (n (i_ κ))).tape (J (i_ κ) t))
        (i:=fun κ => (⟨(p_ κ).val * E.W + E.Q.loc l0, hjlt κ⟩ : Fin (NU (i_ κ) * E.W))) tJD hjix
      have hval := Can.fetch (t:=c cl) (L:=fun κ : K => bits (n (i_ κ)))
        (v:=fun κ => J (i_ κ) ((p_ κ).val * E.W + E.Q.loc l0))
        (i:=fun κ => E.placeT (n (i_ κ)) (hh (i_ κ)) (μ (i_ κ)) (p_ κ) l0 (κ.1.1.2, κ.1.2.2.2)) hJt haddr
      refine hval.cong (fun _ => rfl) (fun κ => ?_)
      show _ = E.V0 _ _ _ _ κ.1.1.1.2 κ.1.1.2 κ.1.2
      unfold V0
      rw [κ.2, hL]
  have HL := Can.layout (t:=c cl) (L:=fun e : ElemF NU ib => fleet E.X E.R 0 (col e.1.1 e.1.2))
    (v:=fun e => E.V0 (n e.1.1) (hh e.1.1) (μ e.1.1) (J e.1.1) e.1.2 e.2) (P:=fun _ => 0) (W:=fun _ => 0)
    hsize hv hlarge
  refine HL.mono (fun e => ?_)
  simp [fleet, col]

lemma roleAt_of (t : ℕ) (σ0 : σ) (h : E.Q.loc σ0 = t % E.W) : E.roleAt t = σ0 := by
  apply E.Q.inj; rw [loc_roleAt, h]

/-- **Answering the own slots from the class table.** -/
lemma unload
    (h : CCtx m B s x E.X.n n (fun i => E.NUc (n i) (hh i) (μ i)) (fun i p => E.cUc (n i) (hh i) (μ i) p)
      (fun i p => E.iUc (n i) (hh i) (μ i) p))
    {V : ∀ i, E.CState (n i) (hh i) (μ i)}
    (ct : Has m B s (a (a (a (c cl)))) x (fun i => ctab E.X E.R (E.NUc (n i) (hh i) (μ i))
      (fun p => E.cUc (n i) (hh i) (μ i) p) (fun p => E.iUc (n i) (hh i) (μ i) p) (V i))) :
    Can m B s (jobsT cl) x
      (fun i => jobsTape (n i) (E.NUc (n i) (hh i) (μ i) * E.W) (E.unl (n i) (hh i) (μ i) (V i)))
      (fun i => E.NUc (n i) (hh i) (μ i) * E.W * 2^(n i)) := by
  let NU (i : ι) := E.NUc (n i) (hh i) (μ i)
  let NJ (i : ι) := NU i * E.W
  let col (i : ι) (p : ℕ) := E.cUc (n i) (hh i) (μ i) p
  let ib (i : ι) (p : ℕ) := E.iUc (n i) (hh i) (μ i) p
  have G := h.erig ct
  let EN := EntF NJ n
  let yE (en : EN) : T (p (p s w) w) := ((x en.1.1, en.1.2.val), (bits (n en.1.1)).loc en.2)
  let BE (en : EN) := B en.1.1
  have hE : Knows m BE (p (p s w) w) yE (fun en => (bits (n en.1.1)).loc en.2) := Can.second
  have hbig : Small BE (fun en => 2^(n en.1.1)) := h.big.reindex (fun en : EN => en.1.1)
  have hEs : Small BE (fun en => (bits (n en.1.1)).loc en.2) := hbig.mono (fun en => ((bits _).bd _).le)
  have hNJs : Small B NJ := h.nuS.mul (Small.const _ _)
  have ht : Knows m BE (p (p s w) w) yE (fun en => en.1.2.val) := Can.first.then_do Can.second
  have hts : Small BE (fun en => en.1.2.val) := (hNJs.reindex (fun en : EN => en.1.1)).mono (fun en => en.1.2.2.le)
  have hpt : Knows m BE (p (p s w) w) yE (fun en => en.1.2.val / E.W) := ht.dvdW (Can.wc E.W) hts
  have hat : Knows m BE (p (p s w) w) yE (fun en => en.1.2.val % E.W) := ht.modW (Can.wc E.W) hts
  have hplt : ∀ en : EN, en.1.2.val / E.W < NU en.1.1 := fun en => (Nat.div_lt_iff_lt_mul E.W_pos).2 en.1.2.2
  have hent : Has m BE (p (p s w) w) (c cl) yE
      (fun en => E.unl (n en.1.1) (hh en.1.1) (μ en.1.1) (V en.1.1) en.1.2.val en.2) := by
    apply Can.cases_code (q:=fun en : EN => E.roleAt en.1.2.val) E.Q
      (hat.cong (fun _ => rfl) (fun en => (E.loc_roleAt _).symm))
    intro σ0
    let K := {en : EN // E.roleAt en.1.2.val = σ0}
    let BK (κ : K) := BE κ.1
    let yK (κ : K) := yE κ.1
    let i_ (κ : K) := κ.1.1.1
    let p_ (κ : K) : Fin (NU (i_ κ)) := ⟨κ.1.1.2.val / E.W, hplt κ.1⟩
    let PL (κ : K) := E.placeT (n (i_ κ)) (hh (i_ κ)) (μ (i_ κ)) (p_ κ) σ0
    let qy (κ : K) := (PL κ).symm κ.1.2
    let j (κ : K) : ElemF NU ib := ⟨⟨i_ κ, p_ κ⟩, (qy κ).1⟩
    have hEK := hE.reindex (fun κ : K => κ.1)
    have hEsK := hEs.reindex (fun κ : K => κ.1)
    have hppK : Knows m BK (p (p s w) w) yK (fun κ => (p_ κ).val) := hpt.reindex (fun κ : K => κ.1)
    have hpcK : Knows m BK (p (p s w) w) yK (fun κ => 2^(col (i_ κ) (p_ κ))) :=
      Can.fetch (t:=w) (L:=fun κ : K => Layout.std (NU (i_ κ))) (v:=fun κ q => 2^(col (i_ κ) q)) (i:=p_)
        (((Can.first.then_do Can.first).then_do (h.tpc.reindex (fun en : EN => en.1.1)) : Has m BE (p (p s w) w)
          (a w) yE (fun en => (Layout.std (NU en.1.1)).tape (fun q => 2^(col en.1.1 q)))).reindex
          (fun κ : K => κ.1)) hppK
    have hcbig : Small BK (fun κ => 2^(col (i_ κ) (p_ κ))) :=
      (hbig.reindex (fun κ : K => κ.1)).mono (fun κ => h.two_c_le (i_ κ) (p_ κ))
    have hXc : Knows m BK (p (p s w) w) yK (fun κ => 2^(E.tr σ0 * col (i_ κ) (p_ κ) +
        (E.Xt σ0).n * col (i_ κ) (p_ κ))) :=
      (hpcK.wpow_fixed E.X.n hcbig).cong (fun _ => rfl) (fun κ => by
        rw [← pow_mul, ← E.Xt_n σ0]; ring_nf)
    have hq : Knows m BK (p (p s w) w) yK (fun κ => (bits (ib (i_ κ) (p_ κ))).loc (qy κ).1) :=
      (hEK.dvdW hXc hEsK).cong (fun _ => rfl) (fun κ => (placeS_parts (E.St σ0) (E.Xt σ0) _ _ _ _ κ.1.2).2.2)
    have hxK : Has m BK (p (p s w) w) s yK (fun κ => x (i_ κ)) :=
      ((Can.first.then_do Can.first : Has m BE (p (p s w) w) s yE (fun en => x en.1.1))).reindex (fun κ : K => κ.1)
    have g : Has m (fun κ => B (j κ).1.1) (p (p s w) w) (p (p s w) w) yK
        (fun κ => ((x (j κ).1.1, (j κ).1.2.val), (bits (ib (j κ).1.1 (j κ).1.2)).loc (j κ).2)) :=
      (hxK.pair hppK).pair hq
    have G1 := G.gather j yK g
    have hk1 : Knows m BK (p (p s w) w) yK (fun κ => 2^(E.tr σ0 * col (i_ κ) (p_ κ))) := G1.rig.gear.powerB _
    have hk2 : Knows m BK (p (p s w) w) yK (fun κ => 2^((E.Xt σ0).n * col (i_ κ) (p_ κ))) := G1.rig.gear.powerB _
    have hfib : Knows m BK (p (p s w) w) yK
        (fun κ => (bits (E.tr σ0 * col (i_ κ) (p_ κ))).loc (E.St σ0 |>.peel 0 (col (i_ κ) (p_ κ)) (0, (qy κ).2)).2) :=
      (hEK.modW hk1 hEsK).cong (fun _ => rfl) (fun κ => (placeS_parts (E.St σ0) (E.Xt σ0) _ _ _ _ κ.1.2).1)
    have hrest : Knows m BK (p (p s w) w) yK
        (fun κ => (book (E.Xt σ0) 0 (col (i_ κ) (p_ κ))).loc (E.St σ0 |>.peel 0 (col (i_ κ) (p_ κ)) (0, (qy κ).2)).1) :=
      ((hEK.dvdW hk1 hEsK).modW hk2 hEsK.div).cong (fun _ => rfl)
        (fun κ => (placeS_parts (E.St σ0) (E.Xt σ0) _ _ _ _ κ.1.2).2.1)
    have hgrid := G1.rig.gear.to_gridB E.X 0 (E.St σ0) (E.Xt σ0)
      (fun κ => (E.St σ0).peel 0 (col (i_ κ) (p_ κ)) (0, (qy κ).2)) hrest hfib
    have hb : Knows m BK (p (p s w) w) yK (fun κ => (book E.X 0 (col (i_ κ) (p_ κ))).loc ((0 : Bits 0), (qy κ).2)) :=
      hgrid.cong (fun _ => rfl) (fun κ => by rw [Equiv.symm_apply_apply])
    have hr := G1.rig.read (fun κ => (E.e σ0, ((0 : Bits 0), (qy κ).2))) (Can.wc (E.R.loc (E.e σ0))) hb
    refine hr.cong (fun _ => rfl) (fun κ => ?_)
    show V (i_ κ) (p_ κ) (qy κ).1 (E.e σ0, (0, (qy κ).2)) = E.unl _ _ _ _ κ.1.1.2.val κ.1.2
    unfold unl
    rw [dif_pos (hplt κ.1)]
    have hr0 : E.roleAt κ.1.1.2.val = σ0 := κ.2
    simp only [hr0]
    rfl
  have hlen : Knows m (fun u : UnitF NJ => B u.1) (p s w) (fun u => (x u.1, u.2.val)) (fun u => (bits (n u.1)).n) :=
    Can.first.then_do (h.p2n.reindex (fun u : UnitF NJ => u.1))
  have HI := Can.layout (t:=c cl) (L:=fun u : UnitF NJ => bits (n u.1))
    (v:=fun u e => E.unl (n u.1) (hh u.1) (μ u.1) (V u.1) u.2.val e) (P:=fun _ => 0) (W:=fun _ => 0) hlen
    (hent.mono (fun _ => Nat.zero_le _)) (h.big.reindex (fun u : UnitF NJ => u.1))
  have HO := Can.layout (t:=a (c cl)) (L:=fun i => Layout.std (NJ i))
    (v:=fun i t => (bits (n i)).tape (E.unl (n i) (hh i) (μ i) (V i) t)) (P:=fun i => 2^(n i))
    (W:=fun _ => 0) (h.nuK.times (Can.wc E.W) h.nuS (Small.const _ _)) (HI.mono (fun u => by simp)) hNJs
  refine HO.weaken ⟨3, fun i => ?_⟩
  change 0 + NJ i + NJ i * 2^(n i) + 1 ≤ 3 * (NJ i * 2^(n i) + 1)
  have h2 : NJ i ≤ NJ i * 2^(n i) := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
  omega

end Eng

end
end PowerSaving.RAM
end OAI

end
-- bos_merge: end Submission.Work.Mixed.Prog.LoadRAM

-- bos_merge: begin Submission.Work.Mixed.Prog.Acc
section

/-!
# Mixed engine, R3 program part 12: the source accumulator (agent e-r3prog)

A class returns, besides its own answers, the answered supply vectors its subtree consumed, in
consumption order, with their sizes.  After each child call it appends the child's own source
slots (in slot order) and the child's consumed list.

* `filterMap_range_eq`   the source sizes in slot order are `slotSize (nth srcP k)`;
* `concat3`              three tapes concatenated (pointer copies, linear in the number of entries).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset GF MXR
noncomputable section

universe U

lemma filterMap_range_eq (P : ℕ → Prop) [DecidablePred P] (f : ℕ → ℕ) (N : ℕ) :
    (List.range N).filterMap (fun t => if P t then some (f t) else none) =
      (List.range (Nat.count P N)).map (fun k => f (Nat.nth P k)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.filterMap_append, ih, Nat.count_succ]
    by_cases hp : P N
    · have e1 : List.filterMap (fun t => if P t then some (f t) else none) [N] = [f N] := by simp [hp]
      rw [e1, if_pos hp, List.range_succ, List.map_append]
      simp [Nat.nth_count hp]
    · simp [hp]

lemma getD_map_range (g : ℕ → ℕ) (N k : ℕ) (hk : k < N) : ((List.range N).map g).getD k 0 = g k := by
  rw [List.getD_eq_getElem _ _ (by simpa using hk)]
  simp

section Concat
variable {ι : Type U} {m : Bool} {B : ι → ℕ} {s t : Ty} {x : ι → T s}

/-- Three tapes concatenated. -/
def cat3 {μ : Type*} (L1 L2 L3 : ℕ) (f1 f2 f3 : ℕ → μ) (k : ℕ) : μ :=
  if k < L1 then f1 k else if k < L1 + L2 then f2 (k - L1) else f3 (k - L1 - L2)

lemma concat3 {L1 L2 L3 : ι → ℕ} {f1 f2 f3 : ι → ℕ → T t}
    (h1 : Has m B s (a t) x (fun i => (Layout.std (L1 i)).tape (fun k => f1 i k)))
    (h2 : Has m B s (a t) x (fun i => (Layout.std (L2 i)).tape (fun k => f2 i k)))
    (h3 : Has m B s (a t) x (fun i => (Layout.std (L3 i)).tape (fun k => f3 i k)))
    (k1 : Knows m B s x L1) (k2 : Knows m B s x L2) (k3 : Knows m B s x L3)
    (s1 : Small B L1) (s2 : Small B L2) (s3 : Small B L3) :
    Can m B s (a t) x (fun i => (Layout.std (L1 i + L2 i + L3 i)).tape (fun k => cat3 (L1 i) (L2 i) (L3 i) (f1 i) (f2 i) (f3 i) k))
      (fun i => L1 i + L2 i + L3 i) := by
  let N (i : ι) := L1 i + L2 i + L3 i
  have hN : Knows m B s x N := (k1.plus k2 s1 s2).plus k3 (s1.add s2) s3
  have hNs : Small B N := (s1.add s2).add s3
  let UN := UnitF N
  let yU (u : UN) : T (p s w) := (x u.1, u.2.val)
  have hk : Knows m (fun u : UN => B u.1) (p s w) yU (fun u => u.2.val) := Can.second
  have hks : Small (fun u : UN => B u.1) (fun u => u.2.val) := (hNs.reindex (fun u : UN => u.1)).mono (fun u => u.2.2.le)
  have K1 : Knows m (fun u : UN => B u.1) (p s w) yU (fun u => L1 u.1) := Can.first.then_do (k1.reindex _)
  have K2 : Knows m (fun u : UN => B u.1) (p s w) yU (fun u => L2 u.1) := Can.first.then_do (k2.reindex _)
  have S1 : Small (fun u : UN => B u.1) (fun u => L1 u.1) := s1.reindex _
  have S2 : Small (fun u : UN => B u.1) (fun u => L2 u.1) := s2.reindex _
  have T1U : Has m (fun u : UN => B u.1) (p s w) (a t) yU (fun u => (Layout.std (L1 u.1)).tape (fun k => f1 u.1 k)) :=
    Can.first.then_do (h1.reindex (fun u : UN => u.1))
  have T2U : Has m (fun u : UN => B u.1) (p s w) (a t) yU (fun u => (Layout.std (L2 u.1)).tape (fun k => f2 u.1 k)) :=
    Can.first.then_do (h2.reindex (fun u : UN => u.1))
  have T3U : Has m (fun u : UN => B u.1) (p s w) (a t) yU (fun u => (Layout.std (L3 u.1)).tape (fun k => f3 u.1 k)) :=
    Can.first.then_do (h3.reindex (fun u : UN => u.1))
  have hent : Has m (fun u : UN => B u.1) (p s w) t yU
      (fun u => cat3 (L1 u.1) (L2 u.1) (L3 u.1) (f1 u.1) (f2 u.1) (f3 u.1) u.2.val) := by
    apply Can.testz (hk.wlt K1 |> fun hh => ((Can.wc 1).wsub hh ((Small.const _ 1).mono (fun _ => Nat.sub_le _ _))))
    · -- k < L1
      let K := {u : UN // 1 - (if u.2.val < L1 u.1 then 1 else 0) = 0}
      have hlt : ∀ κ : K, κ.1.2.val < L1 κ.1.1 := fun κ => by
        have := κ.2; by_contra hc; simp [hc] at this
      refine (Can.fetch (t:=t) (L:=fun κ : K => Layout.std (L1 κ.1.1)) (v:=fun κ k => f1 κ.1.1 k)
        (i:=fun κ => ⟨κ.1.2.val, hlt κ⟩) (T1U.reindex (fun κ : K => κ.1))
        (hk.reindex (fun κ : K => κ.1))).cong (fun _ => rfl) (fun κ => ?_)
      simp [cat3, hlt κ]
    · apply Can.testz (((hk.wlt (K1.plus K2 S1 S2)) |> fun hh => ((Can.wc 1).wsub hh
        ((Small.const _ 1).mono (fun _ => Nat.sub_le _ _)))).reindex Subtype.val)
      · let K := {κ : {u : UN // 1 - (if u.2.val < L1 u.1 then 1 else 0) ≠ 0} //
          1 - (if κ.1.2.val < L1 κ.1.1 + L2 κ.1.1 then 1 else 0) = 0}
        have hge : ∀ κ : K, L1 κ.1.1.1 ≤ κ.1.1.2.val := fun κ => by
          have := κ.1.2; by_contra hc; simp [Nat.lt_of_not_le hc] at this
        have hlt : ∀ κ : K, κ.1.1.2.val - L1 κ.1.1.1 < L2 κ.1.1.1 := fun κ => by
          have := κ.2
          have h2 : κ.1.1.2.val < L1 κ.1.1.1 + L2 κ.1.1.1 := by by_contra hc; simp [hc] at this
          have := hge κ; omega
        refine (Can.fetch (t:=t) (L:=fun κ : K => Layout.std (L2 κ.1.1.1)) (v:=fun κ k => f2 κ.1.1.1 k)
          (i:=fun κ => ⟨κ.1.1.2.val - L1 κ.1.1.1, hlt κ⟩)
          (T2U.reindex (fun κ : K => κ.1.1))
          ((hk.wsub K1 hks.sub).reindex (fun κ : K => κ.1.1))).cong (fun _ => rfl) (fun κ => ?_)
        have h1 : ¬ κ.1.1.2.val < L1 κ.1.1.1 := Nat.not_lt.mpr (hge κ)
        have h2 : κ.1.1.2.val < L1 κ.1.1.1 + L2 κ.1.1.1 := by have := hlt κ; omega
        simp [cat3, h1, h2]
      · let K := {κ : {u : UN // 1 - (if u.2.val < L1 u.1 then 1 else 0) ≠ 0} //
          1 - (if κ.1.2.val < L1 κ.1.1 + L2 κ.1.1 then 1 else 0) ≠ 0}
        have hge : ∀ κ : K, L1 κ.1.1.1 + L2 κ.1.1.1 ≤ κ.1.1.2.val := fun κ => by
          have := κ.2; by_contra hc; simp [Nat.lt_of_not_le hc] at this
        have hlt : ∀ κ : K, κ.1.1.2.val - L1 κ.1.1.1 - L2 κ.1.1.1 < L3 κ.1.1.1 := fun κ => by
          have := κ.1.1.2.2; have := hge κ; simp only [N] at *; omega
        refine (Can.fetch (t:=t) (L:=fun κ : K => Layout.std (L3 κ.1.1.1)) (v:=fun κ k => f3 κ.1.1.1 k)
          (i:=fun κ => ⟨κ.1.1.2.val - L1 κ.1.1.1 - L2 κ.1.1.1, hlt κ⟩)
          (T3U.reindex (fun κ : K => κ.1.1))
          (((hk.wsub K1 hks.sub).wsub K2 hks.sub.sub).reindex (fun κ : K => κ.1.1))).cong
          (fun _ => rfl) (fun κ => ?_)
        have h1 : ¬ κ.1.1.2.val < L1 κ.1.1.1 := by have := hge κ; omega
        have h2 : ¬ κ.1.1.2.val < L1 κ.1.1.1 + L2 κ.1.1.1 := Nat.not_lt.mpr (hge κ)
        simp [cat3, h1, h2]
  have H := Can.layout (t:=t) (L:=fun i => Layout.std (N i)) (v:=fun i k => cat3 (L1 i) (L2 i) (L3 i) (f1 i) (f2 i) (f3 i) k)
    (P:=fun _ => 0) (W:=fun _ => 0) hN (hent.mono (fun _ => Nat.zero_le _)) hNs
  refine H.mono (fun i => ?_)
  change 0 + N i + N i * 0 ≤ N i
  omega

end Concat

end
end PowerSaving.RAM
end OAI

end
-- bos_merge: end Submission.Work.Mixed.Prog.Acc

-- bos_merge: begin Submission.Work.Mixed.Prog.SweepMath
section

/-!
# Mixed engine, R3 program part 13: facts about the routing (agent e-r3prog)

* `slotR_spec`    every parent unit `p` feeds exactly the child slot `slotR p` (separation is used here);
* `ownSrc_len`, `ownSrc_getD`   the source slots in order;
* `cjob_src`      a source slot carries the supply vector at the running offset plus its rank;
* `stepV_block`   a block letter on the class state is `ferryM` of its splitting's kernel.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset GF MXR
noncomputable section

namespace Eng
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]
variable (E : Eng α ρ σ)

lemma tq_ge (a : ℕ) (ha : a < E.W) (r : ℕ) (hr : ∀ l, r < E.tr l) : r < E.tq a := by
  unfold tq; rw [dif_pos ha]; exact hr _

/-- **Every parent unit feeds exactly one child slot.** -/
theorem slotR_spec (n h μ r : ℕ) (hr : ∀ l, r < E.tr l) (p : Fin (E.NUc n (h+1) μ)) :
    E.slotR n h μ r p < E.NUc n h (μ * r) * E.W ∧ E.flR n h μ r (E.slotR n h μ r p) ≠ 0 ∧
      E.ppR n h μ r (E.slotR n h μ r p) = p ∧
      E.slotSize n h (μ * r) (E.slotR n h μ r p) = r * E.cUc n (h+1) μ p := by
  obtain ⟨hreg, hlt, hpc⟩ := MXR.U_spec p.2 (W:=E.W) (tq:=E.tq) (mx:=E.mx) (n:=n) (h:=h+1) (ρ:=μ)
  set u := E.Uc n (h+1) μ p with hu
  have hW := E.W_pos
  set τ := u / E.W
  set a0 := u % E.W
  have ha0 : a0 < E.W := Nat.mod_lt _ hW
  have hu' : a0 + E.W * τ = u := by rw [Nat.add_comm]; exact Nat.div_add_mod u E.W
  have hτ : τ < E.W^h := by rw [Nat.div_lt_iff_lt_mul hW, ← pow_succ]; exact hlt
  -- the child unit τ is in the child's region (separation)
  have hcol : colS E.W E.tq (h+1) u = E.tq a0 * colS E.W E.tq h τ := by
    rw [← hu']; exact colS_cons E.W E.tq h a0 τ ha0
  have hregc : inRS E.W E.tq E.mx n h (μ * r) τ := by
    refine ⟨hτ, ?_⟩
    have h1 := hreg.2
    rw [hcol] at h1
    have h2 : r ≤ E.tq a0 := (E.tq_ge a0 ha0 r hr).le
    calc E.mx * (μ * r * colS E.W E.tq h τ) = E.mx * (μ * (r * colS E.W E.tq h τ)) := by ring
      _ ≤ E.mx * (μ * (E.tq a0 * colS E.W E.tq h τ)) := by gcongr
      _ ≤ n := h1
  have hpc' := PC_lt hregc
  have hUPC : E.Uc n h (μ * r) (E.PCc n h (μ * r) τ) = τ := U_PC hregc
  have hslot : E.slotR n h μ r p = E.PCc n h (μ * r) τ * E.W + a0 := rfl
  have e1 : E.slotR n h μ r p % E.W = a0 := by
    rw [hslot, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha0]
  have e2 : E.slotR n h μ r p / E.W = E.PCc n h (μ * r) τ := by
    rw [hslot, Nat.add_comm, Nat.add_mul_div_right _ _ hW, Nat.div_eq_of_lt ha0, zero_add]
  have hlt' : E.slotR n h μ r p < E.NUc n h (μ * r) * E.W := by
    rw [hslot]
    calc E.PCc n h (μ * r) τ * E.W + a0 < E.PCc n h (μ * r) τ * E.W + E.W := by omega
      _ = (E.PCc n h (μ * r) τ + 1) * E.W := by ring
      _ ≤ E.NUc n h (μ * r) * E.W := Nat.mul_le_mul_right _ hpc'
  have hpar : E.parCode n h μ r (E.slotR n h μ r p) = u := by
    unfold parCode; rw [e1, e2]
    show a0 + E.W * E.Uc n h (μ * r) (E.PCc n h (μ * r) τ) = u
    rw [hUPC, hu']
  refine ⟨hlt', ?_, ?_, ?_⟩
  · unfold flR; rw [if_pos (show E.fedP n h μ r _ from ⟨hlt', by rw [hpar]; exact hreg⟩)]; exact one_ne_zero
  · unfold ppR; rw [hpar]; exact hpc
  · unfold slotSize cUc
    rw [e1, e2]
    show E.tq a0 * ((μ * r) * colS E.W E.tq h (E.Uc n h (μ * r) (E.PCc n h (μ * r) τ))) =
      r * (μ * colS E.W E.tq (h+1) u)
    rw [hUPC, hcol]; ring

lemma ownSrc_eq (n h μ r : ℕ) :
    E.ownSrc n h μ r = (List.range (Nat.count (E.srcP n h μ r) (E.NUc n h (μ * r) * E.W))).map
      (fun k => E.slotSize n h (μ * r) (Nat.nth (E.srcP n h μ r) k)) := by
  unfold ownSrc
  have : (List.range (E.NUc n h (μ * r) * E.W)).filterMap
      (fun t => if E.srcP n h μ r t then some (E.slotSize n h (μ * r) t) else none) =
      (List.range (Nat.count (E.srcP n h μ r) (E.NUc n h (μ * r) * E.W))).map
      (fun k => E.slotSize n h (μ * r) (Nat.nth (E.srcP n h μ r) k)) :=
    filterMap_range_eq (E.srcP n h μ r) (E.slotSize n h (μ * r)) _
  exact this

lemma ownSrc_len (n h μ r : ℕ) :
    (E.ownSrc n h μ r).length = Nat.count (E.srcP n h μ r) (E.NUc n h (μ * r) * E.W) := by
  rw [ownSrc_eq]; simp

/-- Source slots are exactly the slots that are not fed. -/
lemma fl_zero_iff (n h μ r t : ℕ) (ht : t < E.NUc n h (μ * r) * E.W) :
    E.flR n h μ r t = 0 ↔ E.srcP n h μ r t := by
  unfold flR
  constructor
  · intro h0
    refine ⟨ht, fun hin => ?_⟩
    rw [if_pos (show E.fedP n h μ r t from ⟨ht, hin⟩)] at h0
    exact one_ne_zero h0
  · intro hs
    rw [if_neg (show ¬ E.fedP n h μ r t from fun hh => hs.2 hh.2)]

/-- **A block letter on the class state is `ferryM` of the kernel on its splitting.** -/
lemma stepV_block {n h μ : ℕ} (V : E.CState n h μ) (l : ρ) (r : ℕ) (z : Fin r → Space α)
    (ind : LinearIndependent F z) :
    E.stepV V (.old (.block l r z ind)) =
      fun (p : Fin (E.NUc n h μ)) q => ferryM 0 (E.cUc n h μ p) l ((bS z ind).lift (kernel (Fin r))) (V p q) := by
  funext p q x
  have hM : blockMat z = (bS z ind).lift (kernel (Fin r)) :=
    blockMat_eq_lift (bS z ind) z (Classical.choose_spec (exists_split z ind))
  unfold stepV gferry ferryM
  simp only [GMove.act, BMove.act]
  rw [hM]

end Eng

end
end PowerSaving.RAM
end OAI

end
-- bos_merge: end Submission.Work.Mixed.Prog.SweepMath

-- bos_merge: begin Submission.Work.Mixed.Prog.Sweep
section

/-!
# Mixed engine, R3 program part 14: one letter of a class with its source accumulator (agent e-r3prog)

The sweep state of a class: `(class table, consumed answers, consumed sizes, running offset)`.

* `Eng.block_step`  a block letter of a class of height `h+1`: routing tables, ONE child call, read back,
                    accumulate the child's own sources and its consumed list.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset GF MXR
noncomputable section

universe U

/-- The sweep state of a class. -/
abbrev StT (cl : Paint) : Ty := p (a (a (a (c cl)))) (p (jobsT cl) (p (a w) w))

/-- Answered consumed supply vectors (sizes `A`, from offset `o`). -/
def accT (n o : ℕ) (sup : ℕ → Bits n → ℂ) (A : List ℕ) : Tape (Tape ℂ) :=
  jobsTape n A.length (fun k => hlow n (A.getD k 0) (sup (o + k)))
/-- Their sizes. -/
def szT (A : List ℕ) : Tape ℕ := (Layout.std A.length).tape (fun k => A.getD k 0)

namespace Eng
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]
variable (E : Eng α ρ σ)
variable {ι : Type U} {m : Bool} {cl : Paint} {b : Bank (portM cl) ι} {s : Ty} {x : ι → T s}
variable {n h μ o BS : ι → ℕ} {sup : ∀ i, ℕ → Bits (n i) → ℂ}

/-- The class table of a class family. -/
abbrev ctabE (n h μ : ℕ) (V : E.CState n h μ) : Tape (Tape (Tape ℂ)) :=
  ctab E.X E.R (E.NUc n h μ) (fun p => E.cUc n h μ p) (fun p => E.iUc n h μ p) V

/-- The accumulated part of one block letter of rank `r`. -/
def accR (n h μ r : ℕ) : List ℕ := E.ownSrc n h μ r ++ E.srcSizes n h (μ * r)

lemma tape_std_ext {μ' : Type*} {N N' : ℕ} (hN : N = N') (f : Fin N → μ') (g : Fin N' → μ')
    (hfg : ∀ k (h1 : k < N) (h2 : k < N'), f ⟨k, h1⟩ = g ⟨k, h2⟩) :
    (Layout.std N).tape f = (Layout.std N').tape g := by
  subst hN
  unfold Layout.tape
  congr 1
  funext j
  have hj : (Layout.std N).atFin j = j := by
    apply Fin.ext; exact Layout.loc_atFin (Layout.std N) j
  rw [hj]
  exact hfg j.val j.2 j.2

/-- **The accumulator after one child.** -/
lemma acc_cat (n o : ℕ) (sup : ℕ → Bits n → ℂ) (A own Ac : List ℕ) (Y' : ℕ → Bits n → ℂ) (nthS : ℕ → ℕ)
    (hY : ∀ k, k < own.length → Y' (nthS k) = hlow n (own.getD k 0) (sup (o + A.length + k))) :
    (Layout.std (A.length + own.length + Ac.length)).tape (fun k => cat3 A.length own.length Ac.length
      (fun k => (bits n).tape (hlow n (A.getD k 0) (sup (o + k))))
      (fun k => (bits n).tape (Y' (nthS k)))
      (fun k => (bits n).tape (hlow n (Ac.getD k 0) (sup (o + A.length + own.length + k)))) k) =
    accT n o sup (A ++ own ++ Ac) := by
  unfold accT jobsTape
  apply tape_std_ext (by simp [Nat.add_assoc])
  intro k h1 h2
  simp only [cat3]
  by_cases ha : k < A.length
  · rw [if_pos ha, List.append_assoc, List.getD_append _ _ _ _ ha]
  · rw [if_neg ha]
    by_cases hb : k < A.length + own.length
    · rw [if_pos hb, hY (k - A.length) (by omega), List.append_assoc,
        List.getD_append_right _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      congr 3; omega
    · rw [if_neg hb, List.append_assoc, List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by omega)]
      congr 3
      omega

lemma sz_cat (A own Ac : List ℕ) :
    (Layout.std (A.length + own.length + Ac.length)).tape (fun k => cat3 A.length own.length Ac.length
      (fun k => A.getD k 0) (fun k => own.getD k 0) (fun k => Ac.getD k 0) k) = szT (A ++ own ++ Ac) := by
  unfold szT
  apply tape_std_ext (by simp [Nat.add_assoc])
  intro k h1 h2
  simp only [cat3]
  by_cases ha : k < A.length
  · rw [if_pos ha, List.append_assoc, List.getD_append _ _ _ _ ha]
  · rw [if_neg ha]
    by_cases hb : k < A.length + own.length
    · rw [if_pos hb, List.append_assoc, List.getD_append_right _ _ _ _ (by omega),
        List.getD_append _ _ _ _ (by omega)]
    · rw [if_neg hb, List.append_assoc, List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by omega)]

/-- Cost of one block letter of a class of height `h+1`. -/
def blkCost (n h μ r L : ℕ) : ℕ :=
  E.rtCost n h μ r + (E.NUc n h (μ * r) * E.W + E.NUc n (h+1) μ) * 2^n + 2 * (L + (E.accR n h μ r).length) + 20

/-- **One block letter of a class of height `h+1`**: routing tables, ONE child call, read-back,
accumulation of the child's sources. -/
theorem block_step
    (cin : CIn m b.B s x n (fun i => h i + 1) μ)
    (cc : CCtx m b.B s x E.X.n n (fun i => E.NUc (n i) (h i + 1) (μ i)) (fun i p => E.cUc (n i) (h i + 1) (μ i) p)
      (fun i p => E.iUc (n i) (h i + 1) (μ i) p))
    (hWp : Knows m b.B s x (fun i => E.W^(h i + 1)))
    (hPCp : Has m b.B s (a w) x (fun i => (Layout.std (E.W^(h i + 1))).tape (fun t => E.PCc (n i) (h i + 1) (μ i) t)))
    (hUp : Has m b.B s (a w) x (fun i => (Layout.std (E.NUc (n i) (h i + 1) (μ i))).tape
      (fun p => E.Uc (n i) (h i + 1) (μ i) p)))
    (tsup : Has m b.B s (jobsT cl) x (fun i => jobsTape (n i) (BS i) (sup i))) (hBSs : Small b.B BS)
    {V : ∀ i, E.CState (n i) (h i + 1) (μ i)} {A : ι → List ℕ}
    (ct : Has m b.B s (a (a (a (c cl)))) x (fun i => E.ctabE (n i) (h i + 1) (μ i) (V i)))
    (tacc : Has m b.B s (jobsT cl) x (fun i => accT (n i) (o i) (sup i) (A i)))
    (tsz : Has m b.B s (a w) x (fun i => szT (A i)))
    (horun : Knows m b.B s x (fun i => o i + (A i).length))
    (l : ρ) (r : ℕ) (z : Fin r → Space α) (ind : LinearIndependent F z) (hr : r ≤ E.X.n)
    (hsep : ∀ l', r < E.tr l')
    (hfit : ∀ i, o i + (A i).length + (E.accR (n i) (h i) (μ i) r).length ≤ BS i)
    {τ : ι → ℕ}
    (hk : ∀ i, (b.use i (E.enc cl (E.childC (n i) (h i) (μ i) (BS i) (sup i) (V i) (o i + (A i).length) l r z ind hr))).OK
      (E.out cl (E.childC (n i) (h i) (μ i) (BS i) (sup i) (V i) (o i + (A i).length) l r z ind hr)) (τ i) (b.ext i)) :
    Able m b s (StT cl) x
      (fun i => (E.ctabE (n i) (h i + 1) (μ i) (E.stepV (V i) (.old (.block l r z ind))),
        accT (n i) (o i) (sup i) (A i ++ E.accR (n i) (h i) (μ i) r), szT (A i ++ E.accR (n i) (h i) (μ i) r),
        o i + (A i ++ E.accR (n i) (h i) (μ i) r).length))
      (fun i => E.blkCost (n i) (h i) (μ i) r (A i).length) τ := by
  let orun (i : ι) := o i + (A i).length
  have hos : Small b.B orun := hBSs.mono (fun i => by have := hfit i; simp only [orun]; omega)
  -- 1. routing tables
  have HR := E.can_route cin r horun hos hWp cc.nuK hPCp hUp
  let rt (i : ι) := E.rtVal (n i) (h i) (μ i) r (orun i)
  let x1 (i : ι) : T (p s RtT) := (x i, rt i)
  have F1 : ∀ {u : Ty} {z : ι → T u}, Has m b.B s u x z → Has m b.B (p s RtT) u x1 z :=
    fun g => Can.first.then_do g
  have cc1 := cc.ext rt
  have hR : Has m b.B (p s RtT) RtT x1 rt := Can.second
  let NU' (i : ι) := E.NUc (n i) (h i) (μ i * r)
  let NJ (i : ι) := NU' i * E.W
  have hNU' : Knows m b.B (p s RtT) x1 NU' := Can.fst (Can.snd (Can.fst hR))
  have hNU's : Small b.B NU' := (cin.child r).powS E.W |>.mono (fun i => E.NU_le' _ _ _)
  have hNJ : Knows m b.B (p s RtT) x1 NJ := hNU'.times (Can.wc E.W) hNU's (Small.const _ _)
  have hNJs : Small b.B NJ := hNU's.mul (Small.const _ _)
  have tfl : Has m b.B (p s RtT) (a w) x1
      (fun i => (Layout.std (NJ i)).tape (fun t => E.flR (n i) (h i) (μ i) r t)) := Can.fst (Can.snd hR)
  have tpp : Has m b.B (p s RtT) (a w) x1
      (fun i => (Layout.std (NJ i)).tape (fun t => E.ppR (n i) (h i) (μ i) r t)) := Can.fst (Can.snd (Can.snd hR))
  have tsi : Has m b.B (p s RtT) (a w) x1
      (fun i => (Layout.std (NJ i)).tape (fun t => E.siR (n i) (h i) (μ i) r (orun i) t)) :=
    Can.fst (Can.snd (Can.snd (Can.snd hR)))
  have tslot : Has m b.B (p s RtT) (a w) x1
      (fun i => (Layout.std (E.NUc (n i) (h i + 1) (μ i))).tape (fun p => E.slotR (n i) (h i) (μ i) r p)) :=
    Can.fst (Can.snd (Can.snd (Can.snd (Can.snd hR))))
  let ns (i : ι) := Nat.count (E.srcP (n i) (h i) (μ i) r) (NJ i)
  have tnth : Has m b.B (p s RtT) (a w) x1
      (fun i => (Layout.std (ns i)).tape (fun k => Nat.nth (E.srcP (n i) (h i) (μ i) r) k)) :=
    Can.fst (Can.snd (Can.snd (Can.snd (Can.snd (Can.snd hR)))))
  have tssz : Has m b.B (p s RtT) (a w) x1
      (fun i => (Layout.std (ns i)).tape (fun k => E.slotSize (n i) (h i) (μ i * r) (Nat.nth (E.srcP (n i) (h i) (μ i) r) k))) :=
    Can.snd (Can.snd (Can.snd (Can.snd (Can.snd (Can.snd hR)))))
  have hnsle : ∀ i, ns i = (E.ownSrc (n i) (h i) (μ i) r).length := fun i => (E.ownSrc_len _ _ _ _).symm
  have hnss : Small b.B ns := hNJs.mono (fun i => MXR.count_le_self _)
  have hns : Knows m b.B (p s RtT) x1 ns := tnth.len (hnss.mono (fun i => le_of_eq (by simp [Layout.tape, Layout.std])))
  -- 2. the block letter (ONE child call)
  have hpp : ∀ i t, E.flR (n i) (h i) (μ i) r t ≠ 0 → E.ppR (n i) (h i) (μ i) r t < E.NUc (n i) (h i + 1) (μ i) :=
    fun i t => E.ppR_lt _ _ _ _ t
  have hsi : ∀ i t, t < NJ i → E.flR (n i) (h i) (μ i) r t = 0 → E.siR (n i) (h i) (μ i) r (orun i) t < BS i := by
    intro i t ht hf
    have hsrc := (E.fl_zero_iff _ _ _ _ t ht).1 hf
    have h1 : Nat.count (E.srcP (n i) (h i) (μ i) r) t < ns i := count_lt_of_mem hsrc ht
    have h2 := hfit i
    have h3 : (E.ownSrc (n i) (h i) (μ i) r).length ≤ (E.accR (n i) (h i) (μ i) r).length := by
      simp [accR]
    unfold siR
    rw [hnsle] at h1
    simp only [orun]; omega
  have hslot := fun i (p : Fin (E.NUc (n i) (h i + 1) (μ i))) => E.slotR_spec (n i) (h i) (μ i) r hsep p
  let S := bS z ind
  let X' := bX (α:=α) r
  have hX' : X'.n + r = E.X.n := E.bX_n hr
  have hkd : Knows m b.B (p s RtT) x1 (fun i => h i + 1) := F1 cin.hK
  have hμ' : Knows m b.B (p s RtT) x1 (fun i => μ i * r) := F1 (cin.μK.times (Can.wc r) cin.μS (Small.const _ _))
  have ho' : Knows m b.B (p s RtT) x1 (fun i => orun i + ns i) := (F1 horun).plus hns hos hnss
  have hk' : ∀ i, (b.use i (mkIn cl (n i) (h i + 1) (μ i * r) (orun i + ns i)
      (jobsTape (n i) (NJ i) (cjob E.X S X' hX' l (cc1.fit i) (V i) (E.flR (n i) (h i) (μ i) r)
        (E.ppR (n i) (h i) (μ i) r) (E.siR (n i) (h i) (μ i) r (orun i)) (hpp i) (sup i)))
      (jobsTape (n i) (BS i) (sup i)))).OK
      (jobsTape (n i) (NJ i) (fun t => hlow (n i) (E.slotSize (n i) (h i) (μ i * r) t)
          (cjob E.X S X' hX' l (cc1.fit i) (V i) (E.flR (n i) (h i) (μ i) r) (E.ppR (n i) (h i) (μ i) r)
            (E.siR (n i) (h i) (μ i) r (orun i)) (hpp i) (sup i) t)),
        jobsTape (n i) (E.cons (n i) (h i) (μ i * r))
          (fun k => hlow (n i) (E.csz (n i) (h i) (μ i * r) k) (sup i (orun i + ns i + k))),
        (Layout.std (E.cons (n i) (h i) (μ i * r))).tape (fun k => E.csz (n i) (h i) (μ i * r) k))
      (τ i) (b.ext i) := by
    intro i
    have := hk i
    rw [hnsle i]
    exact this
  have HB := cc1.block_letter (F1 ct) S X' hX' l (NJ:=NJ) (BS:=BS) (kd:=fun i => h i + 1)
    (μ:=fun i => μ i * r) (o:=fun i => orun i + ns i) (fl:=fun i => E.flR (n i) (h i) (μ i) r)
    (pp:=fun i => E.ppR (n i) (h i) (μ i) r) (si:=fun i => E.siR (n i) (h i) (μ i) r (orun i))
    (slot:=fun i => E.slotR (n i) (h i) (μ i) r) (sz:=fun i => E.slotSize (n i) (h i) (μ i * r))
    hpp hsi hslot hNJ hNJs tfl tpp tsi tslot (F1 tsup) hkd hμ' ho' hk'
  -- 3. the accumulator, in the environment holding the call's answer
  let CJ (i : ι) := cjob E.X S X' hX' l (cc1.fit i) (V i) (E.flR (n i) (h i) (μ i) r) (E.ppR (n i) (h i) (μ i) r)
    (E.siR (n i) (h i) (μ i) r (orun i)) (hpp i) (sup i)
  let Y' (i : ι) (t : ℕ) := hlow (n i) (E.slotSize (n i) (h i) (μ i * r) t) (CJ i t)
  let ACC' (i : ι) := jobsTape (n i) (E.cons (n i) (h i) (μ i * r))
    (fun k => hlow (n i) (E.csz (n i) (h i) (μ i * r) k) (sup i (orun i + ns i + k)))
  let SZ' (i : ι) := (Layout.std (E.cons (n i) (h i) (μ i * r))).tape (fun k => E.csz (n i) (h i) (μ i * r) k)
  let ct' (i : ι) := ctab E.X E.R (E.NUc (n i) (h i + 1) (μ i)) (fun p => E.cUc (n i) (h i + 1) (μ i) p)
    (fun p => E.iUc (n i) (h i + 1) (μ i) p)
    (fun p q => ferryM 0 (E.cUc (n i) (h i + 1) (μ i) p) l (S.lift (kernel (Fin r))) (V i p q))
  let R2 (i : ι) : T (p (a (a (a (c cl)))) (portOut cl)) := (ct' i, jobsTape (n i) (NJ i) (Y' i), ACC' i, SZ' i)
  let x2 (i : ι) : T (p (p s RtT) (p (a (a (a (c cl)))) (portOut cl))) := (x1 i, R2 i)
  have F2 : ∀ {u : Ty} {z : ι → T u}, Has m b.B (p s RtT) u x1 z →
      Has m b.B (p (p s RtT) (p (a (a (a (c cl)))) (portOut cl))) u x2 z := fun g => Can.first.then_do g
  have hR2 : Has m b.B (p (p s RtT) (p (a (a (a (c cl)))) (portOut cl))) (p (a (a (a (c cl)))) (portOut cl)) x2 R2 :=
    Can.second
  -- the child's own source slots, answered, in slot order
  let SK := UnitF ns
  let yK (u : SK) : T (p (p (p s RtT) (p (a (a (a (c cl)))) (portOut cl))) w) := (x2 u.1, u.2.val)
  have hnthK : Knows m (fun u : SK => b.B u.1) (p (p (p s RtT) (p (a (a (a (c cl)))) (portOut cl))) w) yK
      (fun u => Nat.nth (E.srcP (n u.1) (h u.1) (μ u.1) r) u.2) := unit_fetch _ (F2 tnth)
  have hnthlt : ∀ u : SK, Nat.nth (E.srcP (n u.1) (h u.1) (μ u.1) r) u.2 < NJ u.1 := fun u =>
    (MXR.nth_spec u.2.2).2.1
  have hOS := Can.fetch (t:=a (c cl)) (L:=fun u : SK => Layout.std (NJ u.1))
    (v:=fun u t => (bits (n u.1)).tape (Y' u.1 t))
    (i:=fun u => (⟨Nat.nth (E.srcP (n u.1) (h u.1) (μ u.1) r) u.2, hnthlt u⟩ : Fin (NJ u.1)))
    (Can.first.then_do ((Can.fst (Can.snd hR2)).reindex (fun u : SK => u.1))) hnthK
  have TOS := tabC (t:=a (c cl)) (P:=fun _ => 0)
    (fun i (k : Fin (ns i)) => (bits (n i)).tape (Y' i (Nat.nth (E.srcP (n i) (h i) (μ i) r) k)))
    (F2 hns) hnss hOS
  let OS (i : ι) := (Layout.std (ns i)).tape (fun k : Fin (ns i) =>
    (bits (n i)).tape (Y' i (Nat.nth (E.srcP (n i) (h i) (μ i) r) k)))
  let x3 (i : ι) := (x2 i, OS i)
  let s3 : Ty := p (p (p s RtT) (p (a (a (a (c cl)))) (portOut cl))) (jobsT cl)
  have F3 : ∀ {u : Ty} {z : ι → T u}, Has m b.B s u x z → Has m b.B s3 u x3 z :=
    fun g => Can.first.then_do (F2 (F1 g))
  have hR3 : Has m b.B s3 (p (a (a (a (c cl)))) (portOut cl)) x3 R2 := Can.first.then_do hR2
  -- lengths
  have hAs : Small b.B (fun i => (A i).length) := hBSs.mono (fun i => by have := hfit i; omega)
  have hconsle : ∀ i, E.cons (n i) (h i) (μ i * r) ≤ BS i := fun i => by
    have := hfit i; simp [accR, cons] at *; omega
  have hcs : Small b.B (fun i => E.cons (n i) (h i) (μ i * r)) := hBSs.mono hconsle
  have kA : Knows m b.B s3 x3 (fun i => (A i).length) := (F3 tacc).len (hAs.mono (fun i => le_of_eq rfl))
  have kns : Knows m b.B s3 x3 ns := Can.first.then_do (F2 hns)
  have kc : Knows m b.B s3 x3 (fun i => E.cons (n i) (h i) (μ i * r)) :=
    (Can.fst (Can.snd (Can.snd hR3))).len (hcs.mono (fun i => le_of_eq rfl))
  have HACC := concat3 (t:=a (c cl)) (L1:=fun i => (A i).length) (L2:=ns) (L3:=fun i => E.cons (n i) (h i) (μ i * r))
    (f1:=fun i k => (bits (n i)).tape (hlow (n i) ((A i).getD k 0) (sup i (o i + k))))
    (f2:=fun i k => (bits (n i)).tape (Y' i (Nat.nth (E.srcP (n i) (h i) (μ i) r) k)))
    (f3:=fun i k => (bits (n i)).tape (hlow (n i) (E.csz (n i) (h i) (μ i * r) k) (sup i (orun i + ns i + k))))
    (F3 tacc) Can.second (Can.fst (Can.snd (Can.snd hR3))) kA kns kc hAs hnss hcs
  have HSZ := concat3 (t:=w) (L1:=fun i => (A i).length) (L2:=ns) (L3:=fun i => E.cons (n i) (h i) (μ i * r))
    (f1:=fun i k => (A i).getD k 0)
    (f2:=fun i k => E.slotSize (n i) (h i) (μ i * r) (Nat.nth (E.srcP (n i) (h i) (μ i) r) k))
    (f3:=fun i k => E.csz (n i) (h i) (μ i * r) k)
    (F3 tsz) (Can.first.then_do (F2 tssz)) (Can.snd (Can.snd (Can.snd hR3))) kA kns kc hAs hnss hcs
  have hor' : Knows m b.B s3 x3 (fun i => orun i + ns i + E.cons (n i) (h i) (μ i * r)) :=
    ((F3 horun).plus kns hos hnss).plus kc (hos.add hnss) hcs
  have HST := (Can.fst hR3).fork (HACC.fork (HSZ.fork hor'))
  -- 4. the values
  have eY : ∀ i k, k < (E.ownSrc (n i) (h i) (μ i) r).length →
      Y' i (Nat.nth (E.srcP (n i) (h i) (μ i) r) k) =
        hlow (n i) ((E.ownSrc (n i) (h i) (μ i) r).getD k 0) (sup i (o i + (A i).length + k)) := by
    intro i k hk
    rw [← hnsle i] at hk
    obtain ⟨hP, hlt, hcnt⟩ := MXR.nth_spec hk
    have hf0 : E.flR (n i) (h i) (μ i) r (Nat.nth (E.srcP (n i) (h i) (μ i) r) k) = 0 :=
      (E.fl_zero_iff _ _ _ _ _ hlt).2 hP
    simp only [Y', CJ]
    unfold cjob
    rw [dif_neg (fun hh => hh hf0)]
    rw [E.ownSrc_eq, getD_map_range _ _ _ hk]
    unfold siR
    rw [hcnt]
  have eACC : ∀ i, (Layout.std ((A i).length + ns i + E.cons (n i) (h i) (μ i * r))).tape (fun k =>
      cat3 (A i).length (ns i) (E.cons (n i) (h i) (μ i * r))
        (fun k => (bits (n i)).tape (hlow (n i) ((A i).getD k 0) (sup i (o i + k))))
        (fun k => (bits (n i)).tape (Y' i (Nat.nth (E.srcP (n i) (h i) (μ i) r) k)))
        (fun k => (bits (n i)).tape (hlow (n i) (E.csz (n i) (h i) (μ i * r) k) (sup i (orun i + ns i + k)))) k) =
      accT (n i) (o i) (sup i) (A i ++ E.accR (n i) (h i) (μ i) r) := by
    intro i
    have := acc_cat (n i) (o i) (sup i) (A i) (E.ownSrc (n i) (h i) (μ i) r) (E.srcSizes (n i) (h i) (μ i * r))
      (Y' i) (Nat.nth (E.srcP (n i) (h i) (μ i) r)) (eY i)
    show _ = accT (n i) (o i) (sup i) (A i ++ (E.ownSrc (n i) (h i) (μ i) r ++ E.srcSizes (n i) (h i) (μ i * r)))
    rw [← List.append_assoc, ← this, hnsle i]
    rfl
  have eSZ : ∀ i, (Layout.std ((A i).length + ns i + E.cons (n i) (h i) (μ i * r))).tape (fun k =>
      cat3 (A i).length (ns i) (E.cons (n i) (h i) (μ i * r)) (fun k => (A i).getD k 0)
        (fun k => E.slotSize (n i) (h i) (μ i * r) (Nat.nth (E.srcP (n i) (h i) (μ i) r) k))
        (fun k => E.csz (n i) (h i) (μ i * r) k) k) = szT (A i ++ E.accR (n i) (h i) (μ i) r) := by
    intro i
    show _ = szT (A i ++ (E.ownSrc (n i) (h i) (μ i) r ++ E.srcSizes (n i) (h i) (μ i * r)))
    rw [← List.append_assoc, ← sz_cat]
    apply tape_std_ext (by rw [hnsle i]; rfl)
    intro k h1 h2
    simp only [cat3]
    by_cases ha : k < (A i).length
    · rw [if_pos ha, if_pos ha]
    · rw [if_neg ha, if_neg ha]
      by_cases hb : k < (A i).length + ns i
      · have hns_def : ns i = Nat.count (E.srcP (n i) (h i) (μ i) r) (E.NUc (n i) (h i) (μ i * r) * E.W) := rfl
        rw [if_pos hb, if_pos (by rw [← hnsle i]; exact hb), E.ownSrc_eq, getD_map_range _ _ _ (by omega)]
      · rw [if_neg hb, if_neg (by rw [← hnsle i]; exact hb), hnsle i]
        rfl
  have ect : ∀ i, ct' i = E.ctabE (n i) (h i + 1) (μ i) (E.stepV (V i) (.old (.block l r z ind))) := by
    intro i; rw [E.stepV_block]
  have eor : ∀ i, orun i + ns i + E.cons (n i) (h i) (μ i * r) = o i + (A i ++ E.accR (n i) (h i) (μ i) r).length := by
    intro i
    show o i + (A i).length + ns i + (E.srcSizes (n i) (h i) (μ i * r)).length =
      o i + (A i ++ (E.ownSrc (n i) (h i) (μ i) r ++ E.srcSizes (n i) (h i) (μ i * r))).length
    rw [List.length_append, List.length_append, hnsle i]; omega
  have Hfin : Can m b.B s3 (StT cl) x3
      (fun i => (E.ctabE (n i) (h i + 1) (μ i) (E.stepV (V i) (.old (.block l r z ind))),
        accT (n i) (o i) (sup i) (A i ++ E.accR (n i) (h i) (μ i) r), szT (A i ++ E.accR (n i) (h i) (μ i) r),
        o i + (A i ++ E.accR (n i) (h i) (μ i) r).length))
      (fun i => 0 + ((A i).length + ns i + E.cons (n i) (h i) (μ i * r) +
        ((A i).length + ns i + E.cons (n i) (h i) (μ i * r) + 0))) :=
    HST.cong (fun _ => rfl) (fun i => Prod.ext (ect i) (Prod.ext (eACC i) (Prod.ext (eSZ i) (eor i))))
  have Hpost := TOS.save Hfin
  have H := (Able.of_can (b:=b) HR).save (HB.save (Able.of_can (b:=b) Hpost))
  refine H.weaken ⟨4, fun i => ?_⟩ (fun i => by simp)
  have hns' := hnsle i
  have hc' : E.cons (n i) (h i) (μ i * r) = (E.srcSizes (n i) (h i) (μ i * r)).length := rfl
  have hacc : (E.accR (n i) (h i) (μ i) r).length = ns i + E.cons (n i) (h i) (μ i * r) := by
    rw [hns', hc']; simp [accR]
  have hbk : E.blkCost (n i) (h i) (μ i) r (A i).length = E.rtCost (n i) (h i) (μ i) r +
      (NJ i + E.NUc (n i) (h i + 1) (μ i)) * 2^(n i) + 2 * ((A i).length + (ns i + E.cons (n i) (h i) (μ i * r))) + 20 := by
    unfold blkCost; rw [hacc]
  dsimp only
  rw [hbk, Nat.add_mul]
  generalize NJ i * 2^(n i) = X1
  generalize E.NUc (n i) (h i + 1) (μ i) * 2^(n i) = X2
  omega

/-- What the letters of a word add to the accumulator. -/
def accW (n h μ : ℕ) (ws : GWord α ρ) : List ℕ := (blockRanks ws).flatMap (fun r => E.accR n h μ r)

lemma accW_cons (n h μ : ℕ) (mv : GMove α ρ) (ws : GWord α ρ) :
    E.accW n h μ (mv :: ws) = (match mv.rk? with | some r => E.accR n h μ r | none => []) ++ E.accW n h μ ws := by
  unfold accW blockRanks
  rw [List.filterMap_cons]
  cases mv.rk? <;> simp

/-- Sweep cost of a word for a class of height `h+1` (accumulator length `L` before it). -/
def swCost (n h μ : ℕ) : ℕ → GWord α ρ → ℕ
  | _, [] => 0
  | L, mv :: ws => (match mv.rk? with
      | some r => E.blkCost n h μ r L
      | none => E.NUc n (h+1) μ * 2^n) +
      swCost n h μ (L + (match mv.rk? with | some r => (E.accR n h μ r).length | none => 0)) ws

lemma runV_cons {n h μ : ℕ} (V : E.CState n h μ) (mv : GMove α ρ) (ws : GWord α ρ) :
    E.runV V (mv :: ws) = E.runV (E.stepV V mv) ws := by
  funext p q; unfold runV stepV; exact gcoast_cons 0 _ mv ws (V p q)

lemma runV_nil {n h μ : ℕ} (V : E.CState n h μ) : E.runV V [] = V := by
  funext p q x; rfl

end Eng

end
end PowerSaving.RAM
end OAI

end
-- bos_merge: end Submission.Work.Mixed.Prog.Sweep

-- bos_merge: begin Submission.Work.Mixed.Prog.SweepUp
section

/-!
# Mixed engine, R3 program part 15: the sweep of a class of height `h+1` over a word (agent e-r3prog)

`Eng.sweepUp`: by induction on the word, every letter in order: a free letter is one pass, a block
letter is ONE child call (`block_step`).  The charge is exactly the list of child calls `kidsUp`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset GF MXR
noncomputable section

universe U

namespace Eng
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]
variable (E : Eng α ρ σ)
variable {ι : Type U} {m : Bool} {cl : Paint} {b : Bank (portM cl) ι}
variable {n h μ o BS : ι → ℕ} {sup : ∀ i, ℕ → Bits (n i) → ℂ} {τ : ι → MDesc → ℕ}

/-- **The sweep of a class of height `h+1`.** -/
theorem sweepUp (ws : GWord α ρ) :
    ∀ {s : Ty} {x : ι → T s} {V : ∀ i, E.CState (n i) (h i + 1) (μ i)} {A : ι → List ℕ},
    CIn m b.B s x n (fun i => h i + 1) μ →
    CCtx m b.B s x E.X.n n (fun i => E.NUc (n i) (h i + 1) (μ i)) (fun i p => E.cUc (n i) (h i + 1) (μ i) p)
      (fun i p => E.iUc (n i) (h i + 1) (μ i) p) →
    Knows m b.B s x (fun i => E.W^(h i + 1)) →
    Has m b.B s (a w) x (fun i => (Layout.std (E.W^(h i + 1))).tape (fun t => E.PCc (n i) (h i + 1) (μ i) t)) →
    Has m b.B s (a w) x (fun i => (Layout.std (E.NUc (n i) (h i + 1) (μ i))).tape
      (fun p => E.Uc (n i) (h i + 1) (μ i) p)) →
    Has m b.B s (jobsT cl) x (fun i => jobsTape (n i) (BS i) (sup i)) → Small b.B BS →
    Has m b.B s (a (a (a (c cl)))) x (fun i => E.ctabE (n i) (h i + 1) (μ i) (V i)) →
    Has m b.B s (jobsT cl) x (fun i => accT (n i) (o i) (sup i) (A i)) →
    Has m b.B s (a w) x (fun i => szT (A i)) →
    Knows m b.B s x (fun i => o i + (A i).length) →
    ws.Proper E.X.n → (∀ mv ∈ ws, ∀ r, mv.rk? = some r → ∀ l, r < E.tr l) →
    (∀ i, o i + (A i).length + (E.accW (n i) (h i) (μ i) ws).length ≤ BS i) →
    (∀ i c, c ∈ E.kidsUp (n i) (h i) (μ i) (BS i) (sup i) (V i) (o i + (A i).length) ws →
      (b.use i (E.enc cl c)).OK (E.out cl c) (τ i c) (b.ext i)) →
    Able m b s (StT cl) x
      (fun i => (E.ctabE (n i) (h i + 1) (μ i) (E.runV (V i) ws),
        accT (n i) (o i) (sup i) (A i ++ E.accW (n i) (h i) (μ i) ws),
        szT (A i ++ E.accW (n i) (h i) (μ i) ws), o i + (A i ++ E.accW (n i) (h i) (μ i) ws).length))
      (fun i => E.swCost (n i) (h i) (μ i) (A i).length ws)
      (fun i => ((E.kidsUp (n i) (h i) (μ i) (BS i) (sup i) (V i) (o i + (A i).length) ws).map (τ i)).sum) := by
  induction ws with
  | nil =>
    intro s x V A cin cc hWp hPCp hUp tsup hBSs ct tacc tsz horun hP hsep hfit hk
    have H := ct.fork (tacc.fork (tsz.fork horun))
    have H2 := Able.of_can (b:=b) (H.mono (W':=fun _ => 0) (fun _ => by simp))
    refine Able.mono (H2.cong (fun _ => rfl) (fun i => ?_)) (fun i => Nat.zero_le _) (fun i => Nat.zero_le _)
    simp [runV_nil, accW, blockRanks]
  | cons mv ws ih =>
    intro s x V A cin cc hWp hPCp hUp tsup hBSs ct tacc tsz horun hP hsep hfit hk
    -- the continuation after one letter: the facts in the extended environment
    have cont : ∀ (V' : ∀ i, E.CState (n i) (h i + 1) (μ i)) (A' : ι → List ℕ) (W1 Z1 : ι → ℕ),
        Able m b s (StT cl) x (fun i => (E.ctabE (n i) (h i + 1) (μ i) (V' i), accT (n i) (o i) (sup i) (A' i),
          szT (A' i), o i + (A' i).length)) W1 Z1 →
        (∀ i, o i + (A' i).length + (E.accW (n i) (h i) (μ i) ws).length ≤ BS i) →
        (∀ i c, c ∈ E.kidsUp (n i) (h i) (μ i) (BS i) (sup i) (V' i) (o i + (A' i).length) ws →
          (b.use i (E.enc cl c)).OK (E.out cl c) (τ i c) (b.ext i)) →
        Able m b s (StT cl) x
          (fun i => (E.ctabE (n i) (h i + 1) (μ i) (E.runV (V' i) ws),
            accT (n i) (o i) (sup i) (A' i ++ E.accW (n i) (h i) (μ i) ws),
            szT (A' i ++ E.accW (n i) (h i) (μ i) ws), o i + (A' i ++ E.accW (n i) (h i) (μ i) ws).length))
          (fun i => W1 i + E.swCost (n i) (h i) (μ i) (A' i).length ws)
          (fun i => Z1 i + ((E.kidsUp (n i) (h i) (μ i) (BS i) (sup i) (V' i) (o i + (A' i).length) ws).map (τ i)).sum) := by
      intro V' A' W1 Z1 H1 hfit' hk'
      let st (i : ι) : T (StT cl) := (E.ctabE (n i) (h i + 1) (μ i) (V' i), accT (n i) (o i) (sup i) (A' i),
          szT (A' i), o i + (A' i).length)
      have F : ∀ {u : Ty} {z : ι → T u}, Has m b.B s u x z → Has m b.B (p s (StT cl)) u (fun i => (x i, st i)) z :=
        fun g => Can.first.then_do g
      have hst : Has m b.B (p s (StT cl)) (StT cl) (fun i => (x i, st i)) st := Can.second
      have H2 := ih (s:=p s (StT cl)) (x:=fun i => (x i, st i)) (V:=V') (A:=A') (cin.ext st) (cc.ext st) (F hWp) (F hPCp) (F hUp)
        (F tsup) hBSs (Can.fst hst) (Can.fst (Can.snd hst)) (Can.fst (Can.snd (Can.snd hst)))
        (Can.snd (Can.snd (Can.snd hst))) hP.tail (fun mv' hm => hsep mv' (List.mem_cons_of_mem _ hm)) hfit' hk'
      exact H1.save H2
    -- a free letter
    have free : mv.rk? = none →
        (∀ i, E.kidsUp (n i) (h i) (μ i) (BS i) (sup i) (V i) (o i + (A i).length) (mv :: ws) =
          E.kidsUp (n i) (h i) (μ i) (BS i) (sup i) (E.stepV (V i) mv) (o i + (A i).length) ws) →
        Able m b s (StT cl) x
          (fun i => (E.ctabE (n i) (h i + 1) (μ i) (E.runV (V i) (mv :: ws)),
            accT (n i) (o i) (sup i) (A i ++ E.accW (n i) (h i) (μ i) (mv :: ws)),
            szT (A i ++ E.accW (n i) (h i) (μ i) (mv :: ws)), o i + (A i ++ E.accW (n i) (h i) (μ i) (mv :: ws)).length))
          (fun i => E.swCost (n i) (h i) (μ i) (A i).length (mv :: ws))
          (fun i => ((E.kidsUp (n i) (h i) (μ i) (BS i) (sup i) (V i) (o i + (A i).length) (mv :: ws)).map (τ i)).sum) := by
      intro hfree hkids
      have hacc : ∀ i, E.accW (n i) (h i) (μ i) (mv :: ws) = E.accW (n i) (h i) (μ i) ws := fun i => by
        rw [accW_cons, hfree]; rfl
      have H1 : Able m b s (StT cl) x (fun i => (E.ctabE (n i) (h i + 1) (μ i) (E.stepV (V i) mv),
          accT (n i) (o i) (sup i) (A i), szT (A i), o i + (A i).length))
          (fun i => E.NUc (n i) (h i + 1) (μ i) * 2^(n i)) (fun _ => 0) :=
        Able.of_can (b:=b) (((cc.free_letter ct rfl mv hfree).fork (tacc.fork (tsz.fork horun))).mono
          (fun i => by simp))
      have H := cont (fun i => E.stepV (V i) mv) A _ _ H1 (fun i => by rw [← hacc i]; exact hfit i)
        (fun i c hc => hk i c (by rw [hkids i]; exact hc))
      refine (H.cong (fun _ => rfl) (fun i => ?_)).mono (fun i => le_of_eq ?_) (fun i => le_of_eq ?_)
      · rw [runV_cons, hacc i]
      · simp only [swCost, hfree, Nat.add_zero]
      · rw [hkids i, Nat.zero_add]
    cases mv with
    | old mv =>
      cases mv with
      | localM g => exact free rfl (fun i => rfl)
      | shift l z => exact free rfl (fun i => rfl)
      | block l r z ind =>
        have hpr : 1 ≤ r ∧ r < E.X.n := hP.head
        have hr : r ≤ E.X.n := hpr.2.le
        have hsep' : ∀ l', r < E.tr l' := hsep _ List.mem_cons_self r rfl
        have hacc : ∀ i, E.accW (n i) (h i) (μ i) (.old (.block l r z ind) :: ws) =
            E.accR (n i) (h i) (μ i) r ++ E.accW (n i) (h i) (μ i) ws := fun i => by
          rw [accW_cons]; rfl
        have hlen : ∀ i, o i + (A i).length + (E.ownSrc (n i) (h i) (μ i) r).length + E.cons (n i) (h i) (μ i * r) =
            o i + (A i ++ E.accR (n i) (h i) (μ i) r).length := fun i => by
          simp [accR, cons]; omega
        have hkids : ∀ i, E.kidsUp (n i) (h i) (μ i) (BS i) (sup i) (V i) (o i + (A i).length)
            (.old (.block l r z ind) :: ws) =
            E.childC (n i) (h i) (μ i) (BS i) (sup i) (V i) (o i + (A i).length) l r z ind hr ::
              E.kidsUp (n i) (h i) (μ i) (BS i) (sup i) (E.stepV (V i) (.old (.block l r z ind)))
                (o i + (A i ++ E.accR (n i) (h i) (μ i) r).length) ws := fun i => by
          simp only [kidsUp, dif_pos hr, List.singleton_append]
          rw [hlen i]
        have hfit1 : ∀ i, o i + (A i).length + (E.accR (n i) (h i) (μ i) r).length ≤ BS i := fun i => by
          have := hfit i; rw [hacc i, List.length_append] at this; omega
        have H1 := E.block_step cin cc hWp hPCp hUp tsup hBSs ct tacc tsz horun l r z ind hr hsep' hfit1
          (τ:=fun i => τ i (E.childC (n i) (h i) (μ i) (BS i) (sup i) (V i) (o i + (A i).length) l r z ind hr))
          (fun i => hk i _ (by rw [hkids i]; exact List.mem_cons_self))
        have H := cont (fun i => E.stepV (V i) (.old (.block l r z ind))) (fun i => A i ++ E.accR (n i) (h i) (μ i) r)
          _ _ H1 (fun i => by have := hfit i; rw [hacc i] at this; simp only [List.length_append] at *; omega)
          (fun i c hc => hk i c (by rw [hkids i]; exact List.mem_cons_of_mem _ hc))
        refine (H.cong (fun _ => rfl) (fun i => ?_)).mono (fun i => le_of_eq ?_) (fun i => le_of_eq ?_)
        · rw [runV_cons, hacc i, List.append_assoc]
        · simp only [swCost, GMove.rk?, GMove.shadow, BMove.rk?, List.length_append]
        · rw [hkids i, List.map_cons, List.sum_cons]
    | perm l G => exact free rfl (fun i => rfl)
    | phase l z c' => exact free rfl (fun i => rfl)

end Eng

end
end PowerSaving.RAM
end OAI

end
-- bos_merge: end Submission.Work.Mixed.Prog.SweepUp

-- bos_merge: begin Submission.Work.Mixed.Prog.SweepLeaf
section

/-!
# Mixed engine, R3 program part 16: the sweep of a leaf class (agent e-r3prog)

`Eng.sweepLeaf`: every letter of the word on a leaf class; a block letter is ONE fresh top call
(`exit_letter`).  The charge is exactly the list of exits `kidsLeaf`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset GF MXR
noncomputable section

universe U

namespace Eng
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]
variable (E : Eng α ρ σ)
variable {ι : Type U} {m : Bool} {cl : Paint} {b : Bank (portM cl) ι}
variable {n μ : ι → ℕ} {τ : ι → MDesc → ℕ}

lemma cU_leaf (n μ p : ℕ) : E.cUc n 0 μ p = μ := by
  simp [cUc, MXR.cU]

/-- Sweep cost of a word on a leaf class. -/
def lfCost (n μ : ℕ) : GWord α ρ → ℕ
  | [] => 0
  | mv :: ws => (match mv.rk? with
      | some _ => E.NUc n 0 μ * 2^n + 2 * n + 2
      | none => E.NUc n 0 μ * 2^n) + lfCost n μ ws

/-- **The sweep of a leaf class.** -/
theorem sweepLeaf (ws : GWord α ρ) :
    ∀ {s : Ty} {x : ι → T s} {V : ∀ i, E.CState (n i) 0 (μ i)},
    CIn m b.B s x n (fun _ => 0) μ →
    CCtx m b.B s x E.X.n n (fun i => E.NUc (n i) 0 (μ i)) (fun i p => E.cUc (n i) 0 (μ i) p)
      (fun i p => E.iUc (n i) 0 (μ i) p) →
    Has m b.B s (a (a (a (c cl)))) x (fun i => E.ctabE (n i) 0 (μ i) (V i)) →
    ws.Proper E.X.n → (∀ i, E.X.n * μ i ≤ n i) →
    (∀ i c, c ∈ E.kidsLeaf (n i) (μ i) (V i) ws → (b.use i (E.enc cl c)).OK (E.out cl c) (τ i c) (b.ext i)) →
    Able m b s (a (a (a (c cl)))) x (fun i => E.ctabE (n i) 0 (μ i) (E.runV (V i) ws))
      (fun i => E.lfCost (n i) (μ i) ws) (fun i => ((E.kidsLeaf (n i) (μ i) (V i) ws).map (τ i)).sum) := by
  induction ws with
  | nil =>
    intro s x V cin cc ct hP hfit hk
    refine Able.mono ((Able.of_can (b:=b) (ct.mono (W':=fun _ => 0) (fun _ => le_rfl))).cong (fun _ => rfl)
      (fun i => by rw [runV_nil])) (fun i => Nat.zero_le _) (fun i => Nat.zero_le _)
  | cons mv ws ih =>
    intro s x V cin cc ct hP hfit hk
    have cont : ∀ (V' : ∀ i, E.CState (n i) 0 (μ i)) (W1 Z1 : ι → ℕ),
        Able m b s (a (a (a (c cl)))) x (fun i => E.ctabE (n i) 0 (μ i) (V' i)) W1 Z1 →
        (∀ i c, c ∈ E.kidsLeaf (n i) (μ i) (V' i) ws → (b.use i (E.enc cl c)).OK (E.out cl c) (τ i c) (b.ext i)) →
        Able m b s (a (a (a (c cl)))) x (fun i => E.ctabE (n i) 0 (μ i) (E.runV (V' i) ws))
          (fun i => W1 i + E.lfCost (n i) (μ i) ws)
          (fun i => Z1 i + ((E.kidsLeaf (n i) (μ i) (V' i) ws).map (τ i)).sum) := by
      intro V' W1 Z1 H1 hk'
      let st (i : ι) : T (a (a (a (c cl)))) := E.ctabE (n i) 0 (μ i) (V' i)
      have H2 := ih (s:=p s (a (a (a (c cl))))) (x:=fun i => (x i, st i)) (V:=V') (cin.ext (t:=a (a (a (c cl)))) st)
        (cc.ext (t:=a (a (a (c cl)))) st)
        Can.second hP.tail hfit hk'
      exact H1.save H2
    have free : mv.rk? = none →
        (∀ i, E.kidsLeaf (n i) (μ i) (V i) (mv :: ws) = E.kidsLeaf (n i) (μ i) (E.stepV (V i) mv) ws) →
        Able m b s (a (a (a (c cl)))) x (fun i => E.ctabE (n i) 0 (μ i) (E.runV (V i) (mv :: ws)))
          (fun i => E.lfCost (n i) (μ i) (mv :: ws)) (fun i => ((E.kidsLeaf (n i) (μ i) (V i) (mv :: ws)).map (τ i)).sum) := by
      intro hfree hkids
      have H1 : Able m b s (a (a (a (c cl)))) x (fun i => E.ctabE (n i) 0 (μ i) (E.stepV (V i) mv))
          (fun i => E.NUc (n i) 0 (μ i) * 2^(n i)) (fun _ => 0) :=
        Able.of_can (b:=b) (cc.free_letter ct rfl mv hfree)
      have H := cont (fun i => E.stepV (V i) mv) _ _ H1 (fun i c hc => hk i c (by rw [hkids i]; exact hc))
      refine (H.cong (fun _ => rfl) (fun i => ?_)).mono (fun i => le_of_eq ?_) (fun i => le_of_eq ?_)
      · rw [runV_cons]
      · simp only [lfCost, hfree]
      · rw [hkids i, Nat.zero_add]
    cases mv with
    | old mv =>
      cases mv with
      | localM g => exact free rfl (fun i => rfl)
      | shift l z => exact free rfl (fun i => rfl)
      | block l r z ind =>
        have hpr : 1 ≤ r ∧ r < E.X.n := hP.head
        have hr : r ≤ E.X.n := hpr.2.le
        have hkn : ∀ i, r * μ i ≤ n i := fun i => le_trans (Nat.mul_le_mul_right _ hr) (hfit i)
        have hkids : ∀ i, E.kidsLeaf (n i) (μ i) (V i) (.old (.block l r z ind) :: ws) =
            E.exitC (n i) (μ i) (V i) l r z ind hr :: E.kidsLeaf (n i) (μ i) (E.stepV (V i) (.old (.block l r z ind))) ws :=
          fun i => by simp only [kidsLeaf, dif_pos hr, List.singleton_append]
        -- the powers for the exit
        have hke : Knows m b.B s x (fun i => r * μ i) := (Can.wc r).times cin.μK (Small.const _ _) cin.μS
        have hkes : Small b.B (fun i => r * μ i) := (Small.const _ r).mul cin.μS
        have hp1 : Can m b.B s w x (fun i => 2^(r * μ i)) (fun i => n i + 1) :=
          (hke.mono (fun _ => Nat.zero_le _)).wTwo hkes (cin.big.mono (fun i => Nat.pow_le_pow_right (by omega) (hkn i)))
            (Dom.of_le (fun i => by have := hkn i; omega))
        have hnk : Knows m b.B s x (fun i => n i - r * μ i) := cin.nK.minus hke cin.nS
        have hp2 : Can m b.B s w x (fun i => 2^(n i - r * μ i)) (fun i => n i + 1) :=
          (hnk.mono (fun _ => Nat.zero_le _)).wTwo (cin.nS.sub) (cin.big.mono (fun i => Nat.pow_le_pow_right (by omega)
            (Nat.sub_le _ _))) (Dom.of_le (fun i => by omega))
        let PW (i : ι) : T (p w (p w w)) := (2^(r * μ i), 2^(n i - r * μ i), r * μ i)
        have HPW : Can m b.B s (p w (p w w)) x PW (fun i => n i + 1 + (n i + 1 + 0)) := hp1.fork (hp2.fork hke)
        let x1 (i : ι) : T (p s (p w (p w w))) := (x i, PW i)
        have cc1 := cc.ext PW
        have ct1 : Has m b.B (p s (p w (p w w))) (a (a (a (c cl)))) x1 (fun i => E.ctabE (n i) 0 (μ i) (V i)) :=
          Can.first.then_do ct
        let S := bS z ind
        let X' := bX (α:=α) r
        have hX' : X'.n + r = E.X.n := E.bX_n hr
        have hk1 : ∀ i, (b.use i (mkIn cl (r * μ i) 0 0 0
            (jobsTape (r * μ i) (E.NUc (n i) 0 (μ i) * 2^(n i - r * μ i))
              (toVec (n i) (r * μ i) (hkn i) (exJobs E.X S X' hX' l (cc1.fit i) (V i))))
            (jobsTape (r * μ i) 0 (fun _ _ => 0)))).OK
          (jobsTape (r * μ i) (E.NUc (n i) 0 (μ i) * 2^(n i - r * μ i))
            (fun t => ripple (r * μ i) (toVec (n i) (r * μ i) (hkn i) (exJobs E.X S X' hX' l (cc1.fit i) (V i)) t)),
            jobsTape (r * μ i) 0 (fun _ _ => 0), (Layout.std 0).tape (fun _ => (0 : ℕ)))
          (τ i (E.exitC (n i) (μ i) (V i) l r z ind hr)) (b.ext i) := by
          intro i
          have := hk i (E.exitC (n i) (μ i) (V i) l r z ind hr) (by rw [hkids i]; exact List.mem_cons_self)
          have e : E.exitC (n i) (μ i) (V i) l r z ind hr = MDesc.top (r * μ i) (E.NUc (n i) 0 (μ i) * 2^(n i - r * μ i))
              (toVec (n i) (r * μ i) (hkn i) (exJobs E.X S X' hX' l (cc1.fit i) (V i))) := by
            unfold exitC; rw [dif_pos (hkn i)]
          rw [e] at this ⊢
          exact this
        have HE := cc1.exit_letter ct1 S X' hX' l μ (fun i p => E.cU_leaf _ _ _) hkn
          (Can.fst Can.second) (Can.fst (Can.snd Can.second)) (Can.snd (Can.snd Can.second)) hk1
        have H1 : Able m b s (a (a (a (c cl)))) x
            (fun i => E.ctabE (n i) 0 (μ i) (E.stepV (V i) (.old (.block l r z ind))))
            (fun i => n i + 1 + (n i + 1 + 0) + E.NUc (n i) 0 (μ i) * 2^(n i))
            (fun i => 0 + τ i (E.exitC (n i) (μ i) (V i) l r z ind hr)) := by
          have := (Able.of_can (b:=b) HPW).save (Able.fst HE)
          refine this.cong (fun _ => rfl) (fun i => ?_)
          rw [E.stepV_block]
        have H := cont (fun i => E.stepV (V i) (.old (.block l r z ind))) _ _ H1
          (fun i c hc => hk i c (by rw [hkids i]; exact List.mem_cons_of_mem _ hc))
        refine (H.cong (fun _ => rfl) (fun i => ?_)).mono (fun i => le_of_eq ?_) (fun i => le_of_eq ?_)
        · rw [runV_cons]
        · show _ = (E.NUc (n i) 0 (μ i) * 2^(n i) + 2 * n i + 2) + E.lfCost (n i) (μ i) ws
          ring
        · rw [hkids i, List.map_cons, List.sum_cons, Nat.zero_add]
    | perm l G => exact free rfl (fun i => rfl)
    | phase l z c' => exact free rfl (fun i => rfl)

end Eng

end
end PowerSaving.RAM
end OAI

end
-- bos_merge: end Submission.Work.Mixed.Prog.SweepLeaf

-- bos_merge: begin Submission.Work.Mixed.Prog.ClassBody
section

/-!
# Mixed engine, R3 program part 17: the body of a class call (agent e-r3prog)

From the port input `(n, I, h+1, μ, o, own jobs, supply)`: `2^n`, the class tables, load, the sweep of
the whole word (child calls or exits), unload, answer `(own answers, consumed answers, sizes)`.

* `Eng.class_up`    a class of height `h+1` (children);
* `Eng.class_leaf`  a class of height `0` (exits).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset GF MXR
noncomputable section

universe U

namespace Eng
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]
variable (E : Eng α ρ σ)
variable {ι : Type U} {m : Bool} {cl : Paint} {b : Bank (portM cl) ι}
variable {n h μ o BS : ι → ℕ} {J sup : ∀ i, ℕ → Bits (n i) → ℂ} {τ : ι → MDesc → ℕ}

/-- The empty tapes are all equal. -/
lemma jobsTape_zero (n : ℕ) (f g : ℕ → Bits n → ℂ) : jobsTape n 0 f = jobsTape n 0 g := by
  unfold jobsTape; exact tape_std_ext rfl _ _ (fun k h1 _ => absurd h1 (Nat.not_lt_zero _))

/-- The own answers after the word are `hlow` of the own jobs. -/
lemma own_answers (n h μ : ℕ) (J : ℕ → Bits n → ℂ) :
    jobsTape n (E.NUc n h μ * E.W) (E.unl n h μ (E.runV (E.V0 n h μ J) E.wd)) =
      jobsTape n (E.NUc n h μ * E.W) (fun t => hlow n (E.slotSize n h μ t) (J t)) := by
  unfold jobsTape
  apply tape_std_ext rfl
  intro k h1 _
  show (bits n).tape (E.unl n h μ (E.runV (E.V0 n h μ J) E.wd) k) = (bits n).tape (hlow n (E.slotSize n h μ k) (J k))
  rw [E.unl_run n h μ J k h1]

/-- The decoded port input of a class. -/
lemma decode {x : ι → T (portIn cl)}
    (hx : ∀ i, x i = mkIn cl (n i) (h i + 1) (μ i) (o i) (jobsTape (n i) (E.NUc (n i) (h i) (μ i) * E.W) (J i))
      (jobsTape (n i) (BS i) (sup i))) :
    Knows m b.B (portIn cl) x n ∧ Has m b.B (portIn cl) sc x (fun _ => Complex.I) ∧
    Knows m b.B (portIn cl) x (fun i => h i + 1) ∧ Knows m b.B (portIn cl) x μ ∧ Knows m b.B (portIn cl) x o ∧
    Has m b.B (portIn cl) (jobsT cl) x (fun i => jobsTape (n i) (E.NUc (n i) (h i) (μ i) * E.W) (J i)) ∧
    Has m b.B (portIn cl) (jobsT cl) x (fun i => jobsTape (n i) (BS i) (sup i)) := by
  refine ⟨Can.first.cong (fun _ => rfl) (fun i => by rw [hx i]; rfl),
    (Can.fst Can.second).cong (fun _ => rfl) (fun i => by rw [hx i]; rfl),
    (Can.fst (Can.snd Can.second)).cong (fun _ => rfl) (fun i => by rw [hx i]; rfl),
    (Can.fst (Can.snd (Can.snd Can.second))).cong (fun _ => rfl) (fun i => by rw [hx i]; rfl),
    (Can.fst (Can.snd (Can.snd (Can.snd Can.second)))).cong (fun _ => rfl) (fun i => by rw [hx i]; rfl),
    (Can.fst (Can.snd (Can.snd (Can.snd (Can.snd Can.second))))).cong (fun _ => rfl) (fun i => by rw [hx i]; rfl),
    (Can.snd (Can.snd (Can.snd (Can.snd (Can.snd Can.second))))).cong (fun _ => rfl) (fun i => by rw [hx i]; rfl)⟩

/-- Local work of a class of height `h+1`. -/
def locUp (n h μ : ℕ) : ℕ :=
  (n + 1) + E.idxCost n (h+1) μ + E.NUc n (h+1) μ * (4 * n + 4 * (h + 1) + 8) +
    E.NUc n (h+1) μ * (2 * 2^n + 2) + E.NUc n (h+1) μ * 2^n + E.swCost n h μ 0 E.wd +
    E.NUc n (h+1) μ * E.W * 2^n

lemma szT_nil : szT [] = (Layout.std 0).tape (fun _ : Fin 0 => (0 : ℕ)) := by
  unfold szT; exact tape_std_ext rfl _ _ (fun k h1 _ => absurd h1 (Nat.not_lt_zero _))

/-- **The body of a class of height `h+1`.** -/
theorem class_up (hB2 : Small b.B (fun i => 2^(n i))) (hBS : Small b.B BS)
    (hle : ∀ i, h i + 1 ≤ n i) (hμ : Small b.B μ)
    (hfit : ∀ i, o i + E.cons (n i) (h i + 1) (μ i) ≤ BS i)
    (hk : ∀ i c, c ∈ E.kidsC (MDesc.cls (n i) (h i + 1) (μ i) (o i) (BS i) (J i) (sup i)) →
      (b.use i (E.enc cl c)).OK (E.out cl c) (τ i c) (b.ext i)) :
    Able m b (portIn cl) (portOut cl)
      (fun i => E.enc cl (MDesc.cls (n i) (h i + 1) (μ i) (o i) (BS i) (J i) (sup i)))
      (fun i => E.out cl (MDesc.cls (n i) (h i + 1) (μ i) (o i) (BS i) (J i) (sup i)))
      (fun i => E.locUp (n i) (h i) (μ i))
      (fun i => ((E.kidsC (MDesc.cls (n i) (h i + 1) (μ i) (o i) (BS i) (J i) (sup i))).map (τ i)).sum) := by
  let x0 (i : ι) := E.enc cl (MDesc.cls (n i) (h i + 1) (μ i) (o i) (BS i) (J i) (sup i))
  obtain ⟨hn, hI, hkd, hμK, hoK, hown, hsup⟩ := E.decode (b:=b) (x:=x0) (n:=n) (h:=fun i => h i + 1) (μ:=μ)
    (o:=o) (BS:=BS) (J:=J) (sup:=sup) (fun i => rfl)
  -- 2^n
  have hnS : Small b.B n := hB2.mono (fun i => Nat.lt_two_pow_self.le)
  have H2n : Can m b.B (portIn cl) w x0 (fun i => 2^(n i)) (fun i => n i + 1) :=
    (hn.mono (fun _ => Nat.zero_le _)).wTwo hnS hB2 (Dom.of_le (fun i => by omega))
  let x1 (i : ι) : T (p (portIn cl) w) := (x0 i, 2^(n i))
  have c1 : CIn m b.B (p (portIn cl) w) x1 n (fun i => h i + 1) μ :=
    ⟨Can.first.then_do hn, Can.first.then_do ((hkd.wsub (Can.wc 1) (hnS.mono (fun i => by have := hle i; omega))).cong
      (fun _ => rfl) (fun i => by simp)), Can.first.then_do hμK, Can.second, Can.first.then_do hI, hB2,
      hle, hμ⟩
  have Hidx := E.can_index c1
  have Hun := E.can_units c1
  have Hge := E.can_gears c1
  have cc := E.cctx c1
  let idx (i : ι) := E.idxVal (n i) (h i + 1) (μ i)
  let un (i : ι) := E.unitVal (n i) (h i + 1) (μ i)
  let ge (i : ι) := E.gearVal (n i) (h i + 1) (μ i)
  let s4 : Ty := ClsT (p (portIn cl) w)
  let x4 (i : ι) : T s4 := (((x1 i, idx i), un i), ge i)
  have F4 : ∀ {u : Ty} {z : ι → T u}, Has m b.B (portIn cl) u x0 z → Has m b.B s4 u x4 z :=
    fun g => Can.first.then_do (Can.first.then_do (Can.first.then_do (Can.first.then_do g)))
  have hidx4 : Has m b.B s4 IdxT x4 idx := Can.first.then_do (Can.first.then_do Can.second)
  have c4 : CIn m b.B s4 x4 n (fun i => h i + 1) μ :=
    ((c1.ext (t:=IdxT) idx).ext (t:=UnT) un).ext (t:=GearT) ge
  -- load
  have Hld := E.load cc (J:=J) (F4 hown)
  let ct0 (i : ι) : T (a (a (a (c cl)))) := E.ctabE (n i) (h i + 1) (μ i) (E.V0 (n i) (h i + 1) (μ i) (J i))
  let s5 : Ty := p s4 (a (a (a (c cl))))
  let x5 (i : ι) : T s5 := (x4 i, ct0 i)
  have F5 : ∀ {u : Ty} {z : ι → T u}, Has m b.B s4 u x4 z → Has m b.B s5 u x5 z := fun g => Can.first.then_do g
  -- the sweep
  have tacc : Has m b.B s5 (jobsT cl) x5 (fun i => accT (n i) (o i) (sup i) ([] : List ℕ)) :=
    (has_noJobs (cl:=cl) n).cong (fun _ => rfl) (fun i => jobsTape_zero _ _ _)
  have tsz : Has m b.B s5 (a w) x5 (fun i => szT ([] : List ℕ)) := by
    have := can_tabIx (t:=w) (N:=fun _ => 0) (x:=x5) (B:=b.B) (m:=m) (fun i (t : Fin 0) => (0 : ℕ)) (Can.wc 0)
      (Small.const _ 0) (can_of_empty (fun u => Nat.not_lt_zero _ u.2.2))
    exact this.cong (fun _ => rfl) (fun i => szT_nil.symm)
  have horun : Knows m b.B s5 x5 (fun i => o i + ([] : List ℕ).length) := F5 (F4 hoK)
  have Hsw := E.sweepUp (b:=b) (n:=n) (h:=h) (μ:=μ) (o:=o) (BS:=BS) (sup:=sup) (τ:=τ) E.wd
    (s:=s5) (x:=x5) (V:=fun i => E.V0 (n i) (h i + 1) (μ i) (J i)) (A:=fun _ => [])
    (c4.ext (t:=a (a (a (c cl)))) ct0) (cc.ext (t:=a (a (a (c cl)))) ct0)
    (F5 (Can.fst hidx4)) (F5 (Can.fst (Can.snd (Can.snd hidx4)))) (F5 (Can.snd (Can.snd (Can.snd hidx4))))
    (F5 (F4 hsup)) hBS Can.second tacc tsz horun E.hP E.sep
    (fun i => by
      have h1 := hfit i
      have e : (E.accW (n i) (h i) (μ i) E.wd).length = E.cons (n i) (h i + 1) (μ i) := rfl
      simp only [List.length_nil, Nat.add_zero]; omega)
    (fun i c hc => hk i c hc)
  -- unload and answer
  let stF (i : ι) : T (StT cl) := (E.ctabE (n i) (h i + 1) (μ i) (E.runV (E.V0 (n i) (h i + 1) (μ i) (J i)) E.wd),
      accT (n i) (o i) (sup i) ([] ++ E.accW (n i) (h i) (μ i) E.wd),
      szT ([] ++ E.accW (n i) (h i) (μ i) E.wd), o i + ([] ++ E.accW (n i) (h i) (μ i) E.wd).length)
  let s6 : Ty := p s5 (StT cl)
  let x6 (i : ι) : T s6 := (x5 i, stF i)
  have cc6 := (cc.ext (t:=a (a (a (c cl)))) ct0).ext (t:=StT cl) stF
  have hst : Has m b.B s6 (StT cl) x6 stF := Can.second
  have HU := E.unload cc6 (V:=fun i => E.runV (E.V0 (n i) (h i + 1) (μ i) (J i)) E.wd) (Can.fst hst)
  have Hout : Can m b.B s6 (portOut cl) x6
      (fun i => E.out cl (MDesc.cls (n i) (h i + 1) (μ i) (o i) (BS i) (J i) (sup i)))
      (fun i => E.NUc (n i) (h i + 1) (μ i) * E.W * 2^(n i)) := by
    refine ((HU.fork ((Can.fst (Can.snd hst)).fork (Can.fst (Can.snd (Can.snd hst))))).cong (fun _ => rfl)
      (fun i => ?_)).mono (fun i => by simp)
    show (_, _, _) = (_, _, _)
    rw [E.own_answers]
    rfl
  have H := (Able.of_can (b:=b) H2n).save ((Able.of_can (b:=b) Hidx).save ((Able.of_can (b:=b) Hun).save
    ((Able.of_can (b:=b) Hge).save ((Able.of_can (b:=b) Hld).save (Hsw.save (Able.of_can (b:=b) Hout))))))
  refine H.mono (fun i => le_of_eq ?_) (fun i => le_of_eq ?_)
  · simp only [locUp, List.length_nil]; ring
  · simp only [Nat.zero_add, Nat.add_zero, List.length_nil]
    rfl

/-- Local work of a leaf class. -/
def locLeaf (n μ : ℕ) : ℕ :=
  (n + 1) + E.idxCost n 0 μ + E.NUc n 0 μ * (4 * n + 4 * 0 + 8) +
    E.NUc n 0 μ * (2 * 2^n + 2) + E.NUc n 0 μ * 2^n + E.lfCost n μ E.wd + E.NUc n 0 μ * E.W * 2^n

/-- **The body of a leaf class.** -/
theorem class_leaf (hB2 : Small b.B (fun i => 2^(n i))) (hμ : Small b.B μ) (hfit : ∀ i, E.X.n * μ i ≤ n i)
    (hk : ∀ i c, c ∈ E.kidsC (MDesc.cls (n i) 0 (μ i) (o i) (BS i) (J i) (sup i)) →
      (b.use i (E.enc cl c)).OK (E.out cl c) (τ i c) (b.ext i)) :
    Able m b (portIn cl) (portOut cl)
      (fun i => E.enc cl (MDesc.cls (n i) 0 (μ i) (o i) (BS i) (J i) (sup i)))
      (fun i => E.out cl (MDesc.cls (n i) 0 (μ i) (o i) (BS i) (J i) (sup i)))
      (fun i => E.locLeaf (n i) (μ i))
      (fun i => ((E.kidsC (MDesc.cls (n i) 0 (μ i) (o i) (BS i) (J i) (sup i))).map (τ i)).sum) := by
  let x0 (i : ι) := E.enc cl (MDesc.cls (n i) 0 (μ i) (o i) (BS i) (J i) (sup i))
  obtain ⟨hn, hI, hkd, hμK, hoK, hown, hsup⟩ := E.decode (b:=b) (x:=x0) (n:=n) (h:=fun _ => 0) (μ:=μ)
    (o:=o) (BS:=BS) (J:=J) (sup:=sup) (fun i => rfl)
  have hnS : Small b.B n := hB2.mono (fun i => Nat.lt_two_pow_self.le)
  have H2n : Can m b.B (portIn cl) w x0 (fun i => 2^(n i)) (fun i => n i + 1) :=
    (hn.mono (fun _ => Nat.zero_le _)).wTwo hnS hB2 (Dom.of_le (fun i => by omega))
  let x1 (i : ι) : T (p (portIn cl) w) := (x0 i, 2^(n i))
  have c1 : CIn m b.B (p (portIn cl) w) x1 n (fun _ => 0) μ :=
    ⟨Can.first.then_do hn, Can.wc 0, Can.first.then_do hμK, Can.second, Can.first.then_do hI, hB2,
      fun i => Nat.zero_le _, hμ⟩
  have Hidx := E.can_index c1
  have Hun := E.can_units c1
  have Hge := E.can_gears c1
  have cc := E.cctx c1
  let idx (i : ι) := E.idxVal (n i) 0 (μ i)
  let un (i : ι) := E.unitVal (n i) 0 (μ i)
  let ge (i : ι) := E.gearVal (n i) 0 (μ i)
  let s4 : Ty := ClsT (p (portIn cl) w)
  let x4 (i : ι) : T s4 := (((x1 i, idx i), un i), ge i)
  have F4 : ∀ {u : Ty} {z : ι → T u}, Has m b.B (portIn cl) u x0 z → Has m b.B s4 u x4 z :=
    fun g => Can.first.then_do (Can.first.then_do (Can.first.then_do (Can.first.then_do g)))
  have c4 : CIn m b.B s4 x4 n (fun _ => 0) μ :=
    ((c1.ext (t:=IdxT) idx).ext (t:=UnT) un).ext (t:=GearT) ge
  have Hld := E.load cc (J:=J) (F4 hown)
  let ct0 (i : ι) : T (a (a (a (c cl)))) := E.ctabE (n i) 0 (μ i) (E.V0 (n i) 0 (μ i) (J i))
  let s5 : Ty := p s4 (a (a (a (c cl))))
  let x5 (i : ι) : T s5 := (x4 i, ct0 i)
  have Hsw := E.sweepLeaf (b:=b) (n:=n) (μ:=μ) (τ:=τ) E.wd (s:=s5) (x:=x5)
    (V:=fun i => E.V0 (n i) 0 (μ i) (J i)) (c4.ext (t:=a (a (a (c cl)))) ct0) (cc.ext (t:=a (a (a (c cl)))) ct0)
    Can.second E.hP hfit (fun i c hc => hk i c hc)
  let ctF (i : ι) : T (a (a (a (c cl)))) := E.ctabE (n i) 0 (μ i) (E.runV (E.V0 (n i) 0 (μ i) (J i)) E.wd)
  let s6 : Ty := p s5 (a (a (a (c cl))))
  let x6 (i : ι) : T s6 := (x5 i, ctF i)
  have cc6 := (cc.ext (t:=a (a (a (c cl)))) ct0).ext (t:=a (a (a (c cl)))) ctF
  have HU := E.unload cc6 (V:=fun i => E.runV (E.V0 (n i) 0 (μ i) (J i)) E.wd) Can.second
  have hz : Has m b.B s6 (jobsT cl) x6 (fun i => jobsTape (n i) 0 (fun _ _ => 0)) := has_noJobs n
  have hz2 : Has m b.B s6 (a w) x6 (fun i => (Layout.std 0).tape (fun _ : Fin 0 => (0 : ℕ))) :=
    can_tabIx (t:=w) (N:=fun _ => 0) (x:=x6) (B:=b.B) (m:=m) (fun i (t : Fin 0) => (0 : ℕ)) (Can.wc 0)
      (Small.const _ 0) (can_of_empty (fun u => Nat.not_lt_zero _ u.2.2))
  have Hout : Can m b.B s6 (portOut cl) x6
      (fun i => E.out cl (MDesc.cls (n i) 0 (μ i) (o i) (BS i) (J i) (sup i)))
      (fun i => E.NUc (n i) 0 (μ i) * E.W * 2^(n i)) := by
    refine ((HU.fork (hz.fork hz2)).cong (fun _ => rfl) (fun i => ?_)).mono (fun i => by simp)
    show (_, _, _) = (_, _, _)
    rw [E.own_answers]
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · dsimp only
      unfold jobsTape
      exact tape_std_ext (show 0 = E.cons (n i) 0 (μ i) from rfl) _ _ (fun k h1 _ => absurd h1 (Nat.not_lt_zero _))
    · dsimp only
      exact tape_std_ext (show 0 = E.cons (n i) 0 (μ i) from rfl) _ _ (fun k h1 _ => absurd h1 (Nat.not_lt_zero _))
  have H := (Able.of_can (b:=b) H2n).save ((Able.of_can (b:=b) Hidx).save ((Able.of_can (b:=b) Hun).save
    ((Able.of_can (b:=b) Hge).save ((Able.of_can (b:=b) Hld).save (Hsw.save (Able.of_can (b:=b) Hout))))))
  refine H.mono (fun i => le_of_eq ?_) (fun i => le_of_eq ?_)
  · simp only [locLeaf]; ring
  · simp only [Nat.zero_add, Nat.add_zero]
    rfl

/-- Local work of a class. -/
def clsLoc (n h μ : ℕ) : ℕ := if h = 0 then E.locLeaf n μ else E.locUp n (h - 1) μ

/-- **The body of a class call** (any height): a leaf class makes exits, a higher class makes child calls. -/
theorem class_body (hB2 : Small b.B (fun i => 2^(n i))) (hBS : Small b.B BS)
    (hv1 : ∀ i, h i = 0 → E.X.n * μ i ≤ n i) (hv2 : ∀ i, h i ≤ n i) (hv3 : ∀ i, μ i ≤ n i)
    (hv4 : ∀ i, o i + E.cons (n i) (h i) (μ i) ≤ BS i)
    (hk : ∀ i c, c ∈ E.kidsC (MDesc.cls (n i) (h i) (μ i) (o i) (BS i) (J i) (sup i)) →
      (b.use i (E.enc cl c)).OK (E.out cl c) (τ i c) (b.ext i)) :
    Able m b (portIn cl) (portOut cl)
      (fun i => E.enc cl (MDesc.cls (n i) (h i) (μ i) (o i) (BS i) (J i) (sup i)))
      (fun i => E.out cl (MDesc.cls (n i) (h i) (μ i) (o i) (BS i) (J i) (sup i)))
      (fun i => E.clsLoc (n i) (h i) (μ i))
      (fun i => ((E.kidsC (MDesc.cls (n i) (h i) (μ i) (o i) (BS i) (J i) (sup i))).map (τ i)).sum) := by
  let x0 (i : ι) := E.enc cl (MDesc.cls (n i) (h i) (μ i) (o i) (BS i) (J i) (sup i))
  have hkd : Knows m b.B (portIn cl) x0 (fun i => h i + 1) := Can.fst (Can.snd Can.second)
  have hnS : Small b.B n := hB2.mono (fun i => Nat.lt_two_pow_self.le)
  have hh : Knows m b.B (portIn cl) x0 h :=
    (hkd.wsub (Can.wc 1) (hnS.mono (fun i => by have := hv2 i; omega))).cong (fun _ => rfl) (fun i => by simp)
  have hμs : Small b.B μ := hnS.mono hv3
  apply Able.branch (hh.mono (W':=fun i => E.clsLoc (n i) (h i) (μ i)) (fun _ => Nat.zero_le _))
    (fun i => h i = 0) (fun i => Iff.rfl)
  · -- leaf classes
    let K := {i // h i = 0}
    have H := E.class_leaf (m:=m) (b:=b.comap (fun i : K => i.1)) (n:=fun i : K => n i.1) (μ:=fun i : K => μ i.1)
      (o:=fun i : K => o i.1) (BS:=fun i : K => BS i.1) (J:=fun i : K => J i.1) (sup:=fun i : K => sup i.1)
      (τ:=fun i : K => τ i.1) (hB2.reindex _) (hμs.reindex _) (fun i => hv1 i.1 i.2)
      (fun i c hc => hk i.1 c (by rw [i.2]; exact hc))
    refine (H.cong (fun i => ?_) (fun i => ?_)).mono (fun i => le_of_eq ?_) (fun i => le_of_eq ?_)
    · show E.enc cl (MDesc.cls (n i.1) 0 _ _ _ _ _) = E.enc cl (MDesc.cls (n i.1) (h i.1) _ _ _ _ _)
      rw [i.2]
    · show E.out cl (MDesc.cls (n i.1) 0 _ _ _ _ _) = E.out cl (MDesc.cls (n i.1) (h i.1) _ _ _ _ _)
      rw [i.2]
    · show E.locLeaf (n i.1) (μ i.1) = E.clsLoc (n i.1) (h i.1) (μ i.1)
      unfold clsLoc; rw [if_pos i.2]
    · show _ = ((E.kidsC (MDesc.cls (n i.1) (h i.1) (μ i.1) (o i.1) (BS i.1) (J i.1) (sup i.1))).map (τ i.1)).sum
      rw [i.2]
  · -- classes of height h'+1
    let K := {i // ¬ h i = 0}
    have hsucc : ∀ i : K, h i.1 - 1 + 1 = h i.1 := fun i => by have := i.2; omega
    have H := E.class_up (m:=m) (b:=b.comap (fun i : K => i.1)) (n:=fun i : K => n i.1) (h:=fun i : K => h i.1 - 1)
      (μ:=fun i : K => μ i.1) (o:=fun i : K => o i.1) (BS:=fun i : K => BS i.1) (J:=fun i : K => J i.1)
      (sup:=fun i : K => sup i.1) (τ:=fun i : K => τ i.1) (hB2.reindex _) (hBS.reindex _)
      (fun i => by rw [hsucc i]; exact hv2 i.1) (hμs.reindex _)
      (fun i => by rw [hsucc i]; exact hv4 i.1)
      (fun i c hc => hk i.1 c (by rw [← hsucc i]; exact hc))
    refine (H.cong (fun i => ?_) (fun i => ?_)).mono (fun i => le_of_eq ?_) (fun i => le_of_eq ?_)
    · show E.enc cl (MDesc.cls (n i.1) (h i.1 - 1 + 1) _ _ _ _ _) = E.enc cl (MDesc.cls (n i.1) (h i.1) _ _ _ _ _)
      rw [hsucc i]
    · show E.out cl (MDesc.cls (n i.1) (h i.1 - 1 + 1) _ _ _ _ _) = E.out cl (MDesc.cls (n i.1) (h i.1) _ _ _ _ _)
      rw [hsucc i]
    · show E.locUp (n i.1) (h i.1 - 1) (μ i.1) = E.clsLoc (n i.1) (h i.1) (μ i.1)
      unfold clsLoc; rw [if_neg i.2]
    · show _ = ((E.kidsC (MDesc.cls (n i.1) (h i.1) (μ i.1) (o i.1) (BS i.1) (J i.1) (sup i.1))).map (τ i.1)).sum
      rw [hsucc i]

end Eng

end
end PowerSaving.RAM
end OAI

end
-- bos_merge: end Submission.Work.Mixed.Prog.ClassBody

-- bos_merge: begin Submission.Work.Mixed.Prog.Valid
section

/-!
# Mixed engine, R3 program part 18: valid descriptors (agent e-r3prog)

The handler answers VALID descriptors: every top job, and every class of the lockstep tree
(`1 ≤ μ`, `mx * μ * kmin^h ≤ n`: rl-prove's region invariant; its subtree's consumption fits in the supply).

* `Eng.Valid`        the predicate;
* `Eng.kidsC_valid`  the calls of a valid class are valid;
* `Eng.class_body_valid`  the class body for any family of valid class descriptors.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset GF MXR
noncomputable section

universe U

namespace Eng
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]
variable (E : Eng α ρ σ)

/-- Valid descriptors. -/
def Valid (kmin : ℕ) : MDesc → Prop
  | .top _ _ _ => True
  | .cls n h μ o BS _ _ => 1 ≤ μ ∧ E.mx * μ * kmin ^ h ≤ n ∧ o + E.cons n h μ ≤ BS

/-- The smallest target rank (used by `Valid`). -/
structure KMin (kmin : ℕ) : Prop where
  two : 2 ≤ kmin
  att : ∃ l, E.tr l = kmin

lemma rk_lt_kmin {kmin : ℕ} (hk : E.KMin kmin) {mv : GMove α ρ} (hmv : mv ∈ E.wd) {r : ℕ}
    (hr : mv.rk? = some r) : r < kmin := by
  obtain ⟨l, hl⟩ := hk.att
  rw [← hl]; exact E.sep mv hmv r hr l

lemma accW_cons_len (n h μ : ℕ) (mv : GMove α ρ) (ws : GWord α ρ) :
    (E.accW n h μ ws).length ≤ (E.accW n h μ (mv :: ws)).length := by
  rw [accW_cons]; simp

/-- The children of a class along a word are valid. -/
lemma kidsUp_valid {kmin : ℕ} (hk : E.KMin kmin) (n h μ BS : ℕ) (sup : ℕ → Bits n → ℂ) (hμ : 1 ≤ μ)
    (hreg : E.mx * μ * kmin ^ (h+1) ≤ n) :
    ∀ (ws : GWord α ρ), (∀ mv ∈ ws, mv ∈ E.wd) → ∀ (V : E.CState n (h+1) μ) (o' : ℕ),
      o' + (E.accW n h μ ws).length ≤ BS → ∀ c ∈ E.kidsUp n h μ BS sup V o' ws, E.Valid kmin c := by
  intro ws
  induction ws with
  | nil => intro _ V o' _ c hc; simp [kidsUp] at hc
  | cons mv ws ih =>
    intro hsub V o' hfit c hc
    have hsub' : ∀ mv' ∈ ws, mv' ∈ E.wd := fun mv' hm => hsub mv' (List.mem_cons_of_mem _ hm)
    cases mv with
    | old mv =>
      cases mv with
      | localM g => exact ih hsub' _ o' (le_trans (by have := E.accW_cons_len n h μ (.old (.localM g)) ws; omega) hfit) c hc
      | shift l z => exact ih hsub' _ o' (le_trans (by have := E.accW_cons_len n h μ (.old (.shift l z)) ws; omega) hfit) c hc
      | block l r z ind =>
        have hrk : r < kmin := E.rk_lt_kmin hk (hsub _ List.mem_cons_self) rfl
        have hacc : E.accW n h μ (.old (.block l r z ind) :: ws) = E.accR n h μ r ++ E.accW n h μ ws := by
          rw [accW_cons]; rfl
        rw [hacc, List.length_append] at hfit
        simp only [kidsUp] at hc
        rcases List.mem_append.1 hc with hc | hc
        · split_ifs at hc with hr
          · rw [List.mem_singleton] at hc
            subst hc
            refine ⟨?_, ?_, ?_⟩
            · have h1 : (GMove.old (.block l r z ind) : GMove α ρ).Proper E.X.n := E.hP _ (hsub _ List.mem_cons_self)
              obtain ⟨h1, _⟩ := h1
              exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
            · calc E.mx * (μ * r) * kmin ^ h ≤ E.mx * μ * kmin * kmin ^ h := by
                    have := Nat.mul_le_mul_left (E.mx * μ) hrk.le
                    calc E.mx * (μ * r) * kmin ^ h = E.mx * μ * r * kmin ^ h := by ring
                      _ ≤ E.mx * μ * kmin * kmin ^ h := Nat.mul_le_mul_right _ this
                _ = E.mx * μ * kmin ^ (h + 1) := by ring
                _ ≤ n := hreg
            · have : (E.accR n h μ r).length = (E.ownSrc n h μ r).length + E.cons n h (μ * r) := by
                simp [accR, cons]
              omega
          · simp at hc
        · exact ih hsub' _ _ (by simp only [accR, cons, List.length_append] at hfit ⊢; omega) c hc
    | perm l G => exact ih hsub' _ o' (le_trans (by have := E.accW_cons_len n h μ (.perm l G) ws; omega) hfit) c hc
    | phase l z c' => exact ih hsub' _ o' (le_trans (by have := E.accW_cons_len n h μ (.phase l z c') ws; omega) hfit) c hc

/-- The exits of a leaf class are valid (top jobs). -/
lemma kidsLeaf_valid {kmin : ℕ} (n μ : ℕ) : ∀ (ws : GWord α ρ) (V : E.CState n 0 μ),
    ∀ c ∈ E.kidsLeaf n μ V ws, E.Valid kmin c := by
  intro ws
  induction ws with
  | nil => intro V c hc; simp [kidsLeaf] at hc
  | cons mv ws ih =>
    intro V c hc
    cases mv with
    | old mv =>
      cases mv with
      | localM g => exact ih _ c hc
      | shift l z => exact ih _ c hc
      | block l r z ind =>
        simp only [kidsLeaf] at hc
        rcases List.mem_append.1 hc with hc | hc
        · split_ifs at hc with hr
          · rw [List.mem_singleton] at hc; subst hc
            unfold exitC; split_ifs <;> trivial
          · simp at hc
        · exact ih _ c hc
    | perm l G => exact ih _ c hc
    | phase l z c' => exact ih _ c hc

/-- **The calls of a valid class are valid.** -/
theorem kidsC_valid {kmin : ℕ} (hk : E.KMin kmin) (d : MDesc) (hd : E.Valid kmin d) :
    ∀ c ∈ E.kidsC d, E.Valid kmin c := by
  cases d with
  | top n B v => intro c hc; simp [kidsC] at hc
  | cls n h μ o BS J sup =>
    obtain ⟨hμ, hreg, hfit⟩ := hd
    cases h with
    | zero => exact E.kidsLeaf_valid n μ _ _
    | succ h =>
      exact E.kidsUp_valid hk n h μ BS sup hμ hreg E.wd (fun _ hm => hm) _ o (by
        have e : (E.accW n h μ E.wd).length = E.cons n (h+1) μ := rfl
        omega)

lemma valid_facts {kmin : ℕ} (hk : E.KMin kmin) {n h μ o BS : ℕ} {J sup : ℕ → Bits n → ℂ}
    (hd : E.Valid kmin (MDesc.cls n h μ o BS J sup)) :
    (h = 0 → E.X.n * μ ≤ n) ∧ h ≤ n ∧ μ ≤ n ∧ o + E.cons n h μ ≤ BS := by
  obtain ⟨hμ, hreg, hfit⟩ := hd
  have hk1 : 1 ≤ kmin ^ h := Nat.one_le_pow _ _ (by have := hk.two; omega)
  have hm : 1 ≤ E.mx := le_trans (by norm_num) E.three
  refine ⟨fun h0 => by subst h0; simpa using hreg, ?_, ?_, hfit⟩
  · have h1 : h < 2 ^ h := Nat.lt_two_pow_self
    have h2 : 2 ^ h ≤ kmin ^ h := Nat.pow_le_pow_left hk.two _
    have h3 : kmin ^ h ≤ E.mx * μ * kmin ^ h := Nat.le_mul_of_pos_left _ (Nat.mul_pos hm hμ)
    omega
  · have : μ ≤ E.mx * μ * kmin ^ h := by
      calc μ ≤ E.mx * μ := Nat.le_mul_of_pos_left _ hm
        _ ≤ E.mx * μ * kmin ^ h := Nat.le_mul_of_pos_right _ hk1
    omega

/-- **The class body for valid descriptors.** -/
theorem class_body_valid {kmin : ℕ} (hk : E.KMin kmin) {ι : Type U} {m : Bool} {cl : Paint}
    {b : Bank (portM cl) ι} {n h μ o BS : ι → ℕ} {J sup : ∀ i, ℕ → Bits (n i) → ℂ} {τ : ι → MDesc → ℕ}
    (hB2 : Small b.B (fun i => 2^(n i))) (hBS : Small b.B BS)
    (hd : ∀ i, E.Valid kmin (MDesc.cls (n i) (h i) (μ i) (o i) (BS i) (J i) (sup i)))
    (hkc : ∀ i c, c ∈ E.kidsC (MDesc.cls (n i) (h i) (μ i) (o i) (BS i) (J i) (sup i)) →
      (b.use i (E.enc cl c)).OK (E.out cl c) (τ i c) (b.ext i)) :
    Able m b (portIn cl) (portOut cl)
      (fun i => E.enc cl (MDesc.cls (n i) (h i) (μ i) (o i) (BS i) (J i) (sup i)))
      (fun i => E.out cl (MDesc.cls (n i) (h i) (μ i) (o i) (BS i) (J i) (sup i)))
      (fun i => E.clsLoc (n i) (h i) (μ i))
      (fun i => ((E.kidsC (MDesc.cls (n i) (h i) (μ i) (o i) (BS i) (J i) (sup i))).map (τ i)).sum) :=
  E.class_body hB2 hBS (fun i => (E.valid_facts hk (hd i)).1) (fun i => (E.valid_facts hk (hd i)).2.1)
    (fun i => (E.valid_facts hk (hd i)).2.2.1) (fun i => (E.valid_facts hk (hd i)).2.2.2) hkc

end Eng

end
end PowerSaving.RAM
end OAI

end
-- bos_merge: end Submission.Work.Mixed.Prog.Valid
