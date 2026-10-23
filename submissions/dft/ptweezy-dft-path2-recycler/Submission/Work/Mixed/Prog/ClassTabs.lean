import Submission.Work.Mixed.Prog.Loops

/-!
# Mixed engine, R3 program part 8: the tables of a class (agent e-r3prog)

From `(n, h, μ)` a class computes, by brute force over the `W^h` codes (polynomial bookkeeping):

* index part `(W^h, NU, PC table, U table)` (`Eng.can_index`);
* unit part `(cU, 2^cU, iU, 2^iU)` per unit (`Eng.can_units`);
* gear part (XOR table and `lum` table of each unit's column) (`Eng.can_gears`);

and from them the class context `CCtx` of `CTab.lean` (`Eng.cctx`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset GF MXR
noncomputable section

universe U

/-- What a class knows of itself at constant cost. -/
structure CIn {ι : Type U} (m : Bool) (B : ι → ℕ) (s : Ty) (x : ι → T s) (n h μ : ι → ℕ) : Prop where
  nK : Knows m B s x n
  hK : Knows m B s x h
  μK : Knows m B s x μ
  p2n : Knows m B s x (fun i => 2^(n i))
  imag : Has m B s sc x (fun _ => Complex.I)
  big : Small B (fun i => 2^(n i))
  hle : ∀ i, h i ≤ n i
  μS : Small B μ

namespace CIn
variable {ι : Type U} {m : Bool} {B : ι → ℕ} {s : Ty} {x : ι → T s} {n h μ : ι → ℕ}
variable (c : CIn m B s x n h μ)
include c

lemma nS : Small B n := c.big.mono (fun i => Nat.lt_two_pow_self.le)
lemma hS : Small B h := c.nS.mono c.hle

/-- `b^h` is polynomial in `2^n`. -/
lemma powS (b : ℕ) : Small B (fun i => b^(h i)) := by
  obtain ⟨d, hd⟩ := c.big
  refine ⟨d * b, fun i => ?_⟩
  calc b^(h i) ≤ (2^b)^(h i) := Nat.pow_le_pow_left (Nat.lt_two_pow_self).le _
    _ ≤ (2^b)^(n i) := Nat.pow_le_pow_right (Nat.two_pow_pos b) (c.hle i)
    _ = (2^(n i))^b := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ ≤ ((B i + 2)^d)^b := Nat.pow_le_pow_left (hd i) _
    _ = (B i + 2)^(d * b) := by rw [← pow_mul]

/-- The facts survive extending the environment. -/
lemma ext {t : Ty} (y : ι → T t) : CIn m B (p s t) (fun i => (x i, y i)) n h μ :=
  ⟨Can.first.then_do c.nK, Can.first.then_do c.hK, Can.first.then_do c.μK, Can.first.then_do c.p2n,
    Can.first.then_do c.imag, c.big, c.hle, c.μS⟩

/-- Reindexing. -/
lemma reindex {κ : Type U} (j : κ → ι) {t : Ty} (y : κ → T t)
    (g : Has m (fun k => B (j k)) t s y (fun k => x (j k))) :
    CIn m (fun k => B (j k)) t y (fun k => n (j k)) (fun k => h (j k)) (fun k => μ (j k)) :=
  ⟨g.then_do (c.nK.reindex j), g.then_do (c.hK.reindex j), g.then_do (c.μK.reindex j),
    g.then_do (c.p2n.reindex j), g.then_do (c.imag.reindex j), c.big.reindex j,
    fun k => c.hle (j k), c.μS.reindex j⟩

end CIn

namespace Eng
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]
variable (E : Eng α ρ σ)
variable {ι : Type U} {m : Bool} {B : ι → ℕ} {s : Ty} {x : ι → T s} {n h μ : ι → ℕ}

/-- The region test of a code (`1` in the region). -/
lemma knows_inR (c : CIn m B s x n h μ) {j : ι → ℕ} (hj : Knows m B s x j) (hjs : Small B j)
    (hWh : Knows m B s x (fun i => E.W^(h i))) :
    Can m B s w x (fun i => if inRS E.W E.tq E.mx (n i) (h i) (μ i) (j i) then 1 else 0)
      (fun i => h i + 1) := by
  have hcol := E.can_colS c.hK c.hS hj hjs (c.powS E.mx)
  have hcs : Small B (fun i => colS E.W E.tq (h i) (j i)) :=
    (c.powS E.mx).mono (fun i => (E.stepC_iter_le (h i) (j i)).1)
  have hv : Can m B s w x (fun i => E.mx * (μ i * colS E.W E.tq (h i) (j i))) (fun i => h i + 1) :=
    (Can.wc E.mx).times (c.μK.mono (fun _ => Nat.zero_le _) |>.times hcol c.μS hcs)
      (Small.const _ E.mx) (c.μS.mul hcs)
  have ha : Can m B s w x (fun i => if j i < E.W^(h i) then 1 else 0) (fun i => h i + 1) :=
    (hj.mono (fun _ => Nat.zero_le _)).wlt (hWh.mono (fun _ => Nat.zero_le _))
  have hb : Can m B s w x (fun i => 1 - (if n i < E.mx * (μ i * colS E.W E.tq (h i) (j i)) then 1 else 0))
      (fun i => h i + 1) :=
    (Can.wc 1).wsub ((c.nK.mono (fun _ => Nat.zero_le _)).wlt hv) ((Small.const _ 1).mono (fun _ => Nat.sub_le _ _))
  refine (ha.times hb ((Small.const _ 1).mono (fun i => by split <;> omega))
    ((Small.const _ 1).mono (fun _ => Nat.sub_le _ _))).cong (fun _ => rfl) (fun i => ?_)
  unfold inRS
  by_cases h1 : j i < E.W^(h i) <;> by_cases h2 : E.mx * (μ i * colS E.W E.tq (h i) (j i)) ≤ n i
  · simp [h1, h2, Nat.not_lt.mpr h2]
  · simp [h1, h2, Nat.lt_of_not_le h2]
  · simp [h1]
  · simp [h1]

/-- Index part of the class tables. -/
abbrev IdxT : Ty := p w (p w (p (a w) (a w)))
def idxVal (n h μ : ℕ) : T IdxT :=
  (E.W^h, E.NUc n h μ, (Layout.std (E.W^h)).tape (fun t => E.PCc n h μ t),
    (Layout.std (E.NUc n h μ)).tape (fun p => E.Uc n h μ p))

/-- Cost bound of the index part. -/
def idxCost (n h μ : ℕ) : ℕ := (E.W^h + 1) * (E.W^h + 1) * (h + 2)

lemma NU_le' (n h μ : ℕ) : E.NUc n h μ ≤ E.W^h := MXR.NU_le n h μ

/-- **The index part** (brute force over the codes). -/
lemma can_index (c : CIn m B s x n h μ) :
    Can m B s IdxT x (fun i => E.idxVal (n i) (h i) (μ i)) (fun i => E.idxCost (n i) (h i) (μ i)) := by
  have hWh := can_powv E.W E.W_pos c.hK c.hS (c.powS E.W)
  have hWs := c.powS E.W
  let NUf (i : ι) := E.NUc (n i) (h i) (μ i)
  have hNUs : Small B NUf := hWs.mono (fun i => E.NU_le' _ _ _)
  -- environment x1 = (x, W^h)
  let x1 (i : ι) : T (p s w) := (x i, E.W^(h i))
  have c1 := c.ext (t:=w) (fun i => E.W^(h i))
  have hWh1 : Knows m B (p s w) x1 (fun i => E.W^(h i)) := Can.second
  -- the region test inside any loop over codes below `W^h`
  have test : ∀ {κ : Type U} (jx : κ → ι) (y : κ → T (p (p s w) w)) (jj : κ → ℕ),
      Has m (fun k => B (jx k)) (p (p s w) w) (p s w) y (fun k => x1 (jx k)) →
      Knows m (fun k => B (jx k)) (p (p s w) w) y jj → (∀ k, jj k ≤ E.W^(h (jx k))) →
      Can m (fun k => B (jx k)) (p (p s w) w) w y
        (fun k => if inRS E.W E.tq E.mx (n (jx k)) (h (jx k)) (μ (jx k)) (jj k) then 1 else 0)
        (fun k => h (jx k) + 1) := by
    intro κ jx y jj hy hj hjl
    have cd := c1.reindex jx y hy
    exact E.knows_inR cd hj ((hWs.reindex jx).mono hjl) (hy.then_do (hWh1.reindex jx))
  -- NU
  have hNU : Can m B (p s w) w x1 NUf (fun i => E.W^(h i) * (h i + 1 + 1) + 1) :=
    can_count (P:=fun i => inRS E.W E.tq E.mx (n i) (h i) (μ i)) (Wt:=fun i => h i + 1) hWh1 hWs
      (test (fun d : During (fun i => E.W^(h i)) => d.i) (fun d => (x1 d.i, d.j)) (fun d => d.j)
        Can.first Can.second (fun d => d.hj.le))
  -- environment x2 = (x1, NU)
  let x2 (i : ι) : T (p (p s w) w) := (x1 i, NUf i)
  have hNU2 : Knows m B (p (p s w) w) x2 NUf := Can.second
  have hW2 : Knows m B (p (p s w) w) x2 (fun i => E.W^(h i)) := Can.first.then_do hWh1
  -- PC table
  let UW := UnitF (fun i => E.W^(h i))
  have hcnt : Can m (fun u : UW => B u.1) (p (p (p s w) w) w) w (fun u => (x2 u.1, u.2.val))
      (fun u => E.PCc (n u.1) (h u.1) (μ u.1) u.2.val) (fun u => u.2.val * (h u.1 + 1 + 1) + 1) := by
    let DD := During (fun u : UW => u.2.val)
    have t0 := test (fun d : DD => d.i.1) (fun d => (x1 d.i.1, d.j)) (fun d => d.j)
        Can.first Can.second (fun d => le_trans d.hj.le d.i.2.2.le)
    have ty : Has m (fun d : DD => B d.i.1) (p (p (p (p s w) w) w) w) (p (p s w) w)
        (fun d => ((x2 d.i.1, d.i.2.val), d.j)) (fun d => (x1 d.i.1, d.j)) :=
      (Can.first.then_do (Can.first.then_do Can.first)).pair Can.second
    have t1 : Can m (fun d : DD => B d.i.1) (p (p (p (p s w) w) w) w) w
        (fun d => ((x2 d.i.1, d.i.2.val), d.j))
        (fun d => if inRS E.W E.tq E.mx (n d.i.1) (h d.i.1) (μ d.i.1) d.j then 1 else 0)
        (fun d => h d.i.1 + 1) := (ty.pipe t0).mono (fun d => by simp)
    exact can_count (P:=fun u : UW => inRS E.W E.tq E.mx (n u.1) (h u.1) (μ u.1)) (Wt:=fun u => h u.1 + 1)
      Can.second ((hWs.reindex (fun u : UW => u.1)).mono (fun u => u.2.2.le)) t1
  have HPC := Can.layout (t:=w) (L:=fun i => Layout.std (E.W^(h i)))
    (v:=fun i t => E.PCc (n i) (h i) (μ i) t) (P:=fun i => E.W^(h i) * (h i + 2) + 1)
    (W:=fun _ => 0) hW2 (hcnt.mono (fun u => by
      have := u.2.2
      change u.2.val * (h u.1 + 1 + 1) + 1 ≤ E.W^(h u.1) * (h u.1 + 2) + 1
      nlinarith)) hWs
  -- U table
  let UN := UnitF NUf
  have hsr : Can m (fun u : UN => B u.1) (p (p (p s w) w) w) w (fun u => (x2 u.1, u.2.val))
      (fun u => if u.2.val < Nat.count (inRS E.W E.tq E.mx (n u.1) (h u.1) (μ u.1)) (E.W^(h u.1))
        then Nat.nth (inRS E.W E.tq E.mx (n u.1) (h u.1) (μ u.1)) u.2.val else 0)
      (fun u => E.W^(h u.1) * (h u.1 + 1 + 1) + 1) := by
    let DD := During (fun u : UN => E.W^(h u.1))
    have t0 := test (fun d : DD => d.i.1) (fun d => (x1 d.i.1, d.j)) (fun d => d.j)
        Can.first Can.second (fun d => d.hj.le)
    have ty : Has m (fun d : DD => B d.i.1) (p (p (p (p s w) w) w) w) (p (p s w) w)
        (fun d => ((x2 d.i.1, d.i.2.val), d.j)) (fun d => (x1 d.i.1, d.j)) :=
      (Can.first.then_do (Can.first.then_do Can.first)).pair Can.second
    have t1 : Can m (fun d : DD => B d.i.1) (p (p (p (p s w) w) w) w) w
        (fun d => ((x2 d.i.1, d.i.2.val), d.j))
        (fun d => if inRS E.W E.tq E.mx (n d.i.1) (h d.i.1) (μ d.i.1) d.j then 1 else 0)
        (fun d => h d.i.1 + 1) := (ty.pipe t0).mono (fun d => by simp)
    exact can_nthc (P:=fun u : UN => inRS E.W E.tq E.mx (n u.1) (h u.1) (μ u.1)) (Wt:=fun u => h u.1 + 1)
      (Can.first.then_do (hW2.reindex (fun u : UN => u.1))) (hWs.reindex (fun u : UN => u.1)) Can.second t1
  have hsr' : Can m (fun u : UN => B u.1) (p (p (p s w) w) w) w (fun u => (x2 u.1, u.2.val))
      (fun u => E.Uc (n u.1) (h u.1) (μ u.1) u.2.val) (fun u => E.W^(h u.1) * (h u.1 + 2) + 1) := by
    refine (hsr.mono (fun u => le_of_eq (by ring))).cong (fun _ => rfl) (fun u => ?_)
    have : u.2.val < Nat.count (inRS E.W E.tq E.mx (n u.1) (h u.1) (μ u.1)) (E.W^(h u.1)) := u.2.2
    rw [if_pos this]; rfl
  have HU := Can.layout (t:=w) (L:=fun i => Layout.std (NUf i)) (v:=fun i p => E.Uc (n i) (h i) (μ i) p)
    (P:=fun i => E.W^(h i) * (h i + 2) + 1) (W:=fun _ => 0) hNU2 hsr' hNUs
  -- assemble
  have Hfin := hW2.fork (hNU2.fork (HPC.fork HU))
  have Hall := hWh.save (hNU.save Hfin)
  refine Hall.weaken ⟨8, fun i => ?_⟩
  have h1 : NUf i ≤ E.W^(h i) := E.NU_le' _ _ _
  have h0 : 1 ≤ E.W^(h i) := Nat.one_le_pow _ _ E.W_pos
  simp only [idxCost]
  change h i + 1 + (E.W^(h i) * (h i + 1 + 1) + 1 + (0 + (0 + ((0 + E.W^(h i) + E.W^(h i) * (E.W^(h i) * (h i + 2) + 1)) +
    (0 + NUf i + NUf i * (E.W^(h i) * (h i + 2) + 1)))))) + 1 ≤ 8 * ((E.W^(h i) + 1) * (E.W^(h i) + 1) * (h i + 2) + 1)
  have h2 : NUf i * (E.W^(h i) * (h i + 2) + 1) ≤ E.W^(h i) * (E.W^(h i) * (h i + 2) + 1) :=
    Nat.mul_le_mul_right _ h1
  have h3 : h i + 1 ≤ E.W^(h i) * (h i + 2) := by nlinarith
  nlinarith

/-- Unit part of the class tables. -/
abbrev UnT : Ty := p (a w) (p (a w) (p (a w) (a w)))
def unitVal (n h μ : ℕ) : T UnT :=
  ((Layout.std (E.NUc n h μ)).tape (fun p => E.cUc n h μ p),
   (Layout.std (E.NUc n h μ)).tape (fun p => 2^(E.cUc n h μ p)),
   (Layout.std (E.NUc n h μ)).tape (fun p => E.iUc n h μ p),
   (Layout.std (E.NUc n h μ)).tape (fun p => 2^(E.iUc n h μ p)))

lemma cU_le (n h μ : ℕ) (p : Fin (E.NUc n h μ)) : E.cUc n h μ p ≤ n := by
  have h1 := MXR.U_fits p.2 (W:=E.W) (tq:=E.tq) (mx:=E.mx)
  have h2 : E.cUc n h μ p ≤ E.mx * E.cUc n h μ p :=
    Nat.le_mul_of_pos_left _ (lt_of_lt_of_le (by norm_num) E.three)
  exact le_trans h2 h1

/-- **The unit part.** -/
lemma can_units (c : CIn m B s x n h μ) :
    Can m B (p s IdxT) UnT (fun i => (x i, E.idxVal (n i) (h i) (μ i))) (fun i => E.unitVal (n i) (h i) (μ i))
      (fun i => E.NUc (n i) (h i) (μ i) * (4 * n i + 4 * h i + 8)) := by
  let x1 (i : ι) : T (p s IdxT) := (x i, E.idxVal (n i) (h i) (μ i))
  let NUf (i : ι) := E.NUc (n i) (h i) (μ i)
  let UN := UnitF NUf
  let yU (u : UN) : T (p (p s IdxT) w) := (x1 u.1, u.2.val)
  have c1 := c.ext (t:=IdxT) (fun i => E.idxVal (n i) (h i) (μ i))
  have cu := c1.reindex (fun u : UN => u.1) (t:=p (p s IdxT) w) yU Can.first
  have hNU : Knows m B (p s IdxT) x1 NUf := Can.fst (Can.snd Can.second)
  have hNUs : Small B NUf := (c.powS E.W).mono (fun i => E.NU_le' _ _ _)
  have hUt : Has m B (p s IdxT) (a w) x1 (fun i => (Layout.std (NUf i)).tape (fun p => E.Uc (n i) (h i) (μ i) p)) :=
    Can.snd (Can.snd (Can.snd Can.second))
  have hUp : Knows m (fun u : UN => B u.1) (p (p s IdxT) w) yU (fun u => E.Uc (n u.1) (h u.1) (μ u.1) u.2) :=
    unit_fetch _ hUt
  have hUs : Small (fun u : UN => B u.1) (fun u => E.Uc (n u.1) (h u.1) (μ u.1) u.2) :=
    ((c.powS E.W).reindex (fun u : UN => u.1)).mono (fun u => (MXR.U_lt u.2.2).le)
  have hcol := E.can_colS cu.hK cu.hS hUp hUs (cu.powS E.mx)
  have hcs : Small (fun u : UN => B u.1) (fun u => colS E.W E.tq (h u.1) (E.Uc (n u.1) (h u.1) (μ u.1) u.2)) :=
    (cu.powS E.mx).mono (fun u => (E.stepC_iter_le _ _).1)
  have hcU : Can m (fun u : UN => B u.1) (p (p s IdxT) w) w yU (fun u => E.cUc (n u.1) (h u.1) (μ u.1) u.2)
      (fun u => h u.1 + 1) := (cu.μK.mono (fun _ => Nat.zero_le _)).times hcol cu.μS hcs
  have hcUle : ∀ u : UN, E.cUc (n u.1) (h u.1) (μ u.1) u.2 ≤ n u.1 := fun u => E.cU_le _ _ _ u.2
  have hcUs : Small (fun u : UN => B u.1) (fun u => E.cUc (n u.1) (h u.1) (μ u.1) u.2) := cu.nS.mono hcUle
  have hcUb : Small (fun u : UN => B u.1) (fun u => 2^(E.cUc (n u.1) (h u.1) (μ u.1) u.2)) :=
    cu.big.mono (fun u => Nat.pow_le_pow_right (by omega) (hcUle u))
  have hp2c := (hcU.mono (W':=fun u => n u.1 + h u.1 + 1) (fun u => by omega)).wTwo hcUs hcUb
    (Dom.of_le (fun u => by have := hcUle u; omega))
  have hiU : Can m (fun u : UN => B u.1) (p (p s IdxT) w) w yU (fun u => E.iUc (n u.1) (h u.1) (μ u.1) u.2)
      (fun u => h u.1 + 1) :=
    (cu.nK.mono (fun _ => Nat.zero_le _)).minus ((Can.wc E.mx).times hcU (Small.const _ _) hcUs) cu.nS
  have hiUle : ∀ u : UN, E.iUc (n u.1) (h u.1) (μ u.1) u.2 ≤ n u.1 := fun u => Nat.sub_le _ _
  have hp2i := (hiU.mono (W':=fun u => n u.1 + h u.1 + 1) (fun u => by omega)).wTwo (cu.nS.mono hiUle)
    (cu.big.mono (fun u => Nat.pow_le_pow_right (by omega) (hiUle u)))
    (Dom.of_le (fun u => by have := hiUle u; omega))
  have mk : ∀ (g : ∀ i, Fin (NUf i) → ℕ),
      Can m (fun u : UN => B u.1) (p (p s IdxT) w) w yU (fun u => g u.1 u.2) (fun u => n u.1 + h u.1 + 1) →
      Can m B (p s IdxT) (a w) x1 (fun i => (Layout.std (NUf i)).tape (g i)) (fun i => NUf i * (n i + h i + 2)) := by
    intro g hg
    have H := Can.layout (t:=w) (L:=fun i => Layout.std (NUf i)) (v:=g) (P:=fun i => n i + h i + 1)
      (W:=fun _ => 0) hNU hg hNUs
    refine H.mono (fun i => ?_)
    change 0 + NUf i + NUf i * (n i + h i + 1) ≤ NUf i * (n i + h i + 2)
    nlinarith
  have T1 := mk (fun i p => E.cUc (n i) (h i) (μ i) p) (hcU.mono (fun u => by omega))
  have T2 := mk (fun i p => 2^(E.cUc (n i) (h i) (μ i) p)) hp2c
  have T3 := mk (fun i p => E.iUc (n i) (h i) (μ i) p) (hiU.mono (fun u => by omega))
  have T4 := mk (fun i p => 2^(E.iUc (n i) (h i) (μ i) p)) hp2i
  refine (T1.fork (T2.fork (T3.fork T4))).mono (fun i => ?_)
  change NUf i * (n i + h i + 2) + (NUf i * (n i + h i + 2) + (NUf i * (n i + h i + 2) + NUf i * (n i + h i + 2)))
    ≤ NUf i * (4 * n i + 4 * h i + 8)
  nlinarith

/-- Gear part of the class tables (XOR and `lum` tables of every unit's column). -/
abbrev GearT : Ty := p (a (a w)) (a (a sc))
def gearVal (n h μ : ℕ) : T GearT :=
  ((Layout.std (E.NUc n h μ)).tape (fun p => xorTab (E.cUc n h μ p)),
   (Layout.std (E.NUc n h μ)).tape (fun p => (bits (E.cUc n h μ p)).tape (fun y : Bits (E.cUc n h μ p) => lum y)))

abbrev ClsT (s : Ty) : Ty := p (p (p s IdxT) UnT) GearT
def clsVal (n h μ : ℕ) : T IdxT × T UnT × T GearT := (E.idxVal n h μ, E.unitVal n h μ, E.gearVal n h μ)

lemma three_c_le (n h μ : ℕ) (p : Fin (E.NUc n h μ)) : 3 * E.cUc n h μ p ≤ n := by
  have h1 := MXR.U_fits p.2 (W:=E.W) (tq:=E.tq) (mx:=E.mx)
  have h2 : 3 * E.cUc n h μ p ≤ E.mx * E.cUc n h μ p := Nat.mul_le_mul_right _ E.three
  exact le_trans h2 h1

/-- **The gear part.** -/
lemma can_gears (c : CIn m B s x n h μ) :
    Can m B (p (p s IdxT) UnT) GearT
      (fun i => ((x i, E.idxVal (n i) (h i) (μ i)), E.unitVal (n i) (h i) (μ i)))
      (fun i => E.gearVal (n i) (h i) (μ i)) (fun i => E.NUc (n i) (h i) (μ i) * (2 * 2^(n i) + 2)) := by
  let x2 (i : ι) : T (p (p s IdxT) UnT) := ((x i, E.idxVal (n i) (h i) (μ i)), E.unitVal (n i) (h i) (μ i))
  let NUf (i : ι) := E.NUc (n i) (h i) (μ i)
  let UN := UnitF NUf
  let yU (u : UN) : T (p (p (p s IdxT) UnT) w) := (x2 u.1, u.2.val)
  have c2 := (c.ext (t:=IdxT) (fun i => E.idxVal (n i) (h i) (μ i))).ext (t:=UnT) (fun i => E.unitVal (n i) (h i) (μ i))
  have cu := c2.reindex (fun u : UN => u.1) (t:=p (p (p s IdxT) UnT) w) yU Can.first
  have hNU : Knows m B (p (p s IdxT) UnT) x2 NUf := Can.first.then_do (Can.fst (Can.snd Can.second))
  have hNUs : Small B NUf := (c.powS E.W).mono (fun i => E.NU_le' _ _ _)
  have hc : Knows m (fun u : UN => B u.1) (p (p (p s IdxT) UnT) w) yU (fun u => E.cUc (n u.1) (h u.1) (μ u.1) u.2) :=
    unit_fetch (m:=m) (B:=B) (s:=p (p s IdxT) UnT) (t:=w) (NU:=NUf) (x:=x2)
      (fun i (p : Fin (NUf i)) => E.cUc (n i) (h i) (μ i) p) (Can.fst Can.second)
  have hp : Knows m (fun u : UN => B u.1) (p (p (p s IdxT) UnT) w) yU
      (fun u => 2^(E.cUc (n u.1) (h u.1) (μ u.1) u.2)) :=
    unit_fetch (m:=m) (B:=B) (s:=p (p s IdxT) UnT) (t:=w) (NU:=NUf) (x:=x2)
      (fun i (p : Fin (NUf i)) => 2^(E.cUc (n i) (h i) (μ i) p)) (Can.fst (Can.snd Can.second))
  have hcle : ∀ u : UN, E.cUc (n u.1) (h u.1) (μ u.1) u.2 ≤ n u.1 := fun u => E.cU_le _ _ _ u.2
  have hcs : Small (fun u : UN => B u.1) (fun u => E.cUc (n u.1) (h u.1) (μ u.1) u.2) := cu.nS.mono hcle
  have hps : Small (fun u : UN => B u.1) (fun u => 2^(E.cUc (n u.1) (h u.1) (μ u.1) u.2)) :=
    cu.big.mono (fun u => Nat.pow_le_pow_right (by omega) (hcle u))
  have hcube : ∀ u : UN, (2^(E.cUc (n u.1) (h u.1) (μ u.1) u.2))^3 ≤ 2^(n u.1) := fun u => by
    rw [← pow_mul]; exact Nat.pow_le_pow_right (by omega) (by have := E.three_c_le _ _ _ u.2; omega)
  have hx := (Can.xor_prepare hc hp hcs hps).mono hcube
  have hl := ((WHT.lum_tables hc hcs hps cu.imag).1).mono
    (fun u => Nat.pow_le_pow_right (by omega) (hcle u))
  have H1 := Can.layout (t:=a w) (L:=fun i => Layout.std (NUf i)) (v:=fun i p => xorTab (E.cUc (n i) (h i) (μ i) p))
    (P:=fun i => 2^(n i)) (W:=fun _ => 0) hNU hx hNUs
  have H2 := Can.layout (t:=a sc) (L:=fun i => Layout.std (NUf i))
    (v:=fun i p => (bits (E.cUc (n i) (h i) (μ i) p)).tape (fun y : Bits (E.cUc (n i) (h i) (μ i) p) => lum y))
    (P:=fun i => 2^(n i)) (W:=fun _ => 0) hNU hl hNUs
  refine (H1.fork H2).mono (fun i => ?_)
  change 0 + NUf i + NUf i * 2^(n i) + (0 + NUf i + NUf i * 2^(n i)) ≤ NUf i * (2 * 2^(n i) + 2)
  nlinarith

/-- **The class context** from the three parts. -/
lemma cctx (c : CIn m B s x n h μ) :
    CCtx m B (ClsT s) (fun i => (((x i, E.idxVal (n i) (h i) (μ i)), E.unitVal (n i) (h i) (μ i)),
        E.gearVal (n i) (h i) (μ i))) E.X.n n (fun i => E.NUc (n i) (h i) (μ i))
      (fun i p => E.cUc (n i) (h i) (μ i) p) (fun i p => E.iUc (n i) (h i) (μ i) p) := by
  have c3 := ((c.ext (t:=IdxT) (fun i => E.idxVal (n i) (h i) (μ i))).ext (t:=UnT)
    (fun i => E.unitVal (n i) (h i) (μ i))).ext (t:=GearT) (fun i => E.gearVal (n i) (h i) (μ i))
  have U3 : Has m B (ClsT s) UnT (fun i => (((x i, E.idxVal (n i) (h i) (μ i)), E.unitVal (n i) (h i) (μ i)),
        E.gearVal (n i) (h i) (μ i))) (fun i => E.unitVal (n i) (h i) (μ i)) := Can.first.then_do Can.second
  have I3 : Has m B (ClsT s) IdxT (fun i => (((x i, E.idxVal (n i) (h i) (μ i)), E.unitVal (n i) (h i) (μ i)),
        E.gearVal (n i) (h i) (μ i))) (fun i => E.idxVal (n i) (h i) (μ i)) :=
    Can.first.then_do (Can.first.then_do Can.second)
  exact ⟨c3.nK, c3.p2n, Can.fst (Can.snd I3), c3.imag, Can.fst U3, Can.fst (Can.snd U3),
    Can.fst (Can.snd (Can.snd U3)), Can.snd (Can.snd (Can.snd U3)), Can.fst Can.second, Can.snd Can.second,
    c.big, (c.powS E.W).mono (fun i => E.NU_le' _ _ _), fun i p => E.fitc _ _ _ p,
    lt_of_lt_of_le (by norm_num) E.three⟩

end Eng

end
end PowerSaving.RAM
end OAI
