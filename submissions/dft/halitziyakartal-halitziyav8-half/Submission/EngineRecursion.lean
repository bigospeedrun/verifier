-- The engine, in three parts: the class job (part 1), the recursion principle and the top job (part 2),
-- the seam to the cost model and the ripple engine (part 3). Each part has its own notices and credits;
-- see texts/credits.lean.
import Submission.EngineSetup
import Submission.EngineCost
set_option linter.all false

-- ===== begin part 1: the class job =====
section
namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset GenMove
noncomputable section
universe U
/-- Undoing the split at `k` of an `n`-bit vector: the low part holds the address modulo `2^k`,
the high part the quotient. -/
lemma lowHigh_symm_loc {n k : ℕ} (hk : k ≤ n) (e : Bits n) :
    (bits k).loc ((lowHigh n k hk).symm e).1 = (bits n).loc e % 2 ^ k ∧
      (bits (n - k)).loc ((lowHigh n k hk).symm e).2 = (bits n).loc e / 2 ^ k := by
  obtain ⟨⟨u, v⟩, rfl⟩ := (lowHigh n k hk).surjective e
  have hu := bits_lt k u
  rw [Equiv.symm_apply_apply, lowHigh, Equiv.trans_apply, cast_append_loc]
  exact ⟨(DigitArith.mod_join' hu).symm, (DigitArith.div_join' hu).symm⟩
/-- With the empty pad, the book address of a grid is the body address of its word. -/
lemma book_nopad {β : Type*} (X : Layout β) (f : ℕ) (u : Grid β 0 f) :
    (gridLayout X 0 f).loc u = (skyLayout X f).loc u.2 := by
  show (bits 0).loc u.1 * _ + _ = _
  rw [bits_loc, Finset.univ_eq_empty, Finset.sum_empty, zero_mul, zero_add]
section Kit3
variable {ι : Type*} {m : Bool} {B : ι → ℕ} {s : Ty} {x : ι → T s}
open DigitArith
namespace BitCtx
variable {f : ι → ℕ} (g : BitCtx m B f s x)
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {k : ℕ}
  (S : Cleave α β (Fin k)) (X : Layout α) (X' : Layout β) {r n : ι → ℕ}
  (hfit : ∀ i, k * f i + X'.n * f i + r i = n i) (hbig : Small B fun i => 2^(n i))
include g hbig
lemma place_enc {q : ∀ i, Bits (r i)} {v : ∀ i, Grid α 0 (f i)}
    (hq : Knows m B s x fun i => (bits (r i)).loc (q i)) (hv : Knows m B s x fun i => (gridLayout X 0 (f i)).loc (v i)) :
    Knows m B s x fun i => (bits (n i)).loc (placeEquiv S X' (hfit i) (q i, (v i).2)) := by
  have ev : ∀ i, v i = (0, (v i).2) := fun i => Prod.ext (Subsingleton.elim _ _) rfl
  obtain ⟨hb, ha⟩ := g.peel_known S X X' v hv
  let low i := (bits (k * f i)).loc (S.peel 0 (f i) (v i)).2
  let mid i := (gridLayout X' 0 (f i)).loc (S.peel 0 (f i) (v i)).1
  let high i := (bits (r i)).loc (q i)
  let P i := 2^(k * f i)
  let Q i := 2^(X'.n * f i)
  have eq (i : ι) : (bits (n i)).loc (placeEquiv S X' (hfit i) (q i, (v i).2)) =
      low i + P i * (mid i + Q i * high i) := by
    show _ = (bits (k * f i)).loc (S.peel 0 (f i) (v i)).2 + 2 ^ (k * f i) *
      ((gridLayout X' 0 (f i)).loc (S.peel 0 (f i) (v i)).1 + 2 ^ (X'.n * f i) * (bits (r i)).loc (q i))
    rw [placeEquiv_loc, book_nopad]
    rfl
  have jobTotalCost : Small B (fun i => low i + P i * (mid i + Q i * high i)) :=
    hbig.mono fun i => by rw [← eq i]; exact ((bits _).bd _).le
  have inner : Small B (fun i => mid i + Q i * high i) :=
    jobTotalCost.mono fun i => (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)).trans (Nat.le_add_left _ _)
  exact (Can.joinBounded ha (g.knows_two_pow k) (Can.joinBounded hb (g.knows_two_pow X'.n) hq inner) jobTotalCost).congr
    fun i => (eq i).symm
lemma place_dec {e : ∀ i, Bits (n i)} (he : Knows m B s x fun i => (bits (n i)).loc (e i)) :
    Knows m B s x (fun i => (bits (r i)).loc ((placeEquiv S X' (hfit i)).symm (e i)).1) ∧
    Knows m B s x (fun i => (gridLayout X 0 (f i)).loc ((0 : Bits 0), ((placeEquiv S X' (hfit i)).symm (e i)).2)) := by
  let u i := S.peel 0 (f i) (0, ((placeEquiv S X' (hfit i)).symm (e i)).2)
  have D : ∀ i, (bits (n i)).loc (e i) % 2 ^ (k * f i) = (bits (k * f i)).loc (u i).2 ∧
      (bits (n i)).loc (e i) / 2 ^ (k * f i) % 2 ^ (X'.n * f i) = (gridLayout X' 0 (f i)).loc (u i).1 ∧
      (bits (n i)).loc (e i) / 2 ^ (k * f i) / 2 ^ (X'.n * f i) =
        (bits (r i)).loc ((placeEquiv S X' (hfit i)).symm (e i)).1 := fun i => by
    have h := placeEquiv_loc S X' (hfit i) ((placeEquiv S X' (hfit i)).symm (e i)).1
      ((placeEquiv S X' (hfit i)).symm (e i)).2
    rw [Prod.mk.eta, Equiv.apply_symm_apply] at h
    have hb : (skyLayout X' (f i)).loc (S.byLetter (f i) ((placeEquiv S X' (hfit i)).symm (e i)).2).1 <
        2 ^ (X'.n * f i) := skyLayout_len X' (f i) ▸ (skyLayout X' (f i)).bd _
    rw [h, book_nopad, DigitArith.mod_join' (bits_lt _ _), DigitArith.div_join' (bits_lt _ _),
      DigitArith.mod_join' hb, DigitArith.div_join' hb]
    exact ⟨rfl, rfl, rfl⟩
  have sE : Small B fun i => (bits (n i)).loc (e i) := hbig.mono fun i => ((bits _).bd _).le
  have hP := g.knows_two_pow k; have hQ := g.knows_two_pow X'.n
  have tail := he.dvdW hP sE
  refine ⟨(tail.dvdW hQ sE.div).congr fun i => (D i).2.2,
    (g.gridLayout_glue S X X' (Layout.std k) (fun _ => (0 : Bits 0)) (fun i => (u i).1.2)
      (fun i => (bitFlat k (f i)).symm (u i).2)
      ((Can.wc 0).congr fun _ => by rw [bits_loc, Finset.univ_eq_empty, Finset.sum_empty])
      ((tail.modW hQ sE.div).congr fun i => by rw [(D i).2.1, book_nopad])
      ((he.modW hP sE).congr fun i => by rw [(D i).1, bitFlat_skyLayout_loc])).congr
      fun i => (congrArg (gridLayout X 0 (f i)).loc ((S.peel 0 (f i)).symm_apply_apply
        ((0 : Bits 0), ((placeEquiv S X' (hfit i)).symm (e i)).2)) :)⟩
end BitCtx
end Kit3
namespace SlotEngine
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]
variable (E : SlotEngine α ρ σ)
lemma slotRank_lt_W (a : ℕ) (ha : a < E.W) : E.rankAt a = E.rank (E.SL.atFin ⟨a, ha⟩) := dif_pos ha

/-- Local cost of one class job on `n` bits: each stage (prefix, load, every move of the sweep with
its call set-up, unload) stays within a constant times one pass `2^n + 2n + 2`. -/
def classCost (n : ℕ) : ℕ := (E.prog.length + E.W + 1) * (2 ^ n + 2 * n + 2)

def Valid : EJob → Prop
  | ⟨false, _, _, _⟩ => True
  | ⟨true, n, μ, _⟩ => 1 ≤ μ ∧ E.mx * μ ≤ n

def passCost (n : ℕ) : ℕ := (E.RL.n + 1) * 2^n
lemma wd_block {l : ρ} {r : ℕ} {z : Fin r → Space α} {ind : LinearIndependent F z}
    (hm : Move.kern l r z ind ∈ E.prog) : 1 ≤ r ∧ r < E.LL.n :=
  E.prog_bounded.kern hm
lemma moveJobs_free {n μ : ℕ} {hf : E.mx * μ ≤ n} {mv : Move α ρ} (h0 : mv.rk? = none) (V : E.CState n μ)
    (rippleUpTo : Script α ρ) : E.leafKids hf V (mv :: rippleUpTo) = E.leafKids hf (E.stepState V mv) rippleUpTo := by
  rcases mv with (_|_|_|_|_) <;> first | rfl | cases h0
theorem kidsC_valid (d : EJob) (hd : E.Valid d) :
    ∀ c ∈ E.childJobs d, E.Valid c := by
  intro c hc
  match d, hd, hc with
  | ⟨false, _, _, _⟩, _, hc => cases hc
  | ⟨true, n, μ, J⟩, _, hc =>
    simp only [childJobs] at hc
    split_ifs at hc with hf
    · suffices ∀ (rippleUpTo : Script α ρ) V, c ∈ E.leafKids hf V rippleUpTo → E.Valid c from this _ _ hc
      intro rippleUpTo; induction rippleUpTo with
      | nil => intro _ h; cases h
      | cons mv rippleUpTo ih =>
        intro V h
        rcases Move.rk_cases mv with h0 | ⟨l, r, z, ind, rfl⟩
        · exact ih _ (E.moveJobs_free h0 V rippleUpTo ▸ h)
        · simp only [leafKids, moveKids, List.mem_append] at h
          refine h.elim (fun h => ?_) (ih _)
          split_ifs at h with hr
          · simp only [List.mem_singleton] at h; subst h; unfold sliceJob; trivial
          · cases h
    · cases hc
lemma pass_le (n : ℕ) : E.passCost n ≤ (E.RL.n + 2) * 2^n :=
  Nat.mul_le_mul_right _ (by omega)
lemma cost_close (n L W : ℕ) (hNL : 2^n ≤ L) (hW : W ≤ 6 * L + E.passCost n) :
    W ≤ (E.RL.n + 8) * L := by
  have := E.pass_le n; have := Nat.mul_le_mul_left (E.RL.n + 2) hNL
  calc W ≤ 6 * L + (E.RL.n + 2) * L := by omega
    _ = _ := by ring
lemma free_dom (n S : ℕ) : E.passCost n + S ≤ (E.RL.n + 3) * (2^n + S) := by
  have := E.pass_le n
  calc _ ≤ (E.RL.n + 2) * 2^n + S := by omega
    _ ≤ (E.RL.n + 2) * 2^n + 2^n + (E.RL.n + 3) * S := by
        have := Nat.le_mul_of_pos_left S (show 0 < E.RL.n + 3 by omega); have := Nat.two_pow_pos n; omega
    _ = _ := by ring
end SlotEngine
namespace SlotEngine
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]
variable (E : SlotEngine α ρ σ)
def stateTape {ι : Type*} (n μ : ι → ℕ) (V : ∀ i, E.CState (n i) (μ i)) (i : ι) : Tape (Tape ℂ) :=
  stateTab E.LL E.RL (μ i) (n i - E.mx * μ i) (V i)
abbrev Ctx {ι : Type U} (m : Bool) (B : ι → ℕ) (s : Ty) (y : ι → T s) (n μ : ι → ℕ) : Prop :=
  ClassCtx m B s y E.LL.n n μ
section Tab
/-- The pad cells of a family of class states: an instance with one pad value. -/
abbrev PadCell {ι : Type U} (n μ : ι → ℕ) := Σ i : ι, Bits (n i - E.mx * μ i)
abbrev ElemF {ι : Type U} (n μ : ι → ℕ) :=
  Σ v : E.PadCell n μ, RoleCell α ρ 0 (μ v.1)
abbrev instEnv {s : Ty} {ι : Type U} {n μ : ι → ℕ} (y : ι → T s) (v : E.PadCell n μ) : T (p s w) :=
  (y v.1, (bits (n v.1 - E.mx * μ v.1)).loc v.2)
/-- The environment of an element cell: its pad cell's environment and the fleet address of its
beach. -/
abbrev cellEnv {s : Ty} {ι : Type U} {n μ : ι → ℕ} (y : ι → T s) (d : E.ElemF n μ) : T (p (p s w) w) :=
  (E.instEnv y d.1, (roleLayout E.LL E.RL 0 (μ d.1.1)).loc d.2)
lemma elem_lift {ι : Type U} {n μ B : ι → ℕ} {m : Bool} {s t : Ty} {y : ι → T s} {z : ι → T t}
    (hz : Has m B s t y z) :
    Has m (fun d : E.ElemF n μ => B d.1.1) (p (p s w) w) t (E.cellEnv y) (fun d => z d.1.1) :=
  Can.first.fst.then_do (hz.reindex _)
lemma elem_gear {ι : Type U} {n μ B : ι → ℕ} {m : Bool} {s : Ty} {y : ι → T s}
    (cx : E.Ctx m B s y n μ) : BitCtx m (fun d : E.ElemF n μ => B d.1.1)
    (fun d => μ d.1.1) (p (p s w) w) (E.cellEnv y) :=
  cx.gear.descend (fun d : E.ElemF n μ => d.1.1) _ Can.first.fst
lemma elem_addr {ι : Type U} {n μ B : ι → ℕ} {m : Bool} {s : Ty} {y : ι → T s} (cx : E.Ctx m B s y n μ) :
    Knows m (fun d : E.ElemF n μ => B d.1.1) (p (p s w) w) (E.cellEnv y) (fun d => E.RL.loc d.2.1) ∧
    Knows m (fun d : E.ElemF n μ => B d.1.1) (p (p s w) w) (E.cellEnv y)
      (fun d => (gridLayout E.LL 0 (μ d.1.1)).loc d.2.2) :=
  ⟨Can.addr_high Can.second ((E.elem_gear cx).grid_size E.LL 0) ((Small.const _ E.RL.n).mul ((E.elem_gear cx).grid_small E.LL 0)),
   Can.addr_low Can.second ((E.elem_gear cx).grid_size E.LL 0) ((Small.const _ E.RL.n).mul ((E.elem_gear cx).grid_small E.LL 0))⟩
lemma can_tabEl {ι : Type U} {n μ B : ι → ℕ} {m : Bool} {s : Ty} {y : ι → T s} {cl : Paint}
    (cx : E.Ctx m B s y n μ) {V : ∀ i, E.CState (n i) (μ i)}
    (hel : Has m (fun d : E.ElemF n μ => B d.1.1) (p (p s w) w) (Ty.c cl) (E.cellEnv y)
      (fun d => V d.1.1 d.1.2 d.2)) :
    Can m B s (a (a (Ty.c cl))) y (fun i => E.stateTape n μ V i) (fun i => E.passCost (n i)) := by
  have g := cx.gear.descend (fun v : E.PadCell n μ => v.1) (E.instEnv y) Can.first
  refine can_stateTab E.LL E.RL (P := fun i => E.passCost (n i)) cx.p2restBits cx.padPowSmall (fun i => ?_)
    ((Can.layout (P := fun _ => 0) ((Can.wc _).times (g.grid_size E.LL 0) (Small.const _ _) (g.grid_small E.LL 0)) (Can.anyCost hel)
      ((Small.const _ _).mul (g.grid_small E.LL 0))).mono fun v => by simp [roleLayout, Layout.pair])
  have := cx.unit_size E.LL E.RL rfl i; have := cx.pow_restBits_le i; rw [roleLayout_n] at *
  unfold passCost; rw [Nat.succ_mul]; omega
lemma elemRig {ι : Type U} {n μ B : ι → ℕ} {m : Bool} {s : Ty} {y : ι → T s} {cl : Paint}
    (cx : E.Ctx m B s y n μ) {V : ∀ i, E.CState (n i) (μ i)}
    (ht : Has m B s (a (a (Ty.c cl))) y (fun i => E.stateTape n μ V i)) :
    RoleTapeCtx m (fun d : E.ElemF n μ => B d.1.1) (fun d => μ d.1.1)
      (p (p s w) w) (E.cellEnv y) cl E.LL E.RL 0 (fun d => V d.1.1 d.1.2) ∧
    Has m (fun d : E.ElemF n μ => B d.1.1) (p (p s w) w) (a sc) (E.cellEnv y)
      (fun d => (bits (μ d.1.1)).tape fun z => phaseProd z) := by
  have g : BitCtx m (fun d : E.ElemF n μ => B d.1.1) (fun d => μ d.1.1)
      (p (p s w) w) (E.cellEnv y) := E.elem_gear cx
  have t : Has m (fun d : E.ElemF n μ => B d.1.1) (p (p s w) w) (a (a (Ty.c cl))) (E.cellEnv y)
      (fun d => E.stateTape n μ V d.1.1) := Can.first.fst.then_do (ht.reindex _)
  unfold stateTape at t
  have i1 : Has m (fun d : E.ElemF n μ => B d.1.1) (p (p s w) w) sc (E.cellEnv y) (fun _ => Complex.I) :=
    Can.first.fst.then_do (cx.imag.reindex _)
  have it : Has m (fun d : E.ElemF n μ => B d.1.1) (p (p s w) w) (a (c cl)) (E.cellEnv y)
      (fun d => (roleLayout E.LL E.RL 0 (μ d.1.1)).tape (V d.1.1 d.1.2)) :=
    has_stateTabRow E.LL E.RL (fun d : E.ElemF n μ => d.1.2) t Can.first.snd
  have lu : Has m (fun d : E.ElemF n μ => B d.1.1) (p (p s w) w) (a sc) (E.cellEnv y)
      (fun d => (bits (μ d.1.1)).tape (fun z => phaseProd z)) :=
    Can.first.fst.then_do (cx.tlum.reindex (fun d : E.ElemF n μ => d.1.1))
  exact ⟨⟨g, i1, it⟩, lu⟩
lemma can_free {ι : Type U} {n μ B : ι → ℕ} {m : Bool} {s : Ty} {y : ι → T s} {cl : Paint}
    (cx : E.Ctx m B s y n μ) {mv : Move α ρ} (h0 : mv.rk? = none) (V : ∀ i, E.CState (n i) (μ i)) :
    Can m B (p s (a (a (Ty.c cl)))) (a (a (Ty.c cl))) (fun i => (y i, E.stateTape n μ V i))
      (fun i => E.stateTape n μ (fun i => E.stepState (V i) mv) i) (fun i => E.passCost (n i)) := by
  have cw : E.Ctx m B (p s (a (a (Ty.c cl)))) (fun i => (y i, E.stateTape n μ V i)) n μ :=
    cx.pull (t := p s (a (a (Ty.c cl)))) (fun i => i) (fun i => (y i, E.stateTape n μ V i)) Can.first
  have R := E.elemRig (cl := cl) (V := V) cw Can.second
  refine E.can_tabEl cw ?_
  exact R.1.ferry_free R.2 mv h0 (fun d => d.2) Can.second
lemma can_roleSet {ι : Type U} {n μ B : ι → ℕ} {m : Bool} {s : Ty} {y : ι → T s} {cl : Paint}
    (cx : E.Ctx m B s y n μ) {V V' : ∀ i, E.CState (n i) (μ i)} (l : ρ)
    (ht : Has m B s (a (a (Ty.c cl))) y (fun i => E.stateTape n μ V i))
    (hV : ∀ i q (b : RoleCell α ρ 0 (μ i)), b.1 ≠ l → V' i q b = V i q b)
    (hl : Has m (fun d : {d : E.ElemF n μ // d.2.1 = l} => B d.1.1.1) (p (p s w) w) (c cl) (fun d => E.cellEnv y d.1)
      (fun d => V' d.1.1.1 d.1.1.2 d.1.2)) :
    Can m B s (a (a (Ty.c cl))) y (fun i => E.stateTape n μ V' i) (fun i => E.passCost (n i)) := by
  have R := (E.elemRig cx ht).1
  refine E.can_tabEl cx (Can.cases_code E.RL (R.addrs _ Can.second).1 fun l' => ?_)
  by_cases e : l' = l
  · subst e; exact hl
  · exact ((Can.fetch R.items Can.second).reindex Subtype.val).cong (fun _ => rfl) fun d => (hV _ _ _ fun h' => e (d.2.symm.trans h')).symm
/-- The vector of slot `l` read back from a class state through the slot's placement. -/
def readSlot {n μ : ℕ} (hf : E.mx * μ ≤ n) (V : E.CState n μ) (l : σ) : Bits n → ℂ := fun e =>
  V ((E.slotPlace hf l).symm e).1 (E.role l, 0, ((E.slotPlace hf l).symm e).2)
/-- Row `t` of the unloaded table: the slot at position `t`, zero past the last slot. -/
def unload {n μ : ℕ} (hf : E.mx * μ ≤ n) (V : E.CState n μ) (t : ℕ) : Bits n → ℂ :=
  if h : t < E.W then E.readSlot hf V (E.SL.atFin ⟨t, h⟩) else 0
/-- After loading `W` rows and running the whole program, the `W` unloaded rows form the expected
answer rack of the class job: each row is its low partial ripple. -/
lemma unload_rack (cl : Paint) {n μ : ℕ} (hf : E.mx * μ ≤ n) (J : ℕ → Bits n → ℂ) :
    Tape.tab E.W (fun t => (bits n).tape (E.unload hf (E.runV (E.initState hf J) E.prog) t)) =
      E.jobRes cl ⟨true, n, μ, J⟩ := by
  show _ = Tape.tab E.W fun t => (bits n).tape (partRip n (fun i => i.val < E.lowLen μ t) (J t))
  refine Bench.tape_congr_sized fun t ht => congrArg (bits n).tape ?_
  let l := E.SL.atFin ⟨t, ht⟩
  have hl : E.SL.loc l = t := by simp [l]
  have rippleLow : E.lowLen μ t = E.rank l * μ := by
    unfold lowLen rankAt; rw [Nat.mod_eq_of_lt ht, dif_pos ht]
  -- the loaded table vanishes off the live roles
  let x0 : Bits (n - E.mx * μ) → Data α ρ μ := fun q j y => E.initState hf J q (j, 0, y)
  have off : ∀ q j, j ∉ Set.range E.role → x0 q j = 0 := fun q j hj => funext fun y => by
    simp only [x0, initState, E.slotOf_none j fun l' h => hj ⟨l', h⟩]; rfl
  have hS := Cleave.adapted_unit (E.vec l) (E.vec_indep l)
  funext e
  obtain ⟨⟨q, y⟩, rfl⟩ := (E.slotPlace hf l).surjective e
  rw [unload, dif_pos ht, rippleLow]
  have drv := congrFun (congrFun (E.drives.read_run μ l) ⟨x0 q, off q⟩) y
  have low := congrFun (placeEquiv_lowRipple (Cleave.adapted (E.vec l) (E.vec_indep l)) hS
    (Layout.std (Fintype.card α - E.rank l)) (fit_split (lay_n E.LL _ (E.rank_le l)) (Nat.add_sub_cancel' hf))
    (J t) q) y
  refine Eq.trans ?_ low.symm
  show E.runV _ E.prog ((E.slotPlace hf l).symm (E.slotPlace hf l (q, y))).1
    (E.role l, 0, ((E.slotPlace hf l).symm (E.slotPlace hf l (q, y))).2) = _
  rw [Equiv.symm_apply_apply]
  refine drv.trans (congrArg (fun u => letterwise μ (blockMat (E.vec l)) u y) (funext fun y' => ?_))
  show E.initState hf J q (E.role l, 0, y') = _
  simp only [initState, E.slotOf_role, hl]
  rfl
abbrev preEnv {ι : Type U} (cl : Paint) (n μ : ι → ℕ) (jobLocalCost : ι → Tape (Tape ℂ)) (i : ι) :
    T (p (p (p ((enginePort cl).1) w) UnitsTy) (p (a w) (a sc))) :=
  ((((headVal 1 (n i) (μ i), jobLocalCost i), 2^(n i)), E.unitVal (n i) (μ i)), gearVal (μ i))
lemma cin_port {ι : Type U} {B : ι → ℕ} {m : Bool} {cl : Paint} {n μ : ι → ℕ} {jobLocalCost : ι → Tape (Tape ℂ)} (hB2 : Small B fun i => 2^(n i))
    (hμ : ∀ i, μ i ≤ n i) :
    ClassIn m B (p ((enginePort cl).1) w) (fun i => ((headVal 1 (n i) (μ i), jobLocalCost i), 2^(n i))) n μ :=
  have sn : Small B n := hB2.mono fun i => Nat.lt_two_pow_self.le
  ⟨Has.extE Can.first.snd.fst, Has.extE Can.first.snd.snd.fst, Can.second, Has.extE Can.first.snd.snd.snd, hB2, sn.mono hμ⟩
/-- The pre-environment of a class job is a class input and a class context. -/
lemma pre_ctx {ι : Type U} {n μ B : ι → ℕ} {m : Bool} {cl : Paint} {jobLocalCost : ι → Tape (Tape ℂ)} (h2 : Small B fun i => 2 ^ n i)
    (hfit : ∀ i, E.mx * μ i ≤ n i) :
    ClassIn m B (p (p (p ((enginePort cl).1) w) UnitsTy) (p (a w) (a sc))) (E.preEnv cl n μ jobLocalCost) n μ ∧
      E.Ctx m B (p (p (p ((enginePort cl).1) w) UnitsTy) (p (a w) (a sc))) (E.preEnv cl n μ jobLocalCost) n μ := by
  have hμ : ∀ i, μ i ≤ n i := fun i =>
    (Nat.le_mul_of_pos_left _ (show 0 < E.LL.n by have := E.three_le; omega)).trans (hfit i)
  have c := cin_port (m := m) (cl := cl) (jobLocalCost := jobLocalCost) h2 hμ
  exact ⟨ClassIn.ofCtx (E.ctx_of_cin c hfit), E.ctx_of_cin c hfit⟩
/-- The prefix of a class job: the power `2^n`, the unit words and the gear values. -/
lemma prefix_can {ι : Type U} {n μ B : ι → ℕ} {m : Bool} {cl : Paint} {jobLocalCost : ι → Tape (Tape ℂ)} (h2 : Small B fun i => 2 ^ n i)
    (hfit : ∀ i, E.mx * μ i ≤ n i) :
    Can m B ((enginePort cl).1) (p (p (p ((enginePort cl).1) w) UnitsTy) (p (a w) (a sc)))
      (fun i => (headVal 1 (n i) (μ i), jobLocalCost i))
      (E.preEnv cl n μ jobLocalCost) (fun i => 2 * 2 ^ n i + 3 * n i + 5) := by
  have hμ : ∀ i, μ i ≤ n i := fun i =>
    (Nat.le_mul_of_pos_left _ (show 0 < E.LL.n by have := E.three_le; omega)).trans (hfit i)
  have c := cin_port (m := m) (cl := cl) (jobLocalCost := jobLocalCost) h2 hμ
  have sn : Small B n := h2.mono fun i => Nat.lt_two_pow_self.le
  have P1 := (Can.id (W := fun _ => 0)).fork (Can.wTwo (W := fun i => n i + 1) (Can.first.snd.fst : Knows m B ((enginePort cl).1)
    (fun i => (headVal 1 (n i) (μ i), jobLocalCost i)) n).anyCost sn h2 (Dom.of_le fun i => Nat.le_succ _))
  have Q1 := Can.wTwo (W := fun i => μ i + 1) c.μK.anyCost c.μS
    (h2.mono fun i => Nat.pow_le_pow_right two_pos (hμ i)) (Dom.of_le fun i => Nat.le_succ _)
  have Q2 := Can.wTwo (W := fun i => n i - E.mx * μ i + 1) (E.knows_restBits c).anyCost
    (c.nSmall.mono fun i => Nat.sub_le _ _) (h2.mono fun i => Nat.pow_le_pow_right two_pos (Nat.sub_le _ _))
    (Dom.of_le fun i => Nat.le_succ _)
  have P2 := (Can.id (W := fun _ => 0)).fork (Q1.fork Q2)
  have P3 := (Can.id (W := fun _ => 0)).fork (E.gears_can c hfit)
  exact ((P1.pipe P2).pipe P3).mono fun i => by
    have := hμ i
    show 0 + (n i + 1) + (0 + (μ i + 1 + (n i - E.mx * μ i + 1))) + (0 + (2 * 2 ^ n i + 2)) ≤ _; omega
/-- Loading, role by role: a role carrying a slot reads that slot's row of the own rack through
the slot's placement, a role without slot is zero. -/
lemma load_can {ι : Type U} {n μ B : ι → ℕ} {m : Bool} {s : Ty} {y : ι → T s} {cl : Paint}
    (cx : E.Ctx m B s y n μ) {J : ∀ i, ℕ → Bits (n i) → ℂ}
    (hJ : Has m B s (a (a (Ty.c cl))) y fun i => Tape.tab E.W fun t => (bits (n i)).tape (J i t)) :
    Can m B s (a (a (Ty.c cl))) y (fun i => E.stateTape n μ (fun i => E.initState (cx.fit i) (J i)) i)
      (fun i => E.passCost (n i)) := by
  refine E.can_tabEl cx (Can.cases_code E.RL (E.elem_addr cx).1 fun j => ?_)
  cases hs : E.roleSlot j with
  | none =>
    refine Can.zero.congr fun d => ?_
    obtain ⟨⟨⟨i, q⟩, j', pd, w⟩, hj⟩ := d
    subst hj
    simp only [initState, hs]
  | some l =>
    let S := Cleave.adapted (E.vec l) (E.vec_indep l)
    let X' := Layout.std (Fintype.card α - E.rank l)
    have hfit : ∀ d : {d : E.ElemF n μ // d.2.1 = j}, E.rank l * μ d.1.1.1 + X'.n * μ d.1.1.1 +
        (n d.1.1.1 - E.mx * μ d.1.1.1) = n d.1.1.1 := fun d =>
      fit_split (lay_n E.LL _ (E.rank_le l)) (Nat.add_sub_cancel' (cx.fit _))
    have g := (E.elem_gear cx).descend (fun d : {d : E.ElemF n μ // d.2.1 = j} => d.1) _ Can.id
    have hq : Knows m (fun d : {d : E.ElemF n μ // d.2.1 = j} => B d.1.1.1) (p (p s w) w)
        (fun d => E.cellEnv y d.1) fun d => (bits (n d.1.1.1 - E.mx * μ d.1.1.1)).loc d.1.1.2 :=
      (Can.first.snd : Knows m (fun d : E.ElemF n μ => B d.1.1) (p (p s w) w) (E.cellEnv y)
        fun d => (bits (n d.1.1 - E.mx * μ d.1.1)).loc d.1.2).reindex Subtype.val
    have ha := g.place_enc S E.LL X' hfit ((cx.big.reindex fun d : {d : E.ElemF n μ // d.2.1 = j} => d.1.1.1))
      hq ((E.elem_addr cx).2.reindex Subtype.val)
    refine (Can.rowEntry (fun d => bits (n d.1.1.1)) (N := fun _ => E.W) (R := fun d => J d.1.1.1)
      (k := fun _ => E.SL.loc l) (((E.elem_lift hJ).reindex Subtype.val)) (Can.wc _) (fun _ => E.SL.bd l) ha).congr
      fun d => ?_
    obtain ⟨⟨⟨i, q⟩, j', pd, w⟩, hj⟩ := d
    subst hj
    simp only [initState, hs]
    rfl
/-- A role read through any placement `placeEquiv S X'` of (pad, word) pairs, at a known address,
from an available table. -/
lemma read_placed {ι : Type U} {n μ B : ι → ℕ} {m : Bool} {s : Ty} {y : ι → T s} {cl : Paint}
    (cx : E.Ctx m B s y n μ) {V : ∀ i, E.CState (n i) (μ i)}
    (ht : Has m B s (a (a (Ty.c cl))) y (fun i => E.stateTape n μ V i))
    {β : Type*} [Fintype β] [DecidableEq β] {k : ℕ} (S : Cleave α β (Fin k)) (X' : Layout β)
    (hfit : ∀ i, k * μ i + X'.n * μ i + (n i - E.mx * μ i) = n i) (l : ρ)
    {e : ∀ i, Bits (n i)} (he : Knows m B s y fun i => (bits (n i)).loc (e i)) :
    Has m B s (c cl) y fun i => readThrough (placeEquiv S X' (hfit i)) (V i) l (e i) := by
  obtain ⟨hq, hb⟩ := cx.gear.place_dec S E.LL X' hfit cx.big he
  have hf := (knows_pair_iff (L₁ := fun _ => E.RL) (L₂ := fun i => gridLayout E.LL 0 (μ i))
    (u := fun i => (l, ((0 : Bits 0), ((placeEquiv S X' (hfit i)).symm (e i)).2)))
    (cx.gear.grid_size E.LL 0) (Small.const B E.RL.n) (cx.gear.grid_small E.LL 0)).2 ⟨Can.wc (E.RL.loc l), hb⟩
  exact has_stateTabRead E.LL E.RL (V' := V) (fun i => ((placeEquiv S X' (hfit i)).symm (e i)).1) _ ht hq hf
/-- Unloading, row by row: row `t < W` is the tape of slot `t` read through its placement; the slot
is chosen once per row. -/
lemma drain_can {ι : Type U} {n μ B : ι → ℕ} {m : Bool} {s : Ty} {y : ι → T s} {cl : Paint}
    (cx : E.Ctx m B s y n μ) {V : ∀ i, E.CState (n i) (μ i)}
    (ht : Has m B s (a (a (Ty.c cl))) y (fun i => E.stateTape n μ V i)) :
    Can m B s (a (a (Ty.c cl))) y
      (fun i => Tape.tab E.W fun t => (bits (n i)).tape (E.unload (cx.fit i) (V i) t))
      (fun i => E.W + E.W * 2 ^ n i) := by
  have hloc : Knows m (fun d : During (fun _ : ι => E.W) => B d.i) (p s w) (fun d => (y d.i, d.j))
      fun d => E.SL.loc (E.SL.atFin ⟨d.j, d.hj⟩) := Can.second.congr fun d => (E.SL.loc_atFin ⟨d.j, d.hj⟩).symm
  refine (Can.tab (uB := fun i _ => 2 ^ n i) (Can.wc E.W : Knows m B s y fun _ => E.W) (Can.cases_code E.SL hloc.anyCost fun l => ?_)
    (Small.const _ _)).mono fun i => by rw [sum_const']; omega
  have hfit : ∀ e : Σ d : {d : During (fun _ : ι => E.W) // E.SL.atFin ⟨d.j, d.hj⟩ = l}, Bits (n d.1.i),
      E.rank l * μ e.1.1.i + (Layout.std (Fintype.card α - E.rank l)).n * μ e.1.1.i +
        (n e.1.1.i - E.mx * μ e.1.1.i) = n e.1.1.i := fun e =>
    fit_split (lay_n E.LL _ (E.rank_le l)) (Nat.add_sub_cancel' (cx.fit _))
  have cx' := cx.pull (t := p (p s w) w) (fun e : Σ d : {d : During (fun _ : ι => E.W) // E.SL.atFin ⟨d.j, d.hj⟩ = l},
    Bits (n d.1.i) => e.1.1.i) (fun e => ((y e.1.1.i, e.1.1.j), (bits (n e.1.1.i)).loc e.2)) Can.first.fst
  have rd := E.read_placed cx' (V := fun e => V e.1.1.i) (Can.first.fst.then_do (ht.reindex _))
    (Cleave.adapted (E.vec l) (E.vec_indep l)) _ hfit (E.role l) (e := fun e => e.2) Can.second
  have hlen : Knows m (fun d : {d : During (fun _ : ι => E.W) // E.SL.atFin ⟨d.j, d.hj⟩ = l} => B d.1.i)
      (p s w) (fun d => (y d.1.i, d.1.j)) fun d => (bits (n d.1.i)).n :=
    (Has.extE (cx.p2n.reindex fun d : {d : During (fun _ : ι => E.W) // E.SL.atFin ⟨d.j, d.hj⟩ = l} => d.1.i)).congr
      fun d => (bits_len _).symm
  refine (Can.layout (L := fun d => bits (n d.1.i)) (P := fun _ => 0)
    (v := fun d e => E.unload (cx.fit d.1.i) (V d.1.i) d.1.j e) hlen (rd.congr fun e => ?_)
    ((cx.big.reindex fun d : {d : During (fun _ : ι => E.W) // E.SL.atFin ⟨d.j, d.hj⟩ = l} => d.1.i).mono
      fun d => (bits_len _).le)).mono (W' := fun d => 2 ^ n d.1.i) fun d => by simp
  obtain ⟨⟨d, hd⟩, u⟩ := e
  subst hd
  simp only [unload, dif_pos d.hj]
  rfl
/-- Write-back of one role through a placement: if the new value of every cell of role `l` is the
entry of an available rack of `2^(n - k μ)` rows on `k μ` bits, at the row and column given by the
high and low parts of the cell's placed address, and the other roles keep their values, the new
table costs one pass. -/
lemma writeBack {ι : Type U} {n μ B : ι → ℕ} {m : Bool} {s : Ty} {y : ι → T s} {cl : Paint}
    (cx : E.Ctx m B s y n μ) {V V' : ∀ i, E.CState (n i) (μ i)} (l : ρ)
    (ht : Has m B s (a (a (Ty.c cl))) y (fun i => E.stateTape n μ V i))
    {β : Type*} [Fintype β] [DecidableEq β] {k : ℕ} (S : Cleave α β (Fin k)) (X' : Layout β)
    (hfit : ∀ i, k * μ i + X'.n * μ i + (n i - E.mx * μ i) = n i) (hk : ∀ i, k * μ i ≤ n i)
    {R : ∀ i, ℕ → Bits (k * μ i) → ℂ}
    (hR : Has m B s (a (a (Ty.c cl))) y fun i =>
      Tape.tab (2 ^ (n i - k * μ i)) fun t => (bits (k * μ i)).tape (R i t))
    (hV : ∀ i q (b : RoleCell α ρ 0 (μ i)), b.1 ≠ l → V' i q b = V i q b)
    (hl : ∀ i q y, V' i q (l, 0, y) =
      R i ((bits (n i - k * μ i)).loc ((lowHigh (n i) (k * μ i) (hk i)).symm (placeEquiv S X' (hfit i) (q, y))).2)
        ((lowHigh (n i) (k * μ i) (hk i)).symm (placeEquiv S X' (hfit i) (q, y))).1) :
    Can m B s (a (a (Ty.c cl))) y (fun i => E.stateTape n μ V' i) (fun i => E.passCost (n i)) := by
  refine E.can_roleSet cx l ht hV ?_
  have g := (E.elem_gear cx).descend (fun d : {d : E.ElemF n μ // d.2.1 = l} => d.1) _ Can.id
  have hq : Knows m (fun d : {d : E.ElemF n μ // d.2.1 = l} => B d.1.1.1) (p (p s w) w)
      (fun d => E.cellEnv y d.1) fun d => (bits (n d.1.1.1 - E.mx * μ d.1.1.1)).loc d.1.1.2 :=
    (Can.first.snd : Knows m (fun d : E.ElemF n μ => B d.1.1) (p (p s w) w) (E.cellEnv y)
      fun d => (bits (n d.1.1 - E.mx * μ d.1.1)).loc d.1.2).reindex Subtype.val
  have sb := cx.big.reindex fun d : {d : E.ElemF n μ // d.2.1 = l} => d.1.1.1
  have he := g.place_enc S E.LL X' (fun d => hfit d.1.1.1) sb hq ((E.elem_addr cx).2.reindex Subtype.val)
  have sE : Small (fun d : {d : E.ElemF n μ // d.2.1 = l} => B d.1.1.1) fun d =>
      (bits (n d.1.1.1)).loc (placeEquiv S X' (hfit d.1.1.1) (d.1.1.2, d.1.2.2.2)) :=
    sb.mono fun d => ((bits _).bd _).le
  have hP := g.knows_two_pow k
  have hhi := (he.dvdW hP sE).congr fun d => (lowHigh_symm_loc (hk d.1.1.1) _).2.symm
  have hlo := (he.modW hP sE).congr fun d => (lowHigh_symm_loc (hk d.1.1.1) _).1.symm
  refine (Can.rowEntry (fun d : {d : E.ElemF n μ // d.2.1 = l} => bits (k * μ d.1.1.1))
    (N := fun d => 2 ^ (n d.1.1.1 - k * μ d.1.1.1)) (R := fun d => R d.1.1.1)
    ((E.elem_lift hR).reindex Subtype.val) hhi (fun d => (bits _).bd _) hlo).congr fun d => ?_
  obtain ⟨⟨⟨i, q⟩, j, pd, u⟩, hj⟩ := d
  subst hj
  obtain rfl : pd = 0 := Subsingleton.elim _ _
  exact (hl i q u).symm
lemma exit_eq {n μ r : ℕ} (hf : E.mx * μ ≤ n) (V : E.CState n μ) (l : ρ) (z : Fin r → Space α)
    (ind : LinearIndependent F z) (hr : r ≤ E.LL.n) (q : Bits (n - E.mx * μ)) (y : Sky α μ) :
    ripple (r * μ) (fun u => readThrough (blockPlace E.LL (Cleave.adapted z ind) hf hr) V l
      (sliceAddr (E.rk_fit hf hr) ((bits (n - r * μ)).loc ((lowHigh n (r * μ) (E.rk_fit hf hr)).symm
        (blockPlace E.LL (Cleave.adapted z ind) hf hr (q, y))).2) u))
      ((lowHigh n (r * μ) (E.rk_fit hf hr)).symm (blockPlace E.LL (Cleave.adapted z ind) hf hr (q, y))).1 =
      letterwise _ (blockMat z) (fun j => V q (l, 0, j)) y := by
  rw [← glueJob_ripple, Prod.mk.eta, Equiv.apply_symm_apply]
  have key := placeEquiv_lowRipple (Cleave.adapted z ind) (Cleave.adapted_unit z ind)
    (Layout.std (Fintype.card α - r)) (fit_split (lay_n E.LL _ hr) (Nat.add_sub_cancel' hf))
    (readThrough (blockPlace E.LL (Cleave.adapted z ind) hf hr) V l) q
  exact (congrFun key y).trans (congrArg (fun u => letterwise μ (blockMat z) u y)
    (funext fun y' => readThrough_place (blockPlace E.LL (Cleave.adapted z ind) hf hr) V l q y'))
end Tab
universe V
section Body
/-- A move without block rank, in one pass. -/
lemma free_able {ι : Type V} {m : Bool} {cl : Paint} {b : Bank (some (enginePort cl)) ι} {s : Ty} {y : ι → T s} {n μ : ι → ℕ}
    (c : E.Ctx m b.B s y n μ) {mv : Move α ρ} (h0 : mv.rk? = none) (V : ∀ i, E.CState (n i) (μ i)) :
    Able m b (p s (a (a (Ty.c cl)))) (p s (a (a (Ty.c cl)))) (fun i => (y i, E.stateTape n μ V i))
      (fun i => (y i, E.stateTape n μ (fun i => E.stepState (V i) mv) i)) (fun i => 2 ^ n i) (fun _ => 0) :=
  (Able.of_can (Can.first.pair (E.can_free c h0 V))).weaken (dom_mul (E.RL.n + 1) fun _ => le_rfl)
    fun _ => le_rfl
/-- One move of the program as an `Able` step on (input, table): a free move in one pass; a block
move by encoding its exit job (the slices of its role read through the adapted block placement),
calling it, and writing the rippled slices back. Local cost a constant times `2^n`, call cost the
prices of the move's children. -/
lemma move_able {ι : Type V} {m : Bool} {cl : Paint} {b : Bank (some (enginePort cl)) ι}
    {s : Ty} {y : ι → T s} {n μ : ι → ℕ} (c : E.Ctx m b.B s y n μ) (mv : Move α ρ) (hmv : mv ∈ E.prog)
    (V : ∀ i, E.CState (n i) (μ i)) {τ : ι → EJob → ℕ}
    (hcall : ∀ i, ∀ d ∈ E.moveKids (c.fit i) (V i) mv,
      (b.use i (E.jobEnc cl d)).OK (E.jobRes cl d) (τ i d) (b.ext i)) :
    Able m b (p s (a (a (Ty.c cl)))) (p s (a (a (Ty.c cl)))) (fun i => (y i, E.stateTape n μ V i))
      (fun i => (y i, E.stateTape n μ (fun i => E.stepState (V i) mv) i)) (fun i => 2 ^ n i)
      (fun i => ((E.moveKids (c.fit i) (V i) mv).map (τ i)).sum) := by
  rcases Move.rk_cases mv with h0 | ⟨l, r, z, ind, rfl⟩
  · exact (E.free_able c h0 V).mono (fun _ => le_rfl) fun _ => Nat.zero_le _
  have hr : r ≤ E.LL.n := (E.wd_block hmv).2.le
  have hk : ∀ i, r * μ i ≤ n i := fun i => E.rk_fit (c.fit i) hr
  have hfit : ∀ i, r * μ i + (Layout.std (Fintype.card α - r)).n * μ i + (n i - E.mx * μ i) = n i :=
    fun i => fit_split (lay_n E.LL _ hr) (Nat.add_sub_cancel' (c.fit i))
  have kids : ∀ i, E.moveKids (c.fit i) (V i) (Move.kern l r z ind) =
      [E.sliceJob (blockPlace E.LL (Cleave.adapted z ind) (c.fit i) hr) (V i) l (hk i)] := fun i => dif_pos hr
  -- the exit job's encoding
  have cx := c.pull (t := p s (a (a (Ty.c cl)))) (fun i => i) (fun i => (y i, E.stateTape n μ V i)) Can.first
  have gP := cx.gear.knows_two_pow r
  have sμ : Small b.B μ := cx.big.mono fun i => (ClassCtx.μ_le c i).trans Nat.lt_two_pow_self.le
  have sR : Small b.B fun i => 2 ^ (r * μ i) := cx.big.mono fun i => Nat.pow_le_pow_right two_pos (hk i)
  have sN : Small b.B fun i => 2 ^ (n i - r * μ i) := cx.big.mono fun i => Nat.pow_le_pow_right two_pos (Nat.sub_le _ _)
  have hN : Knows m b.B (p s (a (a (Ty.c cl)))) (fun i => (y i, E.stateTape n μ V i)) fun i => 2 ^ (n i - r * μ i) :=
    (cx.p2n.dvdW gP cx.big).congr fun i => Nat.pow_div (hk i) two_pos
  have cx2 := c.pull (t := p (p (p s (a (a (Ty.c cl)))) w) w)
    (fun e : Σ q : (Σ i, Fin (2 ^ (n i - r * μ i))), Bits (r * μ q.1) => e.1.1)
    (fun e => (((y e.1.1, E.stateTape n μ V e.1.1), e.1.2.val), (bits (r * μ e.1.1)).loc e.2)) Can.first.fst.fst
  have hloc : ∀ e : Σ q : (Σ i, Fin (2 ^ (n i - r * μ i))), Bits (r * μ q.1),
      (bits (n e.1.1)).loc (sliceAddr (hk e.1.1) e.1.2.val e.2) = (bits (r * μ e.1.1)).loc e.2 + 2 ^ (r * μ e.1.1) * e.1.2.val :=
    fun e => by rw [sliceAddr_loc, Nat.mod_eq_of_lt e.1.2.isLt]
  have sA : Small (fun e : Σ q : (Σ i, Fin (2 ^ (n i - r * μ i))), Bits (r * μ q.1) => b.B e.1.1)
      fun e => (bits (r * μ e.1.1)).loc e.2 + 2 ^ (r * μ e.1.1) * e.1.2.val :=
    cx2.big.mono fun e => by rw [← hloc]; exact ((bits _).bd _).le
  have he := (Can.wadd Can.second (Can.wmul (cx2.gear.knows_two_pow r) Can.first.snd
    (sA.mono fun _ => Nat.le_add_left _ _)) sA).congr fun e => (hloc e).symm
  have rd := E.read_placed cx2 (V := fun e => V e.1.1) Can.first.fst.snd (Cleave.adapted z ind) _
    (fun e => hfit e.1.1) l (e := fun e => sliceAddr (hk e.1.1) e.1.2.val e.2) he
  have rack := Can.rackOf (cl := cl) (L := fun i => bits (r * μ i)) (N := fun i => 2 ^ (n i - r * μ i))
    (R := fun i t u => readThrough (blockPlace E.LL (Cleave.adapted z ind) (c.fit i) hr) (V i) l (sliceAddr (hk i) t.val u))
    ⟨hN, gP.congr fun i => (bits_len _).symm, sN, sR.mono fun i => (bits_len _).le⟩ rd
  have enc : Can m b.B (p s (a (a (Ty.c cl)))) ((enginePort cl).1) (fun i => (y i, E.stateTape n μ V i))
      (fun i => E.jobEnc cl (E.sliceJob (blockPlace E.LL (Cleave.adapted z ind) (c.fit i) hr) (V i) l (hk i)))
      (fun i => 2 ^ (n i - r * μ i) + 2 ^ (n i - r * μ i) * (bits (r * μ i)).n) :=
    (((Can.wc 0).pair (((Can.wc r).times cx.μK (Small.const _ _) sμ).pair ((Can.wc 0).pair cx.imag))).anyCost.pair
      (rack.congr fun i => (Layout.tab_eq_tape (Layout.std _) fun t => (bits (r * μ i)).tape fun u =>
        readThrough (blockPlace E.LL (Cleave.adapted z ind) (c.fit i) hr) (V i) l (sliceAddr (hk i) t u)).symm)).congr
      fun i => rfl
  -- the call and the write-back
  have call := Able.use_call (m := m) (b := b) (Z := fun i => τ i (E.sliceJob (blockPlace E.LL (Cleave.adapted z ind) (c.fit i) hr) (V i) l (hk i)))
    fun i => hcall i _ (by rw [kids]; exact List.mem_singleton_self _)
  have cx3 := c.pull (t := p (p s (a (a (Ty.c cl)))) (a (a (Ty.c cl)))) (fun i => i)
    (fun i => ((y i, E.stateTape n μ V i),
      E.jobRes cl (E.sliceJob (blockPlace E.LL (Cleave.adapted z ind) (c.fit i) hr) (V i) l (hk i)))) Can.first.fst
  have wb := E.writeBack cx3 (V' := fun i => E.stepState (V i) (Move.kern l r z ind)) l Can.first.snd
    (Cleave.adapted z ind) _ hfit hk
    (R := fun i t u => ripple (r * μ i) (fun u' => readThrough (blockPlace E.LL (Cleave.adapted z ind) (c.fit i) hr)
      (V i) l (sliceAddr (hk i) t u')) u) Can.second
    (fun i q b hb => by simp only [stepState, padwise, Move.act, roleAct, if_neg hb])
    fun i q u => by
      show roleAct (μ i) l (blockMat z) (fun j y => V i q (j, 0, y)) l u = _
      rw [roleAct, if_pos rfl]
      exact (E.exit_eq (c.fit i) (V i) l z ind hr q u).symm
  refine (((Able.of_can enc).comp call).save (Able.of_can (Can.first.fst.pair wb))).weaken
    (dom_mul (E.RL.n + 3) fun i => ?_) fun i => ?_
  · have e1 : 2 ^ (n i - r * μ i) * (bits (r * μ i)).n = 2 ^ n i := by
      rw [bits_len, ← pow_add, Nat.sub_add_cancel (hk i)]
    have e2 : 2 ^ (n i - r * μ i) ≤ 2 ^ n i := Nat.pow_le_pow_right two_pos (Nat.sub_le _ _)
    show 2 ^ (n i - r * μ i) + 2 ^ (n i - r * μ i) * (bits (r * μ i)).n + 0 + E.passCost (n i) ≤ _
    rw [e1, passCost]
    have e3 : (E.RL.n + 3) * 2 ^ n i = (E.RL.n + 1) * 2 ^ n i + 2 ^ n i + 2 ^ n i := by ring
    omega
  · rw [kids]; simp
/-- The sweep of a script of program moves, one `move_able` step per move: from (input, table of
`V`) to (input, table of the run of the script), local cost the script length times `2^n`, call
cost the prices of the script's leaf children. -/
theorem sweep {ι : Type V} {m : Bool} {cl : Paint} {b : Bank (some (enginePort cl)) ι}
    {s : Ty} {y : ι → T s} {n μ : ι → ℕ} (c : E.Ctx m b.B s y n μ) {τ : ι → EJob → ℕ} :
    ∀ rippleUpTo : Script α ρ, (∀ mv ∈ rippleUpTo, mv ∈ E.prog) → ∀ V : ∀ i, E.CState (n i) (μ i),
      (∀ i, ∀ d ∈ E.leafKids (c.fit i) (V i) rippleUpTo, (b.use i (E.jobEnc cl d)).OK (E.jobRes cl d) (τ i d) (b.ext i)) →
      Able m b (p s (a (a (Ty.c cl)))) (p s (a (a (Ty.c cl)))) (fun i => (y i, E.stateTape n μ V i))
        (fun i => (y i, E.stateTape n μ (fun i => E.runV (V i) rippleUpTo) i)) (fun i => rippleUpTo.length * 2 ^ n i)
        (fun i => ((E.leafKids (c.fit i) (V i) rippleUpTo).map (τ i)).sum)
  | [], _, _, _ => Able.id
  | mv :: rippleUpTo, hws, V, hc =>
    ((E.move_able c mv (hws mv List.mem_cons_self) V fun i d hd => hc i d (List.mem_append_left _ hd)).comp
      (sweep c rippleUpTo (fun mv' h => hws mv' (List.mem_cons_of_mem _ h)) (fun i => E.stepState (V i) mv)
        fun i d hd => hc i d (List.mem_append_right _ hd))).mono
      (fun i => by rw [List.length_cons, Nat.succ_mul, Nat.add_comm]) fun i => by
        rw [leafKids, List.map_append, List.sum_append]
/-- **One class job.** Prefix, load, the sweep of the whole program, unload: from the encoding of
a fitting class job to its expected result, at the class cost, calling its child jobs. -/
theorem class_able {ι : Type V} {m : Bool} {cl : Paint} {b : Bank (some (enginePort cl)) ι} {n μ : ι → ℕ} {J : ∀ i, ℕ → Bits (n i) → ℂ}
    (h2 : Small b.B fun i => 2 ^ n i) (hfit : ∀ i, E.mx * μ i ≤ n i) {τ : ι → EJob → ℕ}
    (hcall : ∀ i, ∀ d ∈ E.childJobs ⟨true, n i, μ i, J i⟩,
      (b.use i (E.jobEnc cl d)).OK (E.jobRes cl d) (τ i d) (b.ext i)) :
    Able m b ((enginePort cl).1) (a (a (Ty.c cl))) (fun i => E.jobEnc cl ⟨true, n i, μ i, J i⟩)
      (fun i => E.jobRes cl ⟨true, n i, μ i, J i⟩) (fun i => E.classCost (n i))
      (fun i => ((E.childJobs ⟨true, n i, μ i, J i⟩).map (τ i)).sum) := by
  have hkids : ∀ i, E.childJobs ⟨true, n i, μ i, J i⟩ =
      E.leafKids (hfit i) (E.initState (hfit i) (J i)) E.prog := fun i => dif_pos (hfit i)
  obtain ⟨ci, c⟩ := E.pre_ctx (m := m) (cl := cl)
    (jobLocalCost := fun i => Tape.tab E.W fun t => (bits (n i)).tape (J i t)) h2 hfit
  have pre := E.prefix_can (m := m) (cl := cl)
    (jobLocalCost := fun i => Tape.tab E.W fun t => (bits (n i)).tape (J i t)) h2 hfit
  have load := E.load_can c (J := J) Can.first.fst.fst.snd
  have run := E.sweep c (τ := τ) E.prog (fun _ h => h) (fun i => E.initState (c.fit i) (J i))
    fun i d hd => hcall i d (by rw [hkids]; exact hd)
  have out := E.drain_can (cl := cl) (c.pull (t := p (p (p (p ((enginePort cl).1) w) UnitsTy) (p (a w) (a sc))) (a (a (Ty.c cl))))
    (fun i => i) (fun i => (E.preEnv cl n μ (fun i => Tape.tab E.W fun t => (bits (n i)).tape (J i t)) i,
      E.stateTape n μ (fun i => E.runV (E.initState (c.fit i) (J i)) E.prog) i)) Can.first)
    (V := fun i => E.runV (E.initState (c.fit i) (J i)) E.prog) Can.second
  refine (((Able.of_can pre).comp ((Able.of_can load).save (run.comp (Able.of_can out)))).cong
    (fun i => rfl) (fun i => E.unload_rack cl (hfit i) (J i))).weaken (dom_mul (E.RL.n + 4) fun i => ?_) fun i => ?_
  · have hX : 2 ^ n i ≤ 2 ^ n i + 2 * n i + 2 := by omega
    have hL : (E.prog.length + E.W + 1) * (2 ^ n i + 2 * n i + 2) =
        (E.prog.length + E.W) * (2 ^ n i + 2 * n i + 2) + (2 ^ n i + 2 * n i + 2) := by ring
    have hW := Nat.mul_le_mul_left E.W hX
    have hR := Nat.mul_le_mul_left (E.RL.n + 1) hX
    have hW1 := Nat.mul_le_mul_left E.W (show 2 ^ n i + 1 ≤ 2 ^ n i + 2 * n i + 2 by omega)
    rw [Nat.mul_add, Nat.mul_one] at hW1
    have hP := Nat.mul_le_mul_left E.prog.length hX
    show 2 * 2 ^ n i + 3 * n i + 5 + (E.passCost (n i) + (E.prog.length * 2 ^ n i +
      (E.W + E.W * 2 ^ n i))) ≤ (E.RL.n + 4) * E.classCost (n i)
    have h3 : 2 * 2 ^ n i + 3 * n i + 5 ≤ 3 * (2 ^ n i + 2 * n i + 2) := by omega
    have h5 := Nat.mul_le_mul_left (E.RL.n + 3)
      (Nat.le_add_left (2 ^ n i + 2 * n i + 2) ((E.prog.length + E.W) * (2 ^ n i + 2 * n i + 2)))
    unfold passCost classCost
    rw [hL]
    linarith
  · simp only [hkids, Nat.zero_add, Nat.add_zero, le_refl]
end Body
end SlotEngine
end
end PowerSaving.RAM
end OAI
end
-- ===== end part 1 =====

-- ===== begin part 2: closing a recursion; the top job =====
section

namespace OAI
namespace PowerSaving.EngineRecursion

noncomputable section

universe U V


section

open RAM Ty in
/-- What one call of a recursion body may rely on: a job, a handler answering every child of it
within a price per child and a common room. -/
structure Desc {Job : Type V} {s t : Ty} (enc : Job → T s) (res : Job → T t) (kids : Job → Multiset Job) where
  job : Job
  run : Handler (some (s, t))
  price : Job → ℕ
  room : ℕ
  ok : ∀ c ∈ kids job, (run (enc c)).OK (res c) (price c) room
open RAM Ty in
/-- The bank of descriptors: the bound of the job, the room as extra space, the handler. -/
def descBank {Job : Type V} {s t : Ty} {enc : Job → T s} {res : Job → T t} {kids : Job → Multiset Job} (bd : Job → ℕ) :
    Bank (some (s, t)) (Desc enc res kids) :=
  ⟨fun D => bd D.job, fun D => D.room, fun D => D.run⟩
open RAM Ty in
/-- **Closing a recursion.** A body that answers the job of every descriptor whose job satisfies
the invariant, calling its children, closes into a call-free program as soon as each step pays for
itself, children stay invariant, lose rank and do not grow, and a fuel above the rank is computable
and small. -/
theorem closed_of_body {Job : Type V} {s t : Ty} {m : Bool} {enc : Job → T s} {res : Job → T t} {kids : Job → Multiset Job}
    (Inv : Job → Prop) (bd jobLocalCost rk fuel cost : Job → ℕ)
    (body : Able m ((descBank (enc := enc) (res := res) (kids := kids) bd).comap
        fun D : {D : Desc enc res kids // Inv D.job} => D.1) s t (fun D => enc D.1.job)
      (fun D => res D.1.job) (fun D => jobLocalCost D.1.job) fun D => ((kids D.1.job).map D.1.price).sum)
    (hkid : ∀ j, Inv j → ∀ c ∈ kids j, Inv c ∧ rk c < rk j ∧ bd c ≤ bd j)
    (hstep : ∀ j, Inv j → jobLocalCost j + 1 + ((kids j).map cost).sum ≤ cost j)
    (hfuel : Can m (fun j : {j // Inv j} => bd j.1) s w (fun j => enc j.1) (fun j => fuel j.1)
      fun j => cost j.1)
    (hrk : ∀ j, Inv j → rk j < fuel j) (hsm : Small (fun j : {j // Inv j} => bd j.1) fun j => fuel j.1)
    {ι : Type U} (x : ι → Job) (hx : ∀ i, Inv (x i)) :
    Can m (fun i => bd (x i)) s t (fun i => enc (x i)) (fun i => res (x i)) fun i => cost (x i) := by
  obtain ⟨f, C, d, hf⟩ := body
  let step := f.run
  let base := (Code.inert (r := none) (m := m) s t).run ()
  -- depth `N` answers every invariant job of rank below `N`
  have deep : ∀ N j, Inv j → rk j < N →
      (depthRun base step N (enc j)).OK (res j) ((C + 1) * cost j) (max ((bd j + 2) ^ d) N) := by
    intro N
    induction N with
    | zero => intro j _ h; exact absurd h (Nat.not_lt_zero _)
    | succ N ih =>
      intro j hj hr
      let D : Desc enc res kids := ⟨j, depthRun base step N, fun c => (C + 1) * cost c,
        max ((bd j + 2) ^ d) N, fun c hc => by
          obtain ⟨hc1, hc2, hc3⟩ := hkid j hj c hc
          exact (ih c hc1 (by omega)).mono le_rfl
            (max_le_max (Nat.pow_le_pow_left (by omega) d) le_rfl)⟩
      have h := hf ⟨D, hj⟩
      have hs := hstep j hj
      have hsum : ((kids j).map fun c => (C + 1) * cost c).sum = (C + 1) * ((kids j).map cost).sum :=
        Multiset.sum_map_mul_left
      refine ((h.mono le_rfl ?_).pay (t := 1) (le_max_right _ _)).mono ?_ le_rfl
      · show max ((bd j + 2) ^ d) (max ((bd j + 2) ^ d) N) ≤ max ((bd j + 2) ^ d) (N + 1)
        exact max_le (le_max_left _ _) (max_le (le_max_left _ _) (le_max_of_le_right (Nat.le_succ N)))
      · show C * (jobLocalCost j + 1) + ((kids j).map fun c => (C + 1) * cost c).sum + 1 ≤ (C + 1) * cost j
        rw [hsum]
        have := Nat.mul_le_mul_left (C + 1) hs
        rw [Nat.mul_add, Nat.mul_add, Nat.mul_one] at this
        have : C * (jobLocalCost j + 1) + 1 ≤ (C + 1) * jobLocalCost j + (C + 1) := by
          rw [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one]; omega
        omega
  -- the descent from the fuel
  obtain ⟨e, he⟩ := hsm
  have run : Can m (fun j : {j // Inv j} => bd j.1) (p w s) t (fun j => (fuel j.1, enc j.1))
      (fun j => res j.1) fun j => cost j.1 :=
    ⟨Code.descend (Code.inert s t) f, C + 2, d + e, fun j => by
      have h := deep (fuel j.1) j.1 j.2 (hrk j.1 j.2)
      refine ((h.mono le_rfl (max_le_max le_rfl (le_refl (fuel j.1)))).pay (t := 1)
        (le_max_right _ _)).mono ?_ ?_
      · show (C + 1) * cost j.1 + 1 ≤ (C + 2) * (cost j.1 + 1) + 0
        rw [Nat.add_zero, Nat.mul_add, Nat.mul_one]
        have := Nat.mul_le_mul_right (cost j.1) (show C + 1 ≤ C + 2 by omega)
        omega
      · show max ((bd j.1 + 2) ^ d) (fuel j.1) ≤ max ((bd j.1 + 2) ^ (d + e)) 0
        exact le_max_of_le_left (max_le (Nat.pow_le_pow_right (by omega) (Nat.le_add_right _ _))
          ((he j).trans (Nat.pow_le_pow_right (by omega) (Nat.le_add_left _ _))))⟩
  exact (((hfuel.fork (Can.id (W := fun _ => 0))).pipe run).weaken
    (dom_mul 2 fun j => by show cost j.1 + 0 + cost j.1 ≤ 2 * cost j.1; omega)).reindex
    fun i => (⟨x i, hx i⟩ : {j // Inv j})
end
end
end PowerSaving.EngineRecursion
end OAI

namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset GenMove
noncomputable section
universe U
lemma sum_ite_lt (L a b N : ℕ) : ∑ j ∈ range N, (if j < L then a else b) ≤ min N L * a + (N - L) * b := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ]; split_ifs with h
    · rw [show min (N+1) L = min N L + 1 by omega, show N + 1 - L = N - L by omega, Nat.add_mul, Nat.one_mul]; omega
    · rw [show min (N+1) L = min N L by omega, show N + 1 - L = N - L + 1 by omega, Nat.add_mul, Nat.one_mul]; omega
lemma list_sum_map_range (f : ℕ → ℕ) (n : ℕ) : ((List.range n).map f).sum = ∑ j ∈ range n, f j := by
  induction n <;> simp [List.range_succ, sum_range_succ, *]
lemma walshConj_part_high (k lo : ℕ) : walshConj (part k lo k) = partKer k (fun i => lo ≤ i.val) := by
  have h1 : (littleC : Matrix F F ℂ) * littleH = littleH * Matrix.diagonal phaseI := by
    ext i j
    rw [Matrix.mul_apply, sumF, Matrix.mul_diagonal]
    rcases bit_cases i with rfl | rfl <;> rcases bit_cases j with rfl | rfl <;>
      simp only [littleC, littleH, sign, phaseI, ca, cb, ↓reduceIte, mul_zero, mul_one, zero_ne_one,
        one_ne_zero, mul_neg, neg_mul, one_mul] <;> ring_nf
  refine walshConj_eq_of_intertwine ?_
  have h2 : Matrix.diagonal (part k lo k) =
      digitProd (fun i : Fin k => Matrix.diagonal (if lo ≤ i.val then phaseI else fun _ => 1)) := by
    rw [digitProd_diagonal]; congr 1; funext x
    exact Finset.prod_congr rfl fun c _ => by by_cases h : lo ≤ c.val <;> simp [h, c.isLt]
  rw [h2, partKer, walshMat, digitProd_mul, digitProd_mul]
  congr 1; funext i
  by_cases h : lo ≤ i.val
  · simp only [h, if_true]; exact h1
  · simp only [h, if_false]; rw [Matrix.one_mul, Matrix.diagonal_one, Matrix.mul_one]
lemma hhigh_eq_ws (k lo : ℕ) (u : Bits k → ℂ) : partRip k (fun i => lo ≤ i.val) u = rippleUpTo k lo u k := by
  rw [rippleUpTo, walshConj_part_high]; rfl
lemma hhigh_zero (n : ℕ) (u : Bits n → ℂ) : partRip n (fun i => 0 ≤ i.val) u = ripple n u := by
  rw [hhigh_eq_ws, rippleUpTo_last]
/-- Naive kernel on the bit positions `lo .. n-1` of one tape. -/
lemma rippleHigh_moves {ι : Type U} {m : Bool} {B : ι → ℕ} {s : Ty} {x : ι → T s} {cl : Paint} {n lo : ι → ℕ}
    {u : ∀ i, Bits (n i) → ℂ} (hd : Knows m B s x (fun i => n i - lo i)) (hp : Knows m B s x (fun i => 2 ^ lo i))
    (hI : Has m B s sc x (fun _ => Complex.I)) (hT : Has m B s (a (c cl)) x (fun i => (bits (n i)).tape (u i)))
    (hlo : ∀ i, lo i ≤ n i) (h2 : Small B (fun i => 2^(n i))) :
    Can m B s (a (c cl)) x (fun i => (bits (n i)).tape (partRip (n i) (fun j => lo i ≤ j.val) (u i)))
      (fun i => 2^(n i) * (2 * (n i - lo i) + 1)) :=
  (((hd.pair (hp.pair (hI.pair hT))).pipe ((naive_high_can cl m n lo hlo u).ambient h2)).cong (fun _ => rfl)
    fun i => by rw [hhigh_eq_ws]).mono fun _ => (Nat.zero_add _).le
/-- The full ripple of one available tape, naively: the high kernel from position `0`. -/
lemma rip_naive {ι : Type U} {m : Bool} {B : ι → ℕ} {s : Ty} {x : ι → T s} {cl : Paint} {n : ι → ℕ}
    {u : ∀ i, Bits (n i) → ℂ} (hn : Knows m B s x n) (hI : Has m B s sc x fun _ => Complex.I)
    (hT : Has m B s (a (c cl)) x fun i => (bits (n i)).tape (u i)) (h2 : Small B fun i => 2 ^ n i) :
    Can m B s (a (c cl)) x (fun i => (bits (n i)).tape (ripple (n i) (u i)))
      (fun i => 2 ^ n i * (2 * n i + 1)) := by
  have k0 : Knows m B s x fun i => n i - 0 := hn.congr fun i => (Nat.sub_zero _).symm
  have k1 : Knows m B s x fun _ => 2 ^ 0 := (Can.wc 1).congr fun _ => (pow_zero 2).symm
  have h := rippleHigh_moves (lo := fun _ => 0) k0 k1 hI hT (fun _ => Nat.zero_le _) h2
  refine (h.congr fun i => ?_).mono fun i => ?_
  · rw [hhigh_zero]
  · rw [Nat.sub_zero]
/-- Cost of the tree of a top job with `q` full groups of `W` rows and `r` leftover rows at a
row price `X ≥ 1`: groups (encoding, call set-up and high kernel at the per-letter factor `c`),
the naive leftovers and the splice stay within `(c + 4)` times the top-job price. -/
lemma groups_left_le {q W r X n c B : ℕ} (hW : 0 < W) (hX : 1 ≤ X) (hB : q * W + r = B) :
    0 + q + q * (W * X + 0 + (W + W * (X * c))) + (0 + r + r * (X * (2 * n + 1)) + (q * W + r)) ≤
      (c + 4) * ((B + 1) * X + r * ((n + 1) * X)) := by
  have e1 : q * (W * X + 0 + (W + W * (X * c))) = q * W * X + q * W + c * (q * W * X) := by ring
  have a1 : q ≤ q * W := Nat.le_mul_of_pos_right _ hW
  have a2 : q * W ≤ q * W * X := Nat.le_mul_of_pos_right _ hX
  have a3 : q * W * X ≤ (B + 1) * X := Nat.mul_le_mul_right _ (by omega)
  have a4 : c * (q * W * X) ≤ c * ((B + 1) * X) := Nat.mul_le_mul_left _ a3
  have a5 : r ≤ r * ((n + 1) * X) := Nat.le_mul_of_pos_right _ (Nat.mul_pos (Nat.succ_pos _) hX)
  have e2 : r * (X * (2 * n + 1)) + r * X = 2 * (r * ((n + 1) * X)) := by ring
  have a6 : B + 1 ≤ (B + 1) * X := Nat.le_mul_of_pos_right _ hX
  have e3 : (c + 4) * ((B + 1) * X + r * ((n + 1) * X)) =
      c * ((B + 1) * X) + 4 * ((B + 1) * X) + c * (r * ((n + 1) * X)) + 4 * (r * ((n + 1) * X)) := by ring
  rw [e1, e3, hB]
  have a7 := Nat.zero_le (c * (r * ((n + 1) * X)))
  have a8 := Nat.zero_le (r * X)
  omega
/-- Splicing a rack: the first `N · k` cells are read from a table of `N` rows of `k` cells
(row-major), the following `L` cells from a second tape; zero cost per cell. -/
lemma Can.splice {ι : Type U} {m : Bool} {B : ι → ℕ} {s t : Ty} {x : ι → T s} {k : ℕ}
    {N L : ι → ℕ} {G : ι → ℕ → ℕ → T t} {H f : ι → ℕ → T t}
    (hG : Has m B s (a (a t)) x fun i => Tape.tab (N i) fun g => Tape.tab k (G i g))
    (hH : Has m B s (a t) x fun i => Tape.tab (L i) (H i))
    (hP : Knows m B s x fun i => N i * k) (hL : Knows m B s x L) (cutSize : Small B fun i => N i * k + L i)
    (hlo : ∀ i u, u < N i * k → f i u = G i (u / k) (u % k))
    (hhi : ∀ i j, j < L i → f i (N i * k + j) = H i j) :
    Can m B s (a t) x (fun i => Tape.tab (N i * k + L i) (f i)) (fun i => N i * k + L i) := by
  have sj : Small (fun d : During (fun i => N i * k + L i) => B d.i) fun d => d.j :=
    (cutSize.reindex During.i).mono fun d => d.hj.le
  have hj : Knows m (fun d : During (fun i => N i * k + L i) => B d.i) (p s w) (fun d => (x d.i, d.j))
      fun d => d.j := Can.second
  have hP' := Has.extE (v := fun d : During (fun i => N i * k + L i) => ((x d.i, d.j) : T (p s w))) (hP.reindex During.i)
  have lo := Can.look (Can.look (Has.extE (v := fun d : During (fun i => N i * k + L i) => ((x d.i, d.j) : T (p s w)))
    (hG.reindex During.i)) (hj.dvdW (Can.wc k) sj)) (hj.modW (Can.wc k) sj)
  have hi := Can.look (Has.extE (v := fun d : During (fun i => N i * k + L i) => ((x d.i, d.j) : T (p s w)))
    (hH.reindex During.i)) (hj.minus hP' sj)
  have e := Can.tab (uB := fun _ _ => 0)
    (v := fun i u => if (if u < N i * k then 1 else 0) = 0 then (Tape.tab (L i) (H i)).look (u - N i * k) t.blank
      else Tape.look ((Tape.tab (N i) fun g => Tape.tab k (G i g)).look (u / k) (a t).blank) (u % k) t.blank)
    (Can.wadd hP hL cutSize) (Can.branch (Can.wlt hj hP') hi lo) cutSize
  refine (e.congr fun i => Bench.tape_congr_sized fun u hu => ?_).mono fun i => by simp
  by_cases h : u < N i * k
  · have hk : 0 < k := Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.mul_zero] at h; exact Nat.not_lt_zero _ h
    rw [if_pos h, if_neg one_ne_zero, Tape.look_tab, if_pos (Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at h)),
      Tape.look_tab, if_pos (Nat.mod_lt _ hk)]
    exact (hlo i u h).symm
  · rw [if_neg h, if_pos rfl, Tape.look_tab, if_pos (by omega)]
    have h' := hhi i (u - N i * k) (by omega)
    rw [Nat.add_sub_cancel' (by omega)] at h'
    exact h'.symm
namespace SlotEngine
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]
variable (E : SlotEngine α ρ σ)

def topG (n : ℕ) : ℕ := n / E.mx
def topLo (n : ℕ) : ℕ := E.mx * E.topG n
/-- Local cost of a top job, one formula for both regimes: the copies and the tree pass, the
leftover vectors at the naive price, the prepared words, and below the cutoff a naive ripple of
every vector. -/
def topCost (n0 n B : ℕ) : ℕ :=
  (B + 1) * 2 ^ n + B % E.W * ((n + 1) * 2 ^ n) + 2 * (n + 1) +
    if n < n0 then (B + 1) * ((n + 1) * 2 ^ n) else 0

lemma topLo_le (n : ℕ) : E.topLo n ≤ n := Nat.mul_div_le n E.mx
/-- With uniform slot ranks, the low threshold of every row at letter width `μ` is `mx · μ`. -/
lemma lowLen_flat (htr : ∀ l, E.rank l = E.mx) (μ t : ℕ) : E.lowLen μ t = E.mx * μ := by
  unfold lowLen rankAt
  rw [dif_pos (Nat.mod_lt t E.slots_pos), htr]
/-- **The tree of a top job.** Every full group of `W` vectors goes to its root class job; each
answer is finished by the naive high kernel from `topLo n` up; the leftover vectors are rippled
naively. -/
theorem tree_able (htr : ∀ l, E.rank l = E.mx) {ι : Type U} {m : Bool} {cl : Paint}
    {b : Bank (some (enginePort cl)) ι} {s : Ty} {y : ι → T s} {n Bv : ι → ℕ} {v : ∀ i, ℕ → Bits (n i) → ℂ}
    (hn : Knows m b.B s y n) (hI : Has m b.B s sc y fun _ => Complex.I)
    (hp : Knows m b.B s y fun i => 2 ^ n i)
    (hd : Has m b.B s (a (a (Ty.c cl))) y fun i => Tape.tab (Bv i) fun t => (bits (n i)).tape (v i t))
    (hB : Knows m b.B s y Bv)
    (hg : Knows m b.B s y fun i => E.topG (n i)) (hl : Knows m b.B s y fun i => 2 ^ E.topLo (n i))
    (h2 : Small b.B fun i => (Bv i + 1) * 2 ^ n i) {τ : ι → EJob → ℕ}
    (hcall : ∀ i, ∀ t < Bv i / E.W, (b.use i (E.jobEnc cl ((⟨true, n i, E.topG (n i), fun j => v i (t * E.W + j)⟩)))).OK
      (E.jobRes cl ((⟨true, n i, E.topG (n i), fun j => v i (t * E.W + j)⟩))) (τ i ((⟨true, n i, E.topG (n i), fun j => v i (t * E.W + j)⟩))) (b.ext i)) :
    Able m b s (a (a (Ty.c cl))) y (fun i => Tape.tab (Bv i) fun t => (bits (n i)).tape (ripple (n i) (v i t)))
      (fun i => (Bv i + 1) * 2 ^ n i + Bv i % E.W * ((n i + 1) * 2 ^ n i))
      (fun i => ∑ t ∈ range (Bv i / E.W), τ i ((⟨true, n i, E.topG (n i), fun j => v i (t * E.W + j)⟩))) := by
  have sP : Small b.B fun i => 2 ^ n i := h2.mono fun i => Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  have sB : Small b.B Bv := h2.mono fun i =>
    (Nat.le_succ _).trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))
  have sn : Small b.B n := sP.mono fun i => Nat.lt_two_pow_self.le
  have hW : 0 < E.W := E.slots_pos
  have hrow : ∀ (i : ι) (t j : ℕ), t < Bv i / E.W → j < E.W → t * E.W + j < Bv i := fun i t j ht hj => by
    have h1 := Nat.div_mul_le_self (Bv i) E.W
    have h3 := Nat.mul_le_mul_right E.W (Nat.succ_le_of_lt ht); rw [Nat.succ_mul] at h3; omega
  -- one group `t`: the encoding of its root
  have enc : Can m (fun d : During (fun i => Bv i / E.W) => b.B d.i) (p s w) ((enginePort cl).1)
      (fun d => (y d.i, d.j)) (fun d => E.jobEnc cl ((⟨true, n d.i, E.topG (n d.i), fun j => v d.i (d.j * E.W + j)⟩)))
      (fun d => E.W * 2 ^ n d.i) := by
    have gy : Has m (fun e : Σ u : (Σ _ : During (fun i => Bv i / E.W), Fin E.W), Bits (n u.1.i) => b.B e.1.1.i)
        (p (p (p s w) w) w) s (fun e => (((y e.1.1.i, e.1.1.j), e.1.2.val), (bits (n e.1.1.i)).loc e.2))
        fun e => y e.1.1.i := Can.first.fst.fst
    have sR : Small (fun e : Σ u : (Σ _ : During (fun i => Bv i / E.W), Fin E.W), Bits (n u.1.i) => b.B e.1.1.i)
        fun e => e.1.1.j * E.W + e.1.2.val :=
      (sB.reindex fun e : Σ u : (Σ _ : During (fun i => Bv i / E.W), Fin E.W), Bits (n u.1.i) => e.1.1.i).mono
        fun e => (hrow _ _ _ e.1.1.hj e.1.2.isLt).le
    have hR : Knows m (fun e : Σ u : (Σ _ : During (fun i => Bv i / E.W), Fin E.W), Bits (n u.1.i) => b.B e.1.1.i)
        (p (p (p s w) w) w) (fun e => (((y e.1.1.i, e.1.1.j), e.1.2.val), (bits (n e.1.1.i)).loc e.2))
        fun e => e.1.1.j * E.W + e.1.2.val :=
      Can.wadd (Can.wmul Can.first.fst.snd (Can.wc E.W) (sR.mono fun e => Nat.le_add_right _ _))
        Can.first.snd sR
    have hJ := Can.rackOf (cl := cl) (s := p s w) (x := fun d : During (fun i => Bv i / E.W) => (y d.i, d.j))
      (N := fun _ => E.W) (fun d => bits (n d.i)) (R := fun d t => v d.i (d.j * E.W + t.val))
      ⟨Can.wc E.W, Has.extE (hp.reindex During.i), Small.const _ _, sP.reindex During.i⟩
      (Can.rowEntry (s := p (p (p s w) w) w) (t := Ty.c cl) (x := fun e : Σ u : (Σ _ : During (fun i => Bv i / E.W), Fin E.W),
          Bits (n u.1.i) => (((y e.1.1.i, e.1.1.j), e.1.2.val), (bits (n e.1.1.i)).loc e.2))
        (fun e => bits (n e.1.1.i)) (N := fun e => Bv e.1.1.i) (R := fun e => v e.1.1.i)
        (k := fun e => e.1.1.j * E.W + e.1.2.val) (q := fun e => e.2) (gy.then_do (hd.reindex fun e : Σ u : (Σ _ : During (fun i => Bv i / E.W), Fin E.W),
        Bits (n u.1.i) => e.1.1.i)) hR
        (fun e => hrow _ _ _ e.1.1.hj e.1.2.isLt) Can.second)
    have hJ' := (hJ.congr fun d => (Layout.tab_eq_tape (Layout.std E.W)
      fun t => (bits (n d.i)).tape (v d.i (d.j * E.W + t))).symm).weaken (dom_mul 2 fun d => by
      have := Nat.mul_le_mul_left E.W (Nat.one_le_two_pow (n := n d.i))
      show E.W + E.W * 2 ^ n d.i ≤ 2 * (E.W * 2 ^ n d.i); omega)
    exact ((Can.wc 1).pair ((Has.extE (hn.reindex During.i)).anyCost.pair ((Has.extE (hg.reindex During.i)).anyCost.pair
      (Has.extE (hI.reindex During.i)).anyCost))).pair hJ'
  -- its answer, finished row by row by the high kernel
  have fin : Can m (fun d : During (fun i => Bv i / E.W) => b.B d.i) (p (p s w) (a (a (Ty.c cl)))) (a (a (Ty.c cl)))
      (fun d => ((y d.i, d.j), E.jobRes cl ((⟨true, n d.i, E.topG (n d.i), fun j => v d.i (d.j * E.W + j)⟩))))
      (fun d => Tape.tab E.W fun j => (bits (n d.i)).tape (ripple (n d.i) (v d.i (d.j * E.W + j))))
      (fun d => E.W + E.W * (2 ^ n d.i * (2 * E.mx + 1))) := by
    have hsub : ∀ k, k - E.topLo k < E.mx := fun k => by
      have h1 := Nat.lt_mul_div_succ k (show 0 < E.LL.n by have := E.three_le; omega)
      have h3 := Nat.mul_div_le k E.LL.n
      show k - E.LL.n * (k / E.LL.n) < E.LL.n; rw [Nat.mul_add, Nat.mul_one] at h1; omega
    have gy : Has m (fun e : During (fun _ : During (fun i => Bv i / E.W) => E.W) => b.B e.i.i)
        (p (p (p s w) (a (a (Ty.c cl)))) w) s
        (fun e => (((y e.i.i, e.i.j), E.jobRes cl ((⟨true, n e.i.i, E.topG (n e.i.i), fun j => v e.i.i (e.i.j * E.W + j)⟩))), e.j))
        fun e => y e.i.i := Can.first.fst.fst
    have sl : Small (fun e : During (fun _ : During (fun i => Bv i / E.W) => E.W) => b.B e.i.i)
        fun e => E.topLo (n e.i.i) := (sn.reindex fun e : During (fun _ : During (fun i => Bv i / E.W) => E.W) => e.i.i).mono fun e => E.topLo_le _
    have hlo := (Can.wc E.mx).times (gy.then_do (hg.reindex fun e : During (fun _ : During (fun i => Bv i / E.W) => E.W) => e.i.i)) (Small.const _ _)
      ((sn.reindex fun e : During (fun _ : During (fun i => Bv i / E.W) => E.W) => e.i.i).mono fun e => Nat.div_le_self _ _)
    have row := Can.pick (t := a (Ty.c cl)) (n := fun _ => E.W) (W := fun _ => 0) (s := p (p (p s w) (a (a (Ty.c cl)))) w) (m := m)
      (B := fun e : During (fun _ : During (fun i => Bv i / E.W) => E.W) => b.B e.i.i)
      (x := fun e => (((y e.i.i, e.i.j), E.jobRes cl ((⟨true, n e.i.i, E.topG (n e.i.i), fun j => v e.i.i (e.i.j * E.W + j)⟩))), e.j))
      (fun e j => (bits (n e.i.i)).tape (partRip (n e.i.i) (fun k => k.val < E.lowLen (E.topG (n e.i.i)) j)
        (v e.i.i (e.i.j * E.W + j))))
      Can.first.snd Can.second (fun e => e.hj)
    have hi := rippleHigh_moves (lo := fun e : During (fun _ : During (fun i => Bv i / E.W) => E.W) => E.topLo (n e.i.i))
      ((gy.then_do (hn.reindex fun e : During (fun _ : During (fun i => Bv i / E.W) => E.W) => e.i.i)).minus hlo (sn.reindex fun e : During (fun _ : During (fun i => Bv i / E.W) => E.W) => e.i.i))
      (gy.then_do (hl.reindex fun e : During (fun _ : During (fun i => Bv i / E.W) => E.W) => e.i.i)) (gy.then_do (hI.reindex fun e : During (fun _ : During (fun i => Bv i / E.W) => E.W) => e.i.i)) row
      (fun e => E.topLo_le _) (sP.reindex fun e : During (fun _ : During (fun i => Bv i / E.W) => E.W) => e.i.i)
    have hi' := (hi.cong (fun _ => rfl) fun e => by
      show _ = (bits (n e.i.i)).tape (ripple (n e.i.i) (v e.i.i (e.i.j * E.W + e.j)))
      rw [E.lowLen_flat htr]
      exact congrArg _ (partRip_compl _ _ _ (fun k => Nat.not_lt.symm) _)).mono
      (W' := fun e => 2 ^ n e.i.i * (2 * E.mx + 1)) fun e =>
        Nat.mul_le_mul_left _ (by have := hsub (n e.i.i); omega)
    exact (Can.tab (uB := fun d _ => 2 ^ n d.i * (2 * E.mx + 1)) (Can.wc E.W) hi' (Small.const _ _)).mono
      fun d => by rw [sum_const', Nat.zero_add]
  have grp := ((Able.of_can enc).comp (Able.use_call (b := b.comap During.i)
    (Z := fun d : During (fun i => Bv i / E.W) => τ d.i ((⟨true, n d.i, E.topG (n d.i), fun j => v d.i (d.j * E.W + j)⟩)))
    fun d => hcall d.i d.j d.hj)).save (Able.of_can fin)
  have tapes := Able.tab (t := a (a (c cl)))
    (v := fun i t => Tape.tab E.W fun j => (bits (n i)).tape (ripple (n i) (v i (t * E.W + j))))
    (Wb := fun i _ => E.W * 2 ^ n i + 0 + (E.W + E.W * (2 ^ n i * (2 * E.mx + 1))))
    (Zb := fun i t => 0 + τ i ((⟨true, n i, E.topG (n i), fun j => v i (t * E.W + j)⟩)) + 0) (Able.of_can ((hB.dvdW (Can.wc E.W) sB).anyCost (V := fun _ => 0))) grp sB.div
  -- the leftover rows, rippled naively into their own tape
  have sq : Small b.B fun i => Bv i / E.W * E.W := sB.mono fun i => Nat.div_mul_le_self _ _
  have hq : Knows m b.B s y fun i => Bv i / E.W * E.W := (hB.dvdW (Can.wc E.W) sB).times (Can.wc E.W) sB.div (Small.const _ _)
  have hr : Knows m b.B s y fun i => Bv i % E.W := hB.modW (Can.wc E.W) sB
  have left : Can m b.B s (a (a (Ty.c cl))) y
      (fun i => Tape.tab (Bv i % E.W) fun j => (bits (n i)).tape (ripple (n i) (v i (Bv i / E.W * E.W + j))))
      (fun i => 0 + Bv i % E.W + ∑ _j ∈ range (Bv i % E.W), 2 ^ n i * (2 * n i + 1)) := by
    have sk : Small (fun d : During (fun i => Bv i % E.W) => b.B d.i) fun d => Bv d.i / E.W * E.W + d.j :=
      (sB.reindex During.i).mono fun d => by have := d.hj; have := Nat.div_add_mod' (Bv d.i) E.W; omega
    have row := Can.pick (t := a (Ty.c cl)) (n := fun d : During (fun i => Bv i % E.W) => Bv d.i)
      (k := fun d => Bv d.i / E.W * E.W + d.j)
      (fun d t => (bits (n d.i)).tape (v d.i t)) (Has.extE (hd.reindex During.i))
      (Can.wadd (Has.extE (v := fun d : During (fun i => Bv i % E.W) => ((y d.i, d.j) : T (p s w)))
        (hq.reindex During.i)) Can.second sk)
      fun d => by have := d.hj; have := Nat.div_add_mod' (Bv d.i) E.W; omega
    exact Can.tab hr (rip_naive (Has.extE (hn.reindex During.i)) (Has.extE (hI.reindex During.i)) row
      (sP.reindex During.i)) sB.mod
  -- splice the group answers and the leftover rows
  have glue := Can.splice (t := a (Ty.c cl)) (s := p (p s (a (a (a (Ty.c cl))))) (a (a (Ty.c cl)))) (k := E.W) (N := fun i => Bv i / E.W) (L := fun i => Bv i % E.W)
    (f := fun i t => (bits (n i)).tape (ripple (n i) (v i t)))
    (G := fun i g j => (bits (n i)).tape (ripple (n i) (v i (g * E.W + j))))
    (H := fun i j => (bits (n i)).tape (ripple (n i) (v i (Bv i / E.W * E.W + j))))
    (x := fun i => ((y i, Tape.tab (Bv i / E.W) fun t => Tape.tab E.W fun j =>
      (bits (n i)).tape (ripple (n i) (v i (t * E.W + j)))),
      Tape.tab (Bv i % E.W) fun j => (bits (n i)).tape (ripple (n i) (v i (Bv i / E.W * E.W + j)))))
    Can.first.snd Can.second (Has.extE (Has.extE hq)) (Has.extE (Has.extE hr))
    (sB.mono fun i => (Nat.div_add_mod' (Bv i) E.W).le)
    (fun i u _ => by rw [Nat.div_add_mod' u E.W]) fun i j _ => rfl
  have fin := ((Has.extE (t := a (a (a (Ty.c cl)))) (v := fun i => (y i, Tape.tab (Bv i / E.W) fun t => Tape.tab E.W fun j =>
      (bits (n i)).tape (ripple (n i) (v i (t * E.W + j))))) left).save glue).congr (y' := fun i => Tape.tab (Bv i) fun t => (bits (n i)).tape (ripple (n i) (v i t)))
    fun i => by rw [Nat.div_add_mod']
  refine (tapes.save (Able.of_can fin)).weaken (dom_mul (2 * E.mx + 5) fun i => ?_) fun i => by simp
  rw [sum_const', sum_const']
  exact groups_left_le hW Nat.one_le_two_pow (Nat.div_add_mod' (Bv i) E.W)
/-- A top job rippled naively, row by row. -/
lemma naive_can {ι : Type U} {m : Bool} {B : ι → ℕ} {cl : Paint} {n Bv : ι → ℕ}
    {v : ∀ i, ℕ → Bits (n i) → ℂ} (h2 : Small B fun i => (Bv i + 1) * 2 ^ n i) :
    Can m B ((enginePort cl).1) (a (a (Ty.c cl))) (fun i => E.jobEnc cl (⟨false, n i, Bv i, v i⟩))
      (fun i => E.jobRes cl (⟨false, n i, Bv i, v i⟩))
      (fun i => Bv i + Bv i * (2 ^ n i * (2 * n i + 1))) := by
  have sP : Small B fun i => 2 ^ n i := h2.mono fun i => Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  have sB : Small B Bv := h2.mono fun i =>
    (Nat.le_succ _).trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))
  have hd : Has m B ((enginePort cl).1) (a (a (Ty.c cl))) (fun i => E.jobEnc cl (⟨false, n i, Bv i, v i⟩))
      fun i => Tape.tab (Bv i) fun t => (bits (n i)).tape (v i t) := Can.second
  have hn : Knows m B ((enginePort cl).1) (fun i => E.jobEnc cl (⟨false, n i, Bv i, v i⟩)) n := Can.first.snd.fst
  have hI : Has m B ((enginePort cl).1) sc (fun i => E.jobEnc cl (⟨false, n i, Bv i, v i⟩)) fun _ => Complex.I :=
    Can.first.snd.snd.snd
  have rows := Can.tab (uB := fun i _ => 2 ^ n i * (2 * n i + 1))
    (t := a (Ty.c cl)) (v := fun i t => (bits (n i)).tape (ripple (n i) (v i t))) (Can.len hd sB)
    (rip_naive (Has.extE (hn.reindex During.i)) (Has.extE (hI.reindex During.i))
      (Can.pick (t := a (Ty.c cl)) (n := fun d : During Bv => Bv d.i) (fun d t => (bits (n d.i)).tape (v d.i t))
        (Has.extE (hd.reindex During.i)) Can.second fun d => d.hj) (sP.reindex During.i)) sB
  exact rows.mono fun i => by simp [Tape.tab]
section
variable {m : Bool}
/-- **One top job.** Below the cutoff, or with fewer than `W` vectors, every vector is rippled
naively; otherwise the prepared words feed the tree. -/
theorem top_able (htr : ∀ l, E.rank l = E.mx) (n0 : ℕ) {ι : Type U} {cl : Paint}
    {b : Bank (some (enginePort cl)) ι} {n Bv : ι → ℕ} {v : ∀ i, ℕ → Bits (n i) → ℂ}
    (h2 : Small b.B fun i => (Bv i + 1) * 2 ^ n i) {τ : ι → EJob → ℕ}
    (hcall : ∀ i, n0 ≤ n i → E.W ≤ Bv i → ∀ t < Bv i / E.W,
      (b.use i (E.jobEnc cl ⟨true, n i, E.topG (n i), fun j => v i (t * E.W + j)⟩)).OK (E.jobRes cl ⟨true, n i, E.topG (n i), fun j => v i (t * E.W + j)⟩) (τ i ⟨true, n i, E.topG (n i), fun j => v i (t * E.W + j)⟩) (b.ext i)) :
    Able m b ((enginePort cl).1) (a (a (Ty.c cl))) (fun i => E.jobEnc cl (⟨false, n i, Bv i, v i⟩))
      (fun i => E.jobRes cl (⟨false, n i, Bv i, v i⟩)) (fun i => E.topCost n0 (n i) (Bv i))
      (fun i => if n0 ≤ n i ∧ E.W ≤ Bv i then ∑ t ∈ range (Bv i / E.W), τ i ⟨true, n i, E.topG (n i), fun j => v i (t * E.W + j)⟩ else 0) := by
  have hn : Knows m b.B ((enginePort cl).1) (fun i => E.jobEnc cl (⟨false, n i, Bv i, v i⟩)) n := Can.first.snd.fst
  have hBv : Knows m b.B ((enginePort cl).1) (fun i => E.jobEnc cl (⟨false, n i, Bv i, v i⟩)) Bv :=
    Can.len Can.second (h2.mono fun i =>
      (Nat.le_succ _).trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)))
  have naive : ∀ (P : ι → Prop), (∀ i, P i → n i < n0 ∨ Bv i < E.W) →
      Able m (b.comap fun i : {i // P i} => i.1) ((enginePort cl).1) (a (a (Ty.c cl)))
        (fun i => E.jobEnc cl (⟨false, n i.1, Bv i.1, v i.1⟩)) (fun i => E.jobRes cl (⟨false, n i.1, Bv i.1, v i.1⟩))
        (fun i => E.topCost n0 (n i.1) (Bv i.1))
        (fun i => if n0 ≤ n i.1 ∧ E.W ≤ Bv i.1 then ∑ t ∈ range (Bv i.1 / E.W), τ i.1 ⟨true, n i.1, E.topG (n i.1), fun j => v i.1 (t * E.W + j)⟩ else 0) :=
    fun P hP => (Able.of_can (E.naive_can (h2.reindex Subtype.val))).weaken
      (dom_mul 3 fun i => by
        have hX := Nat.one_le_two_pow (n := n i.1)
        have h1 : Bv i.1 * (2 ^ n i.1 * (2 * n i.1 + 1)) ≤ 2 * (Bv i.1 * ((n i.1 + 1) * 2 ^ n i.1)) :=
          calc Bv i.1 * (2 ^ n i.1 * (2 * n i.1 + 1)) ≤ Bv i.1 * (2 * ((n i.1 + 1) * 2 ^ n i.1)) :=
                Nat.mul_le_mul_left _ ((Nat.mul_comm _ _).trans_le ((Nat.mul_le_mul_right _
                  (show 2 * n i.1 + 1 ≤ 2 * (n i.1 + 1) by omega)).trans_eq (Nat.mul_assoc _ _ _)))
            _ = 2 * (Bv i.1 * ((n i.1 + 1) * 2 ^ n i.1)) := by ring
        have h3 : Bv i.1 ≤ Bv i.1 * ((n i.1 + 1) * 2 ^ n i.1) :=
          Nat.le_mul_of_pos_right _ (Nat.mul_pos (Nat.succ_pos _) (Nat.two_pow_pos _))
        have z1 := Nat.zero_le ((Bv i.1 + 1) * 2 ^ n i.1)
        have z2 := Nat.zero_le ((n i.1 + 1) * 2 ^ n i.1)
        show Bv i.1 + Bv i.1 * (2 ^ n i.1 * (2 * n i.1 + 1)) ≤ 3 * E.topCost n0 (n i.1) (Bv i.1)
        unfold topCost
        have z3 := Nat.zero_le (2 * (n i.1 + 1))
        have z4 := Nat.zero_le (Bv i.1 % E.W * ((n i.1 + 1) * 2 ^ n i.1))
        split_ifs with h0
        · have e : (Bv i.1 + 1) * ((n i.1 + 1) * 2 ^ n i.1) =
              Bv i.1 * ((n i.1 + 1) * 2 ^ n i.1) + (n i.1 + 1) * 2 ^ n i.1 := by ring
          linarith
        · have hb : Bv i.1 < E.W := (hP _ i.2).resolve_left h0
          rw [Nat.mod_eq_of_lt hb]
          linarith) fun _ => Nat.zero_le _
  refine Able.branch (n := fun i => if n i < n0 then 1 else 0) (Can.wlt hn (Can.wc n0)).anyCost
    (fun i => n0 ≤ n i) (fun i => by by_cases h : n i < n0 <;> simp [h] <;> omega) ?_ (naive _ fun i h => Or.inl (by omega))
  refine Able.branch (n := fun i => if Bv i.1 < E.W then 1 else 0) (Can.wlt (hBv.reindex Subtype.val)
    (Can.wc E.W)).anyCost (fun i => E.W ≤ Bv i.1) (fun i => by by_cases h : Bv i.1 < E.W <;> simp [h] <;> omega) ?_
    ((naive (fun i => ¬ E.W ≤ Bv i) fun i h => Or.inr (by omega)).reindex
      fun i : {i : {i // n0 ≤ n i} // ¬ E.W ≤ Bv i.1} => (⟨i.1.1, i.2⟩ : {i // ¬ E.W ≤ Bv i}))
  -- the tree branch
  have hkey : ∀ i : {i : {i // n0 ≤ n i} // E.W ≤ Bv i.1}, n0 ≤ n i.1.1 ∧ E.W ≤ Bv i.1.1 := fun i => ⟨i.1.2, i.2⟩
  have h2' := h2.reindex fun i : {i : {i // n0 ≤ n i} // E.W ≤ Bv i.1} => i.1.1
  have sP : Small _ fun i : {i : {i // n0 ≤ n i} // E.W ≤ Bv i.1} => 2 ^ n i.1.1 :=
    h2'.mono fun i => Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  have hn' := hn.reindex fun i : {i : {i // n0 ≤ n i} // E.W ≤ Bv i.1} => i.1.1
  -- the prepared words `2^n`, `topG n = n / mx` and `2^(topLo n)`
  have sn' : Small _ fun i : {i : {i // n0 ≤ n i} // E.W ≤ Bv i.1} => n i.1.1 := sP.mono fun i => Nat.lt_two_pow_self.le
  have hg' := hn'.dvdW (Can.wc E.mx) sn'
  have w1 := Can.wTwo (W := fun i : {i : {i // n0 ≤ n i} // E.W ≤ Bv i.1} => n i.1.1 + 1) hn'.anyCost sn' sP (Dom.of_le fun i => Nat.le_succ _)
  have w2 := Can.wTwo (W := fun i : {i : {i // n0 ≤ n i} // E.W ≤ Bv i.1} => n i.1.1 + 1)
    ((Can.wc E.mx).times hg' (Small.const _ _) (sn'.mono fun i => Nat.div_le_self _ _)).anyCost
    (sn'.mono fun i => E.topLo_le _) (sP.mono fun i => Nat.pow_le_pow_right two_pos (E.topLo_le _))
    (Dom.of_le fun i => (E.topLo_le _).trans (Nat.le_succ _))
  have prep : Can m (fun i : {i : {i // n0 ≤ n i} // E.W ≤ Bv i.1} => b.B i.1.1) ((enginePort cl).1) (p w (p w w))
      (fun i => E.jobEnc cl (⟨false, n i.1.1, Bv i.1.1, v i.1.1⟩))
      (fun i => (2 ^ n i.1.1, E.topG (n i.1.1), 2 ^ E.topLo (n i.1.1)))
      (fun i => n i.1.1 + 1) :=
    w1.pair (hg'.anyCost.pair w2)
  have tree := E.tree_able htr (b := (b.comap Subtype.val).comap Subtype.val)
    (s := p ((enginePort cl).1) (p w (p w w)))
    (y := fun i => (E.jobEnc cl (⟨false, n i.1.1, Bv i.1.1, v i.1.1⟩),
      (2 ^ n i.1.1, E.topG (n i.1.1), 2 ^ E.topLo (n i.1.1))))
    (n := fun i => n i.1.1) (Bv := fun i => Bv i.1.1)
    (v := fun i => v i.1.1) (Has.extE hn') (Has.extE (Can.first.snd.snd.snd.reindex _)) Can.second.fst
    (Has.extE (Can.second.reindex _)) (Has.extE (hBv.reindex _)) Can.second.snd.fst
    Can.second.snd.snd h2' (τ := fun i => τ i.1.1) fun i t ht => hcall i.1.1 (hkey i).1 (hkey i).2 t ht
  have out : Can m (fun i : {i : {i // n0 ≤ n i} // E.W ≤ Bv i.1} => b.B i.1.1) (a (a (Ty.c cl))) (a (a (Ty.c cl)))
      (fun i => Tape.tab (Bv i.1.1) fun t => (bits (n i.1.1)).tape (ripple (n i.1.1) (v i.1.1 t)))
      (fun i => E.jobRes cl (⟨false, n i.1.1, Bv i.1.1, v i.1.1⟩)) (fun _ => 0) :=
    Can.id
  refine ((Able.of_can prep).save (tree.comp (Able.of_can out))).weaken
    (Dom.of_le fun i => ?_) fun i => ?_
  · show n i.1.1 + 1 + ((Bv i.1.1 + 1) * 2 ^ n i.1.1 + Bv i.1.1 % E.W * ((n i.1.1 + 1) * 2 ^ n i.1.1) + 0) ≤
      E.topCost n0 (n i.1.1) (Bv i.1.1)
    rw [topCost, if_neg (Nat.not_lt.2 (hkey i).1)]; omega
  · rw [if_pos (hkey i)]; simp
end
end SlotEngine
end
end PowerSaving.RAM
end OAI
end
-- ===== end part 2 =====

-- ===== begin part 3: the seam to the cost model; the ripple engine =====
section
namespace OAI.PowerSaving
namespace RAM
open Binary Matrix Ty Finset GenMove EngineRecursion
noncomputable section
universe U
namespace SlotEngine
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]
variable (E : SlotEngine α ρ σ)
/-- The bit count of a job. -/
abbrev jobBits (d : EJob) : ℕ := d.n
/-- The form of a job in the cost model: a top job is a batch, a class job a block. -/
def _root_.OAI.PowerSaving.RAM.EJob.form : EJob → EngineCost.JobForm
  | ⟨false, n, B, _⟩ => .batch n B
  | ⟨true, n, μ, _⟩ => .block n μ
def jobCount : EJob → ℕ | ⟨false, _, B, _⟩ => B | ⟨true, _, _, _⟩ => 0
def jobTop : (d : EJob) → ℕ → Bits (jobBits d) → ℂ | ⟨false, _, _, v⟩ => v | ⟨true, _, _, _⟩ => fun _ _ => 0
def jobClassDim : EJob → ℕ | ⟨true, _, μ, _⟩ => μ | ⟨false, _, _, _⟩ => 0
def jobData (d : EJob) : ℕ → Bits (jobBits d) → ℂ := d.vec
/-- The size bound of a job: `(B+2) 2^n` for a top job, `2·2^n` for a class job. -/
def jobBound : EJob → ℕ
  | ⟨false, n, B, _⟩ => (B + 2) * 2 ^ n
  | ⟨true, n, _, _⟩ => 2 * 2 ^ n
def locD (n0 : ℕ) : EJob → ℕ
  | ⟨false, n, B, _⟩ => E.topCost n0 n B
  | ⟨true, n, _, _⟩ => E.classCost n
def allChildJobs (n0 : ℕ) : EJob → List EJob
  | ⟨false, n, B, v⟩ => if n0 ≤ n ∧ E.W ≤ B then
      (List.range (B / E.W)).map fun t => ⟨true, n, E.topG n, fun j => v (t * E.W + j)⟩ else []
  | d => E.childJobs d
/-- The children of a job as a multiset: the recursion runs on plain jobs, validity is its
invariant. -/
abbrev childSet (n0 : ℕ) (d : EJob) : Multiset EJob := (E.allChildJobs n0 d : Multiset EJob)
private lemma top_eta (cl : Paint) : ∀ d : EJob, (E.jobEnc cl d).1.1 = 0 → (⟨false, jobBits d, jobCount d, jobTop d⟩ : EJob) = d
  | ⟨false, _, _, _⟩, _ => rfl
  | ⟨true, _, _, _⟩, h => absurd h Nat.one_ne_zero
private lemma cls_eta (cl : Paint) : ∀ d : EJob, (E.jobEnc cl d).1.1 ≠ 0 →
    (⟨true, jobBits d, jobClassDim d, jobData d⟩ : EJob) = d
  | ⟨false, _, _, _⟩, h => absurd rfl h
  | ⟨true, _, _, _⟩, _ => rfl
private lemma bnd_ge (d : EJob) : (jobCount d + 1) * 2 ^ jobBits d ≤ (jobBound d + 2) ^ 1 ∧ 2 ^ jobBits d ≤ (jobBound d + 2) ^ 1 ∧
    jobCount d ≤ (jobBound d + 2) ^ 1 := by
  have e : jobBound d = (jobCount d + 2) * 2 ^ jobBits d := by rcases d with ⟨_ | _, n, B, v⟩ <;> rfl
  have := Nat.one_le_two_pow (n := jobBits d)
  rw [pow_one, e]
  exact ⟨(Nat.mul_le_mul_right _ (Nat.le_succ _)).trans (Nat.le_add_right _ _),
    (Nat.le_mul_of_pos_left _ (Nat.succ_pos _)).trans (Nat.le_add_right _ _),
    ((Nat.le_add_right _ 2).trans (Nat.le_mul_of_pos_right _ this)).trans (Nat.le_add_right _ _)⟩
private lemma top_facts (n0 : ℕ) (cl : Paint) : ∀ d : EJob, (E.jobEnc cl d).1.1 = 0 →
    E.allChildJobs n0 d = (if n0 ≤ jobBits d ∧ E.W ≤ jobCount d then (List.range (jobCount d / E.W)).map
      fun t => ⟨true, jobBits d, E.topG (jobBits d), fun j => jobTop d (t * E.W + j)⟩ else []) ∧ E.locD n0 d = E.topCost n0 (jobBits d) (jobCount d)
  | ⟨false, _, _, _⟩, _ => ⟨rfl, rfl⟩
  | ⟨true, _, _, _⟩, h => absurd h Nat.one_ne_zero
private lemma cls_facts (n0 : ℕ) (cl : Paint) : ∀ d : EJob, (E.jobEnc cl d).1.1 ≠ 0 →
    E.allChildJobs n0 d = E.childJobs (⟨true, jobBits d, jobClassDim d, (jobData d)⟩) ∧ E.locD n0 d = E.classCost (jobBits d) ∧
      (E.Valid d → E.mx * jobClassDim d ≤ jobBits d)
  | ⟨false, _, _, _⟩, h => absurd rfl h
  | ⟨true, _, _, _⟩, _ => ⟨rfl, rfl, fun h => h.2⟩
/-- The bank of the engine recursion: descriptors of valid jobs, bounded by `jobBound`. -/
abbrev engBank (n0 : ℕ) (cl : Paint) :=
  (descBank (enc := E.jobEnc cl) (res := E.jobRes cl) (kids := E.childSet n0) jobBound).comap
    fun D : {D : Desc (E.jobEnc cl) (E.jobRes cl) (E.childSet n0) // E.Valid D.job} => D.1
/-- **The body of the engine recursion.** One program answers the job of every descriptor of a
valid job, top or class, from the answers of its children. -/
theorem body_able (n0 : ℕ) (htr : ∀ l, E.rank l = E.mx) (m : Bool) (cl : Paint) :
    Able m (E.engBank n0 cl) ((enginePort cl).1) (a (a (Ty.c cl)))
      (fun D => E.jobEnc cl D.1.job) (fun D => E.jobRes cl D.1.job) (fun D => E.locD n0 D.1.job)
      (fun D => ((E.childSet n0 D.1.job).map D.1.price).sum) := by
  refine Able.branch (n := fun D => (E.jobEnc cl D.1.job).1.1) Can.first.fst.anyCost
    (fun D => (E.jobEnc cl D.1.job).1.1 = 0) (fun _ => Iff.rfl) ?_ ?_
  · have hk := fun D : {D : {D : Desc (E.jobEnc cl) (E.jobRes cl) (E.childSet n0) // E.Valid D.job} //
        (E.jobEnc cl D.1.job).1.1 = 0} => E.top_facts n0 cl D.1.1.job D.2
    have hb := E.top_able htr n0 (m := m) (b := (E.engBank n0 cl).comap Subtype.val)
      (n := fun D => jobBits D.1.1.job) (Bv := fun D => jobCount D.1.1.job) (v := fun D => jobTop D.1.1.job)
      ⟨1, fun D => (bnd_ge D.1.1.job).1⟩ (τ := fun D c => D.1.1.price c)
      fun D h1 h3 t ht => D.1.1.ok _ (Multiset.mem_coe.2 (by
        rw [(hk D).1, if_pos ⟨h1, h3⟩]; exact List.mem_map.2 ⟨t, List.mem_range.2 ht, rfl⟩))
    refine (hb.cong (fun D => congrArg _ (top_eta E cl _ D.2)) fun D => congrArg _ (top_eta E cl _ D.2)).weaken
      (Dom.of_le fun D => (hk D).2.ge) fun D => le_of_eq ?_
    rw [Multiset.map_coe, Multiset.sum_coe, (hk D).1]
    split_ifs
    · rw [List.map_map, list_sum_map_range]; rfl
    · rfl
  · have hk := fun D : {D : {D : Desc (E.jobEnc cl) (E.jobRes cl) (E.childSet n0) // E.Valid D.job} //
        ¬ (E.jobEnc cl D.1.job).1.1 = 0} => E.cls_facts n0 cl D.1.1.job D.2
    have hb := E.class_able (m := m) (b := (E.engBank n0 cl).comap Subtype.val)
      (n := fun D => jobBits D.1.1.job) (μ := fun D => jobClassDim D.1.1.job) (J := fun D => jobData D.1.1.job)
      ⟨1, fun D => (bnd_ge D.1.1.job).2.1⟩ (fun D => (hk D).2.2 D.1.2)
      (τ := fun D c => D.1.1.price c)
      fun D c hc => D.1.1.ok c (Multiset.mem_coe.2 (by rw [(hk D).1]; exact hc))
    refine (hb.cong (fun D => congrArg _ (cls_eta E cl _ D.2)) fun D => congrArg _ (cls_eta E cl _ D.2)).weaken
      (Dom.of_le fun D => (hk D).2.1.ge) fun D => le_of_eq ?_
    rw [Multiset.map_coe, Multiset.sum_coe, (hk D).1]
end SlotEngine
end
end RAM
namespace EngineCost
namespace Rule
variable (R : Rule)
open RAM
end Rule
end EngineCost
namespace RAM
open Binary Matrix Ty Finset GenMove
noncomputable section
namespace SlotEngine
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]
variable (E : SlotEngine α ρ σ)
/-- A uniform engine realises the rule: every target has size `mx`, every block rank `r`. -/
structure RealisesRule (R : EngineCost.Rule) : Prop where
  hm : R.m = E.mx
  hW : R.W = E.W
  hrk : E.prog.filterMap Move.rk? = List.replicate R.P R.r
  htr : ∀ l, E.rank l = E.mx
variable {E} {R : EngineCost.Rule}
lemma RealisesRule.topG_eq (H : E.RealisesRule R) (n : ℕ) : E.topG n = n / R.m := by
  rw [H.hm]; rfl
end SlotEngine
end
end RAM
namespace EngineRecursion
universe U V
section
end
end EngineRecursion
namespace RAM
open Binary Matrix Ty Finset GenMove
noncomputable section
namespace SlotEngine
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]
variable {E : SlotEngine α ρ σ} {R : EngineCost.Rule}
theorem clsLoc_le (E : SlotEngine α ρ σ) : ∃ C : ℕ, ∀ n, E.classCost n ≤ C * 2 ^ n :=
  ⟨3 * (E.prog.length + E.W + 1), fun n => by
    have : 2 * n + 2 ≤ 2 * 2 ^ n := by have := Nat.lt_two_pow_self (n := n); omega
    calc E.classCost n ≤ (E.prog.length + E.W + 1) * (3 * 2 ^ n) := Nat.mul_le_mul_left _ (by omega)
      _ = 3 * (E.prog.length + E.W + 1) * 2 ^ n := by ring⟩
/-- The class cost is dominated by the own work of the block form. -/
theorem class_dom (E : SlotEngine α ρ σ) (R : EngineCost.Rule) (n0 : ℕ) :
    ∃ C : ℕ, ∀ n μ, E.classCost n + 1 ≤ C * (R.jobLocalCost n0 (.block n μ) + 1) := by
  obtain ⟨C, hC⟩ := E.clsLoc_le
  exact ⟨C + 1, fun n μ => by
    show E.classCost n + 1 ≤ (C + 1) * (2 ^ n + 1)
    have h := hC n
    have e : (C + 1) * (2 ^ n + 1) = C * 2 ^ n + (C + 2 ^ n + 1) := by ring
    calc E.classCost n + 1 ≤ C * 2 ^ n + 1 := Nat.add_le_add_right h 1
      _ ≤ (C + 1) * (2 ^ n + 1) := by rw [e]; exact Nat.add_le_add_left (Nat.le_add_left 1 _) _⟩
omit [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] in
/-- The tail of a fitting script fits. -/
lemma fits_tail {mv : Move α ρ} {rippleUpTo : Script α ρ} {u : ℕ} (h : Script.Fits (mv :: rippleUpTo) u) : rippleUpTo.Fits u :=
  fun k hk => by
    obtain ⟨a, ha, h'⟩ := List.mem_filterMap.1 hk
    exact h k (List.mem_filterMap.2 ⟨a, List.mem_cons_of_mem _ ha, h'⟩)
variable (E) in
/-- The forms of the exit jobs of a script: one batch per block move, in order. -/
lemma leafKids_form {n μ : ℕ} (hf : E.mx * μ ≤ n) : ∀ rippleUpTo : Script α ρ, Script.Fits rippleUpTo E.LL.n →
    ∀ V : E.CState n μ, (E.leafKids hf V rippleUpTo).map EJob.form =
      (rippleUpTo.filterMap Move.rk?).map fun r => .batch (r * μ) (2 ^ (n - r * μ))
  | [], _, _ => rfl
  | mv :: rippleUpTo, hb, V => by
    have hb' : Script.Fits rippleUpTo E.LL.n := fits_tail hb
    rcases Move.rk_cases mv with h0 | ⟨l, r, z, ind, rfl⟩
    · rw [E.moveJobs_free h0, List.filterMap_cons_none h0, leafKids_form hf rippleUpTo hb']
    · have hr : r ≤ E.LL.n := (hb.kern List.mem_cons_self).2.le
      simp only [leafKids, moveKids, dif_pos hr, List.singleton_append, List.map_cons,
        List.filterMap_cons_some (show (Move.kern l r z ind).rk? = some r from rfl), leafKids_form hf rippleUpTo hb']
      rfl
theorem RealisesRule.kidsC_shape (H : E.RealisesRule R) (n0 n μ : ℕ) (J : ℕ → Bits n → ℂ)
    (hd : E.Valid (⟨true, n, μ, J⟩)) :
    (((E.childJobs (⟨true, n, μ, J⟩)).map EJob.form : List _) : Multiset _) = R.jobKids n0 (.block n μ) := by
  obtain ⟨-, h2⟩ := hd
  simp only [childJobs, dif_pos h2, EngineCost.Rule.jobKids]
  rw [E.leafKids_form h2 _ E.prog_bounded, H.hrk, List.map_replicate, Multiset.coe_replicate]
variable (E) in
/-- Children never have a larger bound than their valid parent. -/
lemma child_bound (n0 : ℕ) (d : EJob) (hd : E.Valid d) : ∀ c ∈ E.allChildJobs n0 d, jobBound c ≤ jobBound d := by
  rcases d with ⟨_ | _, n, μ, J⟩
  · intro c hc
    simp only [allChildJobs] at hc
    split_ifs at hc
    · obtain ⟨t, -, rfl⟩ := List.mem_map.1 hc
      show 2 * 2 ^ n ≤ (μ + 2) * 2 ^ n
      exact Nat.mul_le_mul_right _ (by omega)
    · cases hc
  · obtain ⟨hμ, hf⟩ := hd
    show ∀ c ∈ E.childJobs ⟨true, n, μ, J⟩, jobBound c ≤ 2 * 2 ^ n
    rw [childJobs, dif_pos hf]
    suffices ∀ rippleUpTo : Script α ρ, Script.Fits rippleUpTo E.LL.n → ∀ V : E.CState n μ, ∀ c ∈ E.leafKids hf V rippleUpTo,
        jobBound c ≤ 2 * 2 ^ n from this _ E.prog_bounded _
    intro rippleUpTo
    induction rippleUpTo with
    | nil => intro _ _ c hc; cases hc
    | cons mv rippleUpTo ih =>
      intro hb V c hc
      have hb' : Script.Fits rippleUpTo E.LL.n := fits_tail hb
      rcases Move.rk_cases mv with h0 | ⟨l, r, z, ind, rfl⟩
      · rw [E.moveJobs_free h0] at hc; exact ih hb' _ c hc
      · have hr := hb.kern List.mem_cons_self
        simp only [leafKids, moveKids, dif_pos hr.2.le, List.singleton_append, List.mem_cons] at hc
        rcases hc with rfl | hc
        · have h1 : r * μ + μ ≤ E.mx * μ := by
            have := Nat.mul_le_mul_right μ (Nat.succ_le_of_lt hr.2); rwa [Nat.succ_mul] at this
          have h3 : 2 ^ (r * μ + 1) ≤ 2 ^ n := Nat.pow_le_pow_right two_pos (by omega)
          show (2 ^ (n - r * μ) + 2) * 2 ^ (r * μ) ≤ 2 * 2 ^ n
          rw [Nat.add_mul, ← pow_add, Nat.sub_add_cancel (by omega), pow_succ] at *
          omega
        · exact ih hb' _ c hc
variable (E) in
/-- Every child of a valid job is valid and has no larger bound (cutoff at least `mx`). -/
lemma child_ok (n0 : ℕ) (hn0 : E.mx ≤ n0) (d : EJob) (hd : E.Valid d) (c : EJob) (hc : c ∈ E.allChildJobs n0 d) :
    E.Valid c ∧ jobBound c ≤ jobBound d := by
  refine ⟨?_, E.child_bound n0 d hd c hc⟩
  rcases d with ⟨_ | _, n, B, v⟩
  · simp only [allChildJobs] at hc
    split_ifs at hc with h
    · obtain ⟨t, -, rfl⟩ := List.mem_map.1 hc
      show 1 ≤ E.topG n ∧ E.mx * E.topG n ≤ n
      exact ⟨(Nat.one_le_div_iff (by have := E.three_le; show 0 < E.LL.n; omega)).2 (hn0.trans h.1), E.topLo_le n⟩
    · cases hc
  · exact E.kidsC_valid _ hd c hc
/-- For a realising engine, the forms of the children of any valid job are the sub-forms of its
form. -/
theorem RealisesRule.childForms (H : E.RealisesRule R) (n0 : ℕ) (d : EJob) (hd : E.Valid d) :
    (((E.allChildJobs n0 d).map EJob.form : List _) : Multiset _) = R.jobKids n0 d.form := by
  rcases d with ⟨_ | _, n, B, v⟩
  · show (((E.allChildJobs n0 ⟨false, n, B, v⟩).map EJob.form : List _) : Multiset _) = R.jobKids n0 (.batch n B)
    have hf : (EJob.form ∘ fun t : ℕ => (⟨true, n, E.topG n, fun j => v (t * E.W + j)⟩ : EJob)) =
        fun _ => .block n (n / R.m) := funext fun _ => by
      show EngineCost.JobForm.block n (E.topG n) = _
      rw [H.topG_eq]
    simp only [allChildJobs, EngineCost.Rule.jobKids, H.hW]
    by_cases h : n0 ≤ n ∧ E.W ≤ B
    · rw [if_pos h, if_pos h, List.map_map, hf, List.map_const', List.length_range, Multiset.coe_replicate]
    · rw [if_neg h, if_neg h]; rfl
  · exact H.kidsC_shape n0 n B v hd
end SlotEngine
end
end RAM
namespace RAM
open Binary Matrix Ty Finset GenMove
noncomputable section
universe U
namespace SlotEngine
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]
variable (E : SlotEngine α ρ σ)
variable {E} {R : EngineCost.Rule}
/-- For a realising engine, the local cost of every job is dominated by the own work of its form:
class jobs by `class_dom`, top jobs with the constant `6`. -/
theorem RealisesRule.loc_dom (H : E.RealisesRule R) (n0 : ℕ) :
    ∃ C : ℕ, ∀ d : EJob, E.locD n0 d + 1 ≤ C * (R.jobLocalCost n0 d.form + 1) := by
  obtain ⟨C1, hC1⟩ := class_dom E R n0
  refine ⟨C1 + 6, fun d => ?_⟩
  rcases d with ⟨_ | _, n, B, v⟩
  · show E.topCost n0 n B + 1 ≤ (C1 + 6) * (R.jobLocalCost n0 (.batch n B) + 1)
    have hX : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have hn : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
    have hu : 2 ^ n ≤ (n + 1) * 2 ^ n := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    have hmod : B % E.W ≤ B := Nat.mod_le _ _
    have hm1 := Nat.mul_le_mul_right ((n + 1) * 2 ^ n) hmod
    have hC := Nat.mul_le_mul_right (R.jobLocalCost n0 (.batch n B) + 1) (Nat.le_add_left 6 C1)
    simp only [topCost, EngineCost.Rule.jobLocalCost, H.hW] at hC ⊢
    by_cases h0 : n0 ≤ n
    · rw [if_pos h0, if_neg (Nat.not_lt.2 h0)] at *
      have e1 : (B + 1) * 1 * 2 ^ n = B * 2 ^ n + 2 ^ n := by ring
      have e3 : (B + 1) * 2 ^ n = B * 2 ^ n + 2 ^ n := by ring
      rw [e1] at hC; rw [e1, e3]
      generalize B % E.W * ((n + 1) * 2 ^ n) = S at hC ⊢
      generalize B * 2 ^ n = Y at hC ⊢
      generalize (C1 + 6) * (Y + 2 ^ n + S + 1) = K at hC ⊢
      omega
    · rw [if_neg h0, if_pos (Nat.lt_of_not_le h0)] at *
      have e1 : (B + 1) * (n + 1) * 2 ^ n = B * ((n + 1) * 2 ^ n) + (n + 1) * 2 ^ n := by ring
      have e2 : (B + 1) * ((n + 1) * 2 ^ n) = B * ((n + 1) * 2 ^ n) + (n + 1) * 2 ^ n := by ring
      have e3 : (B + 1) * 2 ^ n = B * 2 ^ n + 2 ^ n := by ring
      have h4 : B * 2 ^ n ≤ B * ((n + 1) * 2 ^ n) := Nat.mul_le_mul_left _ hu
      have h5 : n + 1 ≤ (n + 1) * 2 ^ n := Nat.le_mul_of_pos_right _ hX
      rw [e1] at hC ⊢
      rw [e2, e3]
      generalize B % E.W * ((n + 1) * 2 ^ n) = S at hC ⊢
      generalize B * ((n + 1) * 2 ^ n) = Z at hC h4 ⊢
      generalize (C1 + 6) * (Z + (n + 1) * 2 ^ n + S + 1) = K at hC ⊢
      generalize B * 2 ^ n = Y at h4 ⊢
      generalize (n + 1) * 2 ^ n = U at hC hu h5 ⊢
      omega
  · show E.classCost n + 1 ≤ (C1 + 6) * (R.jobLocalCost n0 (.block n B) + 1)
    exact (hC1 n B).trans (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
end SlotEngine
end
end RAM
namespace RAM
open Binary Matrix Ty Finset GenMove
noncomputable section
universe U
namespace SlotEngine
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]
variable (E : SlotEngine α ρ σ)
variable {E} {R : EngineCost.Rule}
/-- **Closing the engine recursion.** For a realising engine, a cutoff at least `mx` and a
per-vector budget `J` whose every step pays for itself, every valid job is answered from its
encoding, call-free, at the total cost of its form. -/
theorem RealisesRule.answers (H : E.RealisesRule R) (n0 : ℕ) (hn0 : E.mx ≤ n0) {J : ℕ → ℕ}
    (hpay : ∀ d : EngineCost.JobForm, R.jobLocalCost n0 d + 1 + ((R.jobKids n0 d).map (R.jobTotalCost n0 J)).sum ≤ R.jobTotalCost n0 J d)
    (m : Bool) (cl : Paint) {ι : Type U} (x : ι → EJob) (hx : ∀ i, E.Valid (x i)) :
    Can m (fun i => jobBound (x i)) ((enginePort cl).1) (a (a (Ty.c cl)))
      (fun i => E.jobEnc cl (x i)) (fun i => E.jobRes cl (x i)) fun i => R.jobTotalCost n0 J (x i).form := by
  obtain ⟨C, hC⟩ := H.loc_dom n0
  have hm : R.m ≤ n0 := H.hm ▸ hn0
  have fits : ∀ d, E.Valid d → R.Fits d.form := fun d hd => by
    rcases d with ⟨_ | _, n, μ, v⟩
    · trivial
    · exact ⟨hd.1, H.hm ▸ hd.2⟩
  have hbd : ∀ d : EJob, 2 * jobBits d + 2 ≤ (jobBound d + 2) ^ 1 := fun d => by
    have h1 : jobBits d + 1 ≤ 2 ^ jobBits d := Nat.lt_two_pow_self
    have h2 : 2 * 2 ^ jobBits d ≤ jobBound d := by
      rcases d with ⟨_ | _, n, B, v⟩
      · exact Nat.mul_le_mul_right _ (by omega)
      · exact le_rfl
    rw [pow_one]; omega
  have sm : Small (fun j : {j // E.Valid j} => jobBound j.1) fun j => 2 * jobBits j.1 + 2 :=
    ⟨1, fun j => hbd j.1⟩
  have hn : Knows m (fun j : {j // E.Valid j} => jobBound j.1) ((enginePort cl).1) (fun j => E.jobEnc cl j.1)
      fun j => jobBits j.1 := Can.first.snd.fst
  have fuel : Can m (fun j : {j // E.Valid j} => jobBound j.1) ((enginePort cl).1) w (fun j => E.jobEnc cl j.1)
      (fun j => 2 * jobBits j.1 + 2) (fun j => C * R.jobTotalCost n0 J j.1.form) :=
    (Can.wadd (Can.wmul (Can.wc 2) hn (sm.mono fun _ => Nat.le_add_right _ _)) (Can.wc 2) sm).anyCost
  have core := EngineRecursion.closed_of_body (m := m) (enc := E.jobEnc cl) (res := E.jobRes cl) (kids := E.childSet n0)
    E.Valid jobBound (E.locD n0) (fun d => d.form.weight) (fun d => 2 * jobBits d + 2)
    (fun d => C * R.jobTotalCost n0 J d.form) (E.body_able n0 H.htr m cl)
    (fun j hj c hc => by
      have hc' : c ∈ E.allChildJobs n0 j := Multiset.mem_coe.1 hc
      have hf : c.form ∈ R.jobKids n0 j.form := by
        rw [← H.childForms n0 j hj]; exact Multiset.mem_coe.2 (List.mem_map.2 ⟨c, hc', rfl⟩)
      exact ⟨(E.child_ok n0 hn0 j hj c hc').1, (R.jobKids_ok hm (fits j hj) hf).2, (E.child_ok n0 hn0 j hj c hc').2⟩)
    (fun j hj => by
      have e : ((E.childSet n0 j).map fun c => C * R.jobTotalCost n0 J c.form).sum =
          C * ((R.jobKids n0 j.form).map (R.jobTotalCost n0 J)).sum := by
        rw [← H.childForms n0 j hj, Multiset.map_coe, Multiset.sum_coe, Multiset.map_coe, Multiset.sum_coe,
          List.sum_map_mul_left, List.map_map]
        rfl
      rw [e]
      have h1 := hC j
      have h2 := Nat.mul_le_mul_left C (hpay j.form)
      have e2 : C * (R.jobLocalCost n0 j.form + 1 + ((R.jobKids n0 j.form).map (R.jobTotalCost n0 J)).sum) =
          C * (R.jobLocalCost n0 j.form + 1) + C * ((R.jobKids n0 j.form).map (R.jobTotalCost n0 J)).sum := Nat.mul_add _ _ _
      omega)
    fuel
    (fun j _ => by
      rcases j with ⟨_ | _, n, μ, v⟩
      · show 2 * n + 1 < 2 * n + 2; omega
      · show 2 * n < 2 * n + 2; omega)
    sm x hx
  exact core.weaken (dom_mul C fun _ => le_rfl)
/-- **The ripple engine.** An engine realising a rule whose call rate holds at `z1` ripples a
vector of `k` bits at cost `O(2^k ⌈(k+1)^z⌉)` for every `z ∈ (z1, 1]`: one top job of `W` copies. -/
theorem RealisesRule.ripple_engine (H : E.RealisesRule R) (n0 : ℕ) (hn0 : E.mx ≤ n0) {z1 z : ℝ}
    (hrate : (R.P : ℝ) * (R.r : ℝ) ^ z1 ≤ R.W * (R.m : ℝ) ^ z1) (hz1 : 0 ≤ z1) (hz : z1 < z) (hz' : z ≤ 1)
    (m : Bool) (cl : Paint) {ι : Type U} (k : ι → ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2 ^ k i) (simIn cl) (bundle cl) (fun i => givenBits cl (k i) (v i))
      (fun i => (bits (k i)).tape (ripple (k i) (v i))) fun i => 2 ^ k i * envelope z (k i) := by
  obtain ⟨N, C, hN, hJ⟩ := R.budget_exists hrate hz1 hz hz' (H.hm ▸ hn0 : R.m ≤ n0)
  have rackC : Can m (fun i => 2 ^ k i) (simIn cl) (a (a (Ty.c cl))) (fun i => givenBits cl (k i) (v i))
      (fun i => Tape.tab E.W fun _ => (bits (k i)).tape (v i)) (fun i => 0 + E.W + ∑ _j ∈ range E.W, 0) :=
    (Can.tab (uB := fun _ _ => 0) (Can.wc E.W)
      (Has.extE ((Can.second.snd : Has m (fun i => 2 ^ k i) (simIn cl) (a (Ty.c cl)) (fun i => givenBits cl (k i) (v i))
        fun i => (bits (k i)).tape (v i)).reindex During.i)) (Small.const _ _))
  have enc : Can m (fun i => 2 ^ k i) (simIn cl) ((enginePort cl).1) (fun i => givenBits cl (k i) (v i))
      (fun i => E.jobEnc cl (⟨false, k i, E.W, fun _ => v i⟩)) fun i => 0 + E.W + E.W * 0 :=
    ((((Can.wc 0).pair (Can.first.pair ((Can.wc 0).pair Can.second.fst))).pair rackC).congr
      fun i => rfl).mono fun i => by simp
  have main := (H.answers N (hn0.trans hN) hJ m cl (fun i => ⟨false, k i, E.W, fun _ => v i⟩)
    fun _ => trivial).ambient
    ((Small.const _ (E.W + 2)).mul (Small.self fun i => 2 ^ k i))
  have read : Has m (fun i => 2 ^ k i) (a (a (Ty.c cl))) (bundle cl) (fun i => E.jobRes cl (⟨false, k i, E.W, fun _ => v i⟩))
      fun i => (bits (k i)).tape (ripple (k i) (v i)) :=
    Can.pick (t := a (Ty.c cl)) (n := fun _ => E.W) (k := fun _ => 0) (fun i (_ : ℕ) => (bits (k i)).tape (ripple (k i) (v i)))
      Can.id (Can.wc 0) fun _ => E.slots_pos
  refine ((enc.pipe main).pipe (read.anyCost (V := fun _ => 0))).weaken (dom_mul (E.W + E.W * C + N + 2) fun i => ?_)
  have hg := envelope_positive z (k i)
  have hX := Nat.one_le_two_pow (n := k i)
  have hsp : E.W % R.W = 0 := by rw [H.hW, Nat.mod_self]
  show 0 + E.W + E.W * 0 + (E.W * (C * 2 ^ k i * envelope z (k i)) + E.W % R.W * ((k i + 1) * 2 ^ k i) +
    (N + 1) * 2 ^ k i + 1) + 0 ≤ (E.W + E.W * C + N + 2) * (2 ^ k i * envelope z (k i))
  rw [hsp, zero_mul, add_zero]
  have h1 : 1 ≤ 2 ^ k i * envelope z (k i) := Nat.mul_le_mul hX hg
  have h2 : 2 ^ k i ≤ 2 ^ k i * envelope z (k i) := Nat.le_mul_of_pos_right _ hg
  have h3 := Nat.mul_le_mul_left (N + 1) h2
  have h4 := Nat.mul_le_mul_left E.W h1
  have e : E.W * (C * 2 ^ k i * envelope z (k i)) = E.W * C * (2 ^ k i * envelope z (k i)) := by ring
  rw [e]
  nlinarith
end SlotEngine
end
end RAM

end OAI.PowerSaving

end
-- ===== end part 3 =====

section
end
