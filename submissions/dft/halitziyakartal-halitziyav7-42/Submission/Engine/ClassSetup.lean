--might be  containing modified Apache-2.0 codes pieces from one or several sources; notices and credits: Credits.lean
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Submission.Engine.Moves
import Submission.Algebra.DFTIdentities

namespace OAI

namespace PowerSaving.RAM
open Ty Finset Spectral
noncomputable section

namespace Bench
universe U V
variable {ι : Type U} {κ : Type V} {m : Bool} {b : Bench m ι}
  {n k S : ι→ℕ} {t : Ty}

lemma Nick.branch {x y : ι→ℕ} (h : b.Nick n) (g : b.Nick x) (j : b.Nick y) :
    b.Nick fun i => if n i=0 then x i else y i :=
  ⟨Moves.branch h.close g.close j.close, (g.small.add j.small).mono fun _ => by split <;> omega⟩
lemma tape_congr_sized {n : ℕ} {α : Type*} {f g : ℕ→α} (h : ∀ j<n,f j=g j) :
    Tape.tab n f=Tape.tab n g :=
  congrArg (Tape.mk n) (funext fun j => h j j.2)
lemma pick_all {n k : ι→ℕ} (x : ι→ℕ→T t)
    (h : b.Moves (fun _ => 0) (a t) fun i => Tape.tab (n i) (x i)) (g : b.Nick k) :
    b.Moves (fun _ => 0) t fun i => if k i<n i then x i (k i) else t.blank :=
  (Can.look h g.close).cy fun _ => by simp [Tape.look_tab]
def tablePow (z : ℂ) (k : ℕ) : T (a sc) :=
  Tape.tab (2^k) fun i => z^i

lemma geom_two (k : ℕ) : ∑ j ∈ range k, 2^(j+1) + 2 = 2*2^k := by
  induction k with
  | zero => simp
  | succ k ih => rw [sum_range_succ, pow_succ 2 k]; omega

lemma doublingTable {f : ι → ℕ → ℕ → T t} {E O : ι → T t → T t} (h : b.Nick k)
    (g : Small b.size fun i => 2^k i) (h0 : b.Moves (fun _ => 0) t fun i => f i 0 0)
    (hE : ∀ {κ : Type U} (q : Bench m κ) (p : κ → ι), q.Instant b p → ∀ y : κ → T t,
      q.Moves (fun _ => 0) t y → q.Moves (fun _ => 0) t fun x => E (p x) (y x))
    (hO : ∀ {κ : Type U} (q : Bench m κ) (p : κ → ι), q.Instant b p → ∀ y : κ → T t,
      q.Moves (fun _ => 0) t y → q.Moves (fun _ => 0) t fun x => O (p x) (y x))
    (hstep : ∀ i j r, f i (j+1) r = if r%2=0 then E i (f i j (r/2)) else O i (f i j (r/2))) :
    b.Moves (fun i => 2^k i) (a t) fun i => Tape.tab (2^k i) (f i (k i)) := by
  let Tb : ι → ℕ → Tape (T t) := fun i j => Tape.tab (2^j) (f i j)
  let c := b.climbs k (a t) Tb
  have tk := tokenNow (t := a t) b k Tb
  have init : b.Moves (fun _ => 0) (a t) fun i => Tb i 0 :=
    Moves.weaken (arrayNow (Nick.wc 1) (fun i _ => f i 0 0) (Moves.transfer h0 (Instant.scan b _)))
      (Dom.const _ 1) |>.congr fun i => tape_congr_sized fun j hj => by
        rw [Nat.lt_one_iff.1 hj]
  have gs : Small c.size fun d => 2^d.j := (g.reindex During.i).mono fun d => Nat.pow_le_pow_right (by norm_num) d.hj.le
  have hn : c.Nick fun d => 2^(d.j+1) :=
    (Nick.mul ⟨Moves.len tk gs, gs⟩ (Nick.wc 2)).congr fun d => (pow_succ _ _).symm
  have inst := (Instant.scan c fun d => 2^(d.j+1)).next (Instant.climbs (t := a t) b k Tb)
  have rj := chop hn
  have y := Moves.pick (fun e r => f e.i.i e.i.j r) (Moves.transfer tk (Instant.scan c _))
    (rj.div (Nick.wc 2)).close fun e => by
      have : e.j < 2^(e.i.j+1) := e.hj; show e.j / 2 < 2^e.i.j; rw [pow_succ] at this; omega
  have body : c.Moves (fun d => 2^(d.j+1)) (a t) fun d => Tb d.i (d.j+1) :=
    (arrayNow hn (fun d r => if r%2=0 then E d.i (f d.i d.j (r/2)) else O d.i (f d.i d.j (r/2))) (Moves.branch (rj.residue (Nick.wc 2)).close (hE _ _ inst _ y) (hO _ _ inst _ y))).congr
      fun d => congrArg _ (funext fun r => (hstep d.i d.j r).symm)
  refine Moves.weaken (repeatM (t := a t) (u := fun _ j => 2^(j+1)) h Tb init body) ⟨3, fun i => ?_⟩
  have h1 := geom_two (k i)
  have h2 : k i < 2^k i := Nat.lt_pow_self (by norm_num : 1 < 2) ..
  beta_reduce; omega
lemma pylon (h : b.Nick k)
    (g : Small b.size fun i => 2^k i) {z : ι→ℂ} (hz : b.Moves (fun _ => 0) sc z) :
    b.Moves (fun i => 2^k i) (a sc) fun i => tablePow (z i) (k i) := by
  unfold tablePow; exact doublingTable (f := fun i _ r => z i ^ r) (E := fun _ y => y*y) (O := fun i y => z i * (y*y)) h g
    (Moves.one.congr fun _ => (pow_zero _).symm)
    (fun _ _ _ _ hy => Moves.mul hy hy) (fun _ _ hp _ hy => Moves.mul (Moves.transfer hz hp) (Moves.mul hy hy))
    fun i _ r => by
      beta_reduce
      obtain ⟨q, rfl | rfl⟩ := Nat.even_or_odd' r
      · rw [if_pos (by omega), show 2*q/2 = q by omega]; ring
      · rw [if_neg (by omega), show (2*q+1)/2 = q by omega]; ring

lemma square_pow (_h : Small b.size fun i => 2^k i)
    {z : ι→ℂ} {u : ι→ℕ}
    (g : b.Moves (fun _ => 0) (a sc) fun i => tablePow (z i) (k i)) (hk : b.Nick n)
    (hn : ∀ i,0<n i ∧ n i≤2^k i) (hz : ∀ i, z i^n i=1) (hu : b.Nick u) :
    b.Moves (fun _ => 0) sc fun i => chirp (z i) (u i) :=
  (Moves.pick (fun i r => z i ^ r) g ((hu.mul hu).residue hk).close fun i =>
    (Nat.mod_lt _ (hn i).1).trans_le (hn i).2).congr fun i => power_mod (hz i) _

end Bench
end
end PowerSaving.RAM

end OAI

namespace OAI
namespace PowerSaving
namespace LumTable
noncomputable section
open RAM RAM.Ty RAM.Bench Binary Matrix Finset Complex
universe U

lemma tape_loc {α : Type*} {μ : Type*} (L : Layout α) (f : ℕ → μ) :
    L.tape (fun x => f (L.loc x)) = Tape.tab L.n f := by
  simp only [Layout.tape, Tape.tab, Layout.loc_atFin]

def wt (e o : ℂ) : ℕ → ℕ → ℂ
  | 0, _ => 1
  | j+1, r => (if r % 2 = 0 then e else o) * wt e o j (r/2)

lemma wt_eq (e o : ℂ) : ∀ j r, wt e o j r = ∏ l ∈ range j, (if r / 2^l % 2 = 0 then e else o)
  | 0, r => by simp [wt]
  | j+1, r => by
    rw [wt, wt_eq e o j, prod_range_succ', pow_zero, Nat.div_one, mul_comm]
    congr 1
    refine prod_congr rfl fun l _ => ?_
    rw [Nat.div_div_eq_div_mul, pow_succ']

lemma wt_loc (e o : ℂ) (k : ℕ) (y : Bits k) :
    wt e o k ((bits k).loc y) = ∏ i, (if y i = 0 then e else o) := by
  rw [wt_eq, ← Fin.prod_univ_eq_prod_range]
  refine prod_congr rfl fun i _ => ?_
  simp only [bits_div, ZMod.val_eq_zero]

lemma lum_scaled (k : ℕ) (y : Bits k) :
    (1 - I)^k * lum y = ∏ j, if y j = 0 then 1 - I else 1 + I := by
  rw [← Fin.prod_const, lum, ← prod_mul_distrib]
  refine prod_congr rfl fun j _ => ?_
  unfold tint; split_ifs
  · exact mul_one _
  · rw [sub_mul, one_mul, I_mul_I]; ring

section Programs
variable {ι : Type U} {m : Bool}

lemma weight_table {s : Ty} {B : ι → ℕ} {x : ι → T s} {k : ι → ℕ} {e o : ι → ℂ}
    (hk : Knows m B s x k) (hks : Small B k) (hp : Small B fun i => 2^k i)
    (he : Has m B s sc x e) (ho : Has m B s sc x o) :
    Can m B s (a sc) x (fun i => (bits (k i)).tape (fun y => ∏ j, if y j = 0 then e i else o i))
      (fun i => 2^k i) := by
  have he' : (⟨B, s, x⟩ : Bench m ι).Moves (fun _ => 0) sc e := he
  have ho' : (⟨B, s, x⟩ : Bench m ι).Moves (fun _ => 0) sc o := ho
  have hd : Can m B s (a sc) x (fun i => Tape.tab (2^k i) (wt (e i) (o i) (k i))) (fun i => 2^k i) :=
    Bench.doublingTable (b := ⟨B, s, x⟩) (t := sc) (f := fun i => wt (e i) (o i))
      (E := fun i z => e i * z) (O := fun i z => o i * z) ⟨hk, hks⟩ hp Can.one
      (fun q _ hq _ hy => (Bench.Moves.transfer he' hq).mul hy)
      (fun q _ hq _ hy => (Bench.Moves.transfer ho' hq).mul hy)
      (fun i j r => by simp only [wt, ite_mul])
  refine hd.cong (fun _ => rfl) fun i => ?_
  rw [← bits_len, ← tape_loc]
  congr 1; funext y; exact wt_loc _ _ _ y

lemma lum_tables {s : Ty} {B : ι → ℕ} {x : ι → T s} {k : ι → ℕ} (hk : Knows m B s x k)
    (hks : Small B k) (hp : Small B fun i => 2^k i) (hI : Has m B s sc x (fun _ => I)) :
    Can m B s (a sc) x (fun i => (bits (k i)).tape (fun y => lum y)) (fun i => 2^k i) ∧
    Can m B s (a sc) x (fun i => (bits (k i)).tape (fun y => (1 - I)^k i * lum y)) (fun i => 2^k i) :=
  ⟨(weight_table hk hks hp Can.one hI).cong (fun _ => rfl) fun _ => rfl,
    (weight_table hk hks hp (Can.one.sub hI) (Can.one.add hI)).cong (fun _ => rfl)
      fun i => by simp only [lum_scaled]⟩
end Programs
end
end LumTable
end PowerSaving
end OAI

namespace OAI
namespace PowerSaving.RAM
open Ty Binary
universe U V

abbrev Lifts {ι : Type U} (m : Bool) (B : ι → ℕ) (s : Ty) (x : ι → T s) (s' : Ty) (x' : ι → T s') : Prop :=
  ∀ {u : Ty} {z : ι → T u}, Has m B s u x z → Has m B s' u x' z

section
variable {ι : Type U} {κ : Type V} {m : Bool} {B : ι → ℕ} {s t q : Ty} {x : ι → T s}

theorem Has.atW {y : ι → T t} {W : ι → ℕ} (h : Has m B s t x y) : Can m B s t x y W :=
  h.mono fun _ => Nat.zero_le _

theorem Has.extE {v : ι → T (p s t)} {z : ι → T q} {W : ι → ℕ}
    (h : Can m B s q (fun i => (v i).1) z W) : Can m B (p s t) q v z W :=
  Can.first.then_do h

theorem Has.liftE {e : κ → T t} {z : ι → T q} {W : ι → ℕ} (f : κ → ι) (h : Can m B s q x z W) :
    Can m (fun k => B (f k)) (p s t) q (fun k => (x (f k), e k)) (fun k => z (f k)) (fun k => W (f k)) :=
  Has.extE (h.reindex f)

theorem Can.table {N P : ι → ℕ} (g : ∀ i, Fin (N i) → T t) (hN : Knows m B s x N) (hNs : Small B N) (hg : Can m (fun u : Σ i, Fin (N i) => B u.1) (p s w) t (fun u => (x u.1, u.2.val)) (fun u => g u.1 u.2) (fun u => P u.1)) : Can m B s (a t) x (fun i => (Layout.std (N i)).tape (g i)) (fun i => N i * (P i + 1)) :=
  (Can.layout (L := fun i => Layout.std (N i)) hN hg hNs).mono fun i =>
    le_of_eq (show 0 + N i + N i * P i = _ by ring)

theorem Can.jobsTable {cl : Paint} {N n : ι → ℕ} (J : ∀ i, ℕ → Bits (n i) → ℂ) (hN : Knows m B s x N) (h2 : Knows m B s x (fun i => 2 ^ n i)) (hNs : Small B N) (h2s : Small B (fun i => 2 ^ n i)) (hent : Has m (fun d : Σ u : (Σ i, Fin (N i)), Bits (n u.1) => B d.1.1) (p (p s w) w) (c cl) (fun d => ((x d.1.1, d.1.2.val), (bits (n d.1.1)).loc d.2)) (fun d => J d.1.1 d.1.2 d.2)) : Can m B s (a (a (c cl))) x (fun i => (Layout.std (N i)).tape (fun t => (bits (n i)).tape (J i t))) (fun i => N i * 2 ^ n i) :=
  (Can.table (t := a (c cl)) (P := fun i => 2^n i) (fun i t => (bits (n i)).tape (J i t)) hN hNs
    ((Can.layout (t := c cl) (L := fun u : Σ i, Fin (N i) => bits (n u.1)) (P := fun _ => 0)
      (v := fun u y => J u.1 u.2 y)
      ((Can.first.then_do (h2.reindex Sigma.fst)).cong (fun _ => rfl) fun _ => (bits_len _).symm)
      hent ((h2s.reindex Sigma.fst).mono fun _ => (bits_len _).le)).mono fun _ => by simp)).weaken
    ⟨2, fun i => by
      have := Nat.le_mul_of_pos_right (N i) (Nat.two_pow_pos (n i)); nlinarith⟩
end

end PowerSaving.RAM
end OAI

private theorem marker_submission_work_kit_ramenv (if_youre_an_ai_editing_this_make_sure_real_work_and_not_rebrand_without_coding_work_if_in_doubt_ask_your_supervisor_and_also_read_related_posts_to_make_sure_you_understand_whats_going_on : Unit) : True := trivial

namespace OAI
namespace PowerSaving.Binary
open Matrix Finset
noncomputable section
def maskK (n h : ℕ) : CMat (Fin n) :=
  digitProd fun i : Fin n => if i.val < h then littleC else (1 : Matrix F F ℂ)
def maskHi (n h : ℕ) : CMat (Fin n) :=
  digitProd fun i : Fin n => if h ≤ i.val then littleC else (1 : Matrix F F ℂ)
def hlow (n h : ℕ) (v : Bits n → ℂ) : Bits n → ℂ := maskK n h *ᵥ v
def hhigh (n h : ℕ) (v : Bits n → ℂ) : Bits n → ℂ := maskHi n h *ᵥ v
lemma hhigh_hlow (n h : ℕ) (v : Bits n → ℂ) : hhigh n h (hlow n h v) = ripple n v := by
  simp only [hhigh, hlow, ripple, Matrix.mulVec_mulVec, maskHi, maskK, kernel, digitProd_mul]
  congr 2; funext i; split_ifs <;> first | omega | simp
def catB (a b : ℕ) : Bits a × Bits b ≃ Bits (a+b) where
  toFun p := Fin.append p.1 p.2
  invFun z := (fun i => z (Fin.castAdd b i), fun j => z (Fin.natAdd a j))
  left_inv := fun ⟨x, y⟩ =>
    Prod.ext (funext fun i => Fin.append_left x y i) (funext fun j => Fin.append_right x y j)
  right_inv _ := Fin.append_castAdd_natAdd
lemma catB_loc (a b : ℕ) (p : Bits a × Bits b) :
    (bits (a+b)).loc (catB a b p) = (bits a).loc p.1 + 2^a * (bits b).loc p.2 := by
  simp only [catB, Equiv.coe_fn_mk, bits_loc, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
    Fin.coe_castAdd, Fin.coe_natAdd, pow_add, Finset.mul_sum]
  congr 1; exact Finset.sum_congr rfl fun j _ => by ring
def castB {a b : ℕ} (h : a = b) : Bits a ≃ Bits b := Layout.permFn (finCongr h) F
lemma castB_loc {a b : ℕ} (h : a = b) (x : Bits a) : (bits b).loc (castB h x) = (bits a).loc x := by
  subst h; rfl
lemma maskK_cat (a b : ℕ) (x x' : Bits a) (q q' : Bits b) :
    maskK (a+b) a (catB a b (x, q)) (catB a b (x', q')) =
      kernel (Fin a) x x' * (if q = q' then 1 else 0) := by
  simp only [maskK, kernel, digitProd_apply, Fin.prod_univ_add, catB, Equiv.coe_fn_mk,
    Fin.append_left, Fin.append_right, Fin.coe_castAdd, Fin.is_lt, if_true]
  congr 1
  rw [← prod_delta]
  exact Finset.prod_congr rfl fun j _ => by simp [Matrix.one_apply]
lemma maskHi_cat (a b : ℕ) (x x' : Bits a) (q q' : Bits b) :
    maskHi (a+b) a (catB a b (x, q)) (catB a b (x', q')) =
      (if x = x' then 1 else 0) * kernel (Fin b) q q' := by
  simp only [maskHi, kernel, digitProd_apply, Fin.prod_univ_add, catB, Equiv.coe_fn_mk,
    Fin.append_left, Fin.append_right, Fin.coe_natAdd, Nat.le_add_right, if_true]
  congr 1
  rw [← prod_delta]
  exact Finset.prod_congr rfl fun i _ => by simp [Matrix.one_apply, not_le.2 i.isLt]
lemma hlow_catB (a b : ℕ) (w : Bits (a+b) → ℂ) (x : Bits a) (q : Bits b) :
    hlow (a+b) a w (catB a b (x, q)) = ripple a (fun x' => w (catB a b (x', q))) x := by
  rw [hlow, ripple, GenMove.mulVec_apply', GenMove.mulVec_apply', ← (catB a b).sum_comp,
    Fintype.sum_prod_type]
  simp only [maskK_cat, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
lemma hhigh_catB (a b : ℕ) (w : Bits (a+b) → ℂ) (x : Bits a) (y : Bits b) :
    hhigh (a+b) a w (catB a b (x, y)) = ripple b (fun y' => w (catB a b (x, y'))) y := by
  rw [hhigh, ripple, GenMove.mulVec_apply', GenMove.mulVec_apply', ← (catB a b).sum_comp,
    Fintype.sum_prod_type, Finset.sum_comm]
  simp only [maskHi_cat, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
lemma hlow_cast_cat (K B n : ℕ) (hc : K + B = n) (w : Bits n → ℂ) (u : Bits K) (t : Bits B) :
    hlow n K w (castB hc (catB K B (u, t))) = ripple K (fun u' => w (castB hc (catB K B (u', t)))) u := by
  subst hc; exact hlow_catB K B w u t
section
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {k : ℕ}
def pinS (S : Split α β (Fin k)) (X' : Layout β) (f : ℕ) : Sky α f ≃ Bits (k*f + X'.n*f) :=
  (Equiv.uniqueProd (Sky α f) (Bits 0)).symm.trans <|
    (S.peel 0 f).trans <|
      (Equiv.prodCongr (serial X' 0 f (Nat.add_zero _)) (Equiv.refl _)).trans <|
        (Equiv.prodComm _ _).trans (catB (k*f) (X'.n*f))
def placeS (S : Split α β (Fin k)) (X' : Layout β) (f r n : ℕ) (h : k*f + X'.n*f + r = n) :
    Bits r × Sky α f ≃ Bits n :=
  (Equiv.prodComm _ _).trans <| (Equiv.prodCongr (pinS S X' f) (Equiv.refl _)).trans <|
    (catB (k*f + X'.n*f) r).trans (castB h)
lemma placeS_loc (S : Split α β (Fin k)) (X' : Layout β) (f r n : ℕ) (h : k*f + X'.n*f + r = n)
    (q : Bits r) (y : Sky α f) :
    (bits n).loc (placeS S X' f r n h (q, y)) =
      (bits (k*f)).loc (S.peel 0 f (0, y)).2 + 2^(k*f) * (book X' 0 f).loc (S.peel 0 f (0, y)).1 +
        2^(k*f + X'.n*f) * (bits r).loc q := by
  have h0 : (Equiv.uniqueProd (Sky α f) (Bits 0)).symm y = (0, y) :=
    Prod.ext (Subsingleton.elim _ _) (by simp)
  simp only [placeS, pinS, Equiv.trans_apply, Equiv.prodComm_apply, Equiv.prodCongr_apply,
    Prod.map_fst, Prod.map_snd, Prod.fst_swap, Prod.snd_swap, Prod.swap_prod_mk,
    Equiv.refl_apply, castB_loc, catB_loc, h0, serial_code]
lemma placeS_eq (S : Split α β (Fin k)) (X' : Layout β) (f r n : ℕ)
    (h : k*f + X'.n*f + r = n) (q : Bits r) (y : Sky α f) :
    placeS S X' f r n h (q, y) = castB ((Nat.add_assoc _ _ _).symm.trans h)
      (catB (k*f) (X'.n*f + r) (flat k f (S.sky f y).2,
        catB (X'.n*f) r (serial X' 0 f (Nat.add_zero _) (0, (S.sky f y).1), q))) := by
  apply (bits n).inj
  simp only [placeS_loc, castB_loc, catB_loc, serial_code, Split.peel, Equiv.coe_fn_mk]
  ring
theorem hlow_placeS (S : Split α β (Fin k)) (X' : Layout β) (f r n : ℕ) (h : k*f + X'.n*f + r = n)
    (w : Bits n → ℂ) (q : Bits r) (y : Sky α f) :
    hlow n (k*f) w (placeS S X' f r n h (q, y)) =
      matAct f (S.lift (kernel (Fin k))) (fun y' => w (placeS S X' f r n h (q, y'))) y := by
  rw [placeS_eq, hlow_cast_cat, ripple, matAct, GenMove.mulVec_apply', GenMove.mulVec_apply']
  symm
  refine (Fintype.sum_equiv ((S.sky f).trans ((Equiv.refl _).prodCongr (flat k f))) _
    (fun p => if (S.sky f y).1 = p.1 then kernel (Fin (k*f)) (flat k f (S.sky f y).2) p.2 *
      w (castB ((Nat.add_assoc _ _ _).symm.trans h) (catB (k*f) (X'.n*f + r)
        (p.2, catB (X'.n*f) r (serial X' 0 f (Nat.add_zero _) (0, p.1), q)))) else 0)
    ?_).trans ?_
  · intro y'
    beta_reduce
    rw [Split.product, placeS_eq]
    simp only [Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd,
      Equiv.refl_apply, ite_mul, zero_mul]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
end
end
end PowerSaving.Binary
end OAI
namespace OAI.PowerSaving.UnitClass
open Finset
section Iter
variable (W : ℕ) (tq : ℕ → ℕ)
def stepC (x : ℕ × ℕ) : ℕ × ℕ := (x.1 * tq (x.2 % W), x.2 / W)
def colS (h s : ℕ) : ℕ := ((stepC W tq)^[h] (1, s)).1
lemma fst_iter (h : ℕ) : ∀ c s, ((stepC W tq)^[h] (c, s)).1 = c * ((stepC W tq)^[h] (1, s)).1 := by
  induction h with
  | zero => intro c s; simp
  | succ h ih =>
    intro c s
    simp only [Function.iterate_succ_apply, stepC]
    rw [ih (c * tq (s % W)) (s / W), ih (1 * tq (s % W)) (s / W)]; ring
@[simp] lemma colS_zero (s : ℕ) : colS W tq 0 s = 1 := rfl
lemma colS_succ (h s : ℕ) : colS W tq (h+1) s = tq (s % W) * colS W tq h (s / W) := by
  simp only [colS, Function.iterate_succ_apply, stepC]
  rw [fst_iter W tq h (1 * tq (s % W)) (s / W), one_mul]
lemma colS_cons (h a τ : ℕ) (ha : a < W) : colS W tq (h+1) (a + W * τ) = tq a * colS W tq h τ := by
  rw [colS_succ, DigitArith.mod_join' ha, DigitArith.div_join' ha]
lemma lt_of_cons (h a τ : ℕ) (ha : a < W) (hτ : τ < W^h) : a + W * τ < W^(h+1) := by
  have := DigitArith.lt_join hτ ha; rw [pow_succ]; linarith
end Iter
section Count
variable {p : ℕ → Prop} [DecidablePred p]
lemma count_lt_of_mem {N s : ℕ} (hs : p s) (hsN : s < N) : Nat.count p s < Nat.count p N :=
  Nat.count_strict_mono hs hsN
lemma nth_spec {N k : ℕ} (hk : k < Nat.count p N) :
    p (Nat.nth p k) ∧ Nat.nth p k < N ∧ Nat.count p (Nat.nth p k) = k := by
  have hf : ∀ hf : (setOf p).Finite, k < hf.toFinset.card :=
    fun hf => lt_of_lt_of_le hk (Nat.count_le_card hf N)
  exact ⟨Nat.nth_mem k hf, Nat.nth_lt_of_lt_count hk, Nat.count_nth hf⟩
end Count
section Class
variable (W : ℕ) (tq : ℕ → ℕ) (mx : ℕ)
def inRS (n h ρ s : ℕ) : Prop := s < W^h ∧ mx * (ρ * colS W tq h s) ≤ n
instance (n h ρ : ℕ) : DecidablePred (inRS W tq mx n h ρ) := fun s => by
  unfold inRS; infer_instance
def PC (n h ρ t : ℕ) : ℕ := Nat.count (inRS W tq mx n h ρ) t
def NU (n h ρ : ℕ) : ℕ := PC W tq mx n h ρ (W^h)
noncomputable def U (n h ρ p : ℕ) : ℕ := Nat.nth (inRS W tq mx n h ρ) p
noncomputable def cU (n h ρ p : ℕ) : ℕ := ρ * colS W tq h (U W tq mx n h ρ p)
noncomputable def iU (n h ρ p : ℕ) : ℕ :=
  n - mx * cU W tq mx n h ρ p
variable {W tq mx}
lemma PC_lt {n h ρ s : ℕ} (hs : inRS W tq mx n h ρ s) : PC W tq mx n h ρ s < NU W tq mx n h ρ :=
  count_lt_of_mem hs hs.1
lemma U_PC {n h ρ s : ℕ} (hs : inRS W tq mx n h ρ s) : U W tq mx n h ρ (PC W tq mx n h ρ s) = s :=
  Nat.nth_count hs
lemma NU_le (n h ρ : ℕ) : NU W tq mx n h ρ ≤ W^h := Nat.count_le _
lemma U_spec {n h ρ p : ℕ} (hp : p < NU W tq mx n h ρ) :
    inRS W tq mx n h ρ (U W tq mx n h ρ p) ∧ U W tq mx n h ρ p < W^h ∧
      PC W tq mx n h ρ (U W tq mx n h ρ p) = p := nth_spec hp
section
variable {n h ρ p : ℕ} (hp : p < NU W tq mx n h ρ)
include hp
lemma U_lt : U W tq mx n h ρ p < W^h := (U_spec hp).2.1
lemma U_fits : mx * cU W tq mx n h ρ p ≤ n := (U_spec hp).1.2
lemma PC_U : PC W tq mx n h ρ (U W tq mx n h ρ p) = p := (U_spec hp).2.2
end
end Class
end OAI.PowerSaving.UnitClass
namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset GenMove UnitClass
noncomputable section
universe U
abbrev UnitF {ι : Type U} (NU : ι → ℕ) := Σ i, Fin (NU i)
structure CCtx {ι : Type U} (m : Bool) (B : ι → ℕ) (s : Ty) (x : ι → T s) (mx : ℕ) (n NU : ι → ℕ)
    (col ib : ι → ℕ → ℕ) : Prop where
  (nK : Knows m B s x n) (p2n : Knows m B s x fun i => 2^(n i))
  (nuK : Knows m B s x NU)
  imag :
    Has m B s sc x fun _ => Complex.I
  tc : Has m B s (a w) x
    fun i => (Layout.std (NU i)).tape fun p => col i p
  tpc : Has m B s (a w) x
    fun i => (Layout.std (NU i)).tape fun p => 2^(col i p)
  (tib : Has m B s (a w) x fun i => (Layout.std (NU i)).tape fun p => ib i p)
  tpib :
    Has m B s (a w) x fun i => (Layout.std (NU i)).tape fun p => 2^(ib i p)
  txr : Has m B s (a (a w)) x
    fun i => (Layout.std (NU i)).tape fun p => xorTab (col i p)
  tlum : Has m B s (a (a sc)) x fun i =>
    (Layout.std (NU i)).tape fun p => (bits (col i p)).tape fun y : Bits (col i p) => lum y
  (big : Small B fun i => 2^(n i)) (nuS : Small B NU)
  fit :
    ∀ i (p : Fin (NU i)), mx * col i p + ib i p = n i
  mx1 : 1 ≤ mx
section
variable {α β ρ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype ρ] [DecidableEq ρ] {k : ℕ}
def blockJob (S : Split α β (Fin k)) (X' : Layout β) (f r n : ℕ)
    (h : k*f + X'.n*f + r = n) (l : ρ) (v : Bits r → Grain α ρ 0 f) : Bits n → ℂ :=
  fun e => v ((placeS S X' f r n h).symm e).1 (l, (0, ((placeS S X' f r n h).symm e).2))
lemma blockJob_placeS (S : Split α β (Fin k)) (X' : Layout β) (f r n : ℕ)
    (h : k*f + X'.n*f + r = n) (l : ρ) (v : Bits r → Grain α ρ 0 f) (q : Bits r) (y : Sky α f) :
    blockJob S X' f r n h l v (placeS S X' f r n h (q, y)) = v q (l, (0, y)) := by
  simp [blockJob]
omit [Fintype β] [DecidableEq β] in
lemma fitk {X : Layout α} (X' : Layout β) (hX' : X'.n + k = X.n) {f r n : ℕ}
    (hf : X.n * f + r = n) : k*f + X'.n*f + r = n := by
  rw [← hf, ← hX']; ring
def cjob (X : Layout α) (S : Split α β (Fin k)) (X' : Layout β) (hX' : X'.n + k = X.n) (l : ρ)
    {NU n : ℕ} {col ib : ℕ → ℕ} (hfit : ∀ p : Fin NU, X.n * col p + ib p = n)
    (V : ∀ p : Fin NU, Bits (ib p) → Grain α ρ 0 (col p)) (fl pp si : ℕ → ℕ)
    (hpp : ∀ t, fl t ≠ 0 → pp t < NU) (sup : ℕ → Bits n → ℂ) (t : ℕ) : Bits n → ℂ :=
  if hf : fl t ≠ 0 then
    blockJob S X' (col (pp t)) (ib (pp t)) n (fitk X' hX' (hfit ⟨pp t, hpp t hf⟩)) l (V ⟨pp t, hpp t hf⟩)
  else sup (si t)
abbrev jobsT (cl : Paint) : Ty := a (a (c cl))
abbrev portIn (cl : Paint) : Ty :=
  p w (p sc (p w (p w (p w (p (jobsT cl) (jobsT cl))))))
abbrev portOut (cl : Paint) : Ty := p (jobsT cl) (p (jobsT cl) (a w))
abbrev portM (cl : Paint) : Port := some (portIn cl, portOut cl)
def mkIn (cl : Paint) (n kind μ o : ℕ) (own sup : Tape (Tape ℂ)) : T (portIn cl) :=
  (n, Complex.I, kind, μ, o, own, sup)
def jobsTape (n N : ℕ) (J : ℕ → Bits n → ℂ) : Tape (Tape ℂ) :=
  (Layout.std N).tape fun t => (bits n).tape (J t)
lemma jobsTape_congr {n N : ℕ} {J J' : ℕ → Bits n → ℂ} (h : ∀ t, t < N → J t = J' t) :
    jobsTape n N J = jobsTape n N J' := by
  unfold jobsTape; congr 1; funext t; rw [h t t.isLt]
def bitsOf (b j : ℕ) : Bits b := (bits b).atFin ⟨j % 2^b, Nat.mod_lt _ (Nat.two_pow_pos b)⟩
lemma bitsOf_loc (b j : ℕ) : (bits b).loc (bitsOf b j) = j % 2^b := Layout.loc_atFin _ _
lemma bitsOf_of_loc (b : ℕ) (y : Bits b) : bitsOf b ((bits b).loc y) = y :=
  (bits b).inj (by rw [bitsOf_loc, Nat.mod_eq_of_lt (by simpa using (bits b).bd y)])
def toVec (n k : ℕ) (hk : k ≤ n) (J : ℕ → Bits n → ℂ) (t : ℕ) : Bits k → ℂ :=
  fun x => J (t / 2^(n-k)) (castB (Nat.add_sub_cancel' hk) (catB k (n-k) (x, bitsOf (n-k) t)))
lemma loc_castB_catB (n k : ℕ) (hk : k ≤ n) (x : Bits k) (y : Bits (n-k)) :
    (bits n).loc (castB (Nat.add_sub_cancel' hk) (catB k (n-k) (x, y))) =
      (bits k).loc x + 2^k * (bits (n-k)).loc y := by
  rw [castB_loc, catB_loc]
def fromVec (n k : ℕ) (hk : k ≤ n) (Y : ℕ → Bits k → ℂ) (j : ℕ) : Bits n → ℂ :=
  fun e => Y (j * 2^(n-k) + (bits (n-k)).loc ((catB k (n-k)).symm ((castB (Nat.add_sub_cancel' hk)).symm e)).2)
    ((catB k (n-k)).symm ((castB (Nat.add_sub_cancel' hk)).symm e)).1
lemma fromVec_ripple (n k : ℕ) (hk : k ≤ n) (J : ℕ → Bits n → ℂ) (j : ℕ) :
    fromVec n k hk (fun t => ripple k (toVec n k hk J t)) j = hlow n k (J j) := by
  funext e
  obtain ⟨⟨x, y⟩, rfl⟩ : ∃ p, castB (Nat.add_sub_cancel' hk) (catB k (n-k) p) = e :=
    ⟨(catB k (n-k)).symm ((castB (Nat.add_sub_cancel' hk)).symm e), by simp⟩
  have hy : (bits (n-k)).loc y < 2^(n-k) := by simpa using (bits (n-k)).bd y
  have h1 : (j * 2^(n-k) + (bits (n-k)).loc y) / 2^(n-k) = j := DigitArith.div_join hy
  have h2 : bitsOf (n-k) (j * 2^(n-k) + (bits (n-k)).loc y) = y :=
    (bits (n-k)).inj (by rw [bitsOf_loc, DigitArith.mod_join hy])
  rw [hlow_cast_cat]
  simp only [fromVec, Equiv.symm_apply_apply]; unfold toVec; simp only [h1, h2]
def exFl (N t : ℕ) : ℕ := if t < N then 1 else 0
lemma exFl_pp (N t : ℕ) (h : exFl N t ≠ 0) : t < N := by
  by_contra h'; simp [exFl, h'] at h
def exJobs (X : Layout α) (S : Split α β (Fin k)) (X' : Layout β) (hX' : X'.n + k = X.n) (l : ρ)
    {NU n : ℕ} {col ib : ℕ → ℕ} (hfit : ∀ p : Fin NU, X.n * col p + ib p = n)
    (V : ∀ p : Fin NU, Bits (ib p) → Grain α ρ 0 (col p)) : ℕ → Bits n → ℂ :=
  cjob X S X' hX' l hfit V (exFl NU) id (fun _ => 0) (exFl_pp NU) (fun _ _ => 0)
end
inductive EngJob
  | top (n B : ℕ) (v : ℕ → Bits n → ℂ)
  | cls (n h μ o BS : ℕ) (J sup : ℕ → Bits n → ℂ)
structure BlockEngine (α ρ σ : Type*) [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
    [Fintype σ] [DecidableEq σ] where
  (X : Layout α) (R : Layout ρ) (Q : Layout σ)
  (e : σ → ρ) (he : Function.Injective e)
  tr : σ → ℕ
  tz :
    ∀ l, Fin (tr l) → Space α
  (tind : ∀ l, LinearIndependent F (tz l))
  (tr_le : ∀ l, tr l ≤ X.n) (tr_pos : ∀ l, 1 ≤ tr l)
  wd : GWord α ρ
  (hP : wd.Proper X.n)
  sep :
    ∀ mv ∈ wd, ∀ r, mv.rk? = some r → ∀ l, r < tr l
  (W_pos : 0 < Q.n) (three : 3 ≤ X.n)
  hw : ∀ (f : ℕ) (v : Data α ρ f), (∀ s, (∀ l, e l ≠ s) → v s = 0) →
    ∀ l, gwalk f wd v (e l) = matAct f (blockMat (tz l)) (v (e l))
lemma dom_mul {ι : Type*} {W F : ι → ℕ} (K : ℕ) (h : ∀ i, F i ≤ K * W i) : Dom W F :=
  ⟨K + 1, fun i => by have := h i; nlinarith⟩
lemma lay_n {α : Type*} [Fintype α] (X : Layout α) {r : ℕ} (L : Layout (Fin (Fintype.card α - r)))
    (hr : r ≤ X.n) : L.n + r = X.n := by
  have h1 := L.card; have := X.card; rw [Fintype.card_fin] at h1; omega
namespace BlockEngine
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ] (E : BlockEngine α ρ σ)
abbrev W : ℕ := E.Q.n
def tq (a : ℕ) : ℕ :=
  if h : a < E.Q.n then E.tr (E.Q.atFin ⟨a, h⟩) else 0
abbrev mx : ℕ := E.X.n
abbrev NUc (n h μ : ℕ) : ℕ := UnitClass.NU E.W E.tq E.mx n h μ
abbrev Uc (n h μ p : ℕ) : ℕ := UnitClass.U E.W E.tq E.mx n h μ p
abbrev PCc (n h μ t : ℕ) : ℕ := UnitClass.PC E.W E.tq E.mx n h μ t
abbrev cUc (n h μ p : ℕ) : ℕ := UnitClass.cU E.W E.tq E.mx n h μ p
abbrev iUc (n h μ p : ℕ) : ℕ := UnitClass.iU E.W E.tq E.mx n h μ p
lemma fitc (n h μ : ℕ) (p : Fin (E.NUc n h μ)) : E.X.n * E.cUc n h μ p + E.iUc n h μ p = n :=
  Nat.add_sub_cancel' (UnitClass.U_fits p.2)
lemma tq_loc (l : σ) : E.tq (E.Q.loc l) = E.tr l := by
  rw [tq, dif_pos (E.Q.bd l)]
  congr 1; exact E.Q.inj (Layout.loc_atFin _ _)
def slotSize (n h μ t : ℕ) : ℕ := E.tq (t % E.W) * E.cUc n h μ (t / E.W)
abbrev CState (n h μ : ℕ) := ∀ p : Fin (E.NUc n h μ), Bits (E.iUc n h μ p) → Grain α ρ 0 (E.cUc n h μ p)
def St (l : σ) : Split α (Fin (Fintype.card α - E.tr l)) (Fin (E.tr l)) :=
  Classical.choose (exists_split (E.tz l) (E.tind l))
lemma St_spec (l : σ) (i : Fin (E.tr l)) : (E.St l).e.symm (0, eu i) = E.tz l i :=
  Classical.choose_spec (exists_split (E.tz l) (E.tind l)) i
def Xt (l : σ) : Layout (Fin (Fintype.card α - E.tr l)) := Layout.someLayout _
lemma Xt_n (l : σ) : (E.Xt l).n + E.tr l = E.X.n := lay_n _ _ (E.tr_le l)
def liveOf (l' : ρ) : Option σ := if h : ∃ s0, E.e s0 = l' then some (Classical.choose h) else none
lemma liveOf_e (l : σ) : E.liveOf (E.e l) = some l := by
  have h : ∃ s0, E.e s0 = E.e l := ⟨l, rfl⟩
  rw [liveOf, dif_pos h, E.he (Classical.choose_spec h)]
lemma liveOf_none (l' : ρ) (h : ∀ l, E.e l ≠ l') : E.liveOf l' = none := by
  rw [liveOf, dif_neg]; rintro ⟨s0, hs⟩; exact h s0 hs
def placeT (n h μ : ℕ) (p : Fin (E.NUc n h μ)) (l : σ) :
    Bits (E.iUc n h μ p) × Sky α (E.cUc n h μ p) ≃ Bits n :=
  placeS (E.St l) (E.Xt l) (E.cUc n h μ p) (E.iUc n h μ p) n
    (fitk (E.Xt l) (E.Xt_n l) (E.fitc n h μ p))
def V0 (n h μ : ℕ) (J : ℕ → Bits n → ℂ) : E.CState n h μ := fun p q x =>
  match E.liveOf x.1 with
  | some l => J (p.val * E.W + E.Q.loc l) (E.placeT n h μ p l (q, x.2.2))
  | none => 0
def stepV {n h μ : ℕ} (V : E.CState n h μ) (mv : GMove α ρ) : E.CState n h μ :=
  fun p q => gferry 0 (E.cUc n h μ p) mv (V p q)
def runV {n h μ : ℕ} (V : E.CState n h μ) (ws : GWord α ρ) : E.CState n h μ :=
  fun p q => gcoast 0 (E.cUc n h μ p) ws (V p q)
def parCode (n h μ r t : ℕ) : ℕ := t % E.W + E.W * E.Uc n h (μ * r) (t / E.W)
def fedP (n h μ r t : ℕ) : Prop :=
  t < E.NUc n h (μ*r) * E.W ∧ inRS E.W E.tq E.mx n (h+1) μ (E.parCode n h μ r t)
instance (n h μ r : ℕ) : DecidablePred (E.fedP n h μ r) := fun t => by unfold fedP; infer_instance
def srcP (n h μ r t : ℕ) : Prop :=
  t < E.NUc n h (μ*r) * E.W ∧ ¬ inRS E.W E.tq E.mx n (h+1) μ (E.parCode n h μ r t)
instance (n h μ r : ℕ) : DecidablePred (E.srcP n h μ r) := fun t => by unfold srcP; infer_instance
def flR (n h μ r t : ℕ) : ℕ := if E.fedP n h μ r t then 1 else 0
def ppR (n h μ r t : ℕ) : ℕ := E.PCc n (h+1) μ (E.parCode n h μ r t)
def siR (n h μ r o t : ℕ) : ℕ := o + Nat.count (E.srcP n h μ r) t
def slotR (n h μ r p : ℕ) : ℕ :=
  E.PCc n h (μ*r) (E.Uc n (h+1) μ p / E.W) * E.W + E.Uc n (h+1) μ p % E.W
lemma ppR_lt (n h μ r t : ℕ) (hf : E.flR n h μ r t ≠ 0) : E.ppR n h μ r t < E.NUc n (h+1) μ := by
  by_cases h' : E.fedP n h μ r t
  · exact UnitClass.PC_lt h'.2
  · simp [flR, h'] at hf
def blockRanks (ws : GWord α ρ) : List ℕ := ws.filterMap GMove.rk?
def ownSrc (n h μ r : ℕ) : List ℕ :=
  (List.range (E.NUc n h (μ*r) * E.W)).filterMap
    fun t => if E.srcP n h μ r t then some (E.slotSize n h (μ*r) t) else none
def srcSizes (n : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | h+1, μ => (blockRanks E.wd).flatMap fun r => E.ownSrc n h μ r ++ srcSizes n h (μ*r)
def cons (n h μ : ℕ) : ℕ := (E.srcSizes n h μ).length
def csz (n h μ k : ℕ) : ℕ := (E.srcSizes n h μ).getD k 0
def bS {r : ℕ} (z : Fin r → Space α) (ind : LinearIndependent F z) :
    Split α (Fin (Fintype.card α - r)) (Fin r) := Classical.choose (exists_split z ind)
lemma bS_spec {r : ℕ} (z : Fin r → Space α) (ind : LinearIndependent F z) (i : Fin r) :
    (bS z ind).e.symm (0, eu i) = z i :=
  Classical.choose_spec (exists_split z ind) i
def bX (r : ℕ) : Layout (Fin (Fintype.card α - r)) := Layout.someLayout _
lemma bX_n {r : ℕ} (hr : r ≤ E.X.n) : (bX (α:=α) r).n + r = E.X.n := lay_n _ _ hr
def childC (n h μ BS : ℕ) (sup : ℕ → Bits n → ℂ) (V : E.CState n (h+1) μ) (o : ℕ) (l : ρ) (r : ℕ)
    (z : Fin r → Space α) (ind : LinearIndependent F z) (hr : r ≤ E.X.n) : EngJob :=
  .cls n h (μ*r) (o + (E.ownSrc n h μ r).length) BS
    (cjob E.X (bS z ind) (bX r) (E.bX_n hr) l (E.fitc n (h+1) μ) V (E.flR n h μ r) (E.ppR n h μ r)
      (E.siR n h μ r o) (E.ppR_lt n h μ r) sup)
    sup
def exitC (n μ : ℕ) (V : E.CState n 0 μ) (l : ρ) (r : ℕ) (z : Fin r → Space α)
    (ind : LinearIndependent F z) (hr : r ≤ E.X.n) : EngJob :=
  if hk : r*μ ≤ n then
    .top (r*μ) (E.NUc n 0 μ * 2^(n - r*μ))
      (toVec n (r*μ) hk (exJobs E.X (bS z ind) (bX r) (E.bX_n hr) l (E.fitc n 0 μ) V))
  else .top 0 0 fun _ _ => 0
def kidsUp (n h μ BS : ℕ) (sup : ℕ → Bits n → ℂ) : E.CState n (h+1) μ → ℕ → GWord α ρ → List EngJob
  | _, _, [] => []
  | V, o, .old (.block l r z ind) :: ws =>
    (if hr : r ≤ E.X.n then [E.childC n h μ BS sup V o l r z ind hr] else []) ++
      kidsUp n h μ BS sup (E.stepV V (.old (.block l r z ind)))
        (o + (E.ownSrc n h μ r).length + E.cons n h (μ*r)) ws
  | V, o, mv :: ws => kidsUp n h μ BS sup (E.stepV V mv) o ws
def kidsLeaf (n μ : ℕ) : E.CState n 0 μ → GWord α ρ → List EngJob
  | _, [] => []
  | V, .old (.block l r z ind) :: ws =>
    (if hr : r ≤ E.X.n then [E.exitC n μ V l r z ind hr] else []) ++
      kidsLeaf n μ (E.stepV V (.old (.block l r z ind))) ws
  | V, mv :: ws => kidsLeaf n μ (E.stepV V mv) ws
def childJobs : EngJob → List EngJob
  | .top .. => []
  | .cls n 0 μ _ _ J _ => E.kidsLeaf n μ (E.V0 n 0 μ J) E.wd
  | .cls n (h+1) μ o BS J sup => E.kidsUp n h μ BS sup (E.V0 n (h+1) μ J) o E.wd
def encodeJob (cl : Paint) : EngJob → T (portIn cl)
  | .top n B v => mkIn cl n 0 0 0 (jobsTape n B v) (jobsTape n 0 fun _ _ => 0)
  | .cls n h μ o BS J sup =>
    mkIn cl n (h+1) μ o (jobsTape n (E.NUc n h μ * E.W) J) (jobsTape n BS sup)
def jobAnswer (cl : Paint) : EngJob → T (portOut cl)
  | .top n B v =>
    (jobsTape n B fun t => ripple n (v t), jobsTape n 0 (fun _ _ => 0), (Layout.std 0).tape fun _ => 0)
  | .cls n h μ o BS J sup =>
    (jobsTape n (E.NUc n h μ * E.W) (fun t => hlow n (E.slotSize n h μ t) (J t)),
      jobsTape n (E.cons n h μ) (fun k => hlow n (E.csz n h μ k) (sup (o + k))),
      (Layout.std (E.cons n h μ)).tape fun k => E.csz n h μ k)
end BlockEngine
lemma atU {ι : Type U} {m : Bool} {B : ι → ℕ} {s : Ty} {x : ι → T s} {NU : ι → ℕ} {t' : Ty}
    {z : ∀ i, Fin (NU i) → T t'} (hz : Has m B s (a t') x (fun i => (Layout.std (NU i)).tape (z i))) :
    Has m (fun u : UnitF NU => B u.1) (p s w) t' (fun u => (x u.1, u.2.val)) (fun u => z u.1 u.2) :=
  Can.fetch (L := fun u : UnitF NU => Layout.std (NU u.1)) (i := fun u => u.2)
    (Has.extE (hz.reindex Sigma.fst)) Can.second
section
universe V
variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] {ι : Type U} {m : Bool} {B : ι → ℕ} {s t : Ty} {x : ι → T s} {cl : Paint} {n N : ι → ℕ}
  {J : ∀ i, ℕ → Bits (n i) → ℂ} {tt : ι → ℕ} {e : ∀ i, Bits (n i)}
lemma has_tape0 (f : ι → Fin 0 → T t) : Has m B s (a t) x (fun i => (Layout.std 0).tape (f i)) :=
  (Can.table (P := fun _ => 0) f (Can.wc 0) (Small.const B 0)
    ⟨Code.blank _ _, 0, 0, fun u => u.2.elim0⟩).mono fun _ => by simp
lemma has_jobs0 (n : ι → ℕ) (J : ∀ i, ℕ → Bits (n i) → ℂ) :
    Has m B s (jobsT cl) x (fun i => jobsTape (n i) 0 (J i)) := has_tape0 _
lemma can_jobsTape (hN : Knows m B s x N) (h2 : Knows m B s x (fun i => 2^(n i)))
    (hNs : Small B N) (h2s : Small B (fun i => 2^(n i)))
    (hel : Has m (fun d : Σ u : UnitF N, Bits (n u.1) => B d.1.1) (p (p s w) w) (c cl)
      (fun d => ((x d.1.1, d.1.2.val), (bits (n d.1.1)).loc d.2)) (fun d => J d.1.1 d.1.2.val d.2)) :
    Can m B s (jobsT cl) x (fun i => jobsTape (n i) (N i) (J i)) (fun i => N i * (2^(n i) + 1)) :=
  (Can.jobsTable J hN h2 hNs h2s hel).mono fun i => Nat.mul_le_mul le_rfl (Nat.le_succ _)
section
variable (ht : Has m B s (jobsT cl) x (fun i => jobsTape (n i) (N i) (J i)))
    (hix : Knows m B s x tt) (hlt : ∀ i, tt i < N i)
include ht hix hlt
lemma has_jobsAt : Has m B s (a (c cl)) x (fun i => (bits (n i)).tape (J i (tt i))) :=
  Can.fetch (L := fun i => Layout.std (N i)) (i := fun d => ⟨tt d, hlt d⟩) ht hix
lemma has_jobsRead (he : Knows m B s x (fun i => (bits (n i)).loc (e i))) :
    Has m B s (c cl) x (fun i => J i (tt i) (e i)) := Can.fetch (has_jobsAt ht hix hlt) he
end
variable (X : Layout α) (R : Layout ρ)
lemma fleet_n (f : ℕ) : (fleet X R 0 f).n = R.n * 2^(X.n * f) := by simp [fleet]
def ctab (NU : ℕ) (c ib : ℕ → ℕ)
    (V : ∀ p : Fin NU, Bits (ib p) → Grain α ρ 0 (c p)) : Tape (Tape (Tape ℂ)) :=
  (Layout.std NU).tape (fun p => (bits (ib p)).tape (fun q => (fleet X R 0 (c p)).tape (V p q)))
abbrev InstF {ι : Type U} (NU : ι → ℕ) (ib : ι → ℕ → ℕ) := Σ u : UnitF NU, Bits (ib u.1 u.2)
lemma can_ctab {B : ι → ℕ} {s : Ty} {x : ι → T s}
    {NU : ι → ℕ} {col ib : ι → ℕ → ℕ}
    {V' : ∀ i, ∀ p : Fin (NU i), Bits (ib i p) → Grain α ρ 0 (col i p)}
    (hNU : Knows m B s x NU) (hNUs : Small B NU)
    (hib : Knows m (fun u : UnitF NU => B u.1) (p s w) (fun u => (x u.1, u.2.val))
      (fun u => 2^(ib u.1 u.2)))
    (hibs : Small (fun u : UnitF NU => B u.1) (fun u => 2^(ib u.1 u.2)))
    {P : ι → ℕ} (hP : ∀ u : UnitF NU, 2^(ib u.1 u.2) + 2^(ib u.1 u.2) * (R.n * 2^(X.n * col u.1 u.2)) ≤ P u.1)
    (hin : Can m (fun v : InstF NU ib => B v.1.1) (p (p s w) w) (a (c cl))
      (fun v => ((x v.1.1, v.1.2.val), (bits (ib v.1.1 v.1.2)).loc v.2))
      (fun v => (fleet X R 0 (col v.1.1 v.1.2)).tape (V' v.1.1 v.1.2 v.2))
      (fun v => R.n * 2^(X.n * col v.1.1 v.1.2))) :
    Can m B s (a (a (a (c cl)))) x (fun i => ctab X R (NU i) (col i) (ib i) (V' i))
      (fun i => NU i + NU i * P i) :=
  (Can.layout (L := fun i => Layout.std (NU i)) (P := P) hNU
    ((Can.layout (L := fun u : UnitF NU => bits (ib u.1 u.2)) hib hin hibs).mono
      fun u => by simpa using hP u) hNUs).mono fun i => by simp [Layout.std]
abbrev ctabT (cl : Paint) : Ty := a (a (a (c cl)))
variable {κ : Type V} {Bk : κ → ℕ} {sk : Ty} {y : κ → T sk}
    {NU : κ → ℕ} {col ib : κ → ℕ → ℕ}
    {V' : ∀ k, ∀ p : Fin (NU k), Bits (ib k p) → Grain α ρ 0 (col k p)}
    (pu : ∀ k, Fin (NU k)) (qu : ∀ k, Bits (ib k (pu k))) (bu : ∀ k, Beach α ρ 0 (col k (pu k)))
    (ht : Has m Bk sk (a (a (a (c cl)))) y (fun k => ctab X R (NU k) (col k) (ib k) (V' k)))
    (hp : Knows m Bk sk y (fun k => (pu k).val))
    (hq : Knows m Bk sk y (fun k => (bits (ib k (pu k))).loc (qu k)))
include ht hp hq
lemma has_ctabInst :
    Has m Bk sk (a (c cl)) y (fun k => (fleet X R 0 (col k (pu k))).tape (V' k (pu k) (qu k))) :=
  Can.fetch (L := fun k => bits (ib k (pu k))) (Can.fetch (L := fun k => Layout.std (NU k)) ht hp) hq
lemma has_ctabRead (hb : Knows m Bk sk y (fun k => (fleet X R 0 (col k (pu k))).loc (bu k))) :
    Has m Bk sk (c cl) y (fun k => V' k (pu k) (qu k) (bu k)) :=
  Can.fetch (has_ctabInst X R pu qu ht hp hq) hb
end
namespace CCtx
variable {ι : Type U} {m : Bool} {B : ι → ℕ} {s : Ty} {x : ι → T s} {mx : ℕ}
  {n NU : ι → ℕ} {col ib : ι → ℕ → ℕ}
variable (c : CCtx m B s x mx n NU col ib)
include c
lemma reindex {κ : Type U} (j : κ → ι) {t : Ty} (y : κ → T t)
    (g : Has m (fun k => B (j k)) t s y (fun k => x (j k))) :
    CCtx m (fun k => B (j k)) t y mx (fun k => n (j k)) (fun k => NU (j k))
      (fun k => col (j k)) (fun k => ib (j k)) :=
  have r {u} {z : ι → T u} (hz : Has m B s u x z) := g.then_do (hz.reindex j)
  ⟨r c.1, r c.2, r c.3, r c.4, r c.5, r c.6, r c.7, r c.8, r c.9, r c.10, c.11.reindex j,
    c.12.reindex j, fun k => c.13 (j k), c.14⟩
lemma ext {t : Ty} (y : ι → T t) :
    CCtx m B (p s t) (fun i => (x i, y i)) mx n NU col ib := c.reindex id _ Can.first
lemma pow_ib_le (i : ι) (p : Fin (NU i)) : 2^(ib i p) ≤ 2^(n i) :=
  Nat.pow_le_pow_right two_pos (by have := c.fit i p; omega)
lemma gearU : BitCtx m (fun u : UnitF NU => B u.1) (fun u => col u.1 u.2) (p s w) (fun u => (x u.1, u.2.val)) :=
  ⟨atU c.tpc, atU c.tc, atU c.txr, (c.big.reindex Sigma.fst).mono fun u =>
    Nat.pow_le_pow_right two_pos (by have := c.fit u.1 u.2; have := c.mx1; nlinarith)⟩
lemma lumU : Has m (fun u : UnitF NU => B u.1) (p s w) (a sc) (fun u => (x u.1, u.2.val))
    (fun u => (bits (col u.1 u.2)).tape (fun y : Bits (col u.1 u.2) => lum y)) := atU c.tlum
lemma p2ibU : Knows m (fun u : UnitF NU => B u.1) (p s w) (fun u => (x u.1, u.2.val))
    (fun u => 2^(ib u.1 u.2)) := atU c.tpib
lemma p2ibS : Small (fun u : UnitF NU => B u.1) (fun u => 2^(ib u.1 u.2)) :=
  (c.big.reindex Sigma.fst).mono fun u => c.pow_ib_le u.1 u.2
lemma unit_size {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
    (X : Layout α) (R : Layout ρ) (hX : X.n = mx) (i : ι) (p : Fin (NU i)) :
    2^(ib i p) * (fleet X R 0 (col i p)).n = R.n * 2^(n i) := by
  rw [fleet_n, hX, ← c.fit i p, pow_add]; ring
end CCtx
namespace GMove
variable {α ρ : Type*}
lemma rk_block (l : ρ) (r : ℕ) (z : Fin r → Space α) (ind : LinearIndependent F z) :
    (GMove.old (BMove.block l r z ind)).rk? = some r := rfl
lemma rk_cases (mv : GMove α ρ) :
    mv.rk? = none ∨ ∃ l r z ind, mv = GMove.old (BMove.block l r z ind) := by
  rcases mv with ((_|_|⟨l, r, z, ind⟩)|_|_|_)
  all_goals first | exact Or.inl rfl | exact Or.inr ⟨l, r, z, ind, rfl⟩
end GMove
end
end PowerSaving.RAM
end OAI
namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset GenMove UnitClass
noncomputable section
universe U
lemma nthc_step (P : ℕ → Prop) [DecidablePred P] (q j : ℕ) :
    (if (if Nat.count P j = q then 0 else 1) + (1 - if P j then 1 else 0) = 0 then j
      else if q < Nat.count P j then Nat.nth P q else 0) =
    if q < Nat.count P (j+1) then Nat.nth P q else 0 := by
  rw [Nat.count_succ]
  by_cases hp : P j <;> by_cases hc : Nat.count P j = q <;> simp [hp, hc] <;>
    first | rw [← hc, Nat.nth_count hp] | (split_ifs <;> first | rfl | omega)
section Loops
variable {ι : Type U} {m : Bool} {B : ι → ℕ} {s : Ty} {x : ι → T s}
lemma can_iter {t : Ty} {n Wt : ι → ℕ} {v : ι → ℕ → T t} (hn : Knows m B s x n) (hns : Small B n)
    (h0 : Has m B s t x (fun i => v i 0))
    (hs : Can m (fun d : During n => B d.i) (p s (p w t)) t (fun d => (x d.i, d.j, v d.i d.j))
      (fun d => v d.i (d.j + 1)) (fun d => Wt d.i)) :
    Can m B s t x (fun i => v i (n i)) (fun i => n i * (Wt i + 1) + 1) :=
  (Can.loop (uB := fun i _ => Wt i) hn h0 hs hns).mono fun i => by simp [Nat.mul_add]; omega
lemma can_count {P : ι → ℕ → Prop} [∀ i, DecidablePred (P i)] {T Wt : ι → ℕ}
    (hT : Knows m B s x T) (hTs : Small B T)
    (hind : Can m (fun d : During T => B d.i) (p s w) w (fun d => (x d.i, d.j))
      (fun d => if P d.i d.j then 1 else 0) (fun d => Wt d.i)) :
    Can m B s w x (fun i => Nat.count (P i) (T i)) (fun i => T i * (Wt i + 1) + 1) :=
  can_iter (v := fun i j => Nat.count (P i) j) hT hTs
    ((Can.wc 0).cong (fun _ => rfl) fun _ => (Nat.count_zero _).symm)
    ((Can.second.snd.wadd ((Can.first.pair Can.second.fst).then_do hind)
      ((hTs.reindex During.i).mono fun d => by
        have := Nat.count_le (p := P d.i) (n := d.j); have := d.hj; dsimp only; split_ifs <;> omega)).cong
      (fun _ => rfl) fun d => (Nat.count_succ _ _).symm)
lemma can_nthc {P : ι → ℕ → Prop} [∀ i, DecidablePred (P i)] {T Wt q : ι → ℕ}
    (hT : Knows m B s x T) (hTs : Small B T) (hq : Knows m B s x q)
    (hind : Can m (fun d : During T => B d.i) (p s w) w (fun d => (x d.i, d.j))
      (fun d => if P d.i d.j then 1 else 0) (fun d => Wt d.i)) :
    Can m B s w x (fun i => if q i < Nat.count (P i) (T i) then Nat.nth (P i) (q i) else 0)
      (fun i => T i * (Wt i + 1) + 1) := by
  have hi : Can m (fun d : During T => B d.i) (p s (p w (p w w))) w (fun d => (x d.i, d.j,
      (Nat.count (P d.i) d.j, if q d.i < Nat.count (P d.i) d.j then Nat.nth (P d.i) (q d.i) else 0)))
      (fun d => if P d.i d.j then 1 else 0) (fun d => Wt d.i) :=
    (Can.first.pair Can.second.fst).then_do hind
  exact (can_iter (t := p w w) (v := fun i j => (Nat.count (P i) j,
      if q i < Nat.count (P i) j then Nat.nth (P i) (q i) else 0)) hT hTs
    (((Can.wc 0).pair (Can.wc 0)).cong (fun _ => rfl) fun _ => by simp)
    (((Can.second.snd.fst.wadd hi ((hTs.reindex During.i).mono fun d => by
        have := Nat.count_le (p := P d.i) (n := d.j); have := d.hj; dsimp only; split_ifs <;> omega)).pair
      (can_ite ((Can.eqbit Can.second.snd.fst (Has.extE (Has.atW (hq.reindex During.i)))).wadd
        ((Can.wc 1).wsub hi (Small.const _ 1).sub) ((Small.const _ 2).mono fun _ => by
          dsimp only; split_ifs <;> omega)) Can.second.fst Can.second.snd.snd)).cong (fun _ => rfl)
      fun d => Prod.ext (Nat.count_succ _ _).symm (nthc_step _ _ _))).snd
lemma can_powv (W : ℕ) (hW : 0 < W) {h : ι → ℕ} (hh : Knows m B s x h) (hhs : Small B h)
    (hsm : Small B (fun i => W^(h i))) : Can m B s w x (fun i => W^(h i)) (fun i => h i + 1) :=
  (can_iter (v := fun _ j => W^j) (Wt := fun _ => 0) hh hhs
    ((Can.wc 1).cong (fun _ => rfl) fun i => (pow_zero W).symm)
    ((Can.second.snd.wmul (Can.wc W) ((hsm.reindex During.i).mono fun d =>
      (pow_succ W d.j).symm.le.trans (Nat.pow_le_pow_right hW d.hj))).cong (fun _ => rfl)
      fun d => (pow_succ W d.j).symm)).mono fun i => by simp
end Loops
structure CIn {ι : Type U} (m : Bool) (B : ι → ℕ) (s : Ty) (x : ι → T s) (n h μ : ι → ℕ) : Prop where
  (nK : Knows m B s x n) (hK : Knows m B s x h) (μK : Knows m B s x μ)
  p2n :
    Knows m B s x fun i => 2^(n i)
  (imag : Has m B s sc x fun _ => Complex.I)
  (big : Small B fun i => 2^(n i)) (hle : ∀ i, h i ≤ n i)
  μS : Small B μ
namespace CIn
variable {ι : Type U} {m : Bool} {B : ι → ℕ} {s : Ty} {x : ι → T s} {n h μ : ι → ℕ}
variable (c : CIn m B s x n h μ)
include c
lemma nS : Small B n := c.big.mono fun _ => Nat.lt_two_pow_self.le
lemma hS : Small B h := c.nS.mono c.hle
lemma powS (b : ℕ) : Small B (fun i => b^(h i)) :=
  (c.big.pow b).mono fun i => (Nat.pow_le_pow_left Nat.lt_two_pow_self.le _).trans
    ((pow_right_comm 2 b (h i)).le.trans (Nat.pow_le_pow_left (Nat.pow_le_pow_right two_pos (c.hle i)) _))
lemma ext {t : Ty} (y : ι → T t) : CIn m B (p s t) (fun i => (x i, y i)) n h μ :=
  ⟨Has.extE c.nK, Has.extE c.hK, Has.extE c.μK, Has.extE c.p2n, Has.extE c.imag, c.big, c.hle, c.μS⟩
lemma reindex {κ : Type U} (j : κ → ι) {t : Ty} (y : κ → T t)
    (g : Has m (fun k => B (j k)) t s y (fun k => x (j k))) :
    CIn m (fun k => B (j k)) t y (fun k => n (j k)) (fun k => h (j k)) (fun k => μ (j k)) :=
  ⟨g.then_do (c.nK.reindex j), g.then_do (c.hK.reindex j), g.then_do (c.μK.reindex j),
    g.then_do (c.p2n.reindex j), g.then_do (c.imag.reindex j), c.big.reindex j,
    fun k => c.hle (j k), c.μS.reindex j⟩
lemma onUnits (N : ι → ℕ) : CIn m (fun u : UnitF N => B u.1) (p s w) (fun u => (x u.1, u.2.val))
    (fun u => n u.1) (fun u => h u.1) (fun u => μ u.1) := c.reindex Sigma.fst _ Can.first
end CIn
namespace BlockEngine
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ] (E : BlockEngine α ρ σ) {ι : Type U} {m : Bool} {B : ι → ℕ} {s : Ty} {x : ι → T s}
lemma tq_le (a : ℕ) : E.tq a ≤ E.mx := by unfold tq; split_ifs; exacts [E.tr_le _, Nat.zero_le _]
lemma knows_tq {a : ι → ℕ} (ha : Knows m B s x a) (hlt : ∀ i, a i < E.W) : Knows m B s x (fun i => E.tq (a i)) :=
  Can.cases_code (q := fun i => (⟨a i, hlt i⟩ : Fin E.W)) (Layout.std E.W) ha fun f =>
    (Can.wc (E.tq f.val)).cong (fun _ => rfl) fun i => congrArg (fun g : Fin E.W => E.tq g.val) i.2.symm
lemma iter_bound (sv : ℕ) : ∀ j, ((stepC E.W E.tq)^[j] (1, sv)).1 ≤ E.mx^j ∧
    ((stepC E.W E.tq)^[j] (1, sv)).2 ≤ sv
  | 0 => by simp
  | j+1 => by
    rw [Function.iterate_succ_apply']
    exact ⟨(Nat.mul_le_mul (iter_bound sv j).1 (E.tq_le _)).trans (pow_succ _ _).ge,
      (Nat.div_le_self _ _).trans (iter_bound sv j).2⟩
lemma can_colS {h sv : ι → ℕ} (hh : Knows m B s x h) (hhs : Small B h) (hsv : Knows m B s x sv)
    (hss : Small B sv) (hpow : Small B (fun i => E.mx^(h i))) :
    Can m B s w x (fun i => colS E.W E.tq (h i) (sv i)) (fun i => h i + 1) := by
  have I := fun d : During h => E.iter_bound (sv d.i) d.j
  exact ((can_iter (t := p w w) (v := fun i j => (stepC E.W E.tq)^[j] (1, sv i)) (Wt := fun _ => 0)
    hh hhs ((Can.wc 1).pair hsv)
    (((Can.second.snd.fst.wmul (E.knows_tq (Can.second.snd.snd.wmod (Can.wc E.W)
        ((Small.const _ E.W).mono fun _ => (Nat.mod_lt _ E.W_pos).le)) fun _ => Nat.mod_lt _ E.W_pos)
      ((hpow.reindex During.i).mono fun d => (Nat.mul_le_mul (I d).1 (E.tq_le _)).trans
        ((pow_succ _ _).ge.trans (Nat.pow_le_pow_right ((Nat.zero_lt_succ 2).trans_le E.three) d.hj)))).pair
      (Can.second.snd.snd.wdiv (Can.wc E.W) ((hss.reindex During.i).mono fun d =>
        (Nat.div_le_self _ _).trans (I d).2))).cong (fun _ => rfl)
      fun d => (Function.iterate_succ_apply' (stepC E.W E.tq) d.j (1, sv d.i)).symm)).fst).mono fun i => by simp
variable {n h μ : ι → ℕ}
lemma knows_inR (c : CIn m B s x n h μ) {j : ι → ℕ} (hj : Knows m B s x j) (hjs : Small B j)
    (hWh : Knows m B s x (fun i => E.W^(h i))) :
    Can m B s w x (fun i => if inRS E.W E.tq E.mx (n i) (h i) (μ i) (j i) then 1 else 0) (fun i => h i + 1) := by
  have S1 : Small B fun i => μ i * colS E.W E.tq (h i) (j i) :=
    c.μS.mul ((c.powS E.mx).mono fun i => (E.iter_bound _ _).1)
  refine ((Has.atW (hj.wlt hWh)).wmul (((Can.wc E.mx).wmul ((Has.atW c.μK).wmul
    (E.can_colS c.hK c.hS hj hjs (c.powS E.mx)) S1) ((Small.const _ _).mul S1)).wlt
    ((Has.atW c.nK).wadd (Can.wc 1) (c.nS.add (Small.const _ 1))))
    ((Small.const B 1).mono fun _ => by split_ifs <;> simp)).cong (fun _ => rfl) fun i => ?_
  by_cases h1 : j i < E.W ^ h i <;> by_cases h2 : E.mx * (μ i * colS E.W E.tq (h i) (j i)) ≤ n i <;>
    simp [inRS, h1, h2, Nat.lt_add_one_iff]
lemma cntU (c : CIn m B s x n h μ) (hW : Knows m B s x (fun i => E.W ^ h i)) {T q : ι → ℕ}
    (hT : Knows m B s x T) (hTs : Small B T) (hq : Knows m B s x q) :
    Can m B s (p w w) x (fun i => (E.PCc (n i) (h i) (μ i) (T i), if q i < E.PCc (n i) (h i) (μ i) (T i)
      then E.Uc (n i) (h i) (μ i) (q i) else 0)) (fun i => T i * (h i + 1 + 1) + 1) :=
  have I := E.knows_inR (c.reindex During.i (fun d : During T => (x d.i, d.j)) Can.first) Can.second
    ((hTs.reindex _).mono fun d => d.hj.le) (Has.extE (hW.reindex _))
  (can_count hT hTs I).pair (can_nthc hT hTs hq I)
abbrev IdxT : Ty := p w (p w (p (a w) (a w)))
def idxVal (n h μ : ℕ) : T IdxT :=
  (E.W^h, E.NUc n h μ, (Layout.std (E.W^h)).tape (fun t => E.PCc n h μ t),
    (Layout.std (E.NUc n h μ)).tape (fun p => E.Uc n h μ p))
def idxCost (n h μ : ℕ) : ℕ := (E.W^h + 1) * (E.W^h + 1) * (h + 2)
lemma NU_le' (n h μ : ℕ) : E.NUc n h μ ≤ E.W^h := UnitClass.NU_le _ _ _
lemma can_index (c : CIn m B s x n h μ) :
    Can m B s IdxT x (fun i => E.idxVal (n i) (h i) (μ i)) (fun i => E.idxCost (n i) (h i) (μ i)) := by
  have SK := c.powS E.W
  have c1 := c.ext (t := w) fun i => E.W ^ h i
  have c2 := c1.ext (t := w) fun i => E.NUc (n i) (h i) (μ i)
  refine ((can_powv E.W E.W_pos c.hK c.hS SK).mono ?_).bind
    (((E.cntU c1 Can.second Can.second SK Can.second).fst.mono ?_).bind
      (Can.first.snd.pair (Can.second.pair
        (((Can.table (P := fun i => E.W ^ h i * (h i + 1 + 1) + 1) _ Can.first.snd SK
          ((E.cntU (c2.onUnits fun i => E.W ^ h i) Can.first.fst.snd Can.second
            ((SK.reindex Sigma.fst).mono fun u => u.2.2.le) Can.second).fst.mono fun u =>
              Nat.add_le_add_right (Nat.mul_le_mul_right _ u.2.2.le) _)).mono ?_).pair
        ((Can.table (P := fun i => E.W ^ h i * (h i + 1 + 1) + 1) _ Can.second
          (SK.mono fun i => E.NU_le' _ _ _)
          ((E.cntU (c2.onUnits fun i => E.NUc (n i) (h i) (μ i)) Can.first.fst.snd Can.first.fst.snd
            (SK.reindex Sigma.fst) Can.second).snd.cong (fun _ => rfl) fun u => if_pos u.2.2)).mono ?_)))))
  all_goals
    intro i
    have hN : E.PCc (n i) (h i) (μ i) (E.W ^ h i) ≤ E.W ^ h i := E.NU_le' (n i) (h i) (μ i)
    simp only [idxCost]
    nlinarith [Nat.mul_le_mul_right (E.W ^ h i * (h i + 1 + 1) + 1 + 1) hN,
      Nat.zero_le (E.W ^ h i * E.W ^ h i * h i), Nat.zero_le (E.W ^ h i * h i),
      Nat.zero_le (E.W ^ h i * E.W ^ h i)]
abbrev UnT : Ty := p (a w) (p (a w) (p (a w) (a w)))
def unitVal (n h μ : ℕ) : T UnT :=
  ((Layout.std (E.NUc n h μ)).tape (fun p => E.cUc n h μ p),
   (Layout.std (E.NUc n h μ)).tape (fun p => 2^(E.cUc n h μ p)),
   (Layout.std (E.NUc n h μ)).tape (fun p => E.iUc n h μ p),
   (Layout.std (E.NUc n h μ)).tape (fun p => 2^(E.iUc n h μ p)))
lemma cU_le (n h μ : ℕ) (p : Fin (E.NUc n h μ)) : E.cUc n h μ p ≤ n := by
  have := E.fitc n h μ p; have := E.three; nlinarith
lemma can_units (c : CIn m B s x n h μ) :
    Can m B (p s IdxT) UnT (fun i => (x i, E.idxVal (n i) (h i) (μ i))) (fun i => E.unitVal (n i) (h i) (μ i))
      (fun i => E.NUc (n i) (h i) (μ i) * (4 * n i + 4 * h i + 8)) := by
  have c1 := (c.ext fun i => E.idxVal (n i) (h i) (μ i)).onUnits fun i => E.NUc (n i) (h i) (μ i)
  have SN := (c.powS E.W).mono fun i => E.NU_le' (n i) (h i) (μ i)
  have Sc := c1.nS.mono fun u => E.cU_le _ _ _ u.2
  have NUk : Knows m B (p s IdxT) (fun i => (x i, E.idxVal (n i) (h i) (μ i)))
    (fun i => E.NUc (n i) (h i) (μ i)) := Can.second.snd.fst
  have hUt : Has m B (p s IdxT) (a w) (fun i => (x i, E.idxVal (n i) (h i) (μ i)))
    (fun i => (Layout.std (E.NUc (n i) (h i) (μ i))).tape fun q => E.Uc (n i) (h i) (μ i) q) :=
    Can.second.snd.snd.snd
  have cU := (Has.atW c1.μK).wmul (E.can_colS c1.hK c1.hS
    (atU hUt)
    (((c.powS E.W).reindex _).mono fun u => (UnitClass.U_lt u.2.2).le) (c1.powS E.mx)) Sc
  have hI := (Has.atW c1.nK).wsub ((Can.wc E.mx).wmul cU (c1.nS.mono fun u => UnitClass.U_fits u.2.2))
    c1.nS.sub
  refine ((Can.table (P := fun i => h i + 1 + n i) _ NUk SN
      (cU.mono fun _ => Nat.le_add_right _ _)).pair
    ((Can.table (P := fun i => h i + 1 + n i) _ NUk SN
      ((cU.mono fun _ => Nat.le_add_right _ _).bind ((can_powv 2 two_pos Can.second Sc
        (c1.big.mono fun u => Nat.pow_le_pow_right two_pos (E.cU_le _ _ _ u.2))).mono
        fun u => le_trans (Nat.succ_le_succ (E.cU_le _ _ _ u.2)) (by omega)))).pair
    ((Can.table (P := fun i => h i + 1 + n i) _ NUk SN
      (hI.mono fun _ => Nat.le_add_right _ _)).pair
    (Can.table (P := fun i => h i + 1 + n i) _ NUk SN
      ((hI.mono fun _ => Nat.le_add_right _ _).bind ((can_powv 2 two_pos Can.second c1.nS.sub
        (c1.big.mono fun u => Nat.pow_le_pow_right two_pos (Nat.sub_le _ _))).mono fun u =>
          le_trans (Nat.succ_le_succ (Nat.sub_le _ _)) (by omega))))))).mono
    fun i => Nat.mul_le_mul le_rfl (by omega)
abbrev GearT : Ty := p (a (a w)) (a (a sc))
def gearVal (n h μ : ℕ) : T GearT :=
  ((Layout.std (E.NUc n h μ)).tape (fun p => xorTab (E.cUc n h μ p)),
   (Layout.std (E.NUc n h μ)).tape (fun p => (bits (E.cUc n h μ p)).tape (fun y : Bits (E.cUc n h μ p) => lum y)))
abbrev ClsT (s : Ty) : Ty := p (p (p s IdxT) UnT) GearT
lemma can_gears (c : CIn m B s x n h μ) :
    Can m B (p (p s IdxT) UnT) GearT
      (fun i => ((x i, E.idxVal (n i) (h i) (μ i)), E.unitVal (n i) (h i) (μ i)))
      (fun i => E.gearVal (n i) (h i) (μ i)) (fun i => E.NUc (n i) (h i) (μ i) * (2 * 2^(n i) + 2)) := by
  have c1 := ((c.ext fun i => E.idxVal (n i) (h i) (μ i)).ext fun i => E.unitVal (n i) (h i) (μ i)).onUnits
    fun i => E.NUc (n i) (h i) (μ i)
  have SN := (c.powS E.W).mono fun i => E.NU_le' (n i) (h i) (μ i)
  have NUk : Knows m B (p (p s IdxT) UnT)
    (fun i => ((x i, E.idxVal (n i) (h i) (μ i)), E.unitVal (n i) (h i) (μ i)))
    (fun i => E.NUc (n i) (h i) (μ i)) := Can.first.snd.snd.fst
  have t1 : Has m B (p (p s IdxT) UnT) (a w)
    (fun i => ((x i, E.idxVal (n i) (h i) (μ i)), E.unitVal (n i) (h i) (μ i)))
    (fun i => (Layout.std (E.NUc (n i) (h i) (μ i))).tape fun q => E.cUc (n i) (h i) (μ i) q) :=
    Can.second.fst
  have t2 : Has m B (p (p s IdxT) UnT) (a w)
    (fun i => ((x i, E.idxVal (n i) (h i) (μ i)), E.unitVal (n i) (h i) (μ i)))
    (fun i => (Layout.std (E.NUc (n i) (h i) (μ i))).tape fun q => 2^(E.cUc (n i) (h i) (μ i) q)) :=
    Can.second.snd.fst
  have hc := atU t1
  have Sc := c1.nS.mono fun u => E.cU_le _ _ _ u.2
  have Sp := c1.big.mono fun u => Nat.pow_le_pow_right two_pos (E.cU_le _ _ _ u.2)
  refine ((Can.table (P := fun i => 2^(n i)) _ NUk SN ((Can.xor_prepare hc
    (atU t2) Sc Sp).mono fun u => by
      rw [← pow_mul]; exact Nat.pow_le_pow_right two_pos
        (by have := E.fitc _ _ _ u.2; have := E.three; nlinarith))).pair
    (Can.table (P := fun i => 2^(n i)) _ NUk SN
      ((LumTable.lum_tables hc Sc Sp c1.imag).1.mono fun u =>
        Nat.pow_le_pow_right two_pos (E.cU_le _ _ _ u.2)))).mono
    fun i => Nat.mul_le_mul le_rfl (by omega)
lemma cctx (c : CIn m B s x n h μ) :
    CCtx m B (ClsT s) (fun i => (((x i, E.idxVal (n i) (h i) (μ i)), E.unitVal (n i) (h i) (μ i)),
        E.gearVal (n i) (h i) (μ i))) E.X.n n (fun i => E.NUc (n i) (h i) (μ i))
      (fun i p => E.cUc (n i) (h i) (μ i) p) (fun i p => E.iUc (n i) (h i) (μ i) p) :=
  ⟨Can.first.fst.fst.then_do c.nK, Can.first.fst.fst.then_do c.p2n, Can.first.fst.snd.snd.fst,
    Can.first.fst.fst.then_do c.imag, Can.first.snd.fst,
    Can.first.snd.snd.fst, Can.first.snd.snd.snd.fst, Can.first.snd.snd.snd.snd, Can.second.fst,
    Can.second.snd, c.big, (c.powS E.W).mono fun i => E.NU_le' _ _ _, fun i p => E.fitc _ _ _ p,
    by have := E.three; omega⟩
end BlockEngine
end
end PowerSaving.RAM
end OAI
