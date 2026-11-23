--might be  containing modified Apache-2.0 codes pieces from one or several sources; notices and credits: Credits.lean
import Submission.Engine.ClassSetup

namespace OAI
namespace PowerSaving.EngRecursion
open PowerSaving.RAM Ty

noncomputable section

universe U V

def blankCode {m : Bool} {r : Port} (s t : Ty) : Code m r s t := Code.blank s t

section
variable {D : Type V} {s t : Ty}

structure GDesc (encodeJob : D → T s) (jobAnswer : D → T t) (Kid : D → D → Prop) where
  d : D
  use : Handler (some (s,t))
  tau : D → ℕ
  peak : ℕ
  works : ∀ c, Kid d c → (use (encodeJob c)).OK (jobAnswer c) (tau c) peak

def gfunds (encodeJob : D → T s) (jobAnswer : D → T t) (Kid : D → D → Prop) (bnd : D → ℕ) :
    Bank (some (s,t)) (GDesc encodeJob jobAnswer Kid) :=
  ⟨fun g => bnd g.d, fun g => g.peak, fun g => g.use⟩

theorem closed_inv (m : Bool) (encodeJob : D → T s) (jobAnswer : D → T t)
    (Kid : D → D → Prop) (Inv : D → Prop) (bnd loc rank fuel cost : D → ℕ)
    (charge : D → (D → ℕ) → ℕ)
    (job_body : Able m (gfunds encodeJob jobAnswer Kid bnd) s t (fun i => encodeJob i.d)
      (fun i => jobAnswer i.d) (fun i => loc i.d) (fun i => charge i.d i.tau))
    (hinv : ∀ d c, Inv d → Kid d c → Inv c) (hrk : ∀ d c, Inv d → Kid d c → rank c < rank d)
    (hbd : ∀ d c, Inv d → Kid d c → bnd c ≤ bnd d)
    (hhom : ∀ d, Inv d → ∀ (K : ℕ) (f : D → ℕ),
      charge d (fun c => K * f c) ≤ K * charge d f)
    (hcost : ∀ d, Inv d → loc d + 1 + charge d cost ≤ cost d)
    (hfuel : Can m (fun d : {d // Inv d} => bnd d.1) s Ty.w
      (fun d => encodeJob d.1) (fun d => fuel d.1) (fun d => cost d.1))
    (hrf : ∀ d, Inv d → rank d < fuel d)
    (hfs : Small (fun d : {d // Inv d} => bnd d.1) (fun d => fuel d.1)) {ι : Type U}
    (dd : ι → D) (hdd : ∀ i, Inv (dd i)) :
    Can m (fun i => bnd (dd i)) s t (fun i => encodeJob (dd i))
      (fun i => jobAnswer (dd i)) (fun i => cost (dd i)) := by
  obtain ⟨body, K, deg, hK⟩ := job_body
  obtain ⟨e, he⟩ := hfs
  set base : Prog m s t := blankCode s t with hbase
  set run := depthRun (base.run ()) body.run with hrun
  set Q : ℕ → ℕ := fun b => (b + 2) ^ (deg + 1) with hQ
  have Qmono : ∀ a b, a ≤ b → Q a ≤ Q b := fun a b h => Nat.pow_le_pow_left (by omega) _
  have key : ∀ k x, Inv x → rank x < k →
      (run k (encodeJob x)).OK (jobAnswer x) ((K + 1) * cost x) (max (Q (bnd x)) k) := by
    intro k
    induction k with
    | zero => intro x _ hx; omega
    | succ k ih =>
      intro x hx hlt
      let g : GDesc encodeJob jobAnswer Kid :=
        { d := x, use := run k, tau := fun y => (K + 1) * cost y,
          peak := max (Q (bnd x)) (k + 1),
          works := fun y hy => (ih y (hinv x y hx hy) (by have := hrk x y hx hy; omega)).mono
            le_rfl (max_le_max (Qmono _ _ (hbd x y hx hy)) (Nat.le_succ k)) }
      have hg := hK g
      have hcap : (gfunds encodeJob jobAnswer Kid bnd).cap deg g ≤ max (Q (bnd x)) (k + 1) :=
        max_le (le_max_of_le_left (Nat.pow_le_pow_right (by omega) (Nat.le_succ deg))) le_rfl
      have h1 := (hg.mono le_rfl hcap).pay (t := 1) (le_max_right (Q (bnd x)) (k + 1))
      refine h1.mono ?_ le_rfl
      have c1 := hhom x hx (K + 1) cost
      have c2 := Nat.mul_le_mul_left (K + 1) (hcost x hx)
      simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_one] at c2 ⊢
      change K * loc x + K + charge x (fun y => (K + 1) * cost y) + 1 ≤ _
      have : K * loc x ≤ K * loc x := le_rfl
      nlinarith [c1, c2]
  let D' := {x : D // Inv x}
  have outer : Can m (fun x : D' => bnd x.1) (Ty.p Ty.w s) t (fun x => (fuel x.1, encodeJob x.1))
      (fun x => jobAnswer x.1) (fun x => cost x.1) := by
    refine ⟨.descend base body, K + 2, deg + 1 + e, fun x => ?_⟩
    have h0 := (key (fuel x.1) x.1 x.2 (hrf x.1 x.2)).pay (t := 1) (z := fuel x.1) (le_max_right _ _)
    refine h0.mono ?_ ?_
    · show (K + 1) * cost x.1 + 1 ≤ (K + 2) * (cost x.1 + 1) + 0
      nlinarith
    · show max (Q (bnd x.1)) (fuel x.1) ≤ max ((bnd x.1 + 2) ^ (deg + 1 + e)) 0
      refine le_max_of_le_left (max_le ?_ ?_)
      · exact Nat.pow_le_pow_right (by omega) (by omega)
      · exact (he x).trans (Nat.pow_le_pow_right (by omega) (by omega))
  exact ((hfuel.pair Can.id).then_do outer).reindex (fun i => (⟨dd i, hdd i⟩ : D'))
theorem closed (m : Bool) (encodeJob : D → T s) (jobAnswer : D → T t)
    (Kid : D → D → Prop) (bnd loc rank fuel cost : D → ℕ)
    (charge : D → (D → ℕ) → ℕ)
    (job_body : Able m (gfunds encodeJob jobAnswer Kid bnd) s t (fun i => encodeJob i.d)
      (fun i => jobAnswer i.d) (fun i => loc i.d) (fun i => charge i.d i.tau))
    (hrk : ∀ d c, Kid d c → rank c < rank d) (hbd : ∀ d c, Kid d c → bnd c ≤ bnd d)
    (hhom : ∀ d (K : ℕ) (f : D → ℕ),
      charge d (fun c => K * f c) ≤ K * charge d f)
    (hcost : ∀ d, loc d + 1 + charge d cost ≤ cost d)
    (hfuel : Can m bnd s Ty.w encodeJob fuel cost) (hrf : ∀ d, rank d < fuel d)
    (hfs : Small bnd fuel) {ι : Type U} (dd : ι → D) :
    Can m (fun i => bnd (dd i)) s t (fun i => encodeJob (dd i))
      (fun i => jobAnswer (dd i)) (fun i => cost (dd i)) :=
  closed_inv m encodeJob jobAnswer Kid (fun _ => True) bnd loc rank fuel cost charge job_body
    (fun _ _ _ _ => trivial) (fun d c _ h => hrk d c h) (fun d c _ h => hbd d c h)
    (fun d _ => hhom d) (fun d _ => hcost d)
    (hfuel.reindex (Subtype.val : {d : D // True} → D)) (fun d _ => hrf d)
    (hfs.reindex (Subtype.val : {d : D // True} → D)) dd (fun _ => trivial)
end
section
variable {D : Type V}

def listCharge (kids : D → List D) (d : D) (tau : D → ℕ) : ℕ := ((kids d).map tau).sum

theorem list_sum_map_mul (l : List D) (K : ℕ) (f : D → ℕ) :
    (l.map (fun c => K * f c)).sum = K * (l.map f).sum := by
  rw [List.sum_map_mul_left]
theorem listCharge_hom (kids : D → List D) (d : D) (K : ℕ) (f : D → ℕ) :
    listCharge kids d (fun c => K * f c) ≤ K * listCharge kids d f :=
  (list_sum_map_mul (kids d) K f).le
theorem closed_list {s t : Ty} (m : Bool) (encodeJob : D → T s) (jobAnswer : D → T t)
    (kids : D → List D) (bnd loc rank fuel cost : D → ℕ)
    (job_body : Able m (gfunds encodeJob jobAnswer (fun d c => c ∈ kids d) bnd) s t
      (fun i => encodeJob i.d) (fun i => jobAnswer i.d) (fun i => loc i.d)
      (fun i => listCharge kids i.d i.tau))
    (hrk : ∀ d c, c ∈ kids d → rank c < rank d) (hbd : ∀ d c, c ∈ kids d → bnd c ≤ bnd d)
    (hcost : ∀ d, loc d + 1 + ((kids d).map cost).sum ≤ cost d)
    (hfuel : Can m bnd s Ty.w encodeJob fuel cost) (hrf : ∀ d, rank d < fuel d)
    (hfs : Small bnd fuel) {ι : Type U} (dd : ι → D) :
    Can m (fun i => bnd (dd i)) s t (fun i => encodeJob (dd i))
      (fun i => jobAnswer (dd i)) (fun i => cost (dd i)) :=
  closed m encodeJob jobAnswer (fun d c => c ∈ kids d) bnd loc rank fuel cost
    (listCharge kids) job_body hrk hbd (listCharge_hom kids) hcost hfuel hrf hfs dd
end
end
end PowerSaving.EngRecursion
end OAI

namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset GenMove UnitClass
noncomputable section
universe U
def hiVec (n s : ℕ) (w : Bits n → ℂ) : ℕ → Bits (n - s) → ℂ :=
  if hs : s ≤ n then fun q y => w (castB (Nat.add_sub_cancel' hs) (catB s (n - s) (bitsOf s q, y)))
  else fun _ _ => 0
lemma tm_dm {p x W : ℕ} (hx : x < W) : (p * W + x) / W = p ∧ (p * W + x) % W = x := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.zero_lt_of_lt hx), Nat.add_mul_mod_self_right, Nat.div_eq_of_lt hx,
    Nat.mod_eq_of_lt hx]; exact ⟨Nat.zero_add _, rfl⟩

lemma tm_cast {a : ℕ} (h : a = a) (z : Bits a) : castB h z = z := rfl
lemma tm_ite (L a b N : ℕ) : ∑ j ∈ range N, (if j < L then a else b) ≤ min N L * a + (N - L) * b := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ]; split_ifs with h
    · rw [show min (N+1) L = min N L + 1 by omega, show N + 1 - L = N - L by omega]; linarith
    · rw [show min (N+1) L = min N L by omega, show N + 1 - L = N - L + 1 by omega]; linarith
lemma cnt_blk (R : ℕ → Prop) [DecidablePred R] (W S : ℕ) :
    Nat.count R (S * W) = ∑ s ∈ range S, Nat.count (fun a => R (s * W + a)) W := by
  induction S with
  | zero => simp
  | succ S ih => rw [Nat.succ_mul, Nat.count_add, ih, sum_range_succ]
lemma cnt_cg {R R' : ℕ → Prop} [DecidablePred R] [DecidablePred R'] {W : ℕ} (h : ∀ a < W, R a ↔ R' a) :
    Nat.count R W = Nat.count R' W := by
  simp only [Nat.count_eq_card_filter_range]; exact congrArg _ (Finset.filter_congr fun a ha => h a (mem_range.1 ha))
lemma sum_nth (P : ℕ → Prop) [DecidablePred P] {c : ℕ → ℕ} (hc : ∀ s, ¬ P s → c s = 0) (S : ℕ) :
    ∑ s ∈ range S, c s = ∑ p ∈ range (Nat.count P S), c (Nat.nth P p) := by
  induction S with
  | zero => simp
  | succ S ih =>
    rw [sum_range_succ, Nat.count_succ, ih]; split_ifs with h
    · rw [sum_range_succ, Nat.nth_count h]
    · rw [hc S h, add_zero, add_zero]
lemma rsum (f : ℕ → ℕ) (n : ℕ) : ((List.range n).map f).sum = ∑ j ∈ range n, f j := by
  induction n <;> simp [List.range_succ, sum_range_succ, *]
lemma getD_le {l : List ℕ} {b : ℕ} (h : ∀ a ∈ l, a ≤ b) (k : ℕ) : l.getD k 0 ≤ b := by
  rw [List.getD_eq_getElem?_getD]
  rcases hk : l[k]? with _ | a
  · simp
  · exact h a (List.mem_of_getElem? hk)
namespace BlockEngine
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]
variable (E : BlockEngine α ρ σ)

def nB : ℕ := (blockRanks E.wd).length

def rkI (j : ℕ) : ℕ := (blockRanks E.wd).getD j 0

def topG (kmin n : ℕ) : ℕ := Nat.findGreatest (fun g => E.mx * kmin ^ g ≤ n) n
def topNU0 (kmin n : ℕ) : ℕ := E.NUc n (E.topG kmin n) 1

def topN (kmin n : ℕ) : ℕ := E.topNU0 kmin n * E.W + E.cons n (E.topG kmin n) 1
def topSz (kmin n j : ℕ) : ℕ :=
  if j < E.topNU0 kmin n * E.W then E.slotSize n (E.topG kmin n) 1 j
  else E.csz n (E.topG kmin n) 1 (j - E.topNU0 kmin n * E.W)

def topRoot (kmin n B : ℕ) (v : ℕ → Bits n → ℂ) (t : ℕ) : EngJob :=
  EngJob.cls n (E.topG kmin n) 1 (t * E.topN kmin n + E.topNU0 kmin n * E.W) B
    (fun j => v (t * E.topN kmin n + j)) v
def topAns (kmin n : ℕ) (v : ℕ → Bits n → ℂ) (t j : ℕ) : Bits n → ℂ :=
  hlow n (E.topSz kmin n j) (v (t * E.topN kmin n + j))

def topRest (kmin n : ℕ) (v : ℕ → Bits n → ℂ) (t j : ℕ) : EngJob :=
  EngJob.top (n - E.topSz kmin n j) (2 ^ E.topSz kmin n j)
    (hiVec n (E.topSz kmin n j) (E.topAns kmin n v t j))

def kidsTop (kmin n0 n B : ℕ) (v : ℕ → Bits n → ℂ) : List EngJob :=
  if n0 ≤ n ∧ E.topN kmin n ≤ B then
    (List.range (B / E.topN kmin n)).flatMap fun t =>
      E.topRoot kmin n B v t :: (List.range (E.topN kmin n)).map (E.topRest kmin n v t)
  else []
def locH (h : ℕ) : ℕ := E.nB * (E.W ^ h * E.W * (2 * h + 3 + 1) + 1 + (h + 1) + 4)
def cstC : ℕ → ℕ
  | 0 => 1
  | h + 1 => E.locH h + 1 + E.nB * cstC h

def Ptop (kmin n : ℕ) : ℕ :=
  (n + 1) + (n * (n + 3) + 1) + E.idxCost n (E.topG kmin n) 1
    + E.NUc n (E.topG kmin n) 1 * (4 * n + 4 * E.topG kmin n + 8) + E.cstC (E.topG kmin n)
def locTop (kmin n0 n B : ℕ) : ℕ :=
  if n0 ≤ n then (B + 1) * 2 ^ n + (B % E.topN kmin n) * (n + 1) * 2 ^ n + E.Ptop kmin n
  else (B + 1) * (n + 1) * 2 ^ n + 1

def srcU (n h μ r u : ℕ) : Prop :=
  inRS E.W E.tq E.mx n h (μ * r) (u / E.W) ∧ ¬ inRS E.W E.tq E.mx n (h + 1) μ u
instance (n h μ r : ℕ) : DecidablePred (E.srcU n h μ r) := fun u => by unfold srcU; infer_instance
lemma cons_zero (n μ : ℕ) : E.cons n 0 μ = 0 := rfl
theorem cons_succ_idx (n h μ : ℕ) :
    E.cons n (h+1) μ = ∑ j ∈ Finset.range E.nB,
      (Nat.count (E.srcU n h μ (E.rkI j)) (E.W^h * E.W) + E.cons n h (μ * E.rkI j)) := by
  suffices key : ∀ r, (E.ownSrc n h μ r).length = Nat.count (E.srcU n h μ r) (E.W^h * E.W) by
    simp only [cons, srcSizes, List.length_flatMap, List.length_append, sum_map_getD (z := 0), key]; rfl
  intro r; have h1 : (E.ownSrc n h μ r).length = Nat.count (E.srcP n h μ r) (E.NUc n h (μ * r) * E.W) := by
    unfold ownSrc; induction E.NUc n h (μ * r) * E.W with
    | zero => rfl
    | succ k ih => rw [List.range_succ, List.filterMap_append, List.length_append, ih, Nat.count_succ]; split_ifs <;> simp_all
  have hd := fun p a (ha : a < E.W) => tm_dm (p := p) ha
  rw [h1, cnt_blk, cnt_blk, show E.NUc n h (μ * r) = Nat.count _ (E.W ^ h) from rfl]
  symm; rw [sum_nth (inRS E.W E.tq E.mx n h (μ * r)) (fun s hs => ?_)]
  · refine sum_congr rfl fun p hp => cnt_cg fun a ha => ?_
    have hl : p * E.W + a < E.NUc n h (μ * r) * E.W :=
      (Nat.add_lt_add_left ha _).trans_le (by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (mem_range.1 hp))
    have hu := (UnitClass.U_spec (mem_range.1 hp)).1; unfold UnitClass.U at hu
    simp only [srcU, srcP, parCode, (hd _ _ ha).1, (hd _ _ ha).2, hu, hl, true_and, Nat.add_comm a, Nat.mul_comm E.W]; rfl
  · exact (cnt_cg (R' := fun _ => False) fun a ha => by simp [srcU, (hd _ _ ha).1, hs]).trans (by simp)
lemma locH_mono {h h' : ℕ} (hh : h ≤ h') : E.locH h ≤ E.locH h' := by
  unfold locH; have := E.W_pos; gcongr
lemma cstC_le (h : ℕ) : E.cstC h ≤ (E.nB + 1)^h * (E.locH h + 2) := by
  induction h with
  | zero => simp [cstC]
  | succ h ih =>
    have a := E.locH_mono h.le_succ; have b := Nat.one_le_pow h (E.nB + 1) (by omega)
    have := Nat.mul_le_mul_left E.nB (ih.trans (Nat.mul_le_mul_left ((E.nB + 1)^h) (Nat.add_le_add_right a 2)))
    have := Nat.mul_le_mul b (Nat.add_le_add_right a 2)
    simp only [cstC, pow_succ]; nlinarith
lemma topG_le (kmin n : ℕ) : E.topG kmin n ≤ n := Nat.findGreatest_le n
lemma slot_le {n h μ t : ℕ} (ht : t < E.NUc n h μ * E.W) : E.slotSize n h μ t ≤ n := by
  have := E.fitc n h μ ⟨t / E.W, (Nat.div_lt_iff_lt_mul E.W_pos).2 ht⟩
  exact (Nat.mul_le_mul_right _ (E.tq_le _)).trans (Nat.le.intro this)
lemma src_le (n h μ : ℕ) : ∀ a ∈ E.srcSizes n h μ, a ≤ n := by
  induction h generalizing μ with
  | zero => simp [srcSizes]
  | succ h ih =>
    simp only [srcSizes, ownSrc, List.mem_flatMap, List.mem_append, List.mem_filterMap, List.mem_range]
    rintro a ⟨r, -, ⟨t, ht, e⟩ | e⟩
    · split_ifs at e; cases e; exact E.slot_le ht
    · exact ih _ _ e
lemma topSz_le (kmin n j : ℕ) : E.topSz kmin n j ≤ n := by
  unfold topSz csz; split_ifs with h; exact E.slot_le h
  exact getD_le (E.src_le _ _ _) _
abbrev CsT : Ty := p (p sc w) (p w (p w w))
abbrev CD := {d : ℕ × ℕ × ℕ // d.2.1 ≤ d.1}
def csEnc (d : CD) : T CsT := ((Complex.I, 2^d.1.1), (d.1.1, d.1.2.1, d.1.2.2))
def csKids (d : CD) : List CD :=
  if d.1.2.1 = 0 then [] else
    (List.range E.nB).map (fun j => ⟨(d.1.1, d.1.2.1 - 1, d.1.2.2 * E.rkI j), le_trans (Nat.sub_le _ _) d.2⟩)
def csOut (d : CD) : T Ty.w := E.cons d.1.1 d.1.2.1 d.1.2.2
def csK : ℕ := (blockRanks E.wd).sum + (E.nB + 1) * (E.W + 1) + 1
def csBnd (d : CD) : ℕ := (d.1.2.2 + 1) * E.csK ^ d.1.2.1 * 2^d.1.1
def csLoc (d : CD) : ℕ := if d.1.2.1 = 0 then 0 else E.locH (d.1.2.1 - 1)
lemma rkI_lt (j : ℕ) : E.rkI j < E.csK := by
  have := getD_le (fun a h => List.le_sum_of_mem h) j (l := blockRanks E.wd); unfold rkI csK; omega
lemma cons_le (n h μ : ℕ) : E.cons n h μ ≤ ((E.nB + 1) * (E.W + 1))^h := by
  induction h generalizing μ with
  | zero => exact Nat.zero_le _
  | succ h ih =>
    rw [cons_succ_idx]
    have hW : E.W ^ h ≤ ((E.nB + 1) * (E.W + 1)) ^ h := Nat.pow_le_pow_left (by nlinarith) _
    calc _ ≤ ∑ j ∈ range E.nB, ((E.nB + 1) * (E.W + 1)) ^ h * (E.W + 1) := sum_le_sum fun j _ => by
          have := Nat.count_le (p := E.srcU n h μ (E.rkI j)) (n := E.W ^ h * E.W); have := ih (μ * E.rkI j); nlinarith
      _ ≤ _ := by
        rw [sum_const, card_range, smul_eq_mul, pow_succ]; generalize ((E.nB + 1) * (E.W + 1)) ^ h = P
        nlinarith [Nat.zero_le (P * E.W)]
lemma cs_pos (d : CD) : d.1.2.1 + 1 ≤ E.csBnd d := by
  have h1 := Nat.lt_two_pow_self (n := d.1.2.1)
  have h2 : 2 ^ d.1.2.1 ≤ E.csK ^ d.1.2.1 := Nat.pow_le_pow_left (by
    unfold csK; have := Nat.le_mul_of_pos_left (E.W + 1) (by omega : 0 < E.nB + 1); omega) _
  exact (h1.trans_le h2).trans_le ((Nat.le_mul_of_pos_left _ (Nat.succ_pos _)).trans
    (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)))
def csF (d : CD) (k : ℕ) : ℕ := Nat.count (E.srcU d.1.1 (d.1.2.1 - 1) d.1.2.2 (E.rkI k)) (E.W ^ (d.1.2.1 - 1) * E.W) +
  E.cons d.1.1 (d.1.2.1 - 1) (d.1.2.2 * E.rkI k)
theorem cs_body (m : Bool) :
    Able m (EngRecursion.gfunds csEnc E.csOut
        (fun d c => c ∈ E.csKids d) E.csBnd) CsT w (fun i => csEnc i.d)
      (fun i => E.csOut i.d) (fun i => E.csLoc i.d)
      (fun i => EngRecursion.listCharge E.csKids i.d i.tau) := by
  have hK : E.W ≤ E.csK := by unfold csK; have := Nat.le_mul_of_pos_left (E.W + 1) (by omega : 0 < E.nB + 1); omega
  have bd : ∀ d : CD, 2 ^ d.1.1 ≤ E.csBnd d ∧ d.1.2.2 + 1 ≤ E.csBnd d ∧ E.csK ^ d.1.2.1 ≤ E.csBnd d ∧
      (0 < d.1.2.1 → ∀ j, d.1.2.2 * E.rkI j ≤ E.csBnd d) := fun d => by
    have h1 := Nat.one_le_two_pow (n := d.1.1)
    have h3 : 1 ≤ E.csK ^ d.1.2.1 := Nat.one_le_pow _ _ (E.W_pos.trans_le hK)
    unfold csBnd; refine ⟨Nat.le_mul_of_pos_left _ (Nat.mul_pos (Nat.succ_pos _) h3),
      (Nat.le_mul_of_pos_right _ h3).trans (Nat.le_mul_of_pos_right _ h1),
      (Nat.le_mul_of_pos_left _ (Nat.succ_pos _)).trans (Nat.le_mul_of_pos_right _ h1), fun hp j => ?_⟩
    have := Nat.pow_le_pow_right (E.W_pos.trans_le hK) hp; rw [pow_one] at this
    exact (Nat.mul_le_mul (Nat.le_succ _) ((E.rkI_lt j).le.trans this)).trans (Nat.le_mul_of_pos_right _ h1)
  have hW : ∀ h, E.W ^ h ≤ E.csK ^ h := fun h => Nat.pow_le_pow_left hK h
  let ch (d : CD) (j : ℕ) : CD := ⟨(d.1.1, d.1.2.1 - 1, d.1.2.2 * E.rkI j), le_trans (Nat.sub_le _ _) d.2⟩
  let N (i : EngRecursion.GDesc csEnc E.csOut (fun d c => c ∈ E.csKids d)) : ℕ := E.nB * if 0 < i.d.1.2.1 then 1 else 0
  have hd : ∀ d : During N, 0 < d.i.d.1.2.1 ∧ d.j < E.nB := fun d => by
    have := d.hj; simp only [N] at this; split_ifs at this with h
    exacts [⟨h, by simpa using this⟩, by simp at this]
  have hs : Able m ((EngRecursion.gfunds csEnc E.csOut (fun d c => c ∈ E.csKids d) E.csBnd).comap (During.i (n := N)))
      (p CsT (p w w)) w (fun d => (csEnc d.i.d, d.j, ∑ k ∈ range d.j, E.csF d.i.d k))
      (fun d => ∑ k ∈ range (d.j + 1), E.csF d.i.d k)
      (fun d => d.i.d.1.2.1 + E.W ^ (d.i.d.1.2.1 - 1) * E.W * (d.i.d.1.2.1 + 2) + 1) (fun d => d.i.tau (ch d.i.d d.j)) := by
    have SB := Small.self (fun d : During N => E.csBnd d.i.d)
    have bdd := fun d : During N => bd d.i.d
    have Sh' := SB.mono fun d => (Nat.sub_le _ 1).trans ((Nat.le_succ _).trans (E.cs_pos d.i.d))
    have hh : Knows m (fun d : During N => E.csBnd d.i.d) (p CsT (p w w))
      (fun d => (csEnc d.i.d, d.j, ∑ k ∈ range d.j, E.csF d.i.d k)) (fun d => d.i.d.1.2.1 - 1) :=
      Can.first.snd.snd.fst.wsub (Can.wc 1) Sh'
    have hpw := can_powv E.W E.W_pos hh Sh' (SB.mono fun d => (Nat.pow_le_pow_right E.W_pos (Nat.sub_le _ 1)).trans
      ((hW d.i.d.1.2.1).trans (bdd d).2.2.1))
    have ST := SB.mono fun d => (by rw [← pow_succ, Nat.sub_add_cancel (hd d).1]; exact (hW _).trans (bdd d).2.2.1 :
      E.W ^ (d.i.d.1.2.1 - 1) * E.W ≤ _)
    have vb : ∀ d : During N, ∑ k ∈ range (d.j + 1), E.csF d.i.d k ≤ E.csBnd d.i.d := fun d => by
      have := E.cons_succ_idx d.i.d.1.1 (d.i.d.1.2.1 - 1) d.i.d.1.2.2; rw [Nat.sub_add_cancel (hd d).1] at this
      exact (sum_le_sum_of_subset (range_subset_range.2 (hd d).2)).trans (this ▸ (E.cons_le _ _ _).trans
        ((Nat.pow_le_pow_left (by unfold csK; omega) _).trans (bdd d).2.2.1))
    have g : Able m ((EngRecursion.gfunds csEnc E.csOut (fun d c => c ∈ E.csKids d) E.csBnd).comap (During.i (n := N)))
        (p (p CsT (p w w)) w) w (fun d => ((csEnc d.i.d, d.j, ∑ k ∈ range d.j, E.csF d.i.d k), E.W ^ (d.i.d.1.2.1 - 1)))
        (fun d => ∑ k ∈ range (d.j + 1), E.csF d.i.d k) (fun d => E.W ^ (d.i.d.1.2.1 - 1) * E.W * (d.i.d.1.2.1 + 1 + 1) + 1)
        (fun d => d.i.tau (ch d.i.d d.j)) := by
      let x1 := fun d : During N => ((csEnc d.i.d, d.j, ∑ k ∈ range d.j, E.csF d.i.d k), E.W ^ (d.i.d.1.2.1 - 1))
      let DT := During (fun d : During N => E.W ^ (d.i.d.1.2.1 - 1) * E.W)
      have c2 : CIn m (fun d : During N => E.csBnd d.i.d) (p (p CsT (p w w)) w) x1
          (fun d => d.i.d.1.1) (fun d => d.i.d.1.2.1) (fun d => d.i.d.1.2.2) :=
        ⟨Can.first.fst.snd.fst, Can.first.fst.snd.snd.fst, Can.first.fst.snd.snd.snd, Can.first.fst.fst.snd,
          Can.first.fst.fst.fst, SB.mono fun d => (bdd d).1, fun d => d.i.d.2, SB.mono fun d => (Nat.le_succ _).trans (bdd d).2.1⟩
      have rK : Knows m (fun d : During N => E.csBnd d.i.d) (p (p CsT (p w w)) w) x1 (fun d => E.rkI d.j) :=
        Can.cases_code (Layout.std E.nB) (q := fun d => (⟨d.j, (hd d).2⟩ : Fin E.nB)) Can.first.snd.fst fun f =>
          (Can.wc (E.rkI f)).cong (fun _ => rfl) fun e => (congrArg (fun f : Fin E.nB => E.rkI f) e.2).symm
      have Sr := SB.mono fun d => (bdd d).2.2.2 (hd d).1 d.j
      have c1 : CIn m (fun d : During N => E.csBnd d.i.d) (p (p CsT (p w w)) w) x1 (fun d => d.i.d.1.1) (fun d => d.i.d.1.2.1 - 1)
          (fun d => d.i.d.1.2.2 * E.rkI d.j) := ⟨c2.1, c2.2.wsub (Can.wc 1) Sh', c2.3.wmul rK Sr, c2.4, c2.5, c2.6,
            fun d => (Nat.sub_le _ _).trans d.i.d.2, Sr⟩
      have Su : Small (fun e : DT => E.csBnd e.i.i.d) (·.j) := (ST.reindex During.i).mono fun e => e.hj.le
      have hWh : Knows m (fun e : DT => E.csBnd e.i.i.d) (p (p (p CsT (p w w)) w) w) (fun e => (x1 e.i, e.j))
          (fun e => E.W ^ e.i.i.d.1.2.1) := (Can.first.snd.wmul (Can.wc E.W) (ST.reindex _)).cong (fun _ => rfl)
        fun e => by rw [← pow_succ, Nat.sub_add_cancel (hd e.i).1]
      have ia := E.knows_inR (c1.reindex (t := p (p (p CsT (p w w)) w) w) During.i (fun e : DT => (x1 e.i, e.j)) Can.first) (Can.second.wdiv (Can.wc E.W)
        Su.div) Su.div Can.first.snd
      have ib := E.knows_inR (c2.reindex (t := p (p (p CsT (p w w)) w) w) During.i (fun e : DT => (x1 e.i, e.j)) Can.first) Can.second Su hWh
      have hind : Can m (fun e : DT => E.csBnd e.i.i.d) (p (p (p CsT (p w w)) w) w) w (fun e => (x1 e.i, e.j))
          (fun e => if E.srcU e.i.i.d.1.1 (e.i.i.d.1.2.1 - 1) e.i.i.d.1.2.2 (E.rkI e.i.j) e.j then 1 else 0)
          (fun e => e.i.i.d.1.2.1 + 1) := ((ia.mono fun e => by omega).wmul ((Can.wc 1).wsub ib (Small.const _ 1).sub)
            ((Small.const _ 1).mono fun e => by split_ifs <;> simp)).cong (fun _ => rfl) fun e => by
          simp only [srcU, Nat.sub_add_cancel (hd e.i).1]; split_ifs <;> simp_all
      have cnt := can_count (m := m) (s := p (p CsT (p w w)) w) (x := x1) (T := fun d => E.W ^ (d.i.d.1.2.1 - 1) * E.W) (Wt := fun d => d.i.d.1.2.1 + 1)
        (P := fun d : During N => E.srcU d.i.d.1.1 (d.i.d.1.2.1 - 1) d.i.d.1.2.2 (E.rkI d.j)) (Can.second.wmul (Can.wc E.W) ST) ST hind
      refine (((Able.of_can ((Has.atW Can.first.snd.snd).pair cnt)).fork ((Able.of_can (W := fun _ => 0) ((c2.imag.pair c2.p2n).pair
          (c2.nK.pair (c1.hK.pair c1.μK)))).comp (Able.use_call fun d => d.i.works (ch d.i.d d.j) (by
            unfold csKids; rw [if_neg (hd d).1.ne']; exact List.mem_map.2 ⟨d.j, List.mem_range.2 (hd d).2, rfl⟩)))).comp
          (Able.of_can (W := fun _ => 0) (((Can.first.fst.wadd Can.first.snd (SB.mono fun d => ?_)).wadd Can.second (SB.mono fun d => ?_)).cong
            (fun _ => rfl) fun d => ?_))).mono (fun d => by simp) (fun d => by simp)
      · exact (Nat.add_le_add_left (Nat.le_add_right _ _) _).trans (sum_range_succ (E.csF d.i.d) _ ▸ vb d)
      · exact (Nat.add_assoc _ _ _).trans_le (sum_range_succ (E.csF d.i.d) _ ▸ vb d)
      · exact (Nat.add_assoc _ _ _).trans (sum_range_succ _ _).symm
    refine (Able.save (Able.of_can hpw) g).mono (fun d => ?_) (fun d => by simp)
    exact le_of_eq (by rw [Nat.sub_add_cancel (hd d).1]; ring)
  have L := Able.loop (b := EngRecursion.gfunds csEnc E.csOut (fun d c => c ∈ E.csKids d) E.csBnd) (x := fun i => csEnc i.d)
    (W := fun _ => 0) (W' := fun _ => 0) (n := N) (v := fun i j => ∑ k ∈ range j, E.csF i.d k)
    (Wb := fun i _ => i.d.1.2.1 + E.W ^ (i.d.1.2.1 - 1) * E.W * (i.d.1.2.1 + 2) + 1) (Zb := fun i j => i.tau (ch i.d j))
    (Able.of_can ((Can.wc E.nB).wmul ((Can.wc 0).wlt Can.second.snd.fst) ((Small.const _ E.nB).mono fun i => by
      split_ifs <;> simp))) (Able.of_can ((Can.wc 0).cong (fun _ => rfl) fun _ => by simp)) hs
    ((Small.const _ E.nB).mono fun i => by simp only [N]; split_ifs <;> simp)
  refine (L.cong (fun _ => rfl) fun i => ?_).weaken (Dom.of_le fun i => ?_) fun i => ?_ <;>
    rcases Nat.eq_zero_or_pos i.d.1.2.1 with h0 | hp
  · simp only [N, h0, lt_irrefl, if_false, mul_zero, sum_range_zero]; unfold csOut; rw [h0]; rfl
  · have := E.cons_succ_idx i.d.1.1 (i.d.1.2.1 - 1) i.d.1.2.2; rw [Nat.sub_add_cancel hp] at this
    simp only [N, hp, if_true, mul_one]; exact this.symm
  · simp [N, h0]
  · simp only [N, hp, if_true, mul_one, sum_const, card_range, smul_eq_mul, csLoc, if_neg hp.ne', locH]
    obtain ⟨h, e⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'; rw [e, Nat.succ_sub_one]; generalize E.W ^ h * E.W = T
    nlinarith [Nat.zero_le (E.nB * T * h), Nat.zero_le (E.nB * T)]
  · simp [N, h0]
  · simp only [N, hp, if_true, mul_one, EngRecursion.listCharge, csKids, if_neg hp.ne', List.map_map, rsum, Nat.zero_add]; exact le_rfl
lemma can_cons {ι : Type U} {m : Bool} {B : ι → ℕ} {s : Ty} {x : ι → T s} {n h : ι → ℕ}
    (hle : ∀ i, h i ≤ n i) (hin : Has m B s CsT x (fun i => csEnc ⟨(n i, h i, 1), hle i⟩))
    (hs : Small B (fun i => E.csBnd ⟨(n i, h i, 1), hle i⟩)) :
    Can m B s w x (fun i => E.cons (n i) (h i) 1) (fun i => E.cstC (h i)) := by
  have hk : ∀ d c, c ∈ E.csKids d → 0 < d.1.2.1 ∧ ∃ j, c = ⟨(d.1.1, d.1.2.1 - 1, d.1.2.2 * E.rkI j), le_trans (Nat.sub_le _ _) d.2⟩ :=
    fun d c hc => by
      unfold csKids at hc; split_ifs at hc with h0; · simp at hc
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hc; exact ⟨Nat.pos_of_ne_zero h0, j, rfl⟩
  refine (hin.pipe ((EngRecursion.closed_list m csEnc E.csOut E.csKids E.csBnd E.csLoc (fun d => d.1.2.1) (fun d => d.1.2.1 + 1)
    (fun d => E.cstC d.1.2.1) (E.cs_body m) (fun d c hc => ?_) (fun d c hc => ?_) (fun d => ?_)
    (Can.second.snd.fst.wadd (Can.wc 1) ((Small.self _).mono E.cs_pos)) (fun d => Nat.lt_succ_self _)
    ((Small.self _).mono E.cs_pos) (fun i => ⟨(n i, h i, 1), hle i⟩)).ambient hs)).mono fun i => by simp
  · obtain ⟨h0, j, rfl⟩ := hk d c hc; exact Nat.sub_lt h0 one_pos
  · obtain ⟨h0, j, rfl⟩ := hk d c hc
    have h2 : d.1.2.2 * E.rkI j + 1 ≤ (d.1.2.2 + 1) * E.csK := by have := E.rkI_lt j; nlinarith
    have h3 : E.csK ^ d.1.2.1 = E.csK ^ (d.1.2.1 - 1) * E.csK := by rw [← pow_succ, Nat.sub_add_cancel h0]
    unfold csBnd; dsimp only; rw [h3]; refine Nat.mul_le_mul_right _ ?_
    nlinarith [Nat.mul_le_mul_right (E.csK ^ (d.1.2.1 - 1)) h2]
  · rcases Nat.eq_zero_or_pos d.1.2.1 with h0 | h0
    · simp [csLoc, csKids, h0, cstC]
    · simp only [csLoc, csKids, h0.ne', if_false, List.map_map, Function.comp_def, rsum, sum_const, card_range, smul_eq_mul]
      obtain ⟨h, e⟩ := Nat.exists_eq_succ_of_ne_zero h0.ne'; rw [e, Nat.succ_sub_one, cstC]
lemma can_topG {ι : Type U} {m : Bool} {B : ι → ℕ} {s : Ty} {x : ι → T s} {n : ι → ℕ} (kmin : ℕ)
    (hk : 0 < kmin) (hn : Knows m B s x n) (h2 : Small B (fun i => 2^(n i))) :
    Can m B s w x (fun i => E.topG kmin (n i)) (fun i => n i * (n i + 3) + 1) := by
  have hS : Small B n := h2.mono fun i => Nat.lt_two_pow_self.le
  have hD := hS.reindex (During.i (n := n))
  have hj : Knows m (fun d : During n => B d.i) (p s (p w w)) (fun d => (x d.i, d.j, Nat.findGreatest
      (fun g => E.mx * kmin ^ g ≤ n d.i) d.j)) (fun d => d.j + 1) :=
    Can.second.fst.wadd (Can.wc 1) (hD.mono fun d => d.hj)
  have hk' : Small (fun d : During n => B d.i) fun d => kmin ^ (d.j + 1) := ((h2.pow kmin).reindex _).mono fun d =>
    (Nat.pow_le_pow_right hk d.hj).trans ((Nat.pow_le_pow_left Nat.lt_two_pow_self.le _).trans (by rw [← pow_mul, ← pow_mul, mul_comm]))
  have hc := (Has.atW (Has.extE (hn.reindex During.i))).wlt ((Can.wc E.mx).wmul (can_powv kmin hk hj (hD.mono fun d => d.hj) hk')
    ((Small.const _ _).mul hk'))
  have hj' := Has.atW (W := fun d => d.j + 1 + 1) hj
  refine can_iter (v := fun i j => Nat.findGreatest (fun g => E.mx * kmin ^ g ≤ n i) j) (Wt := fun i => n i + 2) hn hS ((Can.wc 0).cong (fun _ => rfl) fun _ => by simp) (((hj'.wsub ((hj'.wsub Can.second.snd (hD.mono fun d =>
    (Nat.sub_le _ _).trans d.hj)).wmul hc (hD.mono fun d => ?_)) (hD.mono fun d => (Nat.sub_le _ _).trans d.hj)).cong (fun _ => rfl)
    fun d => ?_).mono fun d => by have := d.hj; omega)
  · have := d.hj; split_ifs <;> omega
  · have := Nat.findGreatest_le (P := fun g => E.mx * kmin ^ g ≤ n d.i) d.j
    rw [Nat.findGreatest_succ]; dsimp only; by_cases hc : E.mx * kmin ^ (d.j + 1) ≤ n d.i
    · rw [if_pos hc, if_neg (not_lt.2 hc), Nat.mul_zero, Nat.sub_zero]
    · rw [if_neg hc, if_pos (not_le.1 hc), Nat.mul_one, Nat.sub_sub_self (this.trans (Nat.le_succ _))]
lemma tm_nv {ι : Type U} {m : Bool} {B : ι → ℕ} {s : Ty} {x : ι → T s} {cl : Paint} {n N tt : ι → ℕ}
    {v : ∀ i, ℕ → Bits (n i) → ℂ} (hn : Knows m B s x n) (hI : Has m B s sc x (fun _ => Complex.I))
    (hinp : Has m B s (jobsT cl) x (fun i => jobsTape (n i) (N i) (v i))) (ht : Knows m B s x tt)
    (hlt : ∀ i, tt i < N i) (h2 : Small B (fun i => 2^(n i))) :
    Can m B s (a (c cl)) x (fun i => (bits (n i)).tape (ripple (n i) (v i (tt i)))) (fun i => 2^(n i) * (2 * n i + 1)) :=
  ((hn.pair (hI.pair (has_jobsAt hinp ht hlt))).pipe ((ripple_naive_can cl m n _).ambient h2)).mono fun _ => by simp
lemma tm_naive {ι : Type U} {m : Bool} {B : ι → ℕ} {s : Ty} {x : ι → T s} {cl : Paint} {n N : ι → ℕ}
    {v : ∀ i, ℕ → Bits (n i) → ℂ} (hn : Knows m B s x n) (hI : Has m B s sc x (fun _ => Complex.I))
    (hinp : Has m B s (jobsT cl) x (fun i => jobsTape (n i) (N i) (v i))) (hN : Knows m B s x N)
    (h2 : Small B (fun i => (N i + 1) * 2^(n i))) :
    Can m B s (jobsT cl) x (fun i => jobsTape (n i) (N i) (fun t => ripple (n i) (v i t)))
      (fun i => N i * ((n i + 1) * 2^(n i))) := by
  have := (h2.mono fun i => Nat.le_mul_of_pos_left (2 ^ n i) (Nat.succ_pos (N i)))
  refine (Can.layout (L := fun i => Layout.std (N i)) (P := fun i => 2^(n i) * (2 * n i + 1)) hN (tm_nv (Has.liftE Sigma.fst hn) (Has.liftE Sigma.fst hI)
    (Has.liftE Sigma.fst hinp) Can.second (tt := fun d : (Σ i, Fin (N i)) => d.2.val) (fun d => d.2.2) (this.reindex _))
    (h2.mono fun i => (Nat.le_succ _).trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)))).weaken ⟨3, fun i => ?_⟩
  have := Nat.le_mul_of_pos_right (N i) (Nat.two_pow_pos (n i)); simp only [Layout.std]; nlinarith
lemma tm_bnd {n s : ℕ} (hs : s ≤ n) (x : Bits s) (y : Bits (n - s)) :
    (bits n).loc (castB (Nat.add_sub_cancel' hs) (catB s (n - s) (x, y))) = (bits s).loc x + 2^s * (bits (n - s)).loc y ∧
    (bits s).loc x < 2^s ∧ (bits (n - s)).loc y < 2^(n - s) :=
  ⟨loc_castB_catB n s hs x y, (bits s).bd x, (bits _).bd y⟩
lemma rip_cat {z k n : ℕ} (e : z + k = n) (w : Bits n → ℂ) (x : Bits z) (y : Bits k) :
    ripple n w (castB e (catB z k (x, y))) = ripple k (fun y' => hlow n z w (castB e (catB z k (x, y')))) y := by
  subst e; rw [← hhigh_hlow (z + k) z]; exact hhigh_catB z k _ x y
lemma tree_val (kmin n : ℕ) (v : ℕ → Bits n → ℂ) (t' : ℕ) (e : Bits n) :
    ripple (n - E.topSz kmin n (t' % E.topN kmin n)) (hiVec n (E.topSz kmin n (t' % E.topN kmin n))
      (E.topAns kmin n v (t' / E.topN kmin n) (t' % E.topN kmin n))
      ((bits n).loc e % 2 ^ E.topSz kmin n (t' % E.topN kmin n)))
      (bitsOf _ ((bits n).loc e / 2 ^ E.topSz kmin n (t' % E.topN kmin n))) = ripple n (v t') e := by
  have hs := E.topSz_le kmin n (t' % E.topN kmin n); unfold topAns
  generalize E.topSz kmin n (t' % E.topN kmin n) = z at hs ⊢
  obtain ⟨⟨x, y⟩, rfl⟩ := ((catB z (n - z)).trans (castB (Nat.add_sub_cancel' hs))).surjective e
  obtain ⟨hl, hx, -⟩ := tm_bnd hs x y
  simp only [Equiv.trans_apply, hl, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos z), Nat.div_eq_of_lt hx, Nat.zero_add, bitsOf_of_loc, hiVec, dif_pos hs]
  rw [Nat.div_add_mod']; exact (rip_cat _ _ x y).symm
lemma tm_pick {κ : Type U} {m : Bool} {B : κ → ℕ} {s : Ty} {x : κ → T s} {cl : Paint} (kmin : ℕ) {n Bv t j : κ → ℕ}
    {v : ∀ k, ℕ → Bits (n k) → ℂ} (hU : Has m B s (a w) x (fun k => (Layout.std (E.topNU0 kmin (n k))).tape
      (fun p => E.cUc (n k) (E.topG kmin (n k)) 1 p))) (hNU : Knows m B s x (fun k => E.topNU0 kmin (n k)))
    (hj : Knows m B s x j) (hr : Has m B s (portOut cl) x (fun k => E.jobAnswer cl (E.topRoot kmin (n k) (Bv k) (v k) (t k))))
    (hlt : ∀ k, j k < E.topN kmin (n k)) (hS : Small B (fun k => E.topN kmin (n k) + n k)) :
    Has m B s (p w (a (c cl))) x (fun k => (E.topSz kmin (n k) (j k), (bits (n k)).tape (E.topAns kmin (n k) (v k) (t k) (j k)))) := by
  have hN := hS.mono fun k => Nat.le_add_right _ _
  have hW := hNU.wmul (Can.wc E.W) (hN.mono fun k => Nat.le_add_right _ _)
  refine Can.testz (hj.wlt hW) ?_ ?_
  · have hk : ∀ k : {k // (if j k < E.topNU0 kmin (n k) * E.W then 1 else 0) = 0}, E.topNU0 kmin (n k.1) * E.W ≤ j k.1 ∧
        j k.1 - E.topNU0 kmin (n k.1) * E.W < E.cons (n k.1) (E.topG kmin (n k.1)) 1 := fun k => by
      have := k.2; have := hlt k.1; unfold topN at this; split_ifs at * <;> omega
    have kK : Knows m (fun k : {k // (if j k < E.topNU0 kmin (n k) * E.W then 1 else 0) = 0} => B k.1) s (fun k => x k.1)
      (fun k => j k.1 - E.topNU0 kmin (n k.1) * E.W) := (hj.reindex _).wsub (hW.reindex _) ((hN.reindex Subtype.val).mono fun k => (Nat.sub_le _ _).trans (hlt k.1).le)
    refine ((Can.fetch (L := fun k => Layout.std (E.cons (n k.1) (E.topG kmin (n k.1)) 1)) (i := fun k => ⟨_, (hk k).2⟩)
      (v := fun k q => E.csz (n k.1) (E.topG kmin (n k.1)) 1 q) (hr.reindex _).snd.snd kK).pair (has_jobsAt
      (J := fun k q => hlow (n k.1) (E.csz (n k.1) (E.topG kmin (n k.1)) 1 q) (v k.1 (t k.1 * E.topN kmin (n k.1) +
        E.topNU0 kmin (n k.1) * E.W + q))) (hr.reindex _).snd.fst kK fun k => (hk k).2)).cong (fun _ => rfl) fun k => ?_
    simp only [topSz, topAns, if_neg (Nat.not_lt.2 (hk k).1), Nat.add_assoc, Nat.add_sub_cancel' (hk k).1]
  · have hk : ∀ k : {k // (if j k < E.topNU0 kmin (n k) * E.W then 1 else 0) ≠ 0}, j k.1 < E.topNU0 kmin (n k.1) * E.W :=
      fun k => by have := k.2; split_ifs at this <;> simp_all
    have Sj := (hN.reindex (Subtype.val (p := fun k => (if j k < E.topNU0 kmin (n k) * E.W then 1 else 0) ≠ 0))).mono
      fun k => (hlt k.1).le
    refine (((E.knows_tq ((hj.reindex _).wmod (Can.wc E.W) Sj.mod) fun k => Nat.mod_lt _ E.W_pos).wmul
      (Can.fetch (L := fun k => Layout.std (E.topNU0 kmin (n k.1))) (i := fun k => ⟨_, (Nat.div_lt_iff_lt_mul E.W_pos).2 (hk k)⟩)
        (hU.reindex _) ((hj.reindex _).wdiv (Can.wc E.W) Sj.div)) ((hS.reindex Subtype.val).mono fun k =>
          (E.slot_le (hk k)).trans (Nat.le_add_left _ _))).pair (has_jobsAt
      (J := fun k q => hlow (n k.1) (E.slotSize (n k.1) (E.topG kmin (n k.1)) 1 q) (v k.1 (t k.1 * E.topN kmin (n k.1) + q)))
        (hr.reindex _).fst (hj.reindex _) hk)).cong (fun _ => rfl) fun k => ?_
    simp only [topSz, topAns, if_pos (hk k), slotSize]
lemma tm_rest {κ : Type U} {m : Bool} {cl : Paint} {b : Bank (portM cl) κ} {s : Ty} {x : κ → T s} (kmin : ℕ)
    {n Bv t j : κ → ℕ} {v : ∀ k, ℕ → Bits (n k) → ℂ} {tau : κ → EngJob → ℕ} (hn : Knows m b.B s x n)
    (hI : Has m b.B s sc x (fun _ => Complex.I)) (hp : Knows m b.B s x (fun k => 2^(n k)))
    (hU : Has m b.B s (a w) x (fun k => (Layout.std (E.topNU0 kmin (n k))).tape (fun p => E.cUc (n k) (E.topG kmin (n k)) 1 p)))
    (hNU : Knows m b.B s x (fun k => E.topNU0 kmin (n k))) (hj : Knows m b.B s x j)
    (hr : Has m b.B s (portOut cl) x (fun k => E.jobAnswer cl (E.topRoot kmin (n k) (Bv k) (v k) (t k))))
    (hlt : ∀ k, j k < E.topN kmin (n k)) (hS : Small b.B (fun k => (Bv k + 1) * 2^(n k))) (hNB : ∀ k, E.topN kmin (n k) ≤ Bv k)
    (hc : ∀ k, (b.use k (E.encodeJob cl (E.topRest kmin (n k) (v k) (t k) (j k)))).OK (E.jobAnswer cl (E.topRest kmin (n k) (v k) (t k) (j k)))
      (tau k (E.topRest kmin (n k) (v k) (t k) (j k))) (b.ext k)) :
    Able m b s (p w (jobsT cl)) x (fun k => (2 ^ E.topSz kmin (n k) (j k), (E.jobAnswer cl (E.topRest kmin (n k) (v k) (t k) (j k))).1))
      (fun k => 3 * 2 ^ n k) (fun k => tau k (E.topRest kmin (n k) (v k) (t k) (j k))) := by
  have S2 := hS.mono fun k => Nat.le_mul_of_pos_left (2 ^ n k) (Nat.succ_pos _)
  have X := E.tm_pick kmin hU hNU hj hr hlt (hS.mono fun k => by
    have := Nat.lt_two_pow_self (n := n k); have := hNB k; nlinarith)
  have hz := fun k => E.topSz_le kmin (n k) (j k)
  have e : ∀ k, 2 ^ E.topSz kmin (n k) (j k) * 2 ^ (n k - E.topSz kmin (n k) (j k)) = 2 ^ n k := fun k => by
    rw [← pow_add, Nat.add_sub_cancel' (hz k)]
  have hb : ∀ k q (y : Bits (n k - E.topSz kmin (n k) (j k))), q < 2 ^ E.topSz kmin (n k) (j k) →
      q + 2 ^ E.topSz kmin (n k) (j k) * (bits _).loc y < 2 ^ n k := fun k q y hq => by
    have := (bits _).bd y; have := e k; simp only [bits_len] at *; nlinarith
  have Sz := S2.mono fun k => Nat.pow_le_pow_right two_pos (hz k)
  have pz := can_powv 2 two_pos X.fst (S2.mono fun k => (hz k).trans Nat.lt_two_pow_self.le) Sz
  have L : ∀ {u : Ty} {z : κ → T u}, Has m b.B s u x z → Has m b.B (p s w) u
    (fun k => (x k, 2 ^ E.topSz kmin (n k) (j k))) z := fun h => Has.extE h
  have jobs := can_jobsTape (n := fun k => n k - E.topSz kmin (n k) (j k)) (N := fun k => 2 ^ E.topSz kmin (n k) (j k))
    (J := fun k => hiVec (n k) (E.topSz kmin (n k) (j k)) (E.topAns kmin (n k) (v k) (t k) (j k))) (cl := cl) Can.second
    (((L hp).wdiv Can.second S2.div).cong (fun _ => rfl) fun k => Nat.pow_div (hz k) two_pos) Sz
    (S2.mono fun k => Nat.pow_le_pow_right two_pos (Nat.sub_le _ _)) ((Can.fetch (L := fun d => bits (n d.1.1))
      (i := fun d => castB (Nat.add_sub_cancel' (hz d.1.1)) (catB _ _ (bitsOf _ d.1.2.val, d.2)))
      (v := fun d => E.topAns kmin (n d.1.1) (v d.1.1) (t d.1.1) (j d.1.1)) (Has.extE (Has.extE ((L X.snd).reindex _)))
      ((Can.first.snd.wadd (Can.first.fst.snd.wmul Can.second ?_) ?_).cong (fun _ => rfl) fun d => ?_)).cong (fun _ => rfl)
        fun d => by simp only [hiVec, dif_pos (hz d.1.1)])
  rotate_left
  · exact (S2.reindex _).mono fun d => (Nat.le_add_left _ _).trans (hb _ _ d.2 d.1.2.2).le
  · exact (S2.reindex _).mono fun d => (hb _ _ d.2 d.1.2.2).le
  · rw [(tm_bnd (hz _) _ _).1, bitsOf_loc, Nat.mod_eq_of_lt d.1.2.2]
  have restIn : Can m b.B (p s w) (portIn cl) (fun k => (x k, 2 ^ E.topSz kmin (n k) (j k)))
      (fun k => E.encodeJob cl (E.topRest kmin (n k) (v k) (t k) (j k))) _ := ((Has.atW ((L hn).wsub (L X.fst) (S2.mono fun k => (Nat.sub_le _ _).trans Nat.lt_two_pow_self.le))).pair
    ((Has.atW (L hI)).pair ((Can.wc 0).pair ((Can.wc 0).pair ((Can.wc 0).pair (jobs.pair
      (Has.atW (has_jobs0 _ fun _ _ _ => 0)))))))).cong (fun _ => rfl) fun _ => rfl
  refine ((Able.of_can (Can.save pz ((Has.atW Can.second).pair restIn))).comp (Able.fork (Able.first (W := fun _ => 0)
    (Z := fun _ => 0)) (Able.comp (Able.second (W := fun _ => 0) (Z := fun _ => 0)) (Able.use_call hc)).fst)).mono
    (fun k => ?_) (fun k => by simp)
  have := Nat.lt_two_pow_self (n := n k); have := Nat.pow_le_pow_right two_pos (hz k); have := hz k
  simp only [Nat.mul_add, e]; omega
lemma tm_ent {κ : Type U} {m : Bool} {B : κ → ℕ} {s : Ty} {x : κ → T s} {cl : Paint} (kmin : ℕ) {n Bv tt : κ → ℕ}
    {v : ∀ k, ℕ → Bits (n k) → ℂ} {e : ∀ k, Bits (n k)} (hN : Knows m B s x (fun k => E.topN kmin (n k)))
    (htt : Knows m B s x tt) (he : Knows m B s x (fun k => (bits (n k)).loc (e k)))
    (hA : Has m B s (a (a (p w (jobsT cl)))) x (fun k => Tape.tab (Bv k / E.topN kmin (n k)) (fun t =>
      Tape.tab (E.topN kmin (n k)) (fun j => (2 ^ E.topSz kmin (n k) j, (E.jobAnswer cl (E.topRest kmin (n k) (v k) t j)).1)))))
    (hlt : ∀ k, tt k < Bv k / E.topN kmin (n k) * E.topN kmin (n k)) (hS : Small B (fun k => (Bv k + 1) * 2^(n k))) :
    Has m B s (c cl) x (fun k => ripple (n k) (v k (tt k)) (e k)) := by
  have hpos : ∀ k, 0 < E.topN kmin (n k) := fun k => Nat.pos_of_ne_zero fun h => by have := hlt k; simp [h] at this
  have St := hS.mono fun k => ((hlt k).le.trans (Nat.div_mul_le_self _ _)).trans ((Nat.le_succ _).trans
    (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)))
  have Se := hS.mono fun k => ((bits (n k)).bd (e k)).le.trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
  have PK := ((hA.look (htt.wdiv hN St.div)).look (htt.wmod hN St.mod)).cong (fun _ => rfl) fun k => by
    rw [Tape.look_tab, if_pos ((Nat.div_lt_iff_lt_mul (hpos k)).2 (hlt k)), Tape.look_tab, if_pos (Nat.mod_lt _ (hpos k))]
  refine (has_jobsRead (J := fun k q => ripple (n k - E.topSz kmin (n k) (tt k % E.topN kmin (n k)))
    (hiVec (n k) (E.topSz kmin (n k) (tt k % E.topN kmin (n k)))
      (E.topAns kmin (n k) (v k) (tt k / E.topN kmin (n k)) (tt k % E.topN kmin (n k))) q)) PK.snd (he.wmod PK.fst Se.mod) (fun k => Nat.mod_lt _ (Nat.two_pow_pos _))
    ((he.wdiv PK.fst Se.div).cong (fun _ => rfl) fun k => ?_)).cong (fun _ => rfl) fun k => E.tree_val kmin _ (v k) (tt k) (e k)
  rw [bitsOf_loc, Nat.mod_eq_of_lt ((Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2 ?_)]
  rw [← pow_add, Nat.sub_add_cancel (E.topSz_le _ _ _)]; exact (bits (n k)).bd (e k)
lemma tm_fin {ι : Type U} {m : Bool} {B : ι → ℕ} {s : Ty} {x : ι → T s} {cl : Paint} (kmin : ℕ) {n Bv : ι → ℕ}
    {v : ∀ i, ℕ → Bits (n i) → ℂ} (hn : Knows m B s x n) (hI : Has m B s sc x (fun _ => Complex.I))
    (hp : Knows m B s x (fun i => 2^(n i))) (hinp : Has m B s (jobsT cl) x (fun i => jobsTape (n i) (Bv i) (v i)))
    (hBv : Knows m B s x Bv) (hN : Knows m B s x (fun i => E.topN kmin (n i)))
    (hA : Has m B s (a (a (p w (jobsT cl)))) x (fun i => Tape.tab (Bv i / E.topN kmin (n i)) (fun t =>
      Tape.tab (E.topN kmin (n i)) (fun j => (2 ^ E.topSz kmin (n i) j, (E.jobAnswer cl (E.topRest kmin (n i) (v i) t j)).1)))))
    (hbig : Small B (fun i => (Bv i + 1) * 2^(n i))) :
    Can m B s (jobsT cl) x (fun i => jobsTape (n i) (Bv i) (fun t => ripple (n i) (v i t))) (fun i => 0 + Bv i +
      ∑ t ∈ range (Bv i), if t < Bv i / E.topN kmin (n i) * E.topN kmin (n i) then 2 ^ n i else 2 ^ n i * (2 * n i + 1)) := by
  have S2 := hbig.mono fun i => Nat.le_mul_of_pos_left (2 ^ n i) (Nat.succ_pos _)
  have SB := hbig.mono fun i => (Nat.le_succ _).trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos (n i)))
  have SD := SB.reindex (During.i (n := Bv))
  have hN' : Knows m (fun d : During Bv => B d.i) (p s w) (fun d => (x d.i, d.j)) (fun d => E.topN kmin (n d.i)) :=
    Has.extE (hN.reindex _)
  have tree : Can m (fun k : {d : During Bv // (if d.j < Bv d.i / E.topN kmin (n d.i) * E.topN kmin (n d.i) then 1 else 0)
      ≠ 0} => B k.1.i) (p s w) (a (c cl)) (fun k => (x k.1.i, k.1.j))
      (fun k => (bits (n k.1.i)).tape (ripple (n k.1.i) (v k.1.i k.1.j))) (fun k => 2 ^ n k.1.i) := by
    refine (Can.layout (P := fun _ => 0) (Has.extE (hp.reindex _)) ?_ (S2.reindex _)).mono
      fun k => by simp
    refine E.tm_ent kmin (Has.extE (Has.extE (hN.reindex _))) Can.first.snd Can.second (Has.extE (Has.extE (hA.reindex _)))
      (fun u => ?_) (hbig.reindex _)
    have := u.1.2; split_ifs at this with h; exacts [h, absurd rfl this]
  refine (Can.tab (uB := fun i t => if t < Bv i / E.topN kmin (n i) * E.topN kmin (n i) then 2 ^ n i else 2 ^ n i * (2 * n i + 1))
    hBv (Can.testz (Has.atW (Can.second.wlt (((Has.extE (hBv.reindex _)).wdiv hN' SD.div).wmul hN' (SD.mono fun d =>
      Nat.div_mul_le_self _ _)))) ((tm_nv (Has.extE (hn.reindex _)) (Has.extE (hI.reindex _)) (Has.extE (hinp.reindex _))
        Can.second (fun k => ?_) (S2.reindex _)).mono fun k => ?_) (tree.mono fun k => ?_)) SB).cong (fun _ => rfl)
    fun i => (LumTable.tape_loc (Layout.std _) fun t => (bits (n i)).tape (ripple (n i) (v i t))).symm
  · exact k.1.hj
  · have := k.2; split_ifs at this ⊢ <;> simp_all
  · have := k.2; split_ifs at this ⊢ <;> simp_all
theorem tm_tree {ι : Type U} {m : Bool} {cl : Paint} {b : Bank (portM cl) ι} {s : Ty} {y : ι → T s}
    (kmin : ℕ) {n Bv : ι → ℕ} {v : ∀ i, ℕ → Bits (n i) → ℂ}
    (hn : Knows m b.B s y n) (hI : Has m b.B s sc y (fun _ => Complex.I))
    (hp : Knows m b.B s y (fun i => 2^(n i)))
    (hinp : Has m b.B s (jobsT cl) y (fun i => jobsTape (n i) (Bv i) (v i)))
    (hBv : Knows m b.B s y Bv) (hg : Knows m b.B s y (fun i => E.topG kmin (n i)))
    (hU : Has m b.B s (a w) y (fun i => (Layout.std (E.topNU0 kmin (n i))).tape
      (fun p => E.cUc (n i) (E.topG kmin (n i)) 1 p)))
    (hNU : Knows m b.B s y (fun i => E.topNU0 kmin (n i))) (hN : Knows m b.B s y (fun i => E.topN kmin (n i)))
    (hbig : Small b.B (fun i => (Bv i + 1) * 2^(n i))) (hNB : ∀ i, E.topN kmin (n i) ≤ Bv i)
    {tau : ι → EngJob → ℕ}
    (hroot : ∀ i t, t < Bv i / E.topN kmin (n i) →
      (b.use i (E.encodeJob cl (E.topRoot kmin (n i) (Bv i) (v i) t))).OK (E.jobAnswer cl (E.topRoot kmin (n i) (Bv i) (v i) t))
        (tau i (E.topRoot kmin (n i) (Bv i) (v i) t)) (b.ext i))
    (hrest : ∀ i t j, t < Bv i / E.topN kmin (n i) → j < E.topN kmin (n i) →
      (b.use i (E.encodeJob cl (E.topRest kmin (n i) (v i) t j))).OK (E.jobAnswer cl (E.topRest kmin (n i) (v i) t j))
        (tau i (E.topRest kmin (n i) (v i) t j)) (b.ext i)) :
    Able m b s (jobsT cl) y (fun i => jobsTape (n i) (Bv i) (fun t => ripple (n i) (v i t)))
      (fun i => (Bv i + 1) * 2^(n i) + (Bv i % E.topN kmin (n i)) * (n i + 1) * 2^(n i))
      (fun i => ∑ t ∈ range (Bv i / E.topN kmin (n i)), (tau i (E.topRoot kmin (n i) (Bv i) (v i) t) +
        ∑ j ∈ range (E.topN kmin (n i)), tau i (E.topRest kmin (n i) (v i) t j))) := by
  have S2 := hbig.mono fun i => Nat.le_mul_of_pos_left (2 ^ n i) (Nat.succ_pos _)
  have SB := hbig.mono fun i => (Nat.le_succ _).trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos (n i)))
  have SN := SB.mono hNB
  have LD : ∀ {u : Ty} {z : ι → T u}, Has m b.B s u y z → Has m (b.comap (During.i (n := fun i => Bv i / E.topN kmin (n i)))).B
      (p s w) u (fun d => (y d.i, d.j)) (fun d => z d.i) := fun h => Has.extE (h.reindex _)
  have hlt : ∀ d : During (fun i => Bv i / E.topN kmin (n i)), ∀ j < E.topN kmin (n d.i),
      d.j * E.topN kmin (n d.i) + j < Bv d.i := fun d j hj => by
    have := Nat.div_mul_le_self (Bv d.i) (E.topN kmin (n d.i)); have := d.hj; nlinarith
  have SD := SB.reindex (During.i (n := fun i => Bv i / E.topN kmin (n i)))
  have hW := (LD hNU).wmul (Can.wc E.W) ((SN.reindex _).mono fun d => Nat.le_add_right _ _)
  have own := can_jobsTape (N := fun d => E.topNU0 kmin (n d.i) * E.W) (cl := cl)
    (J := fun d j => v d.i (d.j * E.topN kmin (n d.i) + j)) hW (LD hp) ((SN.reindex _).mono fun d => Nat.le_add_right _ _)
    (S2.reindex _) (has_jobsRead (N := fun e => Bv e.1.1.i) (tt := fun (e : Σ u : UnitF (fun d : During (fun i =>
      Bv i / E.topN kmin (n i)) => E.topNU0 kmin (n d.i) * E.W), Bits (n u.1.i)) => e.1.1.j * E.topN kmin (n e.1.1.i) + e.1.2.val)
      (Has.extE (Has.extE (Has.extE (hinp.reindex _)))) ((Can.first.fst.snd.wmul (Has.extE (Has.extE ((LD hN).reindex _)))
        ((SD.reindex _).mono fun e => (Nat.le_add_right _ _).trans (hlt _ _ (e.1.2.2.trans_le (Nat.le_add_right _ _))).le)).wadd
        Can.first.snd ((SD.reindex _).mono fun e => (hlt _ _ (e.1.2.2.trans_le (Nat.le_add_right _ _))).le))
      (fun e => hlt _ _ (e.1.2.2.trans_le (Nat.le_add_right _ _))) Can.second)
  have ho : ∀ d : During (fun i => Bv i / E.topN kmin (n i)), d.j * E.topN kmin (n d.i) + E.topNU0 kmin (n d.i) * E.W ≤ Bv d.i :=
    fun d => by have := Nat.div_mul_le_self (Bv d.i) (E.topN kmin (n d.i)); have := d.hj; unfold topN at *; nlinarith
  have rootIn : Can m (b.comap (During.i (n := fun i => Bv i / E.topN kmin (n i)))).B (p s w) (portIn cl) (fun d => (y d.i, d.j))
      (fun d => E.encodeJob cl (E.topRoot kmin (n d.i) (Bv d.i) (v d.i) d.j)) _ :=
    ((Has.atW (LD hn)).pair ((Has.atW (LD hI)).pair ((Has.atW ((LD hg).wadd (Can.wc 1) ((S2.reindex _).mono fun d =>
      Nat.succ_le_of_lt ((E.topG_le _ _).trans_lt Nat.lt_two_pow_self)))).pair ((Can.wc 1).pair ((Has.atW ((Can.second.wmul (LD hN)
        (SD.mono fun d => (Nat.le_add_right _ _).trans (ho d))).wadd hW (SD.mono ho))).pair
      (own.pair (Has.atW (LD hinp)))))))).cong (fun _ => rfl) fun _ => rfl
  have root := (Able.of_can rootIn).comp (Able.use_call fun d => hroot d.i d.j d.hj)
  have hs : Able m ((b.comap (During.i (n := fun i => Bv i / E.topN kmin (n i)))).comap (During.i (n := fun d => E.topN kmin (n d.i))))
      (p (p (p s w) (portOut cl)) w) (p w (jobsT cl))
      (fun e => (((y e.i.i, e.i.j), E.jobAnswer cl (E.topRoot kmin (n e.i.i) (Bv e.i.i) (v e.i.i) e.i.j)), e.j))
      (fun e => (2 ^ E.topSz kmin (n e.i.i) e.j, (E.jobAnswer cl (E.topRest kmin (n e.i.i) (v e.i.i) e.i.j e.j)).1))
      (fun e => 3 * 2 ^ n e.i.i) (fun e => tau e.i.i (E.topRest kmin (n e.i.i) (v e.i.i) e.i.j e.j)) :=
    E.tm_rest kmin (Has.extE (Has.extE (Has.extE (hn.reindex _)))) (Has.extE (Has.extE (Has.extE (hI.reindex _))))
      (Has.extE (Has.extE (Has.extE (hp.reindex _)))) (Has.extE (Has.extE (Has.extE (hU.reindex _))))
      (Has.extE (Has.extE (Has.extE (hNU.reindex _)))) Can.second Can.first.snd (fun e => e.hj) (hbig.reindex _)
      (fun e => hNB _) (fun e => hrest e.i.i e.i.j e.j e.i.hj e.hj)
  have inner : Able m (b.comap (During.i (n := fun i => Bv i / E.topN kmin (n i)))) (p (p s w) (portOut cl))
      (a (p w (jobsT cl))) (fun d => ((y d.i, d.j), E.jobAnswer cl (E.topRoot kmin (n d.i) (Bv d.i) (v d.i) d.j)))
      (fun d => Tape.tab (E.topN kmin (n d.i)) fun j => (2 ^ E.topSz kmin (n d.i) j, (E.jobAnswer cl (E.topRest kmin (n d.i) (v d.i) d.j j)).1))
      _ _ := Able.tab (Wb := fun (d : During (fun i => Bv i / E.topN kmin (n i))) _ => 3 * 2 ^ n d.i)
        (Zb := fun (d : During (fun i => Bv i / E.topN kmin (n i))) j => tau d.i (E.topRest kmin (n d.i) (v d.i) d.j j)) (Able.of_can (W := fun _ => 0) (Has.extE (LD hN))) hs (SN.reindex _)
  have P1 := Able.tab (t := a (p w (jobsT cl))) (v := fun i t => Tape.tab (E.topN kmin (n i)) fun j =>
      (2 ^ E.topSz kmin (n i) j, (E.jobAnswer cl (E.topRest kmin (n i) (v i) t j)).1))
    (Wb := fun i _ => E.topNU0 kmin (n i) * E.W * (2 ^ n i + 1) + 0 + (0 + E.topN kmin (n i) + ∑ j ∈ range (E.topN kmin (n i)), 3 * 2 ^ n i))
    (Zb := fun i t => 0 + tau i (E.topRoot kmin (n i) (Bv i) (v i) t) + (0 + ∑ j ∈ range (E.topN kmin (n i)),
      tau i (E.topRest kmin (n i) (v i) t j))) (Able.of_can (W := fun _ => 0) (hBv.wdiv hN SB.div)) (Able.save root inner) SB.div
  refine (Able.save P1 (Able.of_can (E.tm_fin kmin (Has.extE hn) (Has.extE hI) (Has.extE hp) (Has.extE hinp)
    (Has.extE hBv) (Has.extE hN) Can.second hbig))).weaken ⟨10, fun i => ?_⟩ fun i => by simp
  have h1 := tm_ite (Bv i / E.topN kmin (n i) * E.topN kmin (n i)) (2 ^ n i) (2 ^ n i * (2 * n i + 1)) (Bv i)
  have h5 := Nat.div_add_mod' (Bv i) (E.topN kmin (n i))
  rw [show Bv i - Bv i / E.topN kmin (n i) * E.topN kmin (n i) = Bv i % E.topN kmin (n i) by omega,
    min_eq_right (Nat.div_mul_le_self _ _)] at h1
  have h2 := Nat.div_mul_le_self (Bv i) (E.topN kmin (n i))
  have h3 : E.topNU0 kmin (n i) * E.W ≤ E.topN kmin (n i) := Nat.le_add_right _ _
  have h4 := Nat.one_le_two_pow (n := n i)
  have h6 := Nat.div_le_self (Bv i) (E.topN kmin (n i))
  have h7 := Nat.le_mul_of_pos_right (Bv i) h4
  simp only [sum_const, card_range, smul_eq_mul, Nat.zero_add, Nat.add_zero] at h1 ⊢
  generalize 2 ^ n i = P at *; generalize Bv i / E.topN kmin (n i) = g at *
  generalize E.topNU0 kmin (n i) * E.W = U at *; generalize E.topN kmin (n i) = N at *
  nlinarith [Nat.mul_le_mul_right P h2, Nat.mul_le_mul_left g h3, Nat.mul_le_mul_right P (Nat.mul_le_mul_left g h3),
    Nat.zero_le (Bv i % N * n i * P), Nat.zero_le (Bv i % N * P)]
lemma naive_top {Ξ : Type U} {m : Bool} {Bd n Bv : Ξ → ℕ} {cl : Paint} {v : ∀ e, ℕ → Bits (n e) → ℂ}
    (hbig : Small Bd (fun e => (Bv e + 1) * 2^(n e))) :
    Can m Bd (portIn cl) (portOut cl) (fun e => E.encodeJob cl (EngJob.top (n e) (Bv e) (v e)))
      (fun e => E.jobAnswer cl (EngJob.top (n e) (Bv e) (v e))) (fun e => Bv e * ((n e + 1) * 2 ^ n e + 1)) :=
  have ho : Has m Bd (portIn cl) (jobsT cl) (fun e => E.encodeJob cl (EngJob.top (n e) (Bv e) (v e))) _ :=
    Can.second.snd.snd.snd.snd.fst
  have hb : Small Bd Bv := hbig.mono fun _ => (Nat.le_succ _).trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))
  ((tm_naive Can.first Can.second.fst ho (ho.len hb) hbig).pair
    (Has.atW ((has_jobs0 _ fun _ _ _ => 0).pair (has_tape0 _)))).mono fun _ => Nat.mul_le_mul_left _ (Nat.le_succ _)
lemma kids_sum (kmin n0 n B : ℕ) (v : ℕ → Bits n → ℂ) (tau : EngJob → ℕ) : ((E.kidsTop kmin n0 n B v).map tau).sum =
    if n0 ≤ n ∧ E.topN kmin n ≤ B then ∑ t ∈ range (B / E.topN kmin n), (tau (E.topRoot kmin n B v t) +
      ∑ j ∈ range (E.topN kmin n), tau (E.topRest kmin n v t j)) else 0 := by
  unfold kidsTop; split_ifs
  · generalize B / E.topN kmin n = G; induction G with
    | zero => simp
    | succ G ih => simp [List.range_succ, sum_range_succ, ih, rsum, Function.comp_def]
  · rfl
lemma tm_prep {ι : Type U} {m : Bool} {B : ι → ℕ} {s : Ty} {x : ι → T s} (kmin : ℕ) (hk : 0 < kmin) {n : ι → ℕ}
    (hn : Knows m B s x n) (hI : Has m B s sc x (fun _ => Complex.I)) (h2 : Small B (fun i => 2 ^ n i)) :
    Can m B s (p w (p w (p IdxT (p UnT w)))) x (fun i => (2 ^ n i, E.topG kmin (n i), E.idxVal (n i) (E.topG kmin (n i)) 1,
      E.unitVal (n i) (E.topG kmin (n i)) 1, E.cons (n i) (E.topG kmin (n i)) 1)) (fun i => E.Ptop kmin (n i)) := by
  have Sn := h2.mono fun i => Nat.lt_two_pow_self.le
  have c : CIn m B (p (p s w) w) (fun i => ((x i, 2 ^ n i), E.topG kmin (n i))) n (fun i => E.topG kmin (n i)) (fun _ => 1) :=
    ⟨Has.extE (Has.extE hn), Can.second, Can.wc 1, Can.first.snd, Has.extE (Has.extE hI), h2, fun i => E.topG_le _ _,
      Small.const _ 1⟩
  have c4 := (c.ext fun i => E.idxVal (n i) (E.topG kmin (n i)) 1).ext fun i => E.unitVal (n i) (E.topG kmin (n i)) 1
  refine ((can_powv 2 two_pos hn Sn h2).save ((E.can_topG kmin hk (Has.extE hn) h2).save ((E.can_index c).save
    ((E.can_units c).save ((Has.atW Can.first.fst.fst.snd).pair ((Has.atW Can.first.fst.snd).pair ((Has.atW Can.first.snd).pair
      ((Has.atW Can.second).pair (E.can_cons (fun i => E.topG_le _ _) ((c4.imag.pair c4.p2n).pair (c4.nK.pair (c4.hK.pair
        c4.μK))) (((Small.const _ (1 + 1)).mul ((h2.pow E.csK).mono fun i => (Nat.pow_le_pow_right (by unfold csK; omega)
          (E.topG_le kmin (n i))).trans ((Nat.pow_le_pow_left Nat.lt_two_pow_self.le _).trans
            (by rw [← pow_mul, ← pow_mul, mul_comm])))).mul h2)))))))))).mono fun i => by simp only [Ptop]; omega
section
variable {m : Bool}
theorem top_body (kmin n0 : ℕ) (hk : 2 ≤ kmin) (hn0 : E.mx ≤ n0) {κ : Type U} {cl : Paint}
    {b : Bank (portM cl) κ} (n Bv : κ → ℕ) (v : ∀ k, ℕ → Bits (n k) → ℂ)
    (hbig : Small b.B (fun k => (Bv k + 1) * 2^(n k))) (tau : κ → EngJob → ℕ)
    (hcalls : ∀ k c, c ∈ E.kidsTop kmin n0 (n k) (Bv k) (v k) →
      (b.use k (E.encodeJob cl c)).OK (E.jobAnswer cl c) (tau k c) (b.ext k)) :
    Able m b (portIn cl) (portOut cl) (fun k => E.encodeJob cl (EngJob.top (n k) (Bv k) (v k)))
      (fun k => E.jobAnswer cl (EngJob.top (n k) (Bv k) (v k)))
      (fun k => E.locTop kmin n0 (n k) (Bv k))
      (fun k => ((E.kidsTop kmin n0 (n k) (Bv k) (v k)).map (tau k)).sum) := by
  have nv : ∀ {Ξ : Type U} (f : Ξ → κ), (∀ e, ¬ (n0 ≤ n (f e) ∧ E.topN kmin (n (f e)) ≤ Bv (f e))) →
      (∀ e, Bv (f e) * ((n (f e) + 1) * 2 ^ n (f e) + 1) + 1 ≤ 2 * (E.locTop kmin n0 (n (f e)) (Bv (f e)) + 1)) →
      Able m (b.comap f) (portIn cl) (portOut cl) (fun e => E.encodeJob cl (EngJob.top (n (f e)) (Bv (f e)) (v (f e))))
        (fun e => E.jobAnswer cl (EngJob.top (n (f e)) (Bv (f e)) (v (f e)))) (fun e => E.locTop kmin n0 (n (f e)) (Bv (f e)))
        (fun e => ((E.kidsTop kmin n0 (n (f e)) (Bv (f e)) (v (f e))).map (tau (f e))).sum) := fun f hf hc =>
    (Able.of_can (E.naive_top (hbig.reindex f))).weaken ⟨2, hc⟩ fun e => by simp [kidsTop, if_neg (hf e)]
  refine Able.branch (Has.atW (Can.first.wlt (Can.wc n0))) (fun k => n0 ≤ n k)
    (fun k => show (if n k < n0 then 1 else 0) = 0 ↔ n0 ≤ n k by split_ifs <;> simp <;> omega)
    ?_ (nv _ (fun e h => e.2 h.1) fun e => ?_)
  · have S2 := (hbig.reindex (Subtype.val (p := fun k => n0 ≤ n k))).mono fun k => Nat.le_mul_of_pos_left (2 ^ n k.1) (Nat.succ_pos _)
    have hinp : Has m (b.comap (Subtype.val (p := fun k => n0 ≤ n k))).B (portIn cl) (jobsT cl)
        (fun k => E.encodeJob cl (EngJob.top (n k.1) (Bv k.1) (v k.1))) (fun k => jobsTape (n k.1) (Bv k.1) (v k.1)) :=
      Can.second.snd.snd.snd.snd.fst
    have hBv := hinp.len ((hbig.reindex _).mono fun k => (Nat.le_succ _).trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)))
    have Pr := E.tm_prep (m := m) (n := fun k : {k // n0 ≤ n k} => n k.1) kmin (by omega) (Can.first (v := fun k : {k // n0 ≤ n k} => E.encodeJob cl (EngJob.top (n k.1) (Bv k.1) (v k.1)))) Can.second.fst S2
    have hK : E.W ≤ (E.nB + 1) * (E.W + 1) := (Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
    have SN : Small (b.comap (Subtype.val (p := fun k => n0 ≤ n k))).B (fun k => E.topN kmin (n k.1)) :=
      ((S2.pow ((E.nB + 1) * (E.W + 1))).mul (Small.const _ (2 * ((E.nB + 1) * (E.W + 1))))).mono fun k => by
        have h1 := E.NU_le' (n k.1) (E.topG kmin (n k.1)) 1
        have h2 := E.cons_le (n k.1) (E.topG kmin (n k.1)) 1
        have h3 := Nat.pow_le_pow_left hK (E.topG kmin (n k.1))
        have h4 : ((E.nB + 1) * (E.W + 1)) ^ E.topG kmin (n k.1) ≤ (2 ^ n k.1) ^ ((E.nB + 1) * (E.W + 1)) :=
          (Nat.pow_le_pow_right (by nlinarith [E.W_pos]) (E.topG_le _ _)).trans ((Nat.pow_le_pow_left Nat.lt_two_pow_self.le _).trans
            (by rw [← pow_mul, ← pow_mul, mul_comm]))
        have h5 := Nat.one_le_pow (E.topG kmin (n k.1)) ((E.nB + 1) * (E.W + 1)) (by nlinarith [E.W_pos])
        have h6 := Nat.mul_le_mul (h1.trans h3) hK
        have h7 := Nat.mul_le_mul_right ((E.nB + 1) * (E.W + 1)) h4
        have h8 := Nat.le_mul_of_pos_right ((2 ^ n k.1) ^ ((E.nB + 1) * (E.W + 1))) (Nat.mul_pos (Nat.succ_pos E.nB) (Nat.succ_pos E.W))
        unfold topN topNU0; nlinarith
    let X := fun k : {k // n0 ≤ n k} => (E.encodeJob cl (EngJob.top (n k.1) (Bv k.1) (v k.1)), (2 ^ n k.1, E.topG kmin (n k.1),
      E.idxVal (n k.1) (E.topG kmin (n k.1)) 1, E.unitVal (n k.1) (E.topG kmin (n k.1)) 1, E.cons (n k.1) (E.topG kmin (n k.1)) 1))
    have SB := (hbig.reindex (Subtype.val (p := fun k => n0 ≤ n k))).mono fun k =>
      (Nat.le_succ _).trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos (n k.1)))
    have hN : Knows m (b.comap (Subtype.val (p := fun k => n0 ≤ n k))).B (p (portIn cl) (p w (p w (p IdxT (p UnT w))))) X
        (fun k => E.topN kmin (n k.1)) := (Can.second.snd.snd.fst.snd.fst.wmul (Can.wc E.W) (SN.mono fun k =>
          Nat.le_add_right _ _)).wadd Can.second.snd.snd.snd.snd SN
    have hB : Knows m (b.comap (Subtype.val (p := fun k => n0 ≤ n k))).B (p (portIn cl) (p w (p w (p IdxT (p UnT w))))) X
        (fun k => Bv k.1) := Can.first.snd.snd.snd.snd.snd.fst.len SB
    have br : Able m (b.comap (Subtype.val (p := fun k => n0 ≤ n k))) (p (portIn cl) (p w (p w (p IdxT (p UnT w)))))
        (portOut cl) X (fun k => E.jobAnswer cl (EngJob.top (n k.1) (Bv k.1) (v k.1)))
        (fun k => (Bv k.1 + 1) * 2 ^ n k.1 + Bv k.1 % E.topN kmin (n k.1) * (n k.1 + 1) * 2 ^ n k.1)
        (fun k => ((E.kidsTop kmin n0 (n k.1) (Bv k.1) (v k.1)).map (tau k.1)).sum) := by
      refine Able.branch (Has.atW (hB.wlt hN)) (fun k => E.topN kmin (n k.1) ≤ Bv k.1)
        (fun k => show (if Bv k.1 < E.topN kmin (n k.1) then 1 else 0) = 0 ↔ _ by split_ifs <;> simp <;> omega) ?_ ?_
      · refine ((E.tm_tree (n := fun k : {k : {k // n0 ≤ n k} // E.topN kmin (n k.1) ≤ Bv k.1} => n k.1.1)
          (Bv := fun k => Bv k.1.1) (v := fun k => v k.1.1) (y := fun k => X k.1) (s := p (portIn cl) (p w (p w (p IdxT (p UnT w))))) (cl := cl) (tau := fun k => tau k.1.1)
          (b := (b.comap Subtype.val).comap Subtype.val) kmin Can.first.fst Can.first.snd.fst Can.second.fst
          Can.first.snd.snd.snd.snd.snd.fst (hB.reindex _) Can.second.snd.fst Can.second.snd.snd.snd.fst.fst
          Can.second.snd.snd.fst.snd.fst (hN.reindex _) (hbig.reindex _) (fun k => k.2) (fun k t ht => hcalls _ _ ?_)
          (fun k t j ht hj => hcalls _ _ ?_)).fork (Able.of_can (W := fun _ => 0)
            ((has_jobs0 _ fun _ _ _ => 0).pair (has_tape0 _)))).mono (fun k => by simp) (fun k => ?_)
        · unfold kidsTop; rw [if_pos ⟨k.1.2, k.2⟩]
          exact List.mem_flatMap.2 ⟨t, List.mem_range.2 ht, List.mem_cons_self⟩
        · unfold kidsTop; rw [if_pos ⟨k.1.2, k.2⟩]
          exact List.mem_flatMap.2 ⟨t, List.mem_range.2 ht, List.mem_cons_of_mem _ (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)⟩
        · rw [kids_sum, if_pos ⟨k.1.2, k.2⟩]; simp
      · refine (Able.of_can (Has.extE (E.naive_top (hbig.reindex
          (fun k : {k : {k // n0 ≤ n k} // ¬ E.topN kmin (n k.1) ≤ Bv k.1} => k.1.1))))).weaken ⟨2, fun k => ?_⟩
          fun k => by rw [kids_sum, if_neg fun h => k.2 h.2]
        have := Nat.not_le.1 k.2; dsimp only; rw [Nat.mod_eq_of_lt this]
        have : Bv k.1.1 ≤ Bv k.1.1 * 2 ^ n k.1.1 := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
        generalize 2 ^ n k.1.1 = P at *; nlinarith
    refine (Able.save (Able.of_can Pr) br).weaken (Dom.of_le fun k => ?_) fun k => by simp
    simp only [locTop, if_pos k.2]; omega
  · have : Bv e.1 ≤ Bv e.1 * ((n e.1 + 1) * 2 ^ n e.1) := Nat.le_mul_of_pos_right _ (Nat.mul_pos (Nat.succ_pos _) (Nat.two_pow_pos _))
    simp only [locTop, if_neg e.2, Nat.mul_assoc (Bv e.1 + 1)]; generalize (n e.1 + 1) * 2 ^ n e.1 = Q at *; nlinarith
end
end BlockEngine
end
end PowerSaving.RAM
end OAI
