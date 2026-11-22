--might be  containing modified Apache-2.0 codes pieces from one or several sources; notices and credits: Credits.lean
import Submission.Engine.ClassSetup
namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset GenMove UnitClass
noncomputable section
universe U
lemma fm_count {P : ℕ → Prop} [DecidablePred P] (g : ℕ → ℕ) (N : ℕ) :
    ((List.range N).filterMap (fun t => if P t then some (g t) else none)).length = Nat.count P N ∧
    ∀ k < Nat.count P N, ((List.range N).filterMap (fun t => if P t then some (g t) else none)).getD k 0 = g (Nat.nth P k) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.filterMap_append, Nat.count_succ]
    by_cases hP : P N
    · simp only [hP, ite_true, List.filterMap_cons, List.filterMap_nil, List.length_append, ih.1, List.length_singleton, true_and]
      intro k hk
      rcases Nat.lt_or_ge k (Nat.count P N) with h | h
      · rw [DigitArith.getD_append_left _ _ _ (by rw [ih.1]; exact h), ih.2 k h]
      · obtain rfl : k = Nat.count P N := by omega
        have := DigitArith.getD_append_right ((List.range N).filterMap (fun t => if P t then some (g t) else none)) [g N] 0 0
        rw [Nat.add_zero, ih.1] at this; rw [this, Nat.nth_count hP]; rfl
    · simpa [hP] using ih
lemma CIn.ufN {ι : Type*} {m : Bool} {B : ι → ℕ} {s : Ty} {x : ι → T s} {n h μ : ι → ℕ} (c : CIn m B s x n h μ)
    (N : ι → ℕ) : CIn m (fun u : UnitF N => B u.1) (p s w) (fun u => (x u.1, u.2.val)) (fun u => n u.1) (fun u => h u.1)
      (fun u => μ u.1) := c.reindex _ _ Can.first
lemma CIn.lift {ι : Type*} {m : Bool} {B : ι → ℕ} {s t : Ty} {x : ι → T s} {n h μ : ι → ℕ} (c : CIn m B s x n h μ)
    {y : ι → T t} (g : Has m B t s y x) : CIn m B t y n h μ := c.reindex (fun i => i) y g
lemma CCtx.lift {ι : Type*} {m : Bool} {B : ι → ℕ} {s t : Ty} {x : ι → T s} {mx : ℕ} {n NU : ι → ℕ} {col ib : ι → ℕ → ℕ}
    (c : CCtx m B s x mx n NU col ib) {y : ι → T t} (g : Has m B t s y x) : CCtx m B t y mx n NU col ib :=
  c.reindex (fun i => i) y g
lemma getD3 (A B C : List ℕ) (j : ℕ) : (A ++ (B ++ C)).getD j 0 = if j < A.length then A.getD j 0 else
    if j < A.length + B.length then B.getD (j - A.length) 0 else C.getD (j - A.length - B.length) 0 := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
lemma loc_split {n k : ℕ} (hk : k ≤ n) (e : Bits n) : (bits n).loc e =
    (bits k).loc ((catB k (n-k)).symm ((castB (Nat.add_sub_cancel' hk)).symm e)).1 +
      2^k * (bits (n-k)).loc ((catB k (n-k)).symm ((castB (Nat.add_sub_cancel' hk)).symm e)).2 := by
  rw [← loc_castB_catB _ _ hk, Prod.mk.eta, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
section Kit3
variable {ι : Type*} {m : Bool} {B : ι → ℕ} {s : Ty} {x : ι → T s}
open DigitArith
namespace BitCtx
variable {f : ι → ℕ} (g : BitCtx m B f s x)
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {k : ℕ}
  (S : Split α β (Fin k)) (X : Layout α) (X' : Layout β) {r n : ι → ℕ}
  (hfit : ∀ i, k * f i + X'.n * f i + r i = n i) (hbig : Small B fun i => 2^(n i))
private lemma place_loc (i : ι) (q : Bits (r i)) (y : Sky α (f i)) :
    (bits (n i)).loc (placeS S X' (f i) (r i) (n i) (hfit i) (q, y)) =
      (bits (k * f i)).loc (S.peel 0 (f i) (0, y)).2 + 2^(k * f i) * (book X' 0 (f i)).loc (S.peel 0 (f i) (0, y)).1 +
        2^(k * f i) * 2^(X'.n * f i) * (bits (r i)).loc q := by rw [placeS_loc, pow_add]
include g hbig
lemma place_enc {q : ∀ i, Bits (r i)} {v : ∀ i, Grid α 0 (f i)}
    (hq : Knows m B s x fun i => (bits (r i)).loc (q i)) (hv : Knows m B s x fun i => (book X 0 (f i)).loc (v i)) :
    Knows m B s x fun i => (bits (n i)).loc (placeS S X' (f i) (r i) (n i) (hfit i) (q i, (v i).2)) := by
  have ev : ∀ i, v i = (0, (v i).2) := fun i => Prod.ext (Subsingleton.elim _ _) rfl
  obtain ⟨hb, ha⟩ := g.from_gridB X 0 S X' v hv
  have sm : ∀ {F : ι → ℕ}, (∀ i, F i ≤ (bits (n i)).loc (placeS S X' (f i) (r i) (n i) (hfit i) (q i, (v i).2))) →
      Small B F := fun hF => hbig.mono fun i => (hF i).trans ((bits _).bd _).le
  have P := fun i => split3_parts ((place_loc S X' hfit i (q i) (v i).2).trans (by rw [← ev])).symm
  have s2 : ∀ {F : ι → ℕ}, (∀ i, F i ≤ 2^(n i)) → Small B F := fun hF => hbig.mono hF
  have pw : ∀ i a, a ≤ n i → 2^a ≤ 2^(n i) := fun i a h => Nat.pow_le_pow_right two_pos h
  have b1 : ∀ i, 2^(k * f i) ≤ 2^(n i) := fun i => pw i _ (by have := hfit i; omega)
  have b3 : ∀ i, 2^(X'.n * f i) ≤ 2^(n i) := fun i => pw i _ (by have := hfit i; omega)
  have b2 : ∀ i, (book X' 0 (f i)).loc (S.peel 0 (f i) (v i)).1 ≤ 2^(n i) := fun i => ((book X' 0 (f i)).bd _).le.trans (by rw [book_len]; exact b3 i)
  have b4 : ∀ i, 2^(k * f i) * 2^(X'.n * f i) ≤ 2^(n i) := fun i => by rw [← pow_add]; exact pw i _ (by have := hfit i; omega)
  have b5 : ∀ i, (bits (r i)).loc (q i) ≤ 2^(n i) := fun i => ((bits (r i)).bd _).le.trans (by rw [bits_len]; exact pw i _ (by have := hfit i; omega))
  exact ((ha.plus ((g.powerB k).times hb (s2 b1) (s2 b2)) (sm fun i => (P i).1) (sm fun i => (P i).2.1)).plus
    (((g.powerB k).times (g.powerB X'.n) (s2 b1) (s2 b3)).times hq (s2 b4) (s2 b5))
    (sm fun i => (P i).2.2.2) (sm fun i => (P i).2.2.1)).cong (fun _ => rfl) fun i => by rw [place_loc, ← ev]
lemma place_dec {e : ∀ i, Bits (n i)} (he : Knows m B s x fun i => (bits (n i)).loc (e i)) :
    Knows m B s x (fun i => (bits (r i)).loc ((placeS S X' (f i) (r i) (n i) (hfit i)).symm (e i)).1) ∧
    Knows m B s x (fun i => (book X 0 (f i)).loc ((0 : Bits 0), ((placeS S X' (f i) (r i) (n i) (hfit i)).symm (e i)).2)) := by
  let u i := S.peel 0 (f i) (0, ((placeS S X' (f i) (r i) (n i) (hfit i)).symm (e i)).2)
  have E1 : ∀ i, (bits (n i)).loc (e i) = (bits (k * f i)).loc (u i).2 + 2^(k * f i) * (book X' 0 (f i)).loc (u i).1 +
      2^(k * f i) * 2^(X'.n * f i) * (bits (r i)).loc ((placeS S X' (f i) (r i) (n i) (hfit i)).symm (e i)).1 := fun i => by
    conv_lhs => rw [← (placeS S X' (f i) (r i) (n i) (hfit i)).apply_symm_apply (e i)]
    exact place_loc S X' hfit i _ _
  have hA : ∀ i, (bits (k * f i)).loc (u i).2 < 2^(k * f i) := fun i => (bits _).bd _
  have hB : ∀ i, (book X' 0 (f i)).loc (u i).1 < 2^(X'.n * f i) := fun i => by
    have := (book X' 0 (f i)).bd (u i).1; rwa [book_len] at this
  have sE : Small B fun i => (bits (n i)).loc (e i) := hbig.mono fun i => ((bits _).bd _).le
  have hP := g.powerB k; have hQ := g.powerB X'.n
  refine ⟨(he.dvdW (hP.times hQ (hbig.mono fun i => ?_) (hbig.mono fun i => ?_)) sE).cong (fun _ => rfl) fun i => by
      rw [E1, split3_div (hA i) (hB i)], (g.to_gridB X 0 S X' u (((he.dvdW hP sE).modW hQ sE.div).cong (fun _ => rfl)
      fun i => by rw [E1, split3_mid (hA i) (hB i)]) ((he.modW hP sE).cong (fun _ => rfl) fun i => by rw [E1, split3_mod (hA i)])).cong
      (fun _ => rfl) fun i => by simp only [u, Equiv.symm_apply_apply]⟩
  all_goals exact Nat.pow_le_pow_right two_pos (by have := hfit i; omega)
end BitCtx
end Kit3
namespace BlockEngine
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]
variable (E : BlockEngine α ρ σ)
lemma tq_lt_W (a : ℕ) (ha : a < E.W) : E.tq a = E.tr (E.Q.atFin ⟨a, ha⟩) := dif_pos ha

def rtCost (n h μ r : ℕ) : ℕ :=
  E.idxCost n h (μ*r) + 8*(E.W^(h+1)+1)*(E.W^(h+1)+1)*(h+3) + 8

def accR (n h μ r : ℕ) : List ℕ := E.ownSrc n h μ r ++ E.srcSizes n h (μ*r)
def blkCost (n h μ r L : ℕ) : ℕ :=
  E.rtCost n h μ r + (E.NUc n h (μ*r) * E.W + E.NUc n (h+1) μ) * 2^n +
    2*(L + (E.accR n h μ r).length) + 20
def accW (n h μ : ℕ) (ws : GWord α ρ) : List ℕ := (blockRanks ws).flatMap fun r => E.accR n h μ r

def swCost (n h μ : ℕ) : ℕ → GWord α ρ → ℕ
  | _, [] => 0
  | L, mv :: ws =>
    (match mv.rk? with
      | some r => E.blkCost n h μ r L
      | none => E.NUc n (h+1) μ * 2^n) +
    swCost n h μ (L + match mv.rk? with
      | some r => (E.accR n h μ r).length
      | none => 0) ws

def lfCost (n μ : ℕ) : GWord α ρ → ℕ
  | [] => 0
  | mv :: ws =>
    (match mv.rk? with
      | some _ => E.NUc n 0 μ * 2^n + 2*n + 2
      | none => E.NUc n 0 μ * 2^n) + lfCost n μ ws
def locUp (n h μ : ℕ) : ℕ :=
  (n+1) + E.idxCost n (h+1) μ + E.NUc n (h+1) μ * (4*n + 4*(h+1) + 8) +
    E.NUc n (h+1) μ * (2*2^n + 2) + E.NUc n (h+1) μ * 2^n + E.swCost n h μ 0 E.wd +
    E.NUc n (h+1) μ * E.W * 2^n
def locLeaf (n μ : ℕ) : ℕ :=
  (n+1) + E.idxCost n 0 μ + E.NUc n 0 μ * (4*n + 4*0 + 8) +
    E.NUc n 0 μ * (2*2^n + 2) + E.NUc n 0 μ * 2^n + E.lfCost n μ E.wd +
    E.NUc n 0 μ * E.W * 2^n

def clsLoc (n h μ : ℕ) : ℕ :=
  if h = 0 then E.locLeaf n μ else E.locUp n (h-1) μ

def Valid (kmin : ℕ) : EngJob → Prop
  | .top .. => True
  | .cls n h μ o BS _ _ =>
    1 ≤ μ ∧ E.mx * μ * kmin^h ≤ n ∧ o + E.cons n h μ ≤ BS

structure KMin (kmin : ℕ) : Prop where
  two : 2 ≤ kmin
  att : ∃ l, E.tr l = kmin
def passCost (n NU : ℕ) : ℕ := NU + NU * ((E.R.n + 1) * 2^n)
lemma ownSrc_len (n h μ r : ℕ) :
    (E.ownSrc n h μ r).length = Nat.count (E.srcP n h μ r) (E.NUc n h (μ * r) * E.W) := (fm_count _ _).1
lemma accW_cons (n h μ : ℕ) (mv : GMove α ρ) (ws : GWord α ρ) :
    E.accW n h μ (mv :: ws) = (match mv.rk? with | some r => E.accR n h μ r | none => []) ++ E.accW n h μ ws := by
  unfold accW blockRanks; rw [List.filterMap_cons]; cases mv.rk? <;> rfl
lemma wd_block {l : ρ} {r : ℕ} {z : Fin r → Space α} {ind : LinearIndependent F z}
    (hm : GMove.old (BMove.block l r z ind) ∈ E.wd) : 1 ≤ r ∧ r < E.X.n :=
  (GMove.proper_iff _ _).1 (E.hP _ hm) r rfl
lemma kidsUp_free {n h μ BS : ℕ} {sup : ℕ → Bits n → ℂ} {mv : GMove α ρ} (h0 : mv.rk? = none)
    (V : E.CState n (h+1) μ) (o : ℕ) (ws : GWord α ρ) :
    E.kidsUp n h μ BS sup V o (mv :: ws) = E.kidsUp n h μ BS sup (E.stepV V mv) o ws := by
  rcases mv with ((_|_|_)|_|_|_) <;> first | rfl | cases h0
lemma kidsLeaf_free {n μ : ℕ} {mv : GMove α ρ} (h0 : mv.rk? = none) (V : E.CState n 0 μ) (ws : GWord α ρ) :
    E.kidsLeaf n μ V (mv :: ws) = E.kidsLeaf n μ (E.stepV V mv) ws := by
  rcases mv with ((_|_|_)|_|_|_) <;> first | rfl | cases h0
lemma kidsUp_valid {kmin : ℕ} (hk : E.KMin kmin) {n h μ BS : ℕ} {sup : ℕ → Bits n → ℂ}
    (hμ : 1 ≤ μ) (hn : E.mx * μ * kmin ^ (h+1) ≤ n) :
    ∀ (ws : GWord α ρ), (∀ mv ∈ ws, mv ∈ E.wd) → ∀ (V : E.CState n (h+1) μ) (o : ℕ),
      o + (E.accW n h μ ws).length ≤ BS → ∀ c ∈ E.kidsUp n h μ BS sup V o ws, E.Valid kmin c := by
  intro ws
  induction ws with
  | nil => intro _ _ _ _ c hc; cases hc
  | cons mv ws ih =>
    intro hw V o hfit c hc
    rw [accW_cons, List.length_append] at hfit
    rcases GMove.rk_cases mv with h0 | ⟨l, r, z, ind, rfl⟩
    · rw [h0, List.length_nil, Nat.zero_add] at hfit
      rw [E.kidsUp_free h0] at hc; exact ih (fun m hm => hw m (.tail _ hm)) _ _ hfit c hc
    · have hr := E.wd_block (hw _ (.head _))
      simp only [kidsUp, dif_pos hr.2.le, List.singleton_append, List.mem_cons] at hc
      simp only [GMove.rk_block, accR, List.length_append] at hfit
      rcases hc with rfl | hc
      · obtain ⟨l0, hl0⟩ := hk.att
        have hrk : r < kmin := hl0 ▸ E.sep _ (hw _ (.head _)) r rfl l0
        refine ⟨Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), le_trans ?_ hn, by unfold cons; omega⟩
        calc _ = E.mx * μ * kmin ^ h * r := by ring
          _ ≤ E.mx * μ * kmin ^ h * kmin := Nat.mul_le_mul_left _ hrk.le
          _ = _ := by ring
      · exact ih (fun m hm => hw m (.tail _ hm)) _ _ (by unfold cons; omega) c hc
theorem kidsC_valid {kmin : ℕ} (hk : E.KMin kmin) (d : EngJob) (hd : E.Valid kmin d) :
    ∀ c ∈ E.childJobs d, E.Valid kmin c := by
  intro c hc
  match d, hd, hc with
  | .top _ _ _, _, hc => cases hc
  | .cls n 0 μ o BS J sup, _, hc =>
    suffices ∀ (ws : GWord α ρ) V, c ∈ E.kidsLeaf n μ V ws → E.Valid kmin c from this _ _ hc
    intro ws; induction ws with
    | nil => intro _ h; cases h
    | cons mv ws ih =>
      intro V h
      rcases GMove.rk_cases mv with h0 | ⟨l, r, z, ind, rfl⟩
      · exact ih _ (E.kidsLeaf_free h0 V ws ▸ h)
      · simp only [kidsLeaf, List.mem_append] at h
        refine h.elim (fun h => ?_) (ih _)
        split_ifs at h with hr
        · simp only [List.mem_singleton] at h; subst h; unfold exitC; split_ifs <;> trivial
        · cases h
  | .cls n (h+1) μ o BS J sup, hd, hc => exact E.kidsUp_valid hk hd.1 hd.2.1 E.wd (fun _ h => h) _ o hd.2.2 c hc
lemma valid_facts {kmin : ℕ} (hk : E.KMin kmin) {n h μ o BS : ℕ} {J sup : ℕ → Bits n → ℂ}
    (hd : E.Valid kmin (EngJob.cls n h μ o BS J sup)) :
    (h = 0 → E.X.n * μ ≤ n) ∧ h ≤ n ∧ μ ≤ n ∧ o + E.cons n h μ ≤ BS := by
  obtain ⟨h1, h2, h3⟩ := hd
  have hm : 1 ≤ kmin ^ h := Nat.one_le_pow _ _ (by have := hk.two; omega)
  have h4 : μ ≤ E.mx * μ * kmin ^ h :=
    (Nat.le_mul_of_pos_left μ (show 0 < E.X.n by have := E.three; omega)).trans (Nat.le_mul_of_pos_right _ hm)
  refine ⟨fun e => by subst e; simpa using h2, ?_, h4.trans h2, h3⟩
  have : h < 2 ^ h := Nat.lt_two_pow_self
  have : 2 ^ h ≤ kmin ^ h := Nat.pow_le_pow_left hk.two h
  have : kmin ^ h ≤ E.mx * μ * kmin ^ h := Nat.le_mul_of_pos_left _ (by have := E.three; positivity)
  omega
lemma pass_le (n NU : ℕ) : E.passCost n NU ≤ (E.R.n + 2) * (NU * 2^n) := by
  unfold passCost; have := Nat.le_mul_of_pos_right NU (Nat.two_pow_pos n)
  calc _ ≤ NU * 2^n + NU * ((E.R.n + 1) * 2^n) := by omega
    _ = _ := by ring
lemma blk_bound (n h μ r L : ℕ) (Wsum : ℕ)
    (hW : Wsum ≤ E.idxCost n h (μ * r) +
      (0 + E.NUc n h (μ * r) * E.W + E.NUc n h (μ * r) * E.W * (h + 2)) +
      (0 + E.NUc n h (μ * r) * E.W + E.NUc n h (μ * r) * E.W * (E.NUc n h (μ * r) * E.W + 1)) +
      (E.NUc n h (μ * r) * E.W * (0 + 1) + 1) +
      E.NUc n h (μ * r) * E.W * (2^n + 1) +
      E.passCost n (E.NUc n (h+1) μ) +
      (0 + (E.ownSrc n h μ r).length + (E.ownSrc n h μ r).length * (E.NUc n h (μ * r) * E.W * (0 + 1) + 1 + 0)) +
      (0 + (E.ownSrc n h μ r).length + (E.ownSrc n h μ r).length *
        (E.NUc n h (μ * r) * E.W * (0 + 1) + 1 + (h + 1))) +
      2 * (L + (E.accR n h μ r).length + 1)) :
    Wsum ≤ (E.R.n + 41) * E.blkCost n h μ r L := by
  simp only [Nat.zero_add, Nat.mul_one, Nat.add_zero] at hW
  have hA : E.NUc n h (μ * r) * E.W ≤ E.W^(h+1) := by rw [pow_succ]; exact Nat.mul_le_mul_right _ (E.NU_le' _ _ _)
  have hL : (E.ownSrc n h μ r).length ≤ E.NUc n h (μ * r) * E.W := by rw [ownSrc_len]; exact Nat.count_le _
  have hL2 : (E.ownSrc n h μ r).length ≤ (E.accR n h μ r).length := by simp [accR]
  have hN := Nat.le_mul_of_pos_right (E.NUc n (h+1) μ) (Nat.two_pow_pos n)
  have hX : E.NUc n (h+1) μ * 2^n ≤ E.blkCost n h μ r L := by unfold blkCost; rw [Nat.add_mul]; omega
  have := Nat.mul_le_mul_left E.R.n hX
  unfold blkCost rtCost passCost at *
  generalize E.NUc n h (μ * r) * E.W = A at *
  generalize (E.ownSrc n h μ r).length = L1 at *
  generalize E.W^(h+1) = K at *
  generalize E.NUc n (h+1) μ = N at *
  generalize E.idxCost n h (μ * r) = I at *
  have k1 : (K+1)*(K+1) ≤ (K+1)*(K+1)*(h+3) := Nat.le_mul_of_pos_right _ (by omega)
  have k2 : A * (A + 1) ≤ (K+1)*(K+1) := Nat.mul_le_mul (by omega) (by omega)
  have k3 : K + 1 ≤ (K+1)*(K+1) := Nat.le_mul_of_pos_right _ (by omega)
  have : A * (h + 2) ≤ (K+1)*(K+1)*(h+3) := Nat.mul_le_mul (by omega) (by omega)
  have : L1 * (A + 1) ≤ (K+1)*(K+1) := Nat.mul_le_mul (by omega) (by omega)
  have : L1 * (h + 1) ≤ (K+1)*(K+1)*(h+3) := Nat.mul_le_mul (by omega) (by omega)
  have : L1 * (A + 1 + (h + 1)) = L1 * (A + 1) + L1 * (h + 1) := Nat.mul_add ..
  have e1 : (A + N) * 2^n = A * 2^n + N * 2^n := Nat.add_mul ..
  have e2 : N * ((E.R.n + 1) * 2^n) = E.R.n * (N * 2^n) + N * 2^n := by ring
  have e3 : 8 * (K + 1) * (K + 1) * (h + 3) = 8 * ((K+1)*(K+1)*(h+3)) := by ring
  have e4 : A * (2^n + 1) = A * 2^n + A := by ring
  rw [Nat.add_mul E.R.n 41]
  omega
lemma cost_close (n NU L W : ℕ) (hNL : NU * 2^n ≤ L) (hW : W ≤ 6 * L + E.passCost n NU) :
    W ≤ (E.R.n + 8) * L := by
  have := E.pass_le n NU; have := Nat.mul_le_mul_left (E.R.n + 2) hNL
  calc W ≤ 6 * L + (E.R.n + 2) * L := by omega
    _ = _ := by ring
lemma free_dom (n NU S : ℕ) : E.passCost n NU + S ≤ (E.R.n + 3) * (NU * 2^n + S) := by
  have := E.pass_le n NU
  calc _ ≤ (E.R.n + 2) * (NU * 2^n) + S := by omega
    _ ≤ (E.R.n + 2) * (NU * 2^n) + NU * 2^n + (E.R.n + 3) * S := by
        have := Nat.le_mul_of_pos_left S (show 0 < E.R.n + 3 by omega); omega
    _ = _ := by ring
end BlockEngine
abbrev SwT (s : Ty) (cl : Paint) : Ty := p s (p (ctabT cl) (p (jobsT cl) (a w)))
def accA (n : ℕ) (acc : List ℕ) (o : ℕ) (sup : ℕ → Bits n → ℂ) : Tape (Tape ℂ) :=
  jobsTape n acc.length (fun k => hlow n (acc.getD k 0) (sup (o + k)))
def accZ (acc : List ℕ) : Tape ℕ := (Layout.std acc.length).tape (fun k => acc.getD k 0)
namespace BlockEngine
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]
variable (E : BlockEngine α ρ σ)
def tabV {ι : Type*} (n h μ : ι → ℕ) (V : ∀ i, E.CState (n i) (h i) (μ i)) (i : ι) : Tape (Tape (Tape ℂ)) :=
  ctab E.X E.R (E.NUc (n i) (h i) (μ i)) (fun p => E.cUc (n i) (h i) (μ i) p) (fun p => E.iUc (n i) (h i) (μ i) p) (V i)
abbrev Ctx {ι : Type U} (m : Bool) (B : ι → ℕ) (s : Ty) (y : ι → T s) (n h μ : ι → ℕ) : Prop :=
  CCtx m B s y E.X.n n (fun i => E.NUc (n i) (h i) (μ i)) (fun i p => E.cUc (n i) (h i) (μ i) p)
    (fun i p => E.iUc (n i) (h i) (μ i) p)
section Tab
variable {ι : Type U} {m : Bool} {B : ι → ℕ} {s : Ty} {y : ι → T s} {n h μ : ι → ℕ} {cl : Paint}
abbrev InstE (n h μ : ι → ℕ) := InstF (fun i => E.NUc (n i) (h i) (μ i)) (fun i p => E.iUc (n i) (h i) (μ i) p)
abbrev ElemF (n h μ : ι → ℕ) :=
  Σ v : E.InstE n h μ,
    Beach α ρ 0 (E.cUc (n v.1.1) (h v.1.1) (μ v.1.1) v.1.2)
abbrev instEnv (y : ι → T s) (v : E.InstE n h μ) : T (p (p s w) w) :=
  ((y v.1.1, v.1.2.val), (bits (E.iUc (n v.1.1) (h v.1.1) (μ v.1.1) v.1.2)).loc v.2)
abbrev elemEnv (y : ι → T s) (d : E.ElemF n h μ) : T (p (p (p s w) w) w) :=
  (E.instEnv y d.1, (fleet E.X E.R 0 (E.cUc (n d.1.1.1) (h d.1.1.1) (μ d.1.1.1) d.1.1.2)).loc d.2)
lemma elH {t : Ty} {z : ι → T t} (hz : Has m B s t y z) :
    Has m (fun d : E.ElemF n h μ => B d.1.1.1) (p (p (p s w) w) w) t (E.elemEnv y) (fun d => z d.1.1.1) :=
  Can.first.fst.fst.then_do (hz.reindex _)
lemma elGear (cx : E.Ctx m B s y n h μ) : BitCtx m (fun d : E.ElemF n h μ => B d.1.1.1)
    (fun d => E.cUc (n d.1.1.1) (h d.1.1.1) (μ d.1.1.1) d.1.1.2) (p (p (p s w) w) w) (E.elemEnv y) :=
  cx.gearU.descend (fun d : E.ElemF n h μ => d.1.1) _ Can.first.fst
lemma elPQ : Knows m (fun d : E.ElemF n h μ => B d.1.1.1) (p (p (p s w) w) w) (E.elemEnv y) (fun d => (d.1.1.2 : ℕ)) ∧
    Knows m (fun d : E.ElemF n h μ => B d.1.1.1) (p (p (p s w) w) w) (E.elemEnv y)
      (fun d => (bits (E.iUc (n d.1.1.1) (h d.1.1.1) (μ d.1.1.1) d.1.1.2)).loc d.1.2) := ⟨Can.first.fst.snd, Can.first.snd⟩
lemma elRG (cx : E.Ctx m B s y n h μ) :
    Knows m (fun d : E.ElemF n h μ => B d.1.1.1) (p (p (p s w) w) w) (E.elemEnv y) (fun d => E.R.loc d.2.1) ∧
    Knows m (fun d : E.ElemF n h μ => B d.1.1.1) (p (p (p s w) w) w) (E.elemEnv y)
      (fun d => (book E.X 0 (E.cUc (n d.1.1.1) (h d.1.1.1) (μ d.1.1.1) d.1.1.2)).loc d.2.2) :=
  ⟨Can.addr_high Can.second ((E.elGear cx).grid_size E.X 0) ((Small.const _ E.R.n).mul ((E.elGear cx).grid_small E.X 0)),
   Can.addr_low Can.second ((E.elGear cx).grid_size E.X 0) ((Small.const _ E.R.n).mul ((E.elGear cx).grid_small E.X 0))⟩
lemma can_tabEl (cx : E.Ctx m B s y n h μ) {V : ∀ i, E.CState (n i) (h i) (μ i)}
    (hel : Has m (fun d : E.ElemF n h μ => B d.1.1.1) (p (p (p s w) w) w) (Ty.c cl) (E.elemEnv y)
      (fun d => V d.1.1.1 d.1.1.2 d.1.2 d.2)) :
    Can m B s (ctabT cl) y (fun i => E.tabV n h μ V i) (fun i => E.passCost (n i) (E.NUc (n i) (h i) (μ i))) := by
  have g := cx.gearU.descend (fun v : E.InstE n h μ => v.1) (E.instEnv y) Can.first
  refine can_ctab E.X E.R (P := fun i => (E.R.n + 1) * 2^(n i)) cx.nuK cx.nuS cx.p2ibU cx.p2ibS (fun u => ?_)
    ((Can.layout (P := fun _ => 0) ((Can.wc _).times (g.grid_size E.X 0) (Small.const _ _) (g.grid_small E.X 0)) (Has.atW hel)
      ((Small.const _ _).mul (g.grid_small E.X 0))).mono fun v => by simp [fleet, Layout.pair])
  have := cx.unit_size E.X E.R rfl u.1 u.2; have := cx.pow_ib_le u.1 u.2; rw [fleet_n] at *; rw [Nat.succ_mul]; omega
lemma elemRig (cx : E.Ctx m B s y n h μ) {V : ∀ i, E.CState (n i) (h i) (μ i)}
    (ht : Has m B s (ctabT cl) y (fun i => E.tabV n h μ V i)) :
    GRig m (fun d : E.ElemF n h μ => B d.1.1.1) (fun d => E.cUc (n d.1.1.1) (h d.1.1.1) (μ d.1.1.1) d.1.1.2)
      (p (p (p s w) w) w) (E.elemEnv y) cl E.X E.R 0 (fun d => V d.1.1.1 d.1.1.2 d.1.2) := by
  have g : BitCtx m (fun d : E.ElemF n h μ => B d.1.1.1) (fun d => E.cUc (n d.1.1.1) (h d.1.1.1) (μ d.1.1.1) d.1.1.2)
      (p (p (p s w) w) w) (E.elemEnv y) := cx.gearU.descend (fun d : E.ElemF n h μ => d.1.1) _ Can.first.fst
  have t : Has m (fun d : E.ElemF n h μ => B d.1.1.1) (p (p (p s w) w) w) (ctabT cl) (E.elemEnv y)
      (fun d => E.tabV n h μ V d.1.1.1) := Can.first.fst.fst.then_do (ht.reindex _)
  unfold tabV at t
  have i1 : Has m (fun d : E.ElemF n h μ => B d.1.1.1) (p (p (p s w) w) w) sc (E.elemEnv y) (fun _ => Complex.I) := Can.first.fst.fst.then_do (cx.imag.reindex _)
  have it : Has m (fun d : E.ElemF n h μ => B d.1.1.1) (p (p (p s w) w) w) (a (c cl)) (E.elemEnv y)
      (fun d => (fleet E.X E.R 0 (E.cUc (n d.1.1.1) (h d.1.1.1) (μ d.1.1.1) d.1.1.2)).tape (V d.1.1.1 d.1.1.2 d.1.2)) :=
    has_ctabInst E.X E.R (fun d : E.ElemF n h μ => d.1.1.2) (fun d => d.1.2) t Can.first.fst.snd Can.first.snd
  have lu : Has m (fun d : E.ElemF n h μ => B d.1.1.1) (p (p (p s w) w) w) (a sc) (E.elemEnv y)
      (fun d => (bits (E.cUc (n d.1.1.1) (h d.1.1.1) (μ d.1.1.1) d.1.1.2)).tape (fun z => lum z)) :=
    Can.first.fst.then_do (cx.lumU.reindex (fun d : E.ElemF n h μ => d.1.1))
  exact ⟨⟨g, i1, it⟩, lu⟩
lemma can_free (cx : E.Ctx m B s y n h μ) {mv : GMove α ρ} (h0 : mv.rk? = none) (V : ∀ i, E.CState (n i) (h i) (μ i)) :
    Can m B (p s (ctabT cl)) (ctabT cl) (fun i => (y i, E.tabV n h μ V i))
      (fun i => E.tabV n h μ (fun i => E.stepV (V i) mv) i) (fun i => E.passCost (n i) (E.NUc (n i) (h i) (μ i))) := by
  have R := E.elemRig (cl := cl) (V := V) (cx.ext (t := ctabT cl) (fun i => E.tabV n h μ V i)) Can.second
  refine E.can_tabEl (cx.ext _) ?_
  rcases mv with ((M|⟨l, z⟩|⟨l, r, z, ind⟩)|⟨l, G⟩|⟨l, z, c'⟩|⟨gr, gi⟩)
  · exact R.rig.ferry_point M (fun d => d.2) Can.second
  · exact R.rig.ferry_shift l z (fun d => d.2) Can.second
  · cases h0
  · exact R.rig.ferry_perm l G (fun d => d.2) Can.second
  · exact R.ferry_phase l z c' (fun d => d.2) Can.second
  · exact R.rig.ferry_pointG gr gi (fun d => d.2) Can.second
lemma can_roleSet (cx : E.Ctx m B s y n h μ) {V V' : ∀ i, E.CState (n i) (h i) (μ i)} (l : ρ)
    (ht : Has m B s (ctabT cl) y (fun i => E.tabV n h μ V i))
    (hV : ∀ i (p : Fin (E.NUc (n i) (h i) (μ i))) q (b : Beach α ρ 0 (E.cUc (n i) (h i) (μ i) p)), b.1 ≠ l → V' i p q b = V i p q b)
    (hl : Has m (fun d : {d : E.ElemF n h μ // d.2.1 = l} => B d.1.1.1.1) (p (p (p s w) w) w) (c cl) (fun d => E.elemEnv y d.1)
      (fun d => V' d.1.1.1.1 d.1.1.1.2 d.1.1.2 d.1.2)) :
    Can m B s (ctabT cl) y (fun i => E.tabV n h μ V' i) (fun i => E.passCost (n i) (E.NUc (n i) (h i) (μ i))) := by
  have R := (E.elemRig cx ht).rig
  refine E.can_tabEl cx (Can.cases_code E.R (R.addrs _ Can.second).1 fun l' => ?_)
  by_cases e : l' = l
  · subst e; exact hl
  · exact ((Can.fetch R.items Can.second).reindex Subtype.val).cong (fun _ => rfl) fun d => (hV _ _ _ _ fun h' => e (d.2.symm.trans h')).symm
def unl {n h μ : ℕ} (V : E.CState n h μ) (t : ℕ) : Bits n → ℂ := fun e =>
  if ht : t / E.W < E.NUc n h μ then
    V ⟨t / E.W, ht⟩ ((E.placeT n h μ ⟨t / E.W, ht⟩ (E.Q.atFin ⟨t % E.W, Nat.mod_lt _ E.W_pos⟩)).symm e).1
      (E.e (E.Q.atFin ⟨t % E.W, Nat.mod_lt _ E.W_pos⟩),
        (0, ((E.placeT n h μ ⟨t / E.W, ht⟩ (E.Q.atFin ⟨t % E.W, Nat.mod_lt _ E.W_pos⟩)).symm e).2))
  else 0
lemma unl_run {n h μ : ℕ} (J : ℕ → Bits n → ℂ) (t : ℕ) (ht : t < E.NUc n h μ * E.W) :
    E.unl (E.runV (E.V0 n h μ J) E.wd) t = hlow n (E.slotSize n h μ t) (J t) := by
  funext e
  have hp : t / E.W < E.NUc n h μ := (Nat.div_lt_iff_lt_mul E.W_pos).2 ht
  have hl := Nat.mod_lt t E.W_pos
  have ht' : t / E.W * E.W + E.Q.loc (E.Q.atFin ⟨t % E.W, hl⟩) = t := by
    rw [Layout.loc_atFin]; exact Nat.div_add_mod' t E.W
  unfold unl; rw [dif_pos hp]
  obtain ⟨⟨q, y⟩, rfl⟩ := (E.placeT n h μ ⟨t / E.W, hp⟩ (E.Q.atFin ⟨t % E.W, hl⟩)).surjective e
  simp only [Equiv.symm_apply_apply]
  unfold slotSize; rw [E.tq_lt_W _ hl]
  change gwalk _ E.wd _ _ _ = _
  rw [E.hw _ _ (fun s hs => by funext j; simp [V0, E.liveOf_none s hs]) _]
  unfold placeT
  rw [hlow_placeS, ← blockMat_eq_lift _ _ (E.St_spec _)]
  simp only [V0, E.liveOf_e, ht']; rfl
lemma can_load (cx : E.Ctx m B s y n h μ) {J : ∀ i, ℕ → Bits (n i) → ℂ}
    (hJ : Has m B s (jobsT cl) y (fun i => jobsTape (n i) (E.NUc (n i) (h i) (μ i) * E.W) (J i))) :
    Can m B s (ctabT cl) y (fun i => E.tabV n h μ (fun i => E.V0 (n i) (h i) (μ i) (J i)) i)
      (fun i => E.passCost (n i) (E.NUc (n i) (h i) (μ i))) := by
  refine E.can_tabEl cx ?_
  have g : BitCtx m (fun d : E.ElemF n h μ => B d.1.1.1) (fun d => E.cUc (n d.1.1.1) (h d.1.1.1) (μ d.1.1.1) d.1.1.2)
      (p (p (p s w) w) w) (E.elemEnv y) := cx.gearU.descend (fun d : E.ElemF n h μ => d.1.1) _ Can.first.fst
  have sb := (Small.const _ E.R.n).mul (g.grid_small E.X 0)
  have hq : Knows m (fun d : E.ElemF n h μ => B d.1.1.1) _ (E.elemEnv y)
    fun d => (bits (E.iUc (n d.1.1.1) (h d.1.1.1) (μ d.1.1.1) d.1.1.2)).loc d.1.2 := Can.first.snd
  refine Can.cases_code E.R (Can.addr_high Can.second (g.grid_size E.X 0) sb) fun l' => ?_
  cases hl : E.liveOf l' with
  | none => exact Can.zero.cong (fun _ => rfl) fun d => by simp only [V0, d.2, hl]
  | some l =>
    have hp : Knows m (fun d : E.ElemF n h μ => B d.1.1.1) _ (E.elemEnv y) fun d => (d.1.1.2 : ℕ) * E.W + E.Q.loc l :=
      (Can.first.fst.snd.times (Can.wc E.W) ((cx.nuS.reindex _).mono fun (d : E.ElemF n h μ) => d.1.1.2.2.le) (Small.const _ _)).plus
        (Can.wc _) ((cx.nuS.mul (Small.const _ E.W)).reindex _ |>.mono fun (d : E.ElemF n h μ) => Nat.mul_le_mul_right _ d.1.1.2.2.le)
        (Small.const _ _)
    exact (has_jobsRead (J := fun d : {d : E.ElemF n h μ // d.2.1 = l'} => J d.1.1.1.1)
      ((E.elH (n := n) (h := h) (μ := μ) hJ).reindex Subtype.val) (hp.reindex Subtype.val)
      (fun d => DigitArith.lt_join d.1.1.1.2.2 (E.Q.bd l))
      ((g.descend Subtype.val _ Can.id).place_enc (q := fun d => d.1.1.2) (E.St l) E.X (E.Xt l) (fun d => fitk (E.Xt l) (E.Xt_n l) (E.fitc _ _ _ _))
        (cx.big.reindex fun d : {d : E.ElemF n h μ // d.2.1 = l'} => d.1.1.1.1) (hq.reindex Subtype.val)
        ((Can.addr_low Can.second (g.grid_size E.X 0) sb).reindex Subtype.val))).cong (fun _ => rfl)
      fun d => by obtain ⟨d, hd⟩ := d; simp only [V0, hd, hl]; rfl
lemma can_unload (cx : E.Ctx m B s y n h μ) (V : ∀ i, E.CState (n i) (h i) (μ i)) :
    Can m B (p s (ctabT cl)) (jobsT cl) (fun i => (y i, E.tabV n h μ V i))
      (fun i => jobsTape (n i) (E.NUc (n i) (h i) (μ i) * E.W) (E.unl (V i)))
      (fun i => E.NUc (n i) (h i) (μ i) * E.W * 2^(n i) + E.NUc (n i) (h i) (μ i) * E.W) := by
  let D := Σ u : UnitF (fun i => E.NUc (n i) (h i) (μ i) * E.W), Bits (n u.1)
  let yD (d : D) : T (p (p (p s (ctabT cl)) w) w) := (((y d.1.1, E.tabV n h μ V d.1.1), d.1.2.val), (bits (n d.1.1)).loc d.2)
  have sN := cx.nuS.mul (Small.const B E.W)
  have hp : ∀ d : D, (d.1.2 : ℕ) / E.W < E.NUc (n d.1.1) (h d.1.1) (μ d.1.1) := fun d => (Nat.div_lt_iff_lt_mul E.W_pos).2 d.1.2.2
  have st : Small (fun d : D => B d.1.1) fun d => (d.1.2 : ℕ) := (sN.reindex _).mono fun d => d.1.2.2.le
  have ht : Knows m (fun d : D => B d.1.1) _ yD fun d => (d.1.2 : ℕ) := Can.first.snd
  have hpk : Knows m (fun d : D => B d.1.1) _ yD fun d => (d.1.2 : ℕ) / E.W := ht.dvdW (Can.wc _) st
  have he : Knows m (fun d : D => B d.1.1) _ yD fun d => (bits (n d.1.1)).loc d.2 := Can.second
  have g := cx.gearU.descend (fun d : D => (⟨d.1.1, ⟨_, hp d⟩⟩ : UnitF _)) yD (Can.first.fst.fst.pair hpk)
  have hT : Has m (fun d : D => B d.1.1) _ (ctabT cl) yD fun d => E.tabV n h μ V d.1.1 := Can.first.fst.snd
  unfold tabV at hT
  refine (can_jobsTape ((cx.ext _).nuK.times (Can.wc E.W) (cx.nuS) (Small.const _ _)) (cx.ext _).p2n sN cx.big ?_).mono
    fun i => by rw [Nat.mul_succ]
  refine Can.cases_code E.Q (q := fun d : D => E.Q.atFin ⟨(d.1.2 : ℕ) % E.W, Nat.mod_lt _ E.W_pos⟩)
    ((ht.modW (Can.wc E.W) st).cong (fun _ => rfl) fun d => by rw [Layout.loc_atFin]) fun l => ?_
  have dec := (g.descend Subtype.val _ Can.id).place_dec (E.St l) E.X (E.Xt l)
    (fun d => fitk (E.Xt l) (E.Xt_n l) (E.fitc _ _ _ _)) (cx.big.reindex fun d : {d : D // E.Q.atFin ⟨(d.1.2 : ℕ) % E.W, Nat.mod_lt _ E.W_pos⟩ = l} => d.1.1.1)
    (e := fun d => d.1.2) (he.reindex Subtype.val)
  let K := {d : D // E.Q.atFin ⟨(d.1.2 : ℕ) % E.W, Nat.mod_lt _ E.W_pos⟩ = l}
  have g' := g.descend (Subtype.val : K → D) _ Can.id
  have hb : Knows m (fun d : K => B d.1.1.1) _ (fun d => yD d.1) fun d =>
      (fleet E.X E.R 0 (E.cUc (n d.1.1.1) (h d.1.1.1) (μ d.1.1.1) ((d.1.1.2 : ℕ) / E.W))).loc
        (E.e l, ((0 : Bits 0), ((E.placeT (n d.1.1.1) (h d.1.1.1) (μ d.1.1.1) ⟨_, hp d.1⟩ l).symm d.1.2).2)) :=
    Can.addr_join (Can.wc (E.R.loc (E.e l))) dec.2 (g'.grid_size E.X 0) (Small.const _ _) (g'.grid_small E.X 0)
  have r := has_ctabRead E.X E.R (fun d : K => ⟨_, hp d.1⟩)
    (fun d => ((E.placeT (n d.1.1.1) (h d.1.1.1) (μ d.1.1.1) ⟨_, hp d.1⟩ l).symm d.1.2).1)
    (fun d => (E.e l, ((0 : Bits 0), ((E.placeT (n d.1.1.1) (h d.1.1.1) (μ d.1.1.1) ⟨_, hp d.1⟩ l).symm d.1.2).2)))
    (hT.reindex Subtype.val) (hpk.reindex Subtype.val) dec.1 hb
  exact r.cong (fun _ => rfl) fun d => by obtain ⟨d, hd⟩ := d; simp only [unl, dif_pos (hp d), hd]
abbrev preEnv (cl : Paint) (n hh μ o : ι → ℕ) (own sp : ι → Tape (Tape ℂ)) (i : ι) : T (ClsT (p (portIn cl) w)) :=
  ((((mkIn cl (n i) (hh i + 1) (μ i) (o i) (own i) (sp i), 2^(n i)), E.idxVal (n i) (hh i) (μ i)),
    E.unitVal (n i) (hh i) (μ i)), E.gearVal (n i) (hh i) (μ i))
lemma cin_port {n hh μ o : ι → ℕ} {own sp : ι → Tape (Tape ℂ)} (hB2 : Small B fun i => 2^(n i))
    (hle : ∀ i, hh i ≤ n i) (hμ : ∀ i, μ i ≤ n i) :
    CIn m B (p (portIn cl) w) (fun i => (mkIn cl (n i) (hh i + 1) (μ i) (o i) (own i) (sp i), 2^(n i))) n hh μ :=
  have sn : Small B n := hB2.mono fun i => Nat.lt_two_pow_self.le
  ⟨Has.extE Can.first, Has.extE ((Can.second.snd.fst.minus (Can.wc 1) ((sn.add (Small.const _ 1)).mono fun i => by
    simp only [mkIn]; have := hle i; omega)).cong (fun _ => rfl) fun i => Nat.add_sub_cancel ..),
    Has.extE Can.second.snd.snd.fst, Can.second, Has.extE Can.second.fst, hB2, hle, sn.mono hμ⟩
lemma cin_pre {n hh μ o : ι → ℕ} {own sp : ι → Tape (Tape ℂ)} (hB2 : Small B fun i => 2^(n i))
    (hle : ∀ i, hh i ≤ n i) (hμ : ∀ i, μ i ≤ n i) :
    CIn m B (ClsT (p (portIn cl) w)) (E.preEnv cl n hh μ o own sp) n hh μ ∧
    E.Ctx m B (ClsT (p (portIn cl) w)) (E.preEnv cl n hh μ o own sp) n hh μ :=
  ⟨(cin_port hB2 hle hμ).lift Can.first.fst.fst, E.cctx (cin_port hB2 hle hμ)⟩
lemma can_prefix {n hh μ o : ι → ℕ} {own sp : ι → Tape (Tape ℂ)} (hB2 : Small B fun i => 2^(n i))
    (hle : ∀ i, hh i ≤ n i) (hμ : ∀ i, μ i ≤ n i) :
    Can m B (portIn cl) (ClsT (p (portIn cl) w)) (fun i => mkIn cl (n i) (hh i + 1) (μ i) (o i) (own i) (sp i))
      (E.preEnv cl n hh μ o own sp)
      (fun i => (n i + 1) + E.idxCost (n i) (hh i) (μ i) + E.NUc (n i) (hh i) (μ i) * (4 * n i + 4 * hh i + 8) +
        E.NUc (n i) (hh i) (μ i) * (2 * 2^(n i) + 2)) := by
  have c := cin_port (m := m) (o := o) (own := own) (sp := sp) (cl := cl) hB2 hle hμ
  exact (((Can.id (W := fun _ => 0)).fork (can_powv 2 two_pos Can.first (hB2.mono fun i => Nat.lt_two_pow_self.le) hB2)).pipe
    (((Can.id (W := fun _ => 0)).fork (E.can_index c)).pipe (((Can.id (W := fun _ => 0)).fork (E.can_units c)).pipe
      ((Can.id (W := fun _ => 0)).fork (E.can_gears c))))).mono fun i => by simp only [Nat.zero_add, mkIn]; omega
lemma exitC_eq {n μ : ℕ} (V : E.CState n 0 μ) (l : ρ) {r : ℕ} (z : Fin r → Space α) (ind : LinearIndependent F z)
    (hr : r ≤ E.X.n) (hk : r * μ ≤ n) :
    E.exitC n μ V l r z ind hr = EngJob.top (r * μ) (E.NUc n 0 μ * 2^(n - r * μ))
      (toVec n (r * μ) hk (exJobs E.X (bS z ind) (bX (α := α) r) (E.bX_n hr) l (E.fitc n 0 μ) V)) := dif_pos hk
lemma cU_zero (n μ : ℕ) (p : ℕ) : E.cUc n 0 μ p = μ := Nat.mul_one μ
lemma slotR_spec {n h μ r : ℕ} (hsep : ∀ l, r < E.tr l) (p : Fin (E.NUc n (h+1) μ)) :
    E.slotR n h μ r p < E.NUc n h (μ * r) * E.W ∧ E.fedP n h μ r (E.slotR n h μ r p) ∧
      E.ppR n h μ r (E.slotR n h μ r p) = p ∧
      E.slotSize n h (μ * r) (E.slotR n h μ r p) = r * E.cUc n (h+1) μ p := by
  obtain ⟨⟨hu, hfit⟩, -, hpc⟩ := U_spec p.2
  have ha : E.Uc n (h+1) μ p % E.W < E.W := Nat.mod_lt _ E.W_pos
  have hin : inRS E.W E.tq E.mx n h (μ * r) (E.Uc n (h+1) μ p / E.W) := by
    refine ⟨Nat.div_lt_of_lt_mul (by rwa [pow_succ, Nat.mul_comm] at hu), le_trans ?_ hfit⟩
    rw [colS_succ]; have := (E.tq_lt_W _ ha ▸ hsep (E.Q.atFin ⟨_, ha⟩)).le
    exact Nat.mul_le_mul_left _ (by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ this))
  have e1 := DigitArith.div_join (a := E.PCc n h (μ * r) (E.Uc n (h+1) μ p / E.W)) ha
  have e2 := DigitArith.mod_join (a := E.PCc n h (μ * r) (E.Uc n (h+1) μ p / E.W)) ha
  have hU : E.Uc n h (μ * r) (E.PCc n h (μ * r) (E.Uc n (h+1) μ p / E.W)) = E.Uc n (h+1) μ p / E.W := U_PC hin
  have hpar : E.parCode n h μ r (E.slotR n h μ r p) = E.Uc n (h+1) μ p := by
    unfold parCode slotR; rw [e1, e2, hU]; exact Nat.mod_add_div _ _
  have hlt := DigitArith.lt_join (PC_lt hin) ha
  refine ⟨hlt, ⟨hlt, hpar ▸ ⟨hu, hfit⟩⟩, by unfold ppR; rw [hpar]; exact hpc, ?_⟩
  unfold slotSize slotR; rw [e1, e2]
  simp only [cU, hU, colS_succ]; ring
abbrev cjobF (n h μ : ℕ) (sup : ℕ → Bits n → ℂ) (V : E.CState n (h+1) μ) (o : ℕ) (l : ρ) {r : ℕ}
    (z : Fin r → Space α) (ind : LinearIndependent F z) (hr : r ≤ E.X.n) : ℕ → Bits n → ℂ :=
  cjob E.X (bS z ind) (bX (α := α) r) (E.bX_n hr) l (E.fitc n (h+1) μ) V (E.flR n h μ r) (E.ppR n h μ r)
    (E.siR n h μ r o) (E.ppR_lt n h μ r) sup
def plB (n h μ : ℕ) {r : ℕ} (z : Fin r → Space α) (ind : LinearIndependent F z) (hr : r ≤ E.X.n) (p : Fin (E.NUc n h μ)) :=
  placeS (bS z ind) (bX r) _ _ n (fitk (bX r) (E.bX_n hr) (E.fitc n h μ p))
end Tab
universe V
section Slots
variable {ι : Type V} {m : Bool} {B B' : ι → ℕ} {s : Ty} {x : ι → T s} {n h μ : ι → ℕ} {r : ℕ} {cl : Paint}
  {V : ∀ i, E.CState (n i) (h i + 1) (μ i)}
lemma fetchU {n h μ q : ι → ℕ} (hidx : Has m B s IdxT x (fun i => E.idxVal (n i) (h i) (μ i))) (hq : Knows m B s x q)
    (hlt : ∀ i, q i < E.NUc (n i) (h i) (μ i)) : Knows m B s x fun i => E.Uc (n i) (h i) (μ i) (q i) :=
  Can.fetch (L := fun i => Layout.std (E.NUc (n i) (h i) (μ i))) (t := w) (v := fun i (p : Fin (E.NUc (n i) (h i) (μ i))) => E.Uc (n i) (h i) (μ i) p)
    (i := fun i => ⟨q i, hlt i⟩) (hidx.snd.snd.snd : Has m B s (a w) x fun i =>
      (Layout.std (E.NUc (n i) (h i) (μ i))).tape fun p => E.Uc (n i) (h i) (μ i) p) hq
lemma fetchPC {n h μ q : ι → ℕ} (hidx : Has m B s IdxT x (fun i => E.idxVal (n i) (h i) (μ i))) (hq : Knows m B s x q)
    (hlt : ∀ i, q i < E.W ^ h i) : Knows m B s x fun i => E.PCc (n i) (h i) (μ i) (q i) :=
  Can.fetch (L := fun i => Layout.std (E.W ^ h i)) (t := w) (v := fun i (t : Fin (E.W ^ h i)) => E.PCc (n i) (h i) (μ i) t)
    (i := fun i => ⟨q i, hlt i⟩) (hidx.snd.snd.fst : Has m B s (a w) x fun i =>
      (Layout.std (E.W ^ h i)).tape fun t => E.PCc (n i) (h i) (μ i) t) hq
lemma sNUW (ci : CIn m B s x n (fun i => h i + 1) μ) : Small B fun i => E.NUc (n i) (h i) (μ i * r) * E.W :=
  (ci.powS E.W).mono fun i => by rw [pow_succ]; exact Nat.mul_le_mul_right _ (E.NU_le' _ _ _)
lemma kNUW (ci : CIn m B s x n (fun i => h i + 1) μ) (hidx' : Has m B s IdxT x (fun i => E.idxVal (n i) (h i) (μ i * r))) :
    Knows m B s x fun i => E.NUc (n i) (h i) (μ i * r) * E.W :=
  (hidx'.snd.fst : Knows m B s x fun i => E.NUc (n i) (h i) (μ i * r)).times (Can.wc E.W)
    ((E.sNUW ci).mono fun _ => Nat.le_mul_of_pos_right _ E.W_pos) (Small.const _ _)
abbrev itV (n h μ : ℕ) (r : ℕ) : Tape ℕ :=
  (Layout.std (E.NUc n h (μ * r) * E.W)).tape fun t => if inRS E.W E.tq E.mx n (h+1) μ (E.parCode n h μ r t) then 1 else 0
structure BlkCore (m : Bool) (B : ι → ℕ) (s : Ty) (x : ι → T s) (n h μ : ι → ℕ) (r : ℕ) : Prop where
  ci : CIn m B s x n (fun i => h i + 1) μ
  idx' : Has m B s IdxT x (fun i => E.idxVal (n i) (h i) (μ i * r))
structure BlkSrc (m : Bool) (B : ι → ℕ) (s : Ty) (x : ι → T s) (n h μ : ι → ℕ) (r : ℕ) : Prop
    extends E.BlkCore m B s x n h μ r where
  IT : Has m B s (a w) x (fun i => E.itV (n i) (h i) (μ i) r)
structure BlkCls (m : Bool) (B : ι → ℕ) (s : Ty) (x : ι → T s) (n h μ : ι → ℕ) (r : ℕ) (cl : Paint)
    (V : ∀ i, E.CState (n i) (h i + 1) (μ i)) : Prop extends E.BlkCore m B s x n h μ r where
  c : E.Ctx m B s x n (fun i => h i + 1) μ
  idx : Has m B s IdxT x (fun i => E.idxVal (n i) (h i + 1) (μ i))
  tb : Has m B s (ctabT cl) x (fun i => E.tabV n (fun i => h i + 1) μ V i)
structure BlkCx (m : Bool) (B : ι → ℕ) (s : Ty) (x : ι → T s) (n h μ : ι → ℕ) (r : ℕ) (cl : Paint)
    (V : ∀ i, E.CState (n i) (h i + 1) (μ i)) : Prop extends E.BlkSrc m B s x n h μ r, E.BlkCls m B s x n h μ r cl V
lemma BlkCx.lift {E : BlockEngine α ρ σ} {V : ∀ i, E.CState (n i) (h i + 1) (μ i)} (K : E.BlkCx m B s x n h μ r cl V) {t : Ty}
    {y : ι → T t} (g : Has m B t s y x) : E.BlkCx m B t y n h μ r cl V :=
  { ci := K.ci.lift g, c := K.c.lift g, idx := g.then_do K.idx, idx' := g.then_do K.idx', IT := g.then_do K.IT, tb := g.then_do K.tb }
lemma knows_parCode (ci : CIn m B s x n (fun i => h i + 1) μ)
    (hidx' : Has m B s IdxT x (fun i => E.idxVal (n i) (h i) (μ i * r))) {t : ι → ℕ} (tK : Knows m B s x t)
    (ht : ∀ i, t i < E.NUc (n i) (h i) (μ i * r) * E.W) :
    Knows m B s x (fun i => E.parCode (n i) (h i) (μ i) r (t i)) ∧
      ∀ i, E.parCode (n i) (h i) (μ i) r (t i) < E.W^(h i + 1) := by
  have hq : ∀ i, t i / E.W < E.NUc (n i) (h i) (μ i * r) := fun i => (Nat.div_lt_iff_lt_mul E.W_pos).2 (ht i)
  have hlt : ∀ i, E.parCode (n i) (h i) (μ i) r (t i) < E.W^(h i + 1) :=
    fun i => lt_of_cons E.W (h i) _ _ (Nat.mod_lt _ E.W_pos) (U_lt (hq i))
  have S := ci.powS E.W
  have sm : ∀ {F : ι → ℕ}, (∀ i, F i ≤ E.parCode (n i) (h i) (μ i) r (t i)) → Small B F :=
    fun hF => S.mono fun i => (hF i).trans (hlt i).le
  have st : Small B t := S.mono fun i => (ht i).le.trans (by rw [pow_succ]; exact Nat.mul_le_mul_right _ (E.NU_le' _ _ _))
  refine ⟨((tK.modW (Can.wc E.W) st).plus ((Can.wc E.W).times (E.fetchU hidx' (tK.dvdW (Can.wc E.W) st) hq) (Small.const _ _)
      (S.mono fun i => (U_lt (hq i)).le.trans (Nat.pow_le_pow_right E.W_pos (Nat.le_succ (h i))))) (sm fun i => ?_) (sm fun i => ?_)).cong
    (fun _ => rfl) fun i => rfl, hlt⟩
  all_goals unfold parCode; omega
lemma can_IT (ci : CIn m B s x n (fun i => h i + 1) μ)
    (hidx : Has m B s IdxT x (fun i => E.idxVal (n i) (h i + 1) (μ i)))
    (hidx' : Has m B s IdxT x (fun i => E.idxVal (n i) (h i) (μ i * r))) :
    Can m B s (a w) x (fun i => E.itV (n i) (h i) (μ i) r)
      (fun i => 0 + E.NUc (n i) (h i) (μ i * r) * E.W + E.NUc (n i) (h i) (μ i * r) * E.W * (h i + 2)) := by
  have c' := ci.ufN fun i => E.NUc (n i) (h i) (μ i * r) * E.W
  have pc := E.knows_parCode c' (Has.liftE Sigma.fst hidx') (t := fun d => d.2.val) Can.second (fun d => d.2.2)
  exact Can.layout (L := fun i => Layout.std (E.NUc (n i) (h i) (μ i * r) * E.W)) (P := fun i => h i + 2) (E.kNUW ci hidx')
    (E.knows_inR c' pc.1 ((c'.powS E.W).mono fun d => (pc.2 d).le)
      (Has.liftE Sigma.fst (hidx.fst : Knows m B s x fun i => E.W ^ (h i + 1)))) (E.sNUW ci)
lemma srcInd {T : ι → ℕ} (hIT : Has m B s (a w) x (fun i => E.itV (n i) (h i) (μ i) r))
    (hTl : ∀ i, T i ≤ E.NUc (n i) (h i) (μ i * r) * E.W) :
    Has m (fun d : During T => B d.i) (p s w) w (fun d => (x d.i, d.j))
      (fun d => if E.srcP (n d.i) (h d.i) (μ d.i) r d.j then 1 else 0) :=
  ((Can.wc 1).wsub (Can.fetch (L := fun d : During T => Layout.std (E.NUc (n d.i) (h d.i) (μ d.i * r) * E.W))
    (i := fun d => ⟨d.j, d.hj.trans_le (hTl d.i)⟩) (Has.liftE During.i hIT)
    (Can.second : Knows m (fun d : During T => B d.i) (p s w) (fun d => (x d.i, d.j)) fun d => d.j))
    ((Small.const _ 1).mono fun _ => Nat.sub_le _ _)).cong (fun _ => rfl) fun d => by
    have := d.hj.trans_le (hTl d.i)
    by_cases hc : inRS E.W E.tq E.mx (n d.i) (h d.i + 1) (μ d.i) (E.parCode (n d.i) (h d.i) (μ d.i) r d.j) <;> simp [srcP, hc, this]
lemma can_cntSrc {T : ι → ℕ} (hIT : Has m B s (a w) x (fun i => E.itV (n i) (h i) (μ i) r))
    (hT : Knows m B s x T) (hTs : Small B T) (hTl : ∀ i, T i ≤ E.NUc (n i) (h i) (μ i * r) * E.W) :
    Can m B s w x (fun i => Nat.count (E.srcP (n i) (h i) (μ i) r) (T i)) (fun i => T i * (0 + 1) + 1) := can_count hT hTs (E.srcInd hIT hTl)
lemma can_nthSrc {T q : ι → ℕ} (hIT : Has m B s (a w) x (fun i => E.itV (n i) (h i) (μ i) r))
    (hT : Knows m B s x T) (hTs : Small B T) (hTl : ∀ i, T i ≤ E.NUc (n i) (h i) (μ i * r) * E.W)
    (hq : Knows m B s x q) (hqc : ∀ i, q i < Nat.count (E.srcP (n i) (h i) (μ i) r) (T i)) :
    Can m B s w x (fun i => Nat.nth (E.srcP (n i) (h i) (μ i) r) (q i)) (fun i => T i * (0 + 1) + 1) := (can_nthc hT hTs hq (E.srcInd hIT hTl)).cong (fun _ => rfl) fun i => if_pos (hqc i)
abbrev ctV (n h μ : ℕ) (r : ℕ) : Tape ℕ :=
  (Layout.std (E.NUc n h (μ * r) * E.W)).tape fun t => Nat.count (E.srcP n h μ r) t.val
lemma can_CT (K : E.BlkSrc m B s x n h μ r) :
    Can m B s (a w) x (fun i => E.ctV (n i) (h i) (μ i) r)
      (fun i => 0 + E.NUc (n i) (h i) (μ i * r) * E.W +
        E.NUc (n i) (h i) (μ i * r) * E.W * (E.NUc (n i) (h i) (μ i * r) * E.W + 1)) :=
  Can.layout (L := fun i => Layout.std (E.NUc (n i) (h i) (μ i * r) * E.W))
    (P := fun i => E.NUc (n i) (h i) (μ i * r) * E.W + 1) (E.kNUW K.ci K.idx')
    ((E.can_cntSrc (Has.liftE Sigma.fst K.IT) Can.second (((E.sNUW K.ci).reindex _).mono fun d => d.2.2.le) fun d => d.2.2.le).mono
      fun d => by have := d.2.2; simp only [Layout.std] at *; omega) (E.sNUW K.ci)
lemma can_OJ (K : E.BlkCx m B s x n h μ r cl V)
    (hCT : Has m B s (a w) x (fun i => E.ctV (n i) (h i) (μ i) r))
    {BS o : ι → ℕ} {sup : ∀ i, ℕ → Bits (n i) → ℂ} (hsup : Has m B s (jobsT cl) x (fun i => jobsTape (n i) (BS i) (sup i)))
    (ho : Knows m B s x o) (hBS : Small B BS) (hfit : ∀ i, o i + Nat.count (E.srcP (n i) (h i) (μ i) r) (E.NUc (n i) (h i) (μ i * r) * E.W) ≤ BS i)
    (l : ρ) (z : Fin r → Space α) (ind : LinearIndependent F z) (hr : r ≤ E.X.n) :
    Can m B s (jobsT cl) x (fun i => jobsTape (n i) (E.NUc (n i) (h i) (μ i * r) * E.W)
      (E.cjobF (n i) (h i) (μ i) (sup i) (V i) (o i) l z ind hr)) (fun i => E.NUc (n i) (h i) (μ i * r) * E.W * 2^(n i)) := by
  let N := fun i => E.NUc (n i) (h i) (μ i * r) * E.W
  let D := Σ u : UnitF N, Bits (n u.1)
  let yD (d : D) : T (p (p s w) w) := ((x d.1.1, d.1.2.val), (bits (n d.1.1)).loc d.2)
  have L : ∀ {t : Ty} {z : ι → T t}, Has m B s t x z → Has m (fun d : D => B d.1.1) _ t yD (fun d => z d.1.1) :=
    fun hz => Can.first.fst.then_do (hz.reindex _)
  have ht : Knows m (fun d : D => B d.1.1) _ yD fun d => (d.1.2 : ℕ) := Can.first.snd
  have he : Knows m (fun d : D => B d.1.1) _ yD fun d => (bits (n d.1.1)).loc d.2 := Can.second
  refine Can.jobsTable _ (E.kNUW K.ci K.idx') K.ci.p2n (E.sNUW K.ci) K.ci.big ?_
  let fd (d : D) : ℕ := if inRS E.W E.tq E.mx (n d.1.1) (h d.1.1 + 1) (μ d.1.1)
      (E.parCode (n d.1.1) (h d.1.1) (μ d.1.1) r d.1.2) then 1 else 0
  have hI : Knows m (fun d : D => B d.1.1) _ yD fd :=
    Can.fetch (L := fun d : D => Layout.std (N d.1.1)) (i := fun d => d.1.2) (L K.IT) ht
  refine Can.testz hI ?_ ?_
  · have hsrc : ∀ d : {d : D // fd d = 0}, E.srcP (n d.1.1.1) (h d.1.1.1) (μ d.1.1.1) r d.1.1.2 :=
      fun d => ⟨d.1.1.2.2, fun h' => absurd d.2 (by simp [fd, h'])⟩
    have hc : Knows m (fun d : D => B d.1.1) _ yD fun d => Nat.count (E.srcP (n d.1.1) (h d.1.1) (μ d.1.1) r) d.1.2 :=
      Can.fetch (L := fun d : D => Layout.std (N d.1.1)) (i := fun d => d.1.2) (L hCT) ht
    have hl : ∀ d : {d : D // fd d = 0}, o d.1.1.1 + Nat.count (E.srcP (n d.1.1.1) (h d.1.1.1) (μ d.1.1.1) r) d.1.1.2 < BS d.1.1.1 :=
      fun d => (Nat.add_lt_add_left (count_lt_of_mem (hsrc d) d.1.1.2.2) _).trans_le (hfit _)
    refine (has_jobsRead ((L hsup).reindex Subtype.val) (((L ho).plus hc ((hBS.reindex _).mono fun d => ?_)
      ((hBS.reindex _).mono fun d => ?_)).reindex Subtype.val) hl (he.reindex Subtype.val)).cong (fun _ => rfl) fun d => ?_
    · have := hfit d.1.1; omega
    · have := hfit d.1.1; have := Nat.count_monotone (E.srcP (n d.1.1) (h d.1.1) (μ d.1.1) r)
        (show (d.1.2 : ℕ) ≤ E.NUc (n d.1.1) (h d.1.1) (μ d.1.1 * r) * E.W from d.1.2.2.le); omega
    · have : E.flR (n d.1.1.1) (h d.1.1.1) (μ d.1.1.1) r d.1.1.2 = 0 := if_neg fun h' => (hsrc d).2 h'.2
      simp only [cjobF, cjob, this, ne_eq, not_true_eq_false, dite_false, siR]
  · let D' := {d : D // fd d ≠ 0}
    have hin : ∀ d : D', inRS E.W E.tq E.mx (n d.1.1.1) (h d.1.1.1 + 1) (μ d.1.1.1)
        (E.parCode (n d.1.1.1) (h d.1.1.1) (μ d.1.1.1) r d.1.1.2) := fun d => by_contra fun h' => d.2 (if_neg h')
    have pc := E.knows_parCode (K.ci.reindex (fun d : D => d.1.1) yD Can.first.fst) (L K.idx') ht (fun d => d.1.2.2)
    have hp := (E.fetchPC (L K.idx) pc.1 pc.2).reindex (Subtype.val : D' → D)
    have hpl : ∀ d : D', E.ppR (n d.1.1.1) (h d.1.1.1) (μ d.1.1.1) r d.1.1.2 < E.NUc (n d.1.1.1) (h d.1.1.1 + 1) (μ d.1.1.1) :=
      fun d => PC_lt (hin d)
    have g := K.c.gearU.descend (fun d : D' => (⟨d.1.1.1, ⟨_, hpl d⟩⟩ : UnitF _)) (fun d => yD d.1) (((L Can.id).reindex Subtype.val).pair hp)
    have dec := g.place_dec (bS z ind) E.X (bX r) (fun d => fitk (bX r) (E.bX_n hr) (E.fitc _ _ _ _))
      (K.ci.big.reindex fun d : D' => d.1.1.1) (e := fun d => d.1.2) (he.reindex Subtype.val)
    have hT := L K.tb
    unfold tabV at hT
    have hb : Knows m (fun d : D' => B d.1.1.1) _ (fun d => yD d.1) fun d =>
        (fleet E.X E.R 0 (E.cUc (n d.1.1.1) (h d.1.1.1 + 1) (μ d.1.1.1) (E.ppR (n d.1.1.1) (h d.1.1.1) (μ d.1.1.1) r d.1.1.2))).loc
        (l, ((0 : Bits 0), (E.plB _ _ _ z ind hr ⟨_, hpl d⟩ |>.symm d.1.2).2)) :=
      Can.addr_join (Can.wc (E.R.loc l)) dec.2 (g.grid_size E.X 0) (Small.const _ _) (g.grid_small E.X 0)
    refine (has_ctabRead E.X E.R (fun d : D' => ⟨_, hpl d⟩) _ (fun d => (l, ((0 : Bits 0), _))) (hT.reindex Subtype.val) hp dec.1 hb).cong
      (fun _ => rfl) fun d => ?_
    have : E.flR (n d.1.1.1) (h d.1.1.1) (μ d.1.1.1) r d.1.1.2 ≠ 0 := by
      have : (d.1.1.2 : ℕ) < E.NUc (n d.1.1.1) (h d.1.1.1) (μ d.1.1.1 * r) * E.W := d.1.1.2.2
      simp [flR, fedP, hin d, this]
    simp only [cjobF, cjob, dif_pos this]; rfl
lemma scat_eq {n h μ r : ℕ} (hsep : ∀ l, r < E.tr l) (sup : ℕ → Bits n → ℂ) (V : E.CState n (h+1) μ) (o : ℕ) (l : ρ)
    (z : Fin r → Space α) (ind : LinearIndependent F z) (hr : r ≤ E.X.n) (p : Fin (E.NUc n (h+1) μ))
    (q : Bits (E.iUc n (h+1) μ p)) (y : Sky α (E.cUc n (h+1) μ p)) :
    hlow n (E.slotSize n h (μ * r) (E.slotR n h μ r p)) (E.cjobF n h μ sup V o l z ind hr (E.slotR n h μ r p))
      (E.plB n (h+1) μ z ind hr p (q, y)) = matAct _ (blockMat z) (fun j => V p q (l, 0, j)) y := by
  obtain ⟨-, hf, hpp, hsz⟩ := E.slotR_spec hsep p
  have hfl : E.flR n h μ r (E.slotR n h μ r p) ≠ 0 := by simp [flR, hf]
  rw [hsz]; unfold cjobF cjob; rw [dif_pos hfl]
  have key : ∀ (a : ℕ) (ha : a < E.NUc n (h+1) μ), a = p.val →
      hlow n (r * E.cUc n (h+1) μ p) (blockJob (bS z ind) (bX r) (E.cUc n (h+1) μ a) (E.iUc n (h+1) μ a) n
        (fitk (bX r) (E.bX_n hr) (E.fitc n (h+1) μ ⟨a, ha⟩)) l (V ⟨a, ha⟩))
        (E.plB n (h+1) μ z ind hr p (q, y)) = matAct _ (blockMat z) (fun j => V p q (l, 0, j)) y := by
    rintro a ha rfl
    rw [plB, hlow_placeS, ← blockMat_eq_lift _ _ (bS_spec z ind)]; simp only [blockJob_placeS]
  exact key _ _ hpp
lemma exit_eq {n μ r : ℕ} (V : E.CState n 0 μ) (l : ρ) (z : Fin r → Space α) (ind : LinearIndependent F z)
    (hr : r ≤ E.X.n) (hk : r * μ ≤ n) (p : Fin (E.NUc n 0 μ)) (q : Bits (E.iUc n 0 μ p)) (y : Sky α (E.cUc n 0 μ p)) :
    fromVec n (r * μ) hk (fun t => ripple (r * μ) (toVec n (r * μ) hk
      (exJobs E.X (bS z ind) (bX r) (E.bX_n hr) l (E.fitc n 0 μ) V) t)) p
      (E.plB n 0 μ z ind hr p (q, y)) = matAct _ (blockMat z) (fun j => V p q (l, 0, j)) y := by
  rw [fromVec_ripple]; unfold exJobs cjob; rw [dif_pos (by simp [exFl, p.2])]
  rw [plB, show r * μ = r * E.cUc n 0 μ p by rw [cU_zero], hlow_placeS, ← blockMat_eq_lift _ _ (bS_spec z ind)]
  congr 1; funext j; exact blockJob_placeS _ _ _ _ _ _ _ _ _ _
lemma can_scatter (K : E.BlkCls m B s x n h μ r cl V)
    {sup : ∀ i, ℕ → Bits (n i) → ℂ} {o : ι → ℕ} (l : ρ) (z : Fin r → Space α) (ind : LinearIndependent F z)
    (hr : r ≤ E.X.n) (hsep : ∀ l, r < E.tr l)
    (hout : Has m B s (jobsT cl) x (fun i => jobsTape (n i) (E.NUc (n i) (h i) (μ i * r) * E.W)
      (fun t => hlow (n i) (E.slotSize (n i) (h i) (μ i * r) t) (E.cjobF (n i) (h i) (μ i) (sup i) (V i) (o i) l z ind hr t)))) :
    Can m B s (ctabT cl) x (fun i => E.tabV n (fun i => h i + 1) μ (fun i => E.stepV (V i) (.old (.block l r z ind))) i)
      (fun i => E.passCost (n i) (E.NUc (n i) (h i + 1) (μ i))) := by
  refine E.can_roleSet K.c l K.tb (fun i p q b hb => by simp [stepV, gferry, GMove.act, BMove.act, roleAct, hb]) ?_
  have g := E.elGear K.c
  obtain ⟨hp, hq⟩ := E.elPQ (m := m) (B := B) (y := x) (n := n) (h := fun i => h i + 1) (μ := μ)
  have hg := (E.elRG K.c).2
  have hU := E.fetchU (E.elH (n := n) (h := fun i => h i + 1) (μ := μ) K.idx) hp
    fun d => (d.1.1.2.2 : (d.1.1.2 : ℕ) < E.NUc (n d.1.1.1) (h d.1.1.1 + 1) (μ d.1.1.1))
  have hu : ∀ d : E.ElemF n (fun i => h i + 1) μ, E.Uc (n d.1.1.1) (h d.1.1.1 + 1) (μ d.1.1.1) d.1.1.2 < E.W ^ (h d.1.1.1 + 1) :=
    fun d => U_lt d.1.1.2.2
  have S := (K.ci.powS E.W).reindex fun d : E.ElemF n (fun i => h i + 1) μ => d.1.1.1
  have hsl := (((E.fetchPC (E.elH (n := n) (h := fun i => h i + 1) (μ := μ) K.idx') (hU.dvdW (Can.wc E.W) (S.mono fun d => (hu d).le)) fun d =>
    Nat.div_lt_of_lt_mul (by rw [← pow_succ']; exact hu d)).times (Can.wc E.W) ?_ (Small.const _ _)).plus
    (hU.modW (Can.wc E.W) (S.mono fun d => (hu d).le)) ?_ ?_).cong (fun _ => rfl) fun d => (rfl : _ = E.slotR _ _ _ r _)
  · refine ((has_jobsRead (E.elH (n := n) (h := fun i => h i + 1) (μ := μ) hout) hsl (fun d => (E.slotR_spec hsep d.1.1.2).1)
      (g.place_enc (bS z ind) E.X (bX r) (fun d => fitk (bX r) (E.bX_n hr) (E.fitc _ _ _ _))
        (K.ci.big.reindex fun d : E.ElemF n (fun i => h i + 1) μ => d.1.1.1) hq hg)).reindex Subtype.val).cong (fun _ => rfl)
      fun d => ?_
    obtain ⟨d, hd⟩ := d
    have : d.2.2.1 = 0 := Subsingleton.elim _ _
    erw [E.scat_eq hsep]; simp [stepV, gferry, GMove.act, BMove.act, roleAct, hd, this]
  all_goals refine S.mono fun d => ?_; have := hu d; have := (E.slotR_spec hsep d.1.1.2).1
  all_goals have := Nat.mul_le_mul_right E.W (E.NU_le' (n d.1.1.1) (h d.1.1.1) (μ d.1.1.1 * r))
  all_goals have : E.PCc (n d.1.1.1) (h d.1.1.1) (μ d.1.1.1 * r) (E.Uc (n d.1.1.1) (h d.1.1.1 + 1) (μ d.1.1.1) d.1.1.2 / E.W)
        ≤ E.Uc (n d.1.1.1) (h d.1.1.1 + 1) (μ d.1.1.1) d.1.1.2 := (Nat.count_le _).trans (Nat.div_le_self _ _)
  all_goals have := Nat.mod_le (E.Uc (n d.1.1.1) (h d.1.1.1 + 1) (μ d.1.1.1) d.1.1.2) E.W
  all_goals simp only [slotR, pow_succ] at *; omega
lemma own_nth (K : E.BlkSrc m B s x n h μ r) :
    Can m (fun d : UnitF fun i => (E.ownSrc (n i) (h i) (μ i) r).length => B d.1) (p s w) w (fun d => (x d.1, d.2.val))
      (fun d => Nat.nth (E.srcP (n d.1) (h d.1) (μ d.1) r) d.2) (fun d => E.NUc (n d.1) (h d.1) (μ d.1 * r) * E.W * (0 + 1) + 1) :=
  E.can_nthSrc (Has.liftE Sigma.fst K.IT) (Has.liftE Sigma.fst (E.kNUW K.ci K.idx')) ((E.sNUW K.ci).reindex _) (fun _ => le_rfl)
    Can.second fun d => E.ownSrc_len (n d.1) (h d.1) (μ d.1) r ▸ d.2.2
lemma sOwn (ci : CIn m B s x n (fun i => h i + 1) μ) : Small B fun i => (E.ownSrc (n i) (h i) (μ i) r).length :=
  (E.sNUW ci).mono fun _ => (E.ownSrc_len ..).trans_le (Nat.count_le _)
lemma own_spec {n h μ : ℕ} {k : ℕ} (hk : k < (E.ownSrc n h μ r).length) :
    E.srcP n h μ r (Nat.nth (E.srcP n h μ r) k) ∧ Nat.nth (E.srcP n h μ r) k < E.NUc n h (μ * r) * E.W ∧
    Nat.count (E.srcP n h μ r) (Nat.nth (E.srcP n h μ r) k) = k ∧
    (E.ownSrc n h μ r).getD k 0 = E.slotSize n h (μ * r) (Nat.nth (E.srcP n h μ r) k) := by
  rw [ownSrc_len] at hk; exact ⟨(nth_spec hk).1, (nth_spec hk).2.1, (nth_spec hk).2.2, (fm_count _ _).2 k hk⟩
lemma can_OA (K : E.BlkSrc m B s x n h μ r)
    (hown : Knows m B s x (fun i => (E.ownSrc (n i) (h i) (μ i) r).length))
    {sup : ∀ i, ℕ → Bits (n i) → ℂ} {o : ι → ℕ} {l : ρ}
    {z : Fin r → Space α} {ind : LinearIndependent F z} {hr : r ≤ E.X.n}
    (hout : Has m B s (jobsT cl) x (fun i => jobsTape (n i) (E.NUc (n i) (h i) (μ i * r) * E.W)
      (fun t => hlow (n i) (E.slotSize (n i) (h i) (μ i * r) t) (E.cjobF (n i) (h i) (μ i) (sup i) (V i) (o i) l z ind hr t)))) :
    Can m B s (jobsT cl) x (fun i => jobsTape (n i) (E.ownSrc (n i) (h i) (μ i) r).length
        (fun k => hlow (n i) ((E.ownSrc (n i) (h i) (μ i) r).getD k 0) (sup i (o i + k))))
      (fun i => 0 + (E.ownSrc (n i) (h i) (μ i) r).length + (E.ownSrc (n i) (h i) (μ i) r).length *
        (E.NUc (n i) (h i) (μ i * r) * E.W * (0 + 1) + 1 + 0)) := by
  refine Can.layout (L := fun i => Layout.std (E.ownSrc (n i) (h i) (μ i) r).length)
    (t := a (c cl)) (v := fun i (k : Fin (E.ownSrc (n i) (h i) (μ i) r).length) => (bits (n i)).tape fun e => hlow (n i) ((E.ownSrc (n i) (h i) (μ i) r).getD k 0) (sup i (o i + k)) e) hown
    (((E.own_nth K).save (has_jobsAt (Has.extE (Has.liftE Sigma.fst hout)) Can.second
      fun d => (E.own_spec d.2.2).2.1)).cong (fun _ => rfl) fun d => ?_) (E.sOwn K.ci)
  obtain ⟨hs, -, hc, hg⟩ := E.own_spec d.2.2
  have : E.flR (n d.1) (h d.1) (μ d.1) r (Nat.nth (E.srcP (n d.1) (h d.1) (μ d.1) r) d.2) = 0 := if_neg fun h' => hs.2 h'.2
  simp only [cjobF, cjob, this, ne_eq, not_true_eq_false, dite_false, siR, hc, hg]
lemma can_OS (K : E.BlkSrc m B s x n h μ r)
    (hown : Knows m B s x (fun i => (E.ownSrc (n i) (h i) (μ i) r).length)) :
    Can m B s (a w) x (fun i => accZ (E.ownSrc (n i) (h i) (μ i) r))
      (fun i => 0 + (E.ownSrc (n i) (h i) (μ i) r).length + (E.ownSrc (n i) (h i) (μ i) r).length *
        (E.NUc (n i) (h i) (μ i * r) * E.W * (0 + 1) + 1 + (h i + 1))) := by
  let D := UnitF fun i => (E.ownSrc (n i) (h i) (μ i) r).length
  let Y (d : D) : T (p (p s w) w) := ((x d.1, d.2.val), Nat.nth (E.srcP (n d.1) (h d.1) (μ d.1) r) d.2)
  have L : ∀ {t : Ty} {z : ι → T t}, Has m B s t x z → Has m (fun d : D => B d.1) _ t Y (fun d => z d.1) :=
    fun hz => Can.first.fst.then_do (hz.reindex _)
  have ht : Knows m (fun d : D => B d.1) _ Y fun d => Nat.nth (E.srcP (n d.1) (h d.1) (μ d.1) r) d.2 := Can.second
  have hlt := fun d : D => (E.own_spec d.2.2).2.1
  have hq : ∀ d : D, Nat.nth (E.srcP (n d.1) (h d.1) (μ d.1) r) d.2 / E.W < E.NUc (n d.1) (h d.1) (μ d.1 * r) :=
    fun d => (Nat.div_lt_iff_lt_mul E.W_pos).2 (hlt d)
  have S := (K.ci.powS E.W).reindex fun d : D => d.1
  have st : Small (fun d : D => B d.1) fun d => Nat.nth (E.srcP (n d.1) (h d.1) (μ d.1) r) d.2 :=
    S.mono fun d => (hlt d).le.trans (by rw [pow_succ]; exact Nat.mul_le_mul_right _ (E.NU_le' _ _ _))
  have hU := E.fetchU (L K.idx') (ht.dvdW (Can.wc E.W) st) hq
  have hUl : ∀ d : D, E.Uc (n d.1) (h d.1) (μ d.1 * r) (Nat.nth (E.srcP (n d.1) (h d.1) (μ d.1) r) d.2 / E.W) < E.W ^ (h d.1 + 1) :=
    fun d => (U_lt (hq d)).trans_le (Nat.pow_le_pow_right E.W_pos (Nat.le_succ _))
  have sh : Small B h := K.ci.hS.mono fun i => Nat.le_succ _
  have hc := E.can_colS (L ((K.ci.hK.minus (Can.wc 1) K.ci.hS).cong (fun _ => rfl) fun i => Nat.add_sub_cancel ..))
    (sh.reindex _) hU (S.mono fun d => (hUl d).le) (((K.ci.powS E.mx).mono fun i => Nat.pow_le_pow_right
      (show 0 < E.X.n by have := E.three; omega) (Nat.le_succ _)).reindex _)
  have sn := (K.ci.big.reindex fun d : D => d.1).mono fun d => (E.cU_le _ _ _ ⟨_, hq d⟩).trans Nat.lt_two_pow_self.le
  refine Can.layout (L := fun i => Layout.std (E.ownSrc (n i) (h i) (μ i) r).length) (t := w)
    (v := fun i (k : Fin (E.ownSrc (n i) (h i) (μ i) r).length) => (E.ownSrc (n i) (h i) (μ i) r).getD k 0) hown
    (((E.own_nth K).save (((Has.atW (E.knows_tq (ht.modW (Can.wc E.W) st) fun d => Nat.mod_lt _ E.W_pos)).wmul
      ((Has.atW (L (K.ci.μK.times (Can.wc r) K.ci.μS (Small.const _ _)))).wmul hc sn) ?_).cong (fun _ => rfl) fun d =>
        (rfl : _ = E.slotSize (n d.1) (h d.1) (μ d.1 * r) _))).cong (fun _ => rfl)
      fun d => ((E.own_spec d.2.2).2.2.2).symm) (E.sOwn K.ci)
  refine (K.ci.big.reindex fun d : D => d.1).mono fun d => ?_
  exact (Nat.mul_le_mul_right _ (E.tq_le _)).trans ((U_fits (hq d)).trans Nat.lt_two_pow_self.le)
abbrev cat3 {t : Ty} (A B C : ℕ) (f g k : ℕ → T t) : Tape (T t) :=
  (Layout.std (A + B + C)).tape fun j => if j.val < A then f j else if j.val < A + B then g (j - A) else k (j - A - B)
lemma cat3_eq {t : Ty} (A B C N : ℕ) (f g k F : ℕ → T t) (hN : A + B + C = N)
    (hF : ∀ j < N, F j = if j < A then f j else if j < A + B then g (j - A) else k (j - A - B)) :
    cat3 A B C f g k = (Layout.std N).tape fun j => F j := by
  subst hN; unfold cat3; congr 1; funext j; exact (hF j j.2).symm
lemma can_cat3 {t : Ty} {A B C : ι → ℕ} {f g k : ∀ i, ℕ → T t}
    (hf : Has m B' s (a t) x (fun i => (Layout.std (A i)).tape fun j => f i j))
    (hg : Has m B' s (a t) x (fun i => (Layout.std (B i)).tape fun j => g i j))
    (hk : Has m B' s (a t) x (fun i => (Layout.std (C i)).tape fun j => k i j))
    (hA : Knows m B' s x A) (hB : Knows m B' s x B) (hC : Knows m B' s x C) (hS : Small B' fun i => A i + B i + C i) :
    Can m B' s (a t) x (fun i => cat3 (A i) (B i) (C i) (f i) (g i) (k i)) (fun i => A i + B i + C i) := by
  let D := Σ i, Fin (A i + B i + C i)
  have L : ∀ {t' : Ty} {z : ι → T t'}, Has m B' s t' x z → Has m (fun d : D => B' d.1) (p s w) t' (fun d => (x d.1, d.2.val))
    (fun d => z d.1) := fun hz => Has.liftE Sigma.fst hz
  have hj : Knows m (fun d : D => B' d.1) (p s w) (fun d => (x d.1, d.2.val)) fun d => d.2.val := Can.second
  have sA := hS.mono fun i => (Nat.le_add_right (A i) (B i)).trans (Nat.le_add_right _ (C i))
  have sAB := hS.mono fun i => Nat.le_add_right (A i + B i) (C i)
  have nlt : ∀ {a b : ℕ}, (if a < b then 1 else 0) = 0 → ¬ a < b := fun h => by simpa using h
  have ylt : ∀ {a b : ℕ}, (if a < b then 1 else 0) ≠ 0 → a < b := fun h => by by_contra h'; simp [h'] at h
  refine (Can.table (P := fun _ => 0) _ ((hA.plus hB sA (hS.mono fun i => by omega)).plus hC sAB (hS.mono fun i => by omega)) hS
    (Can.testz (hj.wlt (L hA)) (Can.testz ((hj.wlt ((L hA).plus (L hB) (sA.reindex _) ((hS.mono fun i => by omega).reindex _))).reindex Subtype.val)
      ?_ ?_) ?_)).mono fun i => by simp
  · exact (Can.fetch (L := fun d : {d : {d : D // _} // _} => Layout.std (C d.1.1.1)) (t := t)
      (v := fun d (j : Fin (C d.1.1.1)) => k d.1.1.1 j) (i := fun d => ⟨d.1.1.2.val - A d.1.1.1 - B d.1.1.1, by
        have := d.1.1.2.2; have := nlt d.1.2; have := nlt d.2; omega⟩)
      (((L hk).reindex Subtype.val).reindex Subtype.val) ((((hj.minus (L hA) ((hS.reindex _).mono fun d => d.2.2.le)).minus (L hB)
        ((hS.reindex _).mono fun d => by have := d.2.2; omega)).reindex Subtype.val).reindex Subtype.val)).cong (fun _ => rfl)
      fun d => by have := nlt d.1.2; have := nlt d.2; simp [*]
  · exact (Can.fetch (L := fun d : {d : {d : D // _} // _} => Layout.std (B d.1.1.1)) (t := t)
      (v := fun d (j : Fin (B d.1.1.1)) => g d.1.1.1 j) (i := fun d => ⟨d.1.1.2.val - A d.1.1.1, by
        have := ylt (a := d.1.1.2.val) (b := A d.1.1.1 + B d.1.1.1) d.2; have := nlt d.1.2; omega⟩)
      (((L hg).reindex Subtype.val).reindex Subtype.val) (((hj.minus (L hA) ((hS.reindex _).mono fun d => d.2.2.le)).reindex
        Subtype.val).reindex Subtype.val)).cong (fun _ => rfl)
      fun d => by have := nlt d.1.2; have := ylt d.2; simp [*]
  · exact (Can.fetch (L := fun d : {d : D // _} => Layout.std (A d.1.1)) (t := t)
      (v := fun d (j : Fin (A d.1.1)) => f d.1.1 j) (i := fun d => ⟨d.1.2.val, ylt d.2⟩)
      ((L hf).reindex Subtype.val) (hj.reindex Subtype.val)).cong (fun _ => rfl) fun d => by have := ylt d.2; simp [*]
end Slots
section Body
variable {ι : Type V} {m : Bool} {cl : Paint}
lemma free_step {B : ι → ℕ} {s : Ty} {y : ι → T s} {n h μ : ι → ℕ} (c : E.Ctx m B s y n h μ) {mv : GMove α ρ}
    (h0 : mv.rk? = none) (V : ∀ i, E.CState (n i) (h i) (μ i)) :
    Can m B (p s (ctabT cl)) (ctabT cl) (fun i => (y i, E.tabV n h μ V i))
      (fun i => E.tabV n h μ (fun i => E.stepV (V i) mv) i) (fun i => E.NUc (n i) (h i) (μ i) * 2^(n i)) :=
  (E.can_free c h0 V).weaken (dom_mul _ fun _ => E.pass_le _ _)
lemma exit_enc {B : ι → ℕ} {s : Ty} {y : ι → T s} {n μ : ι → ℕ} {l : ρ} {r : ℕ} {z : Fin r → Space α}
    {ind : LinearIndependent F z} (hr : r ≤ E.X.n) (ci : CIn m B s y n (fun _ => 0) μ) (c : E.Ctx m B s y n (fun _ => 0) μ)
    {V : ∀ i, E.CState (n i) 0 (μ i)} (ht : Has m B s (ctabT cl) y (fun i => E.tabV n (fun _ => 0) μ V i))
    (hk : ∀ i, r * μ i ≤ n i) (h2k : Knows m B s y fun i => 2^(r * μ i)) (h2d : Knows m B s y fun i => 2^(n i - r * μ i)) :
    Can m B s (portIn cl) y (fun i => E.encodeJob cl (EngJob.top (r * μ i) (E.NUc (n i) 0 (μ i) * 2^(n i - r * μ i))
      (toVec (n i) (r * μ i) (hk i) (exJobs E.X (bS z ind) (bX r) (E.bX_n hr) l (E.fitc (n i) 0 (μ i)) (V i)))))
      (fun i => E.NUc (n i) 0 (μ i) * 2^(n i)) := by
  have coordFrame : ∀ i, 2^(r * μ i) ≤ 2^(n i) := fun i => Nat.pow_le_pow_right two_pos (hk i)
  have pd : ∀ i, 2^(n i - r * μ i) ≤ 2^(n i) := fun i => Nat.pow_le_pow_right two_pos (Nat.sub_le _ _)
  have N1 : ∀ i, E.NUc (n i) 0 (μ i) ≤ 1 := fun i => E.NU_le' _ _ _
  have hN : ∀ i, E.NUc (n i) 0 (μ i) * 2^(n i - r * μ i) ≤ 2^(n i) := fun i =>
    (Nat.mul_le_mul_right _ (N1 i)).trans (by rw [Nat.one_mul]; exact pd i)
  let N i := E.NUc (n i) 0 (μ i) * 2^(n i - r * μ i)
  let D := Σ u : UnitF N, Bits (r * μ u.1)
  let yD (d : D) : T (p (p s w) w) := ((y d.1.1, d.1.2.val), (bits (r * μ d.1.1)).loc d.2)
  have L : ∀ {t : Ty} {z : ι → T t}, Has m B s t y z → Has m (fun d : D => B d.1.1) _ t yD (fun d => z d.1.1) :=
    fun hz => Can.first.fst.then_do (hz.reindex _)
  have SD := ci.big.reindex fun d : D => d.1.1
  have ht' : Knows m (fun d : D => B d.1.1) _ yD fun d => (d.1.2 : ℕ) := Can.first.snd
  have st : Small (fun d : D => B d.1.1) fun d => (d.1.2 : ℕ) := SD.mono fun d => d.1.2.2.le.trans (hN _)
  have hp := ht'.dvdW (L h2d) st
  have hpl : ∀ d : D, (d.1.2 : ℕ) / 2^(n d.1.1 - r * μ d.1.1) < E.NUc (n d.1.1) 0 (μ d.1.1) :=
    fun d => Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact d.1.2.2)
  have he : Knows m (fun d : D => B d.1.1) _ yD fun d => (bits (n d.1.1)).loc (castB (Nat.add_sub_cancel' (hk d.1.1))
      (catB _ _ (d.2, bitsOf (n d.1.1 - r * μ d.1.1) d.1.2))) := by
    have E1 := fun d : D => (loc_castB_catB _ _ (hk d.1.1) d.2 (bitsOf (n d.1.1 - r * μ d.1.1) d.1.2)).trans
      (by rw [bitsOf_loc])
    have sm : ∀ {F : D → ℕ}, (∀ d, F d ≤ (bits (n d.1.1)).loc (castB (Nat.add_sub_cancel' (hk d.1.1))
        (catB _ _ (d.2, bitsOf (n d.1.1 - r * μ d.1.1) d.1.2)))) → Small (fun d : D => B d.1.1) F :=
      fun hF => SD.mono fun d => (hF d).trans ((bits _).bd _).le
    exact ((Can.second : Knows m (fun d : D => B d.1.1) _ yD fun d => (bits (r * μ d.1.1)).loc d.2).plus
      ((L h2k).times (ht'.modW (L h2d) st) ((ci.big.mono coordFrame).reindex _) (st.mod)) (sm fun d => by simp only [yD]; rw [E1]; omega)
      (sm fun d => by rw [E1]; omega)).cong (fun _ => rfl) fun d => (E1 d).symm
  have g := c.gearU.descend (fun d : D => (⟨d.1.1, ⟨_, hpl d⟩⟩ : UnitF _)) yD ((L Can.id).pair hp)
  have dec := g.place_dec (bS z ind) E.X (bX r) (fun d => fitk (bX r) (E.bX_n hr) (E.fitc _ _ _ _))
    (ci.big.reindex fun d : D => d.1.1) he
  have hT := L ht
  unfold tabV at hT
  refine ((Has.atW ((Can.wc r).times ci.μK (Small.const _ _) ci.μS)).pair ((Has.atW ci.imag).pair ((Can.wc 0).pair
    ((Can.wc 0).pair ((Can.wc 0).pair ((Can.jobsTable _ (c.nuK.times h2d c.nuS (ci.big.mono pd)) h2k
      (ci.big.mono hN) (ci.big.mono coordFrame) ((has_ctabRead E.X E.R (fun d : D => ⟨_, hpl d⟩) _ (fun d => (l, ((0 : Bits 0), _))) hT hp
        dec.1 (Can.addr_join (Can.wc (E.R.loc l)) dec.2 (g.grid_size E.X 0) (Small.const _ _) (g.grid_small E.X 0))).cong
        (fun _ => rfl) fun d => ?_)).pair (Has.atW (has_jobs0 _ _)))))))).mono fun i => ?_
  · have : exFl (E.NUc (n d.1.1) 0 (μ d.1.1)) ((d.1.2 : ℕ) / 2^(n d.1.1 - r * μ d.1.1)) ≠ 0 := by simp [exFl, hpl d]
    simp only [toVec, exJobs, cjob, dif_pos this]; rfl
  · rw [Nat.mul_assoc, ← pow_add, Nat.sub_add_cancel (hk i)]
lemma exit_scat {B : ι → ℕ} {s : Ty} {y : ι → T s} {n μ : ι → ℕ} {l : ρ} {r : ℕ} {z : Fin r → Space α}
    {ind : LinearIndependent F z} (hr : r ≤ E.X.n) (c : E.Ctx m B s y n (fun _ => 0) μ)
    {V : ∀ i, E.CState (n i) 0 (μ i)} (ht : Has m B s (ctabT cl) y (fun i => E.tabV n (fun _ => 0) μ V i))
    (hk : ∀ i, r * μ i ≤ n i) (h2k : Knows m B s y fun i => 2^(r * μ i)) (h2d : Knows m B s y fun i => 2^(n i - r * μ i))
    (ho : Has m B s (jobsT cl) y (fun i => jobsTape (r * μ i) (E.NUc (n i) 0 (μ i) * 2^(n i - r * μ i))
      (fun t => ripple (r * μ i) (toVec (n i) (r * μ i) (hk i) (exJobs E.X (bS z ind) (bX r) (E.bX_n hr) l (E.fitc (n i) 0 (μ i)) (V i)) t)))) :
    Can m B s (ctabT cl) y (fun i => E.tabV n (fun _ => 0) μ (fun i => E.stepV (V i) (.old (.block l r z ind))) i)
      (fun i => E.passCost (n i) (E.NUc (n i) 0 (μ i))) := by
  refine E.can_roleSet c l ht (fun i p q b hb => by simp [stepV, gferry, GMove.act, BMove.act, roleAct, hb]) ?_
  let K := E.ElemF n (fun _ => 0) μ
  obtain ⟨hp, hq⟩ := E.elPQ (m := m) (B := B) (y := y) (n := n) (h := fun _ => 0) (μ := μ)
  have encodeJob := (E.elGear c).place_enc (bS z ind) E.X (bX r) (fun d => fitk (bX r) (E.bX_n hr) (E.fitc _ _ _ _))
    (c.big.reindex fun d : K => d.1.1.1) hq (E.elRG c).2
  let e (d : K) := E.plB _ _ _ z ind hr d.1.1.2 (d.1.2, d.2.2.2)
  let u (d : K) := (catB _ _).symm ((castB (Nat.add_sub_cancel' (hk d.1.1.1))).symm (e d))
  have sE : Small (fun d : K => B d.1.1.1) fun d => (bits (n d.1.1.1)).loc (e d) :=
    (c.big.reindex fun d : K => d.1.1.1).mono fun d => ((bits _).bd _).le
  have hA : ∀ d : K, (bits (r * μ d.1.1.1)).loc (u d).1 < 2^(r * μ d.1.1.1) := fun d => (bits _).bd _
  have hB : ∀ d : K, (bits (n d.1.1.1 - r * μ d.1.1.1)).loc (u d).2 < 2^(n d.1.1.1 - r * μ d.1.1.1) := fun d => (bits _).bd _
  have hlt : ∀ d : K, (d.1.1.2 : ℕ) * 2^(n d.1.1.1 - r * μ d.1.1.1) + _ < E.NUc (n d.1.1.1) 0 (μ d.1.1.1) * 2^(n d.1.1.1 - r * μ d.1.1.1) :=
    fun d => DigitArith.lt_join d.1.1.2.2 (hB d)
  have N1 : ∀ d : K, E.NUc (n d.1.1.1) 0 (μ d.1.1.1) * 2^(n d.1.1.1 - r * μ d.1.1.1) ≤ 2^(n d.1.1.1) := fun d =>
    (Nat.mul_le_mul_right _ (E.NU_le' _ _ _)).trans (by rw [pow_zero, Nat.one_mul]; exact Nat.pow_le_pow_right two_pos (Nat.sub_le _ _))
  have S2 := c.big.reindex fun d : K => d.1.1.1
  have hhi := (hp.times (E.elH h2d) (S2.mono fun d => d.1.1.2.2.le.trans ((Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)).trans (N1 d)))
    (S2.mono fun d => Nat.pow_le_pow_right two_pos (Nat.sub_le _ _))).plus ((encodeJob.dvdW (E.elH h2k) sE).cong (fun _ => rfl)
      fun d => by erw [loc_split (hk _), DigitArith.div_join' (hA d)]; rfl) (S2.mono fun d => (Nat.le_add_right _ _).trans ((hlt d).le.trans (N1 d)))
      (S2.mono fun d => (Nat.le_add_left _ _).trans ((hlt d).le.trans (N1 d)))
  exact ((has_jobsRead (n := fun d : K => r * μ d.1.1.1) (J := fun d t => ripple (r * μ d.1.1.1) (toVec (n d.1.1.1)
    (r * μ d.1.1.1) (hk _) (exJobs E.X (bS z ind) (bX r) (E.bX_n hr) l (E.fitc (n d.1.1.1) 0 (μ d.1.1.1)) (V d.1.1.1)) t))
    (E.elH ho) hhi hlt ((encodeJob.modW (E.elH h2k) sE).cong (fun _ => rfl) fun d => by
    erw [loc_split (hk _), DigitArith.mod_join' (hA d)])).reindex Subtype.val).cong (fun _ => rfl) fun d => by
      obtain ⟨d, hd⟩ := d
      have : d.2.2.1 = 0 := Subsingleton.elim _ _
      refine (E.exit_eq (V d.1.1.1) l z ind hr (hk _) d.1.1.2 d.1.2 d.2.2.2).trans ?_
      simp [stepV, gferry, GMove.act, BMove.act, roleAct, hd, this]
theorem able_inner_block {b : Bank (portM cl) ι} {s : Ty} {y : ι → T s} {n h μ o BS : ι → ℕ}
    {sup : ∀ i, ℕ → Bits (n i) → ℂ}
    (ci : CIn m b.B s y n (fun i => h i + 1) μ) (c : E.Ctx m b.B s y n (fun i => h i + 1) μ)
    (hidx : Has m b.B s IdxT y (fun i => E.idxVal (n i) (h i + 1) (μ i)))
    (hsup : Has m b.B s (jobsT cl) y (fun i => jobsTape (n i) (BS i) (sup i)))
    (ho : Knows m b.B s y o) (hBS : Small b.B BS)
    {l : ρ} {r : ℕ} {z : Fin r → Space α} {ind : LinearIndependent F z}
    (hm : GMove.old (BMove.block l r z ind) ∈ E.wd)
    (V : ∀ i, E.CState (n i) (h i + 1) (μ i)) (acc : ι → List ℕ)
    (hfitB : ∀ i, o i + (acc i ++ E.accR (n i) (h i) (μ i) r).length ≤ BS i)
    {τ : ι → EngJob → ℕ}
    (hcall : ∀ i, (b.use i (E.encodeJob cl (E.childC (n i) (h i) (μ i) (BS i) (sup i) (V i) (o i + (acc i).length)
        l r z ind (E.wd_block hm).2.le))).OK
      (E.jobAnswer cl (E.childC (n i) (h i) (μ i) (BS i) (sup i) (V i) (o i + (acc i).length) l r z ind
        (E.wd_block hm).2.le))
      (τ i (E.childC (n i) (h i) (μ i) (BS i) (sup i) (V i) (o i + (acc i).length) l r z ind
        (E.wd_block hm).2.le)) (b.ext i)) :
    Able m b (SwT s cl) (SwT s cl)
      (fun i => (y i, (E.tabV n (fun i => h i + 1) μ V i, (accA (n i) (acc i) (o i) (sup i), accZ (acc i)))))
      (fun i => (y i, (E.tabV n (fun i => h i + 1) μ
          (fun i => E.stepV (V i) (GMove.old (BMove.block l r z ind))) i,
        (accA (n i) (acc i ++ E.accR (n i) (h i) (μ i) r) (o i) (sup i),
         accZ (acc i ++ E.accR (n i) (h i) (μ i) r)))))
      (fun i => E.blkCost (n i) (h i) (μ i) r (acc i).length)
      (fun i => τ i (E.childC (n i) (h i) (μ i) (BS i) (sup i) (V i) (o i + (acc i).length) l r z ind
        (E.wd_block hm).2.le)) := by
  have hr := (E.wd_block hm).2.le
  have hsep : ∀ l, r < E.tr l := E.sep _ hm r rfl
  let x0 i : T (SwT s cl) := (y i, (E.tabV n (fun i => h i + 1) μ V i, (accA (n i) (acc i) (o i) (sup i), accZ (acc i))))
  have g0 : Has m b.B _ s x0 y := Can.first
  have c0 : CIn m b.B _ x0 n h (fun i => μ i * r) := ⟨g0.then_do ci.nK, g0.then_do ((ci.hK.minus (Can.wc 1) ci.hS).cong
    (fun _ => rfl) fun i => Nat.add_sub_cancel ..), g0.then_do (ci.μK.times (Can.wc r) ci.μS (Small.const _ _)), g0.then_do ci.p2n,
    g0.then_do ci.imag, ci.big, fun i => (Nat.le_succ _).trans (ci.hle i), ci.μS.mul (Small.const _ _)⟩
  let x1 i : T (p _ IdxT) := (x0 i, E.idxVal (n i) (h i) (μ i * r))
  have g1 : Has m b.B _ s x1 y := Can.first.fst
  have IT := E.can_IT (r := r) (ci.lift g1) (g1.then_do hidx) Can.second
  let x2 i : T (p _ (a w)) := (x1 i, E.itV (n i) (h i) (μ i) r)
  have g2 : Has m b.B _ s x2 y := Can.first.fst.fst
  have K2 : E.BlkCx m b.B _ x2 n h μ r cl V :=
    { ci := ci.lift g2, c := c.lift g2, idx := g2.then_do hidx, idx' := Can.first.snd, IT := Can.second, tb := Can.first.fst.snd.fst }
  have CT := E.can_CT K2.1
  let x3 i : T (p _ (a w)) := (x2 i, E.ctV (n i) (h i) (μ i) r)
  have K3 := K2.lift (y := x3) Can.first
  have CS := E.can_cntSrc K3.IT (E.kNUW K3.ci K3.idx') (E.sNUW K3.ci) fun _ => le_rfl
  let x4 i : T (p _ w) := (x3 i, Nat.count (E.srcP (n i) (h i) (μ i) r) (E.NUc (n i) (h i) (μ i * r) * E.W))
  have g4 : Has m b.B _ s x4 y := Can.first.fst.fst.fst.fst
  have K4 := K3.lift (y := x4) Can.first
  have hown4 : Knows m b.B _ x4 fun i => (E.ownSrc (n i) (h i) (μ i) r).length := Can.second.cong (fun _ => rfl) fun i => (E.ownSrc_len ..).symm
  have hZ4 : Has m b.B _ (a w) x4 fun i => accZ (acc i) := Can.first.fst.fst.fst.snd.snd.snd
  have sBS : ∀ {F : ι → ℕ}, (∀ i, F i ≤ BS i) → Small b.B F := fun hF => hBS.mono hF
  have hl : ∀ i, o i + (acc i).length + (E.ownSrc (n i) (h i) (μ i) r).length + E.cons (n i) (h i) (μ i * r) ≤ BS i := fun i => by
    have := hfitB i; simp only [accR, cons, List.length_append] at *; omega
  have hacc4 : Knows m b.B _ x4 fun i => (acc i).length := Can.len hZ4 (sBS fun i => show (acc i).length ≤ BS i by have := hl i; omega)
  have ho4 := (g4.then_do ho).plus hacc4 (sBS fun i => by have := hl i; omega) (sBS fun i => by have := hl i; omega)
  have OJ := E.can_OJ K4 Can.first.snd (g4.then_do hsup) ho4 hBS
    (fun i => by rw [← E.ownSrc_len]; have := hl i; omega) l z ind hr
  have ENC := (Has.atW (g4.then_do ci.nK)).pair ((Has.atW (g4.then_do ci.imag)).pair ((Has.atW (g4.then_do ci.hK)).pair
    ((Has.atW (g4.then_do (ci.μK.times (Can.wc r) ci.μS (Small.const _ _)))).pair ((Has.atW (ho4.plus hown4
      (sBS fun i => by have := hl i; omega) (sBS fun i => by have := hl i; omega))).pair (OJ.pair (Has.atW (g4.then_do hsup)))))))
  let x5 i : T (p _ (portOut cl)) := (x4 i, E.jobAnswer cl (E.childC (n i) (h i) (μ i) (BS i) (sup i) (V i) (o i + (acc i).length) l r z ind hr))
  have g54 : Has m b.B _ _ x5 x4 := Can.first
  have K5 := K4.lift g54
  have hown5 := g54.then_do hown4
  have hout5 : Has m b.B _ (jobsT cl) x5 (fun i => jobsTape (n i) (E.NUc (n i) (h i) (μ i * r) * E.W)
      (fun t => hlow (n i) (E.slotSize (n i) (h i) (μ i * r) t) (E.cjobF (n i) (h i) (μ i) (sup i) (V i) (o i + (acc i).length)
        l z ind hr t))) := Can.second.fst
  have SC := E.can_scatter K5.toBlkCls l z ind hr hsep hout5
  have OA := E.can_OA K5.1 hown5 hout5
  have OS := E.can_OS K5.1 hown5
  let x7 i : T (p (p _ (jobsT cl)) (a w)) := ((x5 i, jobsTape (n i) (E.ownSrc (n i) (h i) (μ i) r).length fun k => hlow (n i)
    ((E.ownSrc (n i) (h i) (μ i) r).getD k 0) (sup i (o i + (acc i).length + k))), accZ (E.ownSrc (n i) (h i) (μ i) r))
  have g7 : Has m b.B _ _ x7 x5 := Can.first.fst
  have hS : Small b.B fun i => (acc i).length + (E.ownSrc (n i) (h i) (μ i) r).length + E.cons (n i) (h i) (μ i * r) :=
    sBS fun i => by have := hl i; omega
  have hC : Knows m b.B _ x7 fun i => E.cons (n i) (h i) (μ i * r) := g7.then_do (Can.len (Can.second.snd.snd :
    Has m b.B _ (a w) x5 fun i => (Layout.std (E.cons (n i) (h i) (μ i * r))).tape fun k => E.csz (n i) (h i) (μ i * r) k)
    (sBS fun i => show E.cons (n i) (h i) (μ i * r) ≤ BS i by have := hl i; omega))
  have CA := (can_cat3 (t := a (Ty.c cl)) (f := fun i j => (bits (n i)).tape (hlow (n i) ((acc i).getD j 0) (sup i (o i + j))))
    (g := fun i j => (bits (n i)).tape (hlow (n i) ((E.ownSrc (n i) (h i) (μ i) r).getD j 0) (sup i (o i + (acc i).length + j))))
    (k := fun i j => (bits (n i)).tape (hlow (n i) (E.csz (n i) (h i) (μ i * r) j)
      (sup i (o i + (acc i).length + (E.ownSrc (n i) (h i) (μ i) r).length + j))))
    (g7.then_do (g54.then_do Can.first.fst.fst.fst.snd.snd.fst))
    Can.first.snd (g7.then_do Can.second.snd.fst) (g7.then_do (g54.then_do hacc4)) (g7.then_do hown5) hC hS).cong (fun _ => rfl)
    fun i => cat3_eq _ _ _ (acc i ++ E.accR (n i) (h i) (μ i) r).length _ _ _ (fun j => (bits (n i)).tape (hlow (n i)
      ((acc i ++ E.accR (n i) (h i) (μ i) r).getD j 0) (sup i (o i + j)))) (by simp [accR, cons]; omega) fun j hj => by
      simp only [accR]; rw [getD3]; split_ifs <;> congr 3 <;> omega
  have CZ := (can_cat3 (t := w) (f := fun i j => (acc i).getD j 0) (g := fun i j => (E.ownSrc (n i) (h i) (μ i) r).getD j 0)
    (k := fun i j => E.csz (n i) (h i) (μ i * r) j) (g7.then_do (g54.then_do hZ4)) Can.second (g7.then_do Can.second.snd.snd)
    (g7.then_do (g54.then_do hacc4)) (g7.then_do hown5) hC hS).cong (fun _ => rfl)
    fun i => cat3_eq _ _ _ (acc i ++ E.accR (n i) (h i) (μ i) r).length _ _ _ (fun j => (acc i ++ E.accR (n i) (h i) (μ i) r).getD j 0)
      (by simp [accR, cons]; omega) fun j hj => by simp only [accR]; rw [getD3]; rfl
  have PRE := ((Can.id (W := fun _ => 0)).fork (E.can_index c0)).pipe (((Can.id (W := fun _ => 0)).fork IT).pipe
    (((Can.id (W := fun _ => 0)).fork CT).pipe ((Can.id (W := fun _ => 0)).fork CS)))
  have FIN := ((Can.id (W := fun _ => 0)).fork OA).pipe (((Can.id (W := fun _ => 0)).fork (Can.first.then_do OS)).pipe
    ((Has.atW (W := fun _ => 0) (g7.then_do (g54.then_do g4))).fork (((Has.atW g7).then_do SC).fork (CA.fork CZ))))
  refine ((Able.of_can PRE).comp (Able.save ((Able.of_can ENC).comp (Able.use_call hcall)) (Able.of_can FIN))).weaken
    (dom_mul _ fun i => E.blk_bound _ _ _ _ _ _ ?_) fun _ => by simp
  have e1 := Nat.mul_add_one (E.NUc (n i) (h i) (μ i * r) * E.W) (2 ^ n i)
  have e2 : (E.accR (n i) (h i) (μ i) r).length = (E.ownSrc (n i) (h i) (μ i) r).length + E.cons (n i) (h i) (μ i * r) := by
    simp [accR, cons]
  simp only [Nat.zero_add, Nat.add_zero, Nat.mul_one] at *
  omega
theorem able_exit_block {b : Bank (portM cl) ι} {s : Ty} {y : ι → T s} {n μ : ι → ℕ}
    (ci : CIn m b.B s y n (fun _ => 0) μ) (c : E.Ctx m b.B s y n (fun _ => 0) μ)
    (hfit0 : ∀ i, E.X.n * μ i ≤ n i)
    {l : ρ} {r : ℕ} {z : Fin r → Space α} {ind : LinearIndependent F z}
    (hm : GMove.old (BMove.block l r z ind) ∈ E.wd) (V : ∀ i, E.CState (n i) 0 (μ i)) {τ : ι → EngJob → ℕ}
    (hcall : ∀ i, (b.use i (E.encodeJob cl (E.exitC (n i) (μ i) (V i) l r z ind (E.wd_block hm).2.le))).OK
      (E.jobAnswer cl (E.exitC (n i) (μ i) (V i) l r z ind (E.wd_block hm).2.le))
      (τ i (E.exitC (n i) (μ i) (V i) l r z ind (E.wd_block hm).2.le)) (b.ext i)) :
    Able m b (p s (ctabT cl)) (p s (ctabT cl))
      (fun i => (y i, E.tabV n (fun _ => 0) μ V i))
      (fun i => (y i, E.tabV n (fun _ => 0) μ (fun i => E.stepV (V i) (GMove.old (BMove.block l r z ind))) i))
      (fun i => E.NUc (n i) 0 (μ i) * 2^(n i) + 2 * n i + 2)
      (fun i => τ i (E.exitC (n i) (μ i) (V i) l r z ind (E.wd_block hm).2.le)) := by
  have hr := (E.wd_block hm).2.le
  have hk : ∀ i, r * μ i ≤ n i := fun i => (Nat.mul_le_mul_right _ hr).trans (hfit0 i)
  simp only [E.exitC_eq _ _ _ _ hr (hk _)] at hcall ⊢
  have sk : Small b.B fun i => r * μ i := ci.nS.mono hk
  have P1 := can_powv 2 two_pos (Has.extE ((Can.wc r).times ci.μK (Small.const _ _) ci.μS) : Knows m b.B (p s (ctabT cl))
    (fun i => (y i, E.tabV n (fun _ => 0) μ V i)) fun i => r * μ i) sk (ci.big.mono fun i => Nat.pow_le_pow_right two_pos (hk i))
  have g1 : Has m b.B (p (p s (ctabT cl)) w) s (fun i => ((y i, E.tabV n (fun _ => 0) μ V i), 2^(r * μ i))) y := Can.first.fst
  have P2 := can_powv 2 two_pos (g1.then_do (ci.nK.minus ((Can.wc r).times ci.μK (Small.const _ _) ci.μS) ci.nS))
    (ci.nS.mono fun i => Nat.sub_le _ _)
    (ci.big.mono fun i => Nat.pow_le_pow_right two_pos (Nat.sub_le _ _))
  have g : Has m b.B (p (p (p s (ctabT cl)) w) w) s (fun i => (((y i, E.tabV n (fun _ => 0) μ V i), 2^(r * μ i)), 2^(n i - r * μ i)))
    y := Can.first.fst.fst
  refine ((Able.of_can (((Can.id (W := fun _ => 0)).fork P1).pipe ((Can.id (W := fun _ => 0)).fork P2))).comp
    (Able.save ((Able.of_can (E.exit_enc hr (ci.lift g) (c.lift g) Can.first.fst.snd hk
      Can.first.snd Can.second)).comp (Able.use_call hcall))
      (Able.of_can (Can.first.fst.fst.fst.pair (E.exit_scat hr ((c.lift g).ext _) (Has.extE Can.first.fst.snd) hk
        (Has.extE Can.first.snd) (Has.extE Can.second) Can.second.fst))))).weaken
    (dom_mul (2 * (E.R.n + 3)) fun i => ?_) fun _ => by simp
  have := E.free_dom (n i) (E.NUc (n i) 0 (μ i)) (E.NUc (n i) 0 (μ i) * 2^(n i) + 2 * n i + 2)
  have := hk i
  calc _ ≤ E.passCost (n i) (E.NUc (n i) 0 (μ i)) + (E.NUc (n i) 0 (μ i) * 2^(n i) + 2 * n i + 2) := by omega
    _ ≤ _ := by nlinarith
theorem able_sweep_up {b : Bank (portM cl) ι} {s : Ty} {y : ι → T s} {n h μ o BS : ι → ℕ}
    {sup : ∀ i, ℕ → Bits (n i) → ℂ}
    (ci : CIn m b.B s y n (fun i => h i + 1) μ) (c : E.Ctx m b.B s y n (fun i => h i + 1) μ)
    (hidx : Has m b.B s IdxT y (fun i => E.idxVal (n i) (h i + 1) (μ i)))
    (hsup : Has m b.B s (jobsT cl) y (fun i => jobsTape (n i) (BS i) (sup i)))
    (ho : Knows m b.B s y o) (hBS : Small b.B BS) {τ : ι → EngJob → ℕ} :
    ∀ (ws : GWord α ρ), (∀ mv ∈ ws, mv ∈ E.wd) → ∀ (V : ∀ i, E.CState (n i) (h i + 1) (μ i)) (acc : ι → List ℕ),
      (∀ i, o i + (acc i ++ E.accW (n i) (h i) (μ i) ws).length ≤ BS i) →
      (∀ i, ∀ c' ∈ E.kidsUp (n i) (h i) (μ i) (BS i) (sup i) (V i) (o i + (acc i).length) ws,
        (b.use i (E.encodeJob cl c')).OK (E.jobAnswer cl c') (τ i c') (b.ext i)) →
      Able m b (SwT s cl) (SwT s cl)
        (fun i => (y i, (E.tabV n (fun i => h i + 1) μ V i, (accA (n i) (acc i) (o i) (sup i), accZ (acc i)))))
        (fun i => (y i, (E.tabV n (fun i => h i + 1) μ (fun i => E.runV (V i) ws) i,
          (accA (n i) (acc i ++ E.accW (n i) (h i) (μ i) ws) (o i) (sup i),
           accZ (acc i ++ E.accW (n i) (h i) (μ i) ws)))))
        (fun i => E.swCost (n i) (h i) (μ i) (acc i).length ws)
        (fun i => ((E.kidsUp (n i) (h i) (μ i) (BS i) (sup i) (V i) (o i + (acc i).length) ws).map (τ i)).sum) := by
  intro ws
  induction ws with
  | nil =>
    intro _ V acc _ _
    refine (Able.id.cong (fun _ => rfl) fun i => ?_).mono (fun _ => Nat.zero_le _) fun _ => Nat.zero_le _
    rw [show E.accW (n i) (h i) (μ i) [] = [] from rfl, List.append_nil]; rfl
  | cons mv ws ih =>
    intro hw V acc hfit hk
    have ih' := fun V acc hf hk => ih (fun m hm => hw m (.tail _ hm)) V acc hf hk
    rcases GMove.rk_cases mv with h0 | ⟨l, r, z, ind, rfl⟩
    · have e1 : ∀ i, E.accW (n i) (h i) (μ i) (mv :: ws) = E.accW (n i) (h i) (μ i) ws := fun i => by simp [accW_cons, h0]
      simp only [e1, E.kidsUp_free h0] at hfit hk ⊢
      refine ((Able.of_can (Can.first.pair (((Can.first.pair Can.second.fst).then_do (E.free_step c h0 V)).pair
        Can.second.snd))).comp (ih' _ acc hfit hk)).mono (fun i => by simp [swCost, h0]) fun _ => by simp
    · have hm := hw _ (.head _)
      have hr := (E.wd_block hm).2.le
      have e1 : ∀ i, E.accW (n i) (h i) (μ i) (.old (.block l r z ind) :: ws) = E.accR (n i) (h i) (μ i) r ++ E.accW (n i) (h i) (μ i) ws :=
        fun i => E.accW_cons ..
      have e2 : ∀ i, o i + (acc i ++ E.accR (n i) (h i) (μ i) r).length =
          o i + (acc i).length + (E.ownSrc (n i) (h i) (μ i) r).length + E.cons (n i) (h i) (μ i * r) := fun i => by
        simp only [accR, cons, List.length_append]; omega
      simp only [e1, ← List.append_assoc] at hfit ⊢
      simp only [kidsUp, dif_pos hr, List.singleton_append, List.mem_cons, forall_eq_or_imp] at hk
      refine ((E.able_inner_block ci c hidx hsup ho hBS hm V acc (fun i => le_trans
        (by simp only [List.length_append]; omega) (hfit i)) fun i => (hk i).1).comp
        (ih' _ _ hfit fun i => by rw [e2]; exact (hk i).2)).mono (fun i => by simp [swCost, GMove.rk_block]) fun i => by
          rw [e2]; simp [kidsUp, dif_pos hr]
theorem able_sweep_leaf {b : Bank (portM cl) ι} {s : Ty} {y : ι → T s} {n μ : ι → ℕ}
    (ci : CIn m b.B s y n (fun _ => 0) μ) (c : E.Ctx m b.B s y n (fun _ => 0) μ)
    (hfit0 : ∀ i, E.X.n * μ i ≤ n i) {τ : ι → EngJob → ℕ} :
    ∀ (ws : GWord α ρ), (∀ mv ∈ ws, mv ∈ E.wd) → ∀ (V : ∀ i, E.CState (n i) 0 (μ i)),
      (∀ i, ∀ c' ∈ E.kidsLeaf (n i) (μ i) (V i) ws, (b.use i (E.encodeJob cl c')).OK (E.jobAnswer cl c') (τ i c') (b.ext i)) →
      Able m b (p s (ctabT cl)) (p s (ctabT cl))
        (fun i => (y i, E.tabV n (fun _ => 0) μ V i))
        (fun i => (y i, E.tabV n (fun _ => 0) μ (fun i => E.runV (V i) ws) i))
        (fun i => E.lfCost (n i) (μ i) ws)
        (fun i => ((E.kidsLeaf (n i) (μ i) (V i) ws).map (τ i)).sum) := by
  intro ws
  induction ws with
  | nil => intro _ V _; exact (Able.id).mono (fun _ => Nat.zero_le _) fun _ => Nat.zero_le _
  | cons mv ws ih =>
    intro hw V hk
    have ih' := fun V hk => ih (fun m hm => hw m (.tail _ hm)) V hk
    rcases GMove.rk_cases mv with h0 | ⟨l, r, z, ind, rfl⟩
    · simp only [E.kidsLeaf_free h0] at hk ⊢
      exact ((Able.of_can (Can.first.pair (E.free_step c h0 V))).comp (ih' _ hk)).mono (fun i => by simp [lfCost, h0])
        fun _ => by simp
    · have hm := hw _ (.head _)
      have hr := (E.wd_block hm).2.le
      simp only [kidsLeaf, dif_pos hr, List.singleton_append, List.mem_cons, forall_eq_or_imp] at hk
      exact ((E.able_exit_block ci c hfit0 hm V fun i => (hk i).1).comp (ih' _ fun i => (hk i).2)).mono
        (fun i => by simp [lfCost, GMove.rk_block]) fun i => by simp [kidsLeaf, dif_pos hr]
theorem able_class_leaf {b : Bank (portM cl) ι} {n μ o BS : ι → ℕ} {J sup : ∀ i, ℕ → Bits (n i) → ℂ}
    {τ : ι → EngJob → ℕ} (hB2 : Small b.B (fun i => 2^(n i))) (hfit0 : ∀ i, E.X.n * μ i ≤ n i)
    (hkc : ∀ i c', c' ∈ E.childJobs (EngJob.cls (n i) 0 (μ i) (o i) (BS i) (J i) (sup i)) →
      (b.use i (E.encodeJob cl c')).OK (E.jobAnswer cl c') (τ i c') (b.ext i)) :
    Able m b (portIn cl) (portOut cl)
      (fun i => E.encodeJob cl (EngJob.cls (n i) 0 (μ i) (o i) (BS i) (J i) (sup i)))
      (fun i => E.jobAnswer cl (EngJob.cls (n i) 0 (μ i) (o i) (BS i) (J i) (sup i)))
      (fun i => E.locLeaf (n i) (μ i))
      (fun i => ((E.childJobs (EngJob.cls (n i) 0 (μ i) (o i) (BS i) (J i) (sup i))).map (τ i)).sum) := by
  have hle : ∀ i, (fun _ => 0) i ≤ n i := fun _ => Nat.zero_le _
  have hμ : ∀ i, μ i ≤ n i := fun i => (Nat.le_mul_of_pos_left _ (show 0 < E.X.n by have := E.three; omega)).trans (hfit0 i)
  obtain ⟨ci, c⟩ := E.cin_pre (m := m) (B := b.B) (cl := cl) (o := o)
    (own := fun i => jobsTape (n i) (E.NUc (n i) 0 (μ i) * E.W) (J i)) (sp := fun i => jobsTape (n i) (BS i) (sup i)) hB2 hle hμ
  have ul := E.can_unload (cl := cl) c fun i => E.runV (E.V0 (n i) 0 (μ i) (J i)) E.wd
  refine (((Able.of_can (E.can_prefix (m := m) (B := b.B) (cl := cl) (o := o) hB2 hle hμ)).comp
    ((Able.of_can (Can.id.pair (E.can_load c Can.first.fst.fst.fst.snd.snd.snd.snd.snd.fst))).comp
    ((E.able_sweep_leaf ci c hfit0 E.wd (fun _ h => h) _ fun i c' hc => hkc i c' hc).comp
    (Able.of_can (ul.pair (Has.atW ((has_jobs0 n fun i k => hlow (n i) (E.csz (n i) 0 (μ i) k) (sup i (o i + k))).pair
      (has_tape0 fun i (k : Fin 0) => E.csz (n i) 0 (μ i) k)))))))).cong (fun _ => rfl) fun i => ?_).weaken
    (dom_mul _ fun i => E.cost_close (n i) (E.NUc (n i) 0 (μ i)) (E.locLeaf (n i) (μ i)) _ ?_ ?_) fun _ => by simp [childJobs]
  · simp only [jobAnswer]; congr 1; exact jobsTape_congr fun t ht => E.unl_run _ _ ht
  all_goals have := Nat.le_mul_of_pos_right (E.NUc (n i) 0 (μ i) * E.W) (Nat.two_pow_pos (n i))
  all_goals simp only [locLeaf]; omega
theorem able_class_up {b : Bank (portM cl) ι} {n h μ o BS : ι → ℕ} {J sup : ∀ i, ℕ → Bits (n i) → ℂ}
    {τ : ι → EngJob → ℕ} (hB2 : Small b.B (fun i => 2^(n i))) (hBS : Small b.B BS)
    (hle : ∀ i, h i + 1 ≤ n i) (hμ : ∀ i, μ i ≤ n i) (hfit : ∀ i, o i + E.cons (n i) (h i + 1) (μ i) ≤ BS i)
    (hkc : ∀ i c', c' ∈ E.childJobs (EngJob.cls (n i) (h i + 1) (μ i) (o i) (BS i) (J i) (sup i)) →
      (b.use i (E.encodeJob cl c')).OK (E.jobAnswer cl c') (τ i c') (b.ext i)) :
    Able m b (portIn cl) (portOut cl)
      (fun i => E.encodeJob cl (EngJob.cls (n i) (h i + 1) (μ i) (o i) (BS i) (J i) (sup i)))
      (fun i => E.jobAnswer cl (EngJob.cls (n i) (h i + 1) (μ i) (o i) (BS i) (J i) (sup i)))
      (fun i => E.locUp (n i) (h i) (μ i))
      (fun i => ((E.childJobs (EngJob.cls (n i) (h i + 1) (μ i) (o i) (BS i) (J i) (sup i))).map (τ i)).sum) := by
  obtain ⟨ci, c⟩ := E.cin_pre (m := m) (B := b.B) (cl := cl) (o := o)
    (own := fun i => jobsTape (n i) (E.NUc (n i) (h i + 1) (μ i) * E.W) (J i)) (sp := fun i => jobsTape (n i) (BS i) (sup i))
    hB2 hle hμ
  have ul := E.can_unload (cl := cl) c fun i => E.runV (E.V0 (n i) (h i + 1) (μ i) (J i)) E.wd
  refine (((Able.of_can (E.can_prefix (m := m) (B := b.B) (cl := cl) (o := o) hB2 hle hμ)).comp
    ((Able.of_can (Can.id.pair ((E.can_load c Can.first.fst.fst.fst.snd.snd.snd.snd.snd.fst).pair
      (Has.atW ((has_jobs0 (cl := cl) n fun i k => hlow (n i) (([] : List ℕ).getD k 0) (sup i (o i + k))).pair
        (has_tape0 (t := w) fun i (k : Fin 0) => ([] : List ℕ).getD k 0)))))).comp
    ((E.able_sweep_up (o := o) (BS := BS) (sup := sup) ci c Can.first.fst.snd Can.first.fst.fst.fst.snd.snd.snd.snd.snd.snd Can.first.fst.fst.fst.snd.snd.snd.snd.fst
      hBS E.wd (fun _ h => h) _ (fun _ => []) hfit fun i c' hc => hkc i c' hc).comp
    (Able.of_can (((Can.first.pair Can.second.fst).then_do ul).pair (Has.atW Can.second.snd)))))).cong
      (fun _ => rfl) fun i => ?_).weaken
    (dom_mul _ fun i => E.cost_close (n i) (E.NUc (n i) (h i + 1) (μ i)) (E.locUp (n i) (h i) (μ i)) _ ?_ ?_) fun _ => by simp [childJobs]
  · simp only [jobAnswer]; congr 1; exact jobsTape_congr fun t ht => E.unl_run _ _ ht
  all_goals have := Nat.le_mul_of_pos_right (E.NUc (n i) (h i + 1) (μ i) * E.W) (Nat.two_pow_pos (n i))
  all_goals simp only [locUp, List.length_nil]; omega

theorem class_body {kmin : ℕ} (hk : E.KMin kmin) {ι : Type U} {m : Bool} {cl : Paint}
    {b : Bank (portM cl) ι} {n h μ o BS : ι → ℕ} {J sup : ∀ i, ℕ → Bits (n i) → ℂ}
    {τ : ι → EngJob → ℕ}
    (hB2 : Small b.B (fun i => 2^(n i))) (hBS : Small b.B BS)
    (hd : ∀ i, E.Valid kmin (EngJob.cls (n i) (h i) (μ i) (o i) (BS i) (J i) (sup i)))
    (hkc : ∀ i c, c ∈ E.childJobs (EngJob.cls (n i) (h i) (μ i) (o i) (BS i) (J i) (sup i)) →
      (b.use i (E.encodeJob cl c)).OK (E.jobAnswer cl c) (τ i c) (b.ext i)) :
    Able m b (portIn cl) (portOut cl)
      (fun i => E.encodeJob cl (EngJob.cls (n i) (h i) (μ i) (o i) (BS i) (J i) (sup i)))
      (fun i => E.jobAnswer cl (EngJob.cls (n i) (h i) (μ i) (o i) (BS i) (J i) (sup i)))
      (fun i => E.clsLoc (n i) (h i) (μ i))
      (fun i => ((E.childJobs (EngJob.cls (n i) (h i) (μ i) (o i) (BS i) (J i) (sup i))).map (τ i)).sum) := by
  have F := fun i => E.valid_facts hk (hd i)

  let D : ∀ i, ℕ → EngJob := fun i k => EngJob.cls (n i) k (μ i) (o i) (BS i) (J i) (sup i)
  have hkind : Can m b.B (portIn cl) w (fun i => E.encodeJob cl (D i (h i))) h
      (fun i => E.clsLoc (n i) (h i) (μ i)) :=
    (Can.second.snd.fst.minus (Can.wc 1) ((hB2.add (Small.const _ 1)).mono fun i => by
      simp only [D, encodeJob, mkIn]; have := (F i).2.1; have := Nat.lt_two_pow_self (n := n i); omega)).cong
      (fun _ => rfl) fun i => by simp only [D, encodeJob, mkIn, Nat.add_sub_cancel]
  refine Able.branch hkind (fun i => h i = 0) (fun _ => Iff.rfl) ?_ ?_
  · have L := E.able_class_leaf (m := m) (b := b.comap fun i : {i // h i = 0} => i.1)
      (n := fun i => n i.1) (μ := fun i => μ i.1) (o := fun i => o i.1) (BS := fun i => BS i.1)
      (J := fun i => J i.1) (sup := fun i => sup i.1) (τ := fun i => τ i.1) (hB2.reindex _)
      (fun i => (F i.1).1 i.2) (fun i c hc => hkc i.1 c (by rw [i.2]; exact hc))
    exact (L.cong (fun i => congrArg (fun k => E.encodeJob cl (D i.1 k)) i.2.symm)
      (fun i => congrArg (fun k => E.jobAnswer cl (D i.1 k)) i.2.symm)).mono
      (fun i => by simp [clsLoc, i.2])
      (fun i => le_of_eq (congrArg (fun k => ((E.childJobs (D i.1 k)).map (τ i.1)).sum) i.2.symm))
  · have hpos : ∀ i : {i // ¬ h i = 0}, h i.1 - 1 + 1 = h i.1 := fun i => Nat.sub_add_cancel (Nat.pos_of_ne_zero i.2)
    have Up := E.able_class_up (m := m) (b := b.comap fun i : {i // ¬ h i = 0} => i.1)
      (n := fun i => n i.1) (h := fun i => h i.1 - 1) (μ := fun i => μ i.1) (o := fun i => o i.1)
      (BS := fun i => BS i.1) (J := fun i => J i.1) (sup := fun i => sup i.1) (τ := fun i => τ i.1)
      (hB2.reindex _) (hBS.reindex _)
      (fun i => by beta_reduce; have := (F i.1).2.1; have := i.2; omega)
      (fun i => (F i.1).2.2.1)
      (fun i => by beta_reduce; rw [hpos i]; exact (F i.1).2.2.2)
      (fun i c hc => hkc i.1 c (by rw [← hpos i]; exact hc))
    exact (Up.cong (fun i => congrArg (fun k => E.encodeJob cl (D i.1 k)) (hpos i))
      (fun i => congrArg (fun k => E.jobAnswer cl (D i.1 k)) (hpos i))).mono
      (fun i => by simp [clsLoc, i.2])
      (fun i => le_of_eq (congrArg (fun k => ((E.childJobs (D i.1 k)).map (τ i.1)).sum) (hpos i)))
end Body
end BlockEngine
end
end PowerSaving.RAM
end OAI
