import Submission.Work.MixedCost.TopBody

/-!
# Mixed engine, top body part 5: the bookkeeping and the whole top job

(agent e-r3cost, round wht45/lever, 19 Oct 2026.)

* `can_book`  from `n`: `2^n`, the root height `G`, the root's index and unit tables (e-r3prog's
              `can_index`, `can_units`), the consumption `cons n G 1` (`can_cons`); polynomial work `Ptop`;
* `top_body`  **the top job `Do(n, B)` as an open body over any bank**: naive below `n0` or with fewer
              than `N` vectors, else the tree branch; work `locTop`, charge the calls `kidsTop`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset GF MXR
noncomputable section

universe U

/-- `b^(n+1)` is polynomial in `2^n`. -/
lemma small_pow {ι : Type*} {Bd n : ι → ℕ} (h2 : Small Bd (fun e => 2^(n e))) (b : ℕ) :
    Small Bd (fun e => b^(n e + 1)) := by
  obtain ⟨d, hd⟩ := h2
  refine ⟨(d + 1) * b, fun e => ?_⟩
  have h1 : b^(n e + 1) ≤ (2^b)^(n e + 1) := Nat.pow_le_pow_left (Nat.lt_two_pow_self).le _
  have h2' : (2^b)^(n e + 1) = (2 * 2^(n e))^b := by
    rw [← pow_mul, show 2 * 2^(n e) = 2^(n e + 1) by ring, ← pow_mul, mul_comm]
  have h3 : 2 * 2^(n e) ≤ (Bd e + 2)^(d + 1) := by
    calc 2 * 2^(n e) ≤ (Bd e + 2) * (Bd e + 2)^d := Nat.mul_le_mul (by omega) (hd e)
      _ = (Bd e + 2)^(d + 1) := by ring
  calc b^(n e + 1) ≤ (2 * 2^(n e))^b := h2' ▸ h1
    _ ≤ ((Bd e + 2)^(d + 1))^b := Nat.pow_le_pow_left h3 _
    _ = (Bd e + 2)^((d + 1) * b) := by rw [← pow_mul]

namespace Eng
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ] (E : Eng α ρ σ)

/-- The bookkeeping work of a top job. -/
def Ptop (kmin n : ℕ) : ℕ :=
  (n + 1) + (n * (n + 3) + 1) + E.idxCost n (E.topG kmin n) 1 +
    E.NUc n (E.topG kmin n) 1 * (4 * n + 4 * E.topG kmin n + 8) + E.cstC (E.topG kmin n)

/-- The bookkeeping values. -/
abbrev BookT : Ty := p w (p w (p IdxT (p UnT w)))
def bookVal (kmin n : ℕ) : T BookT :=
  (2^n, E.topG kmin n, E.idxVal n (E.topG kmin n) 1, E.unitVal n (E.topG kmin n) 1, E.cons n (E.topG kmin n) 1)

lemma topG_le (kmin n : ℕ) : E.topG kmin n ≤ n := Nat.findGreatest_le n


variable {Ξ : Type U} {m : Bool} {s : Ty} {y : Ξ → T s}

/-- **The bookkeeping of a top job**, polynomial work `Ptop`. -/
lemma can_book (kmin : ℕ) (hk : 2 ≤ kmin) {Bd n : Ξ → ℕ} (hn : Knows m Bd s y n)
    (hI : Has m Bd s sc y (fun _ => Complex.I)) (h2 : Small Bd (fun e => 2^(n e))) (hn1 : ∀ e, 1 ≤ n e) :
    Can m Bd s BookT y (fun e => E.bookVal kmin (n e)) (fun e => E.Ptop kmin (n e)) := by
  let G (e : Ξ) := E.topG kmin (n e)
  have hns : Small Bd n := h2.mono (fun e => (Nat.lt_two_pow_self).le)
  have hGle : ∀ e, G e ≤ n e := fun e => E.topG_le kmin (n e)
  have hp2 : Can m Bd s w y (fun e => 2^(n e)) (fun e => E.Ptop kmin (n e)) :=
    (Can.wTwo (hn.mono (fun _ => Nat.zero_le _)) hns h2 (Dom.of_le (fun e => Nat.le_succ _))).mono
      (fun e => by unfold Eng.Ptop; omega)
  have hG : Can m Bd s w y G (fun e => E.Ptop kmin (n e)) :=
    (can_topG E kmin hk hn (small_pow h2 kmin) hns).mono (fun e => by unfold Eng.Ptop; (try simp only [G]); omega)
  let e1 (e : Ξ) : T (p s (p w w)) := (y e, (2^(n e), G e))
  have hE1 : Can m Bd s (p s (p w w)) y e1 (fun e => E.Ptop kmin (n e)) := Can.pair Can.id (Can.pair hp2 hG)
  have c1 : CIn m Bd (p s (p w w)) e1 n G (fun _ => 1) :=
    ⟨Can.first.then_do hn, Can.second.snd, Can.wc 1, Can.second.fst, Can.first.then_do hI, h2, hGle,
      Small.const _ 1⟩
  have hidx := E.can_index c1
  have hun := E.can_units c1
  have hidx' : Can m Bd (p s (p w w)) IdxT e1 (fun e => E.idxVal (n e) (G e) 1) (fun e => E.Ptop kmin (n e)) :=
    hidx.mono (fun e => by unfold Eng.Ptop; (try simp only [G]); omega)
  have hun' : Can m Bd (p (p s (p w w)) IdxT) UnT (fun e => (e1 e, E.idxVal (n e) (G e) 1))
      (fun e => E.unitVal (n e) (G e) 1) (fun e => E.Ptop kmin (n e)) :=
    hun.mono (fun e => by unfold Eng.Ptop; (try simp only [G]); omega)
  have hbnd : Small Bd (fun e => E.bndC (n e, G e, 1)) := by
    have hK := (small_pow h2 E.Kb)
    have h1 : Small Bd (fun e => n e + 2) := hns.add (Small.const _ 2)
    refine ((h1.mul hK).mul (Small.const _ 2)).mono (fun e => ?_)
    simp only [Eng.bndC]
    exact Nat.mul_le_mul (Nat.mul_le_mul le_rfl (Nat.pow_le_pow_right (by have := E.Kb_ge; omega)
      (by have := hGle e; omega))) (by omega)
  have hcin : Has m Bd (p s (p w w)) (p w (p w w)) e1 (fun e => (n e, G e, 1)) :=
    c1.nK.pair (c1.hK.pair (Can.wc 1))
  have hcons : Can m Bd (p s (p w w)) w e1 (fun e => E.cons (n e) (G e) 1) (fun e => E.Ptop kmin (n e)) :=
    (hcin.mono (fun _ => Nat.zero_le _)).then_do
      (((E.can_cons m (fun e => (n e, G e, 1))).ambient hbnd).mono (fun e => by unfold Eng.Ptop; (try simp only [G]); omega))
  have hall : Can m Bd (p s (p w w)) BookT e1 (fun e => E.bookVal kmin (n e)) (fun e => E.Ptop kmin (n e)) :=
    ((Can.second.fst.mono (fun _ => Nat.zero_le _)).pair ((Can.second.snd.mono (fun _ => Nat.zero_le _)).pair
      (hidx'.pair ((Can.bind hidx' hun').pair hcons)))).cong (fun _ => rfl) (fun e => rfl)
  exact hE1.then_do hall


/-- The local work of a top job. -/
def locTop (kmin n0 n B : ℕ) : ℕ :=
  if n0 ≤ n then (B + 1) * 2^n + (B % E.topN kmin n) * (n + 1) * 2^n + E.Ptop kmin n
  else (B + 1) * (n + 1) * 2^n + 1

lemma sum_map_flatMap {β γ : Type*} (L : List β) (f : β → List γ) (g : γ → ℕ) :
    ((L.flatMap f).map g).sum = (L.map (fun t => ((f t).map g).sum)).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [List.flatMap_cons, ih]

/-- The charge of the calls of a top job. -/
lemma kidsTop_charge (kmin n0 n Bv : ℕ) (v : ℕ → Bits n → ℂ) (tau : MDesc → ℕ) (h : n0 ≤ n ∧ E.topN kmin n ≤ Bv) :
    ((E.kidsTop kmin n0 n Bv v).map tau).sum = ∑ t ∈ Finset.range (Bv / E.topN kmin n),
      (tau (E.topRoot kmin n Bv v t) + ∑ jj ∈ Finset.range (E.topN kmin n), tau (E.topRest kmin n v t jj)) := by
  unfold kidsTop
  rw [if_pos h, sum_map_flatMap, ← sum_map_range]
  congr 1
  refine List.map_congr_left (fun t _ => ?_)
  simp only [List.map_cons, List.sum_cons, List.map_map]
  rw [sum_map_range]
  rfl

lemma mem_kidsTop_root (kmin n0 n Bv : ℕ) (v : ℕ → Bits n → ℂ) (h : n0 ≤ n ∧ E.topN kmin n ≤ Bv) (t : ℕ)
    (ht : t < Bv / E.topN kmin n) : E.topRoot kmin n Bv v t ∈ E.kidsTop kmin n0 n Bv v := by
  unfold kidsTop; rw [if_pos h]
  exact List.mem_flatMap.2 ⟨t, List.mem_range.2 ht, List.mem_cons_self⟩

lemma mem_kidsTop_rest (kmin n0 n Bv : ℕ) (v : ℕ → Bits n → ℂ) (h : n0 ≤ n ∧ E.topN kmin n ≤ Bv) (t jj : ℕ)
    (ht : t < Bv / E.topN kmin n) (hj : jj < E.topN kmin n) :
    E.topRest kmin n v t jj ∈ E.kidsTop kmin n0 n Bv v := by
  unfold kidsTop; rw [if_pos h]
  exact List.mem_flatMap.2 ⟨t, List.mem_range.2 ht,
    List.mem_cons_of_mem _ (List.mem_map.2 ⟨jj, List.mem_range.2 hj, rfl⟩)⟩

/-- The naive top job on all its vectors (OpenAI's `hills_program` on each). -/
lemma naive_top {Bd n Bv : Ξ → ℕ} {cl : Paint} {v : ∀ e, ℕ → Bits (n e) → ℂ}
    (hbig : Small Bd (fun e => (Bv e + 1) * 2^(n e))) :
    Can m Bd (portIn cl) (portOut cl) (fun e => E.enc cl (MDesc.top (n e) (Bv e) (v e)))
      (fun e => E.out cl (MDesc.top (n e) (Bv e) (v e))) (fun e => Bv e * ((n e + 1) * 2 ^ n e + 1)) := by
  have h2s : Small Bd (fun e => 2^(n e)) := hbig.mono (fun e => Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
  have hBs : Small Bd Bv := hbig.mono (fun e => by have : 1 ≤ 2^(n e) := Nat.one_le_two_pow; nlinarith)
  have hown : Has m Bd (portIn cl) (jobsT cl) (fun e => E.enc cl (MDesc.top (n e) (Bv e) (v e)))
      (fun e => jobsTape (n e) (Bv e) (v e)) := Can.second.snd.snd.snd.snd.fst
  have hsup : Has m Bd (portIn cl) (jobsT cl) (fun e => E.enc cl (MDesc.top (n e) (Bv e) (v e)))
      (fun e => jobsTape (n e) 0 (fun _ _ => 0)) := Can.second.snd.snd.snd.snd.snd
  have hBK : Knows m Bd (portIn cl) (fun e => E.enc cl (MDesc.top (n e) (Bv e) (v e))) Bv :=
    (hown.len hBs).cong (fun _ => rfl) (fun e => rfl)
  have hnv := MCost.naive_jobs (m := m) (cl := cl) (Bd := Bd) n Bv v hown Can.first hBK Can.second.fst hBs h2s
  have hEmp3 : Has m Bd (portIn cl) (a w) (fun e => E.enc cl (MDesc.top (n e) (Bv e) (v e)))
      (fun e => (Layout.std 0).tape (fun _ : Fin 0 => (0 : ℕ))) := by
    have H := Can.tab (m := m) (B := Bd) (s := portIn cl) (x := fun e => E.enc cl (MDesc.top (n e) (Bv e) (v e)))
      (t := w) (n := fun _ => 0) (uB := fun _ _ => 0) (v := fun _ _ => 0) (W := fun _ => 0)
      (Can.wc (W := fun _ => 0) 0) (Can.wc 0) (Small.const _ 0)
    exact (H.cong (fun _ => rfl) (fun e => sizes_zero.symm)).mono (fun e => by simp)
  refine ((hnv.mono (fun e => ?_)).pair ((hsup.mono (fun _ => Nat.zero_le _)).pair
    (hEmp3.mono (fun _ => Nat.zero_le _)))).cong (fun _ => rfl) (fun e => rfl)
  rw [Nat.mul_add, mul_one]


/-- **The top job `Do(n, B)` as an open body** over any bank whose handler answers its calls `kidsTop`:
naive below `n0` or with fewer than `N` vectors, else `B / N` tree copies (root class + rest calls),
the leftover naive.  Work `O(locTop)`, charge exactly the costs of the calls. -/
theorem top_body (kmin n0 : ℕ) (hk : 2 ≤ kmin) (hn0 : E.mx ≤ n0) {κ : Type U} {cl : Paint}
    {b : Bank (portM cl) κ} (n Bv : κ → ℕ) (v : ∀ k, ℕ → Bits (n k) → ℂ)
    (hbig : Small b.B (fun k => (Bv k + 1) * 2^(n k))) (tau : κ → MDesc → ℕ)
    (hcalls : ∀ k c, c ∈ E.kidsTop kmin n0 (n k) (Bv k) (v k) →
      (b.use k (E.enc cl c)).OK (E.out cl c) (tau k c) (b.ext k)) :
    Able m b (portIn cl) (portOut cl) (fun k => E.enc cl (MDesc.top (n k) (Bv k) (v k)))
      (fun k => E.out cl (MDesc.top (n k) (Bv k) (v k)))
      (fun k => E.locTop kmin n0 (n k) (Bv k))
      (fun k => ((E.kidsTop kmin n0 (n k) (Bv k) (v k)).map (tau k)).sum) := by
  let x (k : κ) : T (portIn cl) := E.enc cl (MDesc.top (n k) (Bv k) (v k))
  let Y (k : κ) : T (portOut cl) := E.out cl (MDesc.top (n k) (Bv k) (v k))
  let Wt (k : κ) := E.locTop kmin n0 (n k) (Bv k)
  let Zt (k : κ) := ((E.kidsTop kmin n0 (n k) (Bv k) (v k)).map (tau k)).sum
  have nK : Knows m b.B (portIn cl) x n := Can.first
  have t1 : Knows m b.B (portIn cl) x (fun k => if n k < n0 then 1 else 0) := nK.wlt (Can.wc n0)
  -- naive branch: n < n0
  have hnv : Able m (b.comap (fun k : {k // (if n k < n0 then 1 else 0) ≠ 0} => k.val)) (portIn cl) (portOut cl)
      (fun k => x k.val) (fun k => Y k.val) (fun k => Wt k.val) (fun k => Zt k.val) := by
    have hlt : ∀ k : {k // (if n k < n0 then 1 else 0) ≠ 0}, n k.val < n0 := by
      intro k; have := k.2; split_ifs at this with h1 <;> simp_all
    have H := naive_top E (m := m) (cl := cl) (Bd := fun k : {k // (if n k < n0 then 1 else 0) ≠ 0} => b.B k.val)
      (n := fun k => n k.val) (Bv := fun k => Bv k.val) (v := fun k => v k.val) (hbig.reindex Subtype.val)
    refine (Able.of_can H).weaken ⟨2, fun k => ?_⟩ (fun k => Nat.zero_le _)
    have h1 := hlt k
    show _ ≤ 2 * (E.locTop kmin n0 (n k.val) (Bv k.val) + 1)
    unfold Eng.locTop
    rw [if_neg (Nat.not_le.mpr h1)]
    generalize hX : (n k.val + 1) * 2 ^ n k.val = X
    have hX1 : 1 ≤ X := by rw [← hX]; exact Nat.mul_pos (Nat.succ_pos _) (Nat.two_pow_pos _)
    have e1 : (Bv k.val + 1) * (n k.val + 1) * 2 ^ n k.val = Bv k.val * X + X := by rw [← hX]; ring
    rw [e1]
    have : Bv k.val ≤ Bv k.val * X := Nat.le_mul_of_pos_right _ hX1
    nlinarith
  -- main branch: n0 ≤ n
  have hmain : Able m (b.comap (fun k : {k // (if n k < n0 then 1 else 0) = 0} => k.val)) (portIn cl) (portOut cl)
      (fun k => x k.val) (fun k => Y k.val) (fun k => Wt k.val) (fun k => Zt k.val) := by
    let κ0 := {k // (if n k < n0 then 1 else 0) = 0}
    let b0 := b.comap (fun k : κ0 => k.val)
    have hge : ∀ k : κ0, n0 ≤ n k.val := by
      intro k; have := k.2; split_ifs at this with h1 <;> omega
    let x0 (k : κ0) := x k.val
    have h2s : Small b0.B (fun k => 2^(n k.val)) :=
      (hbig.reindex Subtype.val).mono (fun k => Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
    have hBs : Small b0.B (fun k => Bv k.val) :=
      (hbig.reindex Subtype.val).mono (fun k => by have : 1 ≤ 2^(n k.val) := Nat.one_le_two_pow; nlinarith)
    have hbook := E.can_book (m := m) (s := portIn cl) (y := x0) kmin hk (Bd := b0.B) (n := fun k => n k.val)
      Can.first Can.second.fst h2s (fun k => le_trans (le_trans (le_trans (by norm_num) E.three) hn0) (hge k))
    let xm (k : κ0) : T (p (portIn cl) BookT) := (x0 k, E.bookVal kmin (n k.val))
    let Bm := b0.B
    have F : ∀ {t : Ty} {z : κ0 → T t}, Has m Bm (portIn cl) t x0 z → Has m Bm (p (portIn cl) BookT) t xm z :=
      fun g => Can.first.then_do g
    have nK' : Knows m Bm (p (portIn cl) BookT) xm (fun k => n k.val) := F Can.first
    have IK : Has m Bm (p (portIn cl) BookT) sc xm (fun _ => Complex.I) := F Can.second.fst
    have hown : Has m Bm (p (portIn cl) BookT) (jobsT cl) xm (fun k => jobsTape (n k.val) (Bv k.val) (v k.val)) :=
      F Can.second.snd.snd.snd.snd.fst
    have hsup : Has m Bm (p (portIn cl) BookT) (jobsT cl) xm (fun k => jobsTape 0 0 (fun _ _ => 0)) :=
      (F Can.second.snd.snd.snd.snd.snd).cong (fun _ => rfl)
        (fun k => jobsTape_zero (n k.val) 0 (fun _ _ => 0) (fun _ _ => 0))
    have BK : Knows m Bm (p (portIn cl) BookT) xm (fun k => Bv k.val) :=
      (hown.len hBs).cong (fun _ => rfl) (fun k => rfl)
    have p2K : Knows m Bm (p (portIn cl) BookT) xm (fun k => 2^(n k.val)) := Can.second.fst
    have GK : Knows m Bm (p (portIn cl) BookT) xm (fun k => E.topG kmin (n k.val)) := Can.second.snd.fst
    have NUK : Knows m Bm (p (portIn cl) BookT) xm (fun k => E.topNU0 kmin (n k.val)) :=
      Can.second.snd.snd.fst.snd.fst
    have cUK : Has m Bm (p (portIn cl) BookT) (a w) xm
        (fun k => (Layout.std (E.topNU0 kmin (n k.val))).tape (fun p => E.cUc (n k.val) (E.topG kmin (n k.val)) 1 p)) :=
      Can.second.snd.snd.snd.fst.fst
    have consK : Knows m Bm (p (portIn cl) BookT) xm (fun k => E.cons (n k.val) (E.topG kmin (n k.val)) 1) :=
      Can.second.snd.snd.snd.snd
    have hnS : Small Bm (fun k => n k.val) := h2s.mono (fun k => (Nat.lt_two_pow_self).le)
    have hGle : ∀ k : κ0, E.topG kmin (n k.val) ≤ n k.val := fun k => E.topG_le _ _
    have hNUs : Small Bm (fun k => E.topNU0 kmin (n k.val)) :=
      (small_pow h2s E.W).mono (fun k => le_trans (MXR.NU_le _ _ _)
        (Nat.pow_le_pow_right E.W_pos (by have := hGle k; omega)))
    have hcs : Small Bm (fun k => E.cons (n k.val) (E.topG kmin (n k.val)) 1) :=
      (small_pow h2s (E.Ac^2)).mono (fun k => le_trans (E.cons_le _ _ _) (by
        rw [pow_mul]; exact Nat.pow_le_pow_right (Nat.one_le_pow _ _ E.Ac_pos) (by have := hGle k; omega)))
    have hNK : Knows m Bm (p (portIn cl) BookT) xm (fun k => E.topN kmin (n k.val)) :=
      (NUK.times (Can.wc E.W) hNUs (Small.const _ _)).plus consK (hNUs.mul (Small.const _ _)) hcs
    have t2 : Knows m Bm (p (portIn cl) BookT) xm (fun k => if Bv k.val < E.topN kmin (n k.val) then 1 else 0) :=
      BK.wlt hNK
    let W2 (k : κ0) := (Bv k.val + 1) * 2^(n k.val) + (Bv k.val % E.topN kmin (n k.val)) * (n k.val + 1) * 2^(n k.val)
    -- the tree branch
    have htree : Able m (b0.comap (fun k : {k : κ0 // (if Bv k.val < E.topN kmin (n k.val) then 1 else 0) = 0} => k.val))
        (p (portIn cl) BookT) (portOut cl) (fun k => xm k.val) (fun k => Y k.val.val) (fun k => W2 k.val)
        (fun k => Zt k.val.val) := by
      let κ1 := {k : κ0 // (if Bv k.val < E.topN kmin (n k.val) then 1 else 0) = 0}
      have hNB : ∀ k : κ1, E.topN kmin (n k.val.val) ≤ Bv k.val.val := by
        intro k; have := k.2; split_ifs at this with h1 <;> omega
      have hcond : ∀ k : κ1, n0 ≤ n k.val.val ∧ E.topN kmin (n k.val.val) ≤ Bv k.val.val :=
        fun k => ⟨hge k.val, hNB k⟩
      have G1 : ∀ {t : Ty} {z : κ0 → T t}, Has m Bm (p (portIn cl) BookT) t xm z →
          Has m (fun k : κ1 => Bm k.val) (p (portIn cl) BookT) t (fun k => xm k.val) (fun k => z k.val) :=
        fun g => g.reindex Subtype.val
      have hlamK : Knows m Bm (p (portIn cl) BookT) xm (fun k => Bv k.val / E.topN kmin (n k.val)) :=
        BK.dvdW hNK hBs
      have H := tree_branch E (b := b0.comap (fun k : κ1 => k.val)) (y := fun k => xm k.val) kmin
        (n := fun k => n k.val.val) (Bv := fun k => Bv k.val.val)
        (lam := fun k => Bv k.val.val / E.topN kmin (n k.val.val)) (v := fun k => v k.val.val)
        (fun _ => rfl) hNB (G1 nK') (G1 BK) (G1 GK) (G1 NUK) (G1 hNK) (G1 hlamK) (G1 p2K) (G1 hown) (G1 cUK)
        (G1 IK) (G1 hsup) (hbig.reindex (fun k : κ1 => k.val.val)) (tau := fun k => tau k.val.val)
        (fun k t ht => hcalls k.val.val _ (E.mem_kidsTop_root kmin n0 _ _ _ (hcond k) t ht))
        (fun k t jj ht hj => hcalls k.val.val _ (E.mem_kidsTop_rest kmin n0 _ _ _ (hcond k) t jj ht hj))
      refine H.mono (fun k => le_rfl) (fun k => le_of_eq ?_)
      exact (E.kidsTop_charge kmin n0 _ _ _ _ (hcond k)).symm
    -- the naive branch: fewer than one copy
    have hfew : Able m (b0.comap (fun k : {k : κ0 // (if Bv k.val < E.topN kmin (n k.val) then 1 else 0) ≠ 0} => k.val))
        (p (portIn cl) BookT) (portOut cl) (fun k => xm k.val) (fun k => Y k.val.val) (fun k => W2 k.val)
        (fun k => Zt k.val.val) := by
      let κ2 := {k : κ0 // (if Bv k.val < E.topN kmin (n k.val) then 1 else 0) ≠ 0}
      have hlt : ∀ k : κ2, Bv k.val.val < E.topN kmin (n k.val.val) := by
        intro k; have := k.2; split_ifs at this with h1 <;> simp_all
      have H := naive_top E (m := m) (cl := cl) (Bd := fun k : κ2 => Bm k.val)
        (n := fun k => n k.val.val) (Bv := fun k => Bv k.val.val) (v := fun k => v k.val.val)
        (hbig.reindex (fun k : κ2 => k.val.val))
      have H' : Can m (fun k : κ2 => Bm k.val) (p (portIn cl) BookT) (portOut cl) (fun k => xm k.val)
          (fun k => Y k.val.val) (fun k => Bv k.val.val * ((n k.val.val + 1) * 2 ^ n k.val.val + 1)) :=
        (Can.first.mono (fun _ => Nat.zero_le _)).then_do H
      refine (Able.of_can H').weaken ⟨2, fun k => ?_⟩ (fun k => Nat.zero_le _)
      show _ ≤ 2 * (W2 k.val + 1)
      simp only [W2]
      rw [Nat.mod_eq_of_lt (hlt k)]
      have h1 : 1 ≤ 2^(n k.val.val) := Nat.one_le_two_pow
      have e1 : Bv k.val.val * ((n k.val.val + 1) * 2 ^ n k.val.val + 1) =
          Bv k.val.val * (n k.val.val + 1) * 2 ^ n k.val.val + Bv k.val.val := by ring
      rw [e1]
      have : Bv k.val.val ≤ (Bv k.val.val + 1) * 2^(n k.val.val) := by nlinarith
      omega
    have H2 := Able.ifz (t := portOut cl) (x := xm) (y := fun k => Y k.val) (W := W2) (Z := fun k => Zt k.val)
      (Able.of_can t2) htree hfew
    have H3 := Able.save (Able.of_can (b := b0) hbook) H2
    refine (H3.mono (fun k => ?_) (fun k => ?_))
    · show E.Ptop kmin (n k.val) + (0 + W2 k) ≤ E.locTop kmin n0 (n k.val) (Bv k.val)
      unfold Eng.locTop
      rw [if_pos (hge k)]
      simp only [W2]; omega
    · simp
  have H := Able.ifz (t := portOut cl) (y := Y) (W := Wt) (Z := Zt) (Able.of_can t1) hmain hnv
  exact H.mono (fun k => le_of_eq (zero_add _)) (fun k => le_of_eq (zero_add _))

end Eng

end
end PowerSaving.RAM
end OAI

#print axioms OAI.PowerSaving.RAM.Eng.can_book
#print axioms OAI.PowerSaving.RAM.Eng.top_body
