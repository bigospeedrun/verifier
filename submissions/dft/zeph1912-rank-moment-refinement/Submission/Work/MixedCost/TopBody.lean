import Submission.Work.MixedCost.TopRest
import Submission.Work.MixedCost.TopCount
import Submission.Work.MixedCost.Naive
import Submission.Work.Mixed.Prog.ClassTabs

/-!
# Mixed engine, top body part 4: the top job `Do(n, B)` as an open body

(agent e-r3cost, round wht45/lever, 19 Oct 2026; against e-r3prog's `Desc.lean` (port, descriptors) and
`ClassTabs.lean` (the root's unit tables).)

* `rest_elem`  one source vector of a copy: its size, `2^size`, ONE rest call (`rest_call`);
* `copy_elem`  one tree copy: ONE root class call, then one rest call per vector of the copy;
* …
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset GF MXR
noncomputable section

universe U

lemma look_tab {α : Type*} (n : ℕ) (f : ℕ → α) (j : ℕ) (z : α) (h : j < n) : (Tape.tab n f).look j z = f j := by
  simp [Tape.look, Tape.tab, h]

section Elems
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ] (E : Eng α ρ σ)
variable {Ξ : Type U} {m : Bool} {cl : Paint} {b : Bank (portM cl) Ξ} {s : Ty} {y : Ξ → T s}

/-- **One source vector of a copy**: `2^size`, then ONE rest call; answers `(2^size, rest answers)`. -/
lemma rest_elem {n sz : Ξ → ℕ} (hs : ∀ e, sz e ≤ n e) {wv : ∀ e, Bits (n e) → ℂ}
    (hw : Has m b.B s (a (c cl)) y (fun e => (bits (n e)).tape (wv e)))
    (hn : Knows m b.B s y n) (hsz : Knows m b.B s y sz)
    (hI : Has m b.B s sc y (fun _ => Complex.I))
    (hemp : Has m b.B s (jobsT cl) y (fun e => jobsTape 0 0 (fun _ _ => 0)))
    (hbig : Small b.B (fun e => 2^(n e)))
    {Z : Ξ → ℕ}
    (hcall : ∀ e, (b.use e (E.enc cl (MDesc.top (n e - sz e) (2^(sz e)) (hiVec (n e) (sz e) (wv e))))).OK
      (E.out cl (MDesc.top (n e - sz e) (2^(sz e)) (hiVec (n e) (sz e) (wv e)))) (Z e) (b.ext e)) :
    Able m b s (p w (jobsT cl)) y
      (fun e => (2^(sz e), jobsTape (n e - sz e) (2^(sz e))
        (fun q => ripple (n e - sz e) (hiVec (n e) (sz e) (wv e) q))))
      (fun e => (n e + 1) + (0 + 2^(n e))) (fun e => 0 + (0 + Z e)) := by
  have hns : Small b.B n := hbig.mono (fun e => (Nat.lt_two_pow_self).le)
  have h1s : Small b.B (fun e => 2^(sz e)) := hbig.mono (fun e => Nat.pow_le_pow_right (by omega) (hs e))
  have h2s : Small b.B (fun e => 2^(n e - sz e)) :=
    hbig.mono (fun e => Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _))
  have hd : Knows m b.B s y (fun e => n e - sz e) := hn.minus hsz hns
  have hP1 : Can m b.B s w y (fun e => 2^(sz e)) (fun e => n e + 1) :=
    Can.wTwo (hsz.mono (fun _ => Nat.zero_le _)) (hns.mono hs) h1s (Dom.of_le (fun e => by have := hs e; omega))
  have hP2 : Can m b.B s w y (fun e => 2^(n e - sz e)) (fun e => n e + 1) :=
    Can.wTwo (hd.mono (fun _ => Nat.zero_le _)) (hns.mono (fun e => Nat.sub_le _ _)) h2s
      (Dom.of_le (fun e => by omega))
  have hP := hP1.pair hP2
  let y' (e : Ξ) : T (p s (p w w)) := (y e, (2^(sz e), 2^(n e - sz e)))
  have F : ∀ {t : Ty} {z : Ξ → T t}, Has m b.B s t y z → Has m b.B (p s (p w w)) t y' z :=
    fun g => Can.first.then_do g
  have hR := rest_call (cl := cl) E (b := b) (x := y') hs (F hw) (F hn) (F hsz) (Can.second.fst) (Can.second.snd)
    (F hI) (F hemp) hbig hcall
  exact Able.save (Able.of_can hP) (Able.fork (Able.of_can (Can.second.fst)) hR)


/-- Every consumed source size is at most `n`. -/
lemma srcSizes_le (n : ℕ) : ∀ h μ, ∀ z ∈ E.srcSizes n h μ, z ≤ n := by
  intro h
  induction h with
  | zero => intro μ z hz; simp [Eng.srcSizes] at hz
  | succ h ih =>
    intro μ z hz
    simp only [Eng.srcSizes, List.mem_flatMap, List.mem_append] at hz
    obtain ⟨r, -, hz | hz⟩ := hz
    · simp only [Eng.ownSrc, List.mem_filterMap, List.mem_range] at hz
      obtain ⟨t, ht, hz⟩ := hz
      split_ifs at hz with hsrc
      · simp only [Option.some.injEq] at hz
        subst hz
        have hp : t / E.W < E.NUc n h (μ * r) := (Nat.div_lt_iff_lt_mul E.W_pos).2 ht
        have h1 := E.tq_le (t % E.W)
        have h2 := MXR.U_fits hp (W := E.W) (tq := E.tq) (mx := E.mx)
        unfold Eng.slotSize
        calc E.tq (t % E.W) * E.cUc n h (μ * r) (t / E.W) ≤ E.mx * E.cUc n h (μ * r) (t / E.W) :=
              Nat.mul_le_mul_right _ h1
          _ ≤ n := h2
    · exact ih _ z hz

lemma csz_le (n h μ k : ℕ) : E.csz n h μ k ≤ n := by
  unfold Eng.csz
  by_cases hk : k < (E.srcSizes n h μ).length
  · rw [List.getD_eq_getElem _ _ hk]
    exact srcSizes_le E n h μ _ (List.getElem_mem hk)
  · rw [List.getD_eq_default _ _ (by omega)]; exact Nat.zero_le _

lemma slotSize_le (n h μ t : ℕ) (ht : t < E.NUc n h μ * E.W) : E.slotSize n h μ t ≤ n := by
  have hp : t / E.W < E.NUc n h μ := (Nat.div_lt_iff_lt_mul E.W_pos).2 ht
  have h1 := E.tq_le (t % E.W)
  have h2 := MXR.U_fits hp (W := E.W) (tq := E.tq) (mx := E.mx)
  unfold Eng.slotSize
  calc E.tq (t % E.W) * E.cUc n h μ (t / E.W) ≤ E.mx * E.cUc n h μ (t / E.W) := Nat.mul_le_mul_right _ h1
    _ ≤ n := h2

lemma topSz_le (kmin n j : ℕ) : E.topSz kmin n j ≤ n := by
  unfold Eng.topSz
  split_ifs with hj
  · exact slotSize_le E _ _ _ _ hj
  · exact csz_le E _ _ _ _


/-- The answers of the rest call of vector `jj` of copy `t`. -/
def restT (kmin n : ℕ) (v : ℕ → Bits n → ℂ) (t jj : ℕ) : Tape (Tape ℂ) :=
  jobsTape (n - E.topSz kmin n jj) (2^(E.topSz kmin n jj))
    (fun q => ripple (n - E.topSz kmin n jj) (hiVec n (E.topSz kmin n jj) (E.topAns kmin n v t jj) q))

/-- **One tree copy**: ONE root class call, then one rest call per vector of the copy. -/
lemma copy_elem (kmin : ℕ) {n Bv cc : Ξ → ℕ} {v : ∀ e, ℕ → Bits (n e) → ℂ}
    (hfit : ∀ e, (cc e + 1) * E.topN kmin (n e) ≤ Bv e) (hcB : ∀ e, cc e ≤ Bv e)
    (hn : Knows m b.B s y n) (hc : Knows m b.B s y cc)
    (hG : Knows m b.B s y (fun e => E.topG kmin (n e)))
    (hNU : Knows m b.B s y (fun e => E.topNU0 kmin (n e)))
    (hN : Knows m b.B s y (fun e => E.topN kmin (n e)))
    (hown : Has m b.B s (jobsT cl) y (fun e => jobsTape (n e) (Bv e) (v e)))
    (hcU : Has m b.B s (a w) y
      (fun e => (Layout.std (E.topNU0 kmin (n e))).tape (fun p => E.cUc (n e) (E.topG kmin (n e)) 1 p)))
    (hI : Has m b.B s sc y (fun _ => Complex.I))
    (hemp : Has m b.B s (jobsT cl) y (fun e => jobsTape 0 0 (fun _ _ => 0)))
    (hbig : Small b.B (fun e => (Bv e + 1) * 2^(n e)))
    {Zr : Ξ → ℕ} {Zs : Ξ → ℕ → ℕ}
    (hroot : ∀ e, (b.use e (E.enc cl (E.topRoot kmin (n e) (Bv e) (v e) (cc e)))).OK
      (E.out cl (E.topRoot kmin (n e) (Bv e) (v e) (cc e))) (Zr e) (b.ext e))
    (hrest : ∀ e jj, jj < E.topN kmin (n e) →
      (b.use e (E.enc cl (E.topRest kmin (n e) (v e) (cc e) jj))).OK
        (E.out cl (E.topRest kmin (n e) (v e) (cc e) jj)) (Zs e jj) (b.ext e)) :
    Able m b s (a (p w (jobsT cl))) y
      (fun e => Tape.tab (E.topN kmin (n e))
        (fun jj => (2^(E.topSz kmin (n e) jj), restT E kmin (n e) (v e) (cc e) jj)))
      (fun e => E.topNU0 kmin (n e) * E.W + 0 + (0 + (0 + E.topN kmin (n e) +
        ∑ jj ∈ Finset.range (E.topN kmin (n e)), ((n e + 1) + (0 + 2^(n e))))))
      (fun e => 0 + Zr e + (0 + ∑ jj ∈ Finset.range (E.topN kmin (n e)), (0 + (0 + Zs e jj)))) := by
  let G (e : Ξ) := E.topG kmin (n e)
  let NU0 (e : Ξ) := E.topNU0 kmin (n e)
  let N (e : Ξ) := E.topN kmin (n e)
  have hNUN : ∀ e, NU0 e * E.W ≤ N e := fun e => Nat.le_add_right _ _
  have h2n : Small b.B (fun e => 2^(n e)) := hbig.mono (fun e => Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
  have hBs : Small b.B Bv := hbig.mono (fun e => by
    have : 1 ≤ 2^(n e) := Nat.one_le_two_pow
    nlinarith)
  have hNle : ∀ e, N e ≤ Bv e := fun e => le_trans (by nlinarith) (hfit e)
  have hNs : Small b.B N := hBs.mono hNle
  have hcs : Small b.B cc := hBs.mono hcB
  have hns : Small b.B n := h2n.mono (fun e => (Nat.lt_two_pow_self).le)
  have hNUs : Small b.B (fun e => NU0 e * E.W) := hNs.mono hNUN
  have hNUs1 : Small b.B NU0 := hNUs.mono (fun e => Nat.le_mul_of_pos_right _ E.W_pos)
  have hGs : Small b.B G := hns.mono (fun e => Nat.findGreatest_le _)
  have hNUW : Knows m b.B s y (fun e => NU0 e * E.W) := hNU.times (Can.wc E.W) hNUs1 (Small.const _ _)
  -- the root's own jobs: the first `NU0 * W` vectors of the copy
  let Q := Σ e, Fin (NU0 e * E.W)
  let σ : Q → Ξ := Sigma.fst
  let yq (d : Q) : T (p s w) := (y d.1, (Layout.std (NU0 d.1 * E.W)).loc d.2)
  have hlt : ∀ d : Q, cc d.1 * N d.1 + d.2.val < Bv d.1 := by
    intro d
    have h1 := d.2.2
    have h2 := hNUN d.1
    have h3 := hfit d.1
    calc cc d.1 * N d.1 + d.2.val < cc d.1 * N d.1 + N d.1 := by omega
      _ = (cc d.1 + 1) * N d.1 := by ring
      _ ≤ Bv d.1 := h3
  have hadr : Knows m (fun d : Q => b.B d.1) (p s w) yq (fun d => (Layout.std (Bv d.1)).loc
      (⟨cc d.1 * N d.1 + d.2.val, hlt d⟩ : Fin (Bv d.1))) := by
    have h1 : Knows m (fun d : Q => b.B d.1) (p s w) yq (fun d => cc d.1 * N d.1) :=
      Can.first.then_do ((hc.times hN hcs hNs).reindex σ)
    exact (h1.plus Can.second ((hcs.mul hNs).reindex σ) ((hNUs.reindex σ).mono (fun d => d.2.2.le))).cong
      (fun _ => rfl) (fun d => rfl)
  have hfetch : Has m (fun d : Q => b.B d.1) (p s w) (a (c cl)) yq
      (fun d => (bits (n d.1)).tape (v d.1 (cc d.1 * N d.1 + d.2.val))) :=
    Can.fetch (t := a (c cl)) (L := fun d : Q => Layout.std (Bv d.1))
      (v := fun d : Q => fun t : Fin (Bv d.1) => (bits (n d.1)).tape (v d.1 t))
      (i := fun d : Q => (⟨cc d.1 * N d.1 + d.2.val, hlt d⟩ : Fin (Bv d.1)))
      (Can.first.then_do (hown.reindex σ)) hadr
  have hownR : Can m b.B s (jobsT cl) y
      (fun e => jobsTape (n e) (E.NUc (n e) (G e) 1 * E.W) (fun j => v e (cc e * N e + j)))
      (fun e => NU0 e * E.W) := by
    have H := Can.layout (L := fun e => Layout.std (NU0 e * E.W)) (t := a (c cl)) (P := fun _ => 0)
      (v := fun e t => (bits (n e)).tape (v e (cc e * N e + t))) hNUW (hfetch.mono (fun _ => Nat.zero_le _)) hNUs
    refine H.mono (fun e => ?_)
    show 0 + NU0 e * E.W + NU0 e * E.W * 0 ≤ NU0 e * E.W
    simp
  -- the root's input and the call
  have hin : Can m b.B s (portIn cl) y (fun e => E.enc cl (E.topRoot kmin (n e) (Bv e) (v e) (cc e)))
      (fun e => NU0 e * E.W) := by
    have hoff : Knows m b.B s y (fun e => cc e * N e + NU0 e * E.W) :=
      (hc.times hN hcs hNs).plus hNUW (hcs.mul hNs) hNUs
    refine ((hn.mono (fun _ => Nat.zero_le _)).pair ((hI.mono (fun _ => Nat.zero_le _)).pair
      (((hG.plus (Can.wc 1) hGs (Small.const _ 1)).mono (fun _ => Nat.zero_le _)).pair
      ((Can.wc 1).pair ((hoff.mono (fun _ => Nat.zero_le _)).pair (hownR.pair
        (hown.mono (fun _ => Nat.zero_le _)))))))).cong (fun _ => rfl) (fun e => ?_)
    rfl
  have hcall := (Able.of_can (b := b) hin).comp (Able.use_call (m := m) (b := b) hroot)
  -- the rest calls, one per vector of the copy, in the environment `(y, root answers)`
  let R (e : Ξ) : T (portOut cl) := E.out cl (E.topRoot kmin (n e) (Bv e) (v e) (cc e))
  let s2 : Ty := p s (portOut cl)
  let y2 (e : Ξ) : T s2 := (y e, R e)
  let Dd := During (fun e => N e)
  let σd : Dd → Ξ := During.i
  let y3 (d : Dd) : T (p s2 w) := (y2 d.i, d.j)
  let Bd (d : Dd) := b.B d.i
  have F : ∀ {t : Ty} {z : Ξ → T t}, Has m b.B s t y z → Has m Bd (p s2 w) t y3 (fun d => z d.i) :=
    fun g => (Can.first.then_do Can.first).then_do (g.reindex σd)
  have hR : Has m Bd (p s2 w) (portOut cl) y3 (fun d => R d.i) := Can.first.then_do Can.second
  have jK : Knows m Bd (p s2 w) y3 (fun d => d.j) := Can.second
  have hjs : Small Bd (fun d => d.j) := (hNs.reindex σd).mono (fun d => d.hj.le)
  have hNUWd : Knows m Bd (p s2 w) y3 (fun d => NU0 d.i * E.W) := F hNUW
  have tK : Knows m Bd (p s2 w) y3 (fun d => 1 - (if d.j < NU0 d.i * E.W then 1 else 0)) :=
    (Can.wc 1).wsub (jK.wlt hNUWd) ((Small.const _ 1).mono (fun _ => Nat.sub_le _ _))
  have hN1 : ∀ d : Dd, d.j < NU0 d.i * E.W + E.cons (n d.i) (G d.i) 1 := fun d => d.hj
  -- the answered vector
  have hwv : Has m Bd (p s2 w) (a (c cl)) y3
      (fun d => (bits (n d.i)).tape (E.topAns kmin (n d.i) (v d.i) (cc d.i) d.j)) := by
    apply Can.testz tK
    · -- own slot
      have hlt : ∀ d : {d : Dd // 1 - (if d.j < NU0 d.i * E.W then 1 else 0) = 0}, d.1.j < NU0 d.1.i * E.W := by
        intro d; have := d.2; split_ifs at this with h1 <;> omega
      refine (Can.fetch (t := a (c cl))
        (L := fun d : {d : Dd // 1 - (if d.j < NU0 d.i * E.W then 1 else 0) = 0} =>
          Layout.std (E.NUc (n d.1.i) (G d.1.i) 1 * E.W))
        (v := fun d t => (bits (n d.1.i)).tape (hlow (n d.1.i) (E.slotSize (n d.1.i) (G d.1.i) 1 t)
          (v d.1.i (cc d.1.i * N d.1.i + t))))
        (i := fun d => ⟨d.1.j, hlt d⟩) (hR.fst.reindex Subtype.val) (jK.reindex Subtype.val)).cong
        (fun _ => rfl) (fun d => ?_)
      unfold Eng.topAns Eng.topSz
      rw [if_pos (hlt d)]
    · -- consumed source
      have hge : ∀ d : {d : Dd // 1 - (if d.j < NU0 d.i * E.W then 1 else 0) ≠ 0}, NU0 d.1.i * E.W ≤ d.1.j := by
        intro d; have := d.2; split_ifs at this with h1 <;> omega
      have hlt : ∀ d : {d : Dd // 1 - (if d.j < NU0 d.i * E.W then 1 else 0) ≠ 0},
          d.1.j - NU0 d.1.i * E.W < E.cons (n d.1.i) (G d.1.i) 1 := by
        intro d; have := hN1 d.1; have := hge d; omega
      have hadr : Knows m (fun d : {d : Dd // 1 - (if d.j < NU0 d.i * E.W then 1 else 0) ≠ 0} => Bd d.1) (p s2 w)
          (fun d => y3 d.1) (fun d => d.1.j - NU0 d.1.i * E.W) :=
        (jK.reindex Subtype.val).minus (hNUWd.reindex Subtype.val) (hjs.reindex Subtype.val)
      refine (Can.fetch (t := a (c cl))
        (L := fun d : {d : Dd // 1 - (if d.j < NU0 d.i * E.W then 1 else 0) ≠ 0} =>
          Layout.std (E.cons (n d.1.i) (G d.1.i) 1))
        (v := fun d k => (bits (n d.1.i)).tape (hlow (n d.1.i) (E.csz (n d.1.i) (G d.1.i) 1 k)
          (v d.1.i (cc d.1.i * N d.1.i + NU0 d.1.i * E.W + k))))
        (i := fun d => ⟨d.1.j - NU0 d.1.i * E.W, hlt d⟩) (hR.snd.fst.reindex Subtype.val) hadr).cong
        (fun _ => rfl) (fun d => ?_)
      unfold Eng.topAns Eng.topSz
      rw [if_neg (Nat.not_lt.mpr (hge d))]
      have e1 : cc d.1.i * N d.1.i + NU0 d.1.i * E.W + (d.1.j - NU0 d.1.i * E.W) = cc d.1.i * N d.1.i + d.1.j := by
        have := hge d; omega
      simp only [e1]
      rfl
  -- its size
  have hsz : Knows m Bd (p s2 w) y3 (fun d => E.topSz kmin (n d.i) d.j) := by
    apply Can.testz tK
    · have hlt : ∀ d : {d : Dd // 1 - (if d.j < NU0 d.i * E.W then 1 else 0) = 0}, d.1.j < NU0 d.1.i * E.W := by
        intro d; have := d.2; split_ifs at this with h1 <;> omega
      let κ0 := {d : Dd // 1 - (if d.j < NU0 d.i * E.W then 1 else 0) = 0}
      have hdiv : Knows m (fun d : κ0 => Bd d.1) (p s2 w) (fun d => y3 d.1) (fun d => d.1.j / E.W) :=
        (jK.reindex Subtype.val).dvdW (Can.wc E.W) (hjs.reindex Subtype.val)
      have hmod : Knows m (fun d : κ0 => Bd d.1) (p s2 w) (fun d => y3 d.1) (fun d => d.1.j % E.W) :=
        (jK.reindex Subtype.val).modW (Can.wc E.W) (hjs.reindex Subtype.val)
      have htq := E.knows_tq hmod (fun d => Nat.mod_lt _ E.W_pos)
      have hdlt : ∀ d : κ0, d.1.j / E.W < NU0 d.1.i := fun d => (Nat.div_lt_iff_lt_mul E.W_pos).2 (hlt d)
      have hcu : Knows m (fun d : κ0 => Bd d.1) (p s2 w) (fun d => y3 d.1)
          (fun d => E.cUc (n d.1.i) (G d.1.i) 1 (d.1.j / E.W)) :=
        Can.fetch (t := w) (L := fun d : κ0 => Layout.std (NU0 d.1.i))
          (v := fun d (p : Fin (NU0 d.1.i)) => E.cUc (n d.1.i) (G d.1.i) 1 p) (i := fun d => ⟨d.1.j / E.W, hdlt d⟩)
          ((F hcU).reindex Subtype.val) hdiv
      have hcus : Small (fun d : κ0 => Bd d.1) (fun d => E.cUc (n d.1.i) (G d.1.i) 1 (d.1.j / E.W)) :=
        ((hns.reindex σd).reindex Subtype.val).mono (fun d => E.cU_le _ _ _ ⟨_, hdlt d⟩)
      refine (htq.times hcu ((Small.const _ E.mx).mono (fun d => E.tq_le _)) hcus).cong (fun _ => rfl) (fun d => ?_)
      unfold Eng.topSz
      rw [if_pos (hlt d)]
      rfl
    · have hge : ∀ d : {d : Dd // 1 - (if d.j < NU0 d.i * E.W then 1 else 0) ≠ 0}, NU0 d.1.i * E.W ≤ d.1.j := by
        intro d; have := d.2; split_ifs at this with h1 <;> omega
      have hlt : ∀ d : {d : Dd // 1 - (if d.j < NU0 d.i * E.W then 1 else 0) ≠ 0},
          d.1.j - NU0 d.1.i * E.W < E.cons (n d.1.i) (G d.1.i) 1 := by
        intro d; have := hN1 d.1; have := hge d; omega
      have hadr : Knows m (fun d : {d : Dd // 1 - (if d.j < NU0 d.i * E.W then 1 else 0) ≠ 0} => Bd d.1) (p s2 w)
          (fun d => y3 d.1) (fun d => d.1.j - NU0 d.1.i * E.W) :=
        (jK.reindex Subtype.val).minus (hNUWd.reindex Subtype.val) (hjs.reindex Subtype.val)
      refine (Can.fetch (t := w)
        (L := fun d : {d : Dd // 1 - (if d.j < NU0 d.i * E.W then 1 else 0) ≠ 0} =>
          Layout.std (E.cons (n d.1.i) (G d.1.i) 1))
        (v := fun d k => E.csz (n d.1.i) (G d.1.i) 1 k)
        (i := fun d => ⟨d.1.j - NU0 d.1.i * E.W, hlt d⟩) (hR.snd.snd.reindex Subtype.val) hadr).cong
        (fun _ => rfl) (fun d => ?_)
      unfold Eng.topSz
      rw [if_neg (Nat.not_lt.mpr (hge d))]
  -- the rest call
  have hElem := rest_elem E (b := b.comap σd) (y := y3) (n := fun d => n d.i)
    (sz := fun d => E.topSz kmin (n d.i) d.j) (fun d => topSz_le E _ _ _)
    (wv := fun d => E.topAns kmin (n d.i) (v d.i) (cc d.i) d.j) hwv (F hn) hsz (F hI) (F hemp)
    (h2n.reindex σd) (Z := fun d => Zs d.i d.j) (fun d => hrest d.i d.j d.hj)
  have hTab := Able.tab (b := b) (s := s2) (t := p w (jobsT cl)) (x := y2) (n := N) (v := fun e jj => (2^(E.topSz kmin (n e) jj),
      restT E kmin (n e) (v e) (cc e) jj))
    (Wb := fun e jj => (n e + 1) + (0 + 2^(n e))) (Zb := fun e jj => 0 + (0 + Zs e jj))
    (Able.of_can (W := fun _ => 0) (Can.first.then_do hN)) hElem hNs
  refine (Able.save hcall hTab).mono (fun e => le_of_eq ?_) (fun e => le_of_eq ?_) <;> simp [NU0, N]


/-- **The leftover vectors** `λN, …, B-1`, each by OpenAI's own `hills_program`. -/
lemma leftover {Bd : Ξ → ℕ} {n Bv L : Ξ → ℕ} {v : ∀ e, ℕ → Bits (n e) → ℂ} (hL : ∀ e, L e ≤ Bv e)
    (hn : Knows m Bd s y n) (hB : Knows m Bd s y Bv) (hLK : Knows m Bd s y L)
    (hown : Has m Bd s (jobsT cl) y (fun e => jobsTape (n e) (Bv e) (v e)))
    (hI : Has m Bd s sc y (fun _ => Complex.I))
    (hbig : Small Bd (fun e => (Bv e + 1) * 2^(n e))) :
    Can m Bd s (jobsT cl) y
      (fun e => jobsTape (n e) (Bv e - L e) (fun t => ripple (n e) (v e (L e + t))))
      (fun e => (Bv e - L e) + (Bv e - L e) * ((n e + 1) * 2 ^ n e + 1)) := by
  have h2n : Small Bd (fun e => 2^(n e)) := hbig.mono (fun e => Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
  have hBs : Small Bd Bv := hbig.mono (fun e => by have : 1 ≤ 2^(n e) := Nat.one_le_two_pow; nlinarith)
  have hRs : Small Bd (fun e => Bv e - L e) := hBs.mono (fun e => Nat.sub_le _ _)
  have hRK : Knows m Bd s y (fun e => Bv e - L e) := hB.minus hLK hBs
  -- the sub-tape of the leftover jobs
  let Q := Σ e, Fin (Bv e - L e)
  let σ : Q → Ξ := Sigma.fst
  let yq (d : Q) : T (p s w) := (y d.1, (Layout.std (Bv d.1 - L d.1)).loc d.2)
  have hlt : ∀ d : Q, L d.1 + d.2.val < Bv d.1 := fun d => by have := d.2.2; have := hL d.1; omega
  have hadr : Knows m (fun d : Q => Bd d.1) (p s w) yq
      (fun d => (Layout.std (Bv d.1)).loc (⟨L d.1 + d.2.val, hlt d⟩ : Fin (Bv d.1))) :=
    ((Can.first.then_do (hLK.reindex σ)).plus Can.second ((hBs.mono hL).reindex σ)
      ((hRs.reindex σ).mono (fun d => d.2.2.le))).cong (fun _ => rfl) (fun d => rfl)
  have hfetch : Has m (fun d : Q => Bd d.1) (p s w) (a (c cl)) yq
      (fun d => (bits (n d.1)).tape (v d.1 (L d.1 + d.2.val))) :=
    Can.fetch (t := a (c cl)) (L := fun d : Q => Layout.std (Bv d.1))
      (v := fun d : Q => fun t : Fin (Bv d.1) => (bits (n d.1)).tape (v d.1 t))
      (i := fun d : Q => (⟨L d.1 + d.2.val, hlt d⟩ : Fin (Bv d.1)))
      (Can.first.then_do (hown.reindex σ)) hadr
  have hsub : Can m Bd s (jobsT cl) y (fun e => jobsTape (n e) (Bv e - L e) (fun t => v e (L e + t)))
      (fun e => Bv e - L e) := by
    have H := Can.layout (L := fun e => Layout.std (Bv e - L e)) (t := a (c cl)) (P := fun _ => 0)
      (v := fun e t => (bits (n e)).tape (v e (L e + t))) hRK (hfetch.mono (fun _ => Nat.zero_le _)) hRs
    refine H.mono (fun e => ?_)
    show 0 + (Bv e - L e) + (Bv e - L e) * 0 ≤ Bv e - L e
    simp
  -- every leftover job naively, keeping the environment
  let y' (e : Ξ) : T (p s (jobsT cl)) := (y e, jobsTape (n e) (Bv e - L e) (fun t => v e (L e + t)))
  have hnaive := MCost.naive_jobs (m := m) (cl := cl) (x := y') (Bd := Bd) n (fun e => Bv e - L e)
    (fun e t => v e (L e + t)) Can.second (Can.first.then_do hn) (Can.first.then_do hRK)
    (Can.first.then_do hI) hRs h2n
  exact Can.save hsub hnaive


/-- The tape of the copies' rest answers. -/
def copiesT (kmin n : ℕ) (v : ℕ → Bits n → ℂ) (lam : ℕ) : Tape (Tape (ℕ × Tape (Tape ℂ))) :=
  Tape.tab lam (fun c => Tape.tab (E.topN kmin n) (fun jj => (2^(E.topSz kmin n jj), restT E kmin n v c jj)))

lemma look_layout {β μ : Type*} (L : Layout β) (f : β → μ) (i : β) (j : ℕ) (hj : j = L.loc i) (z : μ) :
    (L.tape f).look j z = f i := by rw [hj, Layout.read]

lemma jobsTape_look (n N : ℕ) (J : ℕ → Bits n → ℂ) (q : ℕ) (hq : q < N) (r : ℕ) (hr : r < 2^n)
    (z : Tape ℂ) (z' : ℂ) : ((jobsTape n N J).look q z).look r z' = J q (bitsOf n r) := by
  unfold jobsTape
  rw [look_layout (Layout.std N) _ ⟨q, hq⟩ q rfl,
    look_layout (bits n) _ (bitsOf n r) r (by rw [bitsOf_loc, Nat.mod_eq_of_lt hr])]

/-- **The assembly**: every vector of the top job from its copy's rest answers (`fromHi`) or from the
leftover; work linear. -/
lemma assemble (kmin : ℕ) {Bd : Ξ → ℕ} {n Bv lam : Ξ → ℕ} {v : ∀ e, ℕ → Bits (n e) → ℂ}
    (hlN : ∀ e, lam e * E.topN kmin (n e) ≤ Bv e) (hlamB : ∀ e, lam e ≤ Bv e)
    (hNB : ∀ e, E.topN kmin (n e) ≤ Bv e)
    (hN : Knows m Bd s y (fun e => E.topN kmin (n e)))
    (hlam : Knows m Bd s y lam)
    (hcop : Has m Bd s (a (a (p w (jobsT cl)))) y (fun e => copiesT E kmin (n e) (v e) (lam e)))
    (hleft : Has m Bd s (jobsT cl) y
      (fun e => jobsTape (n e) (Bv e - lam e * E.topN kmin (n e))
        (fun t => ripple (n e) (v e (lam e * E.topN kmin (n e) + t)))))
    (hB : Knows m Bd s y Bv) (h2 : Knows m Bd s y (fun e => 2^(n e)))
    (hbig : Small Bd (fun e => (Bv e + 1) * 2^(n e))) :
    Can m Bd s (jobsT cl) y (fun e => jobsTape (n e) (Bv e) (fun t => ripple (n e) (v e t)))
      (fun e => Bv e + Bv e * 2^(n e)) := by
  let N (e : Ξ) := E.topN kmin (n e)
  have h2s : Small Bd (fun e => 2^(n e)) := hbig.mono (fun e => Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
  have hBs : Small Bd Bv := hbig.mono (fun e => by have : 1 ≤ 2^(n e) := Nat.one_le_two_pow; nlinarith)
  have hLs : Small Bd (fun e => lam e * N e) := hBs.mono hlN
  -- entries
  let Q1 := UnitF Bv
  let Q2 := Σ u : Q1, Bits (n u.1)
  let y2 (d : Q2) : T (p (p s w) w) := ((y d.1.1, d.1.2.val), (bits (n d.1.1)).loc d.2)
  let B2 (d : Q2) := Bd d.1.1
  let σ2 : Q2 → Ξ := fun d => d.1.1
  have F : ∀ {t : Ty} {z : Ξ → T t}, Has m Bd s t y z → Has m B2 (p (p s w) w) t y2 (fun d => z d.1.1) :=
    fun g => (Can.first.then_do Can.first).then_do (g.reindex σ2)
  have tK : Knows m B2 (p (p s w) w) y2 (fun d => d.1.2.val) := Can.first.then_do Can.second
  have pK : Knows m B2 (p (p s w) w) y2 (fun d => (bits (n d.1.1)).loc d.2) := Can.second
  have hts : Small B2 (fun d => d.1.2.val) := (hBs.reindex σ2).mono (fun d => d.1.2.2.le)
  have hploc : ∀ d : Q2, (bits (n d.1.1)).loc d.2 < 2^(n d.1.1) := fun d => by
    have := (bits (n d.1.1)).bd d.2; rwa [bits_len] at this
  have hps : Small B2 (fun d => (bits (n d.1.1)).loc d.2) := (h2s.reindex σ2).mono (fun d => (hploc d).le)
  have hLK : Knows m B2 (p (p s w) w) y2 (fun d => lam d.1.1 * N d.1.1) :=
    F (hlam.times hN (hBs.mono hlamB) (hBs.mono hNB))
  have tst : Knows m B2 (p (p s w) w) y2 (fun d => 1 - (if d.1.2.val < lam d.1.1 * N d.1.1 then 1 else 0)) :=
    (Can.wc 1).wsub (tK.wlt hLK) ((Small.const _ 1).mono (fun _ => Nat.sub_le _ _))
  have hval : Has m B2 (p (p s w) w) (c cl) y2 (fun d => ripple (n d.1.1) (v d.1.1 d.1.2.val) d.2) := by
    apply Can.testz tst
    · -- from the copy `t / N`, vector `t % N`
      let κ0 := {d : Q2 // 1 - (if d.1.2.val < lam d.1.1 * N d.1.1 then 1 else 0) = 0}
      have hlt : ∀ d : κ0, d.1.1.2.val < lam d.1.1.1 * N d.1.1.1 := by
        intro d; have := d.2; split_ifs at this with h1 <;> omega
      have hN0 : ∀ d : κ0, 0 < N d.1.1.1 := fun d => by
        rcases Nat.eq_zero_or_pos (N d.1.1.1) with h0 | h0
        · have := hlt d; rw [h0, mul_zero] at this; omega
        · exact h0
      let tt (d : κ0) := d.1.1.2.val
      let cpy (d : κ0) := tt d / N d.1.1.1
      let jj (d : κ0) := tt d % N d.1.1.1
      have hcl : ∀ d : κ0, cpy d < lam d.1.1.1 := fun d => (Nat.div_lt_iff_lt_mul (hN0 d)).2 (hlt d)
      have hjl : ∀ d : κ0, jj d < N d.1.1.1 := fun d => Nat.mod_lt _ (hN0 d)
      have hsz := fun d : κ0 => topSz_le E kmin (n d.1.1.1) (jj d)
      let B0 (d : κ0) := B2 d.1
      have G0 : ∀ {t : Ty} {z : Q2 → T t}, Has m B2 (p (p s w) w) t y2 z →
          Has m B0 (p (p s w) w) t (fun d => y2 d.1) (fun d => z d.1) := fun g => g.reindex Subtype.val
      have cK : Knows m B0 (p (p s w) w) (fun d => y2 d.1) cpy :=
        (G0 tK).dvdW (G0 (F hN)) (hts.reindex Subtype.val)
      have jK : Knows m B0 (p (p s w) w) (fun d => y2 d.1) jj :=
        (G0 tK).modW (G0 (F hN)) (hts.reindex Subtype.val)
      have hcopy := (G0 (F hcop)).look cK
      have hpair := hcopy.look jK
      have hpair' : Has m B0 (p (p s w) w) (p w (jobsT cl)) (fun d => y2 d.1)
          (fun d => (2^(E.topSz kmin (n d.1.1.1) (jj d)), restT E kmin (n d.1.1.1) (v d.1.1.1) (cpy d) (jj d))) := by
        refine hpair.cong (fun _ => rfl) (fun d => ?_)
        simp only [copiesT]
        rw [look_tab _ _ _ _ (hcl d), look_tab _ _ _ _ (hjl d)]
      have p2K : Knows m B0 (p (p s w) w) (fun d => y2 d.1) (fun d => 2^(E.topSz kmin (n d.1.1.1) (jj d))) :=
        hpair'.fst
      have p2s : Small B0 (fun d => 2^(E.topSz kmin (n d.1.1.1) (jj d))) :=
        ((h2s.reindex σ2).reindex Subtype.val).mono (fun d => Nat.pow_le_pow_right (by norm_num) (hsz d))
      have qK : Knows m B0 (p (p s w) w) (fun d => y2 d.1)
          (fun d => (bits (n d.1.1.1)).loc d.1.2 % 2^(E.topSz kmin (n d.1.1.1) (jj d))) :=
        (G0 pK).modW p2K (hps.reindex Subtype.val)
      have rK : Knows m B0 (p (p s w) w) (fun d => y2 d.1)
          (fun d => (bits (n d.1.1.1)).loc d.1.2 / 2^(E.topSz kmin (n d.1.1.1) (jj d))) :=
        (G0 pK).dvdW p2K (hps.reindex Subtype.val)
      have hjob := (hpair'.snd).look qK
      have hent := hjob.look rK
      refine hent.cong (fun _ => rfl) (fun d => ?_)
      -- evaluate the two looks
      have hq : (bits (n d.1.1.1)).loc d.1.2 % 2^(E.topSz kmin (n d.1.1.1) (jj d)) <
          2^(E.topSz kmin (n d.1.1.1) (jj d)) := Nat.mod_lt _ (Nat.two_pow_pos _)
      have hr : (bits (n d.1.1.1)).loc d.1.2 / 2^(E.topSz kmin (n d.1.1.1) (jj d)) <
          2^(n d.1.1.1 - E.topSz kmin (n d.1.1.1) (jj d)) := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add, Nat.sub_add_cancel (hsz d)]
        exact hploc d.1
      show ((restT E kmin (n d.1.1.1) (v d.1.1.1) (cpy d) (jj d)).look
          ((bits (n d.1.1.1)).loc d.1.2 % 2^(E.topSz kmin (n d.1.1.1) (jj d))) (a (c cl)).blank).look
          ((bits (n d.1.1.1)).loc d.1.2 / 2^(E.topSz kmin (n d.1.1.1) (jj d))) (c cl).blank = _
      unfold restT
      rw [jobsTape_look _ _ _ _ hq _ hr]
      have key := congrFun (fromHi_ripple (n d.1.1.1) (E.topSz kmin (n d.1.1.1) (jj d)) (hsz d)
        (v d.1.1.1 (cpy d * N d.1.1.1 + jj d))) d.1.2
      have htt : cpy d * N d.1.1.1 + jj d = d.1.1.2.val := by
        simp only [cpy, jj, tt]; rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
      rw [htt] at key
      have htt' : cpy d * E.topN kmin (n d.1.1.1) + jj d = d.1.1.2.val := htt
      unfold Eng.topAns
      rw [htt', ← key]
      rfl
    · -- from the leftover
      let κ1 := {d : Q2 // 1 - (if d.1.2.val < lam d.1.1 * N d.1.1 then 1 else 0) ≠ 0}
      have hge : ∀ d : κ1, lam d.1.1.1 * N d.1.1.1 ≤ d.1.1.2.val := by
        intro d; have := d.2; split_ifs at this with h1 <;> omega
      have iK : Knows m (fun d : κ1 => B2 d.1) (p (p s w) w) (fun d => y2 d.1)
          (fun d => d.1.1.2.val - lam d.1.1.1 * N d.1.1.1) :=
        (tK.reindex Subtype.val).minus (hLK.reindex Subtype.val) (hts.reindex Subtype.val)
      have hjob := ((F hleft).reindex Subtype.val).look iK
      have hent := hjob.look (pK.reindex Subtype.val)
      refine hent.cong (fun _ => rfl) (fun d => ?_)
      have hlt : d.1.1.2.val - lam d.1.1.1 * N d.1.1.1 < Bv d.1.1.1 - lam d.1.1.1 * N d.1.1.1 := by
        have := d.1.1.2.2; have := hge d; omega
      rw [jobsTape_look _ _ _ _ hlt _ (hploc d.1), bitsOf_of_loc]
      have e1 : lam d.1.1.1 * N d.1.1.1 + (d.1.1.2.val - lam d.1.1.1 * N d.1.1.1) = d.1.1.2.val := by
        have := hge d; omega
      simp only [N] at e1 ⊢
      rw [e1]
  -- the two layouts
  have hlen : Knows m (fun u : Q1 => Bd u.1) (p s w) (fun u => (y u.1, u.2.val)) (fun u => (bits (n u.1)).n) :=
    Can.first.then_do (h2.reindex (fun u : Q1 => u.1))
  have HI := Can.layout (t := c cl) (L := fun u : Q1 => bits (n u.1))
    (v := fun u e => ripple (n u.1) (v u.1 u.2.val) e) (P := fun _ => 0) (W := fun _ => 0) hlen
    (hval.mono (fun _ => Nat.zero_le _)) (h2s.reindex _)
  have HO := Can.layout (t := a (c cl)) (L := fun e => Layout.std (Bv e))
    (v := fun e t => (bits (n e)).tape (ripple (n e) (v e t))) (P := fun e => 2^(n e)) (W := fun _ => 0)
    hB (HI.mono (fun u => by simp)) hBs
  refine HO.mono (fun e => ?_)
  show 0 + Bv e + Bv e * 2^(n e) ≤ Bv e + Bv e * 2^(n e)
  simp


lemma sizes_zero : (Layout.std 0).tape (fun _ : Fin 0 => (0 : ℕ)) = Tape.tab 0 (fun _ => 0) := by
  refine Tape.ext_look rfl 0 (fun i hi => ?_)
  exact absurd hi (Nat.not_lt_zero _)

lemma tree_arith (lam S r B X n : ℕ) (hS : S ≤ B * (5 * X)) (hlB : lam ≤ B) (hm : r ≤ B) (hX : 1 ≤ X)
    (hB2 : B ≤ B * X) :
    0 + lam + S + ((r + r * ((n + 1) * X + 1)) + (B + B * X)) + 1 ≤ 12 * ((B + 1) * X + r * (n + 1) * X + 1) := by
  have e1 : r * ((n + 1) * X + 1) = r * (n + 1) * X + r := by ring
  have hS' : S ≤ 5 * (B * X) := by rw [show 5 * (B * X) = B * (5 * X) by ring]; exact hS
  have e2 : 12 * ((B + 1) * X + r * (n + 1) * X + 1) = 12 * (B * X) + 12 * X + 12 * (r * (n + 1) * X) + 12 := by ring
  rw [e1, e2]
  omega

/-- **The tree branch of a top job** (`n0 ≤ n`, at least one copy): the copies, the leftover, the
assembly.  Work `O((B+1) 2^n + (B % N)(n+1) 2^n)`, charge the root and rest calls. -/
lemma tree_branch (kmin : ℕ) {n Bv lam : Ξ → ℕ} {v : ∀ e, ℕ → Bits (n e) → ℂ}
    (hlamd : ∀ e, lam e = Bv e / E.topN kmin (n e))
    (hNB : ∀ e, E.topN kmin (n e) ≤ Bv e)
    (hn : Knows m b.B s y n) (hB : Knows m b.B s y Bv)
    (hG : Knows m b.B s y (fun e => E.topG kmin (n e)))
    (hNU : Knows m b.B s y (fun e => E.topNU0 kmin (n e)))
    (hN : Knows m b.B s y (fun e => E.topN kmin (n e)))
    (hlam : Knows m b.B s y lam) (h2 : Knows m b.B s y (fun e => 2^(n e)))
    (hown : Has m b.B s (jobsT cl) y (fun e => jobsTape (n e) (Bv e) (v e)))
    (hcU : Has m b.B s (a w) y
      (fun e => (Layout.std (E.topNU0 kmin (n e))).tape (fun p => E.cUc (n e) (E.topG kmin (n e)) 1 p)))
    (hI : Has m b.B s sc y (fun _ => Complex.I))
    (hemp : Has m b.B s (jobsT cl) y (fun e => jobsTape 0 0 (fun _ _ => 0)))
    (hbig : Small b.B (fun e => (Bv e + 1) * 2^(n e)))
    {tau : Ξ → MDesc → ℕ}
    (hroot : ∀ e t, t < lam e → (b.use e (E.enc cl (E.topRoot kmin (n e) (Bv e) (v e) t))).OK
      (E.out cl (E.topRoot kmin (n e) (Bv e) (v e) t)) (tau e (E.topRoot kmin (n e) (Bv e) (v e) t)) (b.ext e))
    (hrest : ∀ e t jj, t < lam e → jj < E.topN kmin (n e) →
      (b.use e (E.enc cl (E.topRest kmin (n e) (v e) t jj))).OK
        (E.out cl (E.topRest kmin (n e) (v e) t jj)) (tau e (E.topRest kmin (n e) (v e) t jj)) (b.ext e)) :
    Able m b s (portOut cl) y (fun e => E.out cl (MDesc.top (n e) (Bv e) (v e)))
      (fun e => (Bv e + 1) * 2^(n e) + (Bv e % E.topN kmin (n e)) * (n e + 1) * 2^(n e))
      (fun e => ∑ t ∈ Finset.range (lam e), (tau e (E.topRoot kmin (n e) (Bv e) (v e) t) +
        ∑ jj ∈ Finset.range (E.topN kmin (n e)), tau e (E.topRest kmin (n e) (v e) t jj))) := by
  let N (e : Ξ) := E.topN kmin (n e)
  have hBs : Small b.B Bv := hbig.mono (fun e => by have : 1 ≤ 2^(n e) := Nat.one_le_two_pow; nlinarith)
  have h2s : Small b.B (fun e => 2^(n e)) := hbig.mono (fun e => Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
  have hlN : ∀ e, lam e * N e ≤ Bv e := fun e => by rw [hlamd e]; exact Nat.div_mul_le_self _ _
  have hlamB : ∀ e, lam e ≤ Bv e := fun e => by rw [hlamd e]; exact Nat.div_le_self _ _
  have hlams : Small b.B lam := hBs.mono hlamB
  have hNs : Small b.B N := hBs.mono hNB
  have hfit : ∀ e c, c < lam e → (c + 1) * N e ≤ Bv e := fun e c hc => by
    have h1 : c + 1 ≤ Bv e / N e := by rw [← hlamd e]; omega
    exact le_trans (Nat.mul_le_mul_right _ h1) (Nat.div_mul_le_self _ _)
  -- (1) the copies
  let Dd := During lam
  let σd : Dd → Ξ := During.i
  let y1 (d : Dd) : T (p s w) := (y d.i, d.j)
  have F : ∀ {t : Ty} {z : Ξ → T t}, Has m b.B s t y z → Has m (fun d : Dd => b.B d.i) (p s w) t y1 (fun d => z d.i) :=
    fun g => Can.first.then_do (g.reindex σd)
  have hElem := copy_elem E (b := b.comap σd) (y := y1) kmin (n := fun d => n d.i) (Bv := fun d => Bv d.i)
    (cc := fun d => d.j) (v := fun d => v d.i) (fun d => hfit d.i d.j d.hj)
    (fun d => le_trans d.hj.le (hlamB d.i)) (F hn) Can.second (F hG) (F hNU) (F hN) (F hown) (F hcU)
    (F hI) (F hemp) (hbig.reindex σd) (Zr := fun d => tau d.i (E.topRoot kmin (n d.i) (Bv d.i) (v d.i) d.j))
    (Zs := fun d jj => tau d.i (E.topRest kmin (n d.i) (v d.i) d.j jj))
    (fun d => hroot d.i d.j d.hj) (fun d jj hjj => hrest d.i d.j jj d.hj hjj)
  have hCop := Able.tab (b := b) (s := s) (t := a (p w (jobsT cl))) (x := y) (n := lam)
    (v := fun e c => Tape.tab (N e) (fun jj => (2^(E.topSz kmin (n e) jj), restT E kmin (n e) (v e) c jj)))
    (Wb := fun e c => E.topNU0 kmin (n e) * E.W + 0 + (0 + (0 + E.topN kmin (n e) +
        ∑ jj ∈ Finset.range (E.topN kmin (n e)), ((n e + 1) + (0 + 2^(n e))))))
    (Zb := fun e c => 0 + tau e (E.topRoot kmin (n e) (Bv e) (v e) c) +
        (0 + ∑ jj ∈ Finset.range (E.topN kmin (n e)), (0 + (0 + tau e (E.topRest kmin (n e) (v e) c jj)))))
    (Able.of_can (W := fun _ => 0) hlam) hElem hlams
  -- (2) leftover and (3) assembly, keeping the copies
  let y2 (e : Ξ) : T (p s (a (a (p w (jobsT cl))))) := (y e, copiesT E kmin (n e) (v e) (lam e))
  have F2 : ∀ {t : Ty} {z : Ξ → T t}, Has m b.B s t y z → Has m b.B (p s (a (a (p w (jobsT cl))))) t y2 z :=
    fun g => Can.first.then_do g
  have hLK : Knows m b.B (p s (a (a (p w (jobsT cl))))) y2 (fun e => lam e * N e) :=
    F2 (hlam.times hN hlams hNs)
  have hLeft := leftover (cl := cl) (Bd := b.B) (y := y2) (n := n) (Bv := Bv) (L := fun e => lam e * N e)
    (v := v) hlN (F2 hn) (F2 hB) hLK (F2 hown) (F2 hI) hbig
  let y3 (e : Ξ) : T (p (p s (a (a (p w (jobsT cl))))) (jobsT cl)) :=
    (y2 e, jobsTape (n e) (Bv e - lam e * N e) (fun t => ripple (n e) (v e (lam e * N e + t))))
  have F3 : ∀ {t : Ty} {z : Ξ → T t}, Has m b.B s t y z → Has m b.B (p (p s (a (a (p w (jobsT cl))))) (jobsT cl)) t y3 z :=
    fun g => Can.first.then_do (F2 g)
  have hAsm := assemble E (cl := cl) (Bd := b.B) (y := y3) kmin (n := n) (Bv := Bv) (lam := lam) (v := v)
    hlN hlamB hNB (F3 hN) (F3 hlam) (Can.first.then_do Can.second) Can.second (F3 hB) (F3 h2) hbig
  have hMain := Can.save hLeft hAsm
  -- the empty second and third components
  have hEmp2 : Has m b.B (p s (a (a (p w (jobsT cl))))) (jobsT cl) y2 (fun e => jobsTape (n e) 0 (fun _ _ => 0)) :=
    (F2 hemp).cong (fun _ => rfl) (fun e => jobsTape_zero 0 (n e) _ _)
  have hEmp3 : Has m b.B (p s (a (a (p w (jobsT cl))))) (a w) y2
      (fun e => (Layout.std 0).tape (fun _ : Fin 0 => (0 : ℕ))) := by
    have H := Can.tab (m := m) (B := b.B) (s := p s (a (a (p w (jobsT cl))))) (x := y2)
      (t := w) (n := fun _ => 0) (uB := fun _ _ => 0) (v := fun _ _ => 0) (W := fun _ => 0)
      (Can.wc (W := fun _ => 0) 0) (Can.wc 0) (Small.const _ 0)
    refine (H.cong (fun _ => rfl) (fun e => sizes_zero.symm)).mono (fun e => by simp)
  have hOut : Can m b.B (p s (a (a (p w (jobsT cl))))) (portOut cl) y2
      (fun e => E.out cl (MDesc.top (n e) (Bv e) (v e)))
      (fun e => (Bv e - lam e * N e + (Bv e - lam e * N e) * ((n e + 1) * 2 ^ n e + 1)) + (Bv e + Bv e * 2^(n e))) :=
    (hMain.pair ((hEmp2.mono (fun _ => Nat.zero_le _)).pair (hEmp3.mono (fun _ => Nat.zero_le _)))).cong
      (fun _ => rfl) (fun e => rfl)
  have H := Able.save hCop (Able.of_can (b := b) hOut)
  refine (H.weaken ⟨12, fun e => ?_⟩ (fun e => le_of_eq ?_))
  · -- the work
    have hr : Bv e - lam e * N e = Bv e % N e := by
      have h1 := Nat.div_add_mod (Bv e) (N e)
      have h2 : lam e * N e = N e * (Bv e / N e) := by rw [hlamd e, Nat.mul_comm]
      omega
    have hsum : ∑ c ∈ Finset.range (lam e), (E.topNU0 kmin (n e) * E.W + 0 + (0 + (0 + E.topN kmin (n e) +
        ∑ jj ∈ Finset.range (E.topN kmin (n e)), ((n e + 1) + (0 + 2^(n e)))))) ≤ Bv e * (5 * 2^(n e)) := by
      have hNU : E.topNU0 kmin (n e) * E.W ≤ E.topN kmin (n e) := Nat.le_add_right _ _
      rw [Finset.sum_const, Finset.card_range, smul_eq_mul, Finset.sum_const, Finset.card_range, smul_eq_mul]
      have h4 : n e + 3 ≤ 4 * 2^(n e) := by
        have := (Nat.lt_two_pow_self : n e < 2^(n e)); have : 1 ≤ 2^(n e) := Nat.one_le_two_pow; omega
      have hin : E.topNU0 kmin (n e) * E.W + 0 + (0 + (0 + E.topN kmin (n e) +
          E.topN kmin (n e) * ((n e + 1) + (0 + 2^(n e))))) ≤ E.topN kmin (n e) * (5 * 2^(n e)) := by
        nlinarith
      calc lam e * (E.topNU0 kmin (n e) * E.W + 0 + (0 + (0 + E.topN kmin (n e) +
            E.topN kmin (n e) * ((n e + 1) + (0 + 2^(n e))))))
          ≤ lam e * (E.topN kmin (n e) * (5 * 2^(n e))) := Nat.mul_le_mul_left _ hin
        _ = (lam e * E.topN kmin (n e)) * (5 * 2^(n e)) := by ring
        _ ≤ Bv e * (5 * 2^(n e)) := Nat.mul_le_mul_right _ (hlN e)
    show 0 + lam e + ∑ c ∈ Finset.range (lam e), (E.topNU0 kmin (n e) * E.W + 0 + (0 + (0 + E.topN kmin (n e) +
        ∑ jj ∈ Finset.range (E.topN kmin (n e)), ((n e + 1) + (0 + 2^(n e)))))) +
        ((Bv e - lam e * N e + (Bv e - lam e * N e) * ((n e + 1) * 2 ^ n e + 1)) + (Bv e + Bv e * 2^(n e))) + 1 ≤
      12 * ((Bv e + 1) * 2^(n e) + Bv e % E.topN kmin (n e) * (n e + 1) * 2^(n e) + 1)
    rw [hr]
    have hm : Bv e % N e ≤ Bv e := Nat.mod_le _ _
    have hlB := hlamB e
    have hX : 1 ≤ 2^(n e) := Nat.one_le_two_pow
    have hB2 : Bv e ≤ Bv e * 2^(n e) := Nat.le_mul_of_pos_right _ hX
    have hr2 : Bv e % N e * ((n e + 1) * 2 ^ n e + 1) = Bv e % N e * (n e + 1) * 2^(n e) + Bv e % N e := by ring
    have hN' : N e = E.topN kmin (n e) := rfl
    exact tree_arith _ _ _ _ _ _ hsum hlB hm hX hB2
  · -- the charge
    simp only [zero_add, add_zero]


/-- **The root height** `topG kmin n` by one loop over `g ≤ n` (`findGreatest`), work `O(n^2)`. -/
lemma can_topG (kmin : ℕ) (hk : 2 ≤ kmin) {Bd n : Ξ → ℕ} (hn : Knows m Bd s y n)
    (hpow : Small Bd (fun e => kmin^(n e + 1))) (hns : Small Bd n) :
    Can m Bd s w y (fun e => E.topG kmin (n e)) (fun e => n e * (n e + 3) + 1) := by
  let P (e : Ξ) (g : ℕ) : Prop := E.mx * kmin ^ g ≤ n e
  let vG (e : Ξ) (j : ℕ) : ℕ := Nat.findGreatest (P e) j
  let BD (d : During n) := Bd d.i
  have hk0 : 0 < kmin := by omega
  have hs : Can m BD (p s (p w w)) w (fun d => (y d.i, d.j, vG d.i d.j)) (fun d => vG d.i (d.j + 1))
      (fun d => n d.i + 2) := by
    have nK : Knows m BD (p s (p w w)) (fun d => (y d.i, d.j, vG d.i d.j)) (fun d => n d.i) :=
      Can.first.then_do (hn.reindex (fun d : During n => d.i))
    have jK : Knows m BD (p s (p w w)) (fun d => (y d.i, d.j, vG d.i d.j)) (fun d => d.j) := Can.fst Can.second
    have aK : Knows m BD (p s (p w w)) (fun d => (y d.i, d.j, vG d.i d.j)) (fun d => vG d.i d.j) :=
      Can.snd Can.second
    have js : Small BD (fun d => d.j) := (hns.reindex (fun d : During n => d.i)).mono (fun d => d.hj.le)
    have j1K : Knows m BD (p s (p w w)) (fun d => (y d.i, d.j, vG d.i d.j)) (fun d => d.j + 1) :=
      jK.plus (Can.wc 1) js (Small.const _ 1)
    have hps : Small BD (fun d => kmin^(d.j + 1)) :=
      (hpow.reindex (fun d : During n => d.i)).mono (fun d => Nat.pow_le_pow_right hk0 (by have := d.hj; omega))
    have pw := can_powv kmin hk0 j1K (js.add (Small.const _ 1)) hps
    have hmx : Can m BD (p s (p w w)) w (fun d => (y d.i, d.j, vG d.i d.j)) (fun d => E.mx * kmin^(d.j + 1))
        (fun d => d.j + 1 + 1) := (Can.wc E.mx).times pw (Small.const _ _) hps
    have tK : Can m BD (p s (p w w)) w (fun d => (y d.i, d.j, vG d.i d.j))
        (fun d => 1 - (if n d.i < E.mx * kmin^(d.j + 1) then 1 else 0)) (fun d => d.j + 1 + 1) :=
      (Can.wc 1).wsub ((nK.mono (fun _ => Nat.zero_le _)).wlt hmx) ((Small.const _ 1).mono (fun _ => Nat.sub_le _ _))
    have hsel : Can m BD (p s (p w w)) w (fun d => (y d.i, d.j, vG d.i d.j))
        (fun d => (1 - (if n d.i < E.mx * kmin^(d.j + 1) then 1 else 0)) * (d.j + 1) +
          (if n d.i < E.mx * kmin^(d.j + 1) then 1 else 0) * vG d.i d.j) (fun d => d.j + 1 + 1) := by
      have t2 : Can m BD (p s (p w w)) w (fun d => (y d.i, d.j, vG d.i d.j))
          (fun d => if n d.i < E.mx * kmin^(d.j + 1) then 1 else 0) (fun d => d.j + 1 + 1) :=
        (nK.mono (fun _ => Nat.zero_le _)).wlt hmx
      have vs : Small BD (fun d => vG d.i d.j) := js.mono (fun d => Nat.findGreatest_le _)
      exact (tK.times (j1K.mono (fun _ => Nat.zero_le _)) ((Small.const _ 1).mono (fun _ => Nat.sub_le _ _))
        (js.add (Small.const _ 1))).plus (t2.times (aK.mono (fun _ => Nat.zero_le _))
          ((Small.const _ 1).mono (fun d => by split <;> omega)) vs)
        (((Small.const _ 1).mono (fun _ => Nat.sub_le _ _)).mul (js.add (Small.const _ 1)))
        (((Small.const _ 1).mono (fun d => by split <;> omega)).mul vs)
    refine (hsel.cong (fun _ => rfl) (fun d => ?_)).mono (fun d => by have := d.hj; omega)
    show _ = Nat.findGreatest (P d.i) (d.j + 1)
    rw [Nat.findGreatest_succ]
    by_cases hp : E.mx * kmin ^ (d.j + 1) ≤ n d.i
    · simp [hp, Nat.not_lt.mpr hp, P]
    · simp [hp, Nat.lt_of_not_le hp, P]
      rfl
  have H := Can.loop (t := w) (v := vG) (W' := fun _ => 0) (uB := fun e _ => n e + 2) hn
    ((Can.wc (W := fun _ => 0) 0).cong (fun _ => rfl) (fun e => by simp [vG])) hs hns
  refine (H.cong (fun _ => rfl) (fun e => rfl)).mono (fun e => ?_)
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
  change 0 + 0 + n e + n e * (n e + 2) ≤ n e * (n e + 3) + 1
  nlinarith

end Elems

end
end PowerSaving.RAM
end OAI

#print axioms OAI.PowerSaving.RAM.rest_elem
#print axioms OAI.PowerSaving.RAM.copy_elem
#print axioms OAI.PowerSaving.RAM.leftover
#print axioms OAI.PowerSaving.RAM.assemble
#print axioms OAI.PowerSaving.RAM.tree_branch
#print axioms OAI.PowerSaving.RAM.can_topG
