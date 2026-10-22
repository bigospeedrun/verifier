import Submission.Work.XHostT.HF.GeomInst
import Submission.Work.XHostT.TTab
import Submission.Work.XHostT.HF.Count2979C

/-!
# (key: heads-first #2979) The head-first stage of the #2979 network: head bins = heads, from the table

p-hfirst's heads-first certificate (`xnetGeom_heads_first_auto`, Work/XHostT/HF/GeomInst.lean) takes the canonical
head set `headBins S` (A4 bins with remaining climb 48 that no slot is hosted in).  For the #2979 instance
(74 replicas, 112 classes, two sides) this file reduces everything the bridge needs about it to data facts of the
kernel host table (p-a3's format, `schedOfTabOK`):
* `I2979.card_rem_eq`: the number of window-`c` bins with remainder `v` of ANY schedule whose remainders are read
  from a remainder tree `rt` (p-a3's `schedOfTabOK_hrem`, `rfl`) is the computable count `cntKind rt v c nR`;
* `I2979.headBins_card`: with positive residuals (`hpos`), the head bins are counted by `cntKind rt 48 4 nR`;
* `I2979.resK_pos`: positive residuals from the table (every call's provider index below 2, both providers' residuals
  positive);
* `I2979.hLlen`, `I2979.card_live2979`: the head-role count `card Γ * H0` and the live-role count
  `card Γ * 66304` (74 replicas x 896), the two count hypotheses of p-bridge's engine theorem.
Written by x-inst (wht45/lever2979, 19 Oct 2026) on p-hfirst's and p-a3's files; prepared with assistance from Claude.
No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace OAI
namespace PowerSaving
namespace XHostT
namespace I2979
open Finset XHost

lemma cntF_sum (x v : ℕ) : ∀ m, cntF x v m = ∑ b ∈ range m, (if fld x b = v then 1 else 0)
  | 0 => rfl
  | m + 1 => by
    rw [cntF, cntF_sum x v m, Finset.sum_range_succ]
    congr 1
    by_cases h : fld x m = v
    · rw [ite_eq_left_iff.mpr (fun h' => absurd h h')]; simp [h]
    · rw [ite_eq_right_iff.mpr (fun h' => absurd h' h)]
      have : Nat.beq (fld x m) v = false := by
        cases hb : Nat.beq (fld x m) v
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true hb) h
      rw [this]; rfl

lemma cntKind_sum (rt : K.CT) (v c : ℕ) : ∀ n,
    cntKind rt v c n = ∑ ρ ∈ range n, cntF (rt.get (9 * ρ + c)).1 v 224
  | 0 => rfl
  | n + 1 => by rw [cntKind, cntKind_sum rt v c n, Finset.sum_range_succ]

/-- the remainder of bin `b < 224` of host kind `κ` is field `b` of leaf `κ`. -/
lemma remAt_bin (rt : K.CT) (κ b : ℕ) (hb : b < 224) : K.remAt rt (224 * κ + b) = fld (rt.get κ).1 b := by
  have e1 : (224 * κ + b) / 224 = κ := by omega
  have e2 : (224 * κ + b) % 224 = b := by omega
  simp only [K.remAt, fld, e1, e2]

/-- **the count of window-`c` bins with remainder `v`**, for any schedule whose remainders are read from `rt`
(p-a3's encoding of host `(ρh, c, (s, t))` as `2016 ρh + 224 c + 112 s + t`). -/
theorem card_rem_eq {nR : ℕ} {Sl : Type} (S : HostSchedT nR Sl (Fin 112)) (rt : K.CT)
    (hrem : ∀ ρh c j, S.hrem ρh c j
      = K.remAt rt (2016 * ρh.val + 224 * c.val + (if j.1 then 112 else 0) + j.2.val))
    (c : Fin 9) (v : ℕ) :
    (Finset.univ.filter (fun p : Fin nR × Bool × Fin 112 => S.hrem p.1 c p.2 = v)).card = cntKind rt v c.val nR := by
  rw [Finset.card_filter, cntKind_sum, Fintype.sum_prod_type, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl (fun ρ _ => ?_)
  rw [Fintype.sum_prod_type, Fintype.sum_bool, cntF_sum]
  have hT : ∀ t : Fin 112, S.hrem ρ c (true, t) = fld (rt.get (9 * ρ.val + c.val)).1 (112 + t.val) := by
    intro t
    have ht := t.isLt
    rw [hrem, ← remAt_bin rt _ _ (by omega : 112 + t.val < 224)]
    congr 1
    show 2016 * ρ.val + 224 * c.val + (if true = true then 112 else 0) + t.val = 224 * (9 * ρ.val + c.val) + (112 + t.val)
    rw [if_pos rfl]
    omega
  have hF : ∀ t : Fin 112, S.hrem ρ c (false, t) = fld (rt.get (9 * ρ.val + c.val)).1 t.val := by
    intro t
    have ht := t.isLt
    rw [hrem, ← remAt_bin rt _ _ (by omega : t.val < 224)]
    congr 1
    show 2016 * ρ.val + 224 * c.val + (if false = true then 112 else 0) + t.val = 224 * (9 * ρ.val + c.val) + t.val
    rw [if_neg (by decide)]
    omega
  simp only [hT, hF]
  rw [show (224 : ℕ) = 112 + 112 from rfl, Finset.sum_range_add,
    Fin.sum_univ_eq_sum_range (fun t => if fld (rt.get (9 * ρ.val + c.val)).1 (112 + t) = v then 1 else 0) 112,
    Fin.sum_univ_eq_sum_range (fun t => if fld (rt.get (9 * ρ.val + c.val)).1 t = v then 1 else 0) 112]
  ring

/-- with positive residuals, the canonical head bins of a schedule read from `rt` are counted by
`cntKind rt 48 4 nR` (the A4 bins with remainder 48). -/
theorem headBins_card {nR : ℕ} {Sl : Type} [Fintype Sl] [DecidableEq Sl] (S : HostSchedT nR Sl (Fin 112))
    (res : Fin nR → Fin 9 → Sl → ℕ) (hfit : S.fits res) (hpos : ∀ ρ l q, 0 < res ρ l q) (rt : K.CT)
    (hrem : ∀ ρh c j, S.hrem ρh c j
      = K.remAt rt (2016 * ρh.val + 224 * c.val + (if j.1 then 112 else 0) + j.2.val))
    {H0 : ℕ} (hc : cntKind rt 48 4 nR = H0) : (headBins S).card = H0 := by
  rw [headBins_eq S res hfit hpos, card_rem_eq S rt hrem 4 48]
  exact hc

/-- the head-role count of p-bridge's engine theorem: `card Γ` gauge copies of every head bin. -/
theorem hLlen {nR : ℕ} {Sl : Type} [Fintype Sl] [DecidableEq Sl] {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (S : HostSchedT nR Sl (Fin 112))
    (res : Fin nR → Fin 9 → Sl → ℕ) (hfit : S.fits res) (hpos : ∀ ρ l q, 0 < res ρ l q) (rt : K.CT)
    (hrem : ∀ ρh c j, S.hrem ρh c j
      = K.remAt rt (2016 * ρh.val + 224 * c.val + (if j.1 then 112 else 0) + j.2.val))
    {H0 : ℕ} (hc : cntKind rt 48 4 nR = H0) :
    (headsL (Γ := Γ) (nb := 0) (headBins S)).length = Fintype.card Γ * H0 := by
  rw [headsL_length, headBins_card S res hfit hpos rt hrem hc, Nat.mul_comm]

/-- the head-role count from the head count in Finset form (x-tables' `sched2979_heads`). -/
theorem hLlen_card {nR : ℕ} {Sl : Type} [Fintype Sl] [DecidableEq Sl] {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (S : HostSchedT nR Sl (Fin 112))
    (res : Fin nR → Fin 9 → Sl → ℕ) (hfit : S.fits res) (hpos : ∀ ρ l q, 0 < res ρ l q)
    {H0 : ℕ} (hc : (Finset.univ.filter (fun p : Fin nR × Bool × Fin 112 => S.hrem p.1 4 p.2 = 48)).card = H0) :
    (headsL (Γ := Γ) (nb := 0) (headBins S)).length = Fintype.card Γ * H0 := by
  rw [headsL_length, headBins_eq S res hfit hpos, hc, Nat.mul_comm]

/-- the live roles of the #2979 network: 74 replicas x 896 per gauge copy. -/
lemma card_live2979 (Γ : Type) [Fintype Γ] :
    Fintype.card (BLiveT Γ (Fin 112) 0 74) = Fintype.card Γ * 66304 := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  ring

/-- positive residuals from the table: every call's provider index is 0 or 1 and both providers' residuals are
positive (two `decide +kernel` facts on the data). -/
theorem resK_pos (ct : K.CT) (resT nR R : ℕ) (hp : ∀ k < 9 * nR, (ct.get k).2.2 < 2)
    (hq : ∀ p < 2, ∀ q < R, 0 < K.resAt resT p q) : ∀ ρ l (q : Fin R), 0 < resK ct resT nR R ρ l q := by
  intro ρ l q
  unfold resK
  have h1 := ρ.isLt; have h2 := l.isLt
  exact hq _ (hp _ (by omega)) _ q.isLt

/-- p-a3's checked-table schedule reads its remainders from `rt` (`schedOfTabOK_hrem`, by `rfl`). -/
theorem hrem_schedOfTabOK (ct rt : K.CT) (resT nR R : ℕ) (hnR : 0 < nR) (hT : TabOK ct rt resT nR R)
    (hord : K.chkOrder ct (9 * nR) (9 * nR) 0 0 = true) :
    ∀ ρh c j, (schedOfTabOK ct rt resT nR R hnR hT hord).hrem ρh c j
      = K.remAt rt (2016 * ρh.val + 224 * c.val + (if j.1 then 112 else 0) + j.2.val) :=
  fun ρh c j => schedOfTabOK_hrem ct rt resT nR R hnR hT hord ρh c j

end I2979
end XHostT
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.XHostT.I2979.card_rem_eq
#print axioms OAI.PowerSaving.XHostT.I2979.headBins_card
#print axioms OAI.PowerSaving.XHostT.I2979.hLlen
#print axioms OAI.PowerSaving.XHostT.I2979.hLlen_card
#print axioms OAI.PowerSaving.XHostT.I2979.card_live2979
#print axioms OAI.PowerSaving.XHostT.I2979.resK_pos
#print axioms OAI.PowerSaving.XHostT.I2979.hrem_schedOfTabOK
