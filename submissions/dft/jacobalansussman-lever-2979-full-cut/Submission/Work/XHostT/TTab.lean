import Submission.Work.XHostT.TSchedK
import Submission.Work.XHostT.TGeom

/-!
# (key: bridge-host-cross) A kernel-checked host table as a cross-replica host schedule

From the data of Work/XHostT/KCheck.lean (call tree `ct`, remainder tree `rt`, residual table `resT`) and three kernel
facts, the order check `chkOrder`, one `chkPieceCount` theorem per host kind (`hK`) and the record counts summing to
`9 nR * R` (`hsum`), `schedOfTab` is a `HostSchedT nR (Fin R) (Fin 112)`: times `tm ρ l = (ct.get (9 ρ + l)).2.1`,
hosts decoded from `h = 2016 ρh + 224 c + 112 s + t`, remainders from `rt`; `schedOfTab_fits`: it fits the residuals
`resK ct resT ρ l q = resAt resT (ct.get (9 ρ + l)).2.2 q` of the call's provider word.  With `resIc Ic = resK ct resT`
(the provider words' entrance labels against the table's residuals) this is the hypothesis of `bridgeHostT_gcert`.
Written by p-a3 (wht45/lever, 19 Oct 2026); prepared with assistance from Claude.  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace OAI
namespace PowerSaving
namespace XHostT
open Finset XHost
noncomputable section

namespace K

/-! ## The order check -/

lemma bit_and_one (m n : ℕ) : ((m >>> n) &&& 1 = 0) ↔ m.testBit n = false := by
  unfold Nat.testBit
  rw [Nat.land_comm]
  simp

lemma bit_or_ne {s t u : ℕ} (h : ((s ||| (1 <<< t)) >>> u) &&& 1 = 0) : u ≠ t ∧ ((s >>> u) &&& 1 = 0) := by
  rw [bit_and_one, Nat.testBit_lor, Bool.or_eq_false_iff] at h
  refine ⟨fun e => ?_, (bit_and_one s u).mpr h.1⟩
  subst e
  have h2 := h.2
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow_self] at h2
  exact absurd h2 (by decide)

/-- what `chkOrder` checks. -/
lemma chkOrder_sound (ct : CT) (NC : ℕ) : ∀ (n k seen : ℕ), chkOrder ct NC n k seen = true →
    (∀ k', k ≤ k' → k' < k + n → (ct.get k').2.1 < NC ∧ (k' % 9 = 8 ∨ (ct.get k').2.1 < (ct.get (k' + 1)).2.1) ∧
      ((seen >>> (ct.get k').2.1) &&& 1 = 0)) ∧
    (∀ k1 k2, k ≤ k1 → k1 < k2 → k2 < k + n → (ct.get k1).2.1 ≠ (ct.get k2).2.1) := by
  intro n
  induction n with
  | zero => intro k seen _; exact ⟨fun k' h1 h2 => absurd h2 (by omega), fun k1 k2 h1 h2 h3 => absurd h3 (by omega)⟩
  | succ n ih =>
    intro k seen h
    simp only [chkOrder, cond_eq_if] at h
    split_ifs at h with hc
    simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.beq_eq] at hc
    obtain ⟨⟨hc1, hc2⟩, hc3⟩ := hc
    obtain ⟨ih1, ih2⟩ := ih _ _ h
    refine ⟨fun k' h1 h2 => ?_, fun k1 k2 h1 h2 h3 => ?_⟩
    · rcases Nat.eq_or_lt_of_le h1 with rfl | h1
      · exact ⟨hc1, hc3, hc2⟩
      · obtain ⟨a, b, c⟩ := ih1 k' (by omega) (by omega)
        exact ⟨a, b, (bit_or_ne c).2⟩
    · rcases Nat.eq_or_lt_of_le h1 with rfl | h1
      · have := (ih1 k2 (by omega) (by omega)).2.2
        exact fun e => (bit_or_ne this).1 e.symm
      · exact ih2 k1 k2 (by omega) h2 (by omega)

end K

/-! ## Windows of a monotone order (standalone) -/

lemma tm_lt_iff' {nR : ℕ} (tm : Fin nR → Fin 9 → ℕ) (hmono : ∀ ρ (l l' : Fin 9), l < l' → tm ρ l < tm ρ l')
    (ρ : Fin nR) (m : Fin 9) (τ : ℕ) : tm ρ m < τ ↔ m.val < progT tm ρ τ := by
  have tle : ∀ {l l' : Fin 9}, l ≤ l' → tm ρ l ≤ tm ρ l' := fun {l l'} h => by
    rcases h.lt_or_eq with h | h
    · exact (hmono ρ l l' h).le
    · rw [h]
  unfold progT
  constructor
  · intro h
    have hsub : Finset.Iic m ⊆ univ.filter (fun l : Fin 9 => tm ρ l < τ) := by
      intro l hl
      simp only [Finset.mem_Iic] at hl
      simp only [mem_filter, mem_univ, true_and]
      exact lt_of_le_of_lt (tle hl) h
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    omega
  · intro h
    by_contra hc
    have hsub : univ.filter (fun l : Fin 9 => tm ρ l < τ) ⊆ Finset.Iio m := by
      intro l hl
      simp only [mem_filter, mem_univ, true_and] at hl
      simp only [Finset.mem_Iio]
      by_contra hl'
      exact hc (lt_of_le_of_lt (tle (not_lt.mp hl')) hl)
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    omega

lemma kzN_eq (c : Fin 9) : K.kzN c.val = kz c := by fin_cases c <;> rfl
lemma kKN_eq (c : Fin 9) : K.kKN c.val = kK c := by fin_cases c <;> rfl
lemma rkN_eq (c : Fin 9) : K.rkN c.val = rankOf c.val := by fin_cases c <;> rfl

/-! ## The schedule of a checked table -/

/-- the time of call `(ρ, l)`. -/
def tmK (ct : K.CT) (nR : ℕ) (ρ : Fin nR) (l : Fin 9) : ℕ := (ct.get (9 * ρ.val + l.val)).2.1

/-- the residual of slot `q` of call `(ρ, l)` in the table (its provider word's). -/
def resK (ct : K.CT) (resT nR R : ℕ) (ρ : Fin nR) (l : Fin 9) (q : Fin R) : ℕ :=
  K.resAt resT (ct.get (9 * ρ.val + l.val)).2.2 q.val

/-- the host of host index `i = 2016 ρh + 224 c + 112 s + t`. -/
def decH (nR : ℕ) (hnR : 0 < nR) (i : ℕ) : Fin nR × Fin 9 × (Bool × Fin 112) :=
  (⟨i / 2016 % nR, Nat.mod_lt _ hnR⟩, ⟨i % 2016 / 224, by omega⟩, (decide (112 ≤ i % 224), ⟨i % 112, by omega⟩))

/-- the index of a host. -/
def encH' (nR : ℕ) (ρh : Fin nR) (c : Fin 9) (j : Bool × Fin 112) : ℕ :=
  2016 * ρh.val + 224 * c.val + (if j.1 then 112 else 0) + j.2.val

lemma encH'_lt (nR : ℕ) (ρh : Fin nR) (c : Fin 9) (j : Bool × Fin 112) : encH' nR ρh c j < 2016 * nR := by
  unfold encH'
  have := ρh.isLt; have := c.isLt; have := j.2.isLt
  split_ifs <;> omega

lemma decH_encH (nR : ℕ) (hnR : 0 < nR) (ρh : Fin nR) (c : Fin 9) (j : Bool × Fin 112) :
    decH nR hnR (encH' nR ρh c j) = (ρh, c, j) := by
  obtain ⟨s, t⟩ := j
  have := ρh.isLt; have := c.isLt; have := t.isLt
  have key : encH' nR ρh c (s, t) = 2016 * ρh.val + 224 * c.val + (if s then 112 else 0) + t.val := rfl
  have hdiv : encH' nR ρh c (s, t) / 2016 = ρh.val := by rw [key]; cases s <;> simp <;> omega
  have hc : encH' nR ρh c (s, t) % 2016 / 224 = c.val := by rw [key]; cases s <;> simp <;> omega
  have hs : decide (112 ≤ encH' nR ρh c (s, t) % 224) = s := by rw [key]; cases s <;> simp <;> omega
  have ht : encH' nR ρh c (s, t) % 112 = t.val := by rw [key]; cases s <;> simp <;> omega
  refine Prod.ext (Fin.ext ?_) (Prod.ext (Fin.ext ?_) (Prod.ext ?_ (Fin.ext ?_)))
  · show encH' nR ρh c (s, t) / 2016 % nR = ρh.val
    rw [hdiv]
    exact Nat.mod_eq_of_lt ρh.isLt
  · exact hc
  · exact hs
  · exact ht

lemma encH_decH (nR : ℕ) (hnR : 0 < nR) (i : ℕ) (hi : i < 2016 * nR) :
    encH' nR (decH nR hnR i).1 (decH nR hnR i).2.1 (decH nR hnR i).2.2 = i := by
  show 2016 * (i / 2016 % nR) + 224 * (i % 2016 / 224) + (if decide (112 ≤ i % 224) = true then 112 else 0)
    + i % 112 = i
  have h1 : i / 2016 % nR = i / 2016 := Nat.mod_eq_of_lt (by omega)
  rw [h1]
  split_ifs with h <;> simp at h <;> omega

/-- the order facts of a checked order. -/
def OrdFacts (ct : K.CT) (nR : ℕ) : Prop :=
  (∀ ρ l, tmK ct nR ρ l < 9 * nR) ∧ (∀ ρ ρ' l l', tmK ct nR ρ l = tmK ct nR ρ' l' → ρ = ρ' ∧ l = l') ∧
    (∀ ρ (l l' : Fin 9), l < l' → tmK ct nR ρ l < tmK ct nR ρ l')

lemma tmK_facts (ct : K.CT) (nR : ℕ) (hord : K.chkOrder ct (9 * nR) (9 * nR) 0 0 = true) : OrdFacts ct nR := by
  obtain ⟨h1, h2⟩ := K.chkOrder_sound ct (9 * nR) (9 * nR) 0 0 hord
  have hk : ∀ (ρ : Fin nR) (l : Fin 9), 9 * ρ.val + l.val < 9 * nR := fun ρ l => by
    have := ρ.isLt; have := l.isLt; omega
  refine ⟨fun ρ l => (h1 _ (Nat.zero_le _) (by have := hk ρ l; omega)).1, fun ρ ρ' l l' e => ?_, ?_⟩
  · have hk1 := hk ρ l
    have hk2 := hk ρ' l'
    have e2 : 9 * ρ.val + l.val = 9 * ρ'.val + l'.val := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · exact h2 _ _ (Nat.zero_le _) h (by omega) e
      · exact h2 _ _ (Nat.zero_le _) h (by omega) e.symm
    have := l.isLt; have := l'.isLt
    exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
  · have step : ∀ (ρ : Fin nR) (m : ℕ) (hm : m + 1 < 9),
        tmK ct nR ρ ⟨m, by omega⟩ < tmK ct nR ρ ⟨m + 1, hm⟩ := by
      intro ρ m hm
      have := (h1 (9 * ρ.val + m) (Nat.zero_le _) (by have := ρ.isLt; omega)).2.1
      have hmod : (9 * ρ.val + m) % 9 ≠ 8 := by omega
      rcases this with h | h
      · exact absurd h hmod
      · show (ct.get (9 * ρ.val + m)).2.1 < (ct.get (9 * ρ.val + (m + 1))).2.1
        rw [← Nat.add_assoc]
        exact h
    intro ρ l l' hll
    have key : ∀ d : ℕ, ∀ (a : ℕ) (ha : a + d + 1 < 9),
        tmK ct nR ρ ⟨a, by omega⟩ < tmK ct nR ρ ⟨a + d + 1, ha⟩ := by
      intro d
      induction d with
      | zero => intro a ha; exact step ρ a ha
      | succ d ih =>
        intro a ha
        exact lt_trans (ih a (by omega)) (step ρ (a + d + 1) ha)
    rw [Fin.lt_def] at hll
    have := key (l'.val - l.val - 1) l.val (by have := l'.isLt; omega)
    have e1 : (⟨l.val, by omega⟩ : Fin 9) = l := Fin.ext rfl
    have e2 : (⟨l.val + (l'.val - l.val - 1) + 1, by have := l'.isLt; omega⟩ : Fin 9) = l' :=
      Fin.ext (by simp only; omega)
    rw [e1, e2] at this
    exact this

/-- the map from calls to times, a bijection. -/
def tmF (ct : K.CT) (nR : ℕ) (hf : OrdFacts ct nR) (p : Fin nR × Fin 9) : Fin (9 * nR) :=
  ⟨tmK ct nR p.1 p.2, hf.1 p.1 p.2⟩

lemma tmF_bij (ct : K.CT) (nR : ℕ) (hf : OrdFacts ct nR) : Function.Bijective (tmF ct nR hf) := by
  have hinj : Function.Injective (tmF ct nR hf) := fun p p' h => by
    have e := hf.2.1 p.1 p'.1 p.2 p'.2 (congrArg Fin.val h)
    exact Prod.ext e.1 e.2
  exact (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, by simp [mul_comm]⟩

/-- the call at time `τ` (inverse of `tmK`). -/
def clK (ct : K.CT) (nR : ℕ) (hf : OrdFacts ct nR) : Fin (9 * nR) → Fin nR × Fin 9 :=
  (Equiv.ofBijective (tmF ct nR hf) (tmF_bij ct nR hf)).symm

lemma clK_spec (ct : K.CT) (nR : ℕ) (hf : OrdFacts ct nR) (τ : Fin (9 * nR)) :
    tmK ct nR (clK ct nR hf τ).1 (clK ct nR hf τ).2 = τ.val :=
  congrArg Fin.val (Equiv.apply_symm_apply (Equiv.ofBijective (tmF ct nR hf) (tmF_bij ct nR hf)) τ)

/-- the window of the kernel check is the window of the decoded host. -/
lemma win_of_tab (ct : K.CT) (nR : ℕ) (hnR : 0 < nR)
    (hmono : ∀ ρ (l l' : Fin 9), l < l' → tmK ct nR ρ l < tmK ct nR ρ l') (ρ : Fin nR) (l : Fin 9)
    (i : ℕ) (hi : i < 224 * (9 * nR)) (hlo : (K.winOf ct (i / 224)).1 ≤ (ct.get (9 * ρ.val + l.val)).2.1)
    (hhi : (ct.get (9 * ρ.val + l.val)).2.1 ≤ (K.winOf ct (i / 224)).2) :
    inWin (decH nR hnR i).2.1.val (progT (tmK ct nR) (decH nR hnR i).1 (tmK ct nR ρ l)) = true := by
  have eρ : (decH nR hnR i).1.val = i / 2016 := by
    show i / 2016 % nR = i / 2016
    exact Nat.mod_eq_of_lt (by omega)
  have ec : (decH nR hnR i).2.1.val = i % 2016 / 224 := rfl
  set c := (decH nR hnR i).2.1 with hcdef
  set ρh := (decH nR hnR i).1 with hρdef
  have hc9 : i / 224 % 9 = c.val := by rw [ec]; omega
  have hρ9 : i / 224 / 9 = ρh.val := by rw [eρ]; omega
  simp only [K.winOf, cond_eq_if, Nat.beq_eq, hc9, hρ9, kzN_eq, kKN_eq] at hlo hhi
  rw [HostSchedT.inWin_iff]
  have hK1 : 1 ≤ kK c := (show ∀ c : Fin 9, 1 ≤ kK c by decide) c
  have hle : kz c + kK c ≤ 9 := (show ∀ c : Fin 9, kz c + kK c ≤ 9 by decide) c
  constructor
  · by_cases hz : kz c = 0
    · rw [hz]; exact Nat.zero_le _
    · rw [if_neg hz] at hlo
      have hlt : tmK ct nR ρh ⟨kz c - 1, by omega⟩ < tmK ct nR ρ l := by
        show (ct.get (9 * ρh.val + (kz c - 1))).2.1 < (ct.get (9 * ρ.val + l.val)).2.1
        rw [show 9 * ρh.val + (kz c - 1) = 9 * ρh.val + kz c - 1 by omega]
        omega
      have := (tm_lt_iff' (tmK ct nR) hmono ρh ⟨kz c - 1, by omega⟩ _).mp hlt
      simp only at this
      omega
  · by_contra hc
    have hlt : kz c + kK c - 1 < progT (tmK ct nR) ρh (tmK ct nR ρ l) := by omega
    have := (tm_lt_iff' (tmK ct nR) hmono ρh ⟨kz c + kK c - 1, by omega⟩ _).mpr hlt
    have h2 : tmK ct nR ρh ⟨kz c + kK c - 1, by omega⟩ = (ct.get (9 * ρh.val + kz c + kK c - 1)).2.1 := by
      show (ct.get (9 * ρh.val + (kz c + kK c - 1))).2.1 = _
      rw [show 9 * ρh.val + (kz c + kK c - 1) = 9 * ρh.val + kz c + kK c - 1 by omega]
    rw [h2] at this
    exact absurd hhi (not_le.mpr this)

/-- what a checked table gives (the conclusion of `K.table_sound` with `9 nR` calls and kinds; p-hostck's
`K.TableOK ct rt resT NC R NK` unfolds to it when `NC = NK = 9 nR`). -/
def TabOK (ct rt : K.CT) (resT nR R : ℕ) : Prop :=
  (∀ k < 9 * nR, ∀ q < R, K.rowAt (ct.get k).1 q < 224 * (9 * nR) ∧
      (K.winOf ct (K.rowAt (ct.get k).1 q / 224)).1 ≤ (ct.get k).2.1 ∧
      (ct.get k).2.1 ≤ (K.winOf ct (K.rowAt (ct.get k).1 q / 224)).2) ∧
  (∀ k < 9 * nR, ∀ q < R, ∀ q' < R, K.rowAt (ct.get k).1 q = K.rowAt (ct.get k).1 q' → q = q') ∧
  (∀ i < 224 * (9 * nR), (∑ x ∈ (range (9 * nR) ×ˢ range R).filter (fun x => K.rowAt (ct.get x.1).1 x.2 = i),
      K.resAt resT (ct.get x.1).2.2 x.2) + K.remAt rt i = K.rkN (i / 224 % 9))

/-- **the host schedule of a checked table** (`hT`: the table facts, `hord`: the order check). -/
def schedOfTabOK (ct rt : K.CT) (resT nR R : ℕ) (hnR : 0 < nR) (hT : TabOK ct rt resT nR R)
    (hord : K.chkOrder ct (9 * nR) (9 * nR) 0 0 = true) : HostSchedT nR (Fin R) (Fin 112) where
  tm := tmK ct nR
  cl := clK ct nR (tmK_facts ct nR hord)
  htm_lt := (tmK_facts ct nR hord).1
  htm_inj := (tmK_facts ct nR hord).2.1
  htm_mono := (tmK_facts ct nR hord).2.2
  hcl := clK_spec ct nR (tmK_facts ct nR hord)
  host := fun ρ l q => decH nR hnR (K.rowAt (ct.get (9 * ρ.val + l.val)).1 q.val)
  hostInj := fun ρ l q q' h => by
    have hk : 9 * ρ.val + l.val < 9 * nR := by have := ρ.isLt; have := l.isLt; omega
    obtain ⟨hA, hB, -⟩ := hT
    have i1 := (hA _ hk q.val q.isLt).1
    have i2 := (hA _ hk q'.val q'.isLt).1
    have e : K.rowAt (ct.get (9 * ρ.val + l.val)).1 q.val = K.rowAt (ct.get (9 * ρ.val + l.val)).1 q'.val := by
      have e1 := encH_decH nR hnR (K.rowAt (ct.get (9 * ρ.val + l.val)).1 q.val) (by omega)
      have e2 := encH_decH nR hnR (K.rowAt (ct.get (9 * ρ.val + l.val)).1 q'.val) (by omega)
      have h' : decH nR hnR (K.rowAt (ct.get (9 * ρ.val + l.val)).1 q.val)
          = decH nR hnR (K.rowAt (ct.get (9 * ρ.val + l.val)).1 q'.val) := h
      rw [h'] at e1
      exact e1.symm.trans e2
    exact Fin.ext (hB _ hk _ q.isLt _ q'.isLt e)
  hostWin := fun ρ l q => by
    have hk : 9 * ρ.val + l.val < 9 * nR := by have := ρ.isLt; have := l.isLt; omega
    obtain ⟨hA, -, -⟩ := hT
    obtain ⟨hi, hlo, hhi⟩ := hA _ hk q.val q.isLt
    exact win_of_tab ct nR hnR (tmK_facts ct nR hord).2.2 ρ l _ hi hlo hhi
  hrem := fun ρh c j => K.remAt rt (encH' nR ρh c j)

/-- **the schedule of a checked table fits the table's residuals.** -/
theorem schedOfTabOK_fits (ct rt : K.CT) (resT nR R : ℕ) (hnR : 0 < nR) (hT : TabOK ct rt resT nR R)
    (hord : K.chkOrder ct (9 * nR) (9 * nR) 0 0 = true) :
    (schedOfTabOK ct rt resT nR R hnR hT hord).fits (resK ct resT nR R) := by
  intro ρh c j
  obtain ⟨hA, hB, hC⟩ := hT
  have hilt := encH'_lt nR ρh c j
  have hC' := hC (encH' nR ρh c j) (by omega)
  have hrk : encH' nR ρh c j / 224 % 9 = c.val := by
    unfold encH'
    have := ρh.isLt; have := c.isLt; have := j.2.isLt
    split_ifs <;> omega
  rw [hrk, rkN_eq] at hC'
  rw [← hC']
  congr 1
  unfold HostSchedT.load
  refine Finset.sum_bij (fun p _ => (9 * p.1.val + p.2.1.val, p.2.2.val)) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have hk : 9 * p.1.val + p.2.1.val < 9 * nR := by have := p.1.isLt; have := p.2.1.isLt; omega
    have hr := (hA _ hk p.2.2.val p.2.2.isLt).1
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    refine ⟨⟨hk, p.2.2.isLt⟩, ?_⟩
    show K.rowAt (ct.get (9 * p.1.val + p.2.1.val)).1 p.2.2.val = encH' nR ρh c j
    calc K.rowAt (ct.get (9 * p.1.val + p.2.1.val)).1 p.2.2.val
        = encH' nR (decH nR hnR (K.rowAt (ct.get (9 * p.1.val + p.2.1.val)).1 p.2.2.val)).1
            (decH nR hnR (K.rowAt (ct.get (9 * p.1.val + p.2.1.val)).1 p.2.2.val)).2.1
            (decH nR hnR (K.rowAt (ct.get (9 * p.1.val + p.2.1.val)).1 p.2.2.val)).2.2 :=
          (encH_decH nR hnR _ (by omega)).symm
      _ = encH' nR ρh c j := by
          have hp' : decH nR hnR (K.rowAt (ct.get (9 * p.1.val + p.2.1.val)).1 p.2.2.val) = (ρh, c, j) := hp
          rw [hp']
  · intro p _ p' _ h
    simp only [Prod.mk.injEq] at h
    have := p.2.1.isLt; have := p'.2.1.isLt
    exact Prod.ext (Fin.ext (by omega)) (Prod.ext (Fin.ext (by omega)) (Fin.ext h.2))
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hx
    obtain ⟨⟨hk, hq⟩, hr⟩ := hx
    refine ⟨(⟨x.1 / 9, by omega⟩, ⟨x.1 % 9, by omega⟩, ⟨x.2, hq⟩), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      show decH nR hnR (K.rowAt (ct.get (9 * (x.1 / 9) + x.1 % 9)).1 x.2) = (ρh, c, j)
      rw [show 9 * (x.1 / 9) + x.1 % 9 = x.1 by omega, hr, decH_encH]
    · simp only
      exact Prod.ext (by omega) rfl
  · intro p _
    rfl

/-- the schedule's data, as the table's (all by definition). -/
lemma schedOfTabOK_tm (ct rt : K.CT) (resT nR R : ℕ) (hnR : 0 < nR) (hT : TabOK ct rt resT nR R)
    (hord : K.chkOrder ct (9 * nR) (9 * nR) 0 0 = true) (ρ : Fin nR) (l : Fin 9) :
    (schedOfTabOK ct rt resT nR R hnR hT hord).tm ρ l = (ct.get (9 * ρ.val + l.val)).2.1 := rfl

lemma schedOfTabOK_host (ct rt : K.CT) (resT nR R : ℕ) (hnR : 0 < nR) (hT : TabOK ct rt resT nR R)
    (hord : K.chkOrder ct (9 * nR) (9 * nR) 0 0 = true) (ρ : Fin nR) (l : Fin 9) (q : Fin R) :
    (schedOfTabOK ct rt resT nR R hnR hT hord).host ρ l q = decH nR hnR (K.rowAt (ct.get (9 * ρ.val + l.val)).1 q.val) :=
  rfl

lemma schedOfTabOK_hrem (ct rt : K.CT) (resT nR R : ℕ) (hnR : 0 < nR) (hT : TabOK ct rt resT nR R)
    (hord : K.chkOrder ct (9 * nR) (9 * nR) 0 0 = true) (ρh : Fin nR) (c : Fin 9) (j : Bool × Fin 112) :
    (schedOfTabOK ct rt resT nR R hnR hT hord).hrem ρh c j
      = K.remAt rt (2016 * ρh.val + 224 * c.val + (if j.1 then 112 else 0) + j.2.val) := rfl

/-- the per-kind form: one `chkPieceCount` theorem per host kind and the counts. -/
lemma tabOK_of_kinds (ct rt : K.CT) (resT nR R : ℕ) (cK : ℕ → ℕ)
    (hK : ∀ κ < 9 * nR, ∃ bs rs, K.chkPieceCount ct rt resT (9 * nR) R κ 1 bs rs = some (cK κ))
    (hsum : ((List.range (9 * nR)).map cK).sum = 9 * nR * R) : TabOK ct rt resT nR R :=
  K.table_sound (NK := 9 * nR) cK hK hsum

/-- the host schedule of a table checked kind by kind. -/
def schedOfTab (ct rt : K.CT) (resT nR R : ℕ) (hnR : 0 < nR) (cK : ℕ → ℕ)
    (hord : K.chkOrder ct (9 * nR) (9 * nR) 0 0 = true)
    (hK : ∀ κ < 9 * nR, ∃ bs rs, K.chkPieceCount ct rt resT (9 * nR) R κ 1 bs rs = some (cK κ))
    (hsum : ((List.range (9 * nR)).map cK).sum = 9 * nR * R) : HostSchedT nR (Fin R) (Fin 112) :=
  schedOfTabOK ct rt resT nR R hnR (tabOK_of_kinds ct rt resT nR R cK hK hsum) hord

theorem schedOfTab_fits (ct rt : K.CT) (resT nR R : ℕ) (hnR : 0 < nR) (cK : ℕ → ℕ)
    (hord : K.chkOrder ct (9 * nR) (9 * nR) 0 0 = true)
    (hK : ∀ κ < 9 * nR, ∃ bs rs, K.chkPieceCount ct rt resT (9 * nR) R κ 1 bs rs = some (cK κ))
    (hsum : ((List.range (9 * nR)).map cK).sum = 9 * nR * R) :
    (schedOfTab ct rt resT nR R hnR cK hord hK hsum).fits (resK ct resT nR R) :=
  schedOfTabOK_fits ct rt resT nR R hnR _ hord

end
end XHostT
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.XHostT.K.chkOrder_sound
#print axioms OAI.PowerSaving.XHostT.schedOfTabOK
#print axioms OAI.PowerSaving.XHostT.schedOfTabOK_fits
#print axioms OAI.PowerSaving.XHostT.schedOfTab_fits
