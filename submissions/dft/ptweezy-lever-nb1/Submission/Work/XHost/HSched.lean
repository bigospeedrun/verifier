import Submission.Work.XHost.Frames
import Submission.Work.XHost.HostK

/-!
# (key: bridge-host) Host schedules: the slot tables of the HOSTED nine-stage word and their residual conditions

`hUse` (the hosts of one window kind, step by step), `bUse` (the banks of the slots that are not hosted, sub-stage by
sub-stage), `HostSched` (host table, bank map, pads, remainders) and `HostSched.fitsR` (every bank's load plus pad is 73,
every host's load plus remainder is the rank of its idle climb).  Light module (Frames + HostK only).
Written by h-L3-build (wht43, 13 Oct 2026), prepared with assistance from Claude.  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace OAI
namespace PowerSaving
namespace XHost
open Finset

/-! ## The slot tables -/

section Tables
variable {Sl T : Type} {nb : ℕ}

/-- the hosts of kind `c` used in step `k` of the chain of a window that starts at stage `k0`. -/
def hUse (hs : Fin 9 → Sl → Option (Fin 9 × (Bool × T))) (c : Fin 9) (k0 k : ℕ) (q : Sl) : Option (Bool × T) :=
  if hk : k0 + k < 9 then
    (match hs ⟨k0 + k, hk⟩ q with
     | some (c', j) => if c' = c then some j else none
     | none => none)
  else none

lemma hUse_of {hs : Fin 9 → Sl → Option (Fin 9 × (Bool × T))} {c : Fin 9} {k0 k : ℕ} {q : Sl} {j : Bool × T}
    (hk : k0 + k < 9) (h : hs ⟨k0 + k, hk⟩ q = some (c, j)) : hUse hs c k0 k q = some j := by
  unfold hUse
  rw [dif_pos hk, h]
  simp

lemma hUse_to {hs : Fin 9 → Sl → Option (Fin 9 × (Bool × T))} {c : Fin 9} {k0 k : ℕ} {q : Sl} {j : Bool × T}
    (h : hUse hs c k0 k q = some j) : ∃ hk : k0 + k < 9, hs ⟨k0 + k, hk⟩ q = some (c, j) := by
  unfold hUse at h
  by_cases hk : k0 + k < 9
  · rw [dif_pos hk] at h
    refine ⟨hk, ?_⟩
    revert h
    rcases e : hs ⟨k0 + k, hk⟩ q with _ | ⟨c', j'⟩
    · intro h
      exact absurd h (by simp)
    · intro h
      by_cases hc : c' = c
      · subst hc
        simp at h
        rw [h]
      · simp [hc] at h
  · rw [dif_neg hk] at h
    exact absurd h (by simp)

lemma hUse_one (hs : Fin 9 → Sl → Option (Fin 9 × (Bool × T)))
    (hinj : ∀ l q q' j, hs l q = some j → hs l q' = some j → q = q') (c : Fin 9) (k0 k : ℕ) :
    OneUse (hUse hs c k0) k := by
  intro q q' j h h'
  obtain ⟨hk, e⟩ := hUse_to h
  obtain ⟨hk', e'⟩ := hUse_to h'
  exact hinj _ q q' _ e e'

/-- the bank of the slot `q` in sub-stage `k = 9 ρ + l` (`none`: the slot is hosted). -/
def bUse (hs : Fin 9 → Sl → Option (Fin 9 × (Bool × T))) (bk : Fin 8 → Fin 9 → Sl → Fin nb) (k : ℕ) (q : Sl) :
    Option (Fin nb) :=
  match hs ⟨k % 9, Nat.mod_lt _ (by norm_num)⟩ q with
  | none => some (bk ⟨k / 9 % 8, Nat.mod_lt _ (by norm_num)⟩ ⟨k % 9, Nat.mod_lt _ (by norm_num)⟩ q)
  | some _ => none

lemma bUse_eq (hs : Fin 9 → Sl → Option (Fin 9 × (Bool × T))) (bk : Fin 8 → Fin 9 → Sl → Fin nb)
    (ρ : Fin 8) (l : Fin 9) (q : Sl) :
    bUse hs bk (9 * ρ.val + l.val) q = (match hs l q with | none => some (bk ρ l q) | some _ => none) := by
  unfold bUse
  have h1 : (⟨(9 * ρ.val + l.val) / 9 % 8, Nat.mod_lt _ (by norm_num)⟩ : Fin 8) = ρ := by
    apply Fin.ext
    show (9 * ρ.val + l.val) / 9 % 8 = ρ.val
    have := ρ.isLt
    have := l.isLt
    omega
  have h2 : (⟨(9 * ρ.val + l.val) % 9, Nat.mod_lt _ (by norm_num)⟩ : Fin 9) = l := by
    apply Fin.ext
    show (9 * ρ.val + l.val) % 9 = l.val
    have := l.isLt
    omega
  rw [h1, h2]

lemma bUse_bank {hs : Fin 9 → Sl → Option (Fin 9 × (Bool × T))} {bk : Fin 8 → Fin 9 → Sl → Fin nb}
    (ρ : Fin 8) (l : Fin 9) (q : Sl) (hq : hs l q = none) :
    bUse hs bk (9 * ρ.val + l.val) q = some (bk ρ l q) := by
  rw [bUse_eq, hq]

lemma bUse_to {hs : Fin 9 → Sl → Option (Fin 9 × (Bool × T))} {bk : Fin 8 → Fin 9 → Sl → Fin nb}
    (ρ : Fin 8) (l : Fin 9) (q : Sl) (b : Fin nb) (h : bUse hs bk (9 * ρ.val + l.val) q = some b) :
    hs l q = none ∧ bk ρ l q = b := by
  rw [bUse_eq] at h
  revert h
  rcases e : hs l q with _ | x
  · intro h
    simp only [Option.some.injEq] at h
    exact ⟨rfl, h⟩
  · intro h
    exact absurd h (by simp)

lemma bUse_one (hs : Fin 9 → Sl → Option (Fin 9 × (Bool × T))) (bk : Fin 8 → Fin 9 → Sl → Fin nb)
    (hinj : ∀ ρ l q q', hs l q = none → hs l q' = none → bk ρ l q = bk ρ l q' → q = q') (k : ℕ) (hk : k < 72) :
    OneUse (bUse hs bk) k := by
  intro q q' b h h'
  have e : k = 9 * (⟨k / 9, by omega⟩ : Fin 8).val + (⟨k % 9, Nat.mod_lt _ (by norm_num)⟩ : Fin 9).val := by
    show k = 9 * (k / 9) + k % 9
    omega
  rw [e] at h h'
  obtain ⟨h1, h2⟩ := bUse_to _ _ q b h
  obtain ⟨h1', h2'⟩ := bUse_to _ _ q' b h'
  exact hinj _ _ q q' h1 h1' (h2.trans h2'.symm)

end Tables

/-! ## The host schedule -/

/-- start stage and length of the window of kind `c` (A2 B2 A3 B3 A4 B4 F1 F2 F3). -/
def kz (c : Fin 9) : ℕ :=
  match c.val with
  | 0 => 0
  | 1 => 2
  | 2 => 0
  | 3 => 4
  | 4 => 0
  | 5 => 6
  | 6 => 3
  | 7 => 5
  | _ => 7

def kK (c : Fin 9) : ℕ :=
  match c.val with
  | 0 => 2
  | 1 => 1
  | 2 => 4
  | 3 => 1
  | 4 => 6
  | 5 => 1
  | 6 => 6
  | 7 => 4
  | _ => 2

/-- **A host schedule**: the host table, the banks of the slots that are not hosted, the pads, the remainders. -/
structure HostSched (Sl T : Type) [Fintype Sl] where
  nb : ℕ
  hostAt : Fin 9 → Sl → Option (Fin 9 × (Bool × T))
  hostInj : ∀ l q q' j, hostAt l q = some j → hostAt l q' = some j → q = q'
  hostWin : ∀ l q c j, hostAt l q = some (c, j) → inWin c.val l.val = true
  bk : Fin 8 → Fin 9 → Sl → Fin nb
  hinj : ∀ ρ l q q', hostAt l q = none → hostAt l q' = none → bk ρ l q = bk ρ l q' → q = q'
  pad : Fin nb → ℕ
  hrem : Fin 9 → Bool × T → ℕ

/-- **The residual conditions** for residuals `r`: banks `load + pad = 73`, `pad < 73`; hosts `load + hrem = rank`. -/
def HostSched.fitsR {Sl T : Type} [Fintype Sl] [DecidableEq Sl] [DecidableEq T] (S : HostSched Sl T)
    (r : Sl → ℕ) : Prop :=
  (∀ b, LH (bUse S.hostAt S.bk) r 72 b + S.pad b = 73) ∧
  (∀ b, S.pad b < 73) ∧
  (∀ c j, LH (hUse S.hostAt c (kz c)) r (kK c) j + S.hrem c j = rankOf c.val)


end XHost
end PowerSaving
end OAI
