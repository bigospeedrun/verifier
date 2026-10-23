import Submission.Work.XHost.HSched

/-!
# (key: bridge-host-perrun) PER-RUN host schedules of the hosted nine-stage word

h-L3-build's `XHost.HostSched` has ONE host table `hostAt : Fin 9 → Sl → ...` used by all 8 runs.  Here the table is
indexed by the run as well: `hostAt : Fin 8 → Fin 9 → Sl → Option (Fin 9 × (Bool × T))`, and the remainders `hrem`
of the host chains are per run.  `bUseR` (banks of the slots that are not hosted, sub-stage `k = 9 ρ + l`) and
`HostSchedR.fitsR` (every bank's load plus pad is 73; for every run, every host's load plus remainder is the rank of
its idle climb).  `HostSched.toR`: the same-run table of h-L3-build as the special case "the same table in every run",
with the same residual conditions (`HostSched.toR_fitsR`).
Written by fsp-perrun (wht43, 14 Oct 2026), after h-L3-build's Work/XHost/HSched.lean; prepared with assistance from
Claude.  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace OAI
namespace PowerSaving
namespace XHostR
open Finset XHost

section Tables
variable {Sl T : Type} {nb : ℕ}

/-- the bank of the slot `q` in sub-stage `k = 9 ρ + l` (`none`: the slot is hosted), per-run table. -/
def bUseR (hs : Fin 8 → Fin 9 → Sl → Option (Fin 9 × (Bool × T))) (bk : Fin 8 → Fin 9 → Sl → Fin nb) (k : ℕ)
    (q : Sl) : Option (Fin nb) :=
  match hs ⟨k / 9 % 8, Nat.mod_lt _ (by norm_num)⟩ ⟨k % 9, Nat.mod_lt _ (by norm_num)⟩ q with
  | none => some (bk ⟨k / 9 % 8, Nat.mod_lt _ (by norm_num)⟩ ⟨k % 9, Nat.mod_lt _ (by norm_num)⟩ q)
  | some _ => none

lemma bUseR_eq (hs : Fin 8 → Fin 9 → Sl → Option (Fin 9 × (Bool × T))) (bk : Fin 8 → Fin 9 → Sl → Fin nb)
    (ρ : Fin 8) (l : Fin 9) (q : Sl) :
    bUseR hs bk (9 * ρ.val + l.val) q = (match hs ρ l q with | none => some (bk ρ l q) | some _ => none) := by
  unfold bUseR
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

lemma bUseR_bank {hs : Fin 8 → Fin 9 → Sl → Option (Fin 9 × (Bool × T))} {bk : Fin 8 → Fin 9 → Sl → Fin nb}
    (ρ : Fin 8) (l : Fin 9) (q : Sl) (hq : hs ρ l q = none) :
    bUseR hs bk (9 * ρ.val + l.val) q = some (bk ρ l q) := by
  rw [bUseR_eq, hq]

lemma bUseR_to {hs : Fin 8 → Fin 9 → Sl → Option (Fin 9 × (Bool × T))} {bk : Fin 8 → Fin 9 → Sl → Fin nb}
    (ρ : Fin 8) (l : Fin 9) (q : Sl) (b : Fin nb) (h : bUseR hs bk (9 * ρ.val + l.val) q = some b) :
    hs ρ l q = none ∧ bk ρ l q = b := by
  rw [bUseR_eq] at h
  revert h
  rcases e : hs ρ l q with _ | x
  · intro h
    simp only [Option.some.injEq] at h
    exact ⟨rfl, h⟩
  · intro h
    exact absurd h (by simp)

lemma bUseR_one (hs : Fin 8 → Fin 9 → Sl → Option (Fin 9 × (Bool × T))) (bk : Fin 8 → Fin 9 → Sl → Fin nb)
    (hinj : ∀ ρ l q q', hs ρ l q = none → hs ρ l q' = none → bk ρ l q = bk ρ l q' → q = q') (k : ℕ) (hk : k < 72) :
    OneUse (bUseR hs bk) k := by
  intro q q' b h h'
  have e : k = 9 * (⟨k / 9, by omega⟩ : Fin 8).val + (⟨k % 9, Nat.mod_lt _ (by norm_num)⟩ : Fin 9).val := by
    show k = 9 * (k / 9) + k % 9
    omega
  rw [e] at h h'
  obtain ⟨h1, h2⟩ := bUseR_to _ _ q b h
  obtain ⟨h1', h2'⟩ := bUseR_to _ _ q' b h'
  exact hinj _ _ q q' h1 h1' (h2.trans h2'.symm)

/-- with the same table in every run, `bUseR` is h-L3-build's `bUse`. -/
lemma bUseR_const (hs : Fin 9 → Sl → Option (Fin 9 × (Bool × T))) (bk : Fin 8 → Fin 9 → Sl → Fin nb) :
    bUseR (fun _ => hs) bk = bUse hs bk := by
  funext k q
  unfold bUseR bUse
  beta_reduce
  cases hs ⟨k % 9, Nat.mod_lt _ (by norm_num)⟩ q <;> rfl

end Tables

/-- **A per-run host schedule**: one host table and one set of remainders per run, the banks, the pads. -/
structure HostSchedR (Sl T : Type) [Fintype Sl] where
  nb : ℕ
  hostAt : Fin 8 → Fin 9 → Sl → Option (Fin 9 × (Bool × T))
  hostInj : ∀ ρ l q q' j, hostAt ρ l q = some j → hostAt ρ l q' = some j → q = q'
  hostWin : ∀ ρ l q c j, hostAt ρ l q = some (c, j) → inWin c.val l.val = true
  bk : Fin 8 → Fin 9 → Sl → Fin nb
  hinj : ∀ ρ l q q', hostAt ρ l q = none → hostAt ρ l q' = none → bk ρ l q = bk ρ l q' → q = q'
  pad : Fin nb → ℕ
  hrem : Fin 8 → Fin 9 → Bool × T → ℕ

/-- **The residual conditions** for residuals `r`: banks `load + pad = 73`, `pad < 73`; for every run `ρ`, every host
`load + hrem = rank`. -/
def HostSchedR.fitsR {Sl T : Type} [Fintype Sl] [DecidableEq Sl] [DecidableEq T] (S : HostSchedR Sl T)
    (r : Sl → ℕ) : Prop :=
  (∀ b, LH (bUseR S.hostAt S.bk) r 72 b + S.pad b = 73) ∧
  (∀ b, S.pad b < 73) ∧
  (∀ ρ c j, LH (hUse (S.hostAt ρ) c (kz c)) r (kK c) j + S.hrem ρ c j = rankOf c.val)

/-- **The special case**: h-L3-build's same-run table, the same in every run. -/
def _root_.OAI.PowerSaving.XHost.HostSched.toR {Sl T : Type} [Fintype Sl] (S : XHost.HostSched Sl T) :
    HostSchedR Sl T where
  nb := S.nb
  hostAt := fun _ => S.hostAt
  hostInj := fun _ => S.hostInj
  hostWin := fun _ => S.hostWin
  bk := S.bk
  hinj := fun ρ => S.hinj ρ
  pad := S.pad
  hrem := fun _ => S.hrem

theorem _root_.OAI.PowerSaving.XHost.HostSched.toR_fitsR {Sl T : Type} [Fintype Sl] [DecidableEq Sl] [DecidableEq T]
    (S : XHost.HostSched Sl T) (r : Sl → ℕ) (h : S.fitsR r) : S.toR.fitsR r := by
  refine ⟨fun b => ?_, h.2.1, fun _ c j => h.2.2 c j⟩
  show LH (bUseR (fun _ => S.hostAt) S.bk) r 72 b + S.pad b = 73
  rw [bUseR_const]
  exact h.1 b

end XHostR
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.XHost.HostSched.toR_fitsR
