import Submission.Work.Bridge401.GStage
import Submission.Work.Bridge401.StageE
import Submission.Work.Bridge377.Bank

/-! Merged module written by bos_merge.py for the 500-file limit of the Big O Speedrun
pull-request route.  It is the concatenation, in import order, of the 3 modules below; each one
is copied verbatim after its import header, inside `section` ... `end`, with the scopes it leaves
open closed before that `end`.  Members (module, sha256 of the original file):
* `Submission.Work.Bridge401.GNetDef` d5880a8948fd9acfc335a9d78d358a97bcc7ab94d94a0eff6386501b59bd2840
* `Submission.Work.Bridge401.GNetStage` d35dd0647d55dd564389458f429d002b9ca321f94c6e25a2011146b5b90c130e
* `Submission.Work.Bridge401.GNetCert` 4e4ffec171d90609ff322e05d17525240f8d8a88c64c5eba70b22d8c5e7dbab3
-/

-- bos_merge: begin Submission.Work.Bridge401.GNetDef
section

/-!
# (key: bridge-401) The nine-stage word with entrance gauges and residual banks (PR #401): data and frames

Credits: the entrance gauges and the residual banks are Dugongue's (CrocSwap/integer-mult-bounds PR #401); the bank
patterns are Lydakis's (#275); the compressed nine-stage layout is jacklightChen's (#377); the bridged word B_K is
DaysSky's (#363); B_2, the engine, the stage geometry and the E8 unit are Jacob Sussman's (wht-power-saving-lean,
Apache-2.0).  Written by w-newsums/gen401/gen401.py (from gen377.py).
One RUN is the B_4 word of genk (stages 0, 1, 2 on pair 1; stages 2p-1, 2p on pair p >= 2; idle climbs and gate
layers between) for the data of ONE replica.  In stage `l` of run `ρ` the slot `q` of the invocation `g` uses the bank
`(g, use ρ l q)`; before the stage every bank takes its free adapter (`Zb` to `Zp`, `bank_adapt`), and the gauged
step `Wn` moves the used banks to `Zb` of the next sub-stage.  The unit is the 8 runs one after the other
(replica-outer), then ONE padding block of rank `pad b` on every bank.  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace OAI
namespace PowerSaving
namespace GX
open Binary Matrix Finset RAM SS CB RF BR GF
noncomputable section

/-- See the file header.  Stages are numbered 0 to 8, runs (replicas) 0 to 7. -/
structure G401 (H T Sl C α Γ : Type) (nb : ℕ) [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
    [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C] [Fintype α] [DecidableEq α] where
  /-- the gauged invocation (`GInvE`, L1 of DFT Bridge3). -/
  I : GInvE H T Sl C
  /-- frame maps of the invocations of the 9 stages. -/
  G0 : Γ → GWin H α
  G1 : Γ → GWin H α
  G2 : Γ → GWin H α
  G3 : Γ → GWin H α
  G4 : Γ → GWin H α
  G5 : Γ → GWin H α
  G6 : Γ → GWin H α
  G7 : Γ → GWin H α
  G8 : Γ → GWin H α
  /-- the class `(g,t)` is served by the invocation `g` in stage 0 and `r_l t g` in stage `l` (every run). -/
  r1 : T → Γ ≃ Γ
  r2 : T → Γ ≃ Γ
  r3 : T → Γ ≃ Γ
  r4 : T → Γ ≃ Γ
  r5 : T → Γ ≃ Γ
  r6 : T → Γ ≃ Γ
  r7 : T → Γ ≃ Γ
  r8 : T → Γ ≃ Γ
  /-- entrance step of the slot `q` of the invocation `d` in stage `l`: right inverse `N<l> d q`, step `Wn<l> d q`. -/
  N0 : Γ → Sl → CMat α
  Wn0 : Γ → Sl → CMat α
  N1 : Γ → Sl → CMat α
  Wn1 : Γ → Sl → CMat α
  N2 : Γ → Sl → CMat α
  Wn2 : Γ → Sl → CMat α
  N3 : Γ → Sl → CMat α
  Wn3 : Γ → Sl → CMat α
  N4 : Γ → Sl → CMat α
  Wn4 : Γ → Sl → CMat α
  N5 : Γ → Sl → CMat α
  Wn5 : Γ → Sl → CMat α
  N6 : Γ → Sl → CMat α
  Wn6 : Γ → Sl → CMat α
  N7 : Γ → Sl → CMat α
  Wn7 : Γ → Sl → CMat α
  N8 : Γ → Sl → CMat α
  Wn8 : Γ → Sl → CMat α
  /-- the bank of the slot `q` in stage `l` of run `ρ` (at most one use of a bank per sub-stage). -/
  use : Fin 8 → Fin 9 → Sl → Fin nb
  hinj : ∀ ρ l, Function.Injective (use ρ l)
  /-- bank frames before sub-stage `9 ρ + l` (`Zb`) and after its free adapter (`Zp`); the pad ranks. -/
  Zb : ℕ → Γ → Fin nb → CMat α
  Zp : ℕ → Γ → Fin nb → CMat α
  pad : Fin nb → ℕ
  u : Γ → T → Space α
  YF : Γ → T → CMat α
  hm : 2 ≤ Fintype.card α
  /-- prices of the idle climbs, for every price list. -/
  caX2 : (ℕ → ℝ) → ℝ
  caY2 : (ℕ → ℝ) → ℝ
  caX3 : (ℕ → ℝ) → ℝ
  caY3 : (ℕ → ℝ) → ℝ
  caX4 : (ℕ → ℝ) → ℝ
  caY4 : (ℕ → ℝ) → ℝ
  cX1 : (ℕ → ℝ) → ℝ
  cY1 : (ℕ → ℝ) → ℝ
  cX2 : (ℕ → ℝ) → ℝ
  cY2 : (ℕ → ℝ) → ℝ
  cX3 : (ℕ → ℝ) → ℝ
  cY3 : (ℕ → ℝ) → ℝ
  cX4 : (ℕ → ℝ) → ℝ
  cY4 : (ℕ → ℝ) → ℝ
  inv0 : ∀ g t, ∃ N : CMat α, (G0 g).Xm.Φ (tt (I.tv t)) * N = 1
  z0 : ∀ g, (G0 g).Xm.Φ 0 = 1
  hN0 : ∀ d q, (G0 d).X.Φ (I.ent q) * N0 d q = 1
  hW0 : ∀ d q, (G0 d).X.Φ (I.ent q).top = Wn0 d q * (G0 d).X.Φ (I.ent q)
  hN1 : ∀ d q, (G1 d).X.Φ (I.ent q) * N1 d q = 1
  hW1 : ∀ d q, (G1 d).X.Φ (I.ent q).top = Wn1 d q * (G1 d).X.Φ (I.ent q)
  hN2 : ∀ d q, (G2 d).X.Φ (I.ent q) * N2 d q = 1
  hW2 : ∀ d q, (G2 d).X.Φ (I.ent q).top = Wn2 d q * (G2 d).X.Φ (I.ent q)
  hN3 : ∀ d q, (G3 d).X.Φ (I.ent q) * N3 d q = 1
  hW3 : ∀ d q, (G3 d).X.Φ (I.ent q).top = Wn3 d q * (G3 d).X.Φ (I.ent q)
  hN4 : ∀ d q, (G4 d).X.Φ (I.ent q) * N4 d q = 1
  hW4 : ∀ d q, (G4 d).X.Φ (I.ent q).top = Wn4 d q * (G4 d).X.Φ (I.ent q)
  hN5 : ∀ d q, (G5 d).X.Φ (I.ent q) * N5 d q = 1
  hW5 : ∀ d q, (G5 d).X.Φ (I.ent q).top = Wn5 d q * (G5 d).X.Φ (I.ent q)
  hN6 : ∀ d q, (G6 d).X.Φ (I.ent q) * N6 d q = 1
  hW6 : ∀ d q, (G6 d).X.Φ (I.ent q).top = Wn6 d q * (G6 d).X.Φ (I.ent q)
  hN7 : ∀ d q, (G7 d).X.Φ (I.ent q) * N7 d q = 1
  hW7 : ∀ d q, (G7 d).X.Φ (I.ent q).top = Wn7 d q * (G7 d).X.Φ (I.ent q)
  hN8 : ∀ d q, (G8 d).X.Φ (I.ent q) * N8 d q = 1
  hW8 : ∀ d q, (G8 d).X.Φ (I.ent q).top = Wn8 d q * (G8 d).X.Φ (I.ent q)
  /-- the data frames a stage leaves are the data frames the next stage starts from. -/
  x01 : ∀ g t, (G0 g).Xm.Φ 1 = (G1 (r1 t g)).Xm.Φ (tt (I.tv t))
  y01 : ∀ g t, (G0 g).Xm.Φ (1 + tt (I.tv t)) = (G1 (r1 t g)).Xm.Φ 0
  x12 : ∀ g t, (G1 (r1 t g)).Xm.Φ 1 = (G2 (r2 t g)).Xm.Φ (tt (I.tv t))
  y12 : ∀ g t, (G1 (r1 t g)).Xm.Φ (1 + tt (I.tv t)) = (G2 (r2 t g)).Xm.Φ 0
  x23 : ∀ g t, (G2 (r2 t g)).Xm.Φ 1 = (G3 (r3 t g)).Xm.Φ (tt (I.tv t))
  y23 : ∀ g t, (G2 (r2 t g)).Xm.Φ (1 + tt (I.tv t)) = (G3 (r3 t g)).Xm.Φ 0
  x34 : ∀ g t, (G3 (r3 t g)).Xm.Φ 1 = (G4 (r4 t g)).Xm.Φ (tt (I.tv t))
  y34 : ∀ g t, (G3 (r3 t g)).Xm.Φ (1 + tt (I.tv t)) = (G4 (r4 t g)).Xm.Φ 0
  x45 : ∀ g t, (G4 (r4 t g)).Xm.Φ 1 = (G5 (r5 t g)).Xm.Φ (tt (I.tv t))
  y45 : ∀ g t, (G4 (r4 t g)).Xm.Φ (1 + tt (I.tv t)) = (G5 (r5 t g)).Xm.Φ 0
  x56 : ∀ g t, (G5 (r5 t g)).Xm.Φ 1 = (G6 (r6 t g)).Xm.Φ (tt (I.tv t))
  y56 : ∀ g t, (G5 (r5 t g)).Xm.Φ (1 + tt (I.tv t)) = (G6 (r6 t g)).Xm.Φ 0
  x67 : ∀ g t, (G6 (r6 t g)).Xm.Φ 1 = (G7 (r7 t g)).Xm.Φ (tt (I.tv t))
  y67 : ∀ g t, (G6 (r6 t g)).Xm.Φ (1 + tt (I.tv t)) = (G7 (r7 t g)).Xm.Φ 0
  x78 : ∀ g t, (G7 (r7 t g)).Xm.Φ 1 = (G8 (r8 t g)).Xm.Φ (tt (I.tv t))
  y78 : ∀ g t, (G7 (r7 t g)).Xm.Φ (1 + tt (I.tv t)) = (G8 (r8 t g)).Xm.Φ 0
  /-- the banks: start at `1`; before every stage a free adapter; the gauged step; the pad to the kernel. -/
  z0b : ∀ g b, Zb 0 g b = 1
  hP0 : ∀ (ρ : Fin 8) g b, GReach (Zb (9 * ρ.val + 0) g b) (Zp (9 * ρ.val + 0) g b) (fun _ => 0)
  hZ0 : ∀ (ρ : Fin 8) g q, Wn0 g q * Zp (9 * ρ.val + 0) g (use ρ 0 q) = Zb (9 * ρ.val + 1) g (use ρ 0 q)
  hZn0 : ∀ (ρ : Fin 8) g b, (∀ q, use ρ 0 q ≠ b) → Zb (9 * ρ.val + 1) g b = Zp (9 * ρ.val + 0) g b
  hP1 : ∀ (ρ : Fin 8) g b, GReach (Zb (9 * ρ.val + 1) g b) (Zp (9 * ρ.val + 1) g b) (fun _ => 0)
  hZ1 : ∀ (ρ : Fin 8) g q, Wn1 g q * Zp (9 * ρ.val + 1) g (use ρ 1 q) = Zb (9 * ρ.val + 2) g (use ρ 1 q)
  hZn1 : ∀ (ρ : Fin 8) g b, (∀ q, use ρ 1 q ≠ b) → Zb (9 * ρ.val + 2) g b = Zp (9 * ρ.val + 1) g b
  hP2 : ∀ (ρ : Fin 8) g b, GReach (Zb (9 * ρ.val + 2) g b) (Zp (9 * ρ.val + 2) g b) (fun _ => 0)
  hZ2 : ∀ (ρ : Fin 8) g q, Wn2 g q * Zp (9 * ρ.val + 2) g (use ρ 2 q) = Zb (9 * ρ.val + 3) g (use ρ 2 q)
  hZn2 : ∀ (ρ : Fin 8) g b, (∀ q, use ρ 2 q ≠ b) → Zb (9 * ρ.val + 3) g b = Zp (9 * ρ.val + 2) g b
  hP3 : ∀ (ρ : Fin 8) g b, GReach (Zb (9 * ρ.val + 3) g b) (Zp (9 * ρ.val + 3) g b) (fun _ => 0)
  hZ3 : ∀ (ρ : Fin 8) g q, Wn3 g q * Zp (9 * ρ.val + 3) g (use ρ 3 q) = Zb (9 * ρ.val + 4) g (use ρ 3 q)
  hZn3 : ∀ (ρ : Fin 8) g b, (∀ q, use ρ 3 q ≠ b) → Zb (9 * ρ.val + 4) g b = Zp (9 * ρ.val + 3) g b
  hP4 : ∀ (ρ : Fin 8) g b, GReach (Zb (9 * ρ.val + 4) g b) (Zp (9 * ρ.val + 4) g b) (fun _ => 0)
  hZ4 : ∀ (ρ : Fin 8) g q, Wn4 g q * Zp (9 * ρ.val + 4) g (use ρ 4 q) = Zb (9 * ρ.val + 5) g (use ρ 4 q)
  hZn4 : ∀ (ρ : Fin 8) g b, (∀ q, use ρ 4 q ≠ b) → Zb (9 * ρ.val + 5) g b = Zp (9 * ρ.val + 4) g b
  hP5 : ∀ (ρ : Fin 8) g b, GReach (Zb (9 * ρ.val + 5) g b) (Zp (9 * ρ.val + 5) g b) (fun _ => 0)
  hZ5 : ∀ (ρ : Fin 8) g q, Wn5 g q * Zp (9 * ρ.val + 5) g (use ρ 5 q) = Zb (9 * ρ.val + 6) g (use ρ 5 q)
  hZn5 : ∀ (ρ : Fin 8) g b, (∀ q, use ρ 5 q ≠ b) → Zb (9 * ρ.val + 6) g b = Zp (9 * ρ.val + 5) g b
  hP6 : ∀ (ρ : Fin 8) g b, GReach (Zb (9 * ρ.val + 6) g b) (Zp (9 * ρ.val + 6) g b) (fun _ => 0)
  hZ6 : ∀ (ρ : Fin 8) g q, Wn6 g q * Zp (9 * ρ.val + 6) g (use ρ 6 q) = Zb (9 * ρ.val + 7) g (use ρ 6 q)
  hZn6 : ∀ (ρ : Fin 8) g b, (∀ q, use ρ 6 q ≠ b) → Zb (9 * ρ.val + 7) g b = Zp (9 * ρ.val + 6) g b
  hP7 : ∀ (ρ : Fin 8) g b, GReach (Zb (9 * ρ.val + 7) g b) (Zp (9 * ρ.val + 7) g b) (fun _ => 0)
  hZ7 : ∀ (ρ : Fin 8) g q, Wn7 g q * Zp (9 * ρ.val + 7) g (use ρ 7 q) = Zb (9 * ρ.val + 8) g (use ρ 7 q)
  hZn7 : ∀ (ρ : Fin 8) g b, (∀ q, use ρ 7 q ≠ b) → Zb (9 * ρ.val + 8) g b = Zp (9 * ρ.val + 7) g b
  hP8 : ∀ (ρ : Fin 8) g b, GReach (Zb (9 * ρ.val + 8) g b) (Zp (9 * ρ.val + 8) g b) (fun _ => 0)
  hZ8 : ∀ (ρ : Fin 8) g q, Wn8 g q * Zp (9 * ρ.val + 8) g (use ρ 8 q) = Zb (9 * ρ.val + 9) g (use ρ 8 q)
  hZn8 : ∀ (ρ : Fin 8) g b, (∀ q, use ρ 8 q ≠ b) → Zb (9 * ρ.val + 9) g b = Zp (9 * ρ.val + 8) g b
  bpad : ∀ g b, GReach (Zb 72 g b) (kernel α) (fun φ => bcost φ (pad b))
  /-- pair 2, idle until stage 1: ONE block from its start frame to the frame of its twin. -/
  aX2 : ∀ g t, XReach ((G0 g).Xm.Φ (tt (I.tv t))) ((G1 (r1 t g)).Xm.Φ 1) caX2
  aY2 : ∀ g t, XReach ((G0 g).Xm.Φ 0) ((G1 (r1 t g)).Xm.Φ (1 + tt (I.tv t))) caY2
  /-- pair 3, idle until stage 3: ONE block from its start frame to the frame of its twin. -/
  aX3 : ∀ g t, XReach ((G0 g).Xm.Φ (tt (I.tv t))) ((G3 (r3 t g)).Xm.Φ 1) caX3
  aY3 : ∀ g t, XReach ((G0 g).Xm.Φ 0) ((G3 (r3 t g)).Xm.Φ (1 + tt (I.tv t))) caY3
  /-- pair 4, idle until stage 5: ONE block from its start frame to the frame of its twin. -/
  aX4 : ∀ g t, XReach ((G0 g).Xm.Φ (tt (I.tv t))) ((G5 (r5 t g)).Xm.Φ 1) caX4
  aY4 : ∀ g t, XReach ((G0 g).Xm.Φ 0) ((G5 (r5 t g)).Xm.Φ (1 + tt (I.tv t))) caY4
  /-- pair 1 after stage 2: ONE final block. -/
  fX1 : ∀ g t, XReach ((G2 (r2 t g)).Xm.Φ 1) (kernel α) cX1
  fY1 : ∀ g t, XReach ((G2 (r2 t g)).Xm.Φ (1 + tt (I.tv t))) (YF g t) cY1
  /-- pair 2 after stage 4: ONE final block. -/
  fX2 : ∀ g t, XReach ((G4 (r4 t g)).Xm.Φ 1) (kernel α) cX2
  fY2 : ∀ g t, XReach ((G4 (r4 t g)).Xm.Φ (1 + tt (I.tv t))) (YF g t) cY2
  /-- pair 3 after stage 6: ONE final block. -/
  fX3 : ∀ g t, XReach ((G6 (r6 t g)).Xm.Φ 1) (kernel α) cX3
  fY3 : ∀ g t, XReach ((G6 (r6 t g)).Xm.Φ (1 + tt (I.tv t))) (YF g t) cY3
  /-- pair 4 after stage 8: ONE final block. -/
  fX4 : ∀ g t, XReach ((G8 (r8 t g)).Xm.Φ 1) (kernel α) cX4
  fY4 : ∀ g t, XReach ((G8 (r8 t g)).Xm.Φ (1 + tt (I.tv t))) (YF g t) cY4
  term : ∀ g t, kernel α * (G0 g).Xm.Φ (tt (I.tv t)) = shift (u g t) * YF g t

section Net
variable {H T Sl C α Γ : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C] [Fintype α] [DecidableEq α]
  [Fintype Γ] [DecidableEq Γ]
variable {nb : ℕ} (N : G401 H T Sl C α Γ nb)

/-- price of the blocks of ONE run per element of `Γ`: 9 invocations and the idle climbs of the data of
every class of its replica. -/
def G401.runUnit (φ : ℕ → ℝ) : ℝ :=
  9 * N.I.cost φ + (Fintype.card T : ℝ) * ((N.caX2 φ + N.caY2 φ) + 2 * bcost φ (Fintype.card H - 1)
      + ((N.caX3 φ + N.caY3 φ) + 2 * bcost φ (Fintype.card H - 1))
      + ((N.caX4 φ + N.caY4 φ) + 2 * bcost φ (Fintype.card H - 1))
      + (N.cX1 φ + N.cY1 φ)
      + (N.cX2 φ + N.cY2 φ)
      + (N.cX3 φ + N.cY3 φ)
      + (N.cX4 φ + N.cY4 φ))

/-- price of the blocks of one unit (one element of `Γ`): 8 runs and the padding blocks of the banks. -/
def G401.unit (φ : ℕ → ℝ) : ℝ :=
  8 * N.runUnit φ + ∑ b, bcost φ (N.pad b)

/-! data frames of the class `(g,t)`: `xi l`, `yi l` at the START of stage `l`; `xo l`, `yo l` at the
END of stage `l` (only where no next stage follows on that pair). -/
def G401.xi0 (g : Γ) (t : T) : CMat α := (N.G0 g).Xm.Φ (tt (N.I.tv t))
def G401.yi0 (g : Γ) (t : T) : CMat α := (N.G0 g).Xm.Φ 0
def G401.xi1 (g : Γ) (t : T) : CMat α := (N.G1 (N.r1 t g)).Xm.Φ (tt (N.I.tv t))
def G401.yi1 (g : Γ) (t : T) : CMat α := (N.G1 (N.r1 t g)).Xm.Φ 0
def G401.xi2 (g : Γ) (t : T) : CMat α := (N.G2 (N.r2 t g)).Xm.Φ (tt (N.I.tv t))
def G401.yi2 (g : Γ) (t : T) : CMat α := (N.G2 (N.r2 t g)).Xm.Φ 0
def G401.xi3 (g : Γ) (t : T) : CMat α := (N.G3 (N.r3 t g)).Xm.Φ (tt (N.I.tv t))
def G401.yi3 (g : Γ) (t : T) : CMat α := (N.G3 (N.r3 t g)).Xm.Φ 0
def G401.xi4 (g : Γ) (t : T) : CMat α := (N.G4 (N.r4 t g)).Xm.Φ (tt (N.I.tv t))
def G401.yi4 (g : Γ) (t : T) : CMat α := (N.G4 (N.r4 t g)).Xm.Φ 0
def G401.xi5 (g : Γ) (t : T) : CMat α := (N.G5 (N.r5 t g)).Xm.Φ (tt (N.I.tv t))
def G401.yi5 (g : Γ) (t : T) : CMat α := (N.G5 (N.r5 t g)).Xm.Φ 0
def G401.xi6 (g : Γ) (t : T) : CMat α := (N.G6 (N.r6 t g)).Xm.Φ (tt (N.I.tv t))
def G401.yi6 (g : Γ) (t : T) : CMat α := (N.G6 (N.r6 t g)).Xm.Φ 0
def G401.xi7 (g : Γ) (t : T) : CMat α := (N.G7 (N.r7 t g)).Xm.Φ (tt (N.I.tv t))
def G401.yi7 (g : Γ) (t : T) : CMat α := (N.G7 (N.r7 t g)).Xm.Φ 0
def G401.xi8 (g : Γ) (t : T) : CMat α := (N.G8 (N.r8 t g)).Xm.Φ (tt (N.I.tv t))
def G401.yi8 (g : Γ) (t : T) : CMat α := (N.G8 (N.r8 t g)).Xm.Φ 0
def G401.xo2 (g : Γ) (t : T) : CMat α := (N.G2 (N.r2 t g)).Xm.Φ 1
def G401.yo2 (g : Γ) (t : T) : CMat α := (N.G2 (N.r2 t g)).Xm.Φ (1 + tt (N.I.tv t))
def G401.xo4 (g : Γ) (t : T) : CMat α := (N.G4 (N.r4 t g)).Xm.Φ 1
def G401.yo4 (g : Γ) (t : T) : CMat α := (N.G4 (N.r4 t g)).Xm.Φ (1 + tt (N.I.tv t))
def G401.xo6 (g : Γ) (t : T) : CMat α := (N.G6 (N.r6 t g)).Xm.Φ 1
def G401.yo6 (g : Γ) (t : T) : CMat α := (N.G6 (N.r6 t g)).Xm.Φ (1 + tt (N.I.tv t))
def G401.xo8 (g : Γ) (t : T) : CMat α := (N.G8 (N.r8 t g)).Xm.Φ 1
def G401.yo8 (g : Γ) (t : T) : CMat α := (N.G8 (N.r8 t g)).Xm.Φ (1 + tt (N.I.tv t))

/-- the data of a replica before its run and after it. -/
def G401.InitD : BDat4 Γ T → CMat α := mkD4 N.xi0 N.yi0 N.xi0 N.yi0 N.xi0 N.yi0 N.xi0 N.yi0
def G401.FinD : BDat4 Γ T → CMat α := mkD4 (fun _ _ => kernel α) N.YF (fun _ _ => kernel α) N.YF (fun _ _ => kernel α) N.YF (fun _ _ => kernel α) N.YF

/-- frames of a run (on the roles of the run) after each step. -/
def G401.S0 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xi0 N.yi0 N.xi0 N.yi0 N.xi0 N.yi0 N.xi0 N.yi0 (fun g b => N.Zb (9 * ρ.val + 0) g b) (cOne Γ C α)
def G401.S1 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xi0 N.yi0 N.xi0 N.yi0 N.xi0 N.yi0 N.xi0 N.yi0 (fun g b => N.Zp (9 * ρ.val + 0) g b) (cOne Γ C α)
def G401.S2 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xi1 N.yi1 N.xi0 N.yi0 N.xi0 N.yi0 N.xi0 N.yi0 (fun g b => N.Zb (9 * ρ.val + 1) g b) (cOne Γ C α)
def G401.S3 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xi1 N.yi1 N.xi0 N.yi0 N.xi0 N.yi0 N.xi0 N.yi0 (fun g b => N.Zp (9 * ρ.val + 1) g b) (cOne Γ C α)
def G401.S4 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xi2 N.yi2 N.xi0 N.yi0 N.xi0 N.yi0 N.xi0 N.yi0 (fun g b => N.Zb (9 * ρ.val + 2) g b) (cOne Γ C α)
def G401.S5 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xi2 N.yi2 N.xi2 N.yi2 N.xi0 N.yi0 N.xi0 N.yi0 (fun g b => N.Zb (9 * ρ.val + 2) g b) (cOne Γ C α)
def G401.S6 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xi2 N.yi2 N.xi2 N.yi2 N.xi0 N.yi0 N.xi0 N.yi0 (fun g b => N.Zp (9 * ρ.val + 2) g b) (cOne Γ C α)
def G401.S7 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xo2 N.yo2 N.xi2 N.yi2 N.xi0 N.yi0 N.xi0 N.yi0 (fun g b => N.Zb (9 * ρ.val + 3) g b) (cOne Γ C α)
def G401.S8 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xo2 N.yo2 N.xi3 N.yi3 N.xi0 N.yi0 N.xi0 N.yi0 (fun g b => N.Zb (9 * ρ.val + 3) g b) (cOne Γ C α)
def G401.S9 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xo2 N.yo2 N.xi3 N.yi3 N.xi0 N.yi0 N.xi0 N.yi0 (fun g b => N.Zp (9 * ρ.val + 3) g b) (cOne Γ C α)
def G401.S10 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xo2 N.yo2 N.xi4 N.yi4 N.xi0 N.yi0 N.xi0 N.yi0 (fun g b => N.Zb (9 * ρ.val + 4) g b) (cOne Γ C α)
def G401.S11 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xo2 N.yo2 N.xi4 N.yi4 N.xi4 N.yi4 N.xi0 N.yi0 (fun g b => N.Zb (9 * ρ.val + 4) g b) (cOne Γ C α)
def G401.S12 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xo2 N.yo2 N.xi4 N.yi4 N.xi4 N.yi4 N.xi0 N.yi0 (fun g b => N.Zp (9 * ρ.val + 4) g b) (cOne Γ C α)
def G401.S13 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xo2 N.yo2 N.xo4 N.yo4 N.xi4 N.yi4 N.xi0 N.yi0 (fun g b => N.Zb (9 * ρ.val + 5) g b) (cOne Γ C α)
def G401.S14 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xo2 N.yo2 N.xo4 N.yo4 N.xi5 N.yi5 N.xi0 N.yi0 (fun g b => N.Zb (9 * ρ.val + 5) g b) (cOne Γ C α)
def G401.S15 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xo2 N.yo2 N.xo4 N.yo4 N.xi5 N.yi5 N.xi0 N.yi0 (fun g b => N.Zp (9 * ρ.val + 5) g b) (cOne Γ C α)
def G401.S16 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xo2 N.yo2 N.xo4 N.yo4 N.xi6 N.yi6 N.xi0 N.yi0 (fun g b => N.Zb (9 * ρ.val + 6) g b) (cOne Γ C α)
def G401.S17 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xo2 N.yo2 N.xo4 N.yo4 N.xi6 N.yi6 N.xi6 N.yi6 (fun g b => N.Zb (9 * ρ.val + 6) g b) (cOne Γ C α)
def G401.S18 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xo2 N.yo2 N.xo4 N.yo4 N.xi6 N.yi6 N.xi6 N.yi6 (fun g b => N.Zp (9 * ρ.val + 6) g b) (cOne Γ C α)
def G401.S19 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xo2 N.yo2 N.xo4 N.yo4 N.xo6 N.yo6 N.xi6 N.yi6 (fun g b => N.Zb (9 * ρ.val + 7) g b) (cOne Γ C α)
def G401.S20 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xo2 N.yo2 N.xo4 N.yo4 N.xo6 N.yo6 N.xi7 N.yi7 (fun g b => N.Zb (9 * ρ.val + 7) g b) (cOne Γ C α)
def G401.S21 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xo2 N.yo2 N.xo4 N.yo4 N.xo6 N.yo6 N.xi7 N.yi7 (fun g b => N.Zp (9 * ρ.val + 7) g b) (cOne Γ C α)
def G401.S22 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xo2 N.yo2 N.xo4 N.yo4 N.xo6 N.yo6 N.xi8 N.yi8 (fun g b => N.Zb (9 * ρ.val + 8) g b) (cOne Γ C α)
def G401.S23 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xo2 N.yo2 N.xo4 N.yo4 N.xo6 N.yo6 N.xi8 N.yi8 (fun g b => N.Zp (9 * ρ.val + 8) g b) (cOne Γ C α)
def G401.S24 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xo2 N.yo2 N.xo4 N.yo4 N.xo6 N.yo6 N.xo8 N.yo8 (fun g b => N.Zb (9 * ρ.val + 9) g b) (cOne Γ C α)
def G401.S25 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 (fun _ _ => kernel α) N.YF (fun _ _ => kernel α) N.YF (fun _ _ => kernel α) N.YF (fun _ _ => kernel α) N.YF (fun g b => N.Zb (9 * ρ.val + 9) g b) (cOne Γ C α)

/-- frames of all roles at the start of run `k` (`k = 8`: after the last run). -/
def G401.Sfull (k : Fin 9) : BRole401 Γ T nb C → CMat α :=
  mk401 (fun ρ' d => if ρ'.val < k.val then N.FinD d else N.InitD d) (fun g b => N.Zb (9 * k.val) g b) (cOne Γ C α)

/-- frames of all roles after the padding climbs. -/
def G401.Sfin : BRole401 Γ T nb C → CMat α :=
  mk401 (fun _ d => N.FinD d) (fun _ _ => kernel α) (cOne Γ C α)

end Net
end
end GX
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.GX.G401.unit

end
-- bos_merge: end Submission.Work.Bridge401.GNetDef

-- bos_merge: begin Submission.Work.Bridge401.GNetStage
section

/-!
# (key: bridge-401) The stages, idle climbs and gate layers of one run of the compressed nine-stage word

Credits: the entrance gauges and the residual banks are Dugongue's (CrocSwap/integer-mult-bounds PR #401); the bank
patterns are Lydakis's (#275); the compressed nine-stage layout is jacklightChen's (#377); the bridged word B_K is
DaysSky's (#363); B_2, the engine, the stage geometry and the E8 unit are Jacob Sussman's (wht-power-saving-lean,
Apache-2.0).  Written by w-newsums/gen401/gen401.py (from gen377.py).  Copy of Work/GCert/Chain/NetStage.lean (via genk), generic in the run `ρ`.  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace OAI
namespace PowerSaving
namespace GX
open Binary Matrix Finset RAM SS CB RF BR GF
noncomputable section

section Net
variable {H T Sl C α Γ : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C] [Fintype α] [DecidableEq α]
  [Fintype Γ] [DecidableEq Γ]
variable {nb : ℕ} (N : G401 H T Sl C α Γ nb)

/-- the free bank adapters before stage 0 of run `ρ` (`bank_adapt`): every bank from `Zb` to `Zp`. -/
lemma G401.adapt0 (ρ : Fin 8) :
    GRoute (N.S0 ρ) (N.S1 ρ) id (fun _ => 0) := by
  have H1 := GRoute.reach_all (N.S0 ρ) (N.S1 ρ) (fun _ _ => 0) (by
      rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact N.hP0 ρ g b
      · exact GReach.refl _)
  exact H1.cast (fun φ => by simp)

/-- stage 0 of run `ρ`: forward on pair 1; the slot `q` of `g` on the bank `(g, use ρ 0 q)`. -/
lemma G401.stage0 (ρ : Fin 8) :
    GRoute (N.S1 ρ) (N.S2 ρ) (liftQ0 (Γ := Γ) (T := T) (C := C) (N.use ρ 0) GF)
      (fun φ => (Fintype.card Γ : ℝ) * N.I.cost φ) := by
  have h := gistageE_fwd N.I (bid Γ T) N.G0 N.N0 N.Wn0 N.hN0 N.hW0
    (fun g q => N.Zp (9 * ρ.val + 0) g (N.use ρ 0 q)) (cOne Γ C α) (cOne Γ C α)
  have h' : GRoute (bIn N.I.tv (bid Γ T) (fun d => (N.G0 d).Xm)
        (fun g q => N.Zp (9 * ρ.val + 0) g (N.use ρ 0 q)) (cOne Γ C α))
      (mkS N.xi1 N.yi1 (fun g q => N.Zb (9 * ρ.val + 1) g (N.use ρ 0 q)) (cOne Γ C α)) GF
      (fun φ => (Fintype.card Γ : ℝ) * N.I.cost φ) := by
    have e : bOut N.I.tv (bid Γ T) (fun d => (N.G0 d).Xm)
        (fun g q => N.Wn0 g q * N.Zp (9 * ρ.val + 0) g (N.use ρ 0 q)) (cOne Γ C α)
        = mkS N.xi1 N.yi1 (fun g q => N.Zb (9 * ρ.val + 1) g (N.use ρ 0 q)) (cOne Γ C α) := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · exact N.x01 g t
      · exact N.y01 g t
      · exact N.hZ0 ρ g q
      · rfl
    rw [← e]
    exact h
  exact gbliftQ0 (N.use ρ 0) (N.hinj ρ 0) N.xi0 N.yi0 N.xi0 N.yi0 N.xi0 N.yi0 (fun g b => N.Zp (9 * ρ.val + 0) g b)
    (fun g b => N.Zb (9 * ρ.val + 1) g b) h'
    (fun g q => rfl) (fun g q => rfl) (fun g b hb => (N.hZn0 ρ g b hb).symm) (fun _ _ _ => rfl)

/-- the free bank adapters before stage 1 of run `ρ` (`bank_adapt`): every bank from `Zb` to `Zp`. -/
lemma G401.adapt1 (ρ : Fin 8) :
    GRoute (N.S2 ρ) (N.S3 ρ) id (fun _ => 0) := by
  have H1 := GRoute.reach_all (N.S2 ρ) (N.S3 ρ) (fun _ _ => 0) (by
      rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact N.hP1 ρ g b
      · exact GReach.refl _)
  exact H1.cast (fun φ => by simp)

/-- stage 1 of run `ρ`: backward on pair 1; the slot `q` of `g` on the bank `(g, use ρ 1 q)`. -/
lemma G401.stage1 (ρ : Fin 8) :
    GRoute (N.S3 ρ) (N.S4 ρ) (liftQ1 (Γ := Γ) (T := T) (C := C) (N.use ρ 1) GB)
      (fun φ => (Fintype.card Γ : ℝ) * N.I.cost φ) := by
  have h := gistageE_bwd N.I N.r1 N.G1 N.N1 N.Wn1 N.hN1 N.hW1
    (fun g q => N.Zp (9 * ρ.val + 1) g (N.use ρ 1 q)) (cOne Γ C α) (cOne Γ C α)
  have h' : GRoute (bIn N.I.tv N.r1 (fun d => (N.G1 d).Xm)
        (fun g q => N.Zp (9 * ρ.val + 1) g (N.use ρ 1 q)) (cOne Γ C α))
      (mkS N.xi2 N.yi2 (fun g q => N.Zb (9 * ρ.val + 2) g (N.use ρ 1 q)) (cOne Γ C α)) GB
      (fun φ => (Fintype.card Γ : ℝ) * N.I.cost φ) := by
    have e : bOut N.I.tv N.r1 (fun d => (N.G1 d).Xm)
        (fun g q => N.Wn1 g q * N.Zp (9 * ρ.val + 1) g (N.use ρ 1 q)) (cOne Γ C α)
        = mkS N.xi2 N.yi2 (fun g q => N.Zb (9 * ρ.val + 2) g (N.use ρ 1 q)) (cOne Γ C α) := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · exact N.x12 g t
      · exact N.y12 g t
      · exact N.hZ1 ρ g q
      · rfl
    rw [← e]
    exact h
  exact gbliftQ1 (N.use ρ 1) (N.hinj ρ 1) N.xi0 N.yi0 N.xi0 N.yi0 N.xi0 N.yi0 (fun g b => N.Zp (9 * ρ.val + 1) g b)
    (fun g b => N.Zb (9 * ρ.val + 2) g b) h'
    (fun g q => rfl) (fun g q => rfl) (fun g b hb => (N.hZn1 ρ g b hb).symm) (fun _ _ _ => rfl)

/-- first idle climb of pair 2 (ONE block per role), to the frames of pair 1 after stage 1. -/
lemma G401.climbA2 (ρ : Fin 8) :
    XRoute (N.S4 ρ) (N.S5 ρ) id (fun φ => (Fintype.card Γ : ℝ) *
      ((Fintype.card T : ℝ) * (N.caX2 φ + N.caY2 φ))) := by
  have H1 := XRoute.reach_all (N.S4 ρ) (N.S5 ρ)
    (mkR4 (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ => N.caX2) (fun _ _ => N.caY2) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)) (by
      rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
      · exact XReach.refl _
      · exact XReach.refl _
      · show XReach ((N.G0 g).Xm.Φ (tt (N.I.tv t))) ((N.G2 (N.r2 t g)).Xm.Φ (tt (N.I.tv t))) N.caX2
        rw [← N.x12 g t]
        exact N.aX2 g t
      · show XReach ((N.G0 g).Xm.Φ 0) ((N.G2 (N.r2 t g)).Xm.Φ 0) N.caY2
        rw [← N.y12 g t]
        exact N.aY2 g t
      · exact XReach.refl _
      · exact XReach.refl _
      · exact XReach.refl _
      · exact XReach.refl _
      · exact XReach.refl _
      · exact XReach.refl _)
  refine H1.cast (fun φ => ?_)
  simp_rw [mkR4_map (fun c : (ℕ → ℝ) → ℝ => c φ)]
  rw [sum_mkR4]
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_zero, add_zero, zero_add]
  ring

/-- gate layer A of pair 2 in run `ρ`: twins have equal frames. -/
lemma G401.gateA2 (ρ : Fin 8) : XRoute (N.S5 ρ) (N.S5 ρ) (gscQ pABQ_2 kAQ_2) (fun _ => 0) := by
  refine gateP pABQ_2 kAQ_2 (N.S5 ρ) ?_
  rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩) hk
  · rfl
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · rfl
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim

/-- the free bank adapters before stage 2 of run `ρ` (`bank_adapt`): every bank from `Zb` to `Zp`. -/
lemma G401.adapt2 (ρ : Fin 8) :
    GRoute (N.S5 ρ) (N.S6 ρ) id (fun _ => 0) := by
  have H1 := GRoute.reach_all (N.S5 ρ) (N.S6 ρ) (fun _ _ => 0) (by
      rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact N.hP2 ρ g b
      · exact GReach.refl _)
  exact H1.cast (fun φ => by simp)

/-- stage 2 of run `ρ`: forward on pair 1; the slot `q` of `g` on the bank `(g, use ρ 2 q)`. -/
lemma G401.stage2 (ρ : Fin 8) :
    GRoute (N.S6 ρ) (N.S7 ρ) (liftQ2 (Γ := Γ) (T := T) (C := C) (N.use ρ 2) GF)
      (fun φ => (Fintype.card Γ : ℝ) * N.I.cost φ) := by
  have h := gistageE_fwd N.I N.r2 N.G2 N.N2 N.Wn2 N.hN2 N.hW2
    (fun g q => N.Zp (9 * ρ.val + 2) g (N.use ρ 2 q)) (cOne Γ C α) (cOne Γ C α)
  have h' : GRoute (bIn N.I.tv N.r2 (fun d => (N.G2 d).Xm)
        (fun g q => N.Zp (9 * ρ.val + 2) g (N.use ρ 2 q)) (cOne Γ C α))
      (mkS N.xo2 N.yo2 (fun g q => N.Zb (9 * ρ.val + 3) g (N.use ρ 2 q)) (cOne Γ C α)) GF
      (fun φ => (Fintype.card Γ : ℝ) * N.I.cost φ) := by
    have e : bOut N.I.tv N.r2 (fun d => (N.G2 d).Xm)
        (fun g q => N.Wn2 g q * N.Zp (9 * ρ.val + 2) g (N.use ρ 2 q)) (cOne Γ C α)
        = mkS N.xo2 N.yo2 (fun g q => N.Zb (9 * ρ.val + 3) g (N.use ρ 2 q)) (cOne Γ C α) := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · rfl
      · rfl
      · exact N.hZ2 ρ g q
      · rfl
    rw [← e]
    exact h
  exact gbliftQ2 (N.use ρ 2) (N.hinj ρ 2) N.xi2 N.yi2 N.xi0 N.yi0 N.xi0 N.yi0 (fun g b => N.Zp (9 * ρ.val + 2) g b)
    (fun g b => N.Zb (9 * ρ.val + 3) g b) h'
    (fun g q => rfl) (fun g q => rfl) (fun g b hb => (N.hZn2 ρ g b hb).symm) (fun _ _ _ => rfl)

/-- second idle climb of pair 2: the window of stage 2, ONE block of rank `card H - 1` per role. -/
lemma G401.climbB2 (ρ : Fin 8) :
    XRoute (N.S7 ρ) (N.S8 ρ) id (fun φ => (Fintype.card Γ : ℝ) *
      ((Fintype.card T : ℝ) * (2 * bcost φ (Fintype.card H - 1)))) := by
  have H1 := XRoute.reach_all (N.S7 ρ) (N.S8 ρ)
    (mkR4 (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ => (fun φ => bcost φ (Fintype.card H - 1))) (fun _ _ => (fun φ => bcost φ (Fintype.card H - 1))) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)) (by
      rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
      · exact XReach.refl _
      · exact XReach.refl _
      · show XReach ((N.G2 (N.r2 t g)).Xm.Φ (tt (N.I.tv t))) ((N.G3 (N.r3 t g)).Xm.Φ (tt (N.I.tv t)))
          (fun φ => bcost φ (Fintype.card H - 1))
        rw [← N.x23 g t]
        exact GInvE.climbX N.I (N.G2 (N.r2 t g)).Xm t
      · show XReach ((N.G2 (N.r2 t g)).Xm.Φ 0) ((N.G3 (N.r3 t g)).Xm.Φ 0)
          (fun φ => bcost φ (Fintype.card H - 1))
        rw [← N.y23 g t]
        exact GInvE.climbY N.I (N.G2 (N.r2 t g)).Xm t
      · exact XReach.refl _
      · exact XReach.refl _
      · exact XReach.refl _
      · exact XReach.refl _
      · exact XReach.refl _
      · exact XReach.refl _)
  refine H1.cast (fun φ => ?_)
  simp_rw [mkR4_map (fun c : (ℕ → ℝ) → ℝ => c φ)]
  rw [sum_mkR4]
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_zero, add_zero, zero_add]
  ring

/-- gate layer B of pair 2 in run `ρ`: twins have equal frames. -/
lemma G401.gateB2 (ρ : Fin 8) : XRoute (N.S8 ρ) (N.S8 ρ) (gscQ pABQ_2 kBQ_2) (fun _ => 0) := by
  refine gateP pABQ_2 kBQ_2 (N.S8 ρ) ?_
  rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩) hk
  · exact N.x23 g t
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (N.y23 g t).symm
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim

/-- the free bank adapters before stage 3 of run `ρ` (`bank_adapt`): every bank from `Zb` to `Zp`. -/
lemma G401.adapt3 (ρ : Fin 8) :
    GRoute (N.S8 ρ) (N.S9 ρ) id (fun _ => 0) := by
  have H1 := GRoute.reach_all (N.S8 ρ) (N.S9 ρ) (fun _ _ => 0) (by
      rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact N.hP3 ρ g b
      · exact GReach.refl _)
  exact H1.cast (fun φ => by simp)

/-- stage 3 of run `ρ`: backward on pair 2; the slot `q` of `g` on the bank `(g, use ρ 3 q)`. -/
lemma G401.stage3 (ρ : Fin 8) :
    GRoute (N.S9 ρ) (N.S10 ρ) (liftQ3 (Γ := Γ) (T := T) (C := C) (N.use ρ 3) GB)
      (fun φ => (Fintype.card Γ : ℝ) * N.I.cost φ) := by
  have h := gistageE_bwd N.I N.r3 N.G3 N.N3 N.Wn3 N.hN3 N.hW3
    (fun g q => N.Zp (9 * ρ.val + 3) g (N.use ρ 3 q)) (cOne Γ C α) (cOne Γ C α)
  have h' : GRoute (bIn N.I.tv N.r3 (fun d => (N.G3 d).Xm)
        (fun g q => N.Zp (9 * ρ.val + 3) g (N.use ρ 3 q)) (cOne Γ C α))
      (mkS N.xi4 N.yi4 (fun g q => N.Zb (9 * ρ.val + 4) g (N.use ρ 3 q)) (cOne Γ C α)) GB
      (fun φ => (Fintype.card Γ : ℝ) * N.I.cost φ) := by
    have e : bOut N.I.tv N.r3 (fun d => (N.G3 d).Xm)
        (fun g q => N.Wn3 g q * N.Zp (9 * ρ.val + 3) g (N.use ρ 3 q)) (cOne Γ C α)
        = mkS N.xi4 N.yi4 (fun g q => N.Zb (9 * ρ.val + 4) g (N.use ρ 3 q)) (cOne Γ C α) := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · exact N.x34 g t
      · exact N.y34 g t
      · exact N.hZ3 ρ g q
      · rfl
    rw [← e]
    exact h
  exact gbliftQ3 (N.use ρ 3) (N.hinj ρ 3) N.xo2 N.yo2 N.xi0 N.yi0 N.xi0 N.yi0 (fun g b => N.Zp (9 * ρ.val + 3) g b)
    (fun g b => N.Zb (9 * ρ.val + 4) g b) h'
    (fun g q => rfl) (fun g q => rfl) (fun g b hb => (N.hZn3 ρ g b hb).symm) (fun _ _ _ => rfl)

/-- first idle climb of pair 3 (ONE block per role), to the frames of pair 2 after stage 3. -/
lemma G401.climbA3 (ρ : Fin 8) :
    XRoute (N.S10 ρ) (N.S11 ρ) id (fun φ => (Fintype.card Γ : ℝ) *
      ((Fintype.card T : ℝ) * (N.caX3 φ + N.caY3 φ))) := by
  have H1 := XRoute.reach_all (N.S10 ρ) (N.S11 ρ)
    (mkR4 (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ => N.caX3) (fun _ _ => N.caY3) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)) (by
      rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
      · exact XReach.refl _
      · exact XReach.refl _
      · exact XReach.refl _
      · exact XReach.refl _
      · show XReach ((N.G0 g).Xm.Φ (tt (N.I.tv t))) ((N.G4 (N.r4 t g)).Xm.Φ (tt (N.I.tv t))) N.caX3
        rw [← N.x34 g t]
        exact N.aX3 g t
      · show XReach ((N.G0 g).Xm.Φ 0) ((N.G4 (N.r4 t g)).Xm.Φ 0) N.caY3
        rw [← N.y34 g t]
        exact N.aY3 g t
      · exact XReach.refl _
      · exact XReach.refl _
      · exact XReach.refl _
      · exact XReach.refl _)
  refine H1.cast (fun φ => ?_)
  simp_rw [mkR4_map (fun c : (ℕ → ℝ) → ℝ => c φ)]
  rw [sum_mkR4]
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_zero, add_zero, zero_add]
  ring

/-- gate layer A of pair 3 in run `ρ`: twins have equal frames. -/
lemma G401.gateA3 (ρ : Fin 8) : XRoute (N.S11 ρ) (N.S11 ρ) (gscQ pABQ_3 kAQ_3) (fun _ => 0) := by
  refine gateP pABQ_3 kAQ_3 (N.S11 ρ) ?_
  rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩) hk
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · rfl
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · rfl
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim

/-- the free bank adapters before stage 4 of run `ρ` (`bank_adapt`): every bank from `Zb` to `Zp`. -/
lemma G401.adapt4 (ρ : Fin 8) :
    GRoute (N.S11 ρ) (N.S12 ρ) id (fun _ => 0) := by
  have H1 := GRoute.reach_all (N.S11 ρ) (N.S12 ρ) (fun _ _ => 0) (by
      rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact N.hP4 ρ g b
      · exact GReach.refl _)
  exact H1.cast (fun φ => by simp)

/-- stage 4 of run `ρ`: forward on pair 2; the slot `q` of `g` on the bank `(g, use ρ 4 q)`. -/
lemma G401.stage4 (ρ : Fin 8) :
    GRoute (N.S12 ρ) (N.S13 ρ) (liftQ4 (Γ := Γ) (T := T) (C := C) (N.use ρ 4) GF)
      (fun φ => (Fintype.card Γ : ℝ) * N.I.cost φ) := by
  have h := gistageE_fwd N.I N.r4 N.G4 N.N4 N.Wn4 N.hN4 N.hW4
    (fun g q => N.Zp (9 * ρ.val + 4) g (N.use ρ 4 q)) (cOne Γ C α) (cOne Γ C α)
  have h' : GRoute (bIn N.I.tv N.r4 (fun d => (N.G4 d).Xm)
        (fun g q => N.Zp (9 * ρ.val + 4) g (N.use ρ 4 q)) (cOne Γ C α))
      (mkS N.xo4 N.yo4 (fun g q => N.Zb (9 * ρ.val + 5) g (N.use ρ 4 q)) (cOne Γ C α)) GF
      (fun φ => (Fintype.card Γ : ℝ) * N.I.cost φ) := by
    have e : bOut N.I.tv N.r4 (fun d => (N.G4 d).Xm)
        (fun g q => N.Wn4 g q * N.Zp (9 * ρ.val + 4) g (N.use ρ 4 q)) (cOne Γ C α)
        = mkS N.xo4 N.yo4 (fun g q => N.Zb (9 * ρ.val + 5) g (N.use ρ 4 q)) (cOne Γ C α) := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · rfl
      · rfl
      · exact N.hZ4 ρ g q
      · rfl
    rw [← e]
    exact h
  exact gbliftQ4 (N.use ρ 4) (N.hinj ρ 4) N.xo2 N.yo2 N.xi4 N.yi4 N.xi0 N.yi0 (fun g b => N.Zp (9 * ρ.val + 4) g b)
    (fun g b => N.Zb (9 * ρ.val + 5) g b) h'
    (fun g q => rfl) (fun g q => rfl) (fun g b hb => (N.hZn4 ρ g b hb).symm) (fun _ _ _ => rfl)

/-- second idle climb of pair 3: the window of stage 4, ONE block of rank `card H - 1` per role. -/
lemma G401.climbB3 (ρ : Fin 8) :
    XRoute (N.S13 ρ) (N.S14 ρ) id (fun φ => (Fintype.card Γ : ℝ) *
      ((Fintype.card T : ℝ) * (2 * bcost φ (Fintype.card H - 1)))) := by
  have H1 := XRoute.reach_all (N.S13 ρ) (N.S14 ρ)
    (mkR4 (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ => (fun φ => bcost φ (Fintype.card H - 1))) (fun _ _ => (fun φ => bcost φ (Fintype.card H - 1))) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)) (by
      rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
      · exact XReach.refl _
      · exact XReach.refl _
      · exact XReach.refl _
      · exact XReach.refl _
      · show XReach ((N.G4 (N.r4 t g)).Xm.Φ (tt (N.I.tv t))) ((N.G5 (N.r5 t g)).Xm.Φ (tt (N.I.tv t)))
          (fun φ => bcost φ (Fintype.card H - 1))
        rw [← N.x45 g t]
        exact GInvE.climbX N.I (N.G4 (N.r4 t g)).Xm t
      · show XReach ((N.G4 (N.r4 t g)).Xm.Φ 0) ((N.G5 (N.r5 t g)).Xm.Φ 0)
          (fun φ => bcost φ (Fintype.card H - 1))
        rw [← N.y45 g t]
        exact GInvE.climbY N.I (N.G4 (N.r4 t g)).Xm t
      · exact XReach.refl _
      · exact XReach.refl _
      · exact XReach.refl _
      · exact XReach.refl _)
  refine H1.cast (fun φ => ?_)
  simp_rw [mkR4_map (fun c : (ℕ → ℝ) → ℝ => c φ)]
  rw [sum_mkR4]
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_zero, add_zero, zero_add]
  ring

/-- gate layer B of pair 3 in run `ρ`: twins have equal frames. -/
lemma G401.gateB3 (ρ : Fin 8) : XRoute (N.S14 ρ) (N.S14 ρ) (gscQ pABQ_3 kBQ_3) (fun _ => 0) := by
  refine gateP pABQ_3 kBQ_3 (N.S14 ρ) ?_
  rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩) hk
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact N.x45 g t
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (N.y45 g t).symm
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim

/-- the free bank adapters before stage 5 of run `ρ` (`bank_adapt`): every bank from `Zb` to `Zp`. -/
lemma G401.adapt5 (ρ : Fin 8) :
    GRoute (N.S14 ρ) (N.S15 ρ) id (fun _ => 0) := by
  have H1 := GRoute.reach_all (N.S14 ρ) (N.S15 ρ) (fun _ _ => 0) (by
      rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact N.hP5 ρ g b
      · exact GReach.refl _)
  exact H1.cast (fun φ => by simp)

/-- stage 5 of run `ρ`: backward on pair 3; the slot `q` of `g` on the bank `(g, use ρ 5 q)`. -/
lemma G401.stage5 (ρ : Fin 8) :
    GRoute (N.S15 ρ) (N.S16 ρ) (liftQ5 (Γ := Γ) (T := T) (C := C) (N.use ρ 5) GB)
      (fun φ => (Fintype.card Γ : ℝ) * N.I.cost φ) := by
  have h := gistageE_bwd N.I N.r5 N.G5 N.N5 N.Wn5 N.hN5 N.hW5
    (fun g q => N.Zp (9 * ρ.val + 5) g (N.use ρ 5 q)) (cOne Γ C α) (cOne Γ C α)
  have h' : GRoute (bIn N.I.tv N.r5 (fun d => (N.G5 d).Xm)
        (fun g q => N.Zp (9 * ρ.val + 5) g (N.use ρ 5 q)) (cOne Γ C α))
      (mkS N.xi6 N.yi6 (fun g q => N.Zb (9 * ρ.val + 6) g (N.use ρ 5 q)) (cOne Γ C α)) GB
      (fun φ => (Fintype.card Γ : ℝ) * N.I.cost φ) := by
    have e : bOut N.I.tv N.r5 (fun d => (N.G5 d).Xm)
        (fun g q => N.Wn5 g q * N.Zp (9 * ρ.val + 5) g (N.use ρ 5 q)) (cOne Γ C α)
        = mkS N.xi6 N.yi6 (fun g q => N.Zb (9 * ρ.val + 6) g (N.use ρ 5 q)) (cOne Γ C α) := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · exact N.x56 g t
      · exact N.y56 g t
      · exact N.hZ5 ρ g q
      · rfl
    rw [← e]
    exact h
  exact gbliftQ5 (N.use ρ 5) (N.hinj ρ 5) N.xo2 N.yo2 N.xo4 N.yo4 N.xi0 N.yi0 (fun g b => N.Zp (9 * ρ.val + 5) g b)
    (fun g b => N.Zb (9 * ρ.val + 6) g b) h'
    (fun g q => rfl) (fun g q => rfl) (fun g b hb => (N.hZn5 ρ g b hb).symm) (fun _ _ _ => rfl)

/-- first idle climb of pair 4 (ONE block per role), to the frames of pair 3 after stage 5. -/
lemma G401.climbA4 (ρ : Fin 8) :
    XRoute (N.S16 ρ) (N.S17 ρ) id (fun φ => (Fintype.card Γ : ℝ) *
      ((Fintype.card T : ℝ) * (N.caX4 φ + N.caY4 φ))) := by
  have H1 := XRoute.reach_all (N.S16 ρ) (N.S17 ρ)
    (mkR4 (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ => N.caX4) (fun _ _ => N.caY4) (fun _ _ _ => 0) (fun _ _ _ => 0)) (by
      rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
      · exact XReach.refl _
      · exact XReach.refl _
      · exact XReach.refl _
      · exact XReach.refl _
      · exact XReach.refl _
      · exact XReach.refl _
      · show XReach ((N.G0 g).Xm.Φ (tt (N.I.tv t))) ((N.G6 (N.r6 t g)).Xm.Φ (tt (N.I.tv t))) N.caX4
        rw [← N.x56 g t]
        exact N.aX4 g t
      · show XReach ((N.G0 g).Xm.Φ 0) ((N.G6 (N.r6 t g)).Xm.Φ 0) N.caY4
        rw [← N.y56 g t]
        exact N.aY4 g t
      · exact XReach.refl _
      · exact XReach.refl _)
  refine H1.cast (fun φ => ?_)
  simp_rw [mkR4_map (fun c : (ℕ → ℝ) → ℝ => c φ)]
  rw [sum_mkR4]
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_zero, add_zero, zero_add]
  ring

/-- gate layer A of pair 4 in run `ρ`: twins have equal frames. -/
lemma G401.gateA4 (ρ : Fin 8) : XRoute (N.S17 ρ) (N.S17 ρ) (gscQ pABQ_4 kAQ_4) (fun _ => 0) := by
  refine gateP pABQ_4 kAQ_4 (N.S17 ρ) ?_
  rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩) hk
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · rfl
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · rfl
  · exact (hk rfl).elim
  · exact (hk rfl).elim

/-- the free bank adapters before stage 6 of run `ρ` (`bank_adapt`): every bank from `Zb` to `Zp`. -/
lemma G401.adapt6 (ρ : Fin 8) :
    GRoute (N.S17 ρ) (N.S18 ρ) id (fun _ => 0) := by
  have H1 := GRoute.reach_all (N.S17 ρ) (N.S18 ρ) (fun _ _ => 0) (by
      rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact N.hP6 ρ g b
      · exact GReach.refl _)
  exact H1.cast (fun φ => by simp)

/-- stage 6 of run `ρ`: forward on pair 3; the slot `q` of `g` on the bank `(g, use ρ 6 q)`. -/
lemma G401.stage6 (ρ : Fin 8) :
    GRoute (N.S18 ρ) (N.S19 ρ) (liftQ6 (Γ := Γ) (T := T) (C := C) (N.use ρ 6) GF)
      (fun φ => (Fintype.card Γ : ℝ) * N.I.cost φ) := by
  have h := gistageE_fwd N.I N.r6 N.G6 N.N6 N.Wn6 N.hN6 N.hW6
    (fun g q => N.Zp (9 * ρ.val + 6) g (N.use ρ 6 q)) (cOne Γ C α) (cOne Γ C α)
  have h' : GRoute (bIn N.I.tv N.r6 (fun d => (N.G6 d).Xm)
        (fun g q => N.Zp (9 * ρ.val + 6) g (N.use ρ 6 q)) (cOne Γ C α))
      (mkS N.xo6 N.yo6 (fun g q => N.Zb (9 * ρ.val + 7) g (N.use ρ 6 q)) (cOne Γ C α)) GF
      (fun φ => (Fintype.card Γ : ℝ) * N.I.cost φ) := by
    have e : bOut N.I.tv N.r6 (fun d => (N.G6 d).Xm)
        (fun g q => N.Wn6 g q * N.Zp (9 * ρ.val + 6) g (N.use ρ 6 q)) (cOne Γ C α)
        = mkS N.xo6 N.yo6 (fun g q => N.Zb (9 * ρ.val + 7) g (N.use ρ 6 q)) (cOne Γ C α) := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · rfl
      · rfl
      · exact N.hZ6 ρ g q
      · rfl
    rw [← e]
    exact h
  exact gbliftQ6 (N.use ρ 6) (N.hinj ρ 6) N.xo2 N.yo2 N.xo4 N.yo4 N.xi6 N.yi6 (fun g b => N.Zp (9 * ρ.val + 6) g b)
    (fun g b => N.Zb (9 * ρ.val + 7) g b) h'
    (fun g q => rfl) (fun g q => rfl) (fun g b hb => (N.hZn6 ρ g b hb).symm) (fun _ _ _ => rfl)

/-- second idle climb of pair 4: the window of stage 6, ONE block of rank `card H - 1` per role. -/
lemma G401.climbB4 (ρ : Fin 8) :
    XRoute (N.S19 ρ) (N.S20 ρ) id (fun φ => (Fintype.card Γ : ℝ) *
      ((Fintype.card T : ℝ) * (2 * bcost φ (Fintype.card H - 1)))) := by
  have H1 := XRoute.reach_all (N.S19 ρ) (N.S20 ρ)
    (mkR4 (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ => (fun φ => bcost φ (Fintype.card H - 1))) (fun _ _ => (fun φ => bcost φ (Fintype.card H - 1))) (fun _ _ _ => 0) (fun _ _ _ => 0)) (by
      rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
      · exact XReach.refl _
      · exact XReach.refl _
      · exact XReach.refl _
      · exact XReach.refl _
      · exact XReach.refl _
      · exact XReach.refl _
      · show XReach ((N.G6 (N.r6 t g)).Xm.Φ (tt (N.I.tv t))) ((N.G7 (N.r7 t g)).Xm.Φ (tt (N.I.tv t)))
          (fun φ => bcost φ (Fintype.card H - 1))
        rw [← N.x67 g t]
        exact GInvE.climbX N.I (N.G6 (N.r6 t g)).Xm t
      · show XReach ((N.G6 (N.r6 t g)).Xm.Φ 0) ((N.G7 (N.r7 t g)).Xm.Φ 0)
          (fun φ => bcost φ (Fintype.card H - 1))
        rw [← N.y67 g t]
        exact GInvE.climbY N.I (N.G6 (N.r6 t g)).Xm t
      · exact XReach.refl _
      · exact XReach.refl _)
  refine H1.cast (fun φ => ?_)
  simp_rw [mkR4_map (fun c : (ℕ → ℝ) → ℝ => c φ)]
  rw [sum_mkR4]
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_zero, add_zero, zero_add]
  ring

/-- gate layer B of pair 4 in run `ρ`: twins have equal frames. -/
lemma G401.gateB4 (ρ : Fin 8) : XRoute (N.S20 ρ) (N.S20 ρ) (gscQ pABQ_4 kBQ_4) (fun _ => 0) := by
  refine gateP pABQ_4 kBQ_4 (N.S20 ρ) ?_
  rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩) hk
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact N.x67 g t
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (N.y67 g t).symm
  · exact (hk rfl).elim
  · exact (hk rfl).elim

/-- the free bank adapters before stage 7 of run `ρ` (`bank_adapt`): every bank from `Zb` to `Zp`. -/
lemma G401.adapt7 (ρ : Fin 8) :
    GRoute (N.S20 ρ) (N.S21 ρ) id (fun _ => 0) := by
  have H1 := GRoute.reach_all (N.S20 ρ) (N.S21 ρ) (fun _ _ => 0) (by
      rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact N.hP7 ρ g b
      · exact GReach.refl _)
  exact H1.cast (fun φ => by simp)

/-- stage 7 of run `ρ`: backward on pair 4; the slot `q` of `g` on the bank `(g, use ρ 7 q)`. -/
lemma G401.stage7 (ρ : Fin 8) :
    GRoute (N.S21 ρ) (N.S22 ρ) (liftQ7 (Γ := Γ) (T := T) (C := C) (N.use ρ 7) GB)
      (fun φ => (Fintype.card Γ : ℝ) * N.I.cost φ) := by
  have h := gistageE_bwd N.I N.r7 N.G7 N.N7 N.Wn7 N.hN7 N.hW7
    (fun g q => N.Zp (9 * ρ.val + 7) g (N.use ρ 7 q)) (cOne Γ C α) (cOne Γ C α)
  have h' : GRoute (bIn N.I.tv N.r7 (fun d => (N.G7 d).Xm)
        (fun g q => N.Zp (9 * ρ.val + 7) g (N.use ρ 7 q)) (cOne Γ C α))
      (mkS N.xi8 N.yi8 (fun g q => N.Zb (9 * ρ.val + 8) g (N.use ρ 7 q)) (cOne Γ C α)) GB
      (fun φ => (Fintype.card Γ : ℝ) * N.I.cost φ) := by
    have e : bOut N.I.tv N.r7 (fun d => (N.G7 d).Xm)
        (fun g q => N.Wn7 g q * N.Zp (9 * ρ.val + 7) g (N.use ρ 7 q)) (cOne Γ C α)
        = mkS N.xi8 N.yi8 (fun g q => N.Zb (9 * ρ.val + 8) g (N.use ρ 7 q)) (cOne Γ C α) := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · exact N.x78 g t
      · exact N.y78 g t
      · exact N.hZ7 ρ g q
      · rfl
    rw [← e]
    exact h
  exact gbliftQ7 (N.use ρ 7) (N.hinj ρ 7) N.xo2 N.yo2 N.xo4 N.yo4 N.xo6 N.yo6 (fun g b => N.Zp (9 * ρ.val + 7) g b)
    (fun g b => N.Zb (9 * ρ.val + 8) g b) h'
    (fun g q => rfl) (fun g q => rfl) (fun g b hb => (N.hZn7 ρ g b hb).symm) (fun _ _ _ => rfl)

/-- the free bank adapters before stage 8 of run `ρ` (`bank_adapt`): every bank from `Zb` to `Zp`. -/
lemma G401.adapt8 (ρ : Fin 8) :
    GRoute (N.S22 ρ) (N.S23 ρ) id (fun _ => 0) := by
  have H1 := GRoute.reach_all (N.S22 ρ) (N.S23 ρ) (fun _ _ => 0) (by
      rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact N.hP8 ρ g b
      · exact GReach.refl _)
  exact H1.cast (fun φ => by simp)

/-- stage 8 of run `ρ`: forward on pair 4; the slot `q` of `g` on the bank `(g, use ρ 8 q)`. -/
lemma G401.stage8 (ρ : Fin 8) :
    GRoute (N.S23 ρ) (N.S24 ρ) (liftQ8 (Γ := Γ) (T := T) (C := C) (N.use ρ 8) GF)
      (fun φ => (Fintype.card Γ : ℝ) * N.I.cost φ) := by
  have h := gistageE_fwd N.I N.r8 N.G8 N.N8 N.Wn8 N.hN8 N.hW8
    (fun g q => N.Zp (9 * ρ.val + 8) g (N.use ρ 8 q)) (cOne Γ C α) (cOne Γ C α)
  have h' : GRoute (bIn N.I.tv N.r8 (fun d => (N.G8 d).Xm)
        (fun g q => N.Zp (9 * ρ.val + 8) g (N.use ρ 8 q)) (cOne Γ C α))
      (mkS N.xo8 N.yo8 (fun g q => N.Zb (9 * ρ.val + 9) g (N.use ρ 8 q)) (cOne Γ C α)) GF
      (fun φ => (Fintype.card Γ : ℝ) * N.I.cost φ) := by
    have e : bOut N.I.tv N.r8 (fun d => (N.G8 d).Xm)
        (fun g q => N.Wn8 g q * N.Zp (9 * ρ.val + 8) g (N.use ρ 8 q)) (cOne Γ C α)
        = mkS N.xo8 N.yo8 (fun g q => N.Zb (9 * ρ.val + 9) g (N.use ρ 8 q)) (cOne Γ C α) := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · rfl
      · rfl
      · exact N.hZ8 ρ g q
      · rfl
    rw [← e]
    exact h
  exact gbliftQ8 (N.use ρ 8) (N.hinj ρ 8) N.xo2 N.yo2 N.xo4 N.yo4 N.xo6 N.yo6 (fun g b => N.Zp (9 * ρ.val + 8) g b)
    (fun g b => N.Zb (9 * ρ.val + 9) g b) h'
    (fun g q => rfl) (fun g q => rfl) (fun g b hb => (N.hZn8 ρ g b hb).symm) (fun _ _ _ => rfl)

/-- the final climbs of the replica of run `ρ`: every pair from its frames after its last stage. -/
lemma G401.fin (ρ : Fin 8) :
    XRoute (N.S24 ρ) (N.S25 ρ) id (fun φ => (Fintype.card Γ : ℝ) *
      ((Fintype.card T : ℝ) * ((N.cX1 φ + N.cY1 φ) + (N.cX2 φ + N.cY2 φ) + (N.cX3 φ + N.cY3 φ) + (N.cX4 φ + N.cY4 φ)))) := by
  have H1 := XRoute.reach_all (N.S24 ρ) (N.S25 ρ)
    (mkR4 (fun _ _ => N.cX1) (fun _ _ => N.cY1) (fun _ _ => N.cX2) (fun _ _ => N.cY2) (fun _ _ => N.cX3) (fun _ _ => N.cY3) (fun _ _ => N.cX4) (fun _ _ => N.cY4) (fun _ _ _ => 0) (fun _ _ _ => 0)) (by
      rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
      · exact N.fX1 g t
      · exact N.fY1 g t
      · exact N.fX2 g t
      · exact N.fY2 g t
      · exact N.fX3 g t
      · exact N.fY3 g t
      · exact N.fX4 g t
      · exact N.fY4 g t
      · exact XReach.refl _
      · exact XReach.refl _)
  refine H1.cast (fun φ => ?_)
  simp_rw [mkR4_map (fun c : (ℕ → ℝ) → ℝ => c φ)]
  rw [sum_mkR4]
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_zero, add_zero, zero_add]
  ring

/-- gate layer C of pair 4 in run `ρ`: twins have equal frames. -/
lemma G401.gateC4 (ρ : Fin 8) : XRoute (N.S25 ρ) (N.S25 ρ) (gscQ pCQ_4 kCQ_4) (fun _ => 0) := by
  refine gateP pCQ_4 kCQ_4 (N.S25 ρ) ?_
  rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩) hk
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · rfl
  · rfl
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim

/-- gate layer C of pair 3 in run `ρ`: twins have equal frames. -/
lemma G401.gateC3 (ρ : Fin 8) : XRoute (N.S25 ρ) (N.S25 ρ) (gscQ pCQ_3 kCQ_3) (fun _ => 0) := by
  refine gateP pCQ_3 kCQ_3 (N.S25 ρ) ?_
  rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩) hk
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · rfl
  · rfl
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim

/-- gate layer C of pair 2 in run `ρ`: twins have equal frames. -/
lemma G401.gateC2 (ρ : Fin 8) : XRoute (N.S25 ρ) (N.S25 ρ) (gscQ pCQ_2 kCQ_2) (fun _ => 0) := by
  refine gateP pCQ_2 kCQ_2 (N.S25 ρ) ?_
  rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩) hk
  · exact (hk rfl).elim
  · rfl
  · rfl
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim

end Net
end
end GX
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.GX.G401.stage0
#print axioms OAI.PowerSaving.GX.G401.stage1
#print axioms OAI.PowerSaving.GX.G401.stage2
#print axioms OAI.PowerSaving.GX.G401.stage3
#print axioms OAI.PowerSaving.GX.G401.stage4
#print axioms OAI.PowerSaving.GX.G401.stage5
#print axioms OAI.PowerSaving.GX.G401.stage6
#print axioms OAI.PowerSaving.GX.G401.stage7
#print axioms OAI.PowerSaving.GX.G401.stage8
#print axioms OAI.PowerSaving.GX.G401.fin

end
-- bos_merge: end Submission.Work.Bridge401.GNetStage

-- bos_merge: begin Submission.Work.Bridge401.GNetCert
section

/-!
# (key: bridge-401) The certificate of the nine-stage word with entrance gauges and residual banks (PR #401)

Credits: the entrance gauges and the residual banks are Dugongue's (CrocSwap/integer-mult-bounds PR #401); the bank
patterns are Lydakis's (#275); the compressed nine-stage layout is jacklightChen's (#377); the bridged word B_K is
DaysSky's (#363); B_2, the engine, the stage geometry and the E8 unit are Jacob Sussman's (wht-power-saving-lean,
Apache-2.0).  Written by w-newsums/gen401/gen401.py (from gen377.py).
`G401.run ρ`: the route of run `ρ` on the roles of a run (as genk's B_4 route, with the free bank adapters).
`G401.runFull ρ`: the same on all roles (`GRoute.lift` by `emRun4 ρ`).  `G401.sweep`: the 8 runs
(`GRoute.sweep_const`).  `G401.padR`: ONE padding block of rank `pad b` on every bank.  Then the free shifts and the
signed exchange, and `gcert_of_groute`.  The scalar identity goes through `sweep_data4` / `sweep_bank4` and
`chainQ_eq` with `rw` only.  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace OAI
namespace PowerSaving
namespace GX
open Binary Matrix Finset RAM SS CB RF BR GF
noncomputable section

section Net
variable {H T Sl C α Γ : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C] [Fintype α] [DecidableEq α]
  [Fintype Γ] [DecidableEq Γ]
variable {nb : ℕ} (N : G401 H T Sl C α Γ nb)

/-- the whole run `ρ` before the exchange, on the roles of a run. -/
lemma G401.run (ρ : Fin 8) :
    GRoute (N.S0 ρ) (N.S25 ρ) (chainQ (N.use ρ)) (fun φ => (Fintype.card Γ : ℝ) * N.runUnit φ) := by
  have R := ((((((((((((((((((((((((((((((((((N.adapt0 ρ)).trans (N.stage0 ρ)).trans (N.adapt1 ρ)).trans (N.stage1 ρ)).trans (GRoute.ofX (N.climbA2 ρ))).trans (GRoute.ofX (N.gateA2 ρ))).trans (N.adapt2 ρ)).trans (N.stage2 ρ)).trans (GRoute.ofX (N.climbB2 ρ))).trans (GRoute.ofX (N.gateB2 ρ))).trans (N.adapt3 ρ)).trans (N.stage3 ρ)).trans (GRoute.ofX (N.climbA3 ρ))).trans (GRoute.ofX (N.gateA3 ρ))).trans (N.adapt4 ρ)).trans (N.stage4 ρ)).trans (GRoute.ofX (N.climbB3 ρ))).trans (GRoute.ofX (N.gateB3 ρ))).trans (N.adapt5 ρ)).trans (N.stage5 ρ)).trans (GRoute.ofX (N.climbA4 ρ))).trans (GRoute.ofX (N.gateA4 ρ))).trans (N.adapt6 ρ)).trans (N.stage6 ρ)).trans (GRoute.ofX (N.climbB4 ρ))).trans (GRoute.ofX (N.gateB4 ρ))).trans (N.adapt7 ρ)).trans (N.stage7 ρ)).trans (N.adapt8 ρ)).trans (N.stage8 ρ)).trans (GRoute.ofX (N.fin ρ))).trans (GRoute.ofX (N.gateC4 ρ))).trans (GRoute.ofX (N.gateC3 ρ))).trans (GRoute.ofX (N.gateC2 ρ))
  refine R.cast (fun φ => ?_)
  simp only [G401.runUnit]
  ring

/-- run `ρ` on all roles: the other replicas wait (before their run at `InitD`, after it at `FinD`). -/
lemma G401.runFull (ρ : Fin 8) :
    GRoute (N.Sfull ρ.castSucc) (N.Sfull ρ.succ) (liftRun4 ρ (chainQ (N.use ρ)))
      (fun φ => (Fintype.card Γ : ℝ) * N.runUnit φ) := by
  refine GRoute.lift (emRun4 ρ) (h := chainQ (N.use ρ)) ?_ (fun x => ?_) (fun x i hi => ?_) (fun i hi => ?_)
  · have e1 : N.Sfull ρ.castSucc ∘ (emRun4 ρ) = N.S0 ρ := by
      funext r
      rcases r with ((d|⟨g,b⟩)|⟨g,c⟩)
      · exact if_neg (lt_irrefl _)
      · rfl
      · rfl
    have e2 : N.Sfull ρ.succ ∘ (emRun4 ρ) = N.S25 ρ := by
      funext r
      rcases r with ((d|⟨g,b⟩)|⟨g,c⟩)
      · exact if_pos (Nat.lt_succ_self _)
      · have e : 9 * ρ.succ.val = 9 * ρ.val + 9 := by
          rw [Fin.val_succ]
          ring
        show N.Zb (9 * ρ.succ.val) g b = N.Zb (9 * ρ.val + 9) g b
        rw [e]
      · rfl
    rw [e1, e2]
    exact N.run ρ
  · funext r
    rcases r with ((d|⟨g,b⟩)|⟨g,c⟩)
    · exact if_pos rfl
    · rfl
    · rfl
  · rcases i with ((⟨ρ',d⟩|⟨g,b⟩)|⟨g,c⟩)
    · by_cases e : ρ' = ρ
      · subst e
        exact absurd ((cover_iff _ _).mpr ⟨Sum.inl (Sum.inl d), rfl⟩) hi
      · exact if_neg e
    · exact absurd ((cover_iff _ _).mpr ⟨Sum.inl (Sum.inr (g, b)), rfl⟩) hi
    · exact absurd ((cover_iff _ _).mpr ⟨Sum.inr (g, c), rfl⟩) hi
  · rcases i with ((⟨ρ',d⟩|⟨g,b⟩)|⟨g,c⟩)
    · by_cases e : ρ' = ρ
      · subst e
        exact absurd ((cover_iff _ _).mpr ⟨Sum.inl (Sum.inl d), rfl⟩) hi
      · have e' : ρ'.val ≠ ρ.val := fun h => e (Fin.ext h)
        show (if ρ'.val < ρ.castSucc.val then N.FinD d else N.InitD d)
          = (if ρ'.val < ρ.succ.val then N.FinD d else N.InitD d)
        simp only [Fin.val_castSucc, Fin.val_succ]
        split_ifs <;> first | rfl | (exfalso; omega)
    · exact absurd ((cover_iff _ _).mpr ⟨Sum.inl (Sum.inr (g, b)), rfl⟩) hi
    · exact absurd ((cover_iff _ _).mpr ⟨Sum.inr (g, c), rfl⟩) hi

/-- **the 8 runs one after the other.** -/
lemma G401.sweep :
    GRoute (N.Sfull 0) (N.Sfull (Fin.last 8)) (sweepMap (fun ρ : Fin 8 => liftRun4 ρ (chainQ (N.use ρ))))
      (fun φ => ((8 : ℕ) : ℝ) * ((Fintype.card Γ : ℝ) * N.runUnit φ)) :=
  GRoute.sweep_const 8 N.Sfull _ (fun _ φ => (Fintype.card Γ : ℝ) * N.runUnit φ) _ (fun _ _ => rfl)
    (fun ρ => N.runFull ρ)

/-- **the padding blocks**: ONE block of rank `pad b` per bank. -/
lemma G401.padR :
    GRoute (N.Sfull (Fin.last 8)) N.Sfin id
      (fun φ => (Fintype.card Γ : ℝ) * ∑ b, bcost φ (N.pad b)) := by
  have H1 := GRoute.reach_all (N.Sfull (Fin.last 8)) N.Sfin
    (mk401 (fun _ _ _ => 0) (fun _ b φ => bcost φ (N.pad b)) (fun _ _ _ => 0)) (by
      rintro ((⟨ρ',d⟩|⟨g,b⟩)|⟨g,c⟩)
      · have e : N.Sfull (Fin.last 8) (Sum.inl (Sum.inl (ρ', d))) = N.FinD d := if_pos ρ'.isLt
        show GReach (N.Sfull (Fin.last 8) (Sum.inl (Sum.inl (ρ', d)))) (N.FinD d) (fun _ => 0)
        rw [e]
        exact GReach.refl _
      · exact N.bpad g b
      · exact GReach.refl _)
  refine H1.cast (fun φ => ?_)
  simp_rw [mk401_map (fun c : (ℕ → ℝ) → ℝ => c φ)]
  rw [sum_mk401]
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_zero, add_zero, zero_add, Finset.sum_const_zero]

/-- the free shifts at the end. -/
def G401.corr : BRole401 Γ T nb C → Space α :=
  mk401 (fun _ => mkD4 (fun _ _ => 0) (fun g t => N.u g t) (fun _ _ => 0) (fun g t => N.u g t) (fun _ _ => 0) (fun g t => N.u g t) (fun _ _ => 0) (fun g t => N.u g t)) (fun _ _ => 0) (fun _ _ => 0)

def G401.Sz : BRole401 Γ T nb C → CMat α := fun r => shift (N.corr r) * N.Sfin r

/-- **The scratch certificate of the nine-stage word with entrance gauges and residual banks (PR #401)**, in whole
blocks, with its exact price for every price list. -/
theorem g401_certificate :
    GCert α (Sum.inl : BLive401 Γ T nb → BRole401 Γ T nb C)
      (fun φ => (Fintype.card Γ : ℝ) * N.unit φ) := by
  have R1 := N.sweep.trans N.padR
  have R2 : GRoute N.Sfin N.Sz id (fun _ => 0) := GRoute.shifts N.hm N.Sfin N.corr
  have R3 : GRoute N.Sz (fun r => N.Sz (bpull401 r)) (actPoint brec401) (fun _ => 0) :=
    GRoute.gate brec401 N.Sz _ (fun i j h => by
      have hj : j = bpull401 i := by
        by_contra hne
        exact h (by simp [brec401, hne])
      rw [hj])
  have Rt := ((R1.trans R2).trans R3).cast (c' := fun φ => (Fintype.card Γ : ℝ) * N.unit φ)
    (fun φ => by simp only [G401.unit]; push_cast; ring)
  have h0 : ∀ (ρ' : Fin 8) (d : BDat4 Γ T), N.Sfull 0 (Sum.inl (Sum.inl (ρ', d))) = N.InitD d :=
    fun ρ' d => by simp [G401.Sfull, mk401]
  have hS : ∀ r, ∃ M, N.Sfull 0 r * M = 1 := by
    rintro ((⟨ρ',d⟩|⟨g,b⟩)|⟨g,c⟩)
    · rw [h0]
      rcases d with ((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))
      · exact N.inv0 g t
      · refine ⟨1, ?_⟩
        show (N.G0 g).Xm.Φ 0 * 1 = 1
        rw [N.z0, Matrix.mul_one]
      · exact N.inv0 g t
      · refine ⟨1, ?_⟩
        show (N.G0 g).Xm.Φ 0 * 1 = 1
        rw [N.z0, Matrix.mul_one]
      · exact N.inv0 g t
      · refine ⟨1, ?_⟩
        show (N.G0 g).Xm.Φ 0 * 1 = 1
        rw [N.z0, Matrix.mul_one]
      · exact N.inv0 g t
      · refine ⟨1, ?_⟩
        show (N.G0 g).Xm.Φ 0 * 1 = 1
        rw [N.z0, Matrix.mul_one]
    · refine ⟨1, ?_⟩
      show N.Zb 0 g b * 1 = 1
      rw [N.z0b, Matrix.mul_one]
    · exact ⟨1, Matrix.mul_one _⟩
  have hT : ∀ l : BLive401 Γ T nb, N.Sz (bpull401 (Sum.inl l)) = kernel α * N.Sfull 0 (Sum.inl l) := by
    rintro (⟨ρ', d⟩|⟨g,b⟩)
    · rw [h0]
      rcases d with ((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))
      · show shift (N.u g t) * N.YF g t = kernel α * (N.G0 g).Xm.Φ (tt (N.I.tv t))
        exact (N.term g t).symm
      · show shift (0 : Space α) * kernel α = kernel α * (N.G0 g).Xm.Φ 0
        rw [shift_zero, Matrix.one_mul, N.z0, Matrix.mul_one]
      · show shift (N.u g t) * N.YF g t = kernel α * (N.G0 g).Xm.Φ (tt (N.I.tv t))
        exact (N.term g t).symm
      · show shift (0 : Space α) * kernel α = kernel α * (N.G0 g).Xm.Φ 0
        rw [shift_zero, Matrix.one_mul, N.z0, Matrix.mul_one]
      · show shift (N.u g t) * N.YF g t = kernel α * (N.G0 g).Xm.Φ (tt (N.I.tv t))
        exact (N.term g t).symm
      · show shift (0 : Space α) * kernel α = kernel α * (N.G0 g).Xm.Φ 0
        rw [shift_zero, Matrix.one_mul, N.z0, Matrix.mul_one]
      · show shift (N.u g t) * N.YF g t = kernel α * (N.G0 g).Xm.Φ (tt (N.I.tv t))
        exact (N.term g t).symm
      · show shift (0 : Space α) * kernel α = kernel α * (N.G0 g).Xm.Φ 0
        rw [shift_zero, Matrix.one_mul, N.z0, Matrix.mul_one]
    · show shift (0 : Space α) * kernel α = kernel α * N.Zb 0 g b
      rw [shift_zero, Matrix.one_mul, N.z0b, Matrix.mul_one]
  have hg : ∀ x : BRole401 Γ T nb C → ℂ,
      (∀ s, (∀ l : BLive401 Γ T nb, (Sum.inl l : BRole401 Γ T nb C) ≠ s) → x s = 0) →
      ∀ l : BLive401 Γ T nb,
        (actPoint brec401 ∘ (id ∘ (id ∘ sweepMap (fun ρ : Fin 8 => liftRun4 ρ (chainQ (N.use ρ)))))) x (Sum.inl l)
          = x (Sum.inl l) := by
    intro x _ l
    rw [Function.comp_apply, Function.comp_apply, Function.comp_apply, id_eq, id_eq, actPoint_brec401]
    rcases l with (⟨ρ, d⟩|⟨g,b⟩)
    · rcases d with ((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))
      · show ((1:ℚ):ℂ) * sweepMap (fun i : Fin 8 => liftRun4 i (chainQ (N.use i))) x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inl (Sum.inl (Sum.inr ((g,t)))))))) = _
        rw [sweep_data4 N.use, chainQ_eq]
        show ((1:ℚ):ℂ) * x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inl (Sum.inl (Sum.inl ((g,t)))))))) = x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inl (Sum.inl (Sum.inl ((g,t))))))))
        first | (push_cast; ring) | simp
      · show ((-1:ℚ):ℂ) * sweepMap (fun i : Fin 8 => liftRun4 i (chainQ (N.use i))) x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inl (Sum.inl (Sum.inl ((g,t)))))))) = _
        rw [sweep_data4 N.use, chainQ_eq]
        show ((-1:ℚ):ℂ) * (-x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inl (Sum.inl (Sum.inr ((g,t))))))))) = x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inl (Sum.inl (Sum.inr ((g,t))))))))
        first | (push_cast; ring) | simp
      · show ((1:ℚ):ℂ) * sweepMap (fun i : Fin 8 => liftRun4 i (chainQ (N.use i))) x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inl (Sum.inr (Sum.inr ((g,t)))))))) = _
        rw [sweep_data4 N.use, chainQ_eq]
        show ((1:ℚ):ℂ) * x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inl (Sum.inr (Sum.inl ((g,t)))))))) = x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inl (Sum.inr (Sum.inl ((g,t))))))))
        first | (push_cast; ring) | simp
      · show ((-1:ℚ):ℂ) * sweepMap (fun i : Fin 8 => liftRun4 i (chainQ (N.use i))) x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inl (Sum.inr (Sum.inl ((g,t)))))))) = _
        rw [sweep_data4 N.use, chainQ_eq]
        show ((-1:ℚ):ℂ) * (-x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inl (Sum.inr (Sum.inr ((g,t))))))))) = x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inl (Sum.inr (Sum.inr ((g,t))))))))
        first | (push_cast; ring) | simp
      · show ((1:ℚ):ℂ) * sweepMap (fun i : Fin 8 => liftRun4 i (chainQ (N.use i))) x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inr (Sum.inr ((g,t))))))) = _
        rw [sweep_data4 N.use, chainQ_eq]
        show ((1:ℚ):ℂ) * x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inr (Sum.inl ((g,t))))))) = x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inr (Sum.inl ((g,t)))))))
        first | (push_cast; ring) | simp
      · show ((-1:ℚ):ℂ) * sweepMap (fun i : Fin 8 => liftRun4 i (chainQ (N.use i))) x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inr (Sum.inl ((g,t))))))) = _
        rw [sweep_data4 N.use, chainQ_eq]
        show ((-1:ℚ):ℂ) * (-x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inr (Sum.inr ((g,t)))))))) = x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inr (Sum.inr ((g,t)))))))
        first | (push_cast; ring) | simp
      · show ((1:ℚ):ℂ) * sweepMap (fun i : Fin 8 => liftRun4 i (chainQ (N.use i))) x (Sum.inl (Sum.inl (ρ, Sum.inr (Sum.inr ((g,t)))))) = _
        rw [sweep_data4 N.use, chainQ_eq]
        show ((1:ℚ):ℂ) * x (Sum.inl (Sum.inl (ρ, Sum.inr (Sum.inl ((g,t)))))) = x (Sum.inl (Sum.inl (ρ, Sum.inr (Sum.inl ((g,t))))))
        first | (push_cast; ring) | simp
      · show ((-1:ℚ):ℂ) * sweepMap (fun i : Fin 8 => liftRun4 i (chainQ (N.use i))) x (Sum.inl (Sum.inl (ρ, Sum.inr (Sum.inl ((g,t)))))) = _
        rw [sweep_data4 N.use, chainQ_eq]
        show ((-1:ℚ):ℂ) * (-x (Sum.inl (Sum.inl (ρ, Sum.inr (Sum.inr ((g,t))))))) = x (Sum.inl (Sum.inl (ρ, Sum.inr (Sum.inr ((g,t))))))
        first | (push_cast; ring) | simp
    · show ((1:ℚ):ℂ) * sweepMap (fun i : Fin 8 => liftRun4 i (chainQ (N.use i))) x (Sum.inl (Sum.inr (g, b))) = _
      rw [sweep_bank4 N.use]
      first | (push_cast; ring) | simp
  exact gcert_of_groute (Sum.inl : BLive401 Γ T nb → BRole401 Γ T nb C) (N.Sfull 0)
    (fun r => N.Sz (bpull401 r)) _ _ Rt hS hg hT

end Net
end
end GX
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.GX.G401.run
#print axioms OAI.PowerSaving.GX.G401.runFull
#print axioms OAI.PowerSaving.GX.g401_certificate

end
-- bos_merge: end Submission.Work.Bridge401.GNetCert
