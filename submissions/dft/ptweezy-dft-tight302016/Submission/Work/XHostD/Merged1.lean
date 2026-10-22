import Submission.Work.XHost.HRoles
import Submission.Work.XHostD.Prov

/-! Merged module written by bos_merge.py for the 500-file limit of the Big O Speedrun
pull-request route.  It is the concatenation, in import order, of the 3 modules below; each one
is copied verbatim after its import header, inside `section` ... `end`, with the scopes it leaves
open closed before that `end`.  Members (module, sha256 of the original file):
* `Submission.Work.XHostD.HDef` 47a8e6f106332a33d10e7794780f8ccc512500364e836da925e7b7eb96d531f9
* `Submission.Work.XHostD.HStage` 11622e32d4319be18513815a2c8887be83d7153c0032bc9e1b42ffd04a8deaa0
* `Submission.Work.XHostD.HCert` 2d1eabfab4616eff4855cff3b684c7737c7ddf254537ca1c02141bb88c37ce45
-/

-- bos_merge: begin Submission.Work.XHostD.HDef
section

/-!
# (key: bridge-host) The nine-stage word of PR #401 with SAME-RUN HOSTING: data and frames

Copy of Work/Bridge401/GNetDef.lean (Ryan Shea's complex588 tree; `G401` by Nil Mamano, written by his gen401.py, on
Dugongue #401 / jacklightChen #377 / Lydakis #275 / DaysSky #363; engine and E8 unit by Jacob Sussman) with idle-axis
hosting (DaysSky, CrocSwap/integer-mult-bounds PR #442): in stage `l` the slot `q` goes to the idle data role
`hostAt l q = some (c, s, t)` (window kind `c`, side `s`, class `(g, t)` of the run's replica; the same table in every
run) or, when `hostAt l q = none`, to the bank `bk ρ l q`.  The idle climbs A2..A4, B2..B4 and the finals F1..F3 become
host chains `Hb`/`Hp`: free adapters, the hosted residuals, ONE remaining block of rank `hrem c j` at the old place.
Written by h-L3-build/gen/gen_hnet.py (wht43, 13 Oct 2026), prepared with assistance from Claude.  PER-RUN version (one host table per run) written by fsp-perrun/tools/mk_perrun.py (wht43, 14 Oct 2026) from h-L3-build's file by checked text substitution; prepared with assistance from Claude.  TWO-PROVIDER version (a per-call invocation `Ic ρ l` with the target vectors of `I`, per-call entrance labels and residuals) written by lg-a2a4/tools/mk_disp.py (wht43, 14 Oct 2026) from fsp-perrun's file by checked text substitution; prepared with assistance from Claude.  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace OAI
namespace PowerSaving
namespace XHostD
open Binary Matrix Finset RAM SS CB RF BR GF GX XHost
noncomputable section

structure GHost401 (H T Sl C α Γ : Type) (nb : ℕ) [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
    [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C] [Fintype α] [DecidableEq α] where
  /-- the gauged invocation (`GInvE`). -/
  I : GInvE H T Sl C
  /-- the invocation of call `(ρ, l)` (its provider word), with the target vectors of `I`. -/
  Ic : Fin 8 → Fin 9 → GInvE H T Sl C
  hIc : ∀ ρ l, (Ic ρ l).tv = I.tv
  G0 : Γ → GWin H α
  G1 : Γ → GWin H α
  G2 : Γ → GWin H α
  G3 : Γ → GWin H α
  G4 : Γ → GWin H α
  G5 : Γ → GWin H α
  G6 : Γ → GWin H α
  G7 : Γ → GWin H α
  G8 : Γ → GWin H α
  r1 : T → Γ ≃ Γ
  r2 : T → Γ ≃ Γ
  r3 : T → Γ ≃ Γ
  r4 : T → Γ ≃ Γ
  r5 : T → Γ ≃ Γ
  r6 : T → Γ ≃ Γ
  r7 : T → Γ ≃ Γ
  r8 : T → Γ ≃ Γ
  N0 : Fin 8 → Γ → Sl → CMat α
  Wn0 : Fin 8 → Γ → Sl → CMat α
  N1 : Fin 8 → Γ → Sl → CMat α
  Wn1 : Fin 8 → Γ → Sl → CMat α
  N2 : Fin 8 → Γ → Sl → CMat α
  Wn2 : Fin 8 → Γ → Sl → CMat α
  N3 : Fin 8 → Γ → Sl → CMat α
  Wn3 : Fin 8 → Γ → Sl → CMat α
  N4 : Fin 8 → Γ → Sl → CMat α
  Wn4 : Fin 8 → Γ → Sl → CMat α
  N5 : Fin 8 → Γ → Sl → CMat α
  Wn5 : Fin 8 → Γ → Sl → CMat α
  N6 : Fin 8 → Γ → Sl → CMat α
  Wn6 : Fin 8 → Γ → Sl → CMat α
  N7 : Fin 8 → Γ → Sl → CMat α
  Wn7 : Fin 8 → Γ → Sl → CMat α
  N8 : Fin 8 → Γ → Sl → CMat α
  Wn8 : Fin 8 → Γ → Sl → CMat α
  /-- the host of slot `q` in stage `l`, the SAME in every run: (window kind, side, class); `none`: a bank. -/
  hostAt : Fin 8 → Fin 9 → Sl → Option (Fin 9 × (Bool × T))
  hostInj : ∀ ρ l q q' j, hostAt ρ l q = some j → hostAt ρ l q' = some j → q = q'
  hostWin : ∀ ρ l q c j, hostAt ρ l q = some (c, j) → inWin c.val l.val = true
  /-- the bank of a NON-hosted slot `q` in stage `l` of run `ρ` (junk on hosted slots). -/
  bk : Fin 8 → Fin 9 → Sl → Fin nb
  hinj : ∀ ρ l q q', hostAt ρ l q = none → hostAt ρ l q' = none → bk ρ l q = bk ρ l q' → q = q'
  Zb : ℕ → Γ → Fin nb → CMat α
  Zp : ℕ → Γ → Fin nb → CMat α
  pad : Fin nb → ℕ
  /-- the host chains: frame of host `j` of kind `c` before (`Hb`) and after (`Hp`) the adapter of stage `k`. -/
  Hb : Fin 8 → Fin 9 → ℕ → Γ → Bool × T → CMat α
  Hp : Fin 8 → Fin 9 → ℕ → Γ → Bool × T → CMat α
  hrem : Fin 8 → Fin 9 → Bool × T → ℕ
  u : Γ → T → Space α
  YF : Γ → T → CMat α
  hm : 2 ≤ Fintype.card α
  cX4 : (ℕ → ℝ) → ℝ
  cY4 : (ℕ → ℝ) → ℝ
  inv0 : ∀ g t, ∃ N : CMat α, (G0 g).Xm.Φ (tt (I.tv t)) * N = 1
  z0 : ∀ g, (G0 g).Xm.Φ 0 = 1
  hN0 : ∀ (ρ : Fin 8) d q, (G0 d).X.Φ ((Ic ρ 0).ent q) * N0 ρ d q = 1
  hW0 : ∀ (ρ : Fin 8) d q, (G0 d).X.Φ ((Ic ρ 0).ent q).top = Wn0 ρ d q * (G0 d).X.Φ ((Ic ρ 0).ent q)
  hN1 : ∀ (ρ : Fin 8) d q, (G1 d).X.Φ ((Ic ρ 1).ent q) * N1 ρ d q = 1
  hW1 : ∀ (ρ : Fin 8) d q, (G1 d).X.Φ ((Ic ρ 1).ent q).top = Wn1 ρ d q * (G1 d).X.Φ ((Ic ρ 1).ent q)
  hN2 : ∀ (ρ : Fin 8) d q, (G2 d).X.Φ ((Ic ρ 2).ent q) * N2 ρ d q = 1
  hW2 : ∀ (ρ : Fin 8) d q, (G2 d).X.Φ ((Ic ρ 2).ent q).top = Wn2 ρ d q * (G2 d).X.Φ ((Ic ρ 2).ent q)
  hN3 : ∀ (ρ : Fin 8) d q, (G3 d).X.Φ ((Ic ρ 3).ent q) * N3 ρ d q = 1
  hW3 : ∀ (ρ : Fin 8) d q, (G3 d).X.Φ ((Ic ρ 3).ent q).top = Wn3 ρ d q * (G3 d).X.Φ ((Ic ρ 3).ent q)
  hN4 : ∀ (ρ : Fin 8) d q, (G4 d).X.Φ ((Ic ρ 4).ent q) * N4 ρ d q = 1
  hW4 : ∀ (ρ : Fin 8) d q, (G4 d).X.Φ ((Ic ρ 4).ent q).top = Wn4 ρ d q * (G4 d).X.Φ ((Ic ρ 4).ent q)
  hN5 : ∀ (ρ : Fin 8) d q, (G5 d).X.Φ ((Ic ρ 5).ent q) * N5 ρ d q = 1
  hW5 : ∀ (ρ : Fin 8) d q, (G5 d).X.Φ ((Ic ρ 5).ent q).top = Wn5 ρ d q * (G5 d).X.Φ ((Ic ρ 5).ent q)
  hN6 : ∀ (ρ : Fin 8) d q, (G6 d).X.Φ ((Ic ρ 6).ent q) * N6 ρ d q = 1
  hW6 : ∀ (ρ : Fin 8) d q, (G6 d).X.Φ ((Ic ρ 6).ent q).top = Wn6 ρ d q * (G6 d).X.Φ ((Ic ρ 6).ent q)
  hN7 : ∀ (ρ : Fin 8) d q, (G7 d).X.Φ ((Ic ρ 7).ent q) * N7 ρ d q = 1
  hW7 : ∀ (ρ : Fin 8) d q, (G7 d).X.Φ ((Ic ρ 7).ent q).top = Wn7 ρ d q * (G7 d).X.Φ ((Ic ρ 7).ent q)
  hN8 : ∀ (ρ : Fin 8) d q, (G8 d).X.Φ ((Ic ρ 8).ent q) * N8 ρ d q = 1
  hW8 : ∀ (ρ : Fin 8) d q, (G8 d).X.Φ ((Ic ρ 8).ent q).top = Wn8 ρ d q * (G8 d).X.Φ ((Ic ρ 8).ent q)
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
  /-- the banks (non-hosted slots only). -/
  z0b : ∀ g b, Zb 0 g b = 1
  hP0 : ∀ (ρ : Fin 8) g b, GReach (Zb (9 * ρ.val + 0) g b) (Zp (9 * ρ.val + 0) g b) (fun _ => 0)
  hZ0 : ∀ (ρ : Fin 8) g q, hostAt ρ 0 q = none → Wn0 ρ g q * Zp (9 * ρ.val + 0) g (bk ρ 0 q) = Zb (9 * ρ.val + 1) g (bk ρ 0 q)
  hZn0 : ∀ (ρ : Fin 8) g b, (∀ q, hostAt ρ 0 q = none → bk ρ 0 q ≠ b) → Zb (9 * ρ.val + 1) g b = Zp (9 * ρ.val + 0) g b
  hP1 : ∀ (ρ : Fin 8) g b, GReach (Zb (9 * ρ.val + 1) g b) (Zp (9 * ρ.val + 1) g b) (fun _ => 0)
  hZ1 : ∀ (ρ : Fin 8) g q, hostAt ρ 1 q = none → Wn1 ρ g q * Zp (9 * ρ.val + 1) g (bk ρ 1 q) = Zb (9 * ρ.val + 2) g (bk ρ 1 q)
  hZn1 : ∀ (ρ : Fin 8) g b, (∀ q, hostAt ρ 1 q = none → bk ρ 1 q ≠ b) → Zb (9 * ρ.val + 2) g b = Zp (9 * ρ.val + 1) g b
  hP2 : ∀ (ρ : Fin 8) g b, GReach (Zb (9 * ρ.val + 2) g b) (Zp (9 * ρ.val + 2) g b) (fun _ => 0)
  hZ2 : ∀ (ρ : Fin 8) g q, hostAt ρ 2 q = none → Wn2 ρ g q * Zp (9 * ρ.val + 2) g (bk ρ 2 q) = Zb (9 * ρ.val + 3) g (bk ρ 2 q)
  hZn2 : ∀ (ρ : Fin 8) g b, (∀ q, hostAt ρ 2 q = none → bk ρ 2 q ≠ b) → Zb (9 * ρ.val + 3) g b = Zp (9 * ρ.val + 2) g b
  hP3 : ∀ (ρ : Fin 8) g b, GReach (Zb (9 * ρ.val + 3) g b) (Zp (9 * ρ.val + 3) g b) (fun _ => 0)
  hZ3 : ∀ (ρ : Fin 8) g q, hostAt ρ 3 q = none → Wn3 ρ g q * Zp (9 * ρ.val + 3) g (bk ρ 3 q) = Zb (9 * ρ.val + 4) g (bk ρ 3 q)
  hZn3 : ∀ (ρ : Fin 8) g b, (∀ q, hostAt ρ 3 q = none → bk ρ 3 q ≠ b) → Zb (9 * ρ.val + 4) g b = Zp (9 * ρ.val + 3) g b
  hP4 : ∀ (ρ : Fin 8) g b, GReach (Zb (9 * ρ.val + 4) g b) (Zp (9 * ρ.val + 4) g b) (fun _ => 0)
  hZ4 : ∀ (ρ : Fin 8) g q, hostAt ρ 4 q = none → Wn4 ρ g q * Zp (9 * ρ.val + 4) g (bk ρ 4 q) = Zb (9 * ρ.val + 5) g (bk ρ 4 q)
  hZn4 : ∀ (ρ : Fin 8) g b, (∀ q, hostAt ρ 4 q = none → bk ρ 4 q ≠ b) → Zb (9 * ρ.val + 5) g b = Zp (9 * ρ.val + 4) g b
  hP5 : ∀ (ρ : Fin 8) g b, GReach (Zb (9 * ρ.val + 5) g b) (Zp (9 * ρ.val + 5) g b) (fun _ => 0)
  hZ5 : ∀ (ρ : Fin 8) g q, hostAt ρ 5 q = none → Wn5 ρ g q * Zp (9 * ρ.val + 5) g (bk ρ 5 q) = Zb (9 * ρ.val + 6) g (bk ρ 5 q)
  hZn5 : ∀ (ρ : Fin 8) g b, (∀ q, hostAt ρ 5 q = none → bk ρ 5 q ≠ b) → Zb (9 * ρ.val + 6) g b = Zp (9 * ρ.val + 5) g b
  hP6 : ∀ (ρ : Fin 8) g b, GReach (Zb (9 * ρ.val + 6) g b) (Zp (9 * ρ.val + 6) g b) (fun _ => 0)
  hZ6 : ∀ (ρ : Fin 8) g q, hostAt ρ 6 q = none → Wn6 ρ g q * Zp (9 * ρ.val + 6) g (bk ρ 6 q) = Zb (9 * ρ.val + 7) g (bk ρ 6 q)
  hZn6 : ∀ (ρ : Fin 8) g b, (∀ q, hostAt ρ 6 q = none → bk ρ 6 q ≠ b) → Zb (9 * ρ.val + 7) g b = Zp (9 * ρ.val + 6) g b
  hP7 : ∀ (ρ : Fin 8) g b, GReach (Zb (9 * ρ.val + 7) g b) (Zp (9 * ρ.val + 7) g b) (fun _ => 0)
  hZ7 : ∀ (ρ : Fin 8) g q, hostAt ρ 7 q = none → Wn7 ρ g q * Zp (9 * ρ.val + 7) g (bk ρ 7 q) = Zb (9 * ρ.val + 8) g (bk ρ 7 q)
  hZn7 : ∀ (ρ : Fin 8) g b, (∀ q, hostAt ρ 7 q = none → bk ρ 7 q ≠ b) → Zb (9 * ρ.val + 8) g b = Zp (9 * ρ.val + 7) g b
  hP8 : ∀ (ρ : Fin 8) g b, GReach (Zb (9 * ρ.val + 8) g b) (Zp (9 * ρ.val + 8) g b) (fun _ => 0)
  hZ8 : ∀ (ρ : Fin 8) g q, hostAt ρ 8 q = none → Wn8 ρ g q * Zp (9 * ρ.val + 8) g (bk ρ 8 q) = Zb (9 * ρ.val + 9) g (bk ρ 8 q)
  hZn8 : ∀ (ρ : Fin 8) g b, (∀ q, hostAt ρ 8 q = none → bk ρ 8 q ≠ b) → Zb (9 * ρ.val + 9) g b = Zp (9 * ρ.val + 8) g b
  bpad : ∀ g b, GReach (Zb 72 g b) (kernel α) (fun φ => bcost φ (pad b))
  /-- the host chains (XHost.host_frames): start, free adapters, hosted residuals, ONE remaining block. -/
  hH0_A2 : ∀ (ρ : Fin 8) g t, Hb ρ 0 0 g (false, t) = (G0 g).Xm.Φ (tt (I.tv t)) ∧ Hb ρ 0 0 g (true, t) = (G0 g).Xm.Φ 0
  hHP_A2_0 : ∀ (ρ : Fin 8) g j, GReach (Hb ρ 0 0 g j) (Hp ρ 0 0 g j) (fun _ => 0)
  hHZ_A2_0 : ∀ (ρ : Fin 8) g q j, hostAt ρ 0 q = some (0, j) → Wn0 ρ g q * Hp ρ 0 0 g j = Hb ρ 0 1 g j
  hHZn_A2_0 : ∀ (ρ : Fin 8) g j, (∀ q, hostAt ρ 0 q ≠ some (0, j)) → Hb ρ 0 1 g j = Hp ρ 0 0 g j
  hHP_A2_1 : ∀ (ρ : Fin 8) g j, GReach (Hb ρ 0 1 g j) (Hp ρ 0 1 g j) (fun _ => 0)
  hHZ_A2_1 : ∀ (ρ : Fin 8) g q j, hostAt ρ 1 q = some (0, j) → Wn1 ρ g q * Hp ρ 0 1 g j = Hb ρ 0 2 g j
  hHZn_A2_1 : ∀ (ρ : Fin 8) g j, (∀ q, hostAt ρ 1 q ≠ some (0, j)) → Hb ρ 0 2 g j = Hp ρ 0 1 g j
  hHE_A2 : ∀ (ρ : Fin 8) g t, GReach (Hb ρ 0 2 g (false, t)) ((G1 (r1 t g)).Xm.Φ 1) (fun φ => bcost φ (hrem ρ 0 (false, t))) ∧
    GReach (Hb ρ 0 2 g (true, t)) ((G1 (r1 t g)).Xm.Φ (1 + tt (I.tv t))) (fun φ => bcost φ (hrem ρ 0 (true, t)))
  hH0_B2 : ∀ (ρ : Fin 8) g t, Hb ρ 1 2 g (false, t) = (G2 (r2 t g)).Xm.Φ (tt (I.tv t)) ∧ Hb ρ 1 2 g (true, t) = (G2 (r2 t g)).Xm.Φ 0
  hHP_B2_2 : ∀ (ρ : Fin 8) g j, GReach (Hb ρ 1 2 g j) (Hp ρ 1 2 g j) (fun _ => 0)
  hHZ_B2_2 : ∀ (ρ : Fin 8) g q j, hostAt ρ 2 q = some (1, j) → Wn2 ρ g q * Hp ρ 1 2 g j = Hb ρ 1 3 g j
  hHZn_B2_2 : ∀ (ρ : Fin 8) g j, (∀ q, hostAt ρ 2 q ≠ some (1, j)) → Hb ρ 1 3 g j = Hp ρ 1 2 g j
  hHE_B2 : ∀ (ρ : Fin 8) g t, GReach (Hb ρ 1 3 g (false, t)) ((G2 (r2 t g)).Xm.Φ 1) (fun φ => bcost φ (hrem ρ 1 (false, t))) ∧
    GReach (Hb ρ 1 3 g (true, t)) ((G2 (r2 t g)).Xm.Φ (1 + tt (I.tv t))) (fun φ => bcost φ (hrem ρ 1 (true, t)))
  hH0_A3 : ∀ (ρ : Fin 8) g t, Hb ρ 2 0 g (false, t) = (G0 g).Xm.Φ (tt (I.tv t)) ∧ Hb ρ 2 0 g (true, t) = (G0 g).Xm.Φ 0
  hHP_A3_0 : ∀ (ρ : Fin 8) g j, GReach (Hb ρ 2 0 g j) (Hp ρ 2 0 g j) (fun _ => 0)
  hHZ_A3_0 : ∀ (ρ : Fin 8) g q j, hostAt ρ 0 q = some (2, j) → Wn0 ρ g q * Hp ρ 2 0 g j = Hb ρ 2 1 g j
  hHZn_A3_0 : ∀ (ρ : Fin 8) g j, (∀ q, hostAt ρ 0 q ≠ some (2, j)) → Hb ρ 2 1 g j = Hp ρ 2 0 g j
  hHP_A3_1 : ∀ (ρ : Fin 8) g j, GReach (Hb ρ 2 1 g j) (Hp ρ 2 1 g j) (fun _ => 0)
  hHZ_A3_1 : ∀ (ρ : Fin 8) g q j, hostAt ρ 1 q = some (2, j) → Wn1 ρ g q * Hp ρ 2 1 g j = Hb ρ 2 2 g j
  hHZn_A3_1 : ∀ (ρ : Fin 8) g j, (∀ q, hostAt ρ 1 q ≠ some (2, j)) → Hb ρ 2 2 g j = Hp ρ 2 1 g j
  hHP_A3_2 : ∀ (ρ : Fin 8) g j, GReach (Hb ρ 2 2 g j) (Hp ρ 2 2 g j) (fun _ => 0)
  hHZ_A3_2 : ∀ (ρ : Fin 8) g q j, hostAt ρ 2 q = some (2, j) → Wn2 ρ g q * Hp ρ 2 2 g j = Hb ρ 2 3 g j
  hHZn_A3_2 : ∀ (ρ : Fin 8) g j, (∀ q, hostAt ρ 2 q ≠ some (2, j)) → Hb ρ 2 3 g j = Hp ρ 2 2 g j
  hHP_A3_3 : ∀ (ρ : Fin 8) g j, GReach (Hb ρ 2 3 g j) (Hp ρ 2 3 g j) (fun _ => 0)
  hHZ_A3_3 : ∀ (ρ : Fin 8) g q j, hostAt ρ 3 q = some (2, j) → Wn3 ρ g q * Hp ρ 2 3 g j = Hb ρ 2 4 g j
  hHZn_A3_3 : ∀ (ρ : Fin 8) g j, (∀ q, hostAt ρ 3 q ≠ some (2, j)) → Hb ρ 2 4 g j = Hp ρ 2 3 g j
  hHE_A3 : ∀ (ρ : Fin 8) g t, GReach (Hb ρ 2 4 g (false, t)) ((G3 (r3 t g)).Xm.Φ 1) (fun φ => bcost φ (hrem ρ 2 (false, t))) ∧
    GReach (Hb ρ 2 4 g (true, t)) ((G3 (r3 t g)).Xm.Φ (1 + tt (I.tv t))) (fun φ => bcost φ (hrem ρ 2 (true, t)))
  hH0_B3 : ∀ (ρ : Fin 8) g t, Hb ρ 3 4 g (false, t) = (G4 (r4 t g)).Xm.Φ (tt (I.tv t)) ∧ Hb ρ 3 4 g (true, t) = (G4 (r4 t g)).Xm.Φ 0
  hHP_B3_4 : ∀ (ρ : Fin 8) g j, GReach (Hb ρ 3 4 g j) (Hp ρ 3 4 g j) (fun _ => 0)
  hHZ_B3_4 : ∀ (ρ : Fin 8) g q j, hostAt ρ 4 q = some (3, j) → Wn4 ρ g q * Hp ρ 3 4 g j = Hb ρ 3 5 g j
  hHZn_B3_4 : ∀ (ρ : Fin 8) g j, (∀ q, hostAt ρ 4 q ≠ some (3, j)) → Hb ρ 3 5 g j = Hp ρ 3 4 g j
  hHE_B3 : ∀ (ρ : Fin 8) g t, GReach (Hb ρ 3 5 g (false, t)) ((G4 (r4 t g)).Xm.Φ 1) (fun φ => bcost φ (hrem ρ 3 (false, t))) ∧
    GReach (Hb ρ 3 5 g (true, t)) ((G4 (r4 t g)).Xm.Φ (1 + tt (I.tv t))) (fun φ => bcost φ (hrem ρ 3 (true, t)))
  hH0_A4 : ∀ (ρ : Fin 8) g t, Hb ρ 4 0 g (false, t) = (G0 g).Xm.Φ (tt (I.tv t)) ∧ Hb ρ 4 0 g (true, t) = (G0 g).Xm.Φ 0
  hHP_A4_0 : ∀ (ρ : Fin 8) g j, GReach (Hb ρ 4 0 g j) (Hp ρ 4 0 g j) (fun _ => 0)
  hHZ_A4_0 : ∀ (ρ : Fin 8) g q j, hostAt ρ 0 q = some (4, j) → Wn0 ρ g q * Hp ρ 4 0 g j = Hb ρ 4 1 g j
  hHZn_A4_0 : ∀ (ρ : Fin 8) g j, (∀ q, hostAt ρ 0 q ≠ some (4, j)) → Hb ρ 4 1 g j = Hp ρ 4 0 g j
  hHP_A4_1 : ∀ (ρ : Fin 8) g j, GReach (Hb ρ 4 1 g j) (Hp ρ 4 1 g j) (fun _ => 0)
  hHZ_A4_1 : ∀ (ρ : Fin 8) g q j, hostAt ρ 1 q = some (4, j) → Wn1 ρ g q * Hp ρ 4 1 g j = Hb ρ 4 2 g j
  hHZn_A4_1 : ∀ (ρ : Fin 8) g j, (∀ q, hostAt ρ 1 q ≠ some (4, j)) → Hb ρ 4 2 g j = Hp ρ 4 1 g j
  hHP_A4_2 : ∀ (ρ : Fin 8) g j, GReach (Hb ρ 4 2 g j) (Hp ρ 4 2 g j) (fun _ => 0)
  hHZ_A4_2 : ∀ (ρ : Fin 8) g q j, hostAt ρ 2 q = some (4, j) → Wn2 ρ g q * Hp ρ 4 2 g j = Hb ρ 4 3 g j
  hHZn_A4_2 : ∀ (ρ : Fin 8) g j, (∀ q, hostAt ρ 2 q ≠ some (4, j)) → Hb ρ 4 3 g j = Hp ρ 4 2 g j
  hHP_A4_3 : ∀ (ρ : Fin 8) g j, GReach (Hb ρ 4 3 g j) (Hp ρ 4 3 g j) (fun _ => 0)
  hHZ_A4_3 : ∀ (ρ : Fin 8) g q j, hostAt ρ 3 q = some (4, j) → Wn3 ρ g q * Hp ρ 4 3 g j = Hb ρ 4 4 g j
  hHZn_A4_3 : ∀ (ρ : Fin 8) g j, (∀ q, hostAt ρ 3 q ≠ some (4, j)) → Hb ρ 4 4 g j = Hp ρ 4 3 g j
  hHP_A4_4 : ∀ (ρ : Fin 8) g j, GReach (Hb ρ 4 4 g j) (Hp ρ 4 4 g j) (fun _ => 0)
  hHZ_A4_4 : ∀ (ρ : Fin 8) g q j, hostAt ρ 4 q = some (4, j) → Wn4 ρ g q * Hp ρ 4 4 g j = Hb ρ 4 5 g j
  hHZn_A4_4 : ∀ (ρ : Fin 8) g j, (∀ q, hostAt ρ 4 q ≠ some (4, j)) → Hb ρ 4 5 g j = Hp ρ 4 4 g j
  hHP_A4_5 : ∀ (ρ : Fin 8) g j, GReach (Hb ρ 4 5 g j) (Hp ρ 4 5 g j) (fun _ => 0)
  hHZ_A4_5 : ∀ (ρ : Fin 8) g q j, hostAt ρ 5 q = some (4, j) → Wn5 ρ g q * Hp ρ 4 5 g j = Hb ρ 4 6 g j
  hHZn_A4_5 : ∀ (ρ : Fin 8) g j, (∀ q, hostAt ρ 5 q ≠ some (4, j)) → Hb ρ 4 6 g j = Hp ρ 4 5 g j
  hHE_A4 : ∀ (ρ : Fin 8) g t, GReach (Hb ρ 4 6 g (false, t)) ((G5 (r5 t g)).Xm.Φ 1) (fun φ => bcost φ (hrem ρ 4 (false, t))) ∧
    GReach (Hb ρ 4 6 g (true, t)) ((G5 (r5 t g)).Xm.Φ (1 + tt (I.tv t))) (fun φ => bcost φ (hrem ρ 4 (true, t)))
  hH0_B4 : ∀ (ρ : Fin 8) g t, Hb ρ 5 6 g (false, t) = (G6 (r6 t g)).Xm.Φ (tt (I.tv t)) ∧ Hb ρ 5 6 g (true, t) = (G6 (r6 t g)).Xm.Φ 0
  hHP_B4_6 : ∀ (ρ : Fin 8) g j, GReach (Hb ρ 5 6 g j) (Hp ρ 5 6 g j) (fun _ => 0)
  hHZ_B4_6 : ∀ (ρ : Fin 8) g q j, hostAt ρ 6 q = some (5, j) → Wn6 ρ g q * Hp ρ 5 6 g j = Hb ρ 5 7 g j
  hHZn_B4_6 : ∀ (ρ : Fin 8) g j, (∀ q, hostAt ρ 6 q ≠ some (5, j)) → Hb ρ 5 7 g j = Hp ρ 5 6 g j
  hHE_B4 : ∀ (ρ : Fin 8) g t, GReach (Hb ρ 5 7 g (false, t)) ((G6 (r6 t g)).Xm.Φ 1) (fun φ => bcost φ (hrem ρ 5 (false, t))) ∧
    GReach (Hb ρ 5 7 g (true, t)) ((G6 (r6 t g)).Xm.Φ (1 + tt (I.tv t))) (fun φ => bcost φ (hrem ρ 5 (true, t)))
  hH0_F1 : ∀ (ρ : Fin 8) g t, Hb ρ 6 3 g (false, t) = (G2 (r2 t g)).Xm.Φ 1 ∧ Hb ρ 6 3 g (true, t) = (G2 (r2 t g)).Xm.Φ (1 + tt (I.tv t))
  hHP_F1_3 : ∀ (ρ : Fin 8) g j, GReach (Hb ρ 6 3 g j) (Hp ρ 6 3 g j) (fun _ => 0)
  hHZ_F1_3 : ∀ (ρ : Fin 8) g q j, hostAt ρ 3 q = some (6, j) → Wn3 ρ g q * Hp ρ 6 3 g j = Hb ρ 6 4 g j
  hHZn_F1_3 : ∀ (ρ : Fin 8) g j, (∀ q, hostAt ρ 3 q ≠ some (6, j)) → Hb ρ 6 4 g j = Hp ρ 6 3 g j
  hHP_F1_4 : ∀ (ρ : Fin 8) g j, GReach (Hb ρ 6 4 g j) (Hp ρ 6 4 g j) (fun _ => 0)
  hHZ_F1_4 : ∀ (ρ : Fin 8) g q j, hostAt ρ 4 q = some (6, j) → Wn4 ρ g q * Hp ρ 6 4 g j = Hb ρ 6 5 g j
  hHZn_F1_4 : ∀ (ρ : Fin 8) g j, (∀ q, hostAt ρ 4 q ≠ some (6, j)) → Hb ρ 6 5 g j = Hp ρ 6 4 g j
  hHP_F1_5 : ∀ (ρ : Fin 8) g j, GReach (Hb ρ 6 5 g j) (Hp ρ 6 5 g j) (fun _ => 0)
  hHZ_F1_5 : ∀ (ρ : Fin 8) g q j, hostAt ρ 5 q = some (6, j) → Wn5 ρ g q * Hp ρ 6 5 g j = Hb ρ 6 6 g j
  hHZn_F1_5 : ∀ (ρ : Fin 8) g j, (∀ q, hostAt ρ 5 q ≠ some (6, j)) → Hb ρ 6 6 g j = Hp ρ 6 5 g j
  hHP_F1_6 : ∀ (ρ : Fin 8) g j, GReach (Hb ρ 6 6 g j) (Hp ρ 6 6 g j) (fun _ => 0)
  hHZ_F1_6 : ∀ (ρ : Fin 8) g q j, hostAt ρ 6 q = some (6, j) → Wn6 ρ g q * Hp ρ 6 6 g j = Hb ρ 6 7 g j
  hHZn_F1_6 : ∀ (ρ : Fin 8) g j, (∀ q, hostAt ρ 6 q ≠ some (6, j)) → Hb ρ 6 7 g j = Hp ρ 6 6 g j
  hHP_F1_7 : ∀ (ρ : Fin 8) g j, GReach (Hb ρ 6 7 g j) (Hp ρ 6 7 g j) (fun _ => 0)
  hHZ_F1_7 : ∀ (ρ : Fin 8) g q j, hostAt ρ 7 q = some (6, j) → Wn7 ρ g q * Hp ρ 6 7 g j = Hb ρ 6 8 g j
  hHZn_F1_7 : ∀ (ρ : Fin 8) g j, (∀ q, hostAt ρ 7 q ≠ some (6, j)) → Hb ρ 6 8 g j = Hp ρ 6 7 g j
  hHP_F1_8 : ∀ (ρ : Fin 8) g j, GReach (Hb ρ 6 8 g j) (Hp ρ 6 8 g j) (fun _ => 0)
  hHZ_F1_8 : ∀ (ρ : Fin 8) g q j, hostAt ρ 8 q = some (6, j) → Wn8 ρ g q * Hp ρ 6 8 g j = Hb ρ 6 9 g j
  hHZn_F1_8 : ∀ (ρ : Fin 8) g j, (∀ q, hostAt ρ 8 q ≠ some (6, j)) → Hb ρ 6 9 g j = Hp ρ 6 8 g j
  hHE_F1 : ∀ (ρ : Fin 8) g t, GReach (Hb ρ 6 9 g (false, t)) (kernel α) (fun φ => bcost φ (hrem ρ 6 (false, t))) ∧
    GReach (Hb ρ 6 9 g (true, t)) (YF g t) (fun φ => bcost φ (hrem ρ 6 (true, t)))
  hH0_F2 : ∀ (ρ : Fin 8) g t, Hb ρ 7 5 g (false, t) = (G4 (r4 t g)).Xm.Φ 1 ∧ Hb ρ 7 5 g (true, t) = (G4 (r4 t g)).Xm.Φ (1 + tt (I.tv t))
  hHP_F2_5 : ∀ (ρ : Fin 8) g j, GReach (Hb ρ 7 5 g j) (Hp ρ 7 5 g j) (fun _ => 0)
  hHZ_F2_5 : ∀ (ρ : Fin 8) g q j, hostAt ρ 5 q = some (7, j) → Wn5 ρ g q * Hp ρ 7 5 g j = Hb ρ 7 6 g j
  hHZn_F2_5 : ∀ (ρ : Fin 8) g j, (∀ q, hostAt ρ 5 q ≠ some (7, j)) → Hb ρ 7 6 g j = Hp ρ 7 5 g j
  hHP_F2_6 : ∀ (ρ : Fin 8) g j, GReach (Hb ρ 7 6 g j) (Hp ρ 7 6 g j) (fun _ => 0)
  hHZ_F2_6 : ∀ (ρ : Fin 8) g q j, hostAt ρ 6 q = some (7, j) → Wn6 ρ g q * Hp ρ 7 6 g j = Hb ρ 7 7 g j
  hHZn_F2_6 : ∀ (ρ : Fin 8) g j, (∀ q, hostAt ρ 6 q ≠ some (7, j)) → Hb ρ 7 7 g j = Hp ρ 7 6 g j
  hHP_F2_7 : ∀ (ρ : Fin 8) g j, GReach (Hb ρ 7 7 g j) (Hp ρ 7 7 g j) (fun _ => 0)
  hHZ_F2_7 : ∀ (ρ : Fin 8) g q j, hostAt ρ 7 q = some (7, j) → Wn7 ρ g q * Hp ρ 7 7 g j = Hb ρ 7 8 g j
  hHZn_F2_7 : ∀ (ρ : Fin 8) g j, (∀ q, hostAt ρ 7 q ≠ some (7, j)) → Hb ρ 7 8 g j = Hp ρ 7 7 g j
  hHP_F2_8 : ∀ (ρ : Fin 8) g j, GReach (Hb ρ 7 8 g j) (Hp ρ 7 8 g j) (fun _ => 0)
  hHZ_F2_8 : ∀ (ρ : Fin 8) g q j, hostAt ρ 8 q = some (7, j) → Wn8 ρ g q * Hp ρ 7 8 g j = Hb ρ 7 9 g j
  hHZn_F2_8 : ∀ (ρ : Fin 8) g j, (∀ q, hostAt ρ 8 q ≠ some (7, j)) → Hb ρ 7 9 g j = Hp ρ 7 8 g j
  hHE_F2 : ∀ (ρ : Fin 8) g t, GReach (Hb ρ 7 9 g (false, t)) (kernel α) (fun φ => bcost φ (hrem ρ 7 (false, t))) ∧
    GReach (Hb ρ 7 9 g (true, t)) (YF g t) (fun φ => bcost φ (hrem ρ 7 (true, t)))
  hH0_F3 : ∀ (ρ : Fin 8) g t, Hb ρ 8 7 g (false, t) = (G6 (r6 t g)).Xm.Φ 1 ∧ Hb ρ 8 7 g (true, t) = (G6 (r6 t g)).Xm.Φ (1 + tt (I.tv t))
  hHP_F3_7 : ∀ (ρ : Fin 8) g j, GReach (Hb ρ 8 7 g j) (Hp ρ 8 7 g j) (fun _ => 0)
  hHZ_F3_7 : ∀ (ρ : Fin 8) g q j, hostAt ρ 7 q = some (8, j) → Wn7 ρ g q * Hp ρ 8 7 g j = Hb ρ 8 8 g j
  hHZn_F3_7 : ∀ (ρ : Fin 8) g j, (∀ q, hostAt ρ 7 q ≠ some (8, j)) → Hb ρ 8 8 g j = Hp ρ 8 7 g j
  hHP_F3_8 : ∀ (ρ : Fin 8) g j, GReach (Hb ρ 8 8 g j) (Hp ρ 8 8 g j) (fun _ => 0)
  hHZ_F3_8 : ∀ (ρ : Fin 8) g q j, hostAt ρ 8 q = some (8, j) → Wn8 ρ g q * Hp ρ 8 8 g j = Hb ρ 8 9 g j
  hHZn_F3_8 : ∀ (ρ : Fin 8) g j, (∀ q, hostAt ρ 8 q ≠ some (8, j)) → Hb ρ 8 9 g j = Hp ρ 8 8 g j
  hHE_F3 : ∀ (ρ : Fin 8) g t, GReach (Hb ρ 8 9 g (false, t)) (kernel α) (fun φ => bcost φ (hrem ρ 8 (false, t))) ∧
    GReach (Hb ρ 8 9 g (true, t)) (YF g t) (fun φ => bcost φ (hrem ρ 8 (true, t)))
  /-- pair 4 after stage 8: ONE final block (not hosted). -/
  fX4 : ∀ g t, XReach ((G8 (r8 t g)).Xm.Φ 1) (kernel α) cX4
  fY4 : ∀ g t, XReach ((G8 (r8 t g)).Xm.Φ (1 + tt (I.tv t))) (YF g t) cY4
  term : ∀ g t, kernel α * (G0 g).Xm.Φ (tt (I.tv t)) = shift (u g t) * YF g t

section Net
variable {H T Sl C α Γ : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C] [Fintype α] [DecidableEq α]
  [Fintype Γ] [DecidableEq Γ]
variable {nb : ℕ} (N : GHost401 H T Sl C α Γ nb)

/-- price of the remaining climbs of the host chains of kind `c` (both sides, all classes), per element of `Γ`. -/
def GHost401.hcost (ρ : Fin 8) (c : Fin 9) (φ : ℕ → ℝ) : ℝ :=
  ∑ t : T, (bcost φ (N.hrem ρ c (false, t)) + bcost φ (N.hrem ρ c (true, t)))

/-- price of run `ρ` per element of `Γ`: its 9 calls (each its own provider's price), the remaining climbs of run `ρ`, pair 4's final. -/
def GHost401.runUnit (ρ : Fin 8) (φ : ℕ → ℝ) : ℝ :=
  (N.Ic ρ 0).cost φ + (N.Ic ρ 1).cost φ + (N.Ic ρ 2).cost φ + (N.Ic ρ 3).cost φ + (N.Ic ρ 4).cost φ + (N.Ic ρ 5).cost φ + (N.Ic ρ 6).cost φ + (N.Ic ρ 7).cost φ + (N.Ic ρ 8).cost φ
    + (N.hcost ρ 0 φ + N.hcost ρ 1 φ + N.hcost ρ 2 φ + N.hcost ρ 3 φ + N.hcost ρ 4 φ + N.hcost ρ 5 φ
    + N.hcost ρ 6 φ + N.hcost ρ 7 φ + N.hcost ρ 8 φ) + (Fintype.card T : ℝ) * (N.cX4 φ + N.cY4 φ)

/-- price of one unit (one element of `Γ`): the 8 runs (each with its own remaining climbs) and the padding blocks. -/
def GHost401.unit (φ : ℕ → ℝ) : ℝ :=
  (∑ ρ : Fin 8, N.runUnit ρ φ) + ∑ b, bcost φ (N.pad b)

/-- the invocation of call `(ρ, l)` with the target vectors of `I` DEFINITIONALLY (`retagTv`). -/
def GHost401.Jc (ρ : Fin 8) (l : Fin 9) : GInvE H T Sl C := XHostD.retagTv (N.Ic ρ l) N.I.tv (N.hIc ρ l)

/-- the conditions of the role map of stage `l`. -/
lemma GHost401.hok (ρ : Fin 8) (l : Fin 9) : HostOK (pairL l.val) (N.hostAt ρ l) (N.bk ρ l) :=
  ⟨N.hinj ρ l, N.hostInj ρ l, fun q c j h => win_pair c l (N.hostWin ρ l q c j h),
    fun q q' c c' j j' h h' e => win_uniq c c' l (N.hostWin ρ l q c j h) (N.hostWin ρ l q' c' j' h') e⟩

def GHost401.xi0 (g : Γ) (t : T) : CMat α := (N.G0 g).Xm.Φ (tt (N.I.tv t))
def GHost401.yi0 (g : Γ) (t : T) : CMat α := (N.G0 g).Xm.Φ 0
def GHost401.xi1 (g : Γ) (t : T) : CMat α := (N.G1 (N.r1 t g)).Xm.Φ (tt (N.I.tv t))
def GHost401.yi1 (g : Γ) (t : T) : CMat α := (N.G1 (N.r1 t g)).Xm.Φ 0
def GHost401.xi2 (g : Γ) (t : T) : CMat α := (N.G2 (N.r2 t g)).Xm.Φ (tt (N.I.tv t))
def GHost401.yi2 (g : Γ) (t : T) : CMat α := (N.G2 (N.r2 t g)).Xm.Φ 0
def GHost401.xi3 (g : Γ) (t : T) : CMat α := (N.G3 (N.r3 t g)).Xm.Φ (tt (N.I.tv t))
def GHost401.yi3 (g : Γ) (t : T) : CMat α := (N.G3 (N.r3 t g)).Xm.Φ 0
def GHost401.xi4 (g : Γ) (t : T) : CMat α := (N.G4 (N.r4 t g)).Xm.Φ (tt (N.I.tv t))
def GHost401.yi4 (g : Γ) (t : T) : CMat α := (N.G4 (N.r4 t g)).Xm.Φ 0
def GHost401.xi5 (g : Γ) (t : T) : CMat α := (N.G5 (N.r5 t g)).Xm.Φ (tt (N.I.tv t))
def GHost401.yi5 (g : Γ) (t : T) : CMat α := (N.G5 (N.r5 t g)).Xm.Φ 0
def GHost401.xi6 (g : Γ) (t : T) : CMat α := (N.G6 (N.r6 t g)).Xm.Φ (tt (N.I.tv t))
def GHost401.yi6 (g : Γ) (t : T) : CMat α := (N.G6 (N.r6 t g)).Xm.Φ 0
def GHost401.xi7 (g : Γ) (t : T) : CMat α := (N.G7 (N.r7 t g)).Xm.Φ (tt (N.I.tv t))
def GHost401.yi7 (g : Γ) (t : T) : CMat α := (N.G7 (N.r7 t g)).Xm.Φ 0
def GHost401.xi8 (g : Γ) (t : T) : CMat α := (N.G8 (N.r8 t g)).Xm.Φ (tt (N.I.tv t))
def GHost401.yi8 (g : Γ) (t : T) : CMat α := (N.G8 (N.r8 t g)).Xm.Φ 0
def GHost401.xo2 (g : Γ) (t : T) : CMat α := (N.G2 (N.r2 t g)).Xm.Φ 1
def GHost401.yo2 (g : Γ) (t : T) : CMat α := (N.G2 (N.r2 t g)).Xm.Φ (1 + tt (N.I.tv t))
def GHost401.xo4 (g : Γ) (t : T) : CMat α := (N.G4 (N.r4 t g)).Xm.Φ 1
def GHost401.yo4 (g : Γ) (t : T) : CMat α := (N.G4 (N.r4 t g)).Xm.Φ (1 + tt (N.I.tv t))
def GHost401.xo6 (g : Γ) (t : T) : CMat α := (N.G6 (N.r6 t g)).Xm.Φ 1
def GHost401.yo6 (g : Γ) (t : T) : CMat α := (N.G6 (N.r6 t g)).Xm.Φ (1 + tt (N.I.tv t))
def GHost401.xo8 (g : Γ) (t : T) : CMat α := (N.G8 (N.r8 t g)).Xm.Φ 1
def GHost401.yo8 (g : Γ) (t : T) : CMat α := (N.G8 (N.r8 t g)).Xm.Φ (1 + tt (N.I.tv t))

/-- the data of a replica before its run and after it. -/
def GHost401.InitD : BDat4 Γ T → CMat α := mkD4 N.xi0 N.yi0 N.xi0 N.yi0 N.xi0 N.yi0 N.xi0 N.yi0
def GHost401.FinD : BDat4 Γ T → CMat α := mkD4 (fun _ _ => kernel α) N.YF (fun _ _ => kernel α) N.YF (fun _ _ => kernel α) N.YF (fun _ _ => kernel α) N.YF

def GHost401.S0 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xi0 N.yi0 N.xi0 N.yi0 N.xi0 N.yi0 N.xi0 N.yi0 (fun g b => N.Zb (9 * ρ.val + 0) g b) (cOne Γ C α)
def GHost401.S1 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xi0 N.yi0 (fun g t => N.Hp ρ 0 0 g (false, t)) (fun g t => N.Hp ρ 0 0 g (true, t)) (fun g t => N.Hp ρ 2 0 g (false, t)) (fun g t => N.Hp ρ 2 0 g (true, t)) (fun g t => N.Hp ρ 4 0 g (false, t)) (fun g t => N.Hp ρ 4 0 g (true, t)) (fun g b => N.Zp (9 * ρ.val + 0) g b) (cOne Γ C α)
def GHost401.S2 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xi1 N.yi1 (fun g t => N.Hb ρ 0 1 g (false, t)) (fun g t => N.Hb ρ 0 1 g (true, t)) (fun g t => N.Hb ρ 2 1 g (false, t)) (fun g t => N.Hb ρ 2 1 g (true, t)) (fun g t => N.Hb ρ 4 1 g (false, t)) (fun g t => N.Hb ρ 4 1 g (true, t)) (fun g b => N.Zb (9 * ρ.val + 1) g b) (cOne Γ C α)
def GHost401.S3 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xi1 N.yi1 (fun g t => N.Hp ρ 0 1 g (false, t)) (fun g t => N.Hp ρ 0 1 g (true, t)) (fun g t => N.Hp ρ 2 1 g (false, t)) (fun g t => N.Hp ρ 2 1 g (true, t)) (fun g t => N.Hp ρ 4 1 g (false, t)) (fun g t => N.Hp ρ 4 1 g (true, t)) (fun g b => N.Zp (9 * ρ.val + 1) g b) (cOne Γ C α)
def GHost401.S4 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xi2 N.yi2 (fun g t => N.Hb ρ 0 2 g (false, t)) (fun g t => N.Hb ρ 0 2 g (true, t)) (fun g t => N.Hb ρ 2 2 g (false, t)) (fun g t => N.Hb ρ 2 2 g (true, t)) (fun g t => N.Hb ρ 4 2 g (false, t)) (fun g t => N.Hb ρ 4 2 g (true, t)) (fun g b => N.Zb (9 * ρ.val + 2) g b) (cOne Γ C α)
def GHost401.S5 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xi2 N.yi2 N.xi2 N.yi2 (fun g t => N.Hb ρ 2 2 g (false, t)) (fun g t => N.Hb ρ 2 2 g (true, t)) (fun g t => N.Hb ρ 4 2 g (false, t)) (fun g t => N.Hb ρ 4 2 g (true, t)) (fun g b => N.Zb (9 * ρ.val + 2) g b) (cOne Γ C α)
def GHost401.S6 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xi2 N.yi2 (fun g t => N.Hp ρ 1 2 g (false, t)) (fun g t => N.Hp ρ 1 2 g (true, t)) (fun g t => N.Hp ρ 2 2 g (false, t)) (fun g t => N.Hp ρ 2 2 g (true, t)) (fun g t => N.Hp ρ 4 2 g (false, t)) (fun g t => N.Hp ρ 4 2 g (true, t)) (fun g b => N.Zp (9 * ρ.val + 2) g b) (cOne Γ C α)
def GHost401.S7 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xo2 N.yo2 (fun g t => N.Hb ρ 1 3 g (false, t)) (fun g t => N.Hb ρ 1 3 g (true, t)) (fun g t => N.Hb ρ 2 3 g (false, t)) (fun g t => N.Hb ρ 2 3 g (true, t)) (fun g t => N.Hb ρ 4 3 g (false, t)) (fun g t => N.Hb ρ 4 3 g (true, t)) (fun g b => N.Zb (9 * ρ.val + 3) g b) (cOne Γ C α)
def GHost401.S8 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xo2 N.yo2 N.xi3 N.yi3 (fun g t => N.Hb ρ 2 3 g (false, t)) (fun g t => N.Hb ρ 2 3 g (true, t)) (fun g t => N.Hb ρ 4 3 g (false, t)) (fun g t => N.Hb ρ 4 3 g (true, t)) (fun g b => N.Zb (9 * ρ.val + 3) g b) (cOne Γ C α)
def GHost401.S9 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 (fun g t => N.Hp ρ 6 3 g (false, t)) (fun g t => N.Hp ρ 6 3 g (true, t)) N.xi3 N.yi3 (fun g t => N.Hp ρ 2 3 g (false, t)) (fun g t => N.Hp ρ 2 3 g (true, t)) (fun g t => N.Hp ρ 4 3 g (false, t)) (fun g t => N.Hp ρ 4 3 g (true, t)) (fun g b => N.Zp (9 * ρ.val + 3) g b) (cOne Γ C α)
def GHost401.S10 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 (fun g t => N.Hb ρ 6 4 g (false, t)) (fun g t => N.Hb ρ 6 4 g (true, t)) N.xi4 N.yi4 (fun g t => N.Hb ρ 2 4 g (false, t)) (fun g t => N.Hb ρ 2 4 g (true, t)) (fun g t => N.Hb ρ 4 4 g (false, t)) (fun g t => N.Hb ρ 4 4 g (true, t)) (fun g b => N.Zb (9 * ρ.val + 4) g b) (cOne Γ C α)
def GHost401.S11 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 (fun g t => N.Hb ρ 6 4 g (false, t)) (fun g t => N.Hb ρ 6 4 g (true, t)) N.xi4 N.yi4 N.xi4 N.yi4 (fun g t => N.Hb ρ 4 4 g (false, t)) (fun g t => N.Hb ρ 4 4 g (true, t)) (fun g b => N.Zb (9 * ρ.val + 4) g b) (cOne Γ C α)
def GHost401.S12 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 (fun g t => N.Hp ρ 6 4 g (false, t)) (fun g t => N.Hp ρ 6 4 g (true, t)) N.xi4 N.yi4 (fun g t => N.Hp ρ 3 4 g (false, t)) (fun g t => N.Hp ρ 3 4 g (true, t)) (fun g t => N.Hp ρ 4 4 g (false, t)) (fun g t => N.Hp ρ 4 4 g (true, t)) (fun g b => N.Zp (9 * ρ.val + 4) g b) (cOne Γ C α)
def GHost401.S13 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 (fun g t => N.Hb ρ 6 5 g (false, t)) (fun g t => N.Hb ρ 6 5 g (true, t)) N.xo4 N.yo4 (fun g t => N.Hb ρ 3 5 g (false, t)) (fun g t => N.Hb ρ 3 5 g (true, t)) (fun g t => N.Hb ρ 4 5 g (false, t)) (fun g t => N.Hb ρ 4 5 g (true, t)) (fun g b => N.Zb (9 * ρ.val + 5) g b) (cOne Γ C α)
def GHost401.S14 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 (fun g t => N.Hb ρ 6 5 g (false, t)) (fun g t => N.Hb ρ 6 5 g (true, t)) N.xo4 N.yo4 N.xi5 N.yi5 (fun g t => N.Hb ρ 4 5 g (false, t)) (fun g t => N.Hb ρ 4 5 g (true, t)) (fun g b => N.Zb (9 * ρ.val + 5) g b) (cOne Γ C α)
def GHost401.S15 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 (fun g t => N.Hp ρ 6 5 g (false, t)) (fun g t => N.Hp ρ 6 5 g (true, t)) (fun g t => N.Hp ρ 7 5 g (false, t)) (fun g t => N.Hp ρ 7 5 g (true, t)) N.xi5 N.yi5 (fun g t => N.Hp ρ 4 5 g (false, t)) (fun g t => N.Hp ρ 4 5 g (true, t)) (fun g b => N.Zp (9 * ρ.val + 5) g b) (cOne Γ C α)
def GHost401.S16 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 (fun g t => N.Hb ρ 6 6 g (false, t)) (fun g t => N.Hb ρ 6 6 g (true, t)) (fun g t => N.Hb ρ 7 6 g (false, t)) (fun g t => N.Hb ρ 7 6 g (true, t)) N.xi6 N.yi6 (fun g t => N.Hb ρ 4 6 g (false, t)) (fun g t => N.Hb ρ 4 6 g (true, t)) (fun g b => N.Zb (9 * ρ.val + 6) g b) (cOne Γ C α)
def GHost401.S17 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 (fun g t => N.Hb ρ 6 6 g (false, t)) (fun g t => N.Hb ρ 6 6 g (true, t)) (fun g t => N.Hb ρ 7 6 g (false, t)) (fun g t => N.Hb ρ 7 6 g (true, t)) N.xi6 N.yi6 N.xi6 N.yi6 (fun g b => N.Zb (9 * ρ.val + 6) g b) (cOne Γ C α)
def GHost401.S18 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 (fun g t => N.Hp ρ 6 6 g (false, t)) (fun g t => N.Hp ρ 6 6 g (true, t)) (fun g t => N.Hp ρ 7 6 g (false, t)) (fun g t => N.Hp ρ 7 6 g (true, t)) N.xi6 N.yi6 (fun g t => N.Hp ρ 5 6 g (false, t)) (fun g t => N.Hp ρ 5 6 g (true, t)) (fun g b => N.Zp (9 * ρ.val + 6) g b) (cOne Γ C α)
def GHost401.S19 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 (fun g t => N.Hb ρ 6 7 g (false, t)) (fun g t => N.Hb ρ 6 7 g (true, t)) (fun g t => N.Hb ρ 7 7 g (false, t)) (fun g t => N.Hb ρ 7 7 g (true, t)) N.xo6 N.yo6 (fun g t => N.Hb ρ 5 7 g (false, t)) (fun g t => N.Hb ρ 5 7 g (true, t)) (fun g b => N.Zb (9 * ρ.val + 7) g b) (cOne Γ C α)
def GHost401.S20 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 (fun g t => N.Hb ρ 6 7 g (false, t)) (fun g t => N.Hb ρ 6 7 g (true, t)) (fun g t => N.Hb ρ 7 7 g (false, t)) (fun g t => N.Hb ρ 7 7 g (true, t)) N.xo6 N.yo6 N.xi7 N.yi7 (fun g b => N.Zb (9 * ρ.val + 7) g b) (cOne Γ C α)
def GHost401.S21 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 (fun g t => N.Hp ρ 6 7 g (false, t)) (fun g t => N.Hp ρ 6 7 g (true, t)) (fun g t => N.Hp ρ 7 7 g (false, t)) (fun g t => N.Hp ρ 7 7 g (true, t)) (fun g t => N.Hp ρ 8 7 g (false, t)) (fun g t => N.Hp ρ 8 7 g (true, t)) N.xi7 N.yi7 (fun g b => N.Zp (9 * ρ.val + 7) g b) (cOne Γ C α)
def GHost401.S22 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 (fun g t => N.Hb ρ 6 8 g (false, t)) (fun g t => N.Hb ρ 6 8 g (true, t)) (fun g t => N.Hb ρ 7 8 g (false, t)) (fun g t => N.Hb ρ 7 8 g (true, t)) (fun g t => N.Hb ρ 8 8 g (false, t)) (fun g t => N.Hb ρ 8 8 g (true, t)) N.xi8 N.yi8 (fun g b => N.Zb (9 * ρ.val + 8) g b) (cOne Γ C α)
def GHost401.S23 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 (fun g t => N.Hp ρ 6 8 g (false, t)) (fun g t => N.Hp ρ 6 8 g (true, t)) (fun g t => N.Hp ρ 7 8 g (false, t)) (fun g t => N.Hp ρ 7 8 g (true, t)) (fun g t => N.Hp ρ 8 8 g (false, t)) (fun g t => N.Hp ρ 8 8 g (true, t)) N.xi8 N.yi8 (fun g b => N.Zp (9 * ρ.val + 8) g b) (cOne Γ C α)
def GHost401.S24 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 (fun g t => N.Hb ρ 6 9 g (false, t)) (fun g t => N.Hb ρ 6 9 g (true, t)) (fun g t => N.Hb ρ 7 9 g (false, t)) (fun g t => N.Hb ρ 7 9 g (true, t)) (fun g t => N.Hb ρ 8 9 g (false, t)) (fun g t => N.Hb ρ 8 9 g (true, t)) N.xo8 N.yo8 (fun g b => N.Zb (9 * ρ.val + 9) g b) (cOne Γ C α)
def GHost401.S25 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 (fun _ _ => kernel α) N.YF (fun _ _ => kernel α) N.YF (fun _ _ => kernel α) N.YF (fun _ _ => kernel α) N.YF (fun g b => N.Zb (9 * ρ.val + 9) g b) (cOne Γ C α)

/-- frames of all roles at the start of run `k` (`k = 8`: after the last run). -/
def GHost401.Sfull (k : Fin 9) : BRole401 Γ T nb C → CMat α :=
  mk401 (fun ρ' d => if ρ'.val < k.val then N.FinD d else N.InitD d) (fun g b => N.Zb (9 * k.val) g b) (cOne Γ C α)

/-- frames of all roles after the padding climbs. -/
def GHost401.Sfin : BRole401 Γ T nb C → CMat α :=
  mk401 (fun _ d => N.FinD d) (fun _ _ => kernel α) (cOne Γ C α)

end Net
end
end XHostD
end PowerSaving
end OAI

end
-- bos_merge: end Submission.Work.XHostD.HDef

-- bos_merge: begin Submission.Work.XHostD.HStage
section

/-!
# (key: bridge-host) The steps of one run of the HOSTED nine-stage word

Copy of Work/Bridge401/GNetStage.lean (Shea's complex588 tree; written by Nil Mamano's gen401.py) with same-run hosting:
the adapters also move every host of a window (`hHP`), a stage puts its slots on banks or hosts (`ghliftQ<l>`), the
idle climbs are the remaining climbs of the host chains (`hHE`), and the finals of pairs 1-3 are those of F1-F3.
The gate layers are Shea's, word for word.  Written by h-L3-build/gen/gen_hnet.py, prepared with assistance from
Claude.  PER-RUN version (one host table per run) written by fsp-perrun/tools/mk_perrun.py (wht43, 14 Oct 2026) from h-L3-build's file by checked text substitution; prepared with assistance from Claude.  TWO-PROVIDER version (a per-call invocation `Ic ρ l` with the target vectors of `I`, per-call entrance labels and residuals) written by lg-a2a4/tools/mk_disp.py (wht43, 14 Oct 2026) from fsp-perrun's file by checked text substitution; prepared with assistance from Claude.  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
namespace OAI
namespace PowerSaving
namespace XHostD
open Binary Matrix Finset RAM SS CB RF BR GF GX XHost
noncomputable section

section Net
variable {H T Sl C α Γ : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C] [Fintype α] [DecidableEq α]
  [Fintype Γ] [DecidableEq Γ]
variable {nb : ℕ} (N : GHost401 H T Sl C α Γ nb)

/-- the free adapters before stage 0 of run `ρ`: every bank from `Zb` to `Zp`, every host of a window. -/
lemma GHost401.adapt0 (ρ : Fin 8) :
    GRoute (N.S0 ρ) (N.S1 ρ) id (fun _ => 0) := by
  have H1 := GRoute.reach_all (N.S0 ρ) (N.S1 ρ) (fun _ _ => 0) (by
      rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
      · exact GReach.refl _
      · exact GReach.refl _
      · show GReach ((N.G0 g).Xm.Φ (tt (N.I.tv t))) (N.Hp ρ 0 0 g (false, t)) (fun _ => 0)
        rw [← (N.hH0_A2 ρ g t).1]
        exact N.hHP_A2_0 ρ g (false, t)
      · show GReach ((N.G0 g).Xm.Φ 0) (N.Hp ρ 0 0 g (true, t)) (fun _ => 0)
        rw [← (N.hH0_A2 ρ g t).2]
        exact N.hHP_A2_0 ρ g (true, t)
      · show GReach ((N.G0 g).Xm.Φ (tt (N.I.tv t))) (N.Hp ρ 2 0 g (false, t)) (fun _ => 0)
        rw [← (N.hH0_A3 ρ g t).1]
        exact N.hHP_A3_0 ρ g (false, t)
      · show GReach ((N.G0 g).Xm.Φ 0) (N.Hp ρ 2 0 g (true, t)) (fun _ => 0)
        rw [← (N.hH0_A3 ρ g t).2]
        exact N.hHP_A3_0 ρ g (true, t)
      · show GReach ((N.G0 g).Xm.Φ (tt (N.I.tv t))) (N.Hp ρ 4 0 g (false, t)) (fun _ => 0)
        rw [← (N.hH0_A4 ρ g t).1]
        exact N.hHP_A4_0 ρ g (false, t)
      · show GReach ((N.G0 g).Xm.Φ 0) (N.Hp ρ 4 0 g (true, t)) (fun _ => 0)
        rw [← (N.hH0_A4 ρ g t).2]
        exact N.hHP_A4_0 ρ g (true, t)
      · exact N.hP0 ρ g b
      · exact GReach.refl _)
  exact H1.cast (fun φ => by simp)

/-- stage 0 of run `ρ` (pair 1): the slot `q` of `g` on its bank or on its host. -/
lemma GHost401.stage0 (ρ : Fin 8) :
    GRoute (N.S1 ρ) (N.S2 ρ) (liftQ0 (Γ := Γ) (T := T) (C := C) (N.bk ρ 0) GF)
      (fun φ => (Fintype.card Γ : ℝ) * (N.Ic ρ 0).cost φ) := by
  have hUS : ∀ g q, N.Wn0 ρ g q * N.S1 ρ (slotR (N.hostAt ρ 0) (N.bk ρ 0) g q) = N.S2 ρ (slotR (N.hostAt ρ 0) (N.bk ρ 0) g q) := by
    intro g q
    rcases hq : N.hostAt ρ 0 q with _ | ⟨c, s, t⟩
    · rw [slotR_bank hq]
      exact N.hZ0 ρ g q hq
    · rw [slotR_host hq]
      have hw := N.hostWin ρ 0 q c (s, t) hq
      fin_cases c
      · cases s <;> exact N.hHZ_A2_0 ρ g q _ hq
      · exact absurd hw (by decide)
      · cases s <;> exact N.hHZ_A3_0 ρ g q _ hq
      · exact absurd hw (by decide)
      · cases s <;> exact N.hHZ_A4_0 ρ g q _ hq
      · exact absurd hw (by decide)
      · exact absurd hw (by decide)
      · exact absurd hw (by decide)
      · exact absurd hw (by decide)
  have h := gistageE_fwd (N.Jc ρ 0) (bid Γ T) N.G0 (N.N0 ρ) (N.Wn0 ρ) (N.hN0 ρ) (N.hW0 ρ)
    (fun g q => N.S1 ρ (slotR (N.hostAt ρ 0) (N.bk ρ 0) g q)) (cOne Γ C α) (cOne Γ C α)
  have h' : GRoute (bIn N.I.tv (bid Γ T) (fun d => (N.G0 d).Xm)
        (fun g q => N.S1 ρ (slotR (N.hostAt ρ 0) (N.bk ρ 0) g q)) (cOne Γ C α))
      (mkS N.xi1 N.yi1 (fun g q => N.S2 ρ (slotR (N.hostAt ρ 0) (N.bk ρ 0) g q)) (cOne Γ C α)) GF
      (fun φ => (Fintype.card Γ : ℝ) * (N.Ic ρ 0).cost φ) := by
    have e : bOut N.I.tv (bid Γ T) (fun d => (N.G0 d).Xm)
        (fun g q => N.Wn0 ρ g q * N.S1 ρ (slotR (N.hostAt ρ 0) (N.bk ρ 0) g q)) (cOne Γ C α)
        = mkS N.xi1 N.yi1 (fun g q => N.S2 ρ (slotR (N.hostAt ρ 0) (N.bk ρ 0) g q)) (cOne Γ C α) := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · exact N.x01 g t
      · exact N.y01 g t
      · exact hUS g q
      · rfl
    rw [← e]
    exact h
  refine ghliftQ0 (N.hostAt ρ 0) (N.bk ρ 0) (N.hok ρ 0) h' (fun g t => rfl) (fun g t => rfl)
    (fun g t => rfl) (fun g t => rfl) (fun g q => rfl) (fun g q => rfl) (fun g c => rfl) (fun g c => rfl) ?_
    (fun _ _ _ => rfl) GF_loc
  intro r hr
  rcases r with ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
  · exact absurd ((cover_iff _ _).mpr ⟨jX (g,t), rfl⟩) hr
  · exact absurd ((cover_iff _ _).mpr ⟨jY (g,t), rfl⟩) hr
  · exact (N.hHZn_A2_0 ρ g (false, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact (N.hHZn_A2_0 ρ g (true, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact (N.hHZn_A3_0 ρ g (false, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact (N.hHZn_A3_0 ρ g (true, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact (N.hHZn_A4_0 ρ g (false, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact (N.hHZn_A4_0 ρ g (true, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact (N.hZn0 ρ g b (fun q hq hb => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_bank hq, hb]; rfl⟩))).symm
  · exact absurd ((cover_iff _ _).mpr ⟨jC (g,c), rfl⟩) hr

/-- the free adapters before stage 1 of run `ρ`: every bank from `Zb` to `Zp`, every host of a window. -/
lemma GHost401.adapt1 (ρ : Fin 8) :
    GRoute (N.S2 ρ) (N.S3 ρ) id (fun _ => 0) := by
  have H1 := GRoute.reach_all (N.S2 ρ) (N.S3 ρ) (fun _ _ => 0) (by
      rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
      · exact GReach.refl _
      · exact GReach.refl _
      · exact N.hHP_A2_1 ρ g (false, t)
      · exact N.hHP_A2_1 ρ g (true, t)
      · exact N.hHP_A3_1 ρ g (false, t)
      · exact N.hHP_A3_1 ρ g (true, t)
      · exact N.hHP_A4_1 ρ g (false, t)
      · exact N.hHP_A4_1 ρ g (true, t)
      · exact N.hP1 ρ g b
      · exact GReach.refl _)
  exact H1.cast (fun φ => by simp)

/-- stage 1 of run `ρ` (pair 1): the slot `q` of `g` on its bank or on its host. -/
lemma GHost401.stage1 (ρ : Fin 8) :
    GRoute (N.S3 ρ) (N.S4 ρ) (liftQ1 (Γ := Γ) (T := T) (C := C) (N.bk ρ 1) GB)
      (fun φ => (Fintype.card Γ : ℝ) * (N.Ic ρ 1).cost φ) := by
  have hUS : ∀ g q, N.Wn1 ρ g q * N.S3 ρ (slotR (N.hostAt ρ 1) (N.bk ρ 1) g q) = N.S4 ρ (slotR (N.hostAt ρ 1) (N.bk ρ 1) g q) := by
    intro g q
    rcases hq : N.hostAt ρ 1 q with _ | ⟨c, s, t⟩
    · rw [slotR_bank hq]
      exact N.hZ1 ρ g q hq
    · rw [slotR_host hq]
      have hw := N.hostWin ρ 1 q c (s, t) hq
      fin_cases c
      · cases s <;> exact N.hHZ_A2_1 ρ g q _ hq
      · exact absurd hw (by decide)
      · cases s <;> exact N.hHZ_A3_1 ρ g q _ hq
      · exact absurd hw (by decide)
      · cases s <;> exact N.hHZ_A4_1 ρ g q _ hq
      · exact absurd hw (by decide)
      · exact absurd hw (by decide)
      · exact absurd hw (by decide)
      · exact absurd hw (by decide)
  have h := gistageE_bwd (N.Jc ρ 1) N.r1 N.G1 (N.N1 ρ) (N.Wn1 ρ) (N.hN1 ρ) (N.hW1 ρ)
    (fun g q => N.S3 ρ (slotR (N.hostAt ρ 1) (N.bk ρ 1) g q)) (cOne Γ C α) (cOne Γ C α)
  have h' : GRoute (bIn N.I.tv N.r1 (fun d => (N.G1 d).Xm)
        (fun g q => N.S3 ρ (slotR (N.hostAt ρ 1) (N.bk ρ 1) g q)) (cOne Γ C α))
      (mkS N.xi2 N.yi2 (fun g q => N.S4 ρ (slotR (N.hostAt ρ 1) (N.bk ρ 1) g q)) (cOne Γ C α)) GB
      (fun φ => (Fintype.card Γ : ℝ) * (N.Ic ρ 1).cost φ) := by
    have e : bOut N.I.tv N.r1 (fun d => (N.G1 d).Xm)
        (fun g q => N.Wn1 ρ g q * N.S3 ρ (slotR (N.hostAt ρ 1) (N.bk ρ 1) g q)) (cOne Γ C α)
        = mkS N.xi2 N.yi2 (fun g q => N.S4 ρ (slotR (N.hostAt ρ 1) (N.bk ρ 1) g q)) (cOne Γ C α) := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · exact N.x12 g t
      · exact N.y12 g t
      · exact hUS g q
      · rfl
    rw [← e]
    exact h
  refine ghliftQ1 (N.hostAt ρ 1) (N.bk ρ 1) (N.hok ρ 1) h' (fun g t => rfl) (fun g t => rfl)
    (fun g t => rfl) (fun g t => rfl) (fun g q => rfl) (fun g q => rfl) (fun g c => rfl) (fun g c => rfl) ?_
    (fun _ _ _ => rfl) GB_loc
  intro r hr
  rcases r with ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
  · exact absurd ((cover_iff _ _).mpr ⟨jX (g,t), rfl⟩) hr
  · exact absurd ((cover_iff _ _).mpr ⟨jY (g,t), rfl⟩) hr
  · exact (N.hHZn_A2_1 ρ g (false, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact (N.hHZn_A2_1 ρ g (true, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact (N.hHZn_A3_1 ρ g (false, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact (N.hHZn_A3_1 ρ g (true, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact (N.hHZn_A4_1 ρ g (false, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact (N.hHZn_A4_1 ρ g (true, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact (N.hZn1 ρ g b (fun q hq hb => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_bank hq, hb]; rfl⟩))).symm
  · exact absurd ((cover_iff _ _).mpr ⟨jC (g,c), rfl⟩) hr

/-- the remaining climb of the host chains A2 (pair 2): ONE block of rank `hrem 0 j` per role. -/
lemma GHost401.climbA2 (ρ : Fin 8) :
    GRoute (N.S4 ρ) (N.S5 ρ) id (fun φ => (Fintype.card Γ : ℝ) * N.hcost ρ 0 φ) := by
  have H1 := GRoute.reach_all (N.S4 ρ) (N.S5 ρ)
    (mkR4 (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ t φ => bcost φ (N.hrem ρ 0 (false, t))) (fun _ t φ => bcost φ (N.hrem ρ 0 (true, t))) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)) (by
      rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
      · exact GReach.refl _
      · exact GReach.refl _
      · show GReach (N.Hb ρ 0 2 g (false, t)) ((N.G2 (N.r2 t g)).Xm.Φ (tt (N.I.tv t))) (fun φ => bcost φ (N.hrem ρ 0 (false, t)))
        rw [← N.x12 g t]
        exact (N.hHE_A2 ρ g t).1
      · show GReach (N.Hb ρ 0 2 g (true, t)) ((N.G2 (N.r2 t g)).Xm.Φ 0) (fun φ => bcost φ (N.hrem ρ 0 (true, t)))
        rw [← N.y12 g t]
        exact (N.hHE_A2 ρ g t).2
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _)
  refine H1.cast (fun φ => ?_)
  simp_rw [mkR4_map (fun c : (ℕ → ℝ) → ℝ => c φ)]
  rw [sum_mkR4]
  simp only [GHost401.hcost, sum_const, card_univ, nsmul_eq_mul, mul_zero, add_zero, zero_add,
    Finset.sum_add_distrib, Finset.sum_const_zero, smul_zero]
  ring

/-- gate layer A2 of run `ρ` (Shea's, word for word): twins have equal frames. -/
lemma GHost401.gateA2 (ρ : Fin 8) : XRoute (N.S5 ρ) (N.S5 ρ) (gscQ pABQ_2 kAQ_2) (fun _ => 0) := by
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

/-- the free adapters before stage 2 of run `ρ`: every bank from `Zb` to `Zp`, every host of a window. -/
lemma GHost401.adapt2 (ρ : Fin 8) :
    GRoute (N.S5 ρ) (N.S6 ρ) id (fun _ => 0) := by
  have H1 := GRoute.reach_all (N.S5 ρ) (N.S6 ρ) (fun _ _ => 0) (by
      rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
      · exact GReach.refl _
      · exact GReach.refl _
      · show GReach ((N.G2 (N.r2 t g)).Xm.Φ (tt (N.I.tv t))) (N.Hp ρ 1 2 g (false, t)) (fun _ => 0)
        rw [← (N.hH0_B2 ρ g t).1]
        exact N.hHP_B2_2 ρ g (false, t)
      · show GReach ((N.G2 (N.r2 t g)).Xm.Φ 0) (N.Hp ρ 1 2 g (true, t)) (fun _ => 0)
        rw [← (N.hH0_B2 ρ g t).2]
        exact N.hHP_B2_2 ρ g (true, t)
      · exact N.hHP_A3_2 ρ g (false, t)
      · exact N.hHP_A3_2 ρ g (true, t)
      · exact N.hHP_A4_2 ρ g (false, t)
      · exact N.hHP_A4_2 ρ g (true, t)
      · exact N.hP2 ρ g b
      · exact GReach.refl _)
  exact H1.cast (fun φ => by simp)

/-- stage 2 of run `ρ` (pair 1): the slot `q` of `g` on its bank or on its host. -/
lemma GHost401.stage2 (ρ : Fin 8) :
    GRoute (N.S6 ρ) (N.S7 ρ) (liftQ2 (Γ := Γ) (T := T) (C := C) (N.bk ρ 2) GF)
      (fun φ => (Fintype.card Γ : ℝ) * (N.Ic ρ 2).cost φ) := by
  have hUS : ∀ g q, N.Wn2 ρ g q * N.S6 ρ (slotR (N.hostAt ρ 2) (N.bk ρ 2) g q) = N.S7 ρ (slotR (N.hostAt ρ 2) (N.bk ρ 2) g q) := by
    intro g q
    rcases hq : N.hostAt ρ 2 q with _ | ⟨c, s, t⟩
    · rw [slotR_bank hq]
      exact N.hZ2 ρ g q hq
    · rw [slotR_host hq]
      have hw := N.hostWin ρ 2 q c (s, t) hq
      fin_cases c
      · exact absurd hw (by decide)
      · cases s <;> exact N.hHZ_B2_2 ρ g q _ hq
      · cases s <;> exact N.hHZ_A3_2 ρ g q _ hq
      · exact absurd hw (by decide)
      · cases s <;> exact N.hHZ_A4_2 ρ g q _ hq
      · exact absurd hw (by decide)
      · exact absurd hw (by decide)
      · exact absurd hw (by decide)
      · exact absurd hw (by decide)
  have h := gistageE_fwd (N.Jc ρ 2) N.r2 N.G2 (N.N2 ρ) (N.Wn2 ρ) (N.hN2 ρ) (N.hW2 ρ)
    (fun g q => N.S6 ρ (slotR (N.hostAt ρ 2) (N.bk ρ 2) g q)) (cOne Γ C α) (cOne Γ C α)
  have h' : GRoute (bIn N.I.tv N.r2 (fun d => (N.G2 d).Xm)
        (fun g q => N.S6 ρ (slotR (N.hostAt ρ 2) (N.bk ρ 2) g q)) (cOne Γ C α))
      (mkS N.xo2 N.yo2 (fun g q => N.S7 ρ (slotR (N.hostAt ρ 2) (N.bk ρ 2) g q)) (cOne Γ C α)) GF
      (fun φ => (Fintype.card Γ : ℝ) * (N.Ic ρ 2).cost φ) := by
    have e : bOut N.I.tv N.r2 (fun d => (N.G2 d).Xm)
        (fun g q => N.Wn2 ρ g q * N.S6 ρ (slotR (N.hostAt ρ 2) (N.bk ρ 2) g q)) (cOne Γ C α)
        = mkS N.xo2 N.yo2 (fun g q => N.S7 ρ (slotR (N.hostAt ρ 2) (N.bk ρ 2) g q)) (cOne Γ C α) := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · rfl
      · rfl
      · exact hUS g q
      · rfl
    rw [← e]
    exact h
  refine ghliftQ2 (N.hostAt ρ 2) (N.bk ρ 2) (N.hok ρ 2) h' (fun g t => rfl) (fun g t => rfl)
    (fun g t => rfl) (fun g t => rfl) (fun g q => rfl) (fun g q => rfl) (fun g c => rfl) (fun g c => rfl) ?_
    (fun _ _ _ => rfl) GF_loc
  intro r hr
  rcases r with ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
  · exact absurd ((cover_iff _ _).mpr ⟨jX (g,t), rfl⟩) hr
  · exact absurd ((cover_iff _ _).mpr ⟨jY (g,t), rfl⟩) hr
  · exact (N.hHZn_B2_2 ρ g (false, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact (N.hHZn_B2_2 ρ g (true, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact (N.hHZn_A3_2 ρ g (false, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact (N.hHZn_A3_2 ρ g (true, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact (N.hHZn_A4_2 ρ g (false, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact (N.hHZn_A4_2 ρ g (true, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact (N.hZn2 ρ g b (fun q hq hb => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_bank hq, hb]; rfl⟩))).symm
  · exact absurd ((cover_iff _ _).mpr ⟨jC (g,c), rfl⟩) hr

/-- the remaining climb of the host chains B2 (pair 2): ONE block of rank `hrem 1 j` per role. -/
lemma GHost401.climbB2 (ρ : Fin 8) :
    GRoute (N.S7 ρ) (N.S8 ρ) id (fun φ => (Fintype.card Γ : ℝ) * N.hcost ρ 1 φ) := by
  have H1 := GRoute.reach_all (N.S7 ρ) (N.S8 ρ)
    (mkR4 (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ t φ => bcost φ (N.hrem ρ 1 (false, t))) (fun _ t φ => bcost φ (N.hrem ρ 1 (true, t))) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)) (by
      rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
      · exact GReach.refl _
      · exact GReach.refl _
      · show GReach (N.Hb ρ 1 3 g (false, t)) ((N.G3 (N.r3 t g)).Xm.Φ (tt (N.I.tv t))) (fun φ => bcost φ (N.hrem ρ 1 (false, t)))
        rw [← N.x23 g t]
        exact (N.hHE_B2 ρ g t).1
      · show GReach (N.Hb ρ 1 3 g (true, t)) ((N.G3 (N.r3 t g)).Xm.Φ 0) (fun φ => bcost φ (N.hrem ρ 1 (true, t)))
        rw [← N.y23 g t]
        exact (N.hHE_B2 ρ g t).2
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _)
  refine H1.cast (fun φ => ?_)
  simp_rw [mkR4_map (fun c : (ℕ → ℝ) → ℝ => c φ)]
  rw [sum_mkR4]
  simp only [GHost401.hcost, sum_const, card_univ, nsmul_eq_mul, mul_zero, add_zero, zero_add,
    Finset.sum_add_distrib, Finset.sum_const_zero, smul_zero]
  ring

/-- gate layer B2 of run `ρ` (Shea's, word for word): twins have equal frames. -/
lemma GHost401.gateB2 (ρ : Fin 8) : XRoute (N.S8 ρ) (N.S8 ρ) (gscQ pABQ_2 kBQ_2) (fun _ => 0) := by
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

/-- the free adapters before stage 3 of run `ρ`: every bank from `Zb` to `Zp`, every host of a window. -/
lemma GHost401.adapt3 (ρ : Fin 8) :
    GRoute (N.S8 ρ) (N.S9 ρ) id (fun _ => 0) := by
  have H1 := GRoute.reach_all (N.S8 ρ) (N.S9 ρ) (fun _ _ => 0) (by
      rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
      · show GReach ((N.G2 (N.r2 t g)).Xm.Φ 1) (N.Hp ρ 6 3 g (false, t)) (fun _ => 0)
        rw [← (N.hH0_F1 ρ g t).1]
        exact N.hHP_F1_3 ρ g (false, t)
      · show GReach ((N.G2 (N.r2 t g)).Xm.Φ (1 + tt (N.I.tv t))) (N.Hp ρ 6 3 g (true, t)) (fun _ => 0)
        rw [← (N.hH0_F1 ρ g t).2]
        exact N.hHP_F1_3 ρ g (true, t)
      · exact GReach.refl _
      · exact GReach.refl _
      · exact N.hHP_A3_3 ρ g (false, t)
      · exact N.hHP_A3_3 ρ g (true, t)
      · exact N.hHP_A4_3 ρ g (false, t)
      · exact N.hHP_A4_3 ρ g (true, t)
      · exact N.hP3 ρ g b
      · exact GReach.refl _)
  exact H1.cast (fun φ => by simp)

/-- stage 3 of run `ρ` (pair 2): the slot `q` of `g` on its bank or on its host. -/
lemma GHost401.stage3 (ρ : Fin 8) :
    GRoute (N.S9 ρ) (N.S10 ρ) (liftQ3 (Γ := Γ) (T := T) (C := C) (N.bk ρ 3) GB)
      (fun φ => (Fintype.card Γ : ℝ) * (N.Ic ρ 3).cost φ) := by
  have hUS : ∀ g q, N.Wn3 ρ g q * N.S9 ρ (slotR (N.hostAt ρ 3) (N.bk ρ 3) g q) = N.S10 ρ (slotR (N.hostAt ρ 3) (N.bk ρ 3) g q) := by
    intro g q
    rcases hq : N.hostAt ρ 3 q with _ | ⟨c, s, t⟩
    · rw [slotR_bank hq]
      exact N.hZ3 ρ g q hq
    · rw [slotR_host hq]
      have hw := N.hostWin ρ 3 q c (s, t) hq
      fin_cases c
      · exact absurd hw (by decide)
      · exact absurd hw (by decide)
      · cases s <;> exact N.hHZ_A3_3 ρ g q _ hq
      · exact absurd hw (by decide)
      · cases s <;> exact N.hHZ_A4_3 ρ g q _ hq
      · exact absurd hw (by decide)
      · cases s <;> exact N.hHZ_F1_3 ρ g q _ hq
      · exact absurd hw (by decide)
      · exact absurd hw (by decide)
  have h := gistageE_bwd (N.Jc ρ 3) N.r3 N.G3 (N.N3 ρ) (N.Wn3 ρ) (N.hN3 ρ) (N.hW3 ρ)
    (fun g q => N.S9 ρ (slotR (N.hostAt ρ 3) (N.bk ρ 3) g q)) (cOne Γ C α) (cOne Γ C α)
  have h' : GRoute (bIn N.I.tv N.r3 (fun d => (N.G3 d).Xm)
        (fun g q => N.S9 ρ (slotR (N.hostAt ρ 3) (N.bk ρ 3) g q)) (cOne Γ C α))
      (mkS N.xi4 N.yi4 (fun g q => N.S10 ρ (slotR (N.hostAt ρ 3) (N.bk ρ 3) g q)) (cOne Γ C α)) GB
      (fun φ => (Fintype.card Γ : ℝ) * (N.Ic ρ 3).cost φ) := by
    have e : bOut N.I.tv N.r3 (fun d => (N.G3 d).Xm)
        (fun g q => N.Wn3 ρ g q * N.S9 ρ (slotR (N.hostAt ρ 3) (N.bk ρ 3) g q)) (cOne Γ C α)
        = mkS N.xi4 N.yi4 (fun g q => N.S10 ρ (slotR (N.hostAt ρ 3) (N.bk ρ 3) g q)) (cOne Γ C α) := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · exact N.x34 g t
      · exact N.y34 g t
      · exact hUS g q
      · rfl
    rw [← e]
    exact h
  refine ghliftQ3 (N.hostAt ρ 3) (N.bk ρ 3) (N.hok ρ 3) h' (fun g t => rfl) (fun g t => rfl)
    (fun g t => rfl) (fun g t => rfl) (fun g q => rfl) (fun g q => rfl) (fun g c => rfl) (fun g c => rfl) ?_
    (fun _ _ _ => rfl) GB_loc
  intro r hr
  rcases r with ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
  · exact (N.hHZn_F1_3 ρ g (false, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact (N.hHZn_F1_3 ρ g (true, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact absurd ((cover_iff _ _).mpr ⟨jX (g,t), rfl⟩) hr
  · exact absurd ((cover_iff _ _).mpr ⟨jY (g,t), rfl⟩) hr
  · exact (N.hHZn_A3_3 ρ g (false, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact (N.hHZn_A3_3 ρ g (true, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact (N.hHZn_A4_3 ρ g (false, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact (N.hHZn_A4_3 ρ g (true, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact (N.hZn3 ρ g b (fun q hq hb => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_bank hq, hb]; rfl⟩))).symm
  · exact absurd ((cover_iff _ _).mpr ⟨jC (g,c), rfl⟩) hr

/-- the remaining climb of the host chains A3 (pair 3): ONE block of rank `hrem 2 j` per role. -/
lemma GHost401.climbA3 (ρ : Fin 8) :
    GRoute (N.S10 ρ) (N.S11 ρ) id (fun φ => (Fintype.card Γ : ℝ) * N.hcost ρ 2 φ) := by
  have H1 := GRoute.reach_all (N.S10 ρ) (N.S11 ρ)
    (mkR4 (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ t φ => bcost φ (N.hrem ρ 2 (false, t))) (fun _ t φ => bcost φ (N.hrem ρ 2 (true, t))) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)) (by
      rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · show GReach (N.Hb ρ 2 4 g (false, t)) ((N.G4 (N.r4 t g)).Xm.Φ (tt (N.I.tv t))) (fun φ => bcost φ (N.hrem ρ 2 (false, t)))
        rw [← N.x34 g t]
        exact (N.hHE_A3 ρ g t).1
      · show GReach (N.Hb ρ 2 4 g (true, t)) ((N.G4 (N.r4 t g)).Xm.Φ 0) (fun φ => bcost φ (N.hrem ρ 2 (true, t)))
        rw [← N.y34 g t]
        exact (N.hHE_A3 ρ g t).2
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _)
  refine H1.cast (fun φ => ?_)
  simp_rw [mkR4_map (fun c : (ℕ → ℝ) → ℝ => c φ)]
  rw [sum_mkR4]
  simp only [GHost401.hcost, sum_const, card_univ, nsmul_eq_mul, mul_zero, add_zero, zero_add,
    Finset.sum_add_distrib, Finset.sum_const_zero, smul_zero]
  ring

/-- gate layer A3 of run `ρ` (Shea's, word for word): twins have equal frames. -/
lemma GHost401.gateA3 (ρ : Fin 8) : XRoute (N.S11 ρ) (N.S11 ρ) (gscQ pABQ_3 kAQ_3) (fun _ => 0) := by
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

/-- the free adapters before stage 4 of run `ρ`: every bank from `Zb` to `Zp`, every host of a window. -/
lemma GHost401.adapt4 (ρ : Fin 8) :
    GRoute (N.S11 ρ) (N.S12 ρ) id (fun _ => 0) := by
  have H1 := GRoute.reach_all (N.S11 ρ) (N.S12 ρ) (fun _ _ => 0) (by
      rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
      · exact N.hHP_F1_4 ρ g (false, t)
      · exact N.hHP_F1_4 ρ g (true, t)
      · exact GReach.refl _
      · exact GReach.refl _
      · show GReach ((N.G4 (N.r4 t g)).Xm.Φ (tt (N.I.tv t))) (N.Hp ρ 3 4 g (false, t)) (fun _ => 0)
        rw [← (N.hH0_B3 ρ g t).1]
        exact N.hHP_B3_4 ρ g (false, t)
      · show GReach ((N.G4 (N.r4 t g)).Xm.Φ 0) (N.Hp ρ 3 4 g (true, t)) (fun _ => 0)
        rw [← (N.hH0_B3 ρ g t).2]
        exact N.hHP_B3_4 ρ g (true, t)
      · exact N.hHP_A4_4 ρ g (false, t)
      · exact N.hHP_A4_4 ρ g (true, t)
      · exact N.hP4 ρ g b
      · exact GReach.refl _)
  exact H1.cast (fun φ => by simp)

/-- stage 4 of run `ρ` (pair 2): the slot `q` of `g` on its bank or on its host. -/
lemma GHost401.stage4 (ρ : Fin 8) :
    GRoute (N.S12 ρ) (N.S13 ρ) (liftQ4 (Γ := Γ) (T := T) (C := C) (N.bk ρ 4) GF)
      (fun φ => (Fintype.card Γ : ℝ) * (N.Ic ρ 4).cost φ) := by
  have hUS : ∀ g q, N.Wn4 ρ g q * N.S12 ρ (slotR (N.hostAt ρ 4) (N.bk ρ 4) g q) = N.S13 ρ (slotR (N.hostAt ρ 4) (N.bk ρ 4) g q) := by
    intro g q
    rcases hq : N.hostAt ρ 4 q with _ | ⟨c, s, t⟩
    · rw [slotR_bank hq]
      exact N.hZ4 ρ g q hq
    · rw [slotR_host hq]
      have hw := N.hostWin ρ 4 q c (s, t) hq
      fin_cases c
      · exact absurd hw (by decide)
      · exact absurd hw (by decide)
      · exact absurd hw (by decide)
      · cases s <;> exact N.hHZ_B3_4 ρ g q _ hq
      · cases s <;> exact N.hHZ_A4_4 ρ g q _ hq
      · exact absurd hw (by decide)
      · cases s <;> exact N.hHZ_F1_4 ρ g q _ hq
      · exact absurd hw (by decide)
      · exact absurd hw (by decide)
  have h := gistageE_fwd (N.Jc ρ 4) N.r4 N.G4 (N.N4 ρ) (N.Wn4 ρ) (N.hN4 ρ) (N.hW4 ρ)
    (fun g q => N.S12 ρ (slotR (N.hostAt ρ 4) (N.bk ρ 4) g q)) (cOne Γ C α) (cOne Γ C α)
  have h' : GRoute (bIn N.I.tv N.r4 (fun d => (N.G4 d).Xm)
        (fun g q => N.S12 ρ (slotR (N.hostAt ρ 4) (N.bk ρ 4) g q)) (cOne Γ C α))
      (mkS N.xo4 N.yo4 (fun g q => N.S13 ρ (slotR (N.hostAt ρ 4) (N.bk ρ 4) g q)) (cOne Γ C α)) GF
      (fun φ => (Fintype.card Γ : ℝ) * (N.Ic ρ 4).cost φ) := by
    have e : bOut N.I.tv N.r4 (fun d => (N.G4 d).Xm)
        (fun g q => N.Wn4 ρ g q * N.S12 ρ (slotR (N.hostAt ρ 4) (N.bk ρ 4) g q)) (cOne Γ C α)
        = mkS N.xo4 N.yo4 (fun g q => N.S13 ρ (slotR (N.hostAt ρ 4) (N.bk ρ 4) g q)) (cOne Γ C α) := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · rfl
      · rfl
      · exact hUS g q
      · rfl
    rw [← e]
    exact h
  refine ghliftQ4 (N.hostAt ρ 4) (N.bk ρ 4) (N.hok ρ 4) h' (fun g t => rfl) (fun g t => rfl)
    (fun g t => rfl) (fun g t => rfl) (fun g q => rfl) (fun g q => rfl) (fun g c => rfl) (fun g c => rfl) ?_
    (fun _ _ _ => rfl) GF_loc
  intro r hr
  rcases r with ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
  · exact (N.hHZn_F1_4 ρ g (false, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact (N.hHZn_F1_4 ρ g (true, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact absurd ((cover_iff _ _).mpr ⟨jX (g,t), rfl⟩) hr
  · exact absurd ((cover_iff _ _).mpr ⟨jY (g,t), rfl⟩) hr
  · exact (N.hHZn_B3_4 ρ g (false, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact (N.hHZn_B3_4 ρ g (true, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact (N.hHZn_A4_4 ρ g (false, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact (N.hHZn_A4_4 ρ g (true, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact (N.hZn4 ρ g b (fun q hq hb => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_bank hq, hb]; rfl⟩))).symm
  · exact absurd ((cover_iff _ _).mpr ⟨jC (g,c), rfl⟩) hr

/-- the remaining climb of the host chains B3 (pair 3): ONE block of rank `hrem 3 j` per role. -/
lemma GHost401.climbB3 (ρ : Fin 8) :
    GRoute (N.S13 ρ) (N.S14 ρ) id (fun φ => (Fintype.card Γ : ℝ) * N.hcost ρ 3 φ) := by
  have H1 := GRoute.reach_all (N.S13 ρ) (N.S14 ρ)
    (mkR4 (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ t φ => bcost φ (N.hrem ρ 3 (false, t))) (fun _ t φ => bcost φ (N.hrem ρ 3 (true, t))) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)) (by
      rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · show GReach (N.Hb ρ 3 5 g (false, t)) ((N.G5 (N.r5 t g)).Xm.Φ (tt (N.I.tv t))) (fun φ => bcost φ (N.hrem ρ 3 (false, t)))
        rw [← N.x45 g t]
        exact (N.hHE_B3 ρ g t).1
      · show GReach (N.Hb ρ 3 5 g (true, t)) ((N.G5 (N.r5 t g)).Xm.Φ 0) (fun φ => bcost φ (N.hrem ρ 3 (true, t)))
        rw [← N.y45 g t]
        exact (N.hHE_B3 ρ g t).2
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _)
  refine H1.cast (fun φ => ?_)
  simp_rw [mkR4_map (fun c : (ℕ → ℝ) → ℝ => c φ)]
  rw [sum_mkR4]
  simp only [GHost401.hcost, sum_const, card_univ, nsmul_eq_mul, mul_zero, add_zero, zero_add,
    Finset.sum_add_distrib, Finset.sum_const_zero, smul_zero]
  ring

/-- gate layer B3 of run `ρ` (Shea's, word for word): twins have equal frames. -/
lemma GHost401.gateB3 (ρ : Fin 8) : XRoute (N.S14 ρ) (N.S14 ρ) (gscQ pABQ_3 kBQ_3) (fun _ => 0) := by
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

/-- the free adapters before stage 5 of run `ρ`: every bank from `Zb` to `Zp`, every host of a window. -/
lemma GHost401.adapt5 (ρ : Fin 8) :
    GRoute (N.S14 ρ) (N.S15 ρ) id (fun _ => 0) := by
  have H1 := GRoute.reach_all (N.S14 ρ) (N.S15 ρ) (fun _ _ => 0) (by
      rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
      · exact N.hHP_F1_5 ρ g (false, t)
      · exact N.hHP_F1_5 ρ g (true, t)
      · show GReach ((N.G4 (N.r4 t g)).Xm.Φ 1) (N.Hp ρ 7 5 g (false, t)) (fun _ => 0)
        rw [← (N.hH0_F2 ρ g t).1]
        exact N.hHP_F2_5 ρ g (false, t)
      · show GReach ((N.G4 (N.r4 t g)).Xm.Φ (1 + tt (N.I.tv t))) (N.Hp ρ 7 5 g (true, t)) (fun _ => 0)
        rw [← (N.hH0_F2 ρ g t).2]
        exact N.hHP_F2_5 ρ g (true, t)
      · exact GReach.refl _
      · exact GReach.refl _
      · exact N.hHP_A4_5 ρ g (false, t)
      · exact N.hHP_A4_5 ρ g (true, t)
      · exact N.hP5 ρ g b
      · exact GReach.refl _)
  exact H1.cast (fun φ => by simp)

/-- stage 5 of run `ρ` (pair 3): the slot `q` of `g` on its bank or on its host. -/
lemma GHost401.stage5 (ρ : Fin 8) :
    GRoute (N.S15 ρ) (N.S16 ρ) (liftQ5 (Γ := Γ) (T := T) (C := C) (N.bk ρ 5) GB)
      (fun φ => (Fintype.card Γ : ℝ) * (N.Ic ρ 5).cost φ) := by
  have hUS : ∀ g q, N.Wn5 ρ g q * N.S15 ρ (slotR (N.hostAt ρ 5) (N.bk ρ 5) g q) = N.S16 ρ (slotR (N.hostAt ρ 5) (N.bk ρ 5) g q) := by
    intro g q
    rcases hq : N.hostAt ρ 5 q with _ | ⟨c, s, t⟩
    · rw [slotR_bank hq]
      exact N.hZ5 ρ g q hq
    · rw [slotR_host hq]
      have hw := N.hostWin ρ 5 q c (s, t) hq
      fin_cases c
      · exact absurd hw (by decide)
      · exact absurd hw (by decide)
      · exact absurd hw (by decide)
      · exact absurd hw (by decide)
      · cases s <;> exact N.hHZ_A4_5 ρ g q _ hq
      · exact absurd hw (by decide)
      · cases s <;> exact N.hHZ_F1_5 ρ g q _ hq
      · cases s <;> exact N.hHZ_F2_5 ρ g q _ hq
      · exact absurd hw (by decide)
  have h := gistageE_bwd (N.Jc ρ 5) N.r5 N.G5 (N.N5 ρ) (N.Wn5 ρ) (N.hN5 ρ) (N.hW5 ρ)
    (fun g q => N.S15 ρ (slotR (N.hostAt ρ 5) (N.bk ρ 5) g q)) (cOne Γ C α) (cOne Γ C α)
  have h' : GRoute (bIn N.I.tv N.r5 (fun d => (N.G5 d).Xm)
        (fun g q => N.S15 ρ (slotR (N.hostAt ρ 5) (N.bk ρ 5) g q)) (cOne Γ C α))
      (mkS N.xi6 N.yi6 (fun g q => N.S16 ρ (slotR (N.hostAt ρ 5) (N.bk ρ 5) g q)) (cOne Γ C α)) GB
      (fun φ => (Fintype.card Γ : ℝ) * (N.Ic ρ 5).cost φ) := by
    have e : bOut N.I.tv N.r5 (fun d => (N.G5 d).Xm)
        (fun g q => N.Wn5 ρ g q * N.S15 ρ (slotR (N.hostAt ρ 5) (N.bk ρ 5) g q)) (cOne Γ C α)
        = mkS N.xi6 N.yi6 (fun g q => N.S16 ρ (slotR (N.hostAt ρ 5) (N.bk ρ 5) g q)) (cOne Γ C α) := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · exact N.x56 g t
      · exact N.y56 g t
      · exact hUS g q
      · rfl
    rw [← e]
    exact h
  refine ghliftQ5 (N.hostAt ρ 5) (N.bk ρ 5) (N.hok ρ 5) h' (fun g t => rfl) (fun g t => rfl)
    (fun g t => rfl) (fun g t => rfl) (fun g q => rfl) (fun g q => rfl) (fun g c => rfl) (fun g c => rfl) ?_
    (fun _ _ _ => rfl) GB_loc
  intro r hr
  rcases r with ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
  · exact (N.hHZn_F1_5 ρ g (false, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact (N.hHZn_F1_5 ρ g (true, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact (N.hHZn_F2_5 ρ g (false, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact (N.hHZn_F2_5 ρ g (true, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact absurd ((cover_iff _ _).mpr ⟨jX (g,t), rfl⟩) hr
  · exact absurd ((cover_iff _ _).mpr ⟨jY (g,t), rfl⟩) hr
  · exact (N.hHZn_A4_5 ρ g (false, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact (N.hHZn_A4_5 ρ g (true, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact (N.hZn5 ρ g b (fun q hq hb => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_bank hq, hb]; rfl⟩))).symm
  · exact absurd ((cover_iff _ _).mpr ⟨jC (g,c), rfl⟩) hr

/-- the remaining climb of the host chains A4 (pair 4): ONE block of rank `hrem 4 j` per role. -/
lemma GHost401.climbA4 (ρ : Fin 8) :
    GRoute (N.S16 ρ) (N.S17 ρ) id (fun φ => (Fintype.card Γ : ℝ) * N.hcost ρ 4 φ) := by
  have H1 := GRoute.reach_all (N.S16 ρ) (N.S17 ρ)
    (mkR4 (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ t φ => bcost φ (N.hrem ρ 4 (false, t))) (fun _ t φ => bcost φ (N.hrem ρ 4 (true, t))) (fun _ _ _ => 0) (fun _ _ _ => 0)) (by
      rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · show GReach (N.Hb ρ 4 6 g (false, t)) ((N.G6 (N.r6 t g)).Xm.Φ (tt (N.I.tv t))) (fun φ => bcost φ (N.hrem ρ 4 (false, t)))
        rw [← N.x56 g t]
        exact (N.hHE_A4 ρ g t).1
      · show GReach (N.Hb ρ 4 6 g (true, t)) ((N.G6 (N.r6 t g)).Xm.Φ 0) (fun φ => bcost φ (N.hrem ρ 4 (true, t)))
        rw [← N.y56 g t]
        exact (N.hHE_A4 ρ g t).2
      · exact GReach.refl _
      · exact GReach.refl _)
  refine H1.cast (fun φ => ?_)
  simp_rw [mkR4_map (fun c : (ℕ → ℝ) → ℝ => c φ)]
  rw [sum_mkR4]
  simp only [GHost401.hcost, sum_const, card_univ, nsmul_eq_mul, mul_zero, add_zero, zero_add,
    Finset.sum_add_distrib, Finset.sum_const_zero, smul_zero]
  ring

/-- gate layer A4 of run `ρ` (Shea's, word for word): twins have equal frames. -/
lemma GHost401.gateA4 (ρ : Fin 8) : XRoute (N.S17 ρ) (N.S17 ρ) (gscQ pABQ_4 kAQ_4) (fun _ => 0) := by
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

/-- the free adapters before stage 6 of run `ρ`: every bank from `Zb` to `Zp`, every host of a window. -/
lemma GHost401.adapt6 (ρ : Fin 8) :
    GRoute (N.S17 ρ) (N.S18 ρ) id (fun _ => 0) := by
  have H1 := GRoute.reach_all (N.S17 ρ) (N.S18 ρ) (fun _ _ => 0) (by
      rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
      · exact N.hHP_F1_6 ρ g (false, t)
      · exact N.hHP_F1_6 ρ g (true, t)
      · exact N.hHP_F2_6 ρ g (false, t)
      · exact N.hHP_F2_6 ρ g (true, t)
      · exact GReach.refl _
      · exact GReach.refl _
      · show GReach ((N.G6 (N.r6 t g)).Xm.Φ (tt (N.I.tv t))) (N.Hp ρ 5 6 g (false, t)) (fun _ => 0)
        rw [← (N.hH0_B4 ρ g t).1]
        exact N.hHP_B4_6 ρ g (false, t)
      · show GReach ((N.G6 (N.r6 t g)).Xm.Φ 0) (N.Hp ρ 5 6 g (true, t)) (fun _ => 0)
        rw [← (N.hH0_B4 ρ g t).2]
        exact N.hHP_B4_6 ρ g (true, t)
      · exact N.hP6 ρ g b
      · exact GReach.refl _)
  exact H1.cast (fun φ => by simp)

/-- stage 6 of run `ρ` (pair 3): the slot `q` of `g` on its bank or on its host. -/
lemma GHost401.stage6 (ρ : Fin 8) :
    GRoute (N.S18 ρ) (N.S19 ρ) (liftQ6 (Γ := Γ) (T := T) (C := C) (N.bk ρ 6) GF)
      (fun φ => (Fintype.card Γ : ℝ) * (N.Ic ρ 6).cost φ) := by
  have hUS : ∀ g q, N.Wn6 ρ g q * N.S18 ρ (slotR (N.hostAt ρ 6) (N.bk ρ 6) g q) = N.S19 ρ (slotR (N.hostAt ρ 6) (N.bk ρ 6) g q) := by
    intro g q
    rcases hq : N.hostAt ρ 6 q with _ | ⟨c, s, t⟩
    · rw [slotR_bank hq]
      exact N.hZ6 ρ g q hq
    · rw [slotR_host hq]
      have hw := N.hostWin ρ 6 q c (s, t) hq
      fin_cases c
      · exact absurd hw (by decide)
      · exact absurd hw (by decide)
      · exact absurd hw (by decide)
      · exact absurd hw (by decide)
      · exact absurd hw (by decide)
      · cases s <;> exact N.hHZ_B4_6 ρ g q _ hq
      · cases s <;> exact N.hHZ_F1_6 ρ g q _ hq
      · cases s <;> exact N.hHZ_F2_6 ρ g q _ hq
      · exact absurd hw (by decide)
  have h := gistageE_fwd (N.Jc ρ 6) N.r6 N.G6 (N.N6 ρ) (N.Wn6 ρ) (N.hN6 ρ) (N.hW6 ρ)
    (fun g q => N.S18 ρ (slotR (N.hostAt ρ 6) (N.bk ρ 6) g q)) (cOne Γ C α) (cOne Γ C α)
  have h' : GRoute (bIn N.I.tv N.r6 (fun d => (N.G6 d).Xm)
        (fun g q => N.S18 ρ (slotR (N.hostAt ρ 6) (N.bk ρ 6) g q)) (cOne Γ C α))
      (mkS N.xo6 N.yo6 (fun g q => N.S19 ρ (slotR (N.hostAt ρ 6) (N.bk ρ 6) g q)) (cOne Γ C α)) GF
      (fun φ => (Fintype.card Γ : ℝ) * (N.Ic ρ 6).cost φ) := by
    have e : bOut N.I.tv N.r6 (fun d => (N.G6 d).Xm)
        (fun g q => N.Wn6 ρ g q * N.S18 ρ (slotR (N.hostAt ρ 6) (N.bk ρ 6) g q)) (cOne Γ C α)
        = mkS N.xo6 N.yo6 (fun g q => N.S19 ρ (slotR (N.hostAt ρ 6) (N.bk ρ 6) g q)) (cOne Γ C α) := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · rfl
      · rfl
      · exact hUS g q
      · rfl
    rw [← e]
    exact h
  refine ghliftQ6 (N.hostAt ρ 6) (N.bk ρ 6) (N.hok ρ 6) h' (fun g t => rfl) (fun g t => rfl)
    (fun g t => rfl) (fun g t => rfl) (fun g q => rfl) (fun g q => rfl) (fun g c => rfl) (fun g c => rfl) ?_
    (fun _ _ _ => rfl) GF_loc
  intro r hr
  rcases r with ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
  · exact (N.hHZn_F1_6 ρ g (false, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact (N.hHZn_F1_6 ρ g (true, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact (N.hHZn_F2_6 ρ g (false, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact (N.hHZn_F2_6 ρ g (true, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact absurd ((cover_iff _ _).mpr ⟨jX (g,t), rfl⟩) hr
  · exact absurd ((cover_iff _ _).mpr ⟨jY (g,t), rfl⟩) hr
  · exact (N.hHZn_B4_6 ρ g (false, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact (N.hHZn_B4_6 ρ g (true, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact (N.hZn6 ρ g b (fun q hq hb => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_bank hq, hb]; rfl⟩))).symm
  · exact absurd ((cover_iff _ _).mpr ⟨jC (g,c), rfl⟩) hr

/-- the remaining climb of the host chains B4 (pair 4): ONE block of rank `hrem 5 j` per role. -/
lemma GHost401.climbB4 (ρ : Fin 8) :
    GRoute (N.S19 ρ) (N.S20 ρ) id (fun φ => (Fintype.card Γ : ℝ) * N.hcost ρ 5 φ) := by
  have H1 := GRoute.reach_all (N.S19 ρ) (N.S20 ρ)
    (mkR4 (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ t φ => bcost φ (N.hrem ρ 5 (false, t))) (fun _ t φ => bcost φ (N.hrem ρ 5 (true, t))) (fun _ _ _ => 0) (fun _ _ _ => 0)) (by
      rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · show GReach (N.Hb ρ 5 7 g (false, t)) ((N.G7 (N.r7 t g)).Xm.Φ (tt (N.I.tv t))) (fun φ => bcost φ (N.hrem ρ 5 (false, t)))
        rw [← N.x67 g t]
        exact (N.hHE_B4 ρ g t).1
      · show GReach (N.Hb ρ 5 7 g (true, t)) ((N.G7 (N.r7 t g)).Xm.Φ 0) (fun φ => bcost φ (N.hrem ρ 5 (true, t)))
        rw [← N.y67 g t]
        exact (N.hHE_B4 ρ g t).2
      · exact GReach.refl _
      · exact GReach.refl _)
  refine H1.cast (fun φ => ?_)
  simp_rw [mkR4_map (fun c : (ℕ → ℝ) → ℝ => c φ)]
  rw [sum_mkR4]
  simp only [GHost401.hcost, sum_const, card_univ, nsmul_eq_mul, mul_zero, add_zero, zero_add,
    Finset.sum_add_distrib, Finset.sum_const_zero, smul_zero]
  ring

/-- gate layer B4 of run `ρ` (Shea's, word for word): twins have equal frames. -/
lemma GHost401.gateB4 (ρ : Fin 8) : XRoute (N.S20 ρ) (N.S20 ρ) (gscQ pABQ_4 kBQ_4) (fun _ => 0) := by
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

/-- the free adapters before stage 7 of run `ρ`: every bank from `Zb` to `Zp`, every host of a window. -/
lemma GHost401.adapt7 (ρ : Fin 8) :
    GRoute (N.S20 ρ) (N.S21 ρ) id (fun _ => 0) := by
  have H1 := GRoute.reach_all (N.S20 ρ) (N.S21 ρ) (fun _ _ => 0) (by
      rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
      · exact N.hHP_F1_7 ρ g (false, t)
      · exact N.hHP_F1_7 ρ g (true, t)
      · exact N.hHP_F2_7 ρ g (false, t)
      · exact N.hHP_F2_7 ρ g (true, t)
      · show GReach ((N.G6 (N.r6 t g)).Xm.Φ 1) (N.Hp ρ 8 7 g (false, t)) (fun _ => 0)
        rw [← (N.hH0_F3 ρ g t).1]
        exact N.hHP_F3_7 ρ g (false, t)
      · show GReach ((N.G6 (N.r6 t g)).Xm.Φ (1 + tt (N.I.tv t))) (N.Hp ρ 8 7 g (true, t)) (fun _ => 0)
        rw [← (N.hH0_F3 ρ g t).2]
        exact N.hHP_F3_7 ρ g (true, t)
      · exact GReach.refl _
      · exact GReach.refl _
      · exact N.hP7 ρ g b
      · exact GReach.refl _)
  exact H1.cast (fun φ => by simp)

/-- stage 7 of run `ρ` (pair 4): the slot `q` of `g` on its bank or on its host. -/
lemma GHost401.stage7 (ρ : Fin 8) :
    GRoute (N.S21 ρ) (N.S22 ρ) (liftQ7 (Γ := Γ) (T := T) (C := C) (N.bk ρ 7) GB)
      (fun φ => (Fintype.card Γ : ℝ) * (N.Ic ρ 7).cost φ) := by
  have hUS : ∀ g q, N.Wn7 ρ g q * N.S21 ρ (slotR (N.hostAt ρ 7) (N.bk ρ 7) g q) = N.S22 ρ (slotR (N.hostAt ρ 7) (N.bk ρ 7) g q) := by
    intro g q
    rcases hq : N.hostAt ρ 7 q with _ | ⟨c, s, t⟩
    · rw [slotR_bank hq]
      exact N.hZ7 ρ g q hq
    · rw [slotR_host hq]
      have hw := N.hostWin ρ 7 q c (s, t) hq
      fin_cases c
      · exact absurd hw (by decide)
      · exact absurd hw (by decide)
      · exact absurd hw (by decide)
      · exact absurd hw (by decide)
      · exact absurd hw (by decide)
      · exact absurd hw (by decide)
      · cases s <;> exact N.hHZ_F1_7 ρ g q _ hq
      · cases s <;> exact N.hHZ_F2_7 ρ g q _ hq
      · cases s <;> exact N.hHZ_F3_7 ρ g q _ hq
  have h := gistageE_bwd (N.Jc ρ 7) N.r7 N.G7 (N.N7 ρ) (N.Wn7 ρ) (N.hN7 ρ) (N.hW7 ρ)
    (fun g q => N.S21 ρ (slotR (N.hostAt ρ 7) (N.bk ρ 7) g q)) (cOne Γ C α) (cOne Γ C α)
  have h' : GRoute (bIn N.I.tv N.r7 (fun d => (N.G7 d).Xm)
        (fun g q => N.S21 ρ (slotR (N.hostAt ρ 7) (N.bk ρ 7) g q)) (cOne Γ C α))
      (mkS N.xi8 N.yi8 (fun g q => N.S22 ρ (slotR (N.hostAt ρ 7) (N.bk ρ 7) g q)) (cOne Γ C α)) GB
      (fun φ => (Fintype.card Γ : ℝ) * (N.Ic ρ 7).cost φ) := by
    have e : bOut N.I.tv N.r7 (fun d => (N.G7 d).Xm)
        (fun g q => N.Wn7 ρ g q * N.S21 ρ (slotR (N.hostAt ρ 7) (N.bk ρ 7) g q)) (cOne Γ C α)
        = mkS N.xi8 N.yi8 (fun g q => N.S22 ρ (slotR (N.hostAt ρ 7) (N.bk ρ 7) g q)) (cOne Γ C α) := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · exact N.x78 g t
      · exact N.y78 g t
      · exact hUS g q
      · rfl
    rw [← e]
    exact h
  refine ghliftQ7 (N.hostAt ρ 7) (N.bk ρ 7) (N.hok ρ 7) h' (fun g t => rfl) (fun g t => rfl)
    (fun g t => rfl) (fun g t => rfl) (fun g q => rfl) (fun g q => rfl) (fun g c => rfl) (fun g c => rfl) ?_
    (fun _ _ _ => rfl) GB_loc
  intro r hr
  rcases r with ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
  · exact (N.hHZn_F1_7 ρ g (false, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact (N.hHZn_F1_7 ρ g (true, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact (N.hHZn_F2_7 ρ g (false, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact (N.hHZn_F2_7 ρ g (true, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact (N.hHZn_F3_7 ρ g (false, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact (N.hHZn_F3_7 ρ g (true, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact absurd ((cover_iff _ _).mpr ⟨jX (g,t), rfl⟩) hr
  · exact absurd ((cover_iff _ _).mpr ⟨jY (g,t), rfl⟩) hr
  · exact (N.hZn7 ρ g b (fun q hq hb => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_bank hq, hb]; rfl⟩))).symm
  · exact absurd ((cover_iff _ _).mpr ⟨jC (g,c), rfl⟩) hr

/-- the free adapters before stage 8 of run `ρ`: every bank from `Zb` to `Zp`, every host of a window. -/
lemma GHost401.adapt8 (ρ : Fin 8) :
    GRoute (N.S22 ρ) (N.S23 ρ) id (fun _ => 0) := by
  have H1 := GRoute.reach_all (N.S22 ρ) (N.S23 ρ) (fun _ _ => 0) (by
      rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
      · exact N.hHP_F1_8 ρ g (false, t)
      · exact N.hHP_F1_8 ρ g (true, t)
      · exact N.hHP_F2_8 ρ g (false, t)
      · exact N.hHP_F2_8 ρ g (true, t)
      · exact N.hHP_F3_8 ρ g (false, t)
      · exact N.hHP_F3_8 ρ g (true, t)
      · exact GReach.refl _
      · exact GReach.refl _
      · exact N.hP8 ρ g b
      · exact GReach.refl _)
  exact H1.cast (fun φ => by simp)

/-- stage 8 of run `ρ` (pair 4): the slot `q` of `g` on its bank or on its host. -/
lemma GHost401.stage8 (ρ : Fin 8) :
    GRoute (N.S23 ρ) (N.S24 ρ) (liftQ8 (Γ := Γ) (T := T) (C := C) (N.bk ρ 8) GF)
      (fun φ => (Fintype.card Γ : ℝ) * (N.Ic ρ 8).cost φ) := by
  have hUS : ∀ g q, N.Wn8 ρ g q * N.S23 ρ (slotR (N.hostAt ρ 8) (N.bk ρ 8) g q) = N.S24 ρ (slotR (N.hostAt ρ 8) (N.bk ρ 8) g q) := by
    intro g q
    rcases hq : N.hostAt ρ 8 q with _ | ⟨c, s, t⟩
    · rw [slotR_bank hq]
      exact N.hZ8 ρ g q hq
    · rw [slotR_host hq]
      have hw := N.hostWin ρ 8 q c (s, t) hq
      fin_cases c
      · exact absurd hw (by decide)
      · exact absurd hw (by decide)
      · exact absurd hw (by decide)
      · exact absurd hw (by decide)
      · exact absurd hw (by decide)
      · exact absurd hw (by decide)
      · cases s <;> exact N.hHZ_F1_8 ρ g q _ hq
      · cases s <;> exact N.hHZ_F2_8 ρ g q _ hq
      · cases s <;> exact N.hHZ_F3_8 ρ g q _ hq
  have h := gistageE_fwd (N.Jc ρ 8) N.r8 N.G8 (N.N8 ρ) (N.Wn8 ρ) (N.hN8 ρ) (N.hW8 ρ)
    (fun g q => N.S23 ρ (slotR (N.hostAt ρ 8) (N.bk ρ 8) g q)) (cOne Γ C α) (cOne Γ C α)
  have h' : GRoute (bIn N.I.tv N.r8 (fun d => (N.G8 d).Xm)
        (fun g q => N.S23 ρ (slotR (N.hostAt ρ 8) (N.bk ρ 8) g q)) (cOne Γ C α))
      (mkS N.xo8 N.yo8 (fun g q => N.S24 ρ (slotR (N.hostAt ρ 8) (N.bk ρ 8) g q)) (cOne Γ C α)) GF
      (fun φ => (Fintype.card Γ : ℝ) * (N.Ic ρ 8).cost φ) := by
    have e : bOut N.I.tv N.r8 (fun d => (N.G8 d).Xm)
        (fun g q => N.Wn8 ρ g q * N.S23 ρ (slotR (N.hostAt ρ 8) (N.bk ρ 8) g q)) (cOne Γ C α)
        = mkS N.xo8 N.yo8 (fun g q => N.S24 ρ (slotR (N.hostAt ρ 8) (N.bk ρ 8) g q)) (cOne Γ C α) := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · rfl
      · rfl
      · exact hUS g q
      · rfl
    rw [← e]
    exact h
  refine ghliftQ8 (N.hostAt ρ 8) (N.bk ρ 8) (N.hok ρ 8) h' (fun g t => rfl) (fun g t => rfl)
    (fun g t => rfl) (fun g t => rfl) (fun g q => rfl) (fun g q => rfl) (fun g c => rfl) (fun g c => rfl) ?_
    (fun _ _ _ => rfl) GF_loc
  intro r hr
  rcases r with ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
  · exact (N.hHZn_F1_8 ρ g (false, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact (N.hHZn_F1_8 ρ g (true, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact (N.hHZn_F2_8 ρ g (false, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact (N.hHZn_F2_8 ρ g (true, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact (N.hHZn_F3_8 ρ g (false, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact (N.hHZn_F3_8 ρ g (true, t) (fun q hq => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_host hq]; rfl⟩))).symm
  · exact absurd ((cover_iff _ _).mpr ⟨jX (g,t), rfl⟩) hr
  · exact absurd ((cover_iff _ _).mpr ⟨jY (g,t), rfl⟩) hr
  · exact (N.hZn8 ρ g b (fun q hq hb => hr ((cover_iff _ _).mpr
      ⟨jS (g, q), by show slotR _ _ g q = _; rw [slotR_bank hq, hb]; rfl⟩))).symm
  · exact absurd ((cover_iff _ _).mpr ⟨jC (g,c), rfl⟩) hr

/-- the finals of the replica of run `ρ`: the remaining climbs of F1-F3 and pair 4's final block. -/
lemma GHost401.fin (ρ : Fin 8) :
    GRoute (N.S24 ρ) (N.S25 ρ) id (fun φ => (Fintype.card Γ : ℝ) *
      (N.hcost ρ 6 φ + N.hcost ρ 7 φ + N.hcost ρ 8 φ + (Fintype.card T : ℝ) * (N.cX4 φ + N.cY4 φ))) := by
  have H1 := GRoute.reach_all (N.S24 ρ) (N.S25 ρ)
    (mkR4 (fun _ t φ => bcost φ (N.hrem ρ 6 (false, t))) (fun _ t φ => bcost φ (N.hrem ρ 6 (true, t))) (fun _ t φ => bcost φ (N.hrem ρ 7 (false, t))) (fun _ t φ => bcost φ (N.hrem ρ 7 (true, t))) (fun _ t φ => bcost φ (N.hrem ρ 8 (false, t))) (fun _ t φ => bcost φ (N.hrem ρ 8 (true, t))) (fun _ _ => N.cX4) (fun _ _ => N.cY4) (fun _ _ _ => 0) (fun _ _ _ => 0)) (by
      rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
      · exact (N.hHE_F1 ρ g t).1
      · exact (N.hHE_F1 ρ g t).2
      · exact (N.hHE_F2 ρ g t).1
      · exact (N.hHE_F2 ρ g t).2
      · exact (N.hHE_F3 ρ g t).1
      · exact (N.hHE_F3 ρ g t).2
      · exact GReach.ofX (N.fX4 g t)
      · exact GReach.ofX (N.fY4 g t)
      · exact GReach.refl _
      · exact GReach.refl _)
  refine H1.cast (fun φ => ?_)
  simp_rw [mkR4_map (fun c : (ℕ → ℝ) → ℝ => c φ)]
  rw [sum_mkR4]
  simp only [GHost401.hcost, sum_const, card_univ, nsmul_eq_mul, mul_zero, add_zero, zero_add,
    Finset.sum_add_distrib, Finset.sum_const_zero, smul_zero]
  ring

/-- gate layer C4 of run `ρ` (Shea's, word for word): twins have equal frames. -/
lemma GHost401.gateC4 (ρ : Fin 8) : XRoute (N.S25 ρ) (N.S25 ρ) (gscQ pCQ_4 kCQ_4) (fun _ => 0) := by
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

/-- gate layer C3 of run `ρ` (Shea's, word for word): twins have equal frames. -/
lemma GHost401.gateC3 (ρ : Fin 8) : XRoute (N.S25 ρ) (N.S25 ρ) (gscQ pCQ_3 kCQ_3) (fun _ => 0) := by
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

/-- gate layer C2 of run `ρ` (Shea's, word for word): twins have equal frames. -/
lemma GHost401.gateC2 (ρ : Fin 8) : XRoute (N.S25 ρ) (N.S25 ρ) (gscQ pCQ_2 kCQ_2) (fun _ => 0) := by
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
end XHostD
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.XHostD.GHost401.stage0
#print axioms OAI.PowerSaving.XHostD.GHost401.stage1
#print axioms OAI.PowerSaving.XHostD.GHost401.stage2
#print axioms OAI.PowerSaving.XHostD.GHost401.stage3
#print axioms OAI.PowerSaving.XHostD.GHost401.stage4
#print axioms OAI.PowerSaving.XHostD.GHost401.stage5
#print axioms OAI.PowerSaving.XHostD.GHost401.stage6
#print axioms OAI.PowerSaving.XHostD.GHost401.stage7
#print axioms OAI.PowerSaving.XHostD.GHost401.stage8
#print axioms OAI.PowerSaving.XHostD.GHost401.fin

end
-- bos_merge: end Submission.Work.XHostD.HStage

-- bos_merge: begin Submission.Work.XHostD.HCert
section

/-!
# (key: bridge-host) The certificate of the HOSTED nine-stage word

Copy of Work/Bridge401/GNetCert.lean (Ryan Shea's complex588 tree; written by Nil Mamano's gen401.py) for `GHost401`:
the scalar map of a run is Shea's `chainQ` of the bank map `bk` (a hosted stage has the scalar map of a banked one), so
the sweep, the exchange and the scalar identity are Shea's, word for word.  Written by h-L3-build/gen/gen_hnet.py,
prepared with assistance from Claude.  PER-RUN version (one host table per run) written by fsp-perrun/tools/mk_perrun.py (wht43, 14 Oct 2026) from h-L3-build's file by checked text substitution; prepared with assistance from Claude.  TWO-PROVIDER version (a per-call invocation `Ic ρ l` with the target vectors of `I`, per-call entrance labels and residuals) written by lg-a2a4/tools/mk_disp.py (wht43, 14 Oct 2026) from fsp-perrun's file by checked text substitution; prepared with assistance from Claude.  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace OAI
namespace PowerSaving
namespace XHostD
open Binary Matrix Finset RAM SS CB RF BR GF GX XHost
noncomputable section

section Net
variable {H T Sl C α Γ : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C] [Fintype α] [DecidableEq α]
  [Fintype Γ] [DecidableEq Γ]
variable {nb : ℕ} (N : GHost401 H T Sl C α Γ nb)

/-- the whole run `ρ` before the exchange, on the roles of a run. -/
lemma GHost401.run (ρ : Fin 8) :
    GRoute (N.S0 ρ) (N.S25 ρ) (chainQ (N.bk ρ)) (fun φ => (Fintype.card Γ : ℝ) * N.runUnit ρ φ) := by
  have R := ((((((((((((((((((((((((((((((((((N.adapt0 ρ)).trans (N.stage0 ρ)).trans (N.adapt1 ρ)).trans (N.stage1 ρ)).trans ((N.climbA2 ρ))).trans (GRoute.ofX (N.gateA2 ρ))).trans (N.adapt2 ρ)).trans (N.stage2 ρ)).trans ((N.climbB2 ρ))).trans (GRoute.ofX (N.gateB2 ρ))).trans (N.adapt3 ρ)).trans (N.stage3 ρ)).trans ((N.climbA3 ρ))).trans (GRoute.ofX (N.gateA3 ρ))).trans (N.adapt4 ρ)).trans (N.stage4 ρ)).trans ((N.climbB3 ρ))).trans (GRoute.ofX (N.gateB3 ρ))).trans (N.adapt5 ρ)).trans (N.stage5 ρ)).trans ((N.climbA4 ρ))).trans (GRoute.ofX (N.gateA4 ρ))).trans (N.adapt6 ρ)).trans (N.stage6 ρ)).trans ((N.climbB4 ρ))).trans (GRoute.ofX (N.gateB4 ρ))).trans (N.adapt7 ρ)).trans (N.stage7 ρ)).trans (N.adapt8 ρ)).trans (N.stage8 ρ)).trans ((N.fin ρ))).trans (GRoute.ofX (N.gateC4 ρ))).trans (GRoute.ofX (N.gateC3 ρ))).trans (GRoute.ofX (N.gateC2 ρ))
  refine R.cast (fun φ => ?_)
  simp only [GHost401.runUnit]
  ring

/-- run `ρ` on all roles: the other replicas wait (before their run at `InitD`, after it at `FinD`). -/
lemma GHost401.runFull (ρ : Fin 8) :
    GRoute (N.Sfull ρ.castSucc) (N.Sfull ρ.succ) (liftRun4 ρ (chainQ (N.bk ρ)))
      (fun φ => (Fintype.card Γ : ℝ) * N.runUnit ρ φ) := by
  refine GRoute.lift (emRun4 ρ) (h := chainQ (N.bk ρ)) ?_ (fun x => ?_) (fun x i hi => ?_) (fun i hi => ?_)
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

/-- **the 8 runs one after the other** (summed costs: each run has its own host table). -/
lemma GHost401.sweep :
    GRoute (N.Sfull 0) (N.Sfull (Fin.last 8)) (sweepMap (fun ρ : Fin 8 => liftRun4 ρ (chainQ (N.bk ρ))))
      (fun φ => ∑ ρ : Fin 8, (Fintype.card Γ : ℝ) * N.runUnit ρ φ) :=
  GRoute.sweep 8 N.Sfull _ (fun ρ φ => (Fintype.card Γ : ℝ) * N.runUnit ρ φ) (fun ρ => N.runFull ρ)

/-- **the padding blocks**: ONE block of rank `pad b` per bank. -/
lemma GHost401.padR :
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
def GHost401.corr : BRole401 Γ T nb C → Space α :=
  mk401 (fun _ => mkD4 (fun _ _ => 0) (fun g t => N.u g t) (fun _ _ => 0) (fun g t => N.u g t) (fun _ _ => 0) (fun g t => N.u g t) (fun _ _ => 0) (fun g t => N.u g t)) (fun _ _ => 0) (fun _ _ => 0)

def GHost401.Sz : BRole401 Γ T nb C → CMat α := fun r => shift (N.corr r) * N.Sfin r

/-- **The scratch certificate of the nine-stage word with entrance gauges and residual banks (PR #401)**, in whole
blocks, with its exact price for every price list. -/
theorem ghost_certificate :
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
    (fun φ => by simp only [GHost401.unit, mul_add, Finset.mul_sum, add_zero] <;> try ring)
  have h0 : ∀ (ρ' : Fin 8) (d : BDat4 Γ T), N.Sfull 0 (Sum.inl (Sum.inl (ρ', d))) = N.InitD d :=
    fun ρ' d => by simp [GHost401.Sfull, mk401]
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
        (actPoint brec401 ∘ (id ∘ (id ∘ sweepMap (fun ρ : Fin 8 => liftRun4 ρ (chainQ (N.bk ρ)))))) x (Sum.inl l)
          = x (Sum.inl l) := by
    intro x _ l
    rw [Function.comp_apply, Function.comp_apply, Function.comp_apply, id_eq, id_eq, actPoint_brec401]
    rcases l with (⟨ρ, d⟩|⟨g,b⟩)
    · rcases d with ((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))
      · show ((1:ℚ):ℂ) * sweepMap (fun i : Fin 8 => liftRun4 i (chainQ (N.bk i))) x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inl (Sum.inl (Sum.inr ((g,t)))))))) = _
        rw [sweep_data4 N.bk, chainQ_eq]
        show ((1:ℚ):ℂ) * x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inl (Sum.inl (Sum.inl ((g,t)))))))) = x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inl (Sum.inl (Sum.inl ((g,t))))))))
        first | (push_cast; ring) | simp
      · show ((-1:ℚ):ℂ) * sweepMap (fun i : Fin 8 => liftRun4 i (chainQ (N.bk i))) x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inl (Sum.inl (Sum.inl ((g,t)))))))) = _
        rw [sweep_data4 N.bk, chainQ_eq]
        show ((-1:ℚ):ℂ) * (-x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inl (Sum.inl (Sum.inr ((g,t))))))))) = x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inl (Sum.inl (Sum.inr ((g,t))))))))
        first | (push_cast; ring) | simp
      · show ((1:ℚ):ℂ) * sweepMap (fun i : Fin 8 => liftRun4 i (chainQ (N.bk i))) x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inl (Sum.inr (Sum.inr ((g,t)))))))) = _
        rw [sweep_data4 N.bk, chainQ_eq]
        show ((1:ℚ):ℂ) * x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inl (Sum.inr (Sum.inl ((g,t)))))))) = x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inl (Sum.inr (Sum.inl ((g,t))))))))
        first | (push_cast; ring) | simp
      · show ((-1:ℚ):ℂ) * sweepMap (fun i : Fin 8 => liftRun4 i (chainQ (N.bk i))) x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inl (Sum.inr (Sum.inl ((g,t)))))))) = _
        rw [sweep_data4 N.bk, chainQ_eq]
        show ((-1:ℚ):ℂ) * (-x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inl (Sum.inr (Sum.inr ((g,t))))))))) = x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inl (Sum.inr (Sum.inr ((g,t))))))))
        first | (push_cast; ring) | simp
      · show ((1:ℚ):ℂ) * sweepMap (fun i : Fin 8 => liftRun4 i (chainQ (N.bk i))) x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inr (Sum.inr ((g,t))))))) = _
        rw [sweep_data4 N.bk, chainQ_eq]
        show ((1:ℚ):ℂ) * x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inr (Sum.inl ((g,t))))))) = x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inr (Sum.inl ((g,t)))))))
        first | (push_cast; ring) | simp
      · show ((-1:ℚ):ℂ) * sweepMap (fun i : Fin 8 => liftRun4 i (chainQ (N.bk i))) x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inr (Sum.inl ((g,t))))))) = _
        rw [sweep_data4 N.bk, chainQ_eq]
        show ((-1:ℚ):ℂ) * (-x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inr (Sum.inr ((g,t)))))))) = x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inr (Sum.inr ((g,t)))))))
        first | (push_cast; ring) | simp
      · show ((1:ℚ):ℂ) * sweepMap (fun i : Fin 8 => liftRun4 i (chainQ (N.bk i))) x (Sum.inl (Sum.inl (ρ, Sum.inr (Sum.inr ((g,t)))))) = _
        rw [sweep_data4 N.bk, chainQ_eq]
        show ((1:ℚ):ℂ) * x (Sum.inl (Sum.inl (ρ, Sum.inr (Sum.inl ((g,t)))))) = x (Sum.inl (Sum.inl (ρ, Sum.inr (Sum.inl ((g,t))))))
        first | (push_cast; ring) | simp
      · show ((-1:ℚ):ℂ) * sweepMap (fun i : Fin 8 => liftRun4 i (chainQ (N.bk i))) x (Sum.inl (Sum.inl (ρ, Sum.inr (Sum.inl ((g,t)))))) = _
        rw [sweep_data4 N.bk, chainQ_eq]
        show ((-1:ℚ):ℂ) * (-x (Sum.inl (Sum.inl (ρ, Sum.inr (Sum.inr ((g,t))))))) = x (Sum.inl (Sum.inl (ρ, Sum.inr (Sum.inr ((g,t))))))
        first | (push_cast; ring) | simp
    · show ((1:ℚ):ℂ) * sweepMap (fun i : Fin 8 => liftRun4 i (chainQ (N.bk i))) x (Sum.inl (Sum.inr (g, b))) = _
      rw [sweep_bank4 N.bk]
      first | (push_cast; ring) | simp
  exact gcert_of_groute (Sum.inl : BLive401 Γ T nb → BRole401 Γ T nb C) (N.Sfull 0)
    (fun r => N.Sz (bpull401 r)) _ _ Rt hS hg hT

end Net
end
end XHostD
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.XHostD.GHost401.run
#print axioms OAI.PowerSaving.XHostD.GHost401.runFull
#print axioms OAI.PowerSaving.XHostD.ghost_certificate

end
-- bos_merge: end Submission.Work.XHostD.HCert
