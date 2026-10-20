import Submission.Work.XHostT.TStage

/-!
# (key: bridge-host-cross) The certificate of the CROSS-REPLICA hosted nine-stage word

The `9 nR` calls of `XNet` one after the other in the global order (`GRoute.sweep` over `Fin (9 nR)`, call `cl τ` at
time `τ`), then ONE padding block per bank, Shea's free shifts and his signed exchange (`brecT`).  The scalar identity
needs no new mathematics: by `sweep_local` the data of replica `ρ` end as ρ's own nine run-local maps composed in stage
order (`pcomp_full`), which is Shea's `chainQ` without banks (`chainT_eq`), whatever the interleaving.  The price is the
sum over all calls of all replicas, and the pads (`xnet_certificate`).
Written by p-a3 (wht45/lever, 19 Oct 2026) after fsp-perrun's Work/XHostR/HCert.lean (wht43), itself a copy of
Work/Bridge401/GNetCert.lean (Ryan Shea's complex588 tree; Nil Mamano's gen401); hosting by DaysSky (PR #442);
prepared with assistance from Claude.  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
namespace OAI
namespace PowerSaving
namespace XHostT
open Binary Matrix Finset RAM SS CB RF BR GF GX XHost
noncomputable section

section Chain
variable {Γ T C : Type} {nb : ℕ}

/-- ONE replica's nine calls composed in stage order (bank-free `chainQ`). -/
def chainT : (BRun4 Γ T nb C → ℂ) → (BRun4 Γ T nb C → ℂ) :=
  runMap 8 ∘ (runMap 7 ∘ (runMap 6 ∘ (runMap 5 ∘ (runMap 4 ∘ (runMap 3 ∘ (runMap 2 ∘ (runMap 1 ∘ (runMap 0 ∘ id))))))))

/-- the same, written out. -/
def chainTx : (BRun4 Γ T nb C → ℂ) → (BRun4 Γ T nb C → ℂ) :=
  ((gscQ pCQ_2 kCQ_2 ∘ (gscQ pCQ_3 kCQ_3 ∘ (gscQ pCQ_4 kCQ_4 ∘ id))) ∘ sfR 4) ∘ ((id ∘ sbR 4) ∘
  (((gscQ pABQ_4 kBQ_4 ∘ id) ∘ sfR 3) ∘ (((gscQ pABQ_4 kAQ_4 ∘ id) ∘ sbR 3) ∘
  (((gscQ pABQ_3 kBQ_3 ∘ id) ∘ sfR 2) ∘ (((gscQ pABQ_3 kAQ_3 ∘ id) ∘ sbR 2) ∘
  (((gscQ pABQ_2 kBQ_2 ∘ id) ∘ sfR 1) ∘ (((gscQ pABQ_2 kAQ_2 ∘ id) ∘ sbR 1) ∘ ((id ∘ sfR 1) ∘ id))))))))

lemma chainT_x : chainT (Γ := Γ) (T := T) (nb := nb) (C := C) = chainTx := rfl

/-- **The scalar identity of a replica** (Shea's `chainQ_eq`): `X_p = -y_p`, `Y_p = x_p` on every pair. -/
lemma chainT_eq (x : BRun4 Γ T nb C → ℂ) (d : BDat4 Γ T) :
    chainT x (.inl (.inl d)) = mkD4 (fun g t => -x (rqY1 (g,t))) (fun g t => x (rqX1 (g,t)))
      (fun g t => -x (rqY2 (g,t))) (fun g t => x (rqX2 (g,t))) (fun g t => -x (rqY3 (g,t))) (fun g t => x (rqX3 (g,t)))
      (fun g t => -x (rqY4 (g,t))) (fun g t => x (rqX4 (g,t))) d := by
  rw [chainT_x]
  rcases d with ((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))
  all_goals
    simp [chainTx, gscQ, sfR, sbR, dDecD, dD, mkR4, mkD4, pABQ_2, kAQ_2, kBQ_2, pCQ_2, kCQ_2, pABQ_3, kAQ_3, kBQ_3,
      pCQ_3, kCQ_3, pABQ_4, kAQ_4, kBQ_4, pCQ_4, kCQ_4, rqX1, rqY1, rqX2, rqY2, rqX3, rqY3, rqX4, rqY4, dqX1, dqY1,
      dqX2, dqY2, dqX3, dqY3, dqX4, dqY4, rqS, rqC]
    try ring

lemma hpd_pABQ_2 : ∀ d : BDat4 Γ T, ∃ d', (pABQ_2 (nb := nb) (C := C) (.inl (.inl d))) = .inl (.inl d') := by
  intro d; rcases d with ((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩)) <;> exact ⟨_, rfl⟩
lemma hpd_pABQ_3 : ∀ d : BDat4 Γ T, ∃ d', (pABQ_3 (nb := nb) (C := C) (.inl (.inl d))) = .inl (.inl d') := by
  intro d; rcases d with ((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩)) <;> exact ⟨_, rfl⟩
lemma hpd_pABQ_4 : ∀ d : BDat4 Γ T, ∃ d', (pABQ_4 (nb := nb) (C := C) (.inl (.inl d))) = .inl (.inl d') := by
  intro d; rcases d with ((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩)) <;> exact ⟨_, rfl⟩
lemma hpd_pCQ_2 : ∀ d : BDat4 Γ T, ∃ d', (pCQ_2 (nb := nb) (C := C) (.inl (.inl d))) = .inl (.inl d') := by
  intro d; rcases d with ((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩)) <;> exact ⟨_, rfl⟩
lemma hpd_pCQ_3 : ∀ d : BDat4 Γ T, ∃ d', (pCQ_3 (nb := nb) (C := C) (.inl (.inl d))) = .inl (.inl d') := by
  intro d; rcases d with ((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩)) <;> exact ⟨_, rfl⟩
lemma hpd_pCQ_4 : ∀ d : BDat4 Γ T, ∃ d', (pCQ_4 (nb := nb) (C := C) (.inl (.inl d))) = .inl (.inl d') := by
  intro d; rcases d with ((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩)) <;> exact ⟨_, rfl⟩

/-- every call's run-local map reads only data. -/
lemma DL_runMap (l : Fin 9) : DL (runMap (Γ := Γ) (T := T) (nb := nb) (C := C) l) := by
  fin_cases l
  · show DL (id ∘ sfR 1)
    exact DL_comp DL_id ((sfR_fwd 1 prng1).dl prng1)
  · show DL ((gscQ pABQ_2 kAQ_2 ∘ id) ∘ sbR 1)
    exact DL_comp (DL_comp (DL_gsc _ kAQ_2 hpd_pABQ_2) DL_id) ((sbR_bwd 1 prng1).dl prng1)
  · show DL ((gscQ pABQ_2 kBQ_2 ∘ id) ∘ sfR 1)
    exact DL_comp (DL_comp (DL_gsc _ kBQ_2 hpd_pABQ_2) DL_id) ((sfR_fwd 1 prng1).dl prng1)
  · show DL ((gscQ pABQ_3 kAQ_3 ∘ id) ∘ sbR 2)
    exact DL_comp (DL_comp (DL_gsc _ kAQ_3 hpd_pABQ_3) DL_id) ((sbR_bwd 2 prng2).dl prng2)
  · show DL ((gscQ pABQ_3 kBQ_3 ∘ id) ∘ sfR 2)
    exact DL_comp (DL_comp (DL_gsc _ kBQ_3 hpd_pABQ_3) DL_id) ((sfR_fwd 2 prng2).dl prng2)
  · show DL ((gscQ pABQ_4 kAQ_4 ∘ id) ∘ sbR 3)
    exact DL_comp (DL_comp (DL_gsc _ kAQ_4 hpd_pABQ_4) DL_id) ((sbR_bwd 3 prng3).dl prng3)
  · show DL ((gscQ pABQ_4 kBQ_4 ∘ id) ∘ sfR 3)
    exact DL_comp (DL_comp (DL_gsc _ kBQ_4 hpd_pABQ_4) DL_id) ((sfR_fwd 3 prng3).dl prng3)
  · show DL (id ∘ sbR 4)
    exact DL_comp DL_id ((sbR_bwd 4 prng4).dl prng4)
  · show DL ((gscQ pCQ_2 kCQ_2 ∘ (gscQ pCQ_3 kCQ_3 ∘ (gscQ pCQ_4 kCQ_4 ∘ id))) ∘ sfR 4)
    exact DL_comp (DL_comp (DL_gsc _ kCQ_2 hpd_pCQ_2) (DL_comp (DL_gsc _ kCQ_3 hpd_pCQ_3)
      (DL_comp (DL_gsc _ kCQ_4 hpd_pCQ_4) DL_id))) ((sfR_fwd 4 prng4).dl prng4)

/-- every call's run-local map keeps the banks. -/
lemma KB_runMap (l : Fin 9) : KB (runMap (Γ := Γ) (T := T) (nb := nb) (C := C) l) := by
  fin_cases l
  · show KB (id ∘ sfR 1)
    exact KB_comp KB_id (sfR_fwd 1 prng1).hS
  · show KB ((gscQ pABQ_2 kAQ_2 ∘ id) ∘ sbR 1)
    exact KB_comp (KB_comp (KB_gsc pABQ_2 kAQ_2 (fun ⟨_, _⟩ => rfl)) KB_id) (sbR_bwd 1 prng1).hS
  · show KB ((gscQ pABQ_2 kBQ_2 ∘ id) ∘ sfR 1)
    exact KB_comp (KB_comp (KB_gsc pABQ_2 kBQ_2 (fun ⟨_, _⟩ => rfl)) KB_id) (sfR_fwd 1 prng1).hS
  · show KB ((gscQ pABQ_3 kAQ_3 ∘ id) ∘ sbR 2)
    exact KB_comp (KB_comp (KB_gsc pABQ_3 kAQ_3 (fun ⟨_, _⟩ => rfl)) KB_id) (sbR_bwd 2 prng2).hS
  · show KB ((gscQ pABQ_3 kBQ_3 ∘ id) ∘ sfR 2)
    exact KB_comp (KB_comp (KB_gsc pABQ_3 kBQ_3 (fun ⟨_, _⟩ => rfl)) KB_id) (sfR_fwd 2 prng2).hS
  · show KB ((gscQ pABQ_4 kAQ_4 ∘ id) ∘ sbR 3)
    exact KB_comp (KB_comp (KB_gsc pABQ_4 kAQ_4 (fun ⟨_, _⟩ => rfl)) KB_id) (sbR_bwd 3 prng3).hS
  · show KB ((gscQ pABQ_4 kBQ_4 ∘ id) ∘ sfR 3)
    exact KB_comp (KB_comp (KB_gsc pABQ_4 kBQ_4 (fun ⟨_, _⟩ => rfl)) KB_id) (sfR_fwd 3 prng3).hS
  · show KB (id ∘ sbR 4)
    exact KB_comp KB_id (sbR_bwd 4 prng4).hS
  · show KB ((gscQ pCQ_2 kCQ_2 ∘ (gscQ pCQ_3 kCQ_3 ∘ (gscQ pCQ_4 kCQ_4 ∘ id))) ∘ sfR 4)
    exact KB_comp (KB_comp (KB_gsc pCQ_2 kCQ_2 (fun ⟨_, _⟩ => rfl)) (KB_comp (KB_gsc pCQ_3 kCQ_3 (fun ⟨_, _⟩ => rfl))
      (KB_comp (KB_gsc pCQ_4 kCQ_4 (fun ⟨_, _⟩ => rfl)) KB_id))) (sfR_fwd 4 prng4).hS

end Chain

section Net
variable {H T Sl C α Γ : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C] [Fintype α] [DecidableEq α]
  [Fintype Γ] [DecidableEq Γ]
variable {nb nR : ℕ} (N : XNet H T Sl C α Γ nb nR)

/-- the scalar map of the call at time `τ`. -/
def XNet.mapAt (τ : Fin (9 * nR)) : (BRoleT Γ T nb C nR → ℂ) → (BRoleT Γ T nb C nR → ℂ) :=
  liftRunT (N.cl τ).1 (runMap (N.cl τ).2)

/-- the call at time `τ`. -/
lemma XNet.callAt (τ : Fin (9 * nR)) :
    GRoute (N.Ffr τ.val) (N.Ffr (τ.val + 1)) (N.mapAt τ)
      (fun φ => (Fintype.card Γ : ℝ) * N.callU (N.cl τ).1 (N.cl τ).2 φ) := by
  have h := N.call (N.cl τ).1 (N.cl τ).2
  rw [N.hcl τ] at h
  exact h

/-- **the interleaved sweep**: all `9 nR` calls in the global order; the price is the sum over all calls. -/
lemma XNet.sweepT :
    GRoute (N.Ffr 0) (N.Ffr (9 * nR)) (sweepMap N.mapAt)
      (fun φ => (Fintype.card Γ : ℝ) * ∑ ρ : Fin nR, ∑ l : Fin 9, N.callU ρ l φ) := by
  have R := GRoute.sweep (9 * nR) (fun i : Fin (9 * nR + 1) => N.Ffr i.val) N.mapAt _ (fun τ => N.callAt τ)
  refine R.cast (fun φ => ?_)
  show ∑ τ : Fin (9 * nR), (Fintype.card Γ : ℝ) * N.callU (N.cl τ).1 (N.cl τ).2 φ
    = (Fintype.card Γ : ℝ) * ∑ ρ : Fin nR, ∑ l : Fin 9, N.callU ρ l φ
  rw [← Finset.mul_sum, ← Fintype.sum_prod_type']
  congr 1
  exact Fintype.sum_bijective N.cl N.cl_bij _ _ (fun _ => rfl)

/-- **the padding blocks**: ONE block of rank `pad b` per bank. -/
lemma XNet.padR :
    GRoute (N.Ffr (9 * nR)) N.Sfin id (fun φ => (Fintype.card Γ : ℝ) * ∑ b, bcost φ (N.pad b)) := by
  have H1 := GRoute.reach_all (N.Ffr (9 * nR)) N.Sfin
    (mkT (fun _ _ _ => 0) (fun _ b φ => bcost φ (N.pad b)) (fun _ _ _ => 0)) (by
      rintro ((⟨ρ', d⟩|⟨g,b⟩)|⟨g,c⟩)
      · show GReach (N.LD (progT N.tm ρ' (9 * nR)) ρ' (9 * nR) d) (N.FinD d) (fun _ => 0)
        rw [N.prog_end ρ']
        exact GReach.refl _
      · exact N.bpad g b
      · exact GReach.refl _)
  refine H1.cast (fun φ => ?_)
  simp_rw [mkT_map (fun c : (ℕ → ℝ) → ℝ => c φ)]
  rw [sum_mkT]
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_zero, add_zero, zero_add, Finset.sum_const_zero]

/-- the data of replica `ρ` at the end of the sweep: ρ's own nine calls (`sweep_local`, whatever the interleaving). -/
lemma XNet.sweep_data (ρ : Fin nR) (x : BRoleT Γ T nb C nR → ℂ) (d : BDat4 Γ T) :
    sweepMap N.mapAt x (.inl (.inl (ρ, d))) = chainT (x ∘ runPosT ρ) (.inl (.inl d)) := by
  let o : ℕ → Fin nR := fun τ => if h : τ < 9 * nR then (N.cl ⟨τ, h⟩).1 else ρ
  let hh : ℕ → (BRun4 Γ T nb C → ℂ) → (BRun4 Γ T nb C → ℂ) :=
    fun τ => if h : τ < 9 * nR then runMap (N.cl ⟨τ, h⟩).2 else id
  have e : N.mapAt = (fun τ : Fin (9 * nR) => liftRunT (o τ.val) (hh τ.val)) := by
    funext τ
    simp only [XNet.mapAt, o, hh, dif_pos τ.isLt]
  have hDL : ∀ n, DL (hh n) := by
    intro n
    simp only [hh]
    split_ifs
    · exact DL_runMap _
    · exact DL_id
  rw [e, sweep_local hDL (9 * nR) x ρ d]
  -- the composite of ρ's own maps in time order
  have hcall : ∀ l : Fin 9, o (N.tm ρ l) = ρ ∧ hh (N.tm ρ l) = runMap l := by
    intro l
    exact ⟨by simp [o, dif_pos (N.htm_lt ρ l), N.cl_tm ρ l], by simp [hh, dif_pos (N.htm_lt ρ l), N.cl_tm ρ l]⟩
  have hown : ∀ i, i < 9 * nR → o i = ρ → ∃ l : Fin 9, N.tm ρ l = i := by
    intro i hi h
    simp only [o, dif_pos hi] at h
    refine ⟨(N.cl ⟨i, hi⟩).2, ?_⟩
    have e2 := N.hcl ⟨i, hi⟩
    rw [h] at e2
    exact e2
  have step : ∀ l : Fin 9, pcomp o hh ρ (N.tm ρ l + 1) = runMap l ∘ pcomp o hh ρ (N.tm ρ l) := by
    intro l
    rw [pcomp_succ_self (hcall l).1, (hcall l).2]
  have gap : ∀ l l' : Fin 9, l.val + 1 = l'.val → pcomp o hh ρ (N.tm ρ l') = pcomp o hh ρ (N.tm ρ l + 1) := by
    intro l l' hl
    have hlt : N.tm ρ l < N.tm ρ l' := N.htm_mono ρ l l' (by rw [Fin.lt_def]; omega)
    have := pcomp_gap (o := o) (h := hh) (ρ := ρ) (N.tm ρ l + 1) (N.tm ρ l' - (N.tm ρ l + 1)) (by
      intro i h1 h2 hi
      obtain ⟨l'', hl''⟩ := hown i (by have := N.htm_lt ρ l'; omega) hi
      rcases Nat.lt_or_ge l''.val (l.val + 1) with h3 | h3
      · have := N.tm_le ρ (show l'' ≤ l by rw [Fin.le_def]; omega)
        omega
      · have := N.tm_le ρ (show l' ≤ l'' by rw [Fin.le_def]; omega)
        omega)
    rw [show N.tm ρ l + 1 + (N.tm ρ l' - (N.tm ρ l + 1)) = N.tm ρ l' by omega] at this
    exact this
  have gap0 : pcomp o hh ρ (N.tm ρ 0) = id := by
    have := pcomp_gap (o := o) (h := hh) (ρ := ρ) 0 (N.tm ρ 0) (by
      intro i _ h2 hi
      obtain ⟨l'', hl''⟩ := hown i (by have := N.htm_lt ρ 0; omega) hi
      have := N.tm_le ρ (show (0 : Fin 9) ≤ l'' from Fin.zero_le _)
      omega)
    rw [Nat.zero_add] at this
    exact this
  have gapE : pcomp o hh ρ (9 * nR) = pcomp o hh ρ (N.tm ρ 8 + 1) := by
    have h8 := N.htm_lt ρ 8
    have := pcomp_gap (o := o) (h := hh) (ρ := ρ) (N.tm ρ 8 + 1) (9 * nR - (N.tm ρ 8 + 1)) (by
      intro i h1 h2 hi
      obtain ⟨l'', hl''⟩ := hown i (by omega) hi
      have := N.tm_le ρ (show l'' ≤ (8 : Fin 9) from Fin.le_last _)
      omega)
    rw [show N.tm ρ 8 + 1 + (9 * nR - (N.tm ρ 8 + 1)) = 9 * nR by omega] at this
    exact this
  have hfull : pcomp o hh ρ (9 * nR) = chainT := by
    rw [gapE, step 8, gap 7 8 rfl, step 7, gap 6 7 rfl, step 6, gap 5 6 rfl, step 5, gap 4 5 rfl, step 4,
      gap 3 4 rfl, step 3, gap 2 3 rfl, step 2, gap 1 2 rfl, step 1, gap 0 1 rfl, step 0, gap0]
    rfl
  rw [hfull]

/-- the sweep keeps the banks. -/
lemma XNet.sweep_bank (x : BRoleT Γ T nb C nR → ℂ) (s : Γ × Fin nb) :
    sweepMap N.mapAt x (.inl (.inr s)) = x (.inl (.inr s)) :=
  sweepMap_fix (fun r : BRoleT Γ T nb C nR => ∃ s', r = .inl (.inr s')) N.mapAt
    (fun i x r hr => by
      obtain ⟨s', rfl⟩ := hr
      exact KB_runMap _ (x ∘ runPosT (N.cl i).1) s') x _ ⟨s, rfl⟩

/-- the free shifts at the end. -/
def XNet.corr : BRoleT Γ T nb C nR → Space α :=
  mkT (fun _ => mkD4 (fun _ _ => 0) (fun g t => N.u g t) (fun _ _ => 0) (fun g t => N.u g t) (fun _ _ => 0)
    (fun g t => N.u g t) (fun _ _ => 0) (fun g t => N.u g t)) (fun _ _ => 0) (fun _ _ => 0)

def XNet.Sz : BRoleT Γ T nb C nR → CMat α := fun r => shift (N.corr r) * N.Sfin r

/-- the data of every replica at time 0 are the initial frames (the A windows at their start). -/
lemma XNet.h0 (ρ' : Fin nR) (d : BDat4 Γ T) : N.Ffr 0 (.inl (.inl (ρ', d))) = N.InitD d := by
  show N.LD (progT N.tm ρ' 0) ρ' 0 d = N.InitD d
  rw [N.prog_zero ρ']
  rcases d with ((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))
  · rfl
  · rfl
  · exact (N.hH0_A2 ρ' g t).1
  · exact (N.hH0_A2 ρ' g t).2
  · exact (N.hH0_A3 ρ' g t).1
  · exact (N.hH0_A3 ρ' g t).2
  · exact (N.hH0_A4 ρ' g t).1
  · exact (N.hH0_A4 ρ' g t).2

/-- **The scratch certificate of the CROSS-REPLICA hosted nine-stage word** (any replica count, any global order of
the calls, slots hosted in idle data roles of any replica during their windows), in whole blocks, with its exact price
for every price list: the sum over all calls of all replicas and the pads. -/
theorem xnet_certificate :
    GCert α (Sum.inl : BLiveT Γ T nb nR → BRoleT Γ T nb C nR) (fun φ => (Fintype.card Γ : ℝ) * N.unit φ) := by
  have R1 := N.sweepT.trans N.padR
  have R2 : GRoute N.Sfin N.Sz id (fun _ => 0) := GRoute.shifts N.hm N.Sfin N.corr
  have R3 : GRoute N.Sz (fun r => N.Sz (bpullT r)) (actPoint brecT) (fun _ => 0) :=
    GRoute.gate brecT N.Sz _ (fun i j h => by
      have hj : j = bpullT i := by
        by_contra hne
        exact h (by simp [brecT, hne])
      rw [hj])
  have Rt := ((R1.trans R2).trans R3).cast (c' := fun φ => (Fintype.card Γ : ℝ) * N.unit φ)
    (fun φ => by simp only [XNet.unit]; ring)
  have hS : ∀ r, ∃ M, N.Ffr 0 r * M = 1 := by
    rintro ((⟨ρ',d⟩|⟨g,b⟩)|⟨g,c⟩)
    · rw [N.h0]
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
  have hT : ∀ l : BLiveT Γ T nb nR, N.Sz (bpullT (Sum.inl l)) = kernel α * N.Ffr 0 (Sum.inl l) := by
    rintro (⟨ρ', d⟩|⟨g,b⟩)
    · rw [N.h0]
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
  have hg : ∀ x : BRoleT Γ T nb C nR → ℂ,
      (∀ s, (∀ l : BLiveT Γ T nb nR, (Sum.inl l : BRoleT Γ T nb C nR) ≠ s) → x s = 0) →
      ∀ l : BLiveT Γ T nb nR,
        (actPoint brecT ∘ (id ∘ (id ∘ sweepMap N.mapAt))) x (Sum.inl l) = x (Sum.inl l) := by
    intro x _ l
    rw [Function.comp_apply, Function.comp_apply, Function.comp_apply, id_eq, id_eq, actPoint_brecT]
    rcases l with (⟨ρ, d⟩|⟨g,b⟩)
    · rcases d with ((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))
      · show ((1:ℚ):ℂ) * sweepMap N.mapAt x (Sum.inl (Sum.inl (ρ, dqY1 (g,t)))) = _
        rw [N.sweep_data, chainT_eq]
        show ((1:ℚ):ℂ) * x (Sum.inl (Sum.inl (ρ, dqX1 (g,t)))) = x (Sum.inl (Sum.inl (ρ, dqX1 (g,t))))
        simp
      · show ((-1:ℚ):ℂ) * sweepMap N.mapAt x (Sum.inl (Sum.inl (ρ, dqX1 (g,t)))) = _
        rw [N.sweep_data, chainT_eq]
        show ((-1:ℚ):ℂ) * (-x (Sum.inl (Sum.inl (ρ, dqY1 (g,t))))) = x (Sum.inl (Sum.inl (ρ, dqY1 (g,t))))
        simp
      · show ((1:ℚ):ℂ) * sweepMap N.mapAt x (Sum.inl (Sum.inl (ρ, dqY2 (g,t)))) = _
        rw [N.sweep_data, chainT_eq]
        show ((1:ℚ):ℂ) * x (Sum.inl (Sum.inl (ρ, dqX2 (g,t)))) = x (Sum.inl (Sum.inl (ρ, dqX2 (g,t))))
        simp
      · show ((-1:ℚ):ℂ) * sweepMap N.mapAt x (Sum.inl (Sum.inl (ρ, dqX2 (g,t)))) = _
        rw [N.sweep_data, chainT_eq]
        show ((-1:ℚ):ℂ) * (-x (Sum.inl (Sum.inl (ρ, dqY2 (g,t))))) = x (Sum.inl (Sum.inl (ρ, dqY2 (g,t))))
        simp
      · show ((1:ℚ):ℂ) * sweepMap N.mapAt x (Sum.inl (Sum.inl (ρ, dqY3 (g,t)))) = _
        rw [N.sweep_data, chainT_eq]
        show ((1:ℚ):ℂ) * x (Sum.inl (Sum.inl (ρ, dqX3 (g,t)))) = x (Sum.inl (Sum.inl (ρ, dqX3 (g,t))))
        simp
      · show ((-1:ℚ):ℂ) * sweepMap N.mapAt x (Sum.inl (Sum.inl (ρ, dqX3 (g,t)))) = _
        rw [N.sweep_data, chainT_eq]
        show ((-1:ℚ):ℂ) * (-x (Sum.inl (Sum.inl (ρ, dqY3 (g,t))))) = x (Sum.inl (Sum.inl (ρ, dqY3 (g,t))))
        simp
      · show ((1:ℚ):ℂ) * sweepMap N.mapAt x (Sum.inl (Sum.inl (ρ, dqY4 (g,t)))) = _
        rw [N.sweep_data, chainT_eq]
        show ((1:ℚ):ℂ) * x (Sum.inl (Sum.inl (ρ, dqX4 (g,t)))) = x (Sum.inl (Sum.inl (ρ, dqX4 (g,t))))
        simp
      · show ((-1:ℚ):ℂ) * sweepMap N.mapAt x (Sum.inl (Sum.inl (ρ, dqX4 (g,t)))) = _
        rw [N.sweep_data, chainT_eq]
        show ((-1:ℚ):ℂ) * (-x (Sum.inl (Sum.inl (ρ, dqY4 (g,t))))) = x (Sum.inl (Sum.inl (ρ, dqY4 (g,t))))
        simp
    · show ((1:ℚ):ℂ) * sweepMap N.mapAt x (Sum.inl (Sum.inr (g, b))) = _
      rw [N.sweep_bank]
      simp
  exact gcert_of_groute (Sum.inl : BLiveT Γ T nb nR → BRoleT Γ T nb C nR) (N.Ffr 0)
    (fun r => N.Sz (bpullT r)) _ _ Rt hS hg hT

end Net
end
end XHostT
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.XHostT.chainT_eq
#print axioms OAI.PowerSaving.XHostT.XNet.sweepT
#print axioms OAI.PowerSaving.XHostT.XNet.sweep_data
#print axioms OAI.PowerSaving.XHostT.xnet_certificate
