import Submission.Work.CarrierCheck.Scat

/-!
# (key: carrier-check) `hx`, `hy`, `hid` of `CR.Phased` for a checked carrier certificate

`MA = matP un mA`, `MB = matP un mB`, `K = Jrm * Ccm`:

* `Valid.hx`    no gate into an x role:   the x rows of `MB * scatM K * MA` are unit rows;
* `Valid.hy`    no gate reads a y role:   its y columns are unit columns;
* `Valid.hid`   the scalar check:         its block `y ← x` is the identity.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace SSC
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM OAI.PowerSaving.SS
  OAI.PowerSaving.CB OAI.PowerSaving.CR Finset Matrix

namespace CCert
variable {c : CCert}

/-- the gate product of phase A / phase B on the live roles -/
noncomputable def MA (c : CCert) (hv : 0 < c.v) (hR : 0 < c.R) : Matrix c.Rl c.Rl ℚ :=
  matP (c.unemb3 hv hR) c.mA
noncomputable def MB (c : CCert) (hv : 0 < c.v) (hR : 0 < c.R) : Matrix c.Rl c.Rl ℚ :=
  matP (c.unemb3 hv hR) c.mB

theorem Valid.addsA (V : c.Valid) (t s : Nat) (cf : Coef) (h : Micro.add t s cf ∈ c.mA) :
    t < c.n ∧ s < c.v + c.R ∧ c.v ≤ t ∧ s ≠ t :=
  adds_of_carrier c c.A.flatten (List.all_eq_true.mp V.hA) t s cf h

theorem Valid.addsB (V : c.Valid) (t s : Nat) (cf : Coef) (h : Micro.add t s cf ∈ c.mB) :
    t < c.n ∧ s < c.v + c.R ∧ c.v ≤ t ∧ s ≠ t :=
  adds_of_carrier c c.B.flatten (List.all_eq_true.mp V.hB) t s cf h

/-- a role number `≥ v` is not an x role -/
theorem Valid.un_ne_x (V : c.Valid) (t' : Nat) (h1 : t' < c.n) (h2 : c.v ≤ t') (t : Fin c.v) :
    c.unemb3 V.hv V.hR t' ≠ Sum.inl (Sum.inl t) := by
  intro heq
  have h := c.emb3_unemb3 V.hv V.hR t' h1
  rw [heq] at h
  have e : t.val = t' := h
  have := t.isLt
  omega

/-- a role number `< v + R` is not a y role -/
theorem Valid.un_ne_y (V : c.Valid) (s : Nat) (h1 : s < c.v + c.R) (t : Fin c.v) :
    c.unemb3 V.hv V.hR s ≠ Sum.inl (Sum.inr t) := by
  intro heq
  have h := c.emb3_unemb3 V.hv V.hR s (by unfold n; omega)
  rw [heq] at h
  have e : c.v + c.R + t.val = s := h
  omega

theorem scatM_rowX (K : Matrix (Fin c.v) (Fin c.R) ℚ) (t : Fin c.v) (j : c.Rl) :
    scatM K (Sum.inl (Sum.inl t)) j = if (Sum.inl (Sum.inl t) : c.Rl) = j then 1 else 0 := by
  unfold scatM
  rw [Matrix.add_apply, Matrix.one_apply, embYS_rowX, add_zero]

theorem scatM_colY (K : Matrix (Fin c.v) (Fin c.R) ℚ) (i : c.Rl) (t : Fin c.v) :
    scatM K i (Sum.inl (Sum.inr t)) = if i = (Sum.inl (Sum.inr t) : c.Rl) then 1 else 0 := by
  unfold scatM
  rw [Matrix.add_apply, Matrix.one_apply, embYS_colY, add_zero]

/-- **none into x** -/
theorem Valid.hx (V : c.Valid) (t : Fin c.v) (j : c.Rl) :
    (c.MB V.hv V.hR * scatM (c.Jrm * c.Ccm V.hR) * c.MA V.hv V.hR) (Sum.inl (Sum.inl t)) j
      = if (Sum.inl (Sum.inl t) : c.Rl) = j then 1 else 0 := by
  have hA := matP_row (c.unemb3 V.hv V.hR) (Sum.inl (Sum.inl t)) c.mA (fun t' s cf hm => by
    obtain ⟨h1, _, h3, _⟩ := V.addsA t' s cf hm
    exact V.un_ne_x t' h1 h3 t)
  have hB := matP_row (c.unemb3 V.hv V.hR) (Sum.inl (Sum.inl t)) c.mB (fun t' s cf hm => by
    obtain ⟨h1, _, h3, _⟩ := V.addsB t' s cf hm
    exact V.un_ne_x t' h1 h3 t)
  exact unitRow_mul _ _ _ (unitRow_mul _ _ _ hB (scatM_rowX _ t)) hA j

/-- **none reading y** -/
theorem Valid.hy (V : c.Valid) (i : c.Rl) (t : Fin c.v) :
    (c.MB V.hv V.hR * scatM (c.Jrm * c.Ccm V.hR) * c.MA V.hv V.hR) i (Sum.inl (Sum.inr t))
      = if i = (Sum.inl (Sum.inr t) : c.Rl) then 1 else 0 := by
  have hA := matP_col (c.unemb3 V.hv V.hR) (Sum.inl (Sum.inr t)) c.mA (fun t' s cf hm => by
    obtain ⟨_, h2, _, _⟩ := V.addsA t' s cf hm
    exact V.un_ne_y s h2 t)
  have hB := matP_col (c.unemb3 V.hv V.hR) (Sum.inl (Sum.inr t)) c.mB (fun t' s cf hm => by
    obtain ⟨_, h2, _, _⟩ := V.addsB t' s cf hm
    exact V.un_ne_y s h2 t)
  exact unitCol_mul _ _ _ (unitCol_mul _ _ _ hB (fun i => scatM_colY _ i t)) hA i

/-- the start of the scalar check: the x role `t` holds `x_t`, all other roles nothing -/
theorem cm_start (c : CCert) (a0 : SSt)
    (h0 : ∀ r, a0.N r = 0 ∧ a0.P r = if r < c.v then 1 * 2^(c.sw * r) else 0) (hsw : 1 ≤ c.sw)
    (t : Fin c.v) (j : c.Rl) :
    Cm c.sw c.v (c.v + c.R) c.emb3 a0 j t
      = if j = (Sum.inl (Sum.inl t) : c.Rl) then 1 else 0 := by
  have h1lt : 1 < 2^c.sw := Nat.one_lt_two_pow (by omega)
  rcases j with (t' | S') | q
  · have hlt : t'.val < c.v + c.R := by have := t'.isLt; omega
    show cont c.sw (c.v + c.R) a0 t'.val t.val = _
    unfold cont
    rw [(h0 t'.val).1, (h0 t'.val).2, if_pos t'.isLt, dg_mul_pow c.sw 1 h1lt t'.val t.val,
      dg_zero_left, scl_lt _ _ hlt]
    by_cases e : t' = t
    · subst e
      rw [if_pos rfl, if_pos rfl]
      norm_num
    · have e1 : ¬ t.val = t'.val := fun h => e (Fin.ext h.symm)
      have e2 : ¬ (Sum.inl (Sum.inl t') : c.Rl) = Sum.inl (Sum.inl t) :=
        fun h => e (Sum.inl.inj (Sum.inl.inj h))
      rw [if_neg e1, if_neg e2]
      norm_num
  · have hn : ¬ (c.v + c.R + S'.val < c.v) := by omega
    have e2 : ¬ (Sum.inl (Sum.inr S') : c.Rl) = Sum.inl (Sum.inl t) := by
      intro h; cases h
    show cont c.sw (c.v + c.R) a0 (c.v + c.R + S'.val) t.val = _
    unfold cont
    rw [(h0 (c.v + c.R + S'.val)).1, (h0 (c.v + c.R + S'.val)).2, if_neg hn, dg_zero_left,
      if_neg e2]
    norm_num
  · have hn : ¬ (c.v + q.val < c.v) := by omega
    have e2 : ¬ (Sum.inr q : c.Rl) = Sum.inl (Sum.inl t) := by
      intro h; cases h
    show cont c.sw (c.v + c.R) a0 (c.v + q.val) t.val = _
    unfold cont
    rw [(h0 (c.v + q.val)).1, (h0 (c.v + q.val)).2, if_neg hn, dg_zero_left, if_neg e2]
    norm_num

/-- the end of the scalar check: `y_S` holds exactly `x_S` -/
theorem cm_end (c : CCert) (a3 : SSt)
    (h3 : ∀ S, S < c.v → a3.P (c.v + c.R + S) = a3.N (c.v + c.R + S) + 2 * 2^(c.sw * S))
    (hsm : SmallSt c.sw c.v a3) (hsw3 : 3 ≤ c.sw) (S t : Fin c.v) :
    Cm c.sw c.v (c.v + c.R) c.emb3 a3 (Sum.inl (Sum.inr S)) t = if S = t then 1 else 0 := by
  have hsw : 1 ≤ c.sw := by omega
  have h2lt : 2 < 2^c.sw := by
    have h2 : 2^2 ≤ 2^c.sw := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : (2:Nat)^2 = 4 := rfl
    omega
  have h2s : 2 < 2^(c.sw - 1) := by
    have h2 : 2^2 ≤ 2^(c.sw - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : (2:Nat)^2 = 4 := rfl
    omega
  have hsmall2 : SmallV c.sw c.v (2 * 2^(c.sw * S.val)) := by
    intro T _
    rw [dg_mul_pow c.sw 2 h2lt S.val T]
    by_cases hT : T = S.val
    · rw [if_pos hT]; exact h2s
    · rw [if_neg hT]; exact Nat.two_pow_pos _
  show cont c.sw (c.v + c.R) a3 (c.v + c.R + S.val) t.val = _
  unfold cont
  rw [h3 S.val S.isLt, dg_add_small c.sw c.v _ _ hsw (hsm (c.v + c.R + S.val)).2 hsmall2 t.val
    t.isLt, dg_mul_pow c.sw 2 h2lt S.val t.val, scl_ge _ _ (Nat.le_add_right _ _)]
  by_cases e : S = t
  · have e' : t.val = S.val := by rw [e]
    rw [if_pos e', if_pos e]
    push_cast
    ring
  · have e' : ¬ t.val = S.val := fun h => e (Fin.ext h.symm)
    rw [if_neg e', if_neg e]
    push_cast
    ring

/-- **the scalar identity**: the y roles receive exactly the x roles. -/
theorem Valid.hid (V : c.Valid) (hs : c.scalarCheck = true) (S t : Fin c.v) :
    (c.MB V.hv V.hR * scatM (c.Jrm * c.Ccm V.hR) * c.MA V.hv V.hR)
      (Sum.inl (Sum.inr S)) (Sum.inl (Sum.inl t)) = if S = t then 1 else 0 := by
  obtain ⟨a0, a1, a2, a3, hrA, hrS, hrB, h0, h3, hsm3, hsw3⟩ := V.scalar_states hs
  have hun := c.unemb3_emb3 V.hv V.hR
  have hCA : Cm c.sw c.v (c.v + c.R) c.emb3 a1
      = c.MA V.hv V.hR * Cm c.sw c.v (c.v + c.R) c.emb3 a0 :=
    SRun_Cm c.sw c.v (c.v + c.R) c.emb3 (c.unemb3 V.hv V.hR) hun c.mA (fun t' s cf hm => by
      obtain ⟨h1, h2, _, _⟩ := V.addsA t' s cf hm
      exact ⟨c.emb3_unemb3 V.hv V.hR t' h1, c.emb3_unemb3 V.hv V.hR s (by unfold n; omega)⟩)
      a0 a1 hrA
  have hCB : Cm c.sw c.v (c.v + c.R) c.emb3 a3
      = c.MB V.hv V.hR * Cm c.sw c.v (c.v + c.R) c.emb3 a2 :=
    SRun_Cm c.sw c.v (c.v + c.R) c.emb3 (c.unemb3 V.hv V.hR) hun c.mB (fun t' s cf hm => by
      obtain ⟨h1, h2, _, _⟩ := V.addsB t' s cf hm
      exact ⟨c.emb3_unemb3 V.hv V.hR t' h1, c.emb3_unemb3 V.hv V.hR s (by unfold n; omega)⟩)
      a2 a3 hrB
  have hCS := V.cm_scat a1 a2 hrS
  have hC0 := cm_start c a0 h0 (by omega) t
  have hend := cm_end c a3 h3 hsm3 hsw3 S t
  have e1 := mul_unitCol (c.MB V.hv V.hR * scatM (c.Jrm * c.Ccm V.hR) * c.MA V.hv V.hR)
    (Cm c.sw c.v (c.v + c.R) c.emb3 a0) (Sum.inl (Sum.inl t)) t hC0 (Sum.inl (Sum.inr S))
  rw [← e1, Matrix.mul_assoc, Matrix.mul_assoc, ← hCA, ← hCS, ← hCB]
  exact hend

end CCert

end SSC
