import Submission.Work.MixedCost.TopDesc

/-!
# Mixed engine, top body part 2: one rest call

(agent e-r3cost, round wht45/lever, 19 Oct 2026.)  A vector whose low `s` bits the tree has done is cut
into `2^s` vectors of its high `n - s` bits (`can_hiVec`, linear work), handed to ONE top call
`Do(n - s, 2^s)`, and the answers are kept (`rest_call`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset GF MXR
noncomputable section

universe U

/-- Empty tapes of jobs are all equal. -/
lemma jobsTape_zero (n n' : ℕ) (f : ℕ → Bits n → ℂ) (g : ℕ → Bits n' → ℂ) :
    jobsTape n 0 f = jobsTape n' 0 g := by
  unfold jobsTape Layout.tape
  congr 1
  funext j
  exact j.elim0

section Rest
variable {Ξ : Type U} {m : Bool} {cl : Paint} {s : Ty} {x : Ξ → T s} {Bd : Ξ → ℕ}

/-- **Cutting an answered vector into its high-part vectors**: linear work. -/
lemma can_hiVec {n sz : Ξ → ℕ} (hs : ∀ e, sz e ≤ n e) {wv : ∀ e, Bits (n e) → ℂ}
    (hw : Has m Bd s (a (c cl)) x (fun e => (bits (n e)).tape (wv e)))
    (hp1 : Knows m Bd s x (fun e => 2^(sz e))) (hp2 : Knows m Bd s x (fun e => 2^(n e - sz e)))
    (hbig : Small Bd (fun e => 2^(n e))) :
    Can m Bd s (jobsT cl) x
      (fun e => jobsTape (n e - sz e) (2^(sz e)) (hiVec (n e) (sz e) (wv e))) (fun e => 2^(n e)) := by
  have hle1 : ∀ e, 2^(sz e) ≤ 2^(n e) := fun e => Nat.pow_le_pow_right (by omega) (hs e)
  have hle2 : ∀ e, 2^(n e - sz e) ≤ 2^(n e) := fun e => Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _)
  have hs1 : Small Bd (fun e => 2^(sz e)) := hbig.mono hle1
  have hs2 : Small Bd (fun e => 2^(n e - sz e)) := hbig.mono hle2
  let Du := UnitF (fun e => 2^(sz e))
  let Dv := Σ u : Du, Bits (n u.1 - sz u.1)
  let yv (d : Dv) : T (p (p s w) w) := ((x d.1.1, d.1.2.val), (bits (n d.1.1 - sz d.1.1)).loc d.2)
  let Bv (d : Dv) := Bd d.1.1
  have hcls : ∀ {t : Ty} {y : Ξ → T t}, Has m Bd s t x y → Has m Bv (p (p s w) w) t yv (fun d => y d.1.1) :=
    fun g => (Can.first.then_do Can.first).then_do (g.reindex (fun d : Dv => d.1.1))
  have hq : Knows m Bv (p (p s w) w) yv (fun d => d.1.2.val) := Can.first.then_do Can.second
  have hyl : Knows m Bv (p (p s w) w) yv (fun d => (bits (n d.1.1 - sz d.1.1)).loc d.2) := Can.second
  have hqs : Small Bv (fun d => d.1.2.val) := (hs1.reindex (fun d : Dv => d.1.1)).mono (fun d => d.1.2.2.le)
  have hys : Small Bv (fun d => (bits (n d.1.1 - sz d.1.1)).loc d.2) :=
    (hs2.reindex (fun d : Dv => d.1.1)).mono (fun d => ((bits _).bd _).le)
  have hp1s : Small Bv (fun d => 2^(sz d.1.1)) := hs1.reindex (fun d : Dv => d.1.1)
  have haddr : Knows m Bv (p (p s w) w) yv
      (fun d => (bits (n d.1.1)).loc (castB (Nat.add_sub_cancel' (hs d.1.1))
        (catB (sz d.1.1) (n d.1.1 - sz d.1.1) (bitsOf (sz d.1.1) d.1.2.val, d.2)))) := by
    refine (hq.plus ((hcls hp1).times hyl hp1s hys) hqs (hp1s.mul hys)).cong (fun _ => rfl) (fun d => ?_)
    rw [loc_castB_catB _ _ (hs d.1.1), bitsOf_loc, Nat.mod_eq_of_lt d.1.2.2]
  have hv := Can.fetch (t := c cl) (L := fun d : Dv => bits (n d.1.1)) (v := fun d => wv d.1.1)
    (i := fun d => castB (Nat.add_sub_cancel' (hs d.1.1))
      (catB (sz d.1.1) (n d.1.1 - sz d.1.1) (bitsOf (sz d.1.1) d.1.2.val, d.2))) (hcls hw) haddr
  have hv' : Has m Bv (p (p s w) w) (c cl) yv
      (fun d => hiVec (n d.1.1) (sz d.1.1) (wv d.1.1) d.1.2.val d.2) := by
    refine hv.cong (fun _ => rfl) (fun d => ?_)
    unfold hiVec; rw [dif_pos (hs d.1.1)]
  have hlen : Knows m (fun u : Du => Bd u.1) (p s w) (fun u => (x u.1, u.2.val))
      (fun u => (bits (n u.1 - sz u.1)).n) :=
    Can.first.then_do (hp2.reindex (fun u : Du => u.1))
  have HI := Can.layout (t := c cl) (L := fun u : Du => bits (n u.1 - sz u.1))
    (v := fun u y => hiVec (n u.1) (sz u.1) (wv u.1) u.2.val y) (P := fun _ => 0) (W := fun _ => 0) hlen
    (hv'.mono (fun _ => Nat.zero_le _)) (hs2.reindex _)
  have HO := Can.layout (t := a (c cl)) (L := fun e => Layout.std (2^(sz e)))
    (v := fun e q => (bits (n e - sz e)).tape (hiVec (n e) (sz e) (wv e) q)) (P := fun e => 2^(n e - sz e))
    (W := fun _ => 0) hp1 (HI.mono (fun u => by simp)) hs1
  refine HO.weaken ⟨3, fun e => ?_⟩
  change 0 + 2^(sz e) + 2^(sz e) * 2^(n e - sz e) + 1 ≤ 3 * (2^(n e) + 1)
  have e1 : 2^(sz e) * 2^(n e - sz e) = 2^(n e) := by rw [← pow_add, Nat.add_sub_cancel' (hs e)]
  have := hle1 e
  omega

/-- **One rest call**: cut, ONE top call `Do(n - s, 2^s)`, keep the answers.  Work linear, charge
the call's cost. -/
lemma rest_call {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
    [Fintype σ] [DecidableEq σ] (E : Eng α ρ σ) {b : Bank (portM cl) Ξ} {x : Ξ → T s}
    {n sz : Ξ → ℕ} (hs : ∀ e, sz e ≤ n e) {wv : ∀ e, Bits (n e) → ℂ}
    (hw : Has m b.B s (a (c cl)) x (fun e => (bits (n e)).tape (wv e)))
    (hn : Knows m b.B s x n) (hsz : Knows m b.B s x sz)
    (hp1 : Knows m b.B s x (fun e => 2^(sz e))) (hp2 : Knows m b.B s x (fun e => 2^(n e - sz e)))
    (hI : Has m b.B s sc x (fun _ => Complex.I))
    (hemp : Has m b.B s (jobsT cl) x (fun e => jobsTape 0 0 (fun _ _ => 0)))
    (hbig : Small b.B (fun e => 2^(n e)))
    {Z : Ξ → ℕ}
    (hcall : ∀ e, (b.use e (E.enc cl (MDesc.top (n e - sz e) (2^(sz e)) (hiVec (n e) (sz e) (wv e))))).OK
      (E.out cl (MDesc.top (n e - sz e) (2^(sz e)) (hiVec (n e) (sz e) (wv e)))) (Z e) (b.ext e)) :
    Able m b s (jobsT cl) x
      (fun e => jobsTape (n e - sz e) (2^(sz e)) (fun q => ripple (n e - sz e) (hiVec (n e) (sz e) (wv e) q)))
      (fun e => 2^(n e)) Z := by
  have hns : Small b.B n := hbig.mono (fun e => (Nat.lt_two_pow_self).le)
  have hk : Knows m b.B s x (fun e => n e - sz e) := hn.minus hsz hns
  have hpieces := can_hiVec (cl := cl) hs hw hp1 hp2 hbig
  have hin : Can m b.B s (portIn cl) x
      (fun e => E.enc cl (MDesc.top (n e - sz e) (2^(sz e)) (hiVec (n e) (sz e) (wv e)))) (fun e => 2^(n e)) := by
    refine ((hk.mono (fun _ => Nat.zero_le _)).pair ((hI.mono (fun _ => Nat.zero_le _)).pair
      ((Can.wc 0).pair ((Can.wc 0).pair ((Can.wc 0).pair (hpieces.pair
        (hemp.mono (fun _ => Nat.zero_le _)))))))).cong (fun _ => rfl) (fun e => ?_)
    simp only [Eng.enc, mkIn]
    rw [jobsTape_zero 0 (n e - sz e)]
  have Hcall := (Able.of_can (b := b) hin).comp (Able.use_call (m := m) (b := b) hcall)
  refine (Hcall.fst).weaken (Dom.of_le (fun e => by simp)) (fun e => by simp) |>.cong (fun _ => rfl)
    (fun e => rfl)

end Rest

end
end PowerSaving.RAM
end OAI

#print axioms OAI.PowerSaving.RAM.can_hiVec
#print axioms OAI.PowerSaving.RAM.rest_call
