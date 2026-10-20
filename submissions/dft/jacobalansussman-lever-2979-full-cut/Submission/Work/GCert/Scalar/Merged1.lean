import Submission.Work.GCert.Scalar.Bits
import Submission.Work.CarrierCheck.ScalRun

/-! Merged module written by bos_merge.py for the 500-file limit of the Big O Speedrun
pull-request route.  It is the concatenation, in import order, of the 7 modules below; each one
is copied verbatim after its import header, inside `section` ... `end`, with the scopes it leaves
open closed before that `end`.  Members (module, sha256 of the original file):
* `Submission.Work.GCert.Scalar.Step` e7cfb12f249a1d9f24b738ad18460d919e7b0a30624b1e64cf5b8dcf80de1ca8
* `Submission.Work.GCert.Scalar.Ops` a006f49076212a3ffd509f1722ba6216359e85770f784b1da1417cbda9b08ee7
* `Submission.Work.GCert.Scalar.Scat` 7b4bb12bdd107526b985dde55f54e48f8fdd8f91a13bcc130965c9bcd44b8160
* `Submission.Work.GCert.Scalar.Fin` 5f6900bb493f35ad88a490cb0544d3666cbbf110dbbcb17a3d919cf2ec0b39c7
* `Submission.Work.GCert.Scalar.End` fbbd61abb625651ad54e267e4cdd5228990239ca2b041fb27a68645e255fc35b
* `Submission.Work.GCert.Scalar.Runs` b51ca7a8cd7c7ff3aab3801289d4ce3d3fbc5a119da0d83af9df7c22e3e4e344
* `Submission.Work.GCert.Scalar.Check` 3c1fb90b36972a0d20e0932c3a8352846bb11e5f36aa9ad4096b343fa7c2a23c
-/

-- bos_merge: begin Submission.Work.GCert.Scalar.Step
section

/-!
# (key: gx-scalar) One add of the kernel check is one add on abstract states

* `modK_eq`     the one-descent update of a trie leaf;
* `absG`, `GOk` abstract state of a trie with packed leaves (untagged positive and negative vector
  of every register) and the invariant of the check;
* `gcont`       coefficient of source `T` in the content of a register (`unit` per register);
* `GStep`       one add `t += cf * s` on abstract states;
* `gAdd_sound`  the kernel's add is a `GStep`.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace GS
open SSC GXD

theorem modK_leaf (x key : Nat) (f : Nat → (Nat → Bool) → Bool) (k : Trie → Bool) :
    modK (.leaf x) key f k = if key = 0 then f x (fun y => k (.leaf y)) else false := by
  cases key <;> rfl

theorem modK_node (l r : Trie) (key : Nat) (f : Nat → (Nat → Bool) → Bool) (k : Trie → Bool) :
    modK (.node l r) key f k = if key % 2 = 0 then modK l (key/2) f (fun l' => k (.node l' r))
      else modK r (key/2) f (fun r' => k (.node l r')) := by
  have h1 : Nat.shiftRight key 1 = key / 2 := Nat.shiftRight_one key
  have h2 : Nat.land key 1 = key % 2 := Nat.and_one_is_mod key
  show Bool.rec (motive := fun _ => Bool) (modK r (Nat.shiftRight key 1) f fun r' => k (.node l r'))
    (modK l (Nat.shiftRight key 1) f fun l' => k (.node l' r)) (Nat.beq (Nat.land key 1) 0) = _
  rw [h1, h2]
  rcases Nat.mod_two_eq_zero_or_one key with h | h <;> rw [h] <;> rfl

theorem modK_eq (d : Nat) (t : Trie) (hwf : t.wf d) (key : Nat) (f : Nat → (Nat → Bool) → Bool)
    (k : Trie → Bool) :
    modK t key f k = (decide (key < 2^d) && f (t.get key) (fun x => k (t.set key x))) := by
  induction d generalizing t key k with
  | zero =>
    cases t with
    | leaf v =>
      rw [modK_leaf]
      by_cases h : key = 0
      · subst h; simp [Trie.get, Trie.set_leaf]
      · have h' : ¬ key < 2^0 := by simpa using h
        simp [h, h']
    | node l r => exact False.elim hwf
  | succ d ih =>
    cases t with
    | leaf v => exact False.elim hwf
    | node l r =>
      obtain ⟨hl, hr⟩ := hwf
      rw [modK_node]
      have hlt : (key / 2 < 2^d) ↔ (key < 2^(d+1)) := by rw [pow_succ]; omega
      by_cases h : key % 2 = 0
      · have e : (fun x => k ((Trie.node l r).set key x)) = fun x => k (.node (l.set (key/2) x) r) := by
          funext x; rw [Trie.set_node, if_pos h]
        rw [if_pos h, ih l hl, e]; simp [Trie.get, h, hlt]
      · have e : (fun x => k ((Trie.node l r).set key x)) = fun x => k (.node l (r.set (key/2) x)) := by
          funext x; rw [Trie.set_node, if_neg h]
        rw [if_neg h, ih r hr, e]; simp [Trie.get, h, hlt]

/-- abstract state: untagged positive / negative packed vector of every register -/
def absG (d K : Nat) (tr : Trie) : SSt :=
  ⟨fun r => (absS (2^d) tr r % 2^K) >>> 64, fun r => (absS (2^d) tr r >>> K) >>> 64⟩

/-- invariant of the check: both halves of every leaf are tagged vectors with small digits -/
structure GOk (d sw n : Nat) (tr : Trie) : Prop where
  wf : tr.wf d
  ok : ∀ r, OkW sw n (absS (2^d) tr r % 2^(64 + sw * n)) ∧ OkW sw n (absS (2^d) tr r >>> (64 + sw * n))

theorem GOk.small {d sw n : Nat} {tr : Trie} (h : GOk d sw n tr) :
    SmallSt sw n (absG d (64 + sw * n) tr) := fun r => ⟨(h.ok r).1.1, (h.ok r).2.1⟩

/-- coefficient of source `T` in the content of the register `r` (digits over the unit `u r`) -/
def gcont (sw : Nat) (u : Nat → Nat) (a : SSt) (r T : Nat) : ℚ :=
  ((dg sw (a.P r) T : ℚ) - (dg sw (a.N r) T : ℚ)) / (u r : ℚ)

theorem gcont_congr (sw : Nat) (u : Nat → Nat) (a b : SSt) (r T : Nat) (hP : b.P r = a.P r)
    (hN : b.N r = a.N r) : gcont sw u b r T = gcont sw u a r T := by
  unfold gcont
  rw [hP, hN]

/-- one add `t += cf * s` on abstract states -/
def GStep (sw n : Nat) (u : Nat → Nat) (t s : Nat) (cf : Coef) (a b : SSt) : Prop :=
  t ≠ s ∧ (∀ r, r ≠ t → b.P r = a.P r ∧ b.N r = a.N r) ∧
    ∀ T, T < n → gcont sw u b t T = gcont sw u a t T + cf.val * gcont sw u a s T

theorem unitK_pos (ux us uy v v2 r : Nat) (hx : 1 ≤ ux) (hs : 1 ≤ us) (hy : 1 ≤ uy) :
    1 ≤ unitK ux us uy v v2 r := by
  unfold unitK
  cases Nat.ble (Nat.succ r) v <;> cases Nat.ble (Nat.succ r) v2 <;> assumption

/-- **one add of the kernel check is one add on abstract states** -/
theorem gAdd_sound (d sw n tm K ux us uy v v2 : Nat) (hsw : 1 ≤ sw) (htm : tm = maskW sw n)
    (hK : K = 64 + sw * n) (hu : ∀ r, 1 ≤ unitK ux us uy v v2 r)
    (t s : Nat) (co : Co) (ok : Bool) (tr : Trie) (hI : GOk d sw n tr) (k : Trie → Bool)
    (h : gAdd tm K (2^K) ux us uy v v2 t s co ok tr k = true) :
    ∃ tr', GOk d sw n tr' ∧ k tr' = true ∧ ok = true ∧
      GStep sw n (unitK ux us uy v v2) t s (toCoef co) (absG d K tr) (absG d K tr') := by
  subst hK
  obtain ⟨hwf, hok⟩ := hI
  unfold gAdd at h
  obtain ⟨hokb, h1⟩ := guard_true h
  cases hts : Nat.beq t s with
  | true =>
    rw [hts] at h1
    exact absurd h1 Bool.false_ne_true
  | false =>
    rw [hts] at h1
    replace h1 : tr.getK s (fun vs => modK tr t (fun vt kk =>
      gW ux us uy v v2 t s co fun ng a b =>
        gAcc tm (64 + sw * n) (2^(64 + sw * n)) ng a b (vs % 2^(64 + sw * n)) (vs >>> (64 + sw * n))
          (vt % 2^(64 + sw * n)) (vt >>> (64 + sw * n)) kk) k) = true := h1
    have hne : t ≠ s := fun e => by
      rw [e, Nat.beq_refl] at hts
      exact Bool.noConfusion hts
    rw [Trie.getK_eq d tr hwf] at h1
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    obtain ⟨hs2, h2⟩ := h1
    rw [modK_eq d tr hwf] at h2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
    obtain ⟨ht2, h3⟩ := h2
    obtain ⟨a, b, h4, hb, hus, hw⟩ := gW_sound _ _ _ _ _ _ _ _ _ h3
    have es : absS (2^d) tr s = tr.get s := absS_apply d tr s hs2
    have et : absS (2^d) tr t = tr.get t := absS_apply d tr t ht2
    obtain ⟨hps, hns⟩ := hok s
    obtain ⟨hpt, hnt⟩ := hok t
    rw [es] at hps hns
    rw [et] at hpt hnt
    obtain ⟨pt', nt', hpt', hnt', hlt, hk, hd⟩ := gAcc_sound sw n tm (64 + sw * n) hsw htm co.neg a b
      _ _ _ _ hps hns hpt hnt _ h4
    have hset := absS_set d tr hwf t (pt' + nt' <<< (64 + sw * n)) ht2
    refine ⟨tr.set t (pt' + nt' <<< (64 + sw * n)), ⟨Trie.wf_set d tr hwf _ _, ?_⟩, hk, hokb, hne,
      ?_, ?_⟩
    · intro r
      rw [hset]
      by_cases e : r = t
      · rw [e, Function.update_self, dec_lo _ _ _ hlt, dec_hi _ _ _ hlt]
        exact ⟨hpt', hnt'⟩
      · rw [Function.update_of_ne e]
        exact hok r
    · intro r hr
      show (absS (2^d) (tr.set t (pt' + nt' <<< (64 + sw * n))) r % 2^(64 + sw * n)) >>> 64
          = (absS (2^d) tr r % 2^(64 + sw * n)) >>> 64 ∧
        (absS (2^d) (tr.set t (pt' + nt' <<< (64 + sw * n))) r >>> (64 + sw * n)) >>> 64
          = (absS (2^d) tr r >>> (64 + sw * n)) >>> 64
      rw [hset, Function.update_of_ne hr]
      exact ⟨rfl, rfl⟩
    · intro T hT
      obtain ⟨qp, qn, e1, e2, e3⟩ := hd T hT
      have hc := coef_wgt co a b _ _ hb hus (hu t) hw (qp:ℚ) (qn:ℚ)
      show ((dg sw ((absS (2^d) (tr.set t (pt' + nt' <<< (64 + sw * n))) t % 2^(64 + sw * n)) >>> 64) T : ℚ)
            - (dg sw ((absS (2^d) (tr.set t (pt' + nt' <<< (64 + sw * n))) t >>> (64 + sw * n)) >>> 64) T : ℚ))
            / (unitK ux us uy v v2 t : ℚ)
          = ((dg sw ((absS (2^d) tr t % 2^(64 + sw * n)) >>> 64) T : ℚ)
              - (dg sw ((absS (2^d) tr t >>> (64 + sw * n)) >>> 64) T : ℚ)) / (unitK ux us uy v v2 t : ℚ)
            + (toCoef co).val * (((dg sw ((absS (2^d) tr s % 2^(64 + sw * n)) >>> 64) T : ℚ)
              - (dg sw ((absS (2^d) tr s >>> (64 + sw * n)) >>> 64) T : ℚ)) / (unitK ux us uy v v2 s : ℚ))
      rw [hset, Function.update_self, dec_lo _ _ _ hlt, dec_hi _ _ _ hlt, et, es, e1, e2, e3]
      push_cast
      rw [hc]
      ring

#print axioms modK_eq
#print axioms gAdd_sound

end GS

end
-- bos_merge: end Submission.Work.GCert.Scalar.Step

-- bos_merge: begin Submission.Work.GCert.Scalar.Ops
section

/-!
# (key: gx-scalar) The kernel check on gates, chunks and scatter rows runs the list of adds

* `GRun`    a list of single adds `(tgt, src, co)` on abstract states (only the selected sources;
  for these the kind test holds);
* `gGates_sound`, `gChunks_sound`   the check on gates runs `GRun` on `flatMap Gate.adds`;

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace GS
open SSC GXD

/-- a list of adds `(t, s, co)` on abstract states: the adds with `sel s` are done (and pass the
kind test `okf t s`), the others are skipped -/
def GRun (sw n : Nat) (u : Nat → Nat) (okf : Nat → Nat → Bool) (sel : Nat → Bool) :
    SSt → List (Nat × Nat × Co) → SSt → Prop
  | a, [], b => b = a
  | a, x :: l, b => if sel x.2.1 = true then
      (okf x.1 x.2.1 = true ∧ ∃ m, GStep sw n u x.1 x.2.1 (toCoef x.2.2) a m ∧
        GRun sw n u okf sel m l b)
    else GRun sw n u okf sel a l b

section
variable (sw n : Nat) (u : Nat → Nat) (okf : Nat → Nat → Bool) (sel : Nat → Bool)

theorem GRun_append (l1 l2 : List (Nat × Nat × Co)) : ∀ (a m b : SSt),
    GRun sw n u okf sel a l1 m → GRun sw n u okf sel m l2 b →
    GRun sw n u okf sel a (l1 ++ l2) b := by
  induction l1 with
  | nil =>
    intro a m b h1 h2
    have e : m = a := h1
    rw [e] at h2
    exact h2
  | cons x l1 ih =>
    intro a m b h1 h2
    show if sel x.2.1 = true then _ else _
    have h1' : if sel x.2.1 = true then (okf x.1 x.2.1 = true ∧ ∃ m', GStep sw n u x.1 x.2.1
        (toCoef x.2.2) a m' ∧ GRun sw n u okf sel m' l1 m) else GRun sw n u okf sel a l1 m := h1
    by_cases hs : sel x.2.1 = true
    · rw [if_pos hs] at h1' ⊢
      obtain ⟨ho, m1, hst, hr⟩ := h1'
      exact ⟨ho, m1, hst, ih m1 m b hr h2⟩
    · rw [if_neg hs] at h1' ⊢
      exact ih a m b h1' h2

theorem GRun_split (l1 l2 : List (Nat × Nat × Co)) : ∀ (a b : SSt),
    GRun sw n u okf sel a (l1 ++ l2) b →
    ∃ m, GRun sw n u okf sel a l1 m ∧ GRun sw n u okf sel m l2 b := by
  induction l1 with
  | nil =>
    intro a b h
    exact ⟨a, rfl, h⟩
  | cons x l1 ih =>
    intro a b h
    have h' : if sel x.2.1 = true then (okf x.1 x.2.1 = true ∧ ∃ m', GStep sw n u x.1 x.2.1
        (toCoef x.2.2) a m' ∧ GRun sw n u okf sel m' (l1 ++ l2) b)
        else GRun sw n u okf sel a (l1 ++ l2) b := h
    by_cases hs : sel x.2.1 = true
    · rw [if_pos hs] at h'
      obtain ⟨ho, m1, hst, hr⟩ := h'
      obtain ⟨m, r1, r2⟩ := ih m1 b hr
      refine ⟨m, ?_, r2⟩
      show if sel x.2.1 = true then _ else _
      rw [if_pos hs]
      exact ⟨ho, m1, hst, r1⟩
    · rw [if_neg hs] at h'
      obtain ⟨m, r1, r2⟩ := ih a b h'
      refine ⟨m, ?_, r2⟩
      show if sel x.2.1 = true then _ else _
      rw [if_neg hs]
      exact r1

theorem GRun_skip (l : List (Nat × Nat × Co)) (h : ∀ x ∈ l, sel x.2.1 = false) (a : SSt) :
    GRun sw n u okf sel a l a := by
  induction l with
  | nil => exact rfl
  | cons x l ih =>
    show if sel x.2.1 = true then _ else _
    have hs : ¬ sel x.2.1 = true := by rw [h x (List.mem_cons_self ..)]; exact Bool.false_ne_true
    rw [if_neg hs]
    exact ih (fun y hy => h y (List.mem_cons_of_mem _ hy))

end

section
variable (d sw n tm K ux us uy v v2 : Nat) (okf : Nat → Nat → Bool) (sel : Nat → Bool)
  (hsw : 1 ≤ sw) (htm : tm = maskW sw n) (hK : K = 64 + sw * n)
  (hu : ∀ r, 1 ≤ unitK ux us uy v v2 r)
include hsw htm hK hu

local notation "RUN" => GRun sw n (unitK ux us uy v v2) okf

theorem gOut_sound (s : Nat) (hs : sel s = true) (tgts : List (Nat × Co)) :
    ∀ (tr : Trie) (k : Trie → Bool), GOk d sw n tr →
      gOut tm K (2^K) ux us uy v v2 okf s tgts tr k = true →
      ∃ tr', GOk d sw n tr' ∧ k tr' = true ∧
        RUN sel (absG d K tr) (tgts.map fun p => (p.1, s, p.2)) (absG d K tr') := by
  induction tgts with
  | nil => intro tr k hI h; exact ⟨tr, hI, h, rfl⟩
  | cons x l ih =>
    intro tr k hI h
    have h' : gAdd tm K (2^K) ux us uy v v2 x.1 s x.2 (okf x.1 s) tr
        (fun tr' => gOut tm K (2^K) ux us uy v v2 okf s l tr' k) = true := h
    obtain ⟨tr1, hI1, hk1, ho, hst⟩ := gAdd_sound d sw n tm K ux us uy v v2 hsw htm hK hu _ _ _ _ tr
      hI _ h'
    obtain ⟨tr2, hI2, hk2, hr⟩ := ih tr1 k hI1 hk1
    refine ⟨tr2, hI2, hk2, ?_⟩
    show if sel s = true then _ else _
    rw [if_pos hs]
    exact ⟨ho, _, hst, hr⟩

theorem gInn_sound (t : Nat) (srcs : List (Nat × Co)) :
    ∀ (tr : Trie) (k : Trie → Bool), GOk d sw n tr →
      gInn tm K (2^K) ux us uy v v2 okf sel t srcs tr k = true →
      ∃ tr', GOk d sw n tr' ∧ k tr' = true ∧
        RUN sel (absG d K tr) (srcs.map fun p => (t, p.1, p.2)) (absG d K tr') := by
  induction srcs with
  | nil => intro tr k hI h; exact ⟨tr, hI, h, rfl⟩
  | cons x l ih =>
    intro tr k hI h
    have h' : Bool.rec (motive := fun _ => Bool) (gInn tm K (2^K) ux us uy v v2 okf sel t l tr k)
        (gAdd tm K (2^K) ux us uy v v2 t x.1 x.2 (okf t x.1) tr
          (fun tr' => gInn tm K (2^K) ux us uy v v2 okf sel t l tr' k)) (sel x.1) = true := h
    cases hsx : sel x.1 with
    | false =>
      rw [hsx] at h'
      obtain ⟨tr2, hI2, hk2, hr⟩ := ih tr k hI h'
      refine ⟨tr2, hI2, hk2, ?_⟩
      show if sel x.1 = true then _ else _
      rw [hsx, if_neg Bool.false_ne_true]
      exact hr
    | true =>
      rw [hsx] at h'
      obtain ⟨tr1, hI1, hk1, ho, hst⟩ := gAdd_sound d sw n tm K ux us uy v v2 hsw htm hK hu _ _ _ _
        tr hI _ h'
      obtain ⟨tr2, hI2, hk2, hr⟩ := ih tr1 k hI1 hk1
      refine ⟨tr2, hI2, hk2, ?_⟩
      show if sel x.1 = true then _ else _
      rw [if_pos hsx]
      exact ⟨ho, _, hst, hr⟩

theorem gGate_sound (g : Gate) (tr : Trie) (k : Trie → Bool) (hI : GOk d sw n tr)
    (h : gGate tm K (2^K) ux us uy v v2 okf sel g tr k = true) :
    ∃ tr', GOk d sw n tr' ∧ k tr' = true ∧ RUN sel (absG d K tr) g.adds (absG d K tr') := by
  cases g with
  | out f s tgts ex =>
    have h' : Bool.rec (motive := fun _ => Bool) (k tr)
        (gOut tm K (2^K) ux us uy v v2 okf s tgts tr k) (sel s) = true := h
    cases hs : sel s with
    | false =>
      rw [hs] at h'
      refine ⟨tr, hI, h', GRun_skip sw n _ okf sel _ (fun x hx => ?_) _⟩
      obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx
      exact hs
    | true =>
      rw [hs] at h'
      exact gOut_sound d sw n tm K ux us uy v v2 okf sel hsw htm hK hu s hs tgts tr k hI h'
  | inn f t srcs =>
    exact gInn_sound d sw n tm K ux us uy v v2 okf sel hsw htm hK hu t srcs tr k hI h

theorem gGates_sound (gs : List Gate) : ∀ (tr : Trie) (k : Trie → Bool), GOk d sw n tr →
    gGates tm K (2^K) ux us uy v v2 okf sel gs tr k = true →
    ∃ tr', GOk d sw n tr' ∧ k tr' = true ∧
      RUN sel (absG d K tr) (gs.flatMap Gate.adds) (absG d K tr') := by
  induction gs with
  | nil => intro tr k hI h; exact ⟨tr, hI, h, rfl⟩
  | cons g gs ih =>
    intro tr k hI h
    have h' : gGate tm K (2^K) ux us uy v v2 okf sel g tr
        (fun tr' => gGates tm K (2^K) ux us uy v v2 okf sel gs tr' k) = true := h
    obtain ⟨tr1, hI1, hk1, r1⟩ := gGate_sound d sw n tm K ux us uy v v2 okf sel hsw htm hK hu g tr _
      hI h'
    obtain ⟨tr2, hI2, hk2, r2⟩ := ih tr1 k hI1 hk1
    refine ⟨tr2, hI2, hk2, ?_⟩
    rw [List.flatMap_cons]
    exact GRun_append sw n _ okf sel _ _ _ _ _ r1 r2

theorem gChunks_sound (cs : List (List Gate)) : ∀ (tr : Trie) (k : Trie → Bool), GOk d sw n tr →
    gChunks tm K (2^K) ux us uy v v2 okf sel cs tr k = true →
    ∃ tr', GOk d sw n tr' ∧ k tr' = true ∧
      RUN sel (absG d K tr) (cs.flatten.flatMap Gate.adds) (absG d K tr') := by
  induction cs with
  | nil => intro tr k hI h; exact ⟨tr, hI, h, rfl⟩
  | cons gs cs ih =>
    intro tr k hI h
    have h' : gGates tm K (2^K) ux us uy v v2 okf sel gs tr
        (fun tr' => gChunks tm K (2^K) ux us uy v v2 okf sel cs tr' k) = true := h
    obtain ⟨tr1, hI1, hk1, r1⟩ := gGates_sound d sw n tm K ux us uy v v2 okf sel hsw htm hK hu gs tr _
      hI h'
    obtain ⟨tr2, hI2, hk2, r2⟩ := ih tr1 k hI1 hk1
    refine ⟨tr2, hI2, hk2, ?_⟩
    rw [List.flatten_cons, List.flatMap_append]
    exact GRun_append sw n _ okf sel _ _ _ _ _ r1 r2

end

#print axioms gChunks_sound

end GS

end
-- bos_merge: end Submission.Work.GCert.Scalar.Ops

-- bos_merge: begin Submission.Work.GCert.Scalar.Scat
section

/-!
# (key: gx-scalar) The kernel check on the scatter rows runs the list of scatter adds

`gScat_sound`: the check on the scatter rows runs `GRun` on `scatAddsFrom`, there are `v` rows
(the last target is `2 v - 1`), every total index is below `rl`.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace GS
open SSC GXD

/-- the adds of one scatter row: `t += co * (register of total k)` -/
def scatRowAdds (ret : List (Nat × Nat)) (t : Nat) (l : List (Nat × Co)) : List (Nat × Nat × Co) :=
  l.map fun x => (t, (ret.getD x.1 (0, 0)).1, x.2)

/-- the adds of the scatter rows of the targets `t, t+1, ..` -/
def scatAddsFrom (ret : List (Nat × Nat)) : Nat → List (List (Nat × Co)) → List (Nat × Nat × Co)
  | _, [] => []
  | t, l :: rows => scatRowAdds ret t l ++ scatAddsFrom ret (t+1) rows

section
variable (d sw n tm K ux us uy v v2 : Nat) (okf : Nat → Nat → Bool)
  (hsw : 1 ≤ sw) (htm : tm = maskW sw n) (hK : K = 64 + sw * n)
  (hu : ∀ r, 1 ≤ unitK ux us uy v v2 r)
include hsw htm hK hu

local notation "RUN" => GRun sw n (unitK ux us uy v v2) okf

theorem gScatRow_sound (ret : List (Nat × Nat)) (rl t : Nat) (l : List (Nat × Co)) :
    ∀ (tr : Trie) (k : Trie → Bool), GOk d sw n tr →
      gScatRow tm K (2^K) ux us uy v v2 okf ret rl t l tr k = true →
      ∃ tr', GOk d sw n tr' ∧ k tr' = true ∧ (∀ x ∈ l, x.1 < rl) ∧
        RUN (fun _ => true) (absG d K tr) (scatRowAdds ret t l) (absG d K tr') := by
  induction l with
  | nil => intro tr k hI h; exact ⟨tr, hI, h, fun x hx => absurd hx List.not_mem_nil, rfl⟩
  | cons x l ih =>
    intro tr k hI h
    have h' : guard (Nat.ble (Nat.succ x.1) rl) (forceN (ret.getD x.1 (0, 0)).1 fun s =>
        gAdd tm K (2^K) ux us uy v v2 t s x.2 (okf t s) tr
          (fun tr' => gScatRow tm K (2^K) ux us uy v v2 okf ret rl t l tr' k)) = true := h
    obtain ⟨hlt, h2⟩ := guard_true h'
    rw [forceN_eq] at h2
    obtain ⟨tr1, hI1, hk1, ho, hst⟩ := gAdd_sound d sw n tm K ux us uy v v2 hsw htm hK hu _ _ _ _ tr
      hI _ h2
    obtain ⟨tr2, hI2, hk2, hb, hr⟩ := ih tr1 k hI1 hk1
    refine ⟨tr2, hI2, hk2, ?_, ?_⟩
    · intro y hy
      rcases List.mem_cons.mp hy with e | e
      · rw [e]; exact ble_true hlt
      · exact hb y e
    · show if (fun _ => true) (ret.getD x.1 (0, 0)).1 = true then _ else _
      rw [if_pos rfl]
      exact ⟨ho, _, hst, hr⟩

theorem gScat_sound (ret : List (Nat × Nat)) (rl : Nat) (rows : List (List (Nat × Co))) :
    ∀ (t : Nat) (tr : Trie) (k : Trie → Bool), GOk d sw n tr →
      gScat tm K (2^K) ux us uy v v2 okf ret rl rows t tr k = true →
      ∃ tr', GOk d sw n tr' ∧ k tr' = true ∧ t + rows.length = v2 ∧
        (∀ l ∈ rows, ∀ x ∈ l, x.1 < rl) ∧
        RUN (fun _ => true) (absG d K tr) (scatAddsFrom ret t rows) (absG d K tr') := by
  induction rows with
  | nil =>
    intro t tr k hI h
    obtain ⟨h1, h2⟩ := guard_true (show guard (Nat.beq t v2) (k tr) = true from h)
    exact ⟨tr, hI, h2, beq_true h1, fun l hl => absurd hl List.not_mem_nil, rfl⟩
  | cons l rows ih =>
    intro t tr k hI h
    have h' : gScatRow tm K (2^K) ux us uy v v2 okf ret rl t l tr (fun tr' =>
        forceN (Nat.succ t) fun t2 => gScat tm K (2^K) ux us uy v v2 okf ret rl rows t2 tr' k)
        = true := h
    obtain ⟨tr1, hI1, hk1, hb1, r1⟩ := gScatRow_sound d sw n tm K ux us uy v v2 okf hsw htm hK hu
      ret rl t l tr _ hI h'
    rw [forceN_eq] at hk1
    obtain ⟨tr2, hI2, hk2, hlen, hb2, r2⟩ := ih (t+1) tr1 k hI1 hk1
    refine ⟨tr2, hI2, hk2, ?_, ?_, GRun_append sw n _ okf _ _ _ _ _ _ r1 r2⟩
    · rw [List.length_cons]; omega
    · intro l' hl'
      rcases List.mem_cons.mp hl' with e | e
      · rw [e]; exact hb1
      · exact hb2 l' e

end

#print axioms gScat_sound

end GS

end
-- bos_merge: end Submission.Work.GCert.Scalar.Scat

-- bos_merge: begin Submission.Work.GCert.Scalar.Fin
section

/-!
# (key: gx-scalar) Parameters, first contents, final test, equality of tries

* `gPre_sound`    what the parameter tests give;
* `gInit_sound`, `init_ok`   the first contents: register `off + T` holds the unit at digit `T`;
* `gFin_sound`    the final test: `P = N + unit at digit S - lo` (or `+ 0`);
* `cont_start`, `cont_end`   the same as contents (`gcont`);
* `beqK_eq`       the kernel's equality test of tries.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace GS
open SSC GXD

theorem retOKK_sound (v2 nr : Nat) : ∀ (l : List (Nat × Nat)), retOKK v2 nr l = true →
    ∀ x ∈ l, v2 ≤ x.1 ∧ x.1 < nr := by
  intro l
  induction l with
  | nil => intro _ x hx; exact absurd hx List.not_mem_nil
  | cons y l ih =>
    intro h x hx
    have h' : guard (Nat.ble v2 y.1) (guard (Nat.ble (Nat.succ y.1) nr) (retOKK v2 nr l)) = true := h
    obtain ⟨h1, h2⟩ := guard_true h'
    obtain ⟨h3, h4⟩ := guard_true h2
    rcases List.mem_cons.mp hx with e | e
    · rw [e]; exact ⟨ble_true h1, ble_true h3⟩
    · exact ih h4 x e

theorem gPre_sound (c : Raw) (p : SPar) (lo n : Nat) (k : Nat → Nat → Nat → Nat → Nat → Nat → Bool)
    (h : gPre c p lo n k = true) :
    (1 ≤ p.ux ∧ 1 ≤ p.us ∧ 1 ≤ p.uy ∧ 1 ≤ p.sw) ∧ 2 * c.v + c.R ≤ 2^p.d ∧ lo + n ≤ c.v ∧
      (p.ux < 2^(p.sw - 1) ∧ p.uy < 2^(p.sw - 1) ∧ p.ux < 2^31 ∧ p.uy < 2^31) ∧
      (∀ x ∈ c.ret, 2 * c.v ≤ x.1 ∧ x.1 < 2 * c.v + c.R) ∧
      k (2 * c.v) (2 * c.v + c.R) (lo + n) (maskW p.sw n) (64 + p.sw * n) (2^(64 + p.sw * n))
        = true := by
  unfold gPre at h
  rw [forceN_eq, forceN_eq, forceN_eq, forceN_eq, forceN_eq] at h
  obtain ⟨h1, h⟩ := guard_true h
  obtain ⟨h2, h⟩ := guard_true h
  obtain ⟨h3, h⟩ := guard_true h
  obtain ⟨h4, h⟩ := guard_true h
  obtain ⟨h5, h⟩ := guard_true h
  obtain ⟨h6, h⟩ := guard_true h
  obtain ⟨h7, h⟩ := guard_true h
  obtain ⟨h8, h⟩ := guard_true h
  obtain ⟨h9, h⟩ := guard_true h
  obtain ⟨h10, h⟩ := guard_true h
  obtain ⟨h11, h⟩ := guard_true h
  rw [forceN_eq, forceN_eq] at h
  exact ⟨⟨ble_true h1, ble_true h2, ble_true h3, ble_true h4⟩, ble_true h5, ble_true h6,
    ⟨ble_true h7, ble_true h8, ble_true h9, ble_true h10⟩, retOKK_sound _ _ _ h11, h⟩

/-- the tag weight of the digit `T` -/
def tau (T : Nat) : Nat := (2654435761 * (T + 1)) % 4294967296

theorem tau_lt (T : Nat) : tau T < 2^32 := Nat.mod_lt _ (by norm_num)

/-- the first leaf of a source register -/
def leaf0 (sw u T : Nat) : Nat := u <<< (64 + sw * T) + u * tau T

theorem leaf0_facts (sw n u T : Nat) (hu : u < 2^(sw - 1)) (hsw : 1 ≤ sw) (hu2 : u < 2^31)
    (hT : T < n) :
    leaf0 sw u T < 2^(64 + sw * n) ∧ leaf0 sw u T >>> 64 = u * 2^(sw * T) ∧
      leaf0 sw u T % 2^64 < 2^63 := by
  have hc : tau T < 2^32 := tau_lt T
  unfold leaf0
  generalize tau T = c at hc ⊢
  have huc : u * c < 2^63 := by
    have : u * c < 2^31 * 2^32 := Nat.mul_lt_mul'' hu2 hc
    have e : (2:Nat)^31 * 2^32 = 2^63 := by norm_num
    omega
  have e0 : u <<< (64 + sw * T) + u * c = u * c + (u * 2^(sw * T)) * 2^64 := by
    rw [Nat.shiftLeft_eq, Nat.pow_add, Nat.mul_comm (2^64), ← Nat.mul_assoc, Nat.add_comm]
  have hA : u * 2^(sw * T) < 2^(sw * n) := by
    have h1 : u < 2^sw := lt_of_lt_of_le hu (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h2 : u * 2^(sw * T) < 2^sw * 2^(sw * T) := Nat.mul_lt_mul_of_pos_right h1 (Nat.two_pow_pos _)
    have h3 : 2^sw * 2^(sw * T) = 2^(sw * (T + 1)) := by
      rw [← Nat.pow_add, Nat.mul_succ, Nat.add_comm]
    have h4 : 2^(sw * (T + 1)) ≤ 2^(sw * n) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (by omega))
    omega
  have h64 : (2:Nat)^63 < 2^64 := by norm_num
  refine ⟨?_, ?_, ?_⟩
  · rw [e0, Nat.pow_add, Nat.mul_comm (2^64)]
    have : (u * 2^(sw * T) + 1) * 2^64 ≤ 2^(sw * n) * 2^64 := Nat.mul_le_mul_right _ hA
    have e : (u * 2^(sw * T) + 1) * 2^64 = u * 2^(sw * T) * 2^64 + 2^64 := by ring
    omega
  · rw [e0, Nat.shiftRight_eq_div_pow, Nat.add_mul_div_right _ _ (Nat.two_pow_pos 64),
      Nat.div_eq_of_lt (by omega), Nat.zero_add]
  · rw [e0, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    exact huc

theorem gInit_succ (sw u off n i : Nat) (t : Trie) (k : Trie → Bool) :
    gInit sw u off (n+1) i t k = forceN (Nat.add (Nat.shiftLeft u (Nat.add 64 (Nat.mul sw i)))
        (Nat.mul u (Nat.mod (Nat.mul 2654435761 (Nat.succ i)) 4294967296))) fun b =>
      forceN (Nat.succ i) fun i2 => gInit sw u off n i2 (t.set (Nat.add off i) b) k := rfl

theorem gInit_sound (d sw u off : Nat) : ∀ (n i : Nat) (t : Trie) (k : Trie → Bool), t.wf d →
    off + i + n ≤ 2^d → gInit sw u off n i t k = true →
    ∃ t', t'.wf d ∧ k t' = true ∧ ∀ r, absS (2^d) t' r
      = if off + i ≤ r ∧ r < off + i + n then leaf0 sw u (r - off) else absS (2^d) t r := by
  intro n
  induction n with
  | zero =>
    intro i t k hwf _ h
    refine ⟨t, hwf, h, fun r => ?_⟩
    have hn : ¬ (off + i ≤ r ∧ r < off + i + 0) := by omega
    rw [if_neg hn]
  | succ n ih =>
    intro i t k hwf hle h
    rw [gInit_succ, forceN_eq, forceN_eq] at h
    have hi : off + i < 2^d := by omega
    obtain ⟨t', hwf', hk, hval⟩ := ih (i+1) _ k (Trie.wf_set d t hwf _ _) (by omega) h
    refine ⟨t', hwf', hk, fun r => ?_⟩
    rw [hval r]
    have hs := absS_set d t hwf (off + i) (leaf0 sw u i) hi
    have hs' : absS (2^d) (t.set (Nat.add off i) (Nat.add (Nat.shiftLeft u (Nat.add 64 (Nat.mul sw i)))
        (Nat.mul u (Nat.mod (Nat.mul 2654435761 (Nat.succ i)) 4294967296))))
        = Function.update (absS (2^d) t) (off + i) (leaf0 sw u i) := hs
    rw [hs']
    by_cases e : r = off + i
    · have h1 : ¬ (off + (i + 1) ≤ r ∧ r < off + (i + 1) + n) := by omega
      have h2 : off + i ≤ r ∧ r < off + i + (n + 1) := by omega
      have e3 : r - off = i := by omega
      rw [if_neg h1, if_pos h2, e, Function.update_self, ← e, e3]
    · rw [Function.update_of_ne e]
      by_cases hA : off + (i + 1) ≤ r ∧ r < off + (i + 1) + n
      · have h2 : off + i ≤ r ∧ r < off + i + (n + 1) := by omega
        rw [if_pos hA, if_pos h2]
      · have h2 : ¬ (off + i ≤ r ∧ r < off + i + (n + 1)) := by omega
        rw [if_neg hA, if_neg h2]

/-- the state after `gInit` on the empty trie: invariant and abstract contents -/
theorem init_ok (d sw n u off : Nat) (hsw : 1 ≤ sw) (hu : u < 2^(sw - 1)) (hu2 : u < 2^31)
    (t' : Trie) (hwf : t'.wf d)
    (hval : ∀ r, absS (2^d) t' r = if off + 0 ≤ r ∧ r < off + 0 + n then leaf0 sw u (r - off)
      else absS (2^d) (Trie.mk d) r) :
    GOk d sw n t' ∧ ∀ r, (absG d (64 + sw * n) t').N r = 0 ∧ (absG d (64 + sw * n) t').P r
      = if off ≤ r ∧ r < off + n then u * 2^(sw * (r - off)) else 0 := by
  have hus : u < 2^sw := lt_of_lt_of_le hu (Nat.pow_le_pow_right (by norm_num) (by omega))
  have key : ∀ r, (absS (2^d) t' r % 2^(64 + sw * n)) >>> 64
        = (if off ≤ r ∧ r < off + n then u * 2^(sw * (r - off)) else 0) ∧
      absS (2^d) t' r >>> (64 + sw * n) = 0 ∧ absS (2^d) t' r % 2^(64 + sw * n) % 2^64 < 2^63 := by
    intro r
    rw [hval r, Nat.add_zero]
    by_cases hr : off ≤ r ∧ r < off + n
    · obtain ⟨f1, f2, f3⟩ := leaf0_facts sw n u (r - off) hu hsw hu2 (by omega)
      rw [if_pos hr, if_pos hr, Nat.mod_eq_of_lt f1, Nat.shiftRight_eq_div_pow _ (64 + sw * n),
        Nat.div_eq_of_lt f1]
      exact ⟨f2, rfl, f3⟩
    · rw [if_neg hr, if_neg hr, absS_mk]
      exact ⟨by simp, by simp, by norm_num⟩
  refine ⟨⟨hwf, fun r => ?_⟩, fun r => ?_⟩
  · obtain ⟨k1, k2, k3⟩ := key r
    refine ⟨⟨?_, k3⟩, ?_⟩
    · rw [k1]
      intro T _
      by_cases hr : off ≤ r ∧ r < off + n
      · rw [if_pos hr, dg_mul_pow sw u hus]
        by_cases e : T = r - off
        · rw [if_pos e]; exact hu
        · rw [if_neg e]; exact Nat.two_pow_pos _
      · rw [if_neg hr, dg_zero_left]; exact Nat.two_pow_pos _
    · rw [k2]; exact ok_zero sw n
  · obtain ⟨k1, k2, _⟩ := key r
    refine ⟨?_, k1⟩
    show (absS (2^d) t' r >>> (64 + sw * n)) >>> 64 = 0
    rw [k2]; rfl

#print axioms gPre_sound
#print axioms init_ok

end GS

end
-- bos_merge: end Submission.Work.GCert.Scalar.Fin

-- bos_merge: begin Submission.Work.GCert.Scalar.End
section

/-!
# (key: gx-scalar) Final test, contents at the start and at the end, equality of tries

* `gFin_sound`    the final test: `P = N + unit at digit S - lo` (or `+ 0`);
* `cont_start`, `cont_end`   first contents and final test as contents (`gcont`);
* `beqK_eq`       the kernel's equality test of tries.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace GS
open SSC GXD

theorem finE_eq (sw u lo hi S : Nat) :
    Bool.rec (motive := fun _ => Nat) 0 (Bool.rec (motive := fun _ => Nat) 0
      (Nat.shiftLeft u (Nat.mul sw (Nat.sub S lo))) (Nat.ble (Nat.succ S) hi)) (Nat.ble lo S)
      = if lo ≤ S ∧ S < hi then u * 2^(sw * (S - lo)) else 0 := by
  by_cases h1 : lo ≤ S
  · have e1 : Nat.ble lo S = true := Nat.ble_eq_true_of_le h1
    rw [e1]
    by_cases h2 : S < hi
    · have e2 : Nat.ble (Nat.succ S) hi = true := Nat.ble_eq_true_of_le h2
      rw [e2, if_pos ⟨h1, h2⟩]
      exact Nat.shiftLeft_eq _ _
    · have e2 : Nat.ble (Nat.succ S) hi = false :=
        Bool.eq_false_iff.mpr (fun h => h2 (ble_true h))
      rw [e2, if_neg (fun h => h2 h.2)]
  · have e1 : Nat.ble lo S = false := Bool.eq_false_iff.mpr (fun h => h1 (ble_true h))
    rw [e1, if_neg (fun h => h1 h.1)]

theorem gFin_succ (sw K m2 u base lo hi : Nat) (tr : Trie) (cnt S : Nat) :
    gFin sw K m2 u base lo hi tr (cnt+1) S = tr.getK (Nat.add base S) fun x =>
      guard (Nat.beq (Nat.shiftRight (Nat.mod x m2) 64)
          (Nat.add (Nat.shiftRight (Nat.shiftRight x K) 64) (Bool.rec (motive := fun _ => Nat) 0
            (Bool.rec (motive := fun _ => Nat) 0 (Nat.shiftLeft u (Nat.mul sw (Nat.sub S lo)))
              (Nat.ble (Nat.succ S) hi)) (Nat.ble lo S))))
        (forceN (Nat.succ S) (gFin sw K m2 u base lo hi tr cnt)) := rfl

theorem gFin_sound (d sw K u base lo hi : Nat) (tr : Trie) (hwf : tr.wf d) :
    ∀ (cnt S : Nat), gFin sw K (2^K) u base lo hi tr cnt S = true → ∀ j, j < cnt →
      (absG d K tr).P (base + (S + j)) = (absG d K tr).N (base + (S + j))
        + (if lo ≤ S + j ∧ S + j < hi then u * 2^(sw * (S + j - lo)) else 0) := by
  intro cnt
  induction cnt with
  | zero =>
    intro S _ j hj
    exact absurd hj (Nat.not_lt_zero _)
  | succ cnt ih =>
    intro S h j hj
    rw [gFin_succ, Trie.getK_eq d tr hwf] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hr, h2⟩ := h
    obtain ⟨hb, h4⟩ := guard_true h2
    rw [forceN_eq] at h4
    have hr' : base + S < 2^d := hr
    cases j with
    | zero =>
      have hv := beq_true hb
      rw [finE_eq] at hv
      show (absS (2^d) tr (base + (S + 0)) % 2^K) >>> 64
        = (absS (2^d) tr (base + (S + 0)) >>> K) >>> 64 + _
      rw [Nat.add_zero, absS_apply d tr _ hr']
      exact hv
    | succ j =>
      have h5 := ih (S+1) h4 j (by omega)
      have e : S + (j + 1) = S + 1 + j := by omega
      rw [e]
      exact h5

/-- at the start the register `off + T` holds source `T`, all others nothing -/
theorem cont_start (sw n : Nat) (U : Nat → Nat) (a0 : SSt) (off u : Nat) (hu1 : 1 ≤ u)
    (hus : u < 2^sw)
    (h0 : ∀ r, a0.N r = 0 ∧ a0.P r = if off ≤ r ∧ r < off + n then u * 2^(sw * (r - off)) else 0)
    (r T : Nat) (hT : T < n) (hU : (off ≤ r ∧ r < off + n) → U r = u) :
    gcont sw U a0 r T = if r = off + T then 1 else 0 := by
  unfold gcont
  rw [(h0 r).1, (h0 r).2, dg_zero_left]
  by_cases hr : off ≤ r ∧ r < off + n
  · rw [if_pos hr, dg_mul_pow sw u hus, hU hr]
    have u0 : (u:ℚ) ≠ 0 := by positivity
    by_cases e : r = off + T
    · have e' : T = r - off := by omega
      rw [if_pos e', if_pos e]
      field_simp
      simp
    · have e' : ¬ T = r - off := by omega
      rw [if_neg e', if_neg e]
      simp
  · have e : ¬ r = off + T := by omega
    rw [if_neg hr, if_neg e, dg_zero_left]
    simp

/-- at the end: `P = N + unit at digit j` (if `c`) means the content is exactly source `j` -/
theorem cont_end (sw n : Nat) (U : Nat → Nat) (a : SSt) (r u j : Nat) (c : Prop) [Decidable c]
    (hsw : 1 ≤ sw) (hu1 : 1 ≤ u) (hu : u < 2^(sw - 1)) (hU : U r = u)
    (hsm : SmallV sw n (a.N r))
    (h : a.P r = a.N r + (if c then u * 2^(sw * j) else 0)) (T : Nat) (hT : T < n) :
    gcont sw U a r T = if c ∧ T = j then 1 else 0 := by
  have hus : u < 2^sw := lt_of_lt_of_le hu (Nat.pow_le_pow_right (by norm_num) (by omega))
  have u0 : (u:ℚ) ≠ 0 := by positivity
  unfold gcont
  rw [h, hU]
  by_cases hc : c
  · have hsmall : SmallV sw n (u * 2^(sw * j)) := by
      intro T' _
      rw [dg_mul_pow sw u hus]
      by_cases hT' : T' = j
      · rw [if_pos hT']; exact hu
      · rw [if_neg hT']; exact Nat.two_pow_pos _
    rw [if_pos hc, dg_add_small sw n _ _ hsw hsm hsmall T hT, dg_mul_pow sw u hus]
    by_cases e : T = j
    · rw [if_pos e, if_pos ⟨hc, e⟩]
      push_cast
      field_simp
      ring
    · rw [if_neg e, if_neg (fun h => e h.2)]
      push_cast
      simp
  · rw [if_neg hc, if_neg (fun h => hc h.1), Nat.add_zero]
    simp

theorem beqK_eq : ∀ (a b : Trie), beqK a b = true → a = b := by
  intro a
  induction a with
  | leaf x =>
    intro b h
    cases b with
    | leaf x' =>
      have h' : Nat.beq x x' = true := h
      rw [beq_true h']
    | node l' r' => exact absurd (show false = true from h) Bool.false_ne_true
  | node l r il ir =>
    intro b h
    cases b with
    | leaf x' => exact absurd (show false = true from h) Bool.false_ne_true
    | node l' r' =>
      have h' : guard (beqK l l') (beqK r r') = true := h
      obtain ⟨h1, h2⟩ := guard_true h'
      rw [il l' h1, ir r' h2]

#print axioms gFin_sound
#print axioms cont_start
#print axioms cont_end
#print axioms beqK_eq

end GS

end
-- bos_merge: end Submission.Work.GCert.Scalar.End

-- bos_merge: begin Submission.Work.GCert.Scalar.Runs
section

/-!
# (key: gx-scalar) Accepted replays as propositions: items, segments, `XRun`, `YRun`

* `ItemsRun`   a list of items (chunks of `A`, the scatter, chunks of `B`) on abstract states;
* `SegOK`      what an accepted segment check gives; `SegOK.append` joins two segments at a state;
* `XRun c lo n`  an accepted replay of the whole main phase for the sources `lo .. lo+n-1`:
  four abstract states joined by `GRun` on `addsA`, `scatAdds`, `addsB`, the first holding the
  sources in the x roles, the last holding exactly source `t` in `x_t` and in `y_t`;
* `YRun c lo n`  an accepted replay of the adds of `B` that read a y role.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace GS
open SSC GXD

/-- unit of the content of a register -/
noncomputable def U (c : Raw) (p : SPar) : Nat → Nat := unitK p.ux p.us p.uy c.v (2 * c.v)

/-- the single adds `(tgt, src, co)` of phase A / phase B, in order -/
def addsA (c : Raw) : List (Nat × Nat × Co) := c.gatesA.flatMap Gate.adds
def addsB (c : Raw) : List (Nat × Nat × Co) := c.gatesB.flatMap Gate.adds
/-- the single adds of the scatter: `y_t += co * (register of total k)` -/
noncomputable def scatAdds (c : Raw) : List (Nat × Nat × Co) := scatAddsFrom c.ret c.v (scatRows c)

/-- sizes of the scatter: `v` rows, every total index below the number of retained totals -/
def ScatShape (c : Raw) : Prop :=
  c.v + (scatRows c).length = 2 * c.v ∧ ∀ l ∈ scatRows c, ∀ x ∈ l, x.1 < c.ret.length

abbrev okA (c : Raw) : Nat → Nat → Bool := okAK c.v (2 * c.v) (2 * c.v + c.R)
abbrev okS (c : Raw) : Nat → Nat → Bool := okSK c.v (2 * c.v) (2 * c.v + c.R)
abbrev okB (c : Raw) : Nat → Nat → Bool := okBK c.v (2 * c.v) (2 * c.v + c.R)

/-- the tests on the parameters -/
structure PGood (c : Raw) (p : SPar) (lo n : Nat) : Prop where
  hx : 1 ≤ p.ux
  hs : 1 ≤ p.us
  hy : 1 ≤ p.uy
  hsw : 1 ≤ p.sw
  hd : 2 * c.v + c.R ≤ 2^p.d
  hn : lo + n ≤ c.v
  hxs : p.ux < 2^(p.sw - 1)
  hys : p.uy < 2^(p.sw - 1)
  hx2 : p.ux < 2^31
  hy2 : p.uy < 2^31
  hret : ∀ x ∈ c.ret, 2 * c.v ≤ x.1 ∧ x.1 < 2 * c.v + c.R

section
variable (c : Raw) (p : SPar) (lo n : Nat)

def ItemRun : Item → SSt → SSt → Prop
  | .cA gs, a, b => GRun p.sw n (U c p) (okA c) (fun _ => true) a (gs.flatMap Gate.adds) b
  | .scat, a, b => GRun p.sw n (U c p) (okS c) (fun _ => true) a (scatAdds c) b ∧ ScatShape c
  | .cB gs, a, b => GRun p.sw n (U c p) (okB c) (fun _ => true) a (gs.flatMap Gate.adds) b

def ItemsRun : List Item → SSt → SSt → Prop
  | [], a, b => b = a
  | it :: l, a, b => ∃ m, ItemRun c p n it a m ∧ ItemsRun l m b

/-- the first contents: the register `off + T` holds the unit `u` at digit `T` -/
def InitSt (off u : Nat) (a : SSt) : Prop :=
  ∀ r, a.N r = 0 ∧ a.P r = if off ≤ r ∧ r < off + n then u * 2^(p.sw * (r - off)) else 0

/-- the final test for the registers `base + S`, `S < v` -/
def FinSt (base u : Nat) (a : SSt) : Prop :=
  ∀ S, S < c.v → a.P (base + S) = a.N (base + S)
    + (if lo ≤ S ∧ S < lo + n then u * 2^(p.sw * (S - lo)) else 0)

def PostSt : Option Trie → SSt → Prop
  | none, b => SmallSt p.sw n b ∧ FinSt c p lo n 0 p.ux b ∧ FinSt c p lo n c.v p.uy b
  | some t, b => GOk p.d p.sw n t ∧ b = absG p.d (64 + p.sw * n) t

/-- **what an accepted segment gives** -/
def SegOK (pre : Option Trie) (items : List Item) (post : Option Trie) : Prop :=
  PGood c p lo n ∧
    match pre with
    | none => ∃ a b, InitSt p n lo p.ux a ∧ ItemsRun c p n items a b ∧ PostSt c p lo n post b
    | some t => GOk p.d p.sw n t →
        ∃ b, ItemsRun c p n items (absG p.d (64 + p.sw * n) t) b ∧ PostSt c p lo n post b

theorem ItemsRun_append (l1 l2 : List Item) : ∀ (a m b : SSt),
    ItemsRun c p n l1 a m → ItemsRun c p n l2 m b → ItemsRun c p n (l1 ++ l2) a b := by
  induction l1 with
  | nil =>
    intro a m b h1 h2
    have e : m = a := h1
    rw [e] at h2
    exact h2
  | cons x l1 ih =>
    intro a m b h1 h2
    obtain ⟨m1, hs, hr⟩ := h1
    exact ⟨m1, hs, ih m1 m b hr h2⟩

theorem ItemsRun_split (l1 l2 : List Item) : ∀ (a b : SSt),
    ItemsRun c p n (l1 ++ l2) a b → ∃ m, ItemsRun c p n l1 a m ∧ ItemsRun c p n l2 m b := by
  induction l1 with
  | nil => intro a b h; exact ⟨a, rfl, h⟩
  | cons x l1 ih =>
    intro a b h
    obtain ⟨m1, hs, hr⟩ := h
    obtain ⟨m, r1, r2⟩ := ih m1 b hr
    exact ⟨m, ⟨m1, hs, r1⟩, r2⟩

theorem SegOK.append' {pre post : Option Trie} {l1 l2 : List Item} {T : Trie}
    (h1 : SegOK c p lo n pre l1 (some T)) (h2 : SegOK c p lo n (some T) l2 post) :
    SegOK c p lo n pre (l1 ++ l2) post := by
  obtain ⟨hp, h1⟩ := h1
  obtain ⟨_, h2⟩ := h2
  refine ⟨hp, ?_⟩
  cases pre with
  | none =>
    obtain ⟨a, b, hi, hr, hT, eb⟩ := h1
    obtain ⟨b', hr', hpost⟩ := h2 hT
    rw [← eb] at hr'
    exact ⟨a, b', hi, ItemsRun_append c p n l1 l2 a b b' hr hr', hpost⟩
  | some t =>
    intro ht
    obtain ⟨b, hr, hT, eb⟩ := h1 ht
    obtain ⟨b', hr', hpost⟩ := h2 hT
    rw [← eb] at hr'
    exact ⟨b', ItemsRun_append c p n l1 l2 _ b b' hr hr', hpost⟩

theorem ItemsRun_cA (cs : List (List Gate)) : ∀ (a b : SSt),
    ItemsRun c p n (cs.map Item.cA) a b →
    GRun p.sw n (U c p) (okA c) (fun _ => true) a (cs.flatten.flatMap Gate.adds) b := by
  induction cs with
  | nil => intro a b h; exact h
  | cons gs cs ih =>
    intro a b h
    obtain ⟨m, h1, h2⟩ := h
    rw [List.flatten_cons, List.flatMap_append]
    exact GRun_append _ _ _ _ _ _ _ _ _ _ h1 (ih m b h2)

theorem ItemsRun_cB (cs : List (List Gate)) : ∀ (a b : SSt),
    ItemsRun c p n (cs.map Item.cB) a b →
    GRun p.sw n (U c p) (okB c) (fun _ => true) a (cs.flatten.flatMap Gate.adds) b := by
  induction cs with
  | nil => intro a b h; exact h
  | cons gs cs ih =>
    intro a b h
    obtain ⟨m, h1, h2⟩ := h
    rw [List.flatten_cons, List.flatMap_append]
    exact GRun_append _ _ _ _ _ _ _ _ _ _ h1 (ih m b h2)

end

/-- **two segments joined at a state** -/
theorem SegOK.append {c : Raw} {p : SPar} {lo n : Nat} {pre post : Option Trie}
    {l1 l2 : List Item} {T : Trie} (h1 : SegOK c p lo n pre l1 (some T))
    (h2 : SegOK c p lo n (some T) l2 post) : SegOK c p lo n pre (l1 ++ l2) post :=
  SegOK.append' c p lo n h1 h2

/-- **An accepted replay of the main phase** for the sources `lo .. lo+n-1`. -/
def XRun (c : Raw) (lo n : Nat) : Prop :=
  ∃ (p : SPar) (a0 a1 a2 a3 : SSt), PGood c p lo n ∧ InitSt p n lo p.ux a0 ∧
    GRun p.sw n (U c p) (okA c) (fun _ => true) a0 (addsA c) a1 ∧
    GRun p.sw n (U c p) (okS c) (fun _ => true) a1 (scatAdds c) a2 ∧ ScatShape c ∧
    GRun p.sw n (U c p) (okB c) (fun _ => true) a2 (addsB c) a3 ∧
    SmallSt p.sw n a3 ∧ FinSt c p lo n 0 p.ux a3 ∧ FinSt c p lo n c.v p.uy a3

/-- **An accepted replay of the adds of `B` reading a y role**, for the y roles `lo .. lo+n-1`. -/
def YRun (c : Raw) (lo n : Nat) : Prop :=
  ∃ (p : SPar) (a0 a3 : SSt), PGood c p lo n ∧ InitSt p n (c.v + lo) p.uy a0 ∧
    GRun p.sw n (U c p) (okB c) (selY c.v (2 * c.v)) a0 (addsB c) a3 ∧
    SmallSt p.sw n a3 ∧ FinSt c p lo n c.v p.uy a3

/-- the whole program in segments is an accepted replay -/
theorem XRun.of_seg {c : Raw} {p : SPar} {lo n : Nat} (h : SegOK c p lo n none (prog c) none) :
    XRun c lo n := by
  obtain ⟨hp, a, b, hi, hr, hsm, hfx, hfy⟩ := h
  obtain ⟨m1, r1, r2⟩ := ItemsRun_split c p n _ _ a b hr
  obtain ⟨m2, ⟨rs, hsh⟩, r3⟩ := r2
  exact ⟨p, a, m1, m2, b, hp, hi, ItemsRun_cA c p n _ a m1 r1, rs, hsh,
    ItemsRun_cB c p n _ m2 b r3, hsm, hfx, hfy⟩

/-- the same, the items given as a list equal to `prog c` (the equation holds by `rfl`) -/
theorem XRun.of_segs {c : Raw} {p : SPar} {lo n : Nat} {items : List Item}
    (h : SegOK c p lo n none items none) (e : prog c = items) : XRun c lo n :=
  XRun.of_seg (e ▸ h)

#print axioms SegOK.append
#print axioms XRun.of_seg

end GS

end
-- bos_merge: end Submission.Work.GCert.Scalar.Runs

-- bos_merge: begin Submission.Work.GCert.Scalar.Check
section

/-!
# (key: gx-scalar) The kernel checks give the accepted replays

* `SegOK.of_check`   `segCheck c p lo n pre items post = true → SegOK c p lo n pre items post`;
* `XRun.of_check`    `scalCheck c p lo n = true → XRun c lo n`;
* `YRun.of_check`    `yCheck c p lo n = true → YRun c lo n`.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace GS
open SSC GXD

section
variable (c : Raw) (p : SPar) (lo n : Nat) (hp : PGood c p lo n)
include hp

theorem U_pos (r : Nat) : 1 ≤ unitK p.ux p.us p.uy c.v (2 * c.v) r :=
  unitK_pos _ _ _ _ _ _ hp.hx hp.hs hp.hy

theorem gItem_sound (it : Item) (tr : Trie) (k : Trie → Bool) (hI : GOk p.d p.sw n tr)
    (h : gItem c p (2 * c.v) (2 * c.v + c.R) (maskW p.sw n) (64 + p.sw * n) (2^(64 + p.sw * n))
      c.ret.length it tr k = true) :
    ∃ tr', GOk p.d p.sw n tr' ∧ k tr' = true ∧
      ItemRun c p n it (absG p.d (64 + p.sw * n) tr) (absG p.d (64 + p.sw * n) tr') := by
  have hu := U_pos c p lo n hp
  cases it with
  | cA gs =>
    exact gGates_sound p.d p.sw n _ _ p.ux p.us p.uy c.v (2 * c.v) (okA c) (fun _ => true) hp.hsw rfl
      rfl hu gs tr k hI h
  | scat =>
    obtain ⟨tr', hI', hk, hlen, hb, hr⟩ := gScat_sound p.d p.sw n _ _ p.ux p.us p.uy c.v (2 * c.v)
      (okS c) hp.hsw rfl rfl hu c.ret c.ret.length (scatRows c) c.v tr k hI h
    exact ⟨tr', hI', hk, hr, hlen, hb⟩
  | cB gs =>
    exact gGates_sound p.d p.sw n _ _ p.ux p.us p.uy c.v (2 * c.v) (okB c) (fun _ => true) hp.hsw rfl
      rfl hu gs tr k hI h

theorem gItems_sound (items : List Item) : ∀ (tr : Trie) (k : Trie → Bool), GOk p.d p.sw n tr →
    gItems c p (2 * c.v) (2 * c.v + c.R) (maskW p.sw n) (64 + p.sw * n) (2^(64 + p.sw * n))
      c.ret.length items tr k = true →
    ∃ tr', GOk p.d p.sw n tr' ∧ k tr' = true ∧
      ItemsRun c p n items (absG p.d (64 + p.sw * n) tr) (absG p.d (64 + p.sw * n) tr') := by
  induction items with
  | nil => intro tr k hI h; exact ⟨tr, hI, h, rfl⟩
  | cons it items ih =>
    intro tr k hI h
    obtain ⟨tr1, hI1, hk1, r1⟩ := gItem_sound c p lo n hp it tr _ hI h
    obtain ⟨tr2, hI2, hk2, r2⟩ := ih tr1 k hI1 hk1
    exact ⟨tr2, hI2, hk2, _, r1, r2⟩

/-- the final test of a register class, from the kernel test -/
theorem fin_of (base u : Nat) (tr : Trie) (hI : GOk p.d p.sw n tr)
    (h : gFin p.sw (64 + p.sw * n) (2^(64 + p.sw * n)) u base lo (lo + n) tr c.v 0 = true) :
    FinSt c p lo n base u (absG p.d (64 + p.sw * n) tr) := by
  intro S hS
  have := gFin_sound p.d p.sw (64 + p.sw * n) u base lo (lo + n) tr hI.wf c.v 0 h S hS
  rw [Nat.zero_add] at this
  exact this

end

theorem pgood_of {c : Raw} {p : SPar} {lo n : Nat} {X : Prop}
    (h : (1 ≤ p.ux ∧ 1 ≤ p.us ∧ 1 ≤ p.uy ∧ 1 ≤ p.sw) ∧ 2 * c.v + c.R ≤ 2^p.d ∧ lo + n ≤ c.v ∧
      (p.ux < 2^(p.sw - 1) ∧ p.uy < 2^(p.sw - 1) ∧ p.ux < 2^31 ∧ p.uy < 2^31) ∧
      (∀ x ∈ c.ret, 2 * c.v ≤ x.1 ∧ x.1 < 2 * c.v + c.R) ∧ X) :
    PGood c p lo n ∧ X :=
  ⟨⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2, h.2.1, h.2.2.1, h.2.2.2.1.1, h.2.2.2.1.2.1,
    h.2.2.2.1.2.2.1, h.2.2.2.1.2.2.2, h.2.2.2.2.1⟩, h.2.2.2.2.2⟩

/-- **an accepted segment check** -/
theorem SegOK.of_check {c : Raw} {p : SPar} {lo n : Nat} {pre post : Option Trie}
    {items : List Item} (h : segCheck c p lo n pre items post = true) :
    SegOK c p lo n pre items post := by
  unfold segCheck at h
  obtain ⟨hp, h1⟩ := pgood_of (gPre_sound c p lo n _ h)
  rw [forceN_eq] at h1
  refine ⟨hp, ?_⟩
  -- the end of the segment
  have hpost : ∀ tr3, GOk p.d p.sw n tr3 →
      Option.rec (motive := fun _ => Bool)
        (guard (gFin p.sw (64 + p.sw * n) (2^(64 + p.sw * n)) p.ux 0 lo (lo + n) tr3 c.v 0)
          (gFin p.sw (64 + p.sw * n) (2^(64 + p.sw * n)) p.uy c.v lo (lo + n) tr3 c.v 0))
        (fun t => beqK tr3 t) post = true →
      PostSt c p lo n post (absG p.d (64 + p.sw * n) tr3) := by
    intro tr3 hI3 hk
    cases post with
    | none =>
      obtain ⟨f1, f2⟩ := guard_true hk
      exact ⟨hI3.small, fin_of c p lo n hp 0 p.ux tr3 hI3 f1, fin_of c p lo n hp c.v p.uy tr3 hI3 f2⟩
    | some t =>
      have e : tr3 = t := beqK_eq tr3 t hk
      rw [← e]
      exact ⟨hI3, rfl⟩
  cases pre with
  | none =>
    have h2 : gInit p.sw p.ux lo n 0 (Trie.mk p.d) (fun tr0 =>
        gItems c p (2 * c.v) (2 * c.v + c.R) (maskW p.sw n) (64 + p.sw * n) (2^(64 + p.sw * n))
          c.ret.length items tr0 fun tr3 => Option.rec (motive := fun _ => Bool)
            (guard (gFin p.sw (64 + p.sw * n) (2^(64 + p.sw * n)) p.ux 0 lo (lo + n) tr3 c.v 0)
              (gFin p.sw (64 + p.sw * n) (2^(64 + p.sw * n)) p.uy c.v lo (lo + n) tr3 c.v 0))
            (fun t => beqK tr3 t) post) = true := h1
    have hle : lo + 0 + n ≤ 2^p.d := by have := hp.hd; have := hp.hn; omega
    obtain ⟨t0, hwf, hk, hval⟩ := gInit_sound p.d p.sw p.ux lo n 0 (Trie.mk p.d) _ (Trie.wf_mk p.d)
      hle h2
    obtain ⟨hI0, hinit⟩ := init_ok p.d p.sw n p.ux lo hp.hsw hp.hxs hp.hx2 t0 hwf hval
    obtain ⟨tr3, hI3, hk3, hr⟩ := gItems_sound c p lo n hp items t0 _ hI0 hk
    exact ⟨_, _, hinit, hr, hpost tr3 hI3 hk3⟩
  | some t =>
    intro hI0
    have h2 : gItems c p (2 * c.v) (2 * c.v + c.R) (maskW p.sw n) (64 + p.sw * n)
        (2^(64 + p.sw * n)) c.ret.length items t (fun tr3 => Option.rec (motive := fun _ => Bool)
          (guard (gFin p.sw (64 + p.sw * n) (2^(64 + p.sw * n)) p.ux 0 lo (lo + n) tr3 c.v 0)
            (gFin p.sw (64 + p.sw * n) (2^(64 + p.sw * n)) p.uy c.v lo (lo + n) tr3 c.v 0))
          (fun t => beqK tr3 t) post) = true := h1
    obtain ⟨tr3, hI3, hk3, hr⟩ := gItems_sound c p lo n hp items t _ hI0 h2
    exact ⟨_, hr, hpost tr3 hI3 hk3⟩

/-- **the scalar check in one evaluation** -/
theorem XRun.of_check {c : Raw} {p : SPar} {lo n : Nat} (h : scalCheck c p lo n = true) :
    XRun c lo n := XRun.of_seg (SegOK.of_check h)

/-- **the y check** -/
theorem YRun.of_check {c : Raw} {p : SPar} {lo n : Nat} (h : yCheck c p lo n = true) :
    YRun c lo n := by
  unfold yCheck at h
  obtain ⟨hp, h1⟩ := pgood_of (gPre_sound c p lo n _ h)
  have hle : c.v + lo + 0 + n ≤ 2^p.d := by have := hp.hd; have := hp.hn; omega
  obtain ⟨t0, hwf, hk, hval⟩ := gInit_sound p.d p.sw p.uy (c.v + lo) n 0 (Trie.mk p.d) _
    (Trie.wf_mk p.d) hle h1
  obtain ⟨hI0, hinit⟩ := init_ok p.d p.sw n p.uy (c.v + lo) hp.hsw hp.hys hp.hy2 t0 hwf hval
  obtain ⟨tr3, hI3, hk3, hr⟩ := gChunks_sound p.d p.sw n _ _ p.ux p.us p.uy c.v (2 * c.v) (okB c)
    (selY c.v (2 * c.v)) hp.hsw rfl rfl (U_pos c p lo n hp) c.B t0 _ hI0 hk
  exact ⟨p, _, _, hp, hinit, hr, hI3.small, fin_of c p lo n hp c.v p.uy tr3 hI3 hk3⟩

#print axioms SegOK.of_check
#print axioms XRun.of_check
#print axioms YRun.of_check

end GS

end
-- bos_merge: end Submission.Work.GCert.Scalar.Check
