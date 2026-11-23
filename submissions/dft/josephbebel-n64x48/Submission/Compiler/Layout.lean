--might be  containing modified Apache-2.0 codes pieces from one or several sources; notices and credits: Credits.lean
import Submission.Compiler.Judgment
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.SuccPred
import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.Nat.Log

namespace OAI.PowerSaving.DigitArith

theorem div_join {a b n : Nat} (hb : b < n) : (a * n + b) / n = a := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) hb
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hb, Nat.zero_add]

theorem mod_join {a b n : Nat} (hb : b < n) : (a * n + b) % n = b := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]

theorem lt_join {a b m n : Nat} (h : a < m) (g : b < n) : a * n + b < m * n :=
  Nat.lt_of_lt_of_le (Nat.add_lt_add_left g _) (by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ h)

theorem div_join' {a b n : Nat} (hb : b < n) : (b + n * a) / n = a := by
  rw [Nat.mul_comm, Nat.add_comm]; exact div_join hb

theorem mod_join' {a b n : Nat} (hb : b < n) : (b + n * a) % n = b := by
  rw [Nat.mul_comm, Nat.add_comm]; exact mod_join hb

theorem getD_append_left {β : Type _} (L M : List β) (z : β) {k : Nat} (hk : k < L.length) :
    (L ++ M).getD k z = L.getD k z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

theorem getD_append_right {β : Type _} (L M : List β) (z : β) (k : Nat) :
    (L ++ M).getD (L.length + k) z = M.getD k z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right _ _)]

theorem split3_eq (a b c P Q : Nat) : a + P * b + P * Q * c = a + P * (b + Q * c) := by
  rw [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

theorem split3_mod {a b c P Q : Nat} (ha : a < P) : (a + P * b + P * Q * c) % P = a := by
  rw [split3_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]

theorem split3_mid {a b c P Q : Nat} (ha : a < P) (hb : b < Q) :
    (a + P * b + P * Q * c) / P % Q = b := by
  have hP : 0 < P := Nat.lt_of_le_of_lt (Nat.zero_le _) ha
  rw [split3_eq, Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt ha, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]

theorem split3_low {a b P Q : Nat} (ha : a < P) (hb : b < Q) : a + P * b < P * Q := by
  have h1 : P * (b + 1) ≤ P * Q := Nat.mul_le_mul_left P hb
  rw [Nat.mul_succ] at h1
  omega

theorem split3_div {a b c P Q : Nat} (ha : a < P) (hb : b < Q) :
    (a + P * b + P * Q * c) / (P * Q) = c := by
  have hl := split3_low ha hb
  have hPQ : 0 < P * Q := Nat.lt_of_le_of_lt (Nat.zero_le _) hl
  rw [Nat.add_mul_div_left _ _ hPQ, Nat.div_eq_of_lt hl, Nat.zero_add]

theorem split3_parts {a b c P Q T : Nat} (h : a + P * b + P * Q * c = T) :
    a ≤ T ∧ P * b ≤ T ∧ P * Q * c ≤ T ∧ a + P * b ≤ T := by
  omega

end OAI.PowerSaving.DigitArith

namespace OAI.PowerSaving
open Finset
structure Layout (α : Type*) where
  n : ℕ
  loc : α → ℕ
  bd : ∀ i, loc i < n
  inj : Function.Injective loc
  onto : ∀ j : Fin n, ∃ i, loc i = j.val
namespace Layout
variable {α β μ : Type*}
noncomputable def atFin (L : Layout α) (j : Fin L.n) : α := Classical.choose (L.onto j)
@[simp] lemma loc_atFin (L : Layout α) (j : Fin L.n) : L.loc (L.atFin j) = j.val := Classical.choose_spec (L.onto j)
def toIx (L : Layout α) (i : α) : Fin L.n := ⟨L.loc i,L.bd i⟩
noncomputable def index (L : Layout α) : α ≃ Fin L.n :=
  ⟨L.toIx,L.atFin,fun _ => L.inj (L.loc_atFin _),fun j => Fin.ext (L.loc_atFin j)⟩
noncomputable def tape (L : Layout α) (x : α → μ) : Tape μ :=
  ⟨L.n, fun j => x (L.atFin j)⟩
@[simp] lemma read (L : Layout α) (x : α → μ) (i : α) (z : μ) : (L.tape x).look (L.loc i) z = x i := by
  rw [Tape.look_of_lt (L.tape x) z (L.bd i)]; exact congrArg x (L.inj (L.loc_atFin _))
lemma verify (L : Layout α) (v : Tape μ) (z : μ) (x : α → μ) (h : v.len = L.n) (hx : ∀ i, v.look (L.loc i) z = x i) : v = L.tape x :=
  Tape.ext_look h z fun j hj => by
    obtain ⟨i, hi⟩ := L.onto ⟨j, by omega⟩
    obtain rfl : j = L.loc i := hi.symm
    rw [hx, read]
def std (n : ℕ) : Layout (Fin n) :=
  ⟨n,Fin.val, Fin.isLt, fun _ _ => Fin.ext, fun j => ⟨j, rfl⟩⟩
lemma card [Fintype α] (X : Layout α) : Fintype.card α = X.n :=
  (Fintype.card_congr X.index).trans (Fintype.card_fin _)
def comap (L : Layout α) (f : β ≃ α) : Layout β where
  n := L.n
  loc := fun j => L.loc (f j)
  bd := fun j => L.bd (f j)
  inj := fun _ _ h => f.injective (L.inj h)
  onto j := (L.onto j).elim fun i hi => ⟨f.symm i, (congrArg L.loc (f.apply_symm_apply i)).trans hi⟩
noncomputable def someLayout (α : Type*) [Fintype α] : Layout α :=
  (std _).comap (Fintype.equivFin α)
open DigitArith in
def pair (X : Layout α) (Y : Layout β) : Layout (α × β) where
  n := X.n * Y.n
  loc := fun i => X.loc i.1*Y.n + Y.loc i.2
  bd i := lt_join (X.bd i.1) (Y.bd i.2)
  inj a b h := Prod.ext (X.inj ((div_join (Y.bd a.2)).symm.trans ((congrArg (· / Y.n) h).trans (div_join (Y.bd b.2)))))
    (Y.inj ((mod_join (Y.bd a.2)).symm.trans ((congrArg (· % Y.n) h).trans (mod_join (Y.bd b.2)))))
  onto j := by
    have hy := Nat.pos_of_mul_pos_left (Nat.zero_lt_of_lt j.2)
    obtain ⟨a, ha⟩ := X.onto ⟨j / Y.n, (Nat.div_lt_iff_lt_mul hy).2 j.2⟩
    obtain ⟨b, hb⟩ := Y.onto ⟨j % Y.n, Nat.mod_lt _ hy⟩
    exact ⟨(a,b), by rw [ha, hb]; exact Nat.div_add_mod' _ _⟩
@[simp] lemma pair_len (X : Layout α) (Y : Layout β) : (X.pair Y).n = X.n * Y.n := rfl
@[simp] lemma pair_loc (X : Layout α) (Y : Layout β) (i) : (X.pair Y).loc i = X.loc i.1*Y.n+Y.loc i.2 := rfl
lemma pair_div (X : Layout α) (Y : Layout β) (i) : (X.pair Y).loc i / Y.n = X.loc i.1 := DigitArith.div_join (Y.bd _)
lemma pair_mod (X : Layout α) (Y : Layout β) (i) : (X.pair Y).loc i % Y.n = Y.loc i.2 := DigitArith.mod_join (Y.bd _)
def cat (X : Layout α) (Y : Layout β) : Layout (α ⊕ β) where
  n := X.n+Y.n
  loc := Sum.elim X.loc (fun i => X.n+Y.loc i)
  bd := by rintro (i|i) <;> simp [Nat.lt_add_right, X.bd, Y.bd]
  inj := by rintro (a|a) (b|b) h <;> simp at h <;> [rw [X.inj h]; (have := X.bd a; omega); (have := X.bd b; omega); rw [Y.inj h]]
  onto j := if h : j.1 < X.n then ⟨.inl (X.atFin ⟨j, h⟩), by simp⟩ else ⟨.inr (Y.atFin ⟨j - X.n, by omega⟩), by simp; omega⟩
def permFn (e : α ≃ β) (μ : Type*) : (α → μ) ≃ (β → μ) where
  toFun f := f ∘ e.symm
  invFun f := f ∘ e
  left_inv f := funext fun x => congrArg f (e.symm_apply_apply x)
  right_inv f := funext fun x => congrArg f (e.apply_symm_apply x)
lemma vec_code (X : Layout α) (k : ℕ) (x : Fin k → α) :
    ∑ i, X.loc (x i)*X.n^i.val = finFunctionFinEquiv (fun i => X.toIx (x i)) := by
  rw [finFunctionFinEquiv_apply]; try rfl
def vecFin (X : Layout α) (k : ℕ) : Layout (Fin k → α) where
  n := X.n^k
  loc := fun x => ∑ i, X.loc (x i)*X.n^i.val
  bd x := by show ∑ i, X.loc (x i)*X.n^i.val < X.n^k; rw [vec_code]; exact Fin.isLt _
  inj a b h := funext fun i => X.inj (congrArg Fin.val (congrFun (finFunctionFinEquiv.injective
    (Fin.ext (by rw [← vec_code, ← vec_code]; exact h) :
      finFunctionFinEquiv (fun i => X.toIx (a i)) = finFunctionFinEquiv fun i => X.toIx (b i))) i))
  onto j := ⟨fun i => X.atFin (finFunctionFinEquiv.symm j i), by
    show ∑ i : Fin k, X.loc (X.atFin _) * X.n^i.val = j.val
    simp only [loc_atFin]; rw [← finFunctionFinEquiv_apply, Equiv.apply_symm_apply]⟩
noncomputable def digits (J : Layout β) (X : Layout α) : Layout (β → α) :=
  (vecFin X J.n).comap (permFn J.index α)
@[simp] lemma digits_len (J : Layout β) (X : Layout α) : (digits J X).n = X.n^J.n := rfl
lemma digits_code [Fintype β] (J : Layout β) (X : Layout α) (x : β→α) : (digits J X).loc x = ∑ j, X.loc (x j)*X.n^(J.loc j) := by
  show ∑ i, X.loc (x (J.index.symm i)) * X.n^i.val = _
  exact (Fintype.sum_equiv J.index _ _ fun j => by
    first | (simp only [Equiv.symm_apply_apply]; done) | (simp only [Equiv.symm_apply_apply]; rfl)).symm
lemma digits_entry (J : Layout β) (X : Layout α) (x : β→α) (j : β) : (digits J X).loc x / X.n^(J.loc j) % X.n=X.loc (x j) := by
  have h := finFunctionFinEquiv_symm_apply_val (finFunctionFinEquiv fun i => X.toIx (x (J.index.symm i))) (J.index j)
  rw [Equiv.symm_apply_apply, ← vec_code] at h
  exact h.symm.trans (congrArg X.loc (congrArg x (J.index.symm_apply_apply j)))
end Layout
namespace RAM
open Ty
noncomputable section
universe U V Z
section
variable {ι : Type U} {α : ι → Type V}
namespace Able
variable {m : Bool} {r : Port} {b : Bank r ι} {s t : Ty}
  {x : ι → T s} {W Z P H : ι → ℕ}
lemma layout {L : ∀ i, Layout (α i)} {v : ∀ i, α i → T t} (h : Able m b s w x (fun i => (L i).n) W Z) (hs : Able m (b.comap (Sigma.fst (β:=α))) (p s w) t (fun d => (x d.1,(L d.1).loc d.2)) (fun d => v d.1 d.2) (fun d => P d.1) (fun d => H d.1)) (hc : Small b.B fun i => (L i).n) : Able m b s (a t) x (fun i => (L i).tape (v i)) (fun i => W i+(L i).n+(L i).n*P i) (fun i => Z i+(L i).n*H i) := by
  have := Able.tab (v := fun i j => if hj : j < (L i).n then v i ((L i).atFin ⟨j, hj⟩) else t.blank)
    (Wb := fun i _ => P i) (Zb := fun i _ => H i) h
    ((Able.reindex hs fun d : During (fun i => (L i).n) => (⟨d.i, (L d.i).atFin ⟨d.j, d.hj⟩⟩ : Σ i, α i)).cong
      (fun _ => by simp) fun d => by simp [d.hj]) hc
  exact (this.cong (fun _ => rfl) fun i => congrArg (Tape.mk _) (funext fun j => dif_pos j.2)).mono
    (fun _ => by simp) fun _ => by simp
end Able
namespace Small
lemma loc {B : ι → ℕ} {x : ∀ i, α i} {L : ∀ i, Layout (α i)} (h : Small B fun i => (L i).n) : Small B fun i => (L i).loc (x i) :=
  h.mono fun i => ((L i).bd _).le
end Small
namespace Can
variable {m : Bool} {s t : Ty} {x : ι → T s}
  {B W P : ι → ℕ} {L : ∀ i, Layout (α i)} {v : ∀ i, α i → T t}
lemma layout (h : Can m B s w x (fun i => (L i).n) W) (g : Can m (fun d : Σ i, α i => B d.1) (p s w) t (fun d => (x d.1,(L d.1).loc d.2)) (fun d => v d.1 d.2) (fun d => P d.1)) (hn : Small B fun i => (L i).n) : Can m B s (a t) x (fun i => (L i).tape (v i)) (fun i => W i+(L i).n+(L i).n*P i) :=
  Able.mono (Able.layout (P := P) (H := fun _ => 0) h g hn) (fun _ => le_rfl) fun _ => by simp
lemma fetch {i : ∀ d, α d} (h : Can m B s (a t) x (fun i => (L i).tape (v i)) W) (g : Can m B s w x (fun d => (L d).loc (i d)) W) : Can m B s t x (fun d => v d (i d)) W :=
  (look h g).cy fun d => Layout.read _ _ _ _
variable {μ : Type V}
lemma eqbit {n q : ι → ℕ} (h : Can m B s w x n W) (k : Can m B s w x q W) : Can m B s w x (fun i => if n i = q i then 0 else 1) W :=
  (wadd (wlt h k) (wlt k h) ((Small.const B 2).mono fun _ => by split_ifs <;> omega)).cy fun i => by
    rcases lt_trichotomy (n i) (q i) with e | e | e
    · simp [e, e.ne, Nat.lt_asymm e]
    · simp [e]
    · simp [e, e.ne', Nat.lt_asymm e]
lemma cases_code [DecidableEq μ] [Fintype μ] {y : ι → T t} {q : ι→μ} (D : Layout μ) (h : Can m B s w x (fun i => D.loc (q i)) W) (g : ∀ f : μ, Can m (fun i : {i // q i=f} => B i.1) s t (fun i => x i.1) (fun i => y i.1) (fun i => W i.1)) : Can m B s t x y W := by
  suffices ∀ k {κ : Type U} (e : κ → ι), (∀ j, D.loc (q (e j)) < k) →
      Can m (fun j => B (e j)) s t (fun j => x (e j)) (fun j => y (e j)) (fun j => W (e j)) from
    this D.n (·) fun _ => D.bd _
  intro k; induction k with
  | zero => exact fun _ hk => ⟨Code.blank s t, 0, 0, fun j => absurd (hk j) (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro κ e hk
    refine testz (eqbit (reindex h e) (wc k)) ?_ (ih (fun j : Subtype _ => e j.1) fun j => ?_)
    · by_cases hn : k < D.n
      · exact reindex (g (D.atFin ⟨k, hn⟩)) fun j : Subtype _ =>
          ⟨e j.1, D.inj ((by simpa using j.2 : D.loc (q (e j.1)) = k).trans (D.loc_atFin ⟨k, hn⟩).symm)⟩
      · exact ⟨Code.blank s t, 0, 0, fun j => absurd (by
          have : D.loc (q (e j.1)) = k := (by simpa using j.2); have := D.bd (q (e j.1)); omega) hn⟩
    · have h1 : D.loc (q (e j.1)) ≠ k := fun h' => j.2 (by simp [h'])
      have := hk j.1; show D.loc (q (e j.1)) < k; omega
lemma sumP {X} [AddCommMonoid X] (P : (ι → X) → Prop) {v : μ → ι → X} (h : ∀ i, P (v i))
    (z : P fun _ => 0) (ad : ∀ {f g}, P f → P g → P fun j => f j + g j) (S : Finset μ) : P fun j => ∑ i ∈ S, v i j := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using z
  | insert a S ha ih => simpa [sum_insert ha] using ad (h a) ih
lemma sum_wconst [Fintype μ] {v : μ → ι → ℕ} (h : ∀ i : μ, Can m B s w x (v i) W) (g : ∀ i : μ, Small B (v i)) : Can m B s w x (fun j => ∑ i, v i j) W :=
  (sumP (fun f => Can m B s w x f W ∧ Small B f) (fun i => ⟨h i, g i⟩) ⟨wc 0, Small.const B 0⟩
    (fun a b => ⟨wadd a.1 b.1 (a.2.add b.2), a.2.add b.2⟩) univ).1
lemma sum_cconst [Fintype μ] {cl} {v : μ → ι → ℂ} (h : ∀ i : μ, Can m B s (c cl) x (v i) W) : Can m B s (c cl) x (fun j => ∑ i, v i j) W :=
  sumP (fun f => Can m B s (c cl) x f W) h zero add univ
end Can
end
lemma log_step (A j : ℕ) : (A/2^j/2, Nat.log 2 A - Nat.log 2 (A/2^j) + (if 1 < A/2^j then 1 else 0)) =
    (A/2^(j+1), Nat.log 2 A - Nat.log 2 (A/2^(j+1))) := by
  rw [pow_succ, ← Nat.div_div_eq_div_mul, Nat.log_div_base]
  have : Nat.log 2 (A/2^j) ≤ Nat.log 2 A := Nat.log_mono_right (Nat.div_le_self _ _)
  split_ifs with h
  · have := Nat.le_log_of_pow_le (by norm_num : 1 < 2) (show 2^1 ≤ A/2^j by rw [pow_one]; omega)
    exact Prod.ext rfl (by omega)
  · rw [Nat.log_of_lt (show A/2^j < 2 by omega)]; exact Prod.ext rfl (by omega)
section
variable {ι : Type U} {m : Bool}
namespace Small
variable {B P Q : ι → ℕ}
lemma sub (h : Small B P) : Small B (fun i => P i-Q i) := h.mono fun _ => Nat.sub_le _ _
lemma div (h : Small B P) : Small B (fun i => P i/Q i) := h.mono fun _ => Nat.div_le_self _ _
lemma mod (h : Small B P) : Small B (fun i => P i%Q i) := h.mono fun _ => Nat.mod_le _ _
end Small
namespace Can
variable {s t : Ty} {x : ι → T s} {B W A Q : ι → ℕ}
lemma neg {cl} {z : ι→ℂ} (h : Can m B s (c cl) x z W) : Can m B s (c cl) x (fun i => -(z i)) W :=
  (sub zero h).cy fun _ => zero_sub _
section
variable (h : Can m B s w x A W) (k : Can m B s w x Q W) (hh : Small B A)
include h k hh
lemma minus : Can m B s w x (fun i => A i - Q i) W := wsub h k hh.sub
lemma times (gg : Small B Q) : Can m B s w x (fun i => A i * Q i) W := wmul h k (hh.mul gg)
lemma plus (gg : Small B Q) : Can m B s w x (fun i => A i + Q i) W := wadd h k (hh.add gg)
lemma dvdW : Can m B s w x (fun i => A i / Q i) W := wdiv h k hh.div
lemma modW : Can m B s w x (fun i => A i % Q i) W := wmod h k hh.mod
end
lemma wpow_fixed (n : ℕ) (h : Can m B s w x A W) (hh : Small B A) : Can m B s w x (fun i => (A i)^n) W := by
  induction n with
  | zero => exact (wc 1).cy fun _ => (pow_zero _).symm
  | succ n ih => exact (times ih h (hh.pow n) hh).cy fun _ => (pow_succ _ _).symm
lemma wTwo (h : Can m B s w x A W) (hh : Small B A) (hq : Small B fun i => 2^A i) (ha : Dom W A) : Can m B s w x (fun i => 2^A i) W :=
  weaken (loop (W' := W) (uB := fun _ _ => 0) (v := fun _ j => 2^j) h (wc 1)
    ((wmul (snd second) (wc 2) ((hq.reindex During.i).mono fun d => by
      rw [← pow_succ]; exact Nat.pow_le_pow_right (by norm_num) d.hj)).cy fun _ => (pow_succ _ _).symm) hh)
    ((((Dom.self W).add (Dom.self W)).add ha).trans (Dom.of_le fun i => by simp))
lemma logC (h : Can m B s w x A W) (hh : Small B A) (ha : Dom W A) : Can m B s w x (fun i => Nat.log 2 (A i)) W := by
  have hA := hh.reindex (During.i (n := A))
  exact weaken (cy (snd (loop (uB := fun _ _ => 0)
    (v := fun i j => (A i / 2^j, Nat.log 2 (A i) - Nat.log 2 (A i / 2^j))) h (cy (pair h (wc 0)) fun i => by simp)
    (cy (pair (wdiv (fst (snd second)) (wc 2) (hA.mono fun d => (Nat.div_le_self _ _).trans (Nat.div_le_self _ _)))
      (wadd (snd (snd second)) (wlt (wc 1) (fst (snd second))) (hA.mono fun d =>
        (congrArg Prod.snd (log_step (A d.i) d.j)).le.trans ((Nat.sub_le _ _).trans (Nat.log_le_self _ _)))))
      fun d => log_step (A d.i) d.j) hh)) fun i => by
        simp [Nat.div_eq_of_lt (Nat.lt_pow_self (by norm_num : 1 < 2) .. : A i < 2 ^ A i)])
    ((((Dom.self W).add (Dom.self W)).add ha).trans (Dom.of_le fun i => by simp))
lemma natC (n : ℕ) : Can m B s sc x (fun _ => (n:ℂ)) W := by
  induction n with
  | zero => exact zero.cy fun _ => Nat.cast_zero.symm
  | succ n ih => exact (add ih one).cy fun _ => (Nat.cast_succ n).symm
lemma rat (z : ℚ) : Can m B s sc x (fun _ => (z:ℂ)) W := by
  have hn : Can m B s sc x (fun _ => ((z.num : ℤ) : ℂ)) W := by
    cases z.num with
    | ofNat n => exact (natC n).cy fun _ => (Int.cast_natCast n).symm
    | negSucc n => exact (neg (natC (n+1))).cy fun _ => (Int.cast_negSucc n).symm
  exact (mul hn (inv (natC z.den) fun _ => by simp)).cy
    fun _ => by rw [Rat.cast_def, div_eq_mul_inv]
section
variable {α β : ι → Type*} {L : ∀ i, Layout (α i)} {R : ∀ i, Layout (β i)}
  {u : ∀ i, α i × β i}
lemma addr_join (h : Can m B s w x (fun i => (L i).loc (u i).1) W) (k : Can m B s w x (fun i => (R i).loc (u i).2) W) (d : Can m B s w x (fun i => (R i).n) W) (hl : Small B fun i => (L i).n) (hr : Small B fun i => (R i).n) : Can m B s w x (fun i => ((L i).pair (R i)).loc (u i)) W :=
  wadd (wmul h d ((Small.loc hl).mul hr)) k (((Small.loc hl).mul hr).add (Small.loc hr))
variable (h : Can m B s w x (fun i => ((L i).pair (R i)).loc (u i)) W) (k : Can m B s w x (fun i => (R i).n) W) (hs : Small B fun i => (L i).n*(R i).n)
include h k hs
lemma addr_high : Can m B s w x (fun i => (L i).loc (u i).1) W :=
  (wdiv h k (hs.mono fun i => (Nat.div_le_self _ _).trans (((L i).pair (R i)).bd (u i)).le)).cy fun i => Layout.pair_div _ _ _
lemma addr_low : Can m B s w x (fun i => (R i).loc (u i).2) W :=
  (wmod h k (hs.mono fun i => (Nat.mod_le _ _).trans (((L i).pair (R i)).bd (u i)).le)).cy fun i => Layout.pair_mod _ _ _
end
end Can
end
namespace Bench
section
variable {m : Bool} {ι : Type U} {κ : Type V} {μ : Type Z}
def Moves (b : Bench m ι) (W : ι→ℕ) (t : Ty) (f : ι→T t) : Prop :=
  Can m b.size b.tray t b.env f W
structure Nick (b : Bench m ι) (f : ι→ℕ) : Prop where
  close : b.Moves (fun _ => 0) w f
  small : Small b.size f
structure Instant (b : Bench m ι) (q : Bench m κ) (f : ι→κ) : Prop where
  prep : b.Moves (fun _ => 0) q.tray fun i => q.env (f i)
  covers : Small b.size fun i => q.size (f i)
variable {b : Bench m ι} {q : Bench m κ} {z : Bench m μ} {s t : Ty} {W : ι → ℕ}
  {x y : ι → T t}
namespace Moves
lemma congr (h : b.Moves W t x) (g : ∀ i, x i=y i) : b.Moves W t y := Can.cy h g
lemma weaken {P} (h : b.Moves W t x) (g : Dom P W) : b.Moves P t x := Can.weaken h g
lemma ease (h : b.Moves (fun _ => 0) t x) (V : ι → ℕ) : b.Moves V t x := Can.mono h fun _ => Nat.zero_le _
lemma wc (n : ℕ) : b.Moves W w fun _ => n := Can.wc n
lemma pair {u : ι → T s} (h : b.Moves W s u) (g : b.Moves W t x) : b.Moves W (p s t) fun i => (u i,x i) := Can.pair h g
lemma fst {v : ι → T (p s t)} (h : b.Moves W (p s t) v) : b.Moves W s fun i => (v i).1 := Can.fst h
lemma snd {v : ι → T (p s t)} (h : b.Moves W (p s t) v) : b.Moves W t fun i => (v i).2 := Can.snd h
lemma len {v : ι→Tape (T t)} (h : b.Moves W (a t) v) (g : Small b.size fun i => (v i).len) : b.Moves W w fun i => (v i).len := Can.len h g
lemma pick {n k : ι → ℕ} (x : ι → ℕ → T t) (h : b.Moves W (a t) fun i => Tape.tab (n i) (x i)) (g : b.Moves W w k) (hh : ∀ i, k i<n i) : b.Moves W t fun i => x i (k i) :=
  (Can.look h g).cy fun i => by simp [Tape.look_tab, hh i]
lemma transfer {P : κ→ℕ} {x : κ→T t} (h : q.Moves P t x) {f} (g : b.Instant q f) : b.Moves (fun i => P (f i)) t fun i => x (f i) :=
  Can.mono (Can.pipe g.prep (Can.ambient (Can.reindex h f) g.covers)) fun _ => (Nat.zero_add _).le
variable {cl : Paint}
lemma zero : b.Moves W (c cl) (fun _ => 0) := Can.zero
lemma one : b.Moves W sc (fun _ => 1) := Can.one
variable {X Y : ι→ℂ}
lemma mul (h : b.Moves W sc X) (g : b.Moves W (c cl) Y) : b.Moves W (c cl) fun i => X i*Y i := Can.mul h g
lemma inv (h : b.Moves W sc X) (k : ∀ i, X i≠0) : b.Moves W sc fun i => (X i)⁻¹ := Can.inv h k
variable (h : b.Moves W (c cl) X) (g : b.Moves W (c cl) Y)
include h g
lemma add : b.Moves W (c cl) fun i => X i+Y i := Can.add h g
lemma sub : b.Moves W (c cl) fun i => X i-Y i := Can.sub h g
end Moves
namespace Nick
variable {x y : ι→ℕ}
lemma wc (n : ℕ) : b.Nick fun _ => n := ⟨Can.wc n, Small.const _ n⟩
lemma congr (h : b.Nick x) (g : ∀ i, x i=y i) : b.Nick y := by cases funext g; exact h
lemma transfer {f} {x : κ→ℕ} (h : q.Nick x) (g : b.Instant q f) : b.Nick fun i => x (f i) :=
  ⟨Moves.transfer h.close g, (h.small.reindex f).trans g.covers⟩
lemma digit (h : b.Nick x) : b.Digit x := ⟨⟨0, h.close.ease _⟩, h.small⟩
variable (h : b.Nick x) (g : b.Nick y)
include h g
lemma add : b.Nick fun i => x i+y i := let hs := h.small.add g.small; ⟨Can.wadd h.close g.close hs, hs⟩
lemma sub : b.Nick fun i => x i-y i := ⟨Can.wsub h.close g.close h.small.sub, h.small.sub⟩
lemma mul : b.Nick fun i => x i*y i := let hs := h.small.mul g.small; ⟨Can.wmul h.close g.close hs, hs⟩
lemma div : b.Nick fun i => x i/y i := ⟨Can.wdiv h.close g.close h.small.div, h.small.div⟩
lemma residue : b.Nick fun i => x i%y i := ⟨Can.wmod h.close g.close h.small.mod, h.small.mod⟩
end Nick
lemma envNow (b : Bench m ι) : b.Moves W b.tray b.env := Can.id
lemma cherry (b : Bench m ι) (x : ι→T t) : (b.extend t x).Moves W t x := Can.second
lemma caseM {v : ι→T s} (h : b.Moves W t x) (g : (b.extend t x).Moves W s v) : b.Moves W s v := Can.bind h g
namespace Instant
variable {f : ι→κ}
lemma next (h : b.Instant q f) {p : κ→μ} (g : q.Instant z p) : b.Instant z fun i => p (f i) :=
  ⟨Moves.transfer g.prep h, (g.covers.reindex f).trans h.covers⟩
lemma extend (b : Bench m ι) (x : ι→T t) : (b.extend t x).Instant b id := ⟨Can.first, Small.self _⟩
lemma along (b : Bench m ι) (f : κ→ι) : (b.along f).Instant b f := ⟨Can.id, Small.self _⟩
lemma scan (b : Bench m ι) (n : ι→ℕ) : (b.scan n).Instant b During.i := ⟨Can.first, Small.self _⟩
lemma climbs (b : Bench m ι) (n : ι→ℕ) (x : ι → ℕ → T t) : (b.climbs n t x).Instant b During.i := ⟨Can.first, Small.self _⟩
lemma supply (h : b.Instant q f) (x : κ→T t) (hx : b.Moves (fun _ => 0) t (fun i => x (f i))) : b.Instant (q.extend t x) f :=
  ⟨Can.pair h.prep hx, h.covers⟩
lemma select {n : κ→ℕ} {f : ι→During n} (h : b.Instant q (fun i => (f i).i)) (g : b.Moves (fun _ => 0) w (fun i => (f i).j)) : b.Instant (q.scan n) f :=
  ⟨Can.pair h.prep g, h.covers⟩
end Instant
lemma chop {n : ι→ℕ} (h : b.Nick n) : (b.scan n).Nick During.j := ⟨Can.second, h.small.during⟩
lemma stride {n : ι→ℕ} (h : b.Nick n) (x : ι → ℕ → T t) : (b.climbs n t x).Nick During.j :=
  ⟨Can.fst Can.second, h.small.during⟩
lemma tokenNow (b : Bench m ι) (n : ι→ℕ) (x : ι → ℕ → T t) : (b.climbs n t x).Moves (fun _ => 0) t (fun i => x i.i i.j) :=
  Can.snd Can.second
variable {n : ι→ℕ} {u : ι → ℕ → ℕ} (h : b.Nick n)
include h
lemma arrayM (f : ι→ℕ→T t) (hs : (b.scan n).Moves (fun d => u d.i d.j) t (fun d => f d.i d.j)) : b.Moves (fun i => n i + ∑ j ∈ range (n i), u i j) (a t) (fun i => Tape.tab (n i) (f i)) :=
  Can.mono (Can.tab (uB := u) h.close hs h.small) fun _ => by simp
lemma arrayNow (f : ι→ℕ→T t) (hs : (b.scan n).Moves (fun _ => 0) t (fun d => f d.i d.j)) : b.Moves n (a t) (fun i => Tape.tab (n i) (f i)) :=
  Can.mono (Can.tab (uB := fun _ _ => 0) h.close hs h.small) fun _ => by simp
lemma scatterNow (f : ι → ℕ → ℕ × T t) (hs : (b.scan n).Moves (fun _ => 0) (p w t) (fun d => f d.i d.j)) : b.Moves n (a t) (fun i => Tape.sow (n i) (n i) t.blank (f i)) :=
  Can.weaken (Can.sow (uB := fun _ _ => 0) h.close h.close hs h.small h.small) ⟨3, fun i => by simp; omega⟩
lemma repeatM (f : ι → ℕ → T t) (hb : b.Moves (fun _ => 0) t fun i => f i 0) (hh : (b.climbs n t f).Moves (fun d => u d.i d.j) t fun d => f d.i (d.j+1)) : b.Moves (fun i => n i+∑ j ∈ range (n i), u i j) t fun i => f i (n i) :=
  Can.mono (Can.loop (uB := u) h.close hb hh h.small) fun _ => by simp
lemma inspectz (hg : (b.along (Subtype.val (p:=fun i => n i = 0))).Moves (fun i => W i.val) t (fun i => x i.val)) (hj : (b.along (Subtype.val (p:=fun i => n i ≠ 0))).Moves (fun i => W i.val) t (fun i => x i.val)) : b.Moves W t x :=
  Can.testz (Moves.ease h.close W) hg hj
end
section
variable {m : Bool} {ι : Type U} {b : Bench m ι} {n k : ι→ℕ} (h : b.Nick n)
include h
lemma Nick.cmp (g : b.Nick k) : b.Nick fun i => if n i < k i then 1 else 0 :=
  ⟨Can.wlt h.close g.close, (Small.const _ 1).mono fun _ => by split <;> omega⟩
lemma Nick.logM : b.Moves n w fun i => Nat.log 2 (n i) := Can.logC (h.close.ease n) h.small (Dom.self n)
lemma Nick.numeralM : b.Moves n sc fun i => (n i:ℂ) :=
  Can.mono (repeatM (u := fun _ _ => 0) h (fun _ j => (j : T sc)) (Can.zero.cy fun _ => Nat.cast_zero.symm)
    ((Can.add (tokenNow (t := sc) b n fun _ j => (j : ℂ)) Can.one).cy fun _ => (Nat.cast_succ _).symm)) fun _ => by simp
end
section
variable {m : Bool} {ι : Type U} {κ : Type V} {b : Bench m ι} {q : Bench m κ} {s t : Ty}
def Dry (b : Bench m ι) (S : ι→ℕ) (t : Ty) (f : ι→T t) : Prop :=
  PolyCan m b.size S b.tray t b.env f
structure Grain (b : Bench m ι) (S f : ι→ℕ) : Prop where
  dry : b.Dry S w f
  small : Small b.size f
variable {S : ι→ℕ}
lemma Moves.dry {W x} (h : b.Moves W t x) (g : Small S W) : b.Dry S t x := PolyCan.of_can h g
lemma Moves.dunes {x} (h : b.Moves (fun _ => 0) t x) (S : ι→ℕ) : b.Dry S t x := ⟨0, h.ease _⟩
lemma Nick.grain {x} (h : b.Nick x) (S : ι→ℕ) : b.Grain S x := ⟨h.close.dunes S, h.small⟩
lemma Moves.branch {n : ι→ℕ} {W : ι→ℕ} {x y : ι→T t}
    (h : b.Moves W w n) (g : b.Moves W t x) (j : b.Moves W t y) :
    b.Moves W t fun i => if n i=0 then x i else y i :=
  Can.testz h ((Can.reindex g (Subtype.val : {i // n i = 0} → ι)).cy fun i => (if_pos i.2).symm)
    ((Can.reindex j (Subtype.val : {i // n i ≠ 0} → ι)).cy fun i => (if_neg i.2).symm)
namespace Dry
variable {x y : ι→T t}
lemma congr (h : b.Dry S t x) (g : ∀ i, x i=y i) : b.Dry S t y := PolyCan.cong h (fun _ => rfl) g
lemma pair {v : ι→T s} (h : b.Dry S t x) (g : b.Dry S s v) : b.Dry S (p t s) fun i => (x i,v i) := PolyCan.pair h g
lemma fst {v : ι→T (p s t)} (h : b.Dry S (p s t) v) : b.Dry S s fun i => (v i).1 := PolyCan.fst h
lemma snd {v : ι→T (p s t)} (h : b.Dry S (p s t) v) : b.Dry S t fun i => (v i).2 := PolyCan.snd h
lemma wc (n : ℕ) : b.Dry S w fun _ => n := PolyCan.wc n
lemma one : b.Dry S sc fun _ => 1 := PolyCan.one
lemma mul {cl} {x y : ι→ℂ} (h : b.Dry S sc x) (g : b.Dry S (c cl) y) : b.Dry S (c cl) fun i => x i*y i := PolyCan.mul h g
lemma transfer {f : ι→κ} {S : κ→ℕ} {x : κ→T t} (h : q.Dry S t x) (g : b.Instant q f) : b.Dry (fun i => S (f i)) t fun i => x (f i) :=
  PolyCan.pipe (g.prep.dunes _) (PolyCan.weaken (PolyCan.reindex h f) g.covers (Small.self _))
lemma look {x : ι→Tape (T t)} {n} (h : b.Dry S (a t) x) (g : b.Dry S w n) : b.Dry S t fun i => (x i).look (n i) t.blank := PolyCan.look h g
lemma branch {f} (h : b.Dry S w f) (g : b.Dry S t x) (j : b.Dry S t y) : b.Dry S t fun i => if f i = 0 then x i else y i :=
  PolyCan.lift2 h (PolyCan.pair g j) fun u v => Moves.branch u (Can.fst v) (Can.snd v)
lemma pick {x : ι→ℕ→T t} {n k : ι→ℕ} (h : b.Dry S (a t) fun i => Tape.tab (n i) (x i)) (g : b.Dry S w k) (hk : ∀ i,k i<n i) : b.Dry S t fun i => x i (k i) :=
  PolyCan.lift2 h g (Moves.pick x · · hk)
end Dry
namespace Grain
variable {x y : ι→ℕ}
lemma wc (n : ℕ) : b.Grain S fun _ => n := ⟨Dry.wc n, Small.const _ n⟩
lemma congr (h : b.Grain S x) (g : ∀ i,x i=y i) : b.Grain S y := by cases funext g; exact h
lemma transfer {f : ι→κ} {S x : κ→ℕ} (h : q.Grain S x) (g : b.Instant q f) : b.Grain (fun i => S (f i)) fun i => x (f i) :=
  ⟨Dry.transfer h.dry g, (h.small.reindex f).trans g.covers⟩
lemma lin {F : ι → ℕ} (h : b.Grain S x) (g : Small S x) (G : ∀ W, b.Moves W w x → Dom W x → b.Moves W w F)
    (hF : Small b.size F) : b.Grain S F := by
  obtain ⟨d, hd⟩ := h.dry; obtain ⟨e, he⟩ := g
  exact ⟨⟨d+e, G _ (PolyCan.up hd (Nat.le_add_right _ _))
    (Dom.of_le fun i => (he i).trans (Small.pow_mono_degree _ (Nat.le_add_left _ _)))⟩, hF⟩
lemma logtwo (h : b.Grain S x) (g : Small S x) : b.Grain S fun i => Nat.log 2 (x i) :=
  h.lin g (fun _ a => Can.logC a h.small) (h.small.mono fun _ => Nat.log_le_self _ _)
variable (h : b.Grain S x) (g : b.Grain S y)
include h g
lemma add : b.Grain S fun i => x i+y i := let hs := h.small.add g.small; ⟨PolyCan.wadd h.dry g.dry hs, hs⟩
lemma mul : b.Grain S fun i => x i*y i := let hs := h.small.mul g.small; ⟨PolyCan.wmul h.dry g.dry hs, hs⟩
lemma div : b.Grain S fun i => x i/y i := ⟨PolyCan.wdiv h.dry g.dry h.small.div, h.small.div⟩
lemma residue : b.Grain S fun i => x i%y i := ⟨PolyCan.wmod h.dry g.dry h.small.mod, h.small.mod⟩
lemma cmp : b.Grain S fun i => if x i<y i then 1 else 0 :=
  ⟨PolyCan.wlt h.dry g.dry, (Small.const _ 1).mono fun _ => by split <;> omega⟩
end Grain
lemma Dry.token (b : Bench m ι) (n S : ι→ℕ) (x : ι → ℕ → T t) : (b.climbs n t x).Dry (fun i => S i.i) t fun i => x i.i i.j :=
  PolyCan.snd PolyCan.second
variable {n : ι→ℕ} (h : b.Grain S n)
include h
lemma strideG (x : ι → ℕ → T t) : (b.climbs n t x).Grain (fun i => S i.i) During.j := ⟨PolyCan.fst PolyCan.second, h.small.during⟩
lemma chopG : (b.scan n).Grain (fun i => S i.i) During.j := ⟨PolyCan.second, h.small.during⟩
variable (k : Small S n)
include k
lemma cycleG (x : ι → ℕ → T t) (g : b.Dry S t fun i => x i 0) (j : (b.climbs n t x).Dry (fun i => S i.i) t fun i => x i.i (i.j+1)) : b.Dry S t fun i => x i (n i) :=
  PolyCan.loop h.dry g j h.small k
lemma arrayG (x : ι→ℕ→T t) (g : (b.scan n).Dry (fun i => S i.i) t fun i => x i.i i.j) : b.Dry S (a t) fun i => Tape.tab (n i) (x i) :=
  PolyCan.tab h.dry g h.small k
lemma Grain.twoPow (j : Small b.size fun i => 2^n i) : b.Grain S fun i => 2^n i :=
  h.lin k (fun _ a => Can.wTwo a h.small j) j
end
end Bench
end
end RAM
end OAI.PowerSaving
