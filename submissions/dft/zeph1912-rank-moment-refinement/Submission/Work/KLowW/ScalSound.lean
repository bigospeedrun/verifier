import Submission.Work.KLowW.Route
import Submission.Work.KLowW.ScalK

/-!
# (key: p-warpchk) Soundness of the free-warp-algebra replay

The rows mean data: a key `s + N c` is `matAct (KC c) (x (un s))`, `KC c` the product of the letters `K a` of the
word coded by `c` (`KC (enc a + B c) = K a * KC c`); a row `[(k, z), ..]` is `∑ z / D • key`; `vecR R x` gives every
role `j` the row of its register `emb j`.

* `RT.get`, `RT.wf`, `RT.getK_eq`, `RT.get_set`, `RT.wf_set`, `RT.beqK_sound`: the row trie;
* `KC_wcode`          a letter acting on a word code is `K a *` (the free group: `K a * K (-a) = 1` cancels);
* `rowV_insK`, `rowV_mergeK`, `scaleK_sound`, `rowV_warpK`: the kernel row operations are linear algebra;
* `evS_sound`         one event of the replay is the effect `eMap` of the event on the evaluated rows;
* **`scalW_sound`**   `scalW q o evs R R' = true → esMap o K un evs (vecR R x) = vecR R' x`, for EVERY group-like `K`;
* `vecR_id`           identity start rows evaluate to the data itself;
* `vecR_free`         warp-free end rows evaluate to a pointwise scalar map `actPoint (rowsMat ..)`.

No `sorry`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace KLW
open SSC GXD GLab OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.GF OAI.PowerSaving.RAM
  OAI.PowerSaving.CB Finset Matrix

/-! ## the row trie -/

def RT.get : RT → Nat → Row
  | .leaf v, _ => v
  | .node l r, k => if k % 2 = 0 then l.get (k / 2) else r.get (k / 2)

def RT.wf : Nat → RT → Prop
  | 0, .leaf _ => True
  | d + 1, .node l r => RT.wf d l ∧ RT.wf d r
  | _, _ => False

theorem RT.getK_leaf (v : Row) (key : Nat) (k : Row → Bool) :
    (RT.leaf v).getK key k = if key = 0 then k v else false := by
  cases key <;> rfl

theorem RT.getK_node (l r : RT) (key : Nat) (k : Row → Bool) :
    (RT.node l r).getK key k = if key % 2 = 0 then l.getK (key / 2) k else r.getK (key / 2) k := by
  have h1 : Nat.shiftRight key 1 = key / 2 := Nat.shiftRight_one key
  have h2 : Nat.land key 1 = key % 2 := Nat.and_one_is_mod key
  show Bool.rec (motive := fun _ => Bool) (r.getK (Nat.shiftRight key 1) k)
    (l.getK (Nat.shiftRight key 1) k) (Nat.beq (Nat.land key 1) 0) = _
  rw [h1, h2]
  rcases Nat.mod_two_eq_zero_or_one key with h | h <;> rw [h] <;> rfl

theorem RT.set_leaf (v : Row) (key : Nat) (x : Row) : (RT.leaf v).set key x = .leaf x := rfl

theorem RT.set_node (l r : RT) (key : Nat) (x : Row) :
    (RT.node l r).set key x =
      if key % 2 = 0 then .node (l.set (key / 2) x) r else .node l (r.set (key / 2) x) := by
  have h1 : Nat.shiftRight key 1 = key / 2 := Nat.shiftRight_one key
  have h2 : Nat.land key 1 = key % 2 := Nat.and_one_is_mod key
  show Bool.rec (motive := fun _ => RT) (.node l (r.set (Nat.shiftRight key 1) x))
    (.node (l.set (Nat.shiftRight key 1) x) r) (Nat.beq (Nat.land key 1) 0) = _
  rw [h1, h2]
  rcases Nat.mod_two_eq_zero_or_one key with h | h <;> rw [h] <;> rfl

theorem RT.getK_eq (d : Nat) (t : RT) (hwf : t.wf d) (key : Nat) (k : Row → Bool) :
    t.getK key k = (decide (key < 2 ^ d) && k (t.get key)) := by
  induction d generalizing t key with
  | zero =>
    cases t with
    | leaf v =>
      rw [RT.getK_leaf]
      by_cases h : key = 0
      · subst h; simp [RT.get]
      · have h' : ¬ key < 2 ^ 0 := by simpa using h
        simp [h, h']
    | node l r => exact False.elim hwf
  | succ d ih =>
    cases t with
    | leaf v => exact False.elim hwf
    | node l r =>
      obtain ⟨hl, hr⟩ := hwf
      rw [RT.getK_node]
      have hlt : (key / 2 < 2 ^ d) ↔ (key < 2 ^ (d + 1)) := by rw [pow_succ]; omega
      by_cases h : key % 2 = 0
      · rw [if_pos h, ih l hl]; simp [RT.get, h, hlt]
      · rw [if_neg h, ih r hr]; simp [RT.get, h, hlt]

theorem RT.getK_true {d : Nat} {t : RT} (hwf : t.wf d) {key : Nat} {k : Row → Bool}
    (H : t.getK key k = true) : key < 2 ^ d ∧ k (t.get key) = true := by
  rw [RT.getK_eq d t hwf] at H
  obtain ⟨a, b⟩ := Bool.and_eq_true_iff.mp H
  exact ⟨of_decide_eq_true a, b⟩

theorem RT.wf_set (d : Nat) (t : RT) (hwf : t.wf d) (key : Nat) (x : Row) : (t.set key x).wf d := by
  induction d generalizing t key with
  | zero =>
    cases t with
    | leaf v => exact trivial
    | node l r => exact False.elim hwf
  | succ d ih =>
    cases t with
    | leaf v => exact False.elim hwf
    | node l r =>
      obtain ⟨hl, hr⟩ := hwf
      rw [RT.set_node]
      by_cases h : key % 2 = 0
      · rw [if_pos h]; exact ⟨ih l hl _, hr⟩
      · rw [if_neg h]; exact ⟨hl, ih r hr _⟩

theorem RT.get_set (d : Nat) (t : RT) (hwf : t.wf d) (key key' : Nat) (x : Row) (hk : key < 2 ^ d)
    (hk' : key' < 2 ^ d) : (t.set key x).get key' = if key' = key then x else t.get key' := by
  induction d generalizing t key key' with
  | zero =>
    cases t with
    | leaf v =>
      have h1 : key = 0 := by simpa using hk
      have h2 : key' = 0 := by simpa using hk'
      subst h1; subst h2; rfl
    | node l r => exact False.elim hwf
  | succ d ih =>
    cases t with
    | leaf v => exact False.elim hwf
    | node l r =>
      obtain ⟨hl, hr⟩ := hwf
      have hk2 : key / 2 < 2 ^ d := by rw [pow_succ] at hk; omega
      have hk2' : key' / 2 < 2 ^ d := by rw [pow_succ] at hk'; omega
      rw [RT.set_node]
      by_cases h : key % 2 = 0 <;> by_cases h' : key' % 2 = 0
      · rw [if_pos h]
        simp only [RT.get, h', ↓reduceIte]
        rw [ih l hl _ _ hk2 hk2']
        have e : (key' / 2 = key / 2) ↔ (key' = key) := by omega
        simp only [e]
      · rw [if_pos h]
        simp only [RT.get, h', ↓reduceIte]
        have e : key' ≠ key := by omega
        rw [if_neg e]
      · rw [if_neg h]
        simp only [RT.get, h', ↓reduceIte]
        have e : key' ≠ key := by omega
        rw [if_neg e]
      · rw [if_neg h]
        simp only [RT.get, h', ↓reduceIte]
        rw [ih r hr _ _ hk2 hk2']
        have e : (key' / 2 = key / 2) ↔ (key' = key) := by omega
        simp only [e]

theorem RT.wfK_sound : ∀ (t : RT) (d : Nat), RT.wfK t d = true → t.wf d := by
  intro t
  induction t with
  | leaf v =>
    intro d H
    have : d = 0 := beq_true H
    subst this; exact trivial
  | node l r il ir =>
    intro d H
    cases d with
    | zero => exact absurd H Bool.false_ne_true
    | succ m =>
      obtain ⟨a, b⟩ := guard_true H
      exact ⟨il m a, ir m b⟩

theorem izero_sound (z : Int) (h : izero z = true) : z = 0 := by
  cases z with
  | ofNat n =>
    have : n = 0 := beq_true h
    subst this; rfl
  | negSucc n => exact absurd h Bool.false_ne_true

theorem rowEq_sound : ∀ (a b : Row), rowEq a b = true → a = b := by
  intro a
  induction a with
  | nil =>
    intro b H
    cases b with
    | nil => rfl
    | cons y ys => exact absurd H Bool.false_ne_true
  | cons x xs ih =>
    intro b H
    cases b with
    | nil => exact absurd H Bool.false_ne_true
    | cons y ys =>
      obtain ⟨g1, H⟩ := guard_true H
      obtain ⟨g2, g3⟩ := guard_true H
      have e1 : x.1 = y.1 := beq_true g1
      have e2 : x.2 = y.2 := by have := izero_sound _ g2; omega
      rw [ih ys g3, show x = y from Prod.ext e1 e2]

theorem RT.beqK_sound : ∀ (t t' : RT), RT.beqK t t' = true → t = t' := by
  intro t
  induction t with
  | leaf v =>
    intro t' H
    cases t' with
    | leaf v' => rw [rowEq_sound v v' H]
    | node l r => exact absurd H Bool.false_ne_true
  | node l r il ir =>
    intro t' H
    cases t' with
    | leaf v => exact absurd H Bool.false_ne_true
    | node l' r' =>
      obtain ⟨a, b⟩ := guard_true H
      rw [il l' a, ir r' b]

/-! ## word codes -/

/-- the letter of a digit (inverse of `encI`) -/
def decI (m : Nat) : Int := if m % 2 = 0 then ((m / 2 : Nat) : Int) else Int.negSucc (m / 2)

theorem decI_encI (a : Int) : decI (encI a) = a := by
  cases a with
  | ofNat n =>
    show decI (2 * n) = Int.ofNat n
    unfold decI
    rw [if_pos (by omega), show 2 * n / 2 = n by omega]
    rfl
  | negSucc n =>
    show decI (2 * n + 1) = Int.negSucc n
    unfold decI
    rw [if_neg (by omega), show (2 * n + 1) / 2 = n by omega]

theorem encN_eq (a : Int) : encN a = encI (-a) := by
  cases a with
  | ofNat n =>
    cases n with
    | zero => rfl
    | succ m =>
      show 2 * (m + 1) - 1 = encI (Int.negSucc m)
      show 2 * (m + 1) - 1 = 2 * m + 1
      omega
  | negSucc n =>
    show 2 * n + 2 = encI (Int.ofNat (n + 1))
    show 2 * n + 2 = 2 * (n + 1)
    omega

theorem encI_pos (a : Int) (ha : a ≠ 0) : 1 ≤ encI a := by
  cases a with
  | ofNat n =>
    have hn : n ≠ 0 := fun e => ha (by rw [e]; rfl)
    show 1 ≤ 2 * n
    omega
  | negSucc n => show 1 ≤ 2 * n + 1; omega

theorem encN_pos (a : Int) (ha : a ≠ 0) : 1 ≤ encN a := by
  rw [encN_eq]; exact encI_pos _ (neg_ne_zero.mpr ha)

section KC
variable {α : Type} [Fintype α] [DecidableEq α]

/-- the product of the letters of the word with code `c` -/
noncomputable def KC (K : Int → CMat α) (B : Nat) (c : Nat) : CMat α :=
  if h : c = 0 ∨ B < 2 then 1 else K (decI (c % B)) * KC K B (c / B)
termination_by c
decreasing_by
  have h' : c ≠ 0 ∧ 2 ≤ B := by omega
  exact Nat.div_lt_self (Nat.pos_of_ne_zero h'.1) (by omega)

theorem KC_eq (K : Int → CMat α) (B c : Nat) :
    KC K B c = if h : c = 0 ∨ B < 2 then 1 else K (decI (c % B)) * KC K B (c / B) := by
  rw [KC]

theorem KC_zero (K : Int → CMat α) (B : Nat) : KC K B 0 = 1 := by
  rw [KC_eq, dif_pos (Or.inl rfl)]

theorem KC_push (K : Int → CMat α) (B : Nat) (hB : 2 ≤ B) (a : Int) (ha : a ≠ 0) (hlt : encI a < B) (c : Nat) :
    KC K B (encI a + B * c) = K a * KC K B c := by
  have hp := encI_pos a ha
  rw [KC_eq, dif_neg (by omega)]
  have e1 : (encI a + B * c) % B = encI a := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  have e2 : (encI a + B * c) / B = c := by
    rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hlt, Nat.zero_add]
  rw [e1, e2, decI_encI]

theorem KC_pop (K : Int → CMat α) (B : Nat) (hB : 2 ≤ B) (a : Int) (ha : a ≠ 0) (c : Nat)
    (hc : c % B = encN a) (hK : K a * K (-a) = 1) : KC K B (c / B) = K a * KC K B c := by
  have hp := encN_pos a ha
  have hc0 : c ≠ 0 := by
    intro e; subst e; rw [Nat.zero_mod] at hc; omega
  rw [KC_eq K B c, dif_neg (by omega), hc, encN_eq, decI_encI, ← Matrix.mul_assoc, hK, Matrix.one_mul]

/-- **a letter acting on a word code** -/
theorem KC_wcode (K : Int → CMat α) (B : Nat) (hB : 2 ≤ B) (a : Int) (ha : a ≠ 0) (hlt : encI a < B)
    (hK : K a * K (-a) = 1) (c : Nat) : KC K B (wcode B a c) = K a * KC K B c := by
  unfold wcode
  cases h : Nat.beq (c % B) (encN a) with
  | false => exact KC_push K B hB a ha hlt c
  | true => exact KC_pop K B hB a ha c (beq_true h) hK

theorem wkey_div (N B : Nat) (hN : 1 ≤ N) (a : Int) (k : Nat) : wkey N B a k / N = wcode B a (k / N) := by
  unfold wkey
  rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (Nat.mod_lt _ (by omega)), Nat.zero_add]

theorem wkey_mod (N B : Nat) (hN : 1 ≤ N) (a : Int) (k : Nat) : wkey N B a k % N = k % N := by
  unfold wkey
  rw [Nat.add_mul_mod_self_left, Nat.mod_mod]

end KC

/-! ## rows as data -/

section Rows
variable {α ρ : Type} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

theorem matAct_add' (f : ℕ) (M : CMat α) (u v : Sky α f → ℂ) :
    matAct f M (u + v) = matAct f M u + matAct f M v := by
  unfold matAct; exact Matrix.mulVec_add _ _ _

theorem matAct_smul' (f : ℕ) (M : CMat α) (c : ℂ) (u : Sky α f → ℂ) :
    matAct f M (c • u) = c • matAct f M u := by
  unfold matAct; exact Matrix.mulVec_smul _ _ _

theorem matAct_zero'' (f : ℕ) (M : CMat α) : matAct f M (0 : Sky α f → ℂ) = 0 := by
  unfold matAct; exact Matrix.mulVec_zero _

/-- the data of a key -/
noncomputable def keyV (q : SPw) (K : Int → CMat α) (un : Nat → ρ) {f : ℕ} (x : Data α ρ f) (k : Nat) :
    Sky α f → ℂ :=
  matAct f (KC K q.B (k / q.N)) (x (un (k % q.N)))

/-- the data of a row -/
noncomputable def rowV (q : SPw) (K : Int → CMat α) (un : Nat → ρ) {f : ℕ} (x : Data α ρ f) : Row → Sky α f → ℂ
  | [] => 0
  | e :: L => ((e.2 : ℂ) / (q.D : ℂ)) • keyV q K un x e.1 + rowV q K un x L

/-- the data of the rows of all roles -/
noncomputable def vecR (q : SPw) (K : Int → CMat α) (un : Nat → ρ) (emb : ρ → Nat) (R : RT) {f : ℕ}
    (x : Data α ρ f) : Data α ρ f :=
  fun j => rowV q K un x (R.get (emb j))

variable (q : SPw) (K : Int → CMat α) (un : Nat → ρ) {f : ℕ} (x : Data α ρ f)

theorem insK_nil (k : Nat) (c : Int) : insK k c [] = [(k, c)] := rfl

theorem insK_cons (k : Nat) (c : Int) (e : Nat × Int) (L : Row) :
    insK k c (e :: L) = if Nat.blt k e.1 = true then (k, c) :: e :: L else
      if Nat.beq k e.1 = true then (if izero (c + e.2) = true then L else (k, c + e.2) :: L) else e :: insK k c L := by
  show Bool.rec (motive := fun _ => Row)
      (Bool.rec (motive := fun _ => Row) (e :: insK k c L)
        (Bool.rec (motive := fun _ => Row) ((k, c + e.2) :: L) L (izero (c + e.2))) (Nat.beq k e.1))
      ((k, c) :: e :: L) (Nat.blt k e.1) = _
  cases Nat.blt k e.1 <;> cases Nat.beq k e.1 <;> cases izero (c + e.2) <;> rfl

theorem rowV_insK (k : Nat) (c : Int) (L : Row) :
    rowV q K un x (insK k c L) = ((c : ℂ) / (q.D : ℂ)) • keyV q K un x k + rowV q K un x L := by
  induction L with
  | nil => rw [insK_nil]; simp [rowV]
  | cons e L ih =>
    rw [insK_cons]
    split
    · rfl
    · split
      · rename_i _ hq
        have hk : k = e.1 := beq_true hq
        split
        · rename_i hz
          have hz' : c + e.2 = 0 := izero_sound _ hz
          have hc : (c : ℂ) = -(e.2 : ℂ) := by
            have : c = -e.2 := by omega
            rw [this]; push_cast; ring
          simp only [rowV]
          rw [hk, hc, neg_div, neg_smul]
          abel
        · simp only [rowV]
          rw [hk]
          push_cast
          rw [add_div, add_smul]
          abel
      · simp only [rowV]
        rw [ih]
        abel

theorem rowV_mergeK : ∀ (a b : Row), rowV q K un x (mergeK a b) = rowV q K un x a + rowV q K un x b := by
  intro a
  induction a with
  | nil => intro b; show rowV q K un x b = 0 + _; rw [zero_add]
  | cons y ys ih =>
    intro b
    induction b with
    | nil => show rowV q K un x (y :: ys) = _ + 0; rw [add_zero]
    | cons z zs ihz =>
      show rowV q K un x (Bool.rec (motive := fun _ => Row)
        (Bool.rec (motive := fun _ => Row) (z :: mergeK (y :: ys) zs)
          (Bool.rec (motive := fun _ => Row) ((y.1, y.2 + z.2) :: mergeK ys zs) (mergeK ys zs) (izero (y.2 + z.2)))
          (Nat.beq y.1 z.1))
        (y :: mergeK ys (z :: zs)) (Nat.blt y.1 z.1)) = _
      cases hb : Nat.blt y.1 z.1
      · cases hq : Nat.beq y.1 z.1
        · show rowV q K un x (z :: mergeK (y :: ys) zs) = _
          simp only [rowV] at ihz ⊢
          rw [ihz]
          abel
        · have hk : y.1 = z.1 := beq_true hq
          cases hz : izero (y.2 + z.2)
          · show rowV q K un x ((y.1, y.2 + z.2) :: mergeK ys zs) = _
            simp only [rowV]
            rw [ih zs, ← hk]
            push_cast
            rw [add_div, add_smul]
            abel
          · show rowV q K un x (mergeK ys zs) = _
            have hz' : y.2 + z.2 = 0 := izero_sound _ hz
            have hc : (y.2 : ℂ) = -(z.2 : ℂ) := by
              have : y.2 = -z.2 := by omega
              rw [this]; push_cast; ring
            simp only [rowV]
            rw [ih zs, ← hk, hc, neg_div, neg_smul]
            abel
      · show rowV q K un x (y :: mergeK ys (z :: zs)) = _
        simp only [rowV]
        rw [ih (z :: zs)]
        simp only [rowV]
        abel

theorem sgnI_eq (ng : Bool) (z : Int) : sgnI ng z = if ng then -z else z := by
  cases ng <;> rfl

theorem ediv_cast (z : Int) (num den : Nat) (hden : den ≠ 0) (h : izero (Int.emod (z * (num : Int)) (den : Int)) = true) :
    ((Int.ediv (z * (num : Int)) (den : Int) : Int) : ℚ) = (z : ℚ) * (num : ℚ) / (den : ℚ) := by
  have hm : Int.emod (z * (num : Int)) (den : Int) = 0 := izero_sound _ h
  have hd : (den : Int) ∣ z * (num : Int) := Int.dvd_of_emod_eq_zero hm
  have e := Int.ediv_mul_cancel hd
  have hden' : (den : ℚ) ≠ 0 := by exact_mod_cast hden
  rw [eq_div_iff hden']
  have e' : (((z * (num : Int)) / (den : Int) * (den : Int) : Int) : ℚ) = ((z * (num : Int) : Int) : ℚ) := by
    rw [e]
  push_cast at e'
  exact e'

/-- the value `± num / den` -/
def sgnQ (ng : Bool) (num den : Nat) : ℚ := (if ng then -(num : ℚ) else (num : ℚ)) / (den : ℚ)

theorem scaleK_sound (ng : Bool) (num den : Nat) (hden : den ≠ 0) :
    ∀ (row : Row) (k : Row → Bool), scaleK ng num den row k = true →
    ∃ row', k row' = true ∧ ∀ {f : ℕ} (x : Data α ρ f),
      rowV q K un x row' = ((sgnQ ng num den : ℚ) : ℂ) • rowV q K un x row := by
  intro row
  induction row with
  | nil => intro k H; exact ⟨[], H, fun x => by simp [rowV]⟩
  | cons e L ih =>
    intro k H
    obtain ⟨g1, g2⟩ := guard_true H
    obtain ⟨r, hr, hv⟩ := ih _ g2
    refine ⟨_, hr, fun x => ?_⟩
    simp only [rowV]
    rw [hv x, smul_add, ← smul_assoc]
    congr 1
    congr 1
    rw [sgnI_eq, smul_eq_mul]
    have hc := ediv_cast e.2 num den hden g1
    unfold sgnQ
    cases ng
    · simp only [Bool.false_eq_true, if_false]
      have : ((Int.ediv (e.2 * (num : Int)) (den : Int) : Int) : ℂ)
          = (((Int.ediv (e.2 * (num : Int)) (den : Int) : Int) : ℚ) : ℂ) := by push_cast; rfl
      rw [this, hc]
      push_cast
      ring
    · simp only [if_true]
      have : ((-(Int.ediv (e.2 * (num : Int)) (den : Int)) : Int) : ℂ)
          = -(((Int.ediv (e.2 * (num : Int)) (den : Int) : Int) : ℚ) : ℂ) := by push_cast; rfl
      rw [this, hc]
      push_cast
      ring

theorem warpK_cons (N B : Nat) (a : Int) (e : Nat × Int) (L : Row) :
    warpK N B a (e :: L) = insK (wkey N B a e.1) e.2 (warpK N B a L) := rfl

theorem rowV_warpK (hN : 1 ≤ q.N) (hB : 2 ≤ q.B) (a : Int) (ha : a ≠ 0) (hlt : encI a < q.B)
    (hK : K a * K (-a) = 1) : ∀ row : Row,
    rowV q K un x (warpK q.N q.B a row) = matAct f (K a) (rowV q K un x row) := by
  intro row
  induction row with
  | nil => show (0 : Sky α f → ℂ) = _; rw [show rowV q K un x [] = 0 from rfl, matAct_zero'']
  | cons e L ih =>
    rw [warpK_cons, rowV_insK, ih]
    simp only [rowV]
    rw [matAct_add', matAct_smul']
    congr 2
    unfold keyV
    rw [wkey_div q.N q.B hN, wkey_mod q.N q.B hN, KC_wcode K q.B hB a ha hlt hK, matAct_mul]

end Rows

/-! ## the events -/

/-- the numbering of the roles for the scalar replay -/
structure SCtx (q : SPw) {ρ : Type} (emb : ρ → Nat) (un : Nat → ρ) : Prop where
  hun : ∀ j, un (emb j) = j
  hin : ∀ r, r < q.nr → emb (un r) = r
  hlt : ∀ j, emb j < q.nr

section Ev
variable {α ρ : Type} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
variable {q : SPw} {K : Int → CMat α} {emb : ρ → Nat} {un : Nat → ρ}

theorem vecR_set (hq : SCtx q emb un) (hd : q.nr ≤ 2 ^ q.d) {R : RT} (hR : R.wf q.d) {t : Nat} (ht : t < q.nr)
    (row : Row) {f : ℕ} (x : Data α ρ f) (j : ρ) :
    vecR q K un emb (R.set t row) x j = if j = un t then rowV q K un x row else vecR q K un emb R x j := by
  unfold vecR
  rw [RT.get_set q.d R hR t (emb j) row (by omega) (by have := hq.hlt j; omega)]
  by_cases hj : j = un t
  · rw [if_pos (by rw [hj, hq.hin t ht]), if_pos hj]
  · have : emb j ≠ t := fun e => hj (by rw [← e, hq.hun])
    rw [if_neg this, if_neg hj]

theorem vecR_get (hq : SCtx q emb un) {R : RT} {t : Nat} (ht : t < q.nr) {f : ℕ} (x : Data α ρ f) :
    vecR q K un emb R x (un t) = rowV q K un x (R.get t) := by
  unfold vecR; rw [hq.hin t ht]

/-- one add `t += c s` of the replay is the add gate on the evaluated rows -/
theorem addS_sound (hq : SCtx q emb un) (hd : q.nr ≤ 2 ^ q.d) (t s : Nat) (co : Co) (R : RT) (hR : R.wf q.d)
    (k : RT → Bool) (H : addS q t s co R k = true) :
    ∃ R1, k R1 = true ∧ R1.wf q.d ∧ ∀ {f : ℕ} (x : Data α ρ f),
      point f (actPoint (addMat (un t) (un s) (cfC co).val)) (vecR q K un emb R x) = vecR q K un emb R1 x := by
  obtain ⟨g1, H⟩ := guard_true H
  obtain ⟨g2, H⟩ := guard_true H
  obtain ⟨g3, H⟩ := guard_true H
  obtain ⟨g4, H⟩ := guard_true H
  have ht : t < q.nr := ble_true g1
  have hs : s < q.nr := ble_true g2
  have hts : t ≠ s := by
    intro e; subst e
    have : Nat.beq t t = true := Nat.beq_refl t
    rw [this] at g3; exact absurd g3 (by decide)
  have hden : co.den ≠ 0 := by
    intro e
    rw [e] at g4; exact absurd g4 (by decide)
  obtain ⟨_, H⟩ := RT.getK_true hR H
  obtain ⟨_, H⟩ := RT.getK_true hR H
  obtain ⟨rs', hk, hv⟩ := scaleK_sound q K un co.neg co.num co.den hden _ _ H
  refine ⟨_, hk, RT.wf_set q.d R hR t _, fun x => ?_⟩
  funext j i
  show actPoint (addMat (un t) (un s) (cfC co).val) (fun r => vecR q K un emb R x r i) j = _
  rw [SSC.actPoint_addMat, vecR_set hq hd hR ht]
  have hne : un t ≠ un s := fun e => hts (by rw [← hq.hin t ht, e, hq.hin s hs])
  by_cases hj : j = un t
  · rw [if_pos hj, if_pos hj, rowV_mergeK, hv x, vecR_get hq ht, vecR_get hq hs]
    show rowV q K un x (R.get t) i + _ = rowV q K un x (R.get t) i + (((sgnQ co.neg co.num co.den : ℚ) : ℂ) • rowV q K un x (R.get s)) i
    rfl
  · rw [if_neg hj, if_neg hj]

/-- the micro adds of a list of adds in orientation `o` -/
def gmL (o : Bool) (l : List (Nat × Nat × Co)) : List Micro := if o then (mic cfC l).map swapNeg else mic cfC l

theorem addsS_sound (hq : SCtx q emb un) (hd : q.nr ≤ 2 ^ q.d) (o : Bool) :
    ∀ (l : List (Nat × Nat × Co)) (R : RT), R.wf q.d → ∀ (k : RT → Bool), addsS q o l R k = true →
    ∃ R1, k R1 = true ∧ R1.wf q.d ∧ ∀ {f : ℕ} (x : Data α ρ f),
      point f (actPoint (matP un (gmL o l))) (vecR q K un emb R x) = vecR q K un emb R1 x := by
  intro l
  induction l with
  | nil =>
    intro R hR k H
    refine ⟨R, H, hR, fun x => ?_⟩
    have e : matP un (gmL o []) = (1 : Matrix ρ ρ ℚ) := by cases o <;> rfl
    rw [e, actPoint_one']; rfl
  | cons y l ih =>
    intro R hR k H
    cases o with
    | false =>
      have H' : addS q y.1 y.2.1 y.2.2 R (fun R1 => addsS q false l R1 k) = true := H
      obtain ⟨R1, h1, w1, v1⟩ := addS_sound hq hd (K := K) y.1 y.2.1 y.2.2 R hR _ H'
      obtain ⟨R2, h2, w2, v2⟩ := ih R1 w1 k h1
      refine ⟨R2, h2, w2, fun x => ?_⟩
      have e : matP un (gmL false (y :: l)) = matP un (gmL false l) * addMat (un y.1) (un y.2.1) (cfC y.2.2).val := rfl
      rw [e, actPoint_mul, ← v2 x, ← v1 x]
      rfl
    | true =>
      have H' : addS q y.2.1 y.1 ⟨!y.2.2.neg, y.2.2.num, y.2.2.den⟩ R (fun R1 => addsS q true l R1 k) = true := H
      obtain ⟨R1, h1, w1, v1⟩ := addS_sound hq hd (K := K) y.2.1 y.1 ⟨!y.2.2.neg, y.2.2.num, y.2.2.den⟩ R hR _ H'
      obtain ⟨R2, h2, w2, v2⟩ := ih R1 w1 k h1
      refine ⟨R2, h2, w2, fun x => ?_⟩
      have e : matP un (gmL true (y :: l))
          = matP un (gmL true l) * addMat (un y.2.1) (un y.1) (cfC ⟨!y.2.2.neg, y.2.2.num, y.2.2.den⟩).val := rfl
      rw [e, actPoint_mul, ← v2 x, ← v1 x]
      rfl

theorem actPoint_scD (r : ρ) (c : ℚ) (u : ρ → ℂ) (j : ρ) :
    actPoint (scD r c) u j = (if j = r then (c : ℂ) else 1) * u j := by
  unfold actPoint scD
  rw [Finset.sum_eq_single j (fun b _ hb => by rw [Matrix.diagonal_apply_ne _ (Ne.symm hb)]; simp)
    (fun hj => absurd (Finset.mem_univ j) hj)]
  rw [Matrix.diagonal_apply_eq]
  split <;> simp

theorem sgnQ_inv (co : Co) (hn : co.num ≠ 0) (hd : co.den ≠ 0) :
    sgnQ co.neg co.den co.num = (coQ co)⁻¹ := by
  unfold sgnQ coQ cfC Coef.val
  have hn' : (co.num : ℚ) ≠ 0 := by exact_mod_cast hn
  have hd' : (co.den : ℚ) ≠ 0 := by exact_mod_cast hd
  cases co.neg
  · simp only [Bool.false_eq_true, if_false]
    field_simp
  · simp only [if_true]
    field_simp

/-- **one event of the replay is the effect of the event on the evaluated rows** -/
theorem evS_sound (hq : SCtx q emb un) (hd : q.nr ≤ 2 ^ q.d) (hN : 1 ≤ q.N) (hB : 2 ≤ q.B)
    (hK : ∀ a, K a * K (-a) = 1) (o : Bool) (e : WEv) (R : RT) (hR : R.wf q.d) (k : RT → Bool)
    (H : evS q o e R k = true) :
    ∃ R1, k R1 = true ∧ R1.wf q.d ∧ ∀ {f : ℕ} (x : Data α ρ f),
      eMap o K un e f (vecR q K un emb R x) = vecR q K un emb R1 x := by
  cases e with
  | g g =>
    obtain ⟨R1, h1, w1, v1⟩ := addsS_sound (K := K) hq hd o g.adds R hR k H
    exact ⟨R1, h1, w1, fun x => v1 x⟩
  | sc f0 r co =>
    obtain ⟨g1, H⟩ := guard_true H
    obtain ⟨g2, H⟩ := guard_true H
    obtain ⟨g3, H⟩ := guard_true H
    have hr : r < q.nr := ble_true g1
    have hn : co.num ≠ 0 := by intro e; rw [e] at g2; exact absurd g2 (by decide)
    have hden : co.den ≠ 0 := by intro e; rw [e] at g3; exact absurd g3 (by decide)
    obtain ⟨_, H⟩ := RT.getK_true hR H
    have key : ∀ (c : ℚ) (row' : Row), (∀ {f : ℕ} (x : Data α ρ f),
        rowV q K un x row' = (c : ℂ) • rowV q K un x (R.get r)) →
        ∀ {f : ℕ} (x : Data α ρ f), point f (actPoint (scD (un r) c)) (vecR q K un emb R x)
          = vecR q K un emb (R.set r row') x := by
      intro c row' hv f x
      funext j i
      show actPoint (scD (un r) c) (fun r' => vecR q K un emb R x r' i) j = _
      rw [actPoint_scD, vecR_set hq hd hR hr]
      by_cases hj : j = un r
      · rw [if_pos hj, if_pos hj, hv x, hj, vecR_get hq hr]; rfl
      · rw [if_neg hj, if_neg hj, one_mul]
    cases o with
    | false =>
      obtain ⟨row', hk, hv⟩ := scaleK_sound q K un co.neg co.num co.den hden _ _ H
      exact ⟨_, hk, RT.wf_set q.d R hR r _, fun x => key _ row' (fun x => hv x) x⟩
    | true =>
      obtain ⟨row', hk, hv⟩ := scaleK_sound q K un co.neg co.den co.num hn _ _ H
      refine ⟨_, hk, RT.wf_set q.d R hR r _, fun x => ?_⟩
      have := key (coQ co)⁻¹ row' (fun x => by rw [hv x, sgnQ_inv co hn hden]) x
      exact this
  | w r a f0 f1 =>
    obtain ⟨g1, H⟩ := guard_true H
    obtain ⟨g2, H⟩ := guard_true H
    obtain ⟨g3, H⟩ := guard_true H
    obtain ⟨g4, H⟩ := guard_true H
    have hr : r < q.nr := ble_true g1
    have ha : a ≠ 0 := opNe0_sound a g2
    have hlt : encI a < q.B := ble_true g3
    obtain ⟨_, H⟩ := RT.getK_true hR H
    refine ⟨_, H, RT.wf_set q.d R hR r _, fun {f} x => ?_⟩
    funext j
    show roleAct f (un r) (K a) (vecR q K un emb R x) j = _
    rw [vecR_set hq hd hR hr]
    by_cases hj : j = un r
    · rw [if_pos hj]
      simp only [roleAct, if_pos hj]
      rw [rowV_warpK q K un x hN hB a ha hlt (hK a), hj, vecR_get hq hr]
    · rw [if_neg hj]
      simp only [roleAct, if_neg hj]
  | za r f0 =>
    obtain ⟨g1, H⟩ := guard_true H
    have hr : r < q.nr := ble_true g1
    obtain ⟨_, H⟩ := RT.getK_true hR H
    refine ⟨_, H, RT.wf_set q.d R hR r _, fun x => ?_⟩
    funext j i
    show actPoint (scD (un r) 0) (fun r' => vecR q K un emb R x r' i) j = _
    rw [actPoint_scD, vecR_set hq hd hR hr]
    by_cases hj : j = un r
    · rw [if_pos hj, if_pos hj]; simp [rowV]
    · rw [if_neg hj, if_neg hj, one_mul]
  | zf r =>
    obtain ⟨g1, H⟩ := guard_true H
    have hr : r < q.nr := ble_true g1
    obtain ⟨_, H⟩ := RT.getK_true hR H
    refine ⟨_, H, RT.wf_set q.d R hR r _, fun x => ?_⟩
    funext j i
    show actPoint (scD (un r) 0) (fun r' => vecR q K un emb R x r' i) j = _
    rw [actPoint_scD, vecR_set hq hd hR hr]
    by_cases hj : j = un r
    · rw [if_pos hj, if_pos hj]; simp [rowV]
    · rw [if_neg hj, if_neg hj, one_mul]
  | dn r f0 => exact ⟨R, H, hR, fun x => rfl⟩

theorem evsS_sound (hq : SCtx q emb un) (hd : q.nr ≤ 2 ^ q.d) (hN : 1 ≤ q.N) (hB : 2 ≤ q.B)
    (hK : ∀ a, K a * K (-a) = 1) (o : Bool) :
    ∀ (evs : List WEv) (R : RT), R.wf q.d → ∀ (k : RT → Bool), evsS q o evs R k = true →
    ∃ R1, k R1 = true ∧ R1.wf q.d ∧ ∀ {f : ℕ} (x : Data α ρ f),
      esMap o K un evs f (vecR q K un emb R x) = vecR q K un emb R1 x := by
  intro evs
  induction evs with
  | nil => intro R hR k H; exact ⟨R, H, hR, fun x => rfl⟩
  | cons e es ih =>
    intro R hR k H
    obtain ⟨R1, h1, w1, v1⟩ := evS_sound hq hd hN hB hK o e R hR _ H
    obtain ⟨R2, h2, w2, v2⟩ := ih R1 w1 k h1
    refine ⟨R2, h2, w2, fun {f} x => ?_⟩
    show esMap o K un es f (eMap o K un e f (vecR q K un emb R x)) = _
    rw [v1 x, v2 x]

/-- **soundness of the free-warp-algebra replay**: for every group-like interpretation `K` of the letters, the
effect of the events on the evaluated start rows is the evaluated end rows -/
theorem scalW_sound (hq : SCtx q emb un) (hK : ∀ a, K a * K (-a) = 1) {o : Bool} {evs : List WEv} {R R' : RT}
    (H : scalW q o evs R R' = true) :
    R.wf q.d ∧ q.nr ≤ q.N ∧ 1 ≤ q.D ∧ ∀ {f : ℕ} (x : Data α ρ f),
      esMap o K un evs f (vecR q K un emb R x) = vecR q K un emb R' x := by
  unfold scalW at H
  obtain ⟨g0, H⟩ := guard_true H
  obtain ⟨g1, H⟩ := guard_true H
  obtain ⟨g2, H⟩ := guard_true H
  obtain ⟨g3, H⟩ := guard_true H
  obtain ⟨g4, H⟩ := guard_true H
  obtain ⟨g5, H⟩ := guard_true H
  have hR := RT.wfK_sound R q.d g0
  have hd : q.nr ≤ 2 ^ q.d := by have := ble_true g3; simpa using this
  obtain ⟨R1, h1, _, v1⟩ := evsS_sound hq hd (ble_true g1) (ble_true g4) hK o evs R hR _ H
  have e := RT.beqK_sound _ _ h1
  subst e
  exact ⟨hR, ble_true g2, ble_true g5, fun x => v1 x⟩

/-- identity start rows evaluate to the data -/
theorem vecR_id (hq : SCtx q emb un) (hN : q.nr ≤ q.N) (hD : 1 ≤ q.D) {R : RT}
    (h0 : ∀ r, r < q.nr → R.get r = [(r, (q.D : Int))]) {f : ℕ} (x : Data α ρ f) :
    vecR q K un emb R x = x := by
  funext j
  unfold vecR
  have hj := hq.hlt j
  rw [h0 _ hj]
  simp only [rowV, add_zero]
  unfold keyV
  rw [Nat.div_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), KC_zero, matAct_one, hq.hun]
  have hD' : (q.D : ℂ) ≠ 0 := by exact_mod_cast (show q.D ≠ 0 by omega)
  show (((q.D : Int) : ℂ) / (q.D : ℂ)) • x j = x j
  rw [show (((q.D : Int) : ℂ)) = (q.D : ℂ) by push_cast; rfl, div_self hD', one_smul]

/-- the matrix of warp-free rows -/
noncomputable def rowsMat (q : SPw) (un : Nat → ρ) (emb : ρ → Nat) (R : RT) : Matrix ρ ρ ℚ :=
  fun j i => ((R.get (emb j)).map (fun e => if un e.1 = i then (e.2 : ℚ) / (q.D : ℚ) else 0)).sum

theorem rowV_free (hN : 1 ≤ q.N) {f : ℕ} (x : Data α ρ f) (s : Sky α f) :
    ∀ (row : Row), (∀ e ∈ row, e.1 < q.N) →
    rowV q K un x row s = ∑ i, ((((row.map (fun e => if un e.1 = i then (e.2 : ℚ) / (q.D : ℚ) else 0)).sum : ℚ)) : ℂ) * x i s := by
  intro row
  induction row with
  | nil => intro _; simp [rowV]
  | cons e L ih =>
    intro hL
    have he : e.1 < q.N := hL e List.mem_cons_self
    simp only [rowV, Pi.add_apply, Pi.smul_apply, smul_eq_mul, List.map_cons, List.sum_cons]
    rw [ih (fun e' h => hL e' (List.mem_cons_of_mem _ h))]
    unfold keyV
    rw [Nat.div_eq_of_lt he, Nat.mod_eq_of_lt he, KC_zero, matAct_one]
    push_cast
    simp only [add_mul, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single (un e.1) (fun b _ hb => by rw [if_neg (Ne.symm hb)]; simp)
      (fun h => absurd (Finset.mem_univ _) h)]
    rw [if_pos rfl]
    push_cast
    ring

/-- warp-free end rows evaluate to a pointwise scalar map -/
theorem vecR_free (hN : 1 ≤ q.N) {R : RT} (hfree : ∀ j, ∀ e ∈ R.get (emb j), e.1 < q.N) {f : ℕ}
    (x : Data α ρ f) : vecR q K un emb R x = point f (actPoint (rowsMat q un emb R)) x := by
  funext j s
  show rowV q K un x (R.get (emb j)) s = actPoint (rowsMat q un emb R) (fun r => x r s) j
  rw [rowV_free hN x s _ (hfree j)]
  rfl

end Ev
end KLW

#print axioms KLW.scalW_sound
#print axioms KLW.vecR_id
#print axioms KLW.vecR_free
#print axioms KLW.KC_wcode
