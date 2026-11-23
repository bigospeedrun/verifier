import Submission.Cert.Label.Trie

namespace ScalarCheck.Spec
open WarpCheck CertData

def coef : Row → Nat → Int
  | [], _ => 0
  | e :: l, k => (if e.1 = k then e.2 else 0) + coef l k

/-- the row of register `k` in a trie; keys beyond the trie depth read as the empty row (reading the leaf
there, as `WarpCheck.RT.get` does, would alias lower registers and make `RefOk` false for this word;
`WarpCheck.ScalarBridge.get_eq` shows the two agree below `2 ^ d` on well-formed tries). -/
def get : RT → Nat → Row
  | .leaf v, k => if k = 0 then v else []
  | .node l r, k => if k % 2 = 0 then get l (k / 2) else get r (k / 2)

def wf : Nat → RT → Prop
  | 0, .leaf _ => True
  | d + 1, .node l r => wf d l ∧ wf d r
  | _, _ => False

abbrev St := Nat → Nat → Int
def St.of (R : RT) : St := fun r k => coef (get R r) k

def sg (co : Co) : Int := if co.neg then -(co.num : Int) else (co.num : Int)

def AddStep (q : SPw) (t s : Nat) (co : Co) (S S' : St) : Prop :=
  t < q.nr ∧ s < q.nr ∧ t ≠ s ∧ co.den ≠ 0 ∧
  (∀ k, (co.den : Int) * (S' t k - S t k) = sg co * S s k) ∧
  (∀ r, r ≠ t → S' r = S r)

inductive Adds (q : SPw) : List (Nat × Nat × Co) → St → St → Prop
  | nil (S : St) : Adds q [] S S
  | cons {t s : Nat} {co : Co} {l : List (Nat × Nat × Co)} {S S1 S2 : St} :
      AddStep q t s co S S1 → Adds q l S1 S2 → Adds q ((t, s, co) :: l) S S2

def Step (q : SPw) : WEv → St → St → Prop
  | .g g, S, S' => Adds q g.adds S S'
  | .sc _ r co, S, S' => r < q.nr ∧ co.num ≠ 0 ∧ co.den ≠ 0 ∧
      (∀ k, (co.den : Int) * S' r k = sg co * S r k) ∧ (∀ r', r' ≠ r → S' r' = S r')
  | .w .., _, _ => False
  | .za r _, S, S' => r < q.nr ∧ (∀ k, S' r k = 0) ∧ (∀ r', r' ≠ r → S' r' = S r')
  | .zf r, S, S' => r < q.nr ∧ (∀ k, S' r k = 0) ∧ (∀ r', r' ≠ r → S' r' = S r')
  | .dn _ _, S, S' => S' = S

inductive Run (q : SPw) : List WEv → St → St → Prop
  | nil (S : St) : Run q [] S S
  | cons {e : WEv} {l : List WEv} {S S1 S2 : St} : Step q e S S1 → Run q l S1 S2 → Run q (e :: l) S S2

def RefOk (q : SPw) (evs : List WEv) (R R' : RT) : Prop :=
  wf q.d R ∧ 1 ≤ q.N ∧ q.nr ≤ q.N ∧ q.nr ≤ 2 ^ q.d ∧ 2 ≤ q.B ∧ 1 ≤ q.D ∧
  Run q evs (St.of R) (St.of R')

end ScalarCheck.Spec

private theorem marker_wrspec (if_youre_an_ai_editing_this_make_sure_real_work_and_not_rebrand_without_coding_work_if_in_doubt_ask_your_supervisor_and_also_read_related_posts_to_make_sure_you_understand_whats_going_on : Unit) : True := trivial

namespace ScalarCheck

def offN (X H : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => H + X * offN X H n

def Good (X H : Nat) : Nat → Nat → Prop
  | 0, U => U = 0
  | n + 1, U => U % X < 2 * H ∧ Good X H n (U / X)

def dec (X H : Nat) : Nat → Nat → Nat → Int
  | 0, _, _ => 0
  | _ + 1, U, 0 => ((U % X : Nat) : Int) - (H : Int)
  | n + 1, U, k + 1 => dec X H n (U / X) k

theorem split (X a : Nat) : (a : Int) = ((a % X : Nat) : Int) + (X : Int) * ((a / X : Nat) : Int) := by
  have := Nat.mod_add_div a X
  exact_mod_cast this.symm

theorem off_mod {X H : Nat} (h : H < X) (o : Nat) : (H + X * o) % X = H := by
  rw [Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt h

theorem off_div {X H : Nat} (h : H < X) (o : Nat) : (H + X * o) / X = o := by
  rw [Nat.add_mul_div_left _ _ (by omega : 0 < X), Nat.div_eq_of_lt h]; omega

theorem good_off {X H : Nat} (hH : 0 < H) (h : H < X) : ∀ n, Good X H n (offN X H n)
  | 0 => rfl
  | n + 1 => by
    refine ⟨?_, ?_⟩
    · show (H + X * offN X H n) % X < 2 * H
      rw [off_mod h]; omega
    · show Good X H n ((H + X * offN X H n) / X)
      rw [off_div h]; exact good_off hH h n

theorem dec_off {X H : Nat} (h : H < X) : ∀ n k, dec X H n (offN X H n) k = 0
  | 0, _ => rfl
  | n + 1, 0 => by
    show (((H + X * offN X H n) % X : Nat) : Int) - (H : Int) = 0
    rw [off_mod h]; omega
  | n + 1, k + 1 => by
    show dec X H n ((H + X * offN X H n) / X) k = 0
    rw [off_div h]; exact dec_off h n k

theorem small_zero {X : Nat} {L M : Int} (h : L = (X : Int) * M) (hb : L.natAbs < X) : L = 0 :=
  Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (d := (X : Int)) ⟨M, h⟩ (by simpa using hb)

theorem step_core {X H Kd Kn : Nat} (hH : 0 < H) (hX : Kd * (2 * H) + Kd + Kn * H ≤ X) (den : Nat) (sg : Int)
    (ρ : Nat) (hden : den < Kd) (hsg : sg.natAbs < Kn) (hρ : ρ ≤ den) (a0 a1 b0 b1 c0 c1 o : Nat)
    (ha : a0 < 2 * H) (hb : b0 < 2 * H) (hc : c0 < 2 * H)
    (hyp : (den : Int) * (((c0 : Int) + (X : Int) * c1) - ((a0 : Int) + (X : Int) * a1)) + (ρ : Int)
      = sg * (((b0 : Int) + (X : Int) * b1) - ((H : Int) + (X : Int) * o))) :
    (den : Int) * ((c0 : Int) - a0) + (ρ : Int) = sg * ((b0 : Int) - H) ∧
    (den : Int) * ((c1 : Int) - a1) = sg * ((b1 : Int) - o) := by
  have hL : (den : Int) * ((c0 : Int) - a0) + (ρ : Int) - sg * ((b0 : Int) - H)
      = (X : Int) * (sg * ((b1 : Int) - o) - (den : Int) * ((c1 : Int) - a1)) := by grind
  have h1 : ((den : Int) * ((c0 : Int) - a0)).natAbs < Kd * (2 * H) := by
    rw [Int.natAbs_mul, Int.natAbs_natCast]
    exact Nat.mul_lt_mul_of_lt_of_le hden (by omega) (by omega)
  have h2 : (sg * ((b0 : Int) - H)).natAbs < Kn * H := by
    rw [Int.natAbs_mul]
    exact Nat.mul_lt_mul_of_lt_of_le hsg (by omega) hH
  have h3 := Int.natAbs_sub_le ((den : Int) * ((c0 : Int) - a0) + (ρ : Int)) (sg * ((b0 : Int) - H))
  have h4 := Int.natAbs_add_le ((den : Int) * ((c0 : Int) - a0)) (ρ : Int)
  have h5 : ((ρ : Int)).natAbs = ρ := Int.natAbs_natCast ρ
  have L0 := small_zero hL (by omega)
  rw [L0] at hL
  have hXpos : 0 < X := by
    have : 0 < Kd * (2 * H) := Nat.mul_pos (by omega) (by omega)
    omega
  have M0 : sg * ((b1 : Int) - o) - (den : Int) * ((c1 : Int) - a1) = 0 := by
    rcases Int.mul_eq_zero.mp hL.symm with h | h
    · omega
    · exact h
  constructor <;> omega

theorem lin_dec {X H Kd Kn : Nat} (hH : 0 < H) (hX : Kd * (2 * H) + Kd + Kn * H ≤ X) (den : Nat) (sg : Int)
    (hden : den < Kd) (hsg : sg.natAbs < Kn) :
    ∀ (n a b c : Nat), Good X H n a → Good X H n b → Good X H n c →
      (den : Int) * ((c : Int) - a) = sg * ((b : Int) - (offN X H n : Nat)) →
      ∀ k, (den : Int) * (dec X H n c k - dec X H n a k) = sg * dec X H n b k
  | 0, a, b, c, _, _, _, _, k => by simp [dec]
  | n + 1, a, b, c, ⟨ha0, ha1⟩, ⟨hb0, hb1⟩, ⟨hc0, hc1⟩, hyp, k => by
    have eo : ((offN X H (n + 1) : Nat) : Int) = (H : Int) + (X : Int) * ((offN X H n : Nat) : Int) := by
      show (((H + X * offN X H n : Nat)) : Int) = _
      push_cast; rfl
    rw [split X a, split X b, split X c, eo] at hyp
    obtain ⟨e0, e1⟩ := step_core hH hX den sg 0 hden hsg (Nat.zero_le _) _ _ _ _ _ _ _ ha0 hb0 hc0
      (by simp only [Int.natCast_zero, Int.add_zero]; exact hyp)
    have e0 : (den : Int) * (((c % X : Nat) : Int) - ((a % X : Nat) : Int)) = sg * (((b % X : Nat) : Int) - (H : Int)) := by
      simpa using e0
    cases k with
    | zero =>
      show (den : Int) * ((((c % X : Nat) : Int) - (H : Int)) - (((a % X : Nat) : Int) - (H : Int)))
        = sg * (((b % X : Nat) : Int) - (H : Int))
      rw [← e0]; congr 1; omega
    | succ k => exact lin_dec hH hX den sg hden hsg n _ _ _ ha1 hb1 hc1 e1 k

theorem lin_dec0 {X H Kd Kn : Nat} (hH : 0 < H) (hX : Kd * (2 * H) + Kd + Kn * H ≤ X) (den : Nat) (sg : Int)
    (ρ : Nat) (hden : den < Kd) (hsg : sg.natAbs < Kn) (hρ : ρ ≤ den) :
    ∀ (n a b c : Nat), Good X H n a → Good X H n b → Good X H n c →
      (den : Int) * ((c : Int) - a) + (ρ : Int) = sg * ((b : Int) - (offN X H n : Nat)) →
      ∀ k, (den : Int) * (dec X H n c (k + 1) - dec X H n a (k + 1)) = sg * dec X H n b (k + 1)
  | 0, a, b, c, _, _, _, _, k => by simp [dec]
  | n + 1, a, b, c, ⟨ha0, ha1⟩, ⟨hb0, hb1⟩, ⟨hc0, hc1⟩, hyp, k => by
    have eo : ((offN X H (n + 1) : Nat) : Int) = (H : Int) + (X : Int) * ((offN X H n : Nat) : Int) := by
      show (((H + X * offN X H n : Nat)) : Int) = _
      push_cast; rfl
    rw [split X a, split X b, split X c, eo] at hyp
    obtain ⟨_, e1⟩ := step_core hH hX den sg ρ hden hsg hρ _ _ _ _ _ _ _ ha0 hb0 hc0 hyp
    exact lin_dec hH hX den sg hden hsg n _ _ _ ha1 hb1 hc1 e1 k

theorem ins_dec {X H : Nat} (hX : 3 * H ≤ X) (z : Int) (hz : z.natAbs < H) :
    ∀ (n a c j : Nat), Good X H n a → Good X H n c →
      (c : Int) - a = z * ((X ^ j : Nat) : Int) →
      ∀ k, dec X H n c k = dec X H n a k + (if j = k then z else 0)
  | 0, a, c, j, ha, hc, hyp, k => by
    have ha' : a = 0 := ha
    have hc' : c = 0 := hc
    subst ha' hc'
    have hXj : 0 < X ^ j := Nat.pow_pos (by omega)
    have : z = 0 := by
      rcases Int.mul_eq_zero.mp hyp.symm with h | h
      · exact h
      · omega
    simp [dec, this]
  | n + 1, a, c, 0, ⟨ha0, ha1⟩, ⟨hc0, hc1⟩, hyp, k => by
    rw [split X a, split X c] at hyp
    have hM : z - (((c % X : Nat) : Int) - ((a % X : Nat) : Int))
        = (X : Int) * (((c / X : Nat) : Int) - ((a / X : Nat) : Int)) := by
      simp at hyp; grind
    have h3 := Int.natAbs_sub_le z (((c % X : Nat) : Int) - ((a % X : Nat) : Int))
    have M0 := small_zero hM (by omega)
    rw [M0] at hM
    have e1 : c / X = a / X := by
      rcases Int.mul_eq_zero.mp hM.symm with h | h
      · omega
      · omega
    cases k with
    | zero =>
      show (((c % X : Nat) : Int) - (H : Int)) = (((a % X : Nat) : Int) - (H : Int)) + (if 0 = 0 then z else 0)
      simp; omega
    | succ k =>
      show dec X H n (c / X) k = dec X H n (a / X) k + (if 0 = k + 1 then z else 0)
      rw [e1]; simp
  | n + 1, a, c, j + 1, ⟨ha0, ha1⟩, ⟨hc0, hc1⟩, hyp, k => by
    rw [split X a, split X c] at hyp
    have hp : ((X ^ (j + 1) : Nat) : Int) = (X : Int) * ((X ^ j : Nat) : Int) := by
      rw [Nat.pow_succ, Nat.mul_comm]; push_cast; rfl
    rw [hp] at hyp
    have hM : (((c % X : Nat) : Int) - ((a % X : Nat) : Int))
        = (X : Int) * (z * ((X ^ j : Nat) : Int) - (((c / X : Nat) : Int) - ((a / X : Nat) : Int))) := by
      grind
    have M0 := small_zero hM (by omega)
    rw [M0] at hM
    have e1 : ((c / X : Nat) : Int) - ((a / X : Nat) : Int) = z * ((X ^ j : Nat) : Int) := by
      rcases Int.mul_eq_zero.mp hM.symm with h | h
      · omega
      · omega
    have ih := ins_dec hX z hz n _ _ j ha1 hc1 e1
    cases k with
    | zero =>
      show (((c % X : Nat) : Int) - (H : Int)) = (((a % X : Nat) : Int) - (H : Int)) + (if j + 1 = 0 then z else 0)
      simp; omega
    | succ k =>
      show dec X H n (c / X) k = dec X H n (a / X) k + (if j + 1 = k + 1 then z else 0)
      rw [ih k]; simp

def maskN (w h : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (2 ^ w - 2 ^ h) + 2 ^ w * maskN w h n

theorem digit_small {w h d : Nat} (hh : h ≤ w) (hd : d < 2 ^ w) (hm : d &&& (2 ^ w - 2 ^ h) = 0) : d < 2 ^ h := by
  apply Nat.lt_of_not_ge
  intro hge
  obtain ⟨i, hi, hbit⟩ := Nat.exists_ge_and_testBit_of_ge_two_pow hge
  have hiw : i < w := by
    apply Nat.lt_of_not_ge
    intro hwi
    have : d < 2 ^ i := Nat.lt_of_lt_of_le hd (Nat.pow_le_pow_right (by omega) hwi)
    rw [Nat.testBit_lt_two_pow this] at hbit
    cases hbit
  have e : 2 ^ w - 2 ^ h = 2 ^ h * (2 ^ (w - h) - 1) := by
    rw [Nat.mul_sub, ← Nat.pow_add, Nat.mul_one]; congr 2; omega
  have hb2 : (2 ^ w - 2 ^ h).testBit i = true := by
    rw [e, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_sub_one]
    simp; omega
  have := Nat.testBit_and d (2 ^ w - 2 ^ h) i
  rw [hm, hbit, hb2] at this
  simp at this

theorem good_of_mask {w h H : Nat} (hh : h ≤ w) (hH : 2 * H = 2 ^ h) :
    ∀ (n U : Nat), U &&& maskN w h n = 0 → U < (2 ^ w) ^ n → Good (2 ^ w) H n U
  | 0, U, _, hU => by
    show U = 0
    simpa using hU
  | n + 1, U, hm, hU => by
    have hpos : 0 < 2 ^ w := Nat.pow_pos (by omega)
    have hlt : 2 ^ w - 2 ^ h < 2 ^ w := Nat.sub_lt hpos (Nat.pow_pos (by omega))
    have m0 : maskN w h (n + 1) % 2 ^ w = 2 ^ w - 2 ^ h := by
      show ((2 ^ w - 2 ^ h) + 2 ^ w * maskN w h n) % 2 ^ w = _
      rw [Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt hlt
    have m1 : maskN w h (n + 1) / 2 ^ w = maskN w h n := by
      show ((2 ^ w - 2 ^ h) + 2 ^ w * maskN w h n) / 2 ^ w = _
      rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hlt]; omega
    refine ⟨?_, ?_⟩
    · rw [hH]
      apply digit_small hh (Nat.mod_lt _ hpos)
      rw [← m0, ← Nat.and_mod_two_pow, hm]; rfl
    · apply good_of_mask hh hH n
      · rw [← m1, ← Nat.and_div_two_pow, hm]; simp
      · apply Nat.div_lt_of_lt_mul
        rw [Nat.pow_succ, Nat.mul_comm] at hU; exact hU

end ScalarCheck

private theorem marker_wrarith (if_youre_an_ai_editing_this_make_sure_real_work_and_not_rebrand_without_coding_work_if_in_doubt_ask_your_supervisor_and_also_read_related_posts_to_make_sure_you_understand_whats_going_on : Unit) : True := trivial

namespace ScalarCheck
open WarpCheck CertData ScalarCheck.Spec
set_option hygiene false in
local notation "orecP" => Option.rec (motive := fun _ => Option PT)
set_option hygiene false in
local notation "nrecP" => Nat.rec (motive := fun _ => Option PT)
set_option hygiene false in
local notation "brecN" => Bool.rec (motive := fun _ => Option Nat)
set_option hygiene false in
local notation "brecP" => Bool.rec (motive := fun _ => Option PT)

structure Cx where
  X : Nat
  H : Nat
  Kd : Nat
  Kn : Nat
  n : Nat
  OFF : Nat
  MASK : Nat
  XN : Nat

def goodB (c : Cx) (U : Nat) : Bool := Nat.beq (Nat.land U c.MASK) 0 && !(Nat.ble c.XN U)

structure Cx.OK (c : Cx) : Prop where
  hH : 0 < c.H
  hX : c.Kd * (2 * c.H) + c.Kd + c.Kn * c.H ≤ c.X
  hX3 : 3 * c.H ≤ c.X
  hOFF : c.OFF = offN c.X c.H c.n
  hgood : ∀ U, goodB c U = true → Good c.X c.H c.n U

theorem Cx.OK.h3 {c : Cx} (hc : c.OK) : 3 * c.H ≤ c.X := hc.hX3

theorem Cx.OK.hlt {c : Cx} (hc : c.OK) : c.H < c.X := by
  have := hc.h3; have := hc.hH; omega

def obind {α β : Type} (o : Option α) (f : α → Option β) : Option β :=
  match o with
  | none => none
  | some v => f v

def omap {α β : Type} (f : α → β) (o : Option α) : Option β :=
  match o with
  | none => none
  | some v => some (f v)

theorem obind_some {α β : Type} {o : Option α} {f : α → Option β} {x : β} (h : obind o f = some x) :
    ∃ v, o = some v ∧ f v = some x := by
  cases o with
  | none => cases h
  | some v => exact ⟨v, rfl, h⟩

theorem omap_some {α β : Type} {f : α → β} {o : Option α} {x : β} (h : omap f o = some x) :
    ∃ v, o = some v ∧ f v = x := by
  cases o with
  | none => cases h
  | some v => exact ⟨v, rfl, Option.some.inj h⟩

theorem guard_some {α : Type} {g : Bool} {A : Option α} {x : α} (h : (bif g then A else none) = some x) :
    g = true ∧ A = some x := by
  cases g with
  | false => cases h
  | true => exact ⟨rfl, h⟩

theorem brec_some {α : Type} {g : Bool} {A : Option α} {x : α}
    (h : Bool.rec (motive := fun _ => Option α) none A g = some x) : g = true ∧ A = some x := by
  cases g with
  | false => cases h
  | true => exact ⟨rfl, h⟩

theorem nbrec_some {α : Type} {g : Bool} {A : Option α} {x : α}
    (h : Bool.rec (motive := fun _ => Option α) A none g = some x) : g = false ∧ A = some x := by
  cases g with
  | true => cases h
  | false => exact ⟨rfl, h⟩

theorem orec_obind {α β : Type} (o : Option α) (f : α → Option β) :
    Option.rec (motive := fun _ => Option β) none f o = obind o f := by
  cases o <;> rfl

noncomputable def forceO {α : Type} (x : Nat) (k : Nat → Option α) : Option α :=
  Nat.rec (motive := fun _ => Option α) none (fun n _ => k n) (Nat.succ x)

theorem forceO_eq {α : Type} (x : Nat) (k : Nat → Option α) : forceO x k = k x := rfl

inductive PT where
  | leaf (u : Nat)
  | node (l r : PT)

theorem natrec_beq {α : Type} (a b : α) (n : Nat) :
    Nat.rec (motive := fun _ => α) a (fun _ _ => b) n = bif Nat.beq n 0 then a else b := by
  cases n <;> rfl

theorem optrec_omap {α β : Type} (f : α → β) (o : Option α) :
    Option.rec (motive := fun _ => Option β) none (fun x => some (f x)) o = omap f o := by
  cases o <;> rfl

noncomputable def getP (off : Nat) (T : PT) : Nat → Nat :=
  PT.rec (motive := fun _ => Nat → Nat)
    (fun u k => Nat.rec (motive := fun _ => Nat) u (fun _ _ => off) k)
    (fun _ _ gl gr k => Nat.rec (motive := fun _ => Nat) (gl (Nat.shiftRight k 1))
      (fun _ _ => gr (Nat.shiftRight k 1)) (Nat.land k 1)) T

theorem getP_leaf (off u k : Nat) : getP off (.leaf u) k = bif Nat.beq k 0 then u else off :=
  natrec_beq _ _ _
theorem getP_node (off : Nat) (l r : PT) (k : Nat) :
    getP off (.node l r) k = bif Nat.beq (k % 2) 0 then getP off l (k / 2) else getP off r (k / 2) := by
  show Nat.rec (motive := fun _ => Nat) (getP off l (Nat.shiftRight k 1))
    (fun _ _ => getP off r (Nat.shiftRight k 1)) (Nat.land k 1) = _
  rw [natrec_beq]
  have h1 : Nat.land k 1 = k % 2 := Nat.and_one_is_mod k
  have h2 : Nat.shiftRight k 1 = k / 2 := by
    show k >>> 1 = k / 2
    rw [Nat.shiftRight_eq_div_pow]
  rw [h1, h2]

noncomputable def setP (T : PT) : Nat → Nat → Option PT :=
  PT.rec (motive := fun _ => Nat → Nat → Option PT)
    (fun _ k v => nrecP (some (.leaf v)) (fun _ _ => none) k)
    (fun l r sl sr k v => nrecP
      (orecP none (fun l' => some (PT.node l' r)) (sl (Nat.shiftRight k 1) v))
      (fun _ _ => orecP none (fun r' => some (PT.node l r'))
        (sr (Nat.shiftRight k 1) v))
      (Nat.land k 1)) T

theorem setP_leaf (u k v : Nat) : setP (.leaf u) k v = bif Nat.beq k 0 then some (.leaf v) else none :=
  natrec_beq _ _ _
theorem setP_node (l r : PT) (k v : Nat) :
    setP (.node l r) k v = bif Nat.beq (k % 2) 0 then omap (fun l' => PT.node l' r) (setP l (k / 2) v)
      else omap (fun r' => PT.node l r') (setP r (k / 2) v) := by
  show nrecP
      (orecP none (fun l' => some (PT.node l' r)) (setP l (Nat.shiftRight k 1) v))
      (fun _ _ => orecP none (fun r' => some (PT.node l r'))
        (setP r (Nat.shiftRight k 1) v))
      (Nat.land k 1) = _
  rw [natrec_beq, optrec_omap, optrec_omap]
  have h1 : Nat.land k 1 = k % 2 := Nat.and_one_is_mod k
  have h2 : Nat.shiftRight k 1 = k / 2 := by
    show k >>> 1 = k / 2
    rw [Nat.shiftRight_eq_div_pow]
  rw [h1, h2]

noncomputable def modP (T : PT) : Nat → (Nat → Option Nat) → Option PT :=
  PT.rec (motive := fun _ => Nat → (Nat → Option Nat) → Option PT)
    (fun u k f => nrecP
      (orecP none (fun v => some (.leaf v)) (f u)) (fun _ _ => none) k)
    (fun l r ml mr k f => nrecP
      (orecP none (fun l' => some (PT.node l' r)) (ml (Nat.shiftRight k 1) f))
      (fun _ _ => orecP none (fun r' => some (PT.node l r'))
        (mr (Nat.shiftRight k 1) f))
      (Nat.land k 1)) T

theorem modP_eq (off : Nat) : ∀ (T : PT) (k : Nat) (f : Nat → Option Nat),
    modP T k f = obind (f (getP off T k)) (fun v => setP T k v)
  | .leaf u, k, f => by
    cases k with
    | zero =>
      show orecP none (fun v => some (.leaf v)) (f u)
        = obind (f u) (fun v => some (.leaf v))
      cases f u <;> rfl
    | succ k =>
      show (none : Option PT) = obind (f off) (fun _ => none)
      cases f off <;> rfl
  | .node l r, k, f => by
    have il := modP_eq off l (Nat.shiftRight k 1) f
    have ir := modP_eq off r (Nat.shiftRight k 1) f
    show nrecP
        (orecP none (fun l' => some (PT.node l' r)) (modP l (Nat.shiftRight k 1) f))
        (fun _ _ => orecP none (fun r' => some (PT.node l r'))
          (modP r (Nat.shiftRight k 1) f))
        (Nat.land k 1)
      = obind (f (Nat.rec (motive := fun _ => Nat) (getP off l (Nat.shiftRight k 1))
          (fun _ _ => getP off r (Nat.shiftRight k 1)) (Nat.land k 1)))
        (fun v => nrecP
          (orecP none (fun l' => some (PT.node l' r)) (setP l (Nat.shiftRight k 1) v))
          (fun _ _ => orecP none (fun r' => some (PT.node l r'))
            (setP r (Nat.shiftRight k 1) v))
          (Nat.land k 1))
    rw [il, ir]
    generalize Nat.land k 1 = b
    cases b with
    | zero =>
      show orecP none (fun l' => some (PT.node l' r))
          (obind (f (getP off l (Nat.shiftRight k 1))) (fun v => setP l (Nat.shiftRight k 1) v))
        = obind (f (getP off l (Nat.shiftRight k 1)))
          (fun v => orecP none (fun l' => some (PT.node l' r))
            (setP l (Nat.shiftRight k 1) v))
      cases f (getP off l (Nat.shiftRight k 1)) <;> rfl
    | succ b =>
      show orecP none (fun r' => some (PT.node l r'))
          (obind (f (getP off r (Nat.shiftRight k 1))) (fun v => setP r (Nat.shiftRight k 1) v))
        = obind (f (getP off r (Nat.shiftRight k 1)))
          (fun v => orecP none (fun r' => some (PT.node l r'))
            (setP r (Nat.shiftRight k 1) v))
      cases f (getP off r (Nat.shiftRight k 1)) <;> rfl

theorem get_set (off : Nat) : ∀ (T : PT) (r v : Nat) (T' : PT), setP T r v = some T' →
    ∀ r', getP off T' r' = if r' = r then v else getP off T r'
  | .leaf u, r, v, T', h, r' => by
    rw [setP_leaf] at h
    obtain ⟨hg, h⟩ := guard_some h
    have hr : r = 0 := Nat.eq_of_beq_eq_true hg
    cases h; subst hr
    rw [getP_leaf, getP_leaf]
    cases hb : Nat.beq r' 0 with
    | true => have := Nat.eq_of_beq_eq_true hb; simp [this]
    | false => have := Nat.ne_of_beq_eq_false hb; simp [this]
  | .node l rr, r, v, T', h, r' => by
    rw [setP_node] at h
    cases hb : Nat.beq (r % 2) 0 with
    | true =>
      rw [hb] at h
      obtain ⟨l', hl, rfl⟩ := omap_some h
      have ih := get_set off l (r / 2) v l' hl (r' / 2)
      have hr := Nat.eq_of_beq_eq_true hb
      rw [getP_node, getP_node]
      cases hb' : Nat.beq (r' % 2) 0 with
      | true =>
        have hr' := Nat.eq_of_beq_eq_true hb'
        simp only [Bool.cond_true]; rw [ih]
        by_cases e : r' = r
        · simp [e]
        · have : ¬ r' / 2 = r / 2 := by omega
          simp [e, this]
      | false =>
        have hr' := Nat.ne_of_beq_eq_false hb'
        have : ¬ r' = r := by omega
        simp [this]
    | false =>
      rw [hb] at h
      obtain ⟨l', hl, rfl⟩ := omap_some h
      have ih := get_set off rr (r / 2) v l' hl (r' / 2)
      have hr := Nat.ne_of_beq_eq_false hb
      rw [getP_node, getP_node]
      cases hb' : Nat.beq (r' % 2) 0 with
      | false =>
        have hr' := Nat.ne_of_beq_eq_false hb'
        simp only [Bool.cond_false]; rw [ih]
        by_cases e : r' = r
        · simp [e]
        · have : ¬ r' / 2 = r / 2 := by omega
          simp [e, this]
      | true =>
        have hr' := Nat.eq_of_beq_eq_true hb'
        have : ¬ r' = r := by omega
        simp [this]

noncomputable def mulS (m x : Nat) : Nat := Bool.rec (motive := fun _ => Nat) (Nat.mul m x) x (Nat.beq m 1)
noncomputable def divS (x m : Nat) : Nat := Bool.rec (motive := fun _ => Nat) (Nat.div x m) x (Nat.beq m 1)

theorem mulS_eq (m x : Nat) : mulS m x = m * x := by
  unfold mulS
  cases h : Nat.beq m 1 with
  | true => have := Nat.eq_of_beq_eq_true h; subst this; simp
  | false => rfl

theorem divS_eq (x m : Nat) : divS x m = x / m := by
  unfold divS
  cases h : Nat.beq m 1 with
  | true => have := Nat.eq_of_beq_eq_true h; subst this; simp
  | false => rfl

noncomputable def fin (c : Cx) (den s m : Nat) : Option Nat :=
  brecN none
    (forceO (divS (Nat.sub s m) den) fun cc =>
      brecN none
        (brecN (some cc) none (Nat.ble c.XN cc))
        (Nat.beq (Nat.land cc c.MASK) 0))
    (Nat.ble m s)

theorem fin_some {c : Cx} {den s m cc : Nat} (h : fin c den s m = some cc) :
    (∃ ρ : Nat, (den ≠ 0 → ρ ≤ den) ∧ den * cc + ρ + m = s) ∧ goodB c cc = true := by
  unfold fin at h
  obtain ⟨h1, h⟩ := brec_some h
  rw [forceO_eq] at h
  obtain ⟨h3a, h⟩ := brec_some h
  obtain ⟨h3b, h⟩ := nbrec_some h
  have h3 : goodB c (divS (Nat.sub s m) den) = true := by
    show (Nat.beq (Nat.land (divS (Nat.sub s m) den) c.MASK) 0 && !(Nat.ble c.XN (divS (Nat.sub s m) den))) = true
    rw [h3a, h3b]; rfl
  cases h
  have h1 : m ≤ s := Nat.le_of_ble_eq_true h1
  refine ⟨⟨(s - m) % den, fun hd => Nat.le_of_lt (Nat.mod_lt _ (Nat.pos_of_ne_zero hd)), ?_⟩, h3⟩
  show den * (divS (s - m) den) + (s - m) % den + m = s
  rw [divS_eq, Nat.div_add_mod]; omega

noncomputable def lin (c : Cx) (a b : Nat) (co : Co) : Option Nat :=
  brecN
    (brecN
      (brecN
        (brecN
          (fin c co.den (Nat.add (mulS co.den a) (mulS co.num b)) (mulS co.num c.OFF))
          (fin c co.den (Nat.add (mulS co.den a) (mulS co.num c.OFF)) (mulS co.num b))
          co.neg)
        none (Nat.ble c.Kn co.num))
      none (Nat.ble c.Kd co.den))
    none (Nat.beq co.den 0)

theorem natAbs_sg (co : Co) : (sg co).natAbs = co.num := by
  unfold sg; cases co.neg <;> simp

theorem lin_some {c : Cx} {a b cc : Nat} {co : Co} (h : lin c a b co = some cc) :
    co.den ≠ 0 ∧ co.den < c.Kd ∧ co.num < c.Kn ∧ goodB c cc = true ∧
    ∃ ρ : Nat, ρ ≤ co.den ∧ (co.den : Int) * ((cc : Int) - a) + (ρ : Int) = sg co * ((b : Int) - (c.OFF : Nat)) := by
  unfold lin at h
  obtain ⟨g1, h⟩ := nbrec_some h
  obtain ⟨g2, h⟩ := nbrec_some h
  obtain ⟨g3, h⟩ := nbrec_some h
  have g1 : co.den ≠ 0 := Nat.ne_of_beq_eq_false g1
  have g2 : co.den < c.Kd := Nat.lt_of_not_le (Nat.not_le_of_not_ble_eq_true (by simp [g2]))
  have g3 : co.num < c.Kn := Nat.lt_of_not_le (Nat.not_le_of_not_ble_eq_true (by simp [g3]))
  refine ⟨g1, g2, g3, ?_⟩
  cases hn : co.neg with
  | true =>
    rw [hn] at h
    obtain ⟨⟨ρ, hρ, e⟩, hgd⟩ := fin_some h
    refine ⟨hgd, ρ, hρ g1, ?_⟩
    simp only [mulS_eq, Nat.add_eq] at e
    have e' : (co.den : Int) * cc + (ρ : Int) + (co.num : Int) * b = (co.den : Int) * a + (co.num : Int) * c.OFF := by
      exact_mod_cast e
    have : sg co = -(co.num : Int) := by simp [sg, hn]
    rw [this]; grind
  | false =>
    rw [hn] at h
    obtain ⟨⟨ρ, hρ, e⟩, hgd⟩ := fin_some h
    refine ⟨hgd, ρ, hρ g1, ?_⟩
    simp only [mulS_eq, Nat.add_eq] at e
    have e' : (co.den : Int) * cc + (ρ : Int) + (co.num : Int) * c.OFF = (co.den : Int) * a + (co.num : Int) * b := by
      exact_mod_cast e
    have : sg co = (co.num : Int) := by simp [sg, hn]
    rw [this]; grind

noncomputable def addOne (c : Cx) (nr : Nat) (T : PT) (t s : Nat) (co : Co) : Option PT :=
  brecP none
    (brecP none
      (brecP
        (modP T t fun a => lin c a (getP c.OFF T s) co) none (Nat.beq t s))
      (Nat.ble (Nat.succ s) nr))
    (Nat.ble (Nat.succ t) nr)

noncomputable def addsP (c : Cx) (nr : Nat) (l : List (Nat × Nat × Co)) : PT → Option PT :=
  List.rec (motive := fun _ => PT → Option PT) (fun T => some T)
    (fun e _ ih T => obind (addOne c nr T e.1 e.2.1 e.2.2) ih) l

theorem addsP_nil (c : Cx) (nr : Nat) (T : PT) : addsP c nr [] T = some T := rfl
theorem addsP_cons (c : Cx) (nr : Nat) (e : Nat × Nat × Co) (l : List (Nat × Nat × Co)) (T : PT) :
    addsP c nr (e :: l) T = obind (addOne c nr T e.1 e.2.1 e.2.2) (addsP c nr l) := rfl

noncomputable def zeroP (c : Cx) (nr : Nat) (T : PT) (r : Nat) : Option PT :=
  brecP none (setP T r c.OFF) (Nat.ble (Nat.succ r) nr)

noncomputable def scP (c : Cx) (nr : Nat) (T : PT) (r : Nat) (co : Co) : Option PT :=
  brecP none
    (brecP (modP T r fun b => lin c c.OFF b co) none (Nat.beq co.num 0))
    (Nat.ble (Nat.succ r) nr)

noncomputable def outP (c : Cx) (nr s : Nat) (ts : List (Nat × Co)) : PT → Option PT :=
  List.rec (motive := fun _ => PT → Option PT) (fun T => some T)
    (fun p _ ih T => orecP none ih (addOne c nr T p.1 s p.2)) ts

noncomputable def innP (c : Cx) (nr t : Nat) (ss : List (Nat × Co)) : PT → Option PT :=
  List.rec (motive := fun _ => PT → Option PT) (fun T => some T)
    (fun p _ ih T => orecP none ih (addOne c nr T t p.1 p.2)) ss

theorem outP_eq (c : Cx) (nr s : Nat) : ∀ (ts : List (Nat × Co)) (T : PT),
    outP c nr s ts T = addsP c nr (ts.map fun p => (p.1, s, p.2)) T
  | [], _ => rfl
  | p :: ts, T => by
    show orecP none (outP c nr s ts) (addOne c nr T p.1 s p.2)
      = obind (addOne c nr T p.1 s p.2) (addsP c nr (ts.map fun p => (p.1, s, p.2)))
    rw [orec_obind, show outP c nr s ts = addsP c nr (ts.map fun p => (p.1, s, p.2)) from funext (outP_eq c nr s ts)]

theorem innP_eq (c : Cx) (nr t : Nat) : ∀ (ss : List (Nat × Co)) (T : PT),
    innP c nr t ss T = addsP c nr (ss.map fun p => (t, p.1, p.2)) T
  | [], _ => rfl
  | p :: ss, T => by
    show orecP none (innP c nr t ss) (addOne c nr T t p.1 p.2)
      = obind (addOne c nr T t p.1 p.2) (addsP c nr (ss.map fun p => (t, p.1, p.2)))
    rw [orec_obind, show innP c nr t ss = addsP c nr (ss.map fun p => (t, p.1, p.2)) from funext (innP_eq c nr t ss)]

noncomputable def gateP (c : Cx) (nr : Nat) (T : PT) (g : Gate) : Option PT :=
  Gate.rec (motive := fun _ => Option PT) (fun _ s ts _ => outP c nr s ts T) (fun _ t ss => innP c nr t ss T) g

theorem gateP_eq (c : Cx) (nr : Nat) (T : PT) (g : Gate) : gateP c nr T g = addsP c nr g.adds T := by
  cases g with
  | out f s ts x => exact outP_eq c nr s ts T
  | inn f t ss => exact innP_eq c nr t ss T

noncomputable def stepP (c : Cx) (nr : Nat) (e : WEv) (T : PT) : Option PT :=
  WEv.rec (motive := fun _ => Option PT) (fun g => gateP c nr T g) (fun _ r co => scP c nr T r co)
    (fun _ _ _ _ => none) (fun r _ => zeroP c nr T r) (fun r => zeroP c nr T r) (fun _ _ => some T) e

noncomputable def runP (c : Cx) (nr : Nat) (l : List WEv) : PT → Option PT :=
  List.rec (motive := fun _ => PT → Option PT) (fun T => some T)
    (fun e _ ih T => orecP none ih (stepP c nr e T)) l

theorem runP_nil (c : Cx) (nr : Nat) (T : PT) : runP c nr [] T = some T := rfl
theorem runP_cons (c : Cx) (nr : Nat) (e : WEv) (l : List WEv) (T : PT) :
    runP c nr (e :: l) T = obind (stepP c nr e T) (runP c nr l) :=
  orec_obind _ _

noncomputable def SP (c : Cx) (T : PT) : St := fun r k => dec c.X c.H c.n (getP c.OFF T r) (k + 1)

def Inv (c : Cx) (T : PT) : Prop := ∀ r, Good c.X c.H c.n (getP c.OFF T r)

theorem good_OFF {c : Cx} (hc : c.OK) : Good c.X c.H c.n c.OFF := by
  rw [hc.hOFF]; exact good_off hc.hH hc.hlt _

theorem dec_OFF {c : Cx} (hc : c.OK) (k : Nat) : dec c.X c.H c.n c.OFF k = 0 := by
  rw [hc.hOFF]; exact dec_off hc.hlt _ _

theorem set_sound {c : Cx} {T T' : PT} {r v : Nat} (h : setP T r v = some T') (hI : Inv c T)
    (hv : Good c.X c.H c.n v) :
    Inv c T' ∧ (∀ k, SP c T' r k = dec c.X c.H c.n v (k + 1)) ∧ (∀ r', r' ≠ r → SP c T' r' = SP c T r') := by
  have gs := get_set c.OFF T r v T' h
  refine ⟨?_, ?_, ?_⟩
  · intro r'
    rw [gs r']
    by_cases e : r' = r
    · simp [e, hv]
    · simp [e, hI r']
  · intro k
    show dec c.X c.H c.n (getP c.OFF T' r) (k + 1) = _
    rw [gs r]; simp
  · intro r' e
    funext k
    show dec c.X c.H c.n (getP c.OFF T' r') (k + 1) = dec c.X c.H c.n (getP c.OFF T r') (k + 1)
    rw [gs r']; simp [e]

theorem addOne_sound {c : Cx} (hc : c.OK) (q : SPw) {T T' : PT} {t s : Nat} {co : Co}
    (h : addOne c q.nr T t s co = some T') (hI : Inv c T) :
    AddStep q t s co (SP c T) (SP c T') ∧ Inv c T' := by
  unfold addOne at h
  obtain ⟨g1, h⟩ := brec_some h
  obtain ⟨g2, h⟩ := brec_some h
  obtain ⟨g3, h⟩ := nbrec_some h
  have g1 : t < q.nr := Nat.le_of_ble_eq_true g1
  have g2 : s < q.nr := Nat.le_of_ble_eq_true g2
  have g3 : t ≠ s := Nat.ne_of_beq_eq_false g3
  rw [modP_eq c.OFF] at h
  obtain ⟨v, hl, hs⟩ := obind_some h
  obtain ⟨d0, dK, nK, hgd, ρ, hρ, e⟩ := lin_some hl
  have hv := hc.hgood v hgd
  obtain ⟨hI', hr, ho⟩ := set_sound hs hI hv
  refine ⟨⟨g1, g2, g3, d0, ?_, ho⟩, hI'⟩
  intro k
  rw [hr k]
  rw [show ((c.OFF : Nat) : Int) = ((offN c.X c.H c.n : Nat) : Int) from by rw [← hc.hOFF]] at e
  exact lin_dec0 hc.hH hc.hX co.den (sg co) ρ dK (by rw [natAbs_sg]; exact nK) hρ c.n _ _ _ (hI t) (hI s) hv e k

theorem addsP_sound {c : Cx} (hc : c.OK) (q : SPw) : ∀ (l : List (Nat × Nat × Co)) (T T' : PT),
    addsP c q.nr l T = some T' → Inv c T → Adds q l (SP c T) (SP c T') ∧ Inv c T'
  | [], T, T', h, hI => by
    rw [addsP_nil] at h; cases h; exact ⟨Adds.nil _, hI⟩
  | (t, s, co) :: l, T, T', h, hI => by
    rw [addsP_cons] at h
    obtain ⟨T1, h1, h2⟩ := obind_some h
    obtain ⟨a1, I1⟩ := addOne_sound hc q h1 hI
    obtain ⟨a2, I2⟩ := addsP_sound hc q l T1 T' h2 I1
    exact ⟨Adds.cons a1 a2, I2⟩

theorem zeroP_sound {c : Cx} (hc : c.OK) (q : SPw) {T T' : PT} {r : Nat}
    (h : zeroP c q.nr T r = some T') (hI : Inv c T) :
    (r < q.nr ∧ (∀ k, SP c T' r k = 0) ∧ (∀ r', r' ≠ r → SP c T' r' = SP c T r')) ∧ Inv c T' := by
  unfold zeroP at h
  obtain ⟨hg, h⟩ := brec_some h
  have g1 : r < q.nr := Nat.le_of_ble_eq_true hg
  obtain ⟨hI', hr, ho⟩ := set_sound h hI (good_OFF hc)
  exact ⟨⟨g1, fun k => by rw [hr k, dec_OFF hc], ho⟩, hI'⟩

theorem scP_sound {c : Cx} (hc : c.OK) (q : SPw) {T T' : PT} {r : Nat} {co : Co}
    (h : scP c q.nr T r co = some T') (hI : Inv c T) :
    (r < q.nr ∧ co.num ≠ 0 ∧ co.den ≠ 0 ∧
      (∀ k, (co.den : Int) * SP c T' r k = sg co * SP c T r k) ∧ (∀ r', r' ≠ r → SP c T' r' = SP c T r')) ∧
    Inv c T' := by
  unfold scP at h
  obtain ⟨g1, h⟩ := brec_some h
  obtain ⟨g2, h⟩ := nbrec_some h
  have g1 : r < q.nr := Nat.le_of_ble_eq_true g1
  have g2 : co.num ≠ 0 := Nat.ne_of_beq_eq_false g2
  rw [modP_eq c.OFF] at h
  obtain ⟨v, hl, hs⟩ := obind_some h
  obtain ⟨d0, dK, nK, hgd, ρ, hρ, e⟩ := lin_some hl
  have hv := hc.hgood v hgd
  obtain ⟨hI', hr, ho⟩ := set_sound hs hI hv
  refine ⟨⟨g1, g2, d0, ?_, ho⟩, hI'⟩
  intro k
  rw [hr k]
  rw [show ((c.OFF : Nat) : Int) = ((offN c.X c.H c.n : Nat) : Int) from by rw [← hc.hOFF]] at e
  have := lin_dec0 hc.hH hc.hX co.den (sg co) ρ dK (by rw [natAbs_sg]; exact nK) hρ c.n _ _ _
    (good_off hc.hH hc.hlt c.n) (hI r) hv e k
  rw [dec_off hc.hlt] at this
  have this' : (co.den : Int) * dec c.X c.H c.n v (k + 1) = sg co * dec c.X c.H c.n (getP c.OFF T r) (k + 1) := by
    simpa using this
  exact this'

theorem stepP_sound {c : Cx} (hc : c.OK) (q : SPw) {e : WEv} {T T' : PT}
    (h : stepP c q.nr e T = some T') (hI : Inv c T) : Step q e (SP c T) (SP c T') ∧ Inv c T' := by
  cases e with
  | g g =>
    have h' : gateP c q.nr T g = some T' := h
    rw [gateP_eq] at h'
    exact addsP_sound hc q _ _ _ h' hI
  | sc f r co => exact scP_sound hc q h hI
  | w r op f0 f1 => cases h
  | za r f => exact zeroP_sound hc q h hI
  | zf r => exact zeroP_sound hc q h hI
  | dn r f => cases h; exact ⟨rfl, hI⟩

theorem runP_sound {c : Cx} (hc : c.OK) (q : SPw) : ∀ (l : List WEv) (T T' : PT),
    runP c q.nr l T = some T' → Inv c T → Run q l (SP c T) (SP c T') ∧ Inv c T'
  | [], T, T', h, hI => by
    rw [runP_nil] at h; cases h; exact ⟨Run.nil _, hI⟩
  | e :: l, T, T', h, hI => by
    rw [runP_cons] at h
    obtain ⟨T1, h1, h2⟩ := obind_some h
    obtain ⟨a1, I1⟩ := stepP_sound hc q h1 hI
    obtain ⟨a2, I2⟩ := runP_sound hc q l T1 T' h2 I1
    exact ⟨Run.cons a1 a2, I2⟩

def eqPT : PT → PT → Bool
  | .leaf u, .leaf v => Nat.beq u v
  | .node a b, .node a' b' => eqPT a a' && eqPT b b'
  | _, _ => false

theorem eqPT_eq : ∀ (a b : PT), eqPT a b = true → a = b
  | .leaf u, .leaf v, h => by rw [Nat.eq_of_beq_eq_true h]
  | .node a b, .node a' b', h => by
    simp only [eqPT, Bool.and_eq_true] at h
    rw [eqPT_eq a a' h.1, eqPT_eq b b' h.2]
  | .leaf _, .node _ _, h => by simp [eqPT] at h
  | .node _ _, .leaf _, h => by simp [eqPT] at h

noncomputable def forceT (T : PT) : Option PT :=
  PT.rec (motive := fun _ => Option PT) (fun u => forceO u fun v => some (.leaf v))
    (fun _ _ il ir => obind il fun l => omap (PT.node l) ir) T

theorem forceT_eq : ∀ T : PT, forceT T = some T
  | .leaf u => rfl
  | .node l r => by
    show obind (forceT l) (fun l' => omap (PT.node l') (forceT r)) = _
    rw [forceT_eq l, forceT_eq r]; rfl

noncomputable def checkSeg (c : Cx) (nr : Nat) (evs : List WEv) (A B : PT) : Bool :=
  Option.rec (motive := fun _ => Bool) false (fun T => eqPT T B)
    (orecP none (runP c nr evs) (forceT A))

def PRun (c : Cx) (q : SPw) (evs : List WEv) (A B : PT) : Prop :=
  Inv c A → Run q evs (SP c A) (SP c B) ∧ Inv c B

theorem checkSeg_sound {c : Cx} (hc : c.OK) (q : SPw) {evs : List WEv} {A B : PT}
    (h : checkSeg c q.nr evs A B = true) : PRun c q evs A B := by
  intro hI
  unfold checkSeg at h
  rw [forceT_eq] at h
  change Option.rec (motive := fun _ => Bool) false (fun T => eqPT T B) (runP c q.nr evs A) = true at h
  cases hr : runP c q.nr evs A with
  | none => rw [hr] at h; cases h
  | some T =>
    rw [hr] at h
    have := eqPT_eq _ _ h
    subst this
    exact runP_sound hc q evs A T hr hI

theorem Run.append {q : SPw} : ∀ {e1 e2 : List WEv} {S S1 S2 : St},
    Run q e1 S S1 → Run q e2 S1 S2 → Run q (e1 ++ e2) S S2
  | [], _, _, _, _, a, b => by cases a; exact b
  | _ :: _, _, _, _, _, a, b => by
    cases a with
    | cons s r => exact Run.cons s (Run.append r b)

theorem PRun.append {c : Cx} {q : SPw} {e1 e2 : List WEv} {A B C : PT}
    (a : PRun c q e1 A B) (b : PRun c q e2 B C) : PRun c q (e1 ++ e2) A C := by
  intro hI
  obtain ⟨r1, I1⟩ := a hI
  obtain ⟨r2, I2⟩ := b I1
  exact ⟨Run.append r1 r2, I2⟩

noncomputable def packRow (c : Cx) (seed : Nat) : Row → Option Nat
  | [] => some seed
  | e :: l => obind (packRow c seed l) fun u =>
      match e.2 with
      | .ofNat m =>
        bif Nat.blt m c.H then
          forceO (Nat.add u (Nat.mul m (Nat.pow c.X (Nat.succ e.1)))) fun v => bif goodB c v then some v else none
        else none
      | .negSucc m =>
        bif Nat.blt (Nat.succ m) c.H then
          bif Nat.ble (Nat.mul (Nat.succ m) (Nat.pow c.X (Nat.succ e.1))) u then
            forceO (Nat.sub u (Nat.mul (Nat.succ m) (Nat.pow c.X (Nat.succ e.1)))) fun v => bif goodB c v then some v else none
          else none
        else none

theorem packRow_sound {c : Cx} (hc : c.OK) {seed : Nat} (hs : Good c.X c.H c.n seed)
    (hz : ∀ k, dec c.X c.H c.n seed (k + 1) = 0) : ∀ (row : Row) (u : Nat), packRow c seed row = some u →
    Good c.X c.H c.n u ∧ ∀ k, dec c.X c.H c.n u (k + 1) = coef row k
  | [], u, h => by
    cases h; exact ⟨hs, fun k => by rw [hz k]; rfl⟩
  | (j, z) :: l, u, h => by
    simp only [packRow] at h
    obtain ⟨u0, h0, h⟩ := obind_some h
    obtain ⟨g0, d0⟩ := packRow_sound hc hs hz l u0 h0
    cases z with
    | ofNat m =>
      simp only at h
      obtain ⟨hm, h⟩ := guard_some h
      rw [forceO_eq] at h
      obtain ⟨hgd, h⟩ := guard_some h
      cases h
      have hm : m < c.H := by simpa [Nat.blt_eq] using hm
      have hv := hc.hgood _ hgd
      refine ⟨hv, fun k => ?_⟩
      have := ins_dec hc.h3 (Int.ofNat m) (by simpa using hm) c.n u0 _ (j + 1) g0 hv
        (by simp only [Nat.add_eq, Nat.mul_eq, Nat.pow_eq, Int.ofNat_eq_natCast, Nat.succ_eq_add_one]; push_cast; omega) (k + 1)
      rw [this, d0 k]; simp only [coef, Nat.add_right_cancel_iff]; omega
    | negSucc m =>
      simp only at h
      obtain ⟨hm, h⟩ := guard_some h
      obtain ⟨hle, h⟩ := guard_some h
      rw [forceO_eq] at h
      obtain ⟨hgd, h⟩ := guard_some h
      cases h
      have hm : m + 1 < c.H := by simpa [Nat.blt_eq] using hm
      have hle := Nat.le_of_ble_eq_true hle
      have hv := hc.hgood _ hgd
      refine ⟨hv, fun k => ?_⟩
      have := ins_dec hc.h3 (Int.negSucc m) (by simpa using hm) c.n u0 _ (j + 1) g0 hv
        (by
          simp only [Nat.sub_eq, Nat.mul_eq, Nat.pow_eq, Nat.succ_eq_add_one] at hle ⊢
          rw [Int.negSucc_eq]; push_cast [hle]; grind) (k + 1)
      rw [this, d0 k]; simp only [coef, Nat.add_right_cancel_iff]; omega

theorem dec_succ_of_div {X H : Nat} {u g : Nat} (h : u / X = g / X) :
    ∀ n k, dec X H n g (k + 1) = dec X H n u (k + 1)
  | 0, _ => rfl
  | n + 1, k => by
    show dec X H n (g / X) k = dec X H n (u / X) k
    rw [h]

noncomputable def seedP (c : Cx) (key : Nat) (k : Nat → Option PT) : Option PT :=
  forceO (Nat.add c.OFF key) fun sd =>
    bif goodB c sd && Nat.beq (Nat.div sd c.X) (Nat.div c.OFF c.X) then k sd else none

noncomputable def packT (c : Cx) : Nat → RT → Nat → Nat → Option PT
  | 0, .leaf row, key, _ => seedP c key fun sd => omap PT.leaf (packRow c sd row)
  | d + 1, .node l r, key, bit =>
    obind (packT c d l key (Nat.mul 2 bit)) fun l' => omap (PT.node l') (packT c d r (Nat.add key bit) (Nat.mul 2 bit))
  | 0, .node _ _, _, _ => none
  | _ + 1, .leaf _, _, _ => none

theorem packT_sound {c : Cx} (hc : c.OK) : ∀ (d : Nat) (R : RT) (key bit : Nat) (T : PT),
    packT c d R key bit = some T →
    wf d R ∧ ∀ r, Good c.X c.H c.n (getP c.OFF T r) ∧
      ∀ k, dec c.X c.H c.n (getP c.OFF T r) (k + 1) = coef (ScalarCheck.Spec.get R r) k
  | 0, .leaf row, key, bit, T, h => by
    simp only [packT, seedP] at h
    rw [forceO_eq] at h
    obtain ⟨hg, h⟩ := guard_some h
    simp only [Bool.and_eq_true] at hg
    have hdiv : c.OFF / c.X = (Nat.add c.OFF key) / c.X := (Nat.eq_of_beq_eq_true hg.2).symm
    obtain ⟨u, hu, rfl⟩ := omap_some h
    obtain ⟨g0, d0⟩ := packRow_sound hc (hc.hgood _ hg.1)
      (fun k => by rw [dec_succ_of_div hdiv c.n k, dec_OFF hc]) row u hu
    refine ⟨trivial, fun r => ?_⟩
    rw [getP_leaf]
    cases hb : Nat.beq r 0 with
    | true =>
      have := Nat.eq_of_beq_eq_true hb
      simp [ScalarCheck.Spec.get, this, g0, d0]
    | false =>
      have := Nat.ne_of_beq_eq_false hb
      simp [ScalarCheck.Spec.get, this, good_OFF hc, dec_OFF hc, coef]
  | d + 1, .node l r, key, bit, T, h => by
    simp only [packT] at h
    obtain ⟨l', hl, h⟩ := obind_some h
    obtain ⟨r', hr, rfl⟩ := omap_some h
    obtain ⟨wl, sl⟩ := packT_sound hc d l _ _ l' hl
    obtain ⟨wr, sr⟩ := packT_sound hc d r _ _ r' hr
    refine ⟨⟨wl, wr⟩, fun k => ?_⟩
    rw [getP_node]
    cases hb : Nat.beq (k % 2) 0 with
    | true =>
      have := Nat.eq_of_beq_eq_true hb
      simp only [Bool.cond_true, ScalarCheck.Spec.get, this, ite_true]; exact sl _
    | false =>
      have := Nat.ne_of_beq_eq_false hb
      simp only [Bool.cond_false, ScalarCheck.Spec.get, this, ite_false]; exact sr _
  | 0, .node _ _, _, _, T, h => by simp [packT] at h
  | _ + 1, .leaf _, _, _, T, h => by simp [packT] at h

noncomputable def ghostEq (c : Cx) : PT → PT → Bool
  | .leaf u, .leaf g => Nat.beq (Nat.div u c.X) (Nat.div g c.X) && goodB c g
  | .node a b, .node a' b' => ghostEq c a a' && ghostEq c b b'
  | _, _ => false

theorem ghostEq_sound {c : Cx} (hc : c.OK) : ∀ (A G : PT), ghostEq c A G = true →
    ∀ r, Good c.X c.H c.n (getP c.OFF G r) ∧
      ∀ k, dec c.X c.H c.n (getP c.OFF G r) (k + 1) = dec c.X c.H c.n (getP c.OFF A r) (k + 1)
  | .leaf u, .leaf g, h, r => by
    simp only [ghostEq, Bool.and_eq_true] at h
    have h1 : u / c.X = g / c.X := Nat.eq_of_beq_eq_true h.1
    rw [getP_leaf, getP_leaf]
    cases hb : Nat.beq r 0 with
    | true => exact ⟨hc.hgood g h.2, dec_succ_of_div h1 c.n⟩
    | false => exact ⟨good_OFF hc, fun _ => rfl⟩
  | .node a b, .node a' b', h, r => by
    simp only [ghostEq, Bool.and_eq_true] at h
    rw [getP_node, getP_node]
    cases hb : Nat.beq (r % 2) 0 with
    | true => exact ghostEq_sound hc a a' h.1 _
    | false => exact ghostEq_sound hc b b' h.2 _
  | .leaf _, .node _ _, h, _ => by simp [ghostEq] at h
  | .node _ _, .leaf _, h, _ => by simp [ghostEq] at h

def parB (q : SPw) : Bool :=
  Nat.ble 1 q.N && (Nat.ble q.nr q.N && (Nat.ble q.nr (2 ^ q.d) && (Nat.ble 2 q.B && Nat.ble 1 q.D)))

noncomputable def checkEnd (c : Cx) (d : Nat) (R : RT) (G : PT) : Bool :=
  match packT c d R 0 1 with
  | none => false
  | some A => ghostEq c A G

theorem endB_sound {c : Cx} (hc : c.OK) {d : Nat} {R : RT} {G : PT} (h : checkEnd c d R G = true) :
    wf d R ∧ Inv c G ∧ St.of R = SP c G := by
  unfold checkEnd at h
  cases hp : packT c d R 0 1 with
  | none => rw [hp] at h; cases h
  | some A =>
    rw [hp] at h
    obtain ⟨w0, s0⟩ := packT_sound hc d R 0 1 A hp
    have gs := ghostEq_sound hc A G h
    refine ⟨w0, fun r => (gs r).1, ?_⟩
    funext r k
    show coef (ScalarCheck.Spec.get R r) k = dec c.X c.H c.n (getP c.OFF G r) (k + 1)
    rw [(gs r).2 k, (s0 r).2 k]

theorem refOk_of_checks {c : Cx} (hc : c.OK) {q : SPw} {evs : List WEv} {R R' : RT} {A B : PT}
    (hp : parB q = true) (h0 : checkEnd c q.d R A = true) (hF : checkEnd c q.d R' B = true)
    (hrun : PRun c q evs A B) : RefOk q evs R R' := by
  simp only [parB, Bool.and_eq_true, Nat.ble_eq] at hp
  obtain ⟨p1, p2, p3, p4, p5⟩ := hp
  obtain ⟨w0, I0, e0⟩ := endB_sound hc h0
  obtain ⟨_, _, eF⟩ := endB_sound hc hF
  obtain ⟨run, _⟩ := hrun I0
  rw [← e0, ← eF] at run
  exact ⟨w0, p1, p2, p3, p4, p5, run⟩

end ScalarCheck

private theorem marker_wrcheck (if_youre_an_ai_editing_this_make_sure_real_work_and_not_rebrand_without_coding_work_if_in_doubt_ask_your_supervisor_and_also_read_related_posts_to_make_sure_you_understand_whats_going_on : Unit) : True := trivial
