import Submission.Cert.Label.Trie
namespace ControlCheck
open CertData ControlCheck

noncomputable section

inductive Row where
  | n
  | c (k z : Nat) (t : Row)

abbrev bsel {α : Sort _} (b : Bool) (t e : α) : α := Bool.rec e t b
abbrev gd (b x : Bool) : Bool := Bool.rec false x b

def decI (z : Nat) : Int := if z % 2 = 0 then ((z / 2 : Nat) : Int) else -(((z + 1) / 2 : Nat) : Int)

def zadd (a b : Nat) : Nat :=
  bsel (Nat.beq (Nat.mod a 2) 0)
    (bsel (Nat.beq (Nat.mod b 2) 0) (Nat.add a b)
      (bsel (Nat.blt b a) (Nat.sub (Nat.sub a b) 1) (Nat.sub b a)))
    (bsel (Nat.beq (Nat.mod b 2) 0)
      (bsel (Nat.blt a b) (Nat.sub (Nat.sub b a) 1) (Nat.sub a b))
      (Nat.add (Nat.add a b) 1))

def zmag (z : Nat) : Nat := Nat.div (Nat.add z 1) 2
def zsg (z : Nat) : Bool := Nat.beq (Nat.mod z 2) 1
def zenc (s : Bool) (m : Nat) : Nat := bsel s (Nat.sub (Nat.add m m) 1) (Nat.add m m)
def bxor (a b : Bool) : Bool := Bool.rec b (Bool.rec true false b) a

def cm (a b : Nat) : Nat :=
  Nat.add (Nat.mod (Nat.add (Nat.add (Nat.mod a 4) (Nat.mod b 4))
      (Nat.mul 2 (Nat.mul (Nat.mod (Nat.div a 4) 2) (Nat.mod (Nat.div b 4) 2)))) 4)
    (Nat.add (Nat.mul 4 (Nat.mod (Nat.add (Nat.mod (Nat.div a 4) 2) (Nat.mod (Nat.div b 4) 2)) 2))
      (Nat.mul 8 (Nat.add (Nat.div a 8) (Nat.div b 8))))

def kcode (N k : Nat) : Nat := Nat.add (Nat.mod k 8) (Nat.mul 8 (Nat.div (Nat.div k 8) N))
def kcol (N k : Nat) : Nat := Nat.mod (Nat.div k 8) N
def kmk (N c col : Nat) : Nat := Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.div c 8) N) col) 8) (Nat.mod c 8)

def zpush (k s : Nat) (L : Row) : Row := bsel (Nat.beq s 0) L (.c k s L)

def insK (k c : Nat) : Row → Row :=
  Row.rec (motive := fun _ => Row) (.c k c .n)
    (fun ek ez L ih => bsel (Nat.blt k ek) (.c k c (.c ek ez L))
      (bsel (Nat.beq k ek) (zpush k (zadd c ez) L) (.c ek ez ih)))

def mergeK : Row → Row → Row :=
  Row.rec (motive := fun _ => Row → Row) (fun b => b)
    (fun xk xz xs ih b => Row.rec (motive := fun _ => Row) (.c xk xz xs)
      (fun yk yz ys ihy => bsel (Nat.blt xk yk) (.c xk xz (ih (.c yk yz ys)))
        (bsel (Nat.beq xk yk) (zpush xk (zadd xz yz) (ih ys)) (.c yk yz ihy))) b)

def scaleK (ng : Bool) (num den : Nat) : Row → (Row → Bool) → Bool :=
  Row.rec (motive := fun _ => (Row → Bool) → Bool) (fun k => k .n)
    (fun ek ez _ ih k => gd (Nat.beq (Nat.mod (Nat.mul (zmag ez) num) den) 0)
      (ih fun r => k (.c ek (zenc (bxor (zsg ez) ng) (Nat.div (Nat.mul (zmag ez) num) den)) r)))

def lget (S : List Row) : Nat → Row :=
  List.rec (motive := fun _ => Nat → Row) (fun _ => .n)
    (fun x _ ih i => Nat.rec (motive := fun _ => Row) x (fun j _ => ih j) i) S

def lset (S : List Row) : Nat → Row → List Row :=
  List.rec (motive := fun _ => Nat → Row → List Row) (fun _ _ => [])
    (fun x xs ih i v => Nat.rec (motive := fun _ => List Row) (v :: xs) (fun j _ => x :: ih j v) i) S

def rowIs (r : Row) (k z : Nat) : Bool :=
  match r with
  | .c k' z' .n => Nat.beq k' k && Nat.beq z' z
  | _ => false

def finK (N z : Nat) : List Row → List Nat → Nat → Bool
  | [], _, _ => true
  | r :: S, dg, i => rowIs r (kmk N (dg.headD 0) i) z && finK N z S dg.tail (i + 1)

def initS (nr z : Nat) : List Row := (List.range nr).map fun i => Row.c (8 * i) z .n

def rowEqK : Row → Row → Bool :=
  Row.rec (motive := fun _ => Row → Bool)
    (fun b => Row.rec (motive := fun _ => Bool) true (fun _ _ _ _ => false) b)
    (fun xk xz _ ih b => Row.rec (motive := fun _ => Bool) false
      (fun yk yz ys _ => gd (Nat.beq xk yk) (gd (Nat.beq xz yz) (ih ys))) b)

def stEqK : List Row → List Row → Bool :=
  List.rec (motive := fun _ => List Row → Bool)
    (fun T => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) T)
    (fun x _ ih T => List.rec (motive := fun _ => Bool) false (fun y ys _ => gd (rowEqK x y) (ih ys)) T)

def parK (P : CPar) : Bool := gd (Nat.ble 1 P.N) <| gd (Nat.ble P.nr P.N) <| Nat.blt 0 P.Dn

end

theorem bs {α : Sort _} b (t e : α) : bsel b t e = if b then t else e := by cases b <;> rfl
theorem ga {b x} : gd b x = (b && x) := by cases b <;> rfl
@[local simp] theorem nd a b : Nat.div a b = a / b := rfl
@[local simp] theorem nm a b : Nat.mod a b = a % b := rfl
theorem dz a b : decI (zadd a b) = decI a + decI b := by simp [zadd, decI, bs]; grind
theorem de s m : decI (zenc s m) = if s then -(m : Int) else m := by cases s <;> simp [zenc, decI] <;> grind
theorem dm z : decI z = if zsg z then -(zmag z : Int) else zmag z := by simp [decI, zsg, zmag]; grind
theorem kr {N c i} (h : i < N) : kcode N (kmk N c i) = c ∧ kcol N (kmk N c i) = i := by
  have ⟨e, f⟩ : kmk N c i / 8 = i + c / 8 * N ∧ kmk N c i % 8 = c % 8 := by simp [kmk]; omega
  simp [kcode, kcol, e, f, Nat.add_mul_div_right _ _ (Nat.zero_lt_of_lt h), Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]; omega
theorem rE : ∀ {x y : Row}, rowEqK x y = true → x = y
  | .n, .n, _ => rfl
  | .c .., .c .., h => by simp [rowEqK, ga] at h; rw [h.1, h.2.1, rE h.2.2]
  | .n, .c .., h | .c .., .n, h => nomatch h
theorem sE : ∀ {x y : List Row}, stEqK x y = true → x = y
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp [stEqK, ga] at h; rw [rE h.1, sE h.2]
  | [], _ :: _, h | _ :: _, [], h => nomatch h
theorem lD : ∀ S i, lget S i = S.getD i .n
  | [], _ | _ :: _, 0 => rfl
  | _ :: S, i + 1 => lD S i
theorem ls v : ∀ S t, lset S t v = S.set t v
  | [], _ | _ :: _, 0 => rfl
  | _ :: S, t + 1 => congrArg _ (ls v S t)
theorem fE {N z} : ∀ T (dg : List Nat) j, finK N z T dg j = true →
    ∀ i < T.length, lget T i = .c (kmk N (dg.getD i 0) (j + i)) z .n
  | [], _, _, _, _, hi => nomatch hi
  | r :: T, dg, j, h, i, hi => by
    simp only [finK, Bool.and_eq_true] at h
    cases i with
    | zero => unfold rowIs at h; split at h <;> simp at h; rw [h.1.1, h.1.2]; cases dg <;> rfl
    | succ i =>
      refine (fE T _ _ h.2 i (by simpa using hi)).trans ?_; rw [Nat.add_right_comm]
      show _ = Row.c (kmk N _ (j + i + 1)) z .n; cases dg <;> simp
section Sem
variable {R : Type _} [Lean.Grind.CommRing R]

def _root_.ControlCheck.dp {M : Type _} [Mul M] [One M] : (Nat → M) → Nat → Nat → M
  | _, 0, _ => 1
  | D, n + 1, m => (if m % 2 = 1 then D 0 else 1) * ControlCheck.dp (fun i => D (i + 1)) n (m / 2)

def monoG (q L : R) (D : Nat → R) (NS m : Nat) : R := q ^ (m % 4) * L ^ (m / 4 % 2) * dp D NS (m / 8)

def upd (s : Nat → R) (t : Nat) (v : R) : Nat → R := fun i => if i = t then v else s i

def semEvG (κ : Co → R) (mono : Nat → R) : CEv → (Nat → R) → (Nat → R)
  | .add t r co ex, s => upd s t (s t + κ co * (mono ex * s r))
  | .mul r co, s => upd s r (κ co * s r)
  | .mon r m, s => upd s r (mono m * s r)
  | .swp r t, s => fun i => if i = r then s t else if i = t then s r else s i

def semEvsG (κ : Co → R) (mono : Nat → R) : List CEv → (Nat → R) → (Nat → R)
  | [], s => s
  | e :: es, s => semEvsG κ mono es (semEvG κ mono e s)

def rv (φ : Int → R) (tm : Nat → R) : Row → R
  | .n => 0
  | .c k z t => φ (decI z) * tm k + rv φ tm t

open Lean.Grind.Semiring in
theorem p4 {q : R} (hq : q ^ 4 = 1) : ∀ n, q ^ (n % 4) = q ^ n
  | 0 | 1 | 2 | 3 => rfl
  | n + 4 => by rw [Nat.add_mod_right, p4 hq n, pow_add, hq]; grind
theorem d0 (D : Nat → R) : ∀ n, dp D n 0 = 1
  | 0 => rfl
  | n + 1 => by rw [dp, d0]; grind
theorem m0 (q L : R) D NS : monoG q L D NS 0 = 1 := by grind [monoG, d0]
theorem da : ∀ n (D : Nat → R) x y, x &&& y = 0 → dp D n (x + y) = dp D n x * dp D n y
  | 0, _, _, _, _ => by grind [dp]
  | n + 1, D, x, y, h => by
    have := @Nat.and_mod_two_eq_one x y; rw [h] at this
    have e : (x + y) / 2 = x / 2 + y / 2 := by grind
    simp only [dp, e, da n _ _ _ (by rw [← Nat.and_div_two, h])]; grind
open Lean.Grind.Semiring in
theorem mc {q L : R} D NS (hq : q ^ 4 = 1) (hL : L ^ 2 = q ^ 2) a b
    (h : a / 8 &&& b / 8 = 0) : monoG q L D NS (cm a b) = monoG q L D NS a * monoG q L D NS b := by
  have ⟨e, f, g⟩ : cm a b / 8 = a / 8 + b / 8 ∧ cm a b / 4 % 2 = (a / 4 % 2 + b / 4 % 2) % 2 ∧
    cm a b % 4 = (a % 4 + b % 4 + 2 * (a / 4 % 2 * (b / 4 % 2))) % 4 := by simp [cm]; omega
  unfold monoG; rw [e, f, g, da _ _ _ _ h, p4 hq, pow_add, pow_add]
  cases Nat.mod_two_eq_zero_or_one (a / 4) <;> cases Nat.mod_two_eq_zero_or_one (b / 4) <;> simp [*, pow_zero, pow_one] <;> grind [pow_two]
end Sem

section Ring
variable {R : Type _} [Lean.Grind.CommRing R]

variable (φ : Int → R) (tm : Nat → R)

variable (h0 : φ 0 = 0) (hadd : ∀ x y, φ (x + y) = φ x + φ y)
include h0 hadd
theorem rz k s L : rv φ tm (zpush k s L) = φ (decI s) * tm k + rv φ tm L := by
  simp [zpush, bs]; split <;> simp_all [rv, decI] <;> grind
theorem ri k c r : rv φ tm (insK k c r) = φ (decI c) * tm k + rv φ tm r := by
  induction r <;> simp only [insK, bs] at * <;> (repeat' split) <;> simp_all [rv, rz, dz] <;> grind
theorem rm a : ∀ b, rv φ tm (mergeK a b) = rv φ tm a + rv φ tm b := by
  induction a with
  | n => intro b; show rv φ tm b = 0 + _; grind
  | c xk xz xs ih =>
    intro b; induction b <;> simp only [mergeK, bs] at * <;> (repeat' split) <;> simp_all [rv, rz, dz] <;> grind

end Ring

section Sound
variable {R : Type _} [Lean.Grind.CommRing R]

def Rep (nr : Nat) (φ : Int → R) (tm : Nat → R) (S : List Row) (s : Nat → R) : Prop :=
  S.length = nr ∧ ∀ i, i < nr → rv φ tm (lget S i) = s i

variable (κ : Co → R) (φ : Int → R) (q L : R) (D : Nat → R) (u : Nat → R) (P : CPar)

structure SemHyp (κ : Co → R) (φ : Int → R) (q L : R) (P : CPar) : Prop where
  h0 : φ 0 = 0
  hadd : ∀ x y, φ (x + y) = φ x + φ y
  hκ : ∀ (co : Co) (x y : Int), 0 < co.den →
    (co.den : Int) * y = (if co.neg = true then -(co.num : Int) else (co.num : Int)) * x → κ co * φ x = φ y
  hq : q ^ 4 = 1
  hL : L ^ 2 = q ^ 2

theorem rS {nr tm S s t v x} (hS : Rep nr φ tm S s) (ht : t < nr) (hv : rv φ tm v = x) :
    Rep nr φ tm (lset S t v) (upd s t x) := by
  refine ⟨by simp [ls, hS.1], fun i hi => ?_⟩
  have := hS.2 i hi
  simp [lD, ls, List.getD_eq_getElem?_getD, List.getElem?_set, upd, hS.1 ▸ ht] at this ⊢; grind
theorem pK {P : CPar} (h : parK P = true) : 0 < P.N ∧ P.nr ≤ P.N := by
  simp [parK, ga] at h; exact ⟨h.1, h.2.1⟩
theorem parK_nr (P : CPar) (h : parK P = true) : P.nr ≤ P.N := (pK h).2

theorem semEvsG_append (κ : Co → R) (mono : Nat → R) (a b : List CEv) (s : Nat → R) :
    semEvsG κ mono (a ++ b) s = semEvsG κ mono b (semEvsG κ mono a s) := by
  induction a generalizing s with
  | nil => rfl
  | cons e es ih => exact ih _

end Sound
end ControlCheck

private theorem marker_submission_work_ctrlab_check (if_youre_an_ai_editing_this_make_sure_real_work_and_not_rebrand_without_coding_work_if_in_doubt_ask_your_supervisor_and_also_read_related_posts_to_make_sure_you_understand_whats_going_on : Unit) : True := trivial

namespace ControlCheck.Packed

def wM (a m : Nat) : Nat := 8 * (2 ^ (a + 1) * (2 ^ (m + 1) - 1))

def nTab : Bool → List Nat
  | true => [16,7,6,5,4,3,2,1,0,0,1,2,3,4,5,6,7,8,16,7,6,5,4,3,2,1,0,0,1,2,3,4,5,6,7,8]
  | false => [16,16,7,7,6,6,5,5,4,4,3,3,2,2,1,1,8,8,7,7,6,6,5,5,4,4,3,3,2,2,1,1,0,0,0,0]
def dTab : Bool → List Nat
  | true => [0,0,1,2,3,4,5,6,7,8,8,8,8,8,8,8,8,8,0,0,1,2,3,4,5,6,7,8,8,8,8,8,8,8,8,8]
  | false => [0,0,0,0,1,1,2,2,3,3,4,4,5,5,6,6,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,7,7,8,8]

end ControlCheck.Packed

private theorem marker_submission_work_ctrlab_pack7113 (if_youre_an_ai_editing_this_make_sure_real_work_and_not_rebrand_without_coding_work_if_in_doubt_ask_your_supervisor_and_also_read_related_posts_to_make_sure_you_understand_whats_going_on : Unit) : True := trivial

namespace ControlCheck
open CertData

noncomputable section

def sgI (a b : Nat) : Bool := gd (Nat.beq (Nat.mod (Nat.div a 8) 2) 1) (Nat.beq (Nat.mod (Nat.div b 8) 2) 1)

def cmI (a b : Nat) : Nat :=
  Nat.add (Nat.mod (Nat.add (Nat.add (Nat.mod a 4) (Nat.mod b 4))
      (Nat.mul 2 (Nat.mul (Nat.mod (Nat.div a 4) 2) (Nat.mod (Nat.div b 4) 2)))) 4)
    (Nat.add (Nat.mul 4 (Nat.mod (Nat.add (Nat.mod (Nat.div a 4) 2) (Nat.mod (Nat.div b 4) 2)) 2))
      (Nat.add (Nat.mul 8 (Nat.mod (Nat.add (Nat.mod (Nat.div a 8) 2) (Nat.mod (Nat.div b 8) 2)) 2))
        (Nat.mul 16 (Nat.add (Nat.div a 16) (Nat.div b 16)))))

def mmKI (N e : Nat) : Row → (Row → Bool) → Bool :=
  Row.rec (motive := fun _ => (Row → Bool) → Bool) (fun k => k .n)
    (fun ek ez _ ih k => gd (Nat.beq (Nat.land (Nat.div (Nat.div (Nat.div ek 8) N) 2) (Nat.div e 16)) 0)
      (ih fun r => k (insK (kmk N (cmI (kcode N ek) e) (kcol N ek))
        (zenc (bxor (zsg ez) (sgI (kcode N ek) e)) (zmag ez)) r)))

def evKI (P : CPar) (e : CEv) (S : List Row) (k : List Row → Bool) : Bool :=
  CEv.rec (motive := fun _ => Bool)
    (fun t s co ex => gd (Nat.blt t P.nr) <| gd (Nat.blt s P.nr) <| gd (Nat.blt 0 co.den) <|
      scaleK co.neg co.num co.den (lget S s) fun rs =>
        bsel (Nat.beq ex 0) (k (lset S t (mergeK (lget S t) rs)))
          (mmKI P.N ex rs fun rs' => k (lset S t (mergeK (lget S t) rs'))))
    (fun r co => gd (Nat.blt r P.nr) <| gd (Nat.blt 0 co.den) <|
      scaleK co.neg co.num co.den (lget S r) fun r' => k (lset S r r'))
    (fun r m => gd (Nat.blt r P.nr) <| mmKI P.N m (lget S r) fun r' => k (lset S r r'))
    (fun r t => gd (Nat.blt r P.nr) <| gd (Nat.blt t P.nr) <|
      k (lset (lset S r (lget S t)) t (lget S r)))
    e

def checkEventsI (P : CPar) : List CEv → List Row → (List Row → Bool) → Bool :=
  List.rec (motive := fun _ => List Row → (List Row → Bool) → Bool) (fun S k => k S)
    (fun e _ ih S k => evKI P e S fun S1 => ih S1 k)

def checkSegI (P : CPar) (S : List Row) (evs : List CEv) (S' : List Row) : Bool :=
  checkEventsI P evs S fun T => stEqK T S'

def checkLastI (P : CPar) (S : List Row) (evs : List CEv) (diag : List Nat) : Bool :=
  checkEventsI P evs S fun T => finK P.N (2 * P.Dn) T diag 0

end

def lo (m : Nat) : Nat := m % 8 + 8 * (m / 16)

section Sem
variable {R : Type _} [Lean.Grind.CommRing R]

def monoI (q L ι : R) (D : Nat → R) (NS m : Nat) : R :=
  q ^ (m % 4) * L ^ (m / 4 % 2) * ι ^ (m / 8 % 2) * dp D NS (m / 16)

def tmI (q L ι : R) (D u : Nat → R) (P : CPar) (k : Nat) : R :=
  monoI q L ι D P.NS (kcode P.N k) * u (kcol P.N k)
end Sem

set_option maxHeartbeats 50000

theorem naI (a b : Nat) : Nat.add a b = a + b := rfl
theorem nmI (a b : Nat) : Nat.mul a b = a * b := rfl

theorem sgI_t {a b : Nat} (h : sgI a b = true) : a / 8 % 2 = 1 ∧ b / 8 % 2 = 1 := by
  simp only [sgI, ga, Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem sgI_f {a b : Nat} (h : sgI a b = false) : ¬(a / 8 % 2 = 1 ∧ b / 8 % 2 = 1) := by
  intro ⟨h1, h2⟩
  have e1 : Nat.mod (Nat.div a 8) 2 = 1 := h1
  have e2 : Nat.mod (Nat.div b 8) 2 = 1 := h2
  rw [sgI, e1, e2] at h
  exact absurd h (by decide)

theorem dzs (z : Nat) (s : Bool) :
    decI (zenc (bxor (zsg z) s) (zmag z)) = if s = true then -decI z else decI z := by
  rw [de, dm z]; cases zsg z <;> cases s <;> simp [bxor]

theorem cm_pk (x y : Nat) : cm x y = (x % 4 + y % 4 + 2 * (x / 4 % 2 * (y / 4 % 2))) % 4 +
    (4 * ((x / 4 % 2 + y / 4 % 2) % 2) + 8 * (x / 8 + y / 8)) := rfl
theorem cmI_pk (a b : Nat) : cmI a b = (a % 4 + b % 4 + 2 * (a / 4 % 2 * (b / 4 % 2))) % 4 +
    (4 * ((a / 4 % 2 + b / 4 % 2) % 2) + (8 * ((a / 8 % 2 + b / 8 % 2) % 2) + 16 * (a / 16 + b / 16))) := rfl

theorem pkA {x y z w : Nat} (hx : x < 4) (hy : y < 2) : (x + (4 * y + (8 * z + 16 * w))) % 8 = x + 4 * y := by
  omega
theorem pkB {x y z w : Nat} (hx : x < 4) (hy : y < 2) (hz : z < 2) : (x + (4 * y + (8 * z + 16 * w))) / 8 % 2 = z := by
  omega
theorem pkC {x y z w : Nat} (hx : x < 4) (hy : y < 2) (hz : z < 2) : (x + (4 * y + (8 * z + 16 * w))) / 16 = w := by
  omega

theorem loA (m : Nat) : lo m % 4 = m % 4 := by unfold lo; omega
theorem loB (m : Nat) : lo m / 4 % 2 = m / 4 % 2 := by unfold lo; omega
theorem loC (m : Nat) : lo m / 8 = m / 16 := by unfold lo; omega

theorem lo_dj {a b : Nat} (h : a / 16 &&& b / 16 = 0) : lo a / 8 &&& lo b / 8 = 0 := by
  rw [loC, loC]; exact h

theorem ib_cm (a b : Nat) : cmI a b / 8 % 2 = (a / 8 % 2 + b / 8 % 2) % 2 := by
  rw [cmI_pk, pkB (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))]

theorem lo_cm (a b : Nat) : lo (cmI a b) = cm (lo a) (lo b) := by
  rw [cm_pk, loA a, loB a, loC a, loA b, loB b, loC b]
  unfold lo
  rw [cmI_pk, pkA (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)),
    pkC (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))]
  exact Nat.add_assoc _ _ _

end ControlCheck

private theorem marker_submission_work_ctrlab_checkI (if_youre_an_ai_editing_this_make_sure_real_work_and_not_rebrand_without_coding_work_if_in_doubt_ask_your_supervisor_and_also_read_related_posts_to_make_sure_you_understand_whats_going_on : Unit) : True := trivial

namespace ControlCheck
open CertData

attribute [local simp] ControlCheck.nd ControlCheck.nm

section Ring
variable {R : Type _} [Lean.Grind.CommRing R]
set_option maxHeartbeats 50000

theorem rC (a b c d : R) : a * b * c * d = c * (a * b * d) := by grind
theorem rA (f A B U X : R) : f * (A * B * U) + B * X = B * (f * (A * U) + X) := by grind
theorem rB (f A B U X : R) : -f * (-(A * B) * U) + B * X = B * (f * (A * U) + X) := by grind
theorem r01 (x : R) : x ^ 0 * 1 = 1 := by grind

theorem phn (φ : Int → R) (h0 : φ 0 = 0) (hadd : ∀ x y, φ (x + y) = φ x + φ y) (x : Int) : φ (-x) = -φ x := by
  have h := hadd x (-x); rw [show x + -x = 0 by omega, h0] at h; grind

theorem isg {ι : R} (hι : ι ^ 2 = -1) (A B : R) {x y : Nat} (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1) :
    ι ^ ((x + y) % 2) * (A * B) =
      if x = 1 ∧ y = 1 then -(ι ^ x * A * (ι ^ y * B)) else ι ^ x * A * (ι ^ y * B) := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · rw [if_neg (show ¬((0 : Nat) = 1 ∧ (0 : Nat) = 1) by decide)]; show ι ^ 0 * (A * B) = ι ^ 0 * A * (ι ^ 0 * B); grind
  · rw [if_neg (show ¬((0 : Nat) = 1 ∧ (1 : Nat) = 1) by decide)]; show ι ^ 1 * (A * B) = ι ^ 0 * A * (ι ^ 1 * B); grind
  · rw [if_neg (show ¬((1 : Nat) = 1 ∧ (0 : Nat) = 1) by decide)]; show ι ^ 1 * (A * B) = ι ^ 1 * A * (ι ^ 0 * B); grind
  · rw [if_pos (show (1 : Nat) = 1 ∧ (1 : Nat) = 1 from ⟨rfl, rfl⟩)]; show ι ^ 0 * (A * B) = -(ι ^ 1 * A * (ι ^ 1 * B)); grind

theorem monoI_lo (q L ι : R) (D : Nat → R) (NS m : Nat) :
    monoI q L ι D NS m = ι ^ (m / 8 % 2) * monoG q L D NS (lo m) := by
  unfold monoI monoG; rw [loA, loB, loC]; exact rC _ _ _ _

theorem m0I (q L ι : R) (D : Nat → R) (NS : Nat) : monoI q L ι D NS 0 = 1 := by
  rw [monoI_lo]; show ι ^ 0 * monoG q L D NS 0 = 1; rw [m0]; exact r01 ι

theorem mcI {q L ι : R} (D : Nat → R) (NS : Nat) (hq : q ^ 4 = 1) (hL : L ^ 2 = q ^ 2) (hι : ι ^ 2 = -1)
    (a b : Nat) (h : a / 16 &&& b / 16 = 0) :
    monoI q L ι D NS (cmI a b) = if a / 8 % 2 = 1 ∧ b / 8 % 2 = 1
      then -(monoI q L ι D NS a * monoI q L ι D NS b) else monoI q L ι D NS a * monoI q L ι D NS b := by
  rw [monoI_lo q L ι D NS (cmI a b), ib_cm a b, lo_cm a b, mc D NS hq hL _ _ (lo_dj h),
    monoI_lo q L ι D NS a, monoI_lo q L ι D NS b]
  exact isg hι _ _ (Nat.mod_two_eq_zero_or_one _) (Nat.mod_two_eq_zero_or_one _)

end Ring

section SoundI
variable {R : Type _} [Lean.Grind.CommRing R]
set_option maxHeartbeats 200000

theorem sOg (κ : Co → R) (φ : Int → R) (q L : R) (P : CPar) (H : SemHyp κ φ q L P) (tm : Nat → R)
    (co : Co) (hd : 0 < co.den) r : ∀ k, scaleK co.neg co.num co.den r k = true →
    ∃ r', k r' = true ∧ rv φ tm r' = κ co * rv φ tm r := by
  induction r with
  | n => exact fun k h => ⟨_, h, by grind [rv]⟩
  | c ek ez t ih =>
    intro k h; simp only [scaleK, ga, Bool.and_eq_true] at h; have ⟨r', hk, hr⟩ := ih _ h.2
    refine ⟨_, hk, ?_⟩
    simp only [rv, hr]; rw [← H.hκ co (decI ez) _ hd ?_]
    · grind
    · have := congrArg Int.ofNat (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero (Nat.eq_of_beq_eq_true h.1)))
      rw [de, dm ez]; simp at *
      cases co.neg <;> cases zsg ez <;> simp [bxor] <;> grind

theorem mOI (κ : Co → R) (φ : Int → R) (q L ι : R) (D u : Nat → R) (P : CPar) (H : SemHyp κ φ q L P)
    (hι : ι ^ 2 = -1) (hN : 0 < P.N) (e : Nat) (r : Row) : ∀ k, mmKI P.N e r k = true →
    ∃ r', k r' = true ∧ rv φ (tmI q L ι D u P) r' = monoI q L ι D P.NS e * rv φ (tmI q L ι D u P) r := by
  induction r with
  | n => exact fun k h => ⟨_, h, by grind [rv]⟩
  | c ek ez t ih =>
    intro k h; simp only [mmKI, ga, Bool.and_eq_true] at h; have ⟨r', hk, hr⟩ := ih _ h.2
    have c : kcol P.N ek < P.N := Nat.mod_lt _ hN
    have hd : kcode P.N ek / 16 &&& e / 16 = 0 := by
      rw [show kcode P.N ek / 16 = ek / 8 / P.N / 2 by simp only [kcode, nd, nm, naI, nmI]; omega]
      exact Nat.eq_of_beq_eq_true h.1
    have hm := mcI D P.NS H.hq H.hL hι _ _ hd
    refine ⟨_, hk, ?_⟩
    rw [ri _ _ H.h0 H.hadd, hr, tmI, (kr c).1, (kr c).2, dzs]
    simp only [rv, tmI]
    cases hs : sgI (kcode P.N ek) e
    · rw [if_neg (sgI_f hs)] at hm
      rw [if_neg (show ¬(false = true) by decide), hm]; exact rA _ _ _ _ _
    · rw [if_pos (sgI_t hs)] at hm
      rw [if_pos (show true = true from rfl), hm, phn φ H.h0 H.hadd]; exact rB _ _ _ _ _

theorem rDI {φ : Int → R} {q L ι : R} {D u : Nat → R} {P : CPar} (h1 : φ (P.Dn : Int) = 1) {m i : Nat}
    (c : i < P.N) : rv φ (tmI q L ι D u P) (.c (kmk P.N m i) (2 * P.Dn) .n) = monoI q L ι D P.NS m * u i := by
  simp [rv, tmI, kr c, decI, h1]; grind

theorem checkEventsI_sound (κ : Co → R) (φ : Int → R) (q L ι : R) (D u : Nat → R) (P : CPar)
    (H : SemHyp κ φ q L P) (hι : ι ^ 2 = -1) (hN : 0 < P.N) (evs : List CEv) : ∀ (S : List Row) (s : Nat → R),
    Rep P.nr φ (tmI q L ι D u P) S s → ∀ (k : List Row → Bool), checkEventsI P evs S k = true →
    ∃ S', k S' = true ∧ Rep P.nr φ (tmI q L ι D u P) S' (semEvsG κ (monoI q L ι D P.NS) evs s) := by
  induction evs
  · exact fun S s hS k h => ⟨S, h, hS⟩
  rename_i e es ih; intro S s hS k h
  cases e <;> simp only [checkEventsI, evKI, ga, Bool.and_eq_true, Nat.blt_eq] at h
  case add t r co ex =>
    have ⟨ht, hr, hd, h⟩ := h
    have ⟨rs, h, hrs⟩ := sOg κ φ q L P H (tmI q L ι D u P) co hd _ _ h
    rw [bs] at h; split at h <;> rename_i he
    · refine ih _ _ (rS φ hS ht ?_) k h
      rw [rm _ _ H.h0 H.hadd, hrs, hS.2 _ hr, hS.2 _ ht, Nat.eq_of_beq_eq_true he, m0I]; grind
    · have ⟨rs', h, h'⟩ := mOI κ φ q L ι D u P H hι hN _ _ _ h
      refine ih _ _ (rS φ hS ht ?_) k h
      rw [rm _ _ H.h0 H.hadd, h', hrs, hS.2 _ hr, hS.2 _ ht]; grind
  case mul r co =>
    have ⟨hr, hd, h⟩ := h
    have ⟨rs, h, hrs⟩ := sOg κ φ q L P H (tmI q L ι D u P) co hd _ _ h
    exact ih _ _ (rS φ hS hr (by rw [hrs, hS.2 _ hr])) k h
  case mon r m =>
    have ⟨hr, h⟩ := h
    have ⟨rs, h, hrs⟩ := mOI κ φ q L ι D u P H hι hN _ _ _ h
    exact ih _ _ (rS φ hS hr (by rw [hrs, hS.2 _ hr])) k h
  case swp r t =>
    have ⟨hr, ht, h⟩ := h
    have := rS φ (rS φ hS hr (hS.2 t ht)) ht (hS.2 r hr)
    exact ih _ _ ⟨this.1, fun i hi => (this.2 i hi).trans (by grind [upd, semEvG])⟩ k h

theorem initSI_rep (κ : Co → R) (φ : Int → R) (q L ι : R) (D u : Nat → R) (P : CPar)
    (_H : SemHyp κ φ q L P) (h1 : φ (P.Dn : Int) = 1) (hnr : P.nr ≤ P.N) :
    Rep P.nr φ (tmI q L ι D u P) (initS P.nr (2 * P.Dn)) u := by
  refine ⟨by simp [initS], fun i hi => ?_⟩
  simp [lD, initS, hi]; rw [show 8 * i = kmk P.N 0 i by simp [kmk]; omega, rDI h1 (by omega), m0I]; grind

theorem checkSegI_rep (κ : Co → R) (φ : Int → R) (q L ι : R) (D u : Nat → R) (P : CPar)
    (H : SemHyp κ φ q L P) (hι : ι ^ 2 = -1) (hp : parK P = true) {S S' : List Row} {evs : List CEv}
    (h : checkSegI P S evs S' = true) {s : Nat → R} (hS : Rep P.nr φ (tmI q L ι D u P) S s) :
    Rep P.nr φ (tmI q L ι D u P) S' (semEvsG κ (monoI q L ι D P.NS) evs s) := by
  have ⟨T, hT, hR⟩ := checkEventsI_sound κ φ q L ι D u P H hι (pK hp).1 evs S s hS _ h
  rwa [← sE hT]

theorem checkLastI_val (κ : Co → R) (φ : Int → R) (q L ι : R) (D u : Nat → R) (P : CPar)
    (H : SemHyp κ φ q L P) (hι : ι ^ 2 = -1) (h1 : φ (P.Dn : Int) = 1) (hp : parK P = true) {S : List Row}
    {evs : List CEv} {diag : List Nat} (h : checkLastI P S evs diag = true) {s : Nat → R}
    (hS : Rep P.nr φ (tmI q L ι D u P) S s) (i : Nat) (hi : i < P.nr) :
    semEvsG κ (monoI q L ι D P.NS) evs s i = monoI q L ι D P.NS (diag.getD i 0) * u i := by
  have ⟨T, hT, hR⟩ := checkEventsI_sound κ φ q L ι D u P H hι (pK hp).1 evs S s hS _ h
  rw [← hR.2 i hi, fE _ _ _ hT i (hR.1 ▸ hi), Nat.zero_add, rDI h1 (by have := (pK hp).2; omega)]

end SoundI
end ControlCheck

private theorem marker_submission_work_ctrlab_checkIS (if_youre_an_ai_editing_this_make_sure_real_work_and_not_rebrand_without_coding_work_if_in_doubt_ask_your_supervisor_and_also_read_related_posts_to_make_sure_you_understand_whats_going_on : Unit) : True := trivial

namespace ControlCheck.Batch
open ControlCheck CertData

def hostE (κ : Bool) (j : Nat) (rs : List Nat) : List CEv :=
  if κ then
    [.add (rs.getD 1 0) (rs.getD 0 0) ⟨false, 1, 1⟩ 3, .mon (rs.getD 0 0) (16 * 2 ^ (j + 1)), .mon (rs.getD 1 0) (16 * 2 ^ (j + 1)),
     .add (rs.getD 2 0) (rs.getD 3 0) ⟨true, 1, 1⟩ 1, .mon (rs.getD 2 0) (16 * 2 ^ (j + 1)), .mon (rs.getD 3 0) (16 * 2 ^ (j + 1))]
  else
    [.add (rs.getD 0 0) (rs.getD 1 0) ⟨true, 1, 1⟩ 1, .add (rs.getD 1 0) (rs.getD 0 0) ⟨false, 1, 2⟩ 3,
     .mon (rs.getD 0 0) (16 * 2 ^ (j + 1)), .mon (rs.getD 1 0) (16 * 2 ^ (j + 1))]

end ControlCheck.Batch

private theorem marker_submission_work_b48_host (if_youre_an_ai_editing_this_make_sure_real_work_and_not_rebrand_without_coding_work_if_in_doubt_ask_your_supervisor_and_also_read_related_posts_to_make_sure_you_understand_whats_going_on : Unit) : True := trivial
