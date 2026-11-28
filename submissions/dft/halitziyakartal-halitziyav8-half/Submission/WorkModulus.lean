-- The transform length (odd primes and a power of two), the work modulus, and the programs computing them.
import Submission.ReelKit
import Submission.CostCalculus
set_option linter.all false

section

namespace OAI
namespace PowerSaving.Modulus
open Finset Real
noncomputable section

def axisBudget (n : ℕ) := Nat.log 2 (2*n)+1

lemma axisBudget_above (n : ℕ) :
    2*n < 2^axisBudget n := Nat.lt_pow_succ_log_self (by norm_num) _

lemma axisBudget_pow (n : ℕ) (hn : 0<n) :
    2^axisBudget n ≤ 4*n := by
  unfold axisBudget; rw [pow_succ]
  have := Nat.pow_log_le_self 2 (show 2*n ≠ 0 by omega); omega

lemma axisBudget_le (n : ℕ) (hn : 0<n) :
    axisBudget n ≤ 4*n := by
  have := axisBudget_pow n hn; have : axisBudget n < 2^axisBudget n := Nat.lt_two_pow_self; omega

def primeSearchBound (k : ℕ) := (16*(k+4))^2

def OddPrime (i : ℕ) := Nat.Prime i ∧ i>2

instance (i) : Decidable (OddPrime i) := inferInstanceAs (Decidable (_ ∧ _))

def oddPrimeCount (p : ℕ) := ((range p).filter OddPrime).card

lemma oddPrimeCount_succ (p : ℕ) : oddPrimeCount (p+1) = oddPrimeCount p + if OddPrime p then 1 else 0 := by
  unfold oddPrimeCount; rw [card_filter, card_filter, sum_range_succ]

lemma oddPrime_count_ge (S : ℕ) : S ≤ oddPrimeCount (primeSearchBound S + 1) := by
  by_contra hS
  push_neg at hS
  have hB : primeSearchBound S = 2 * (128*(S+4)^2) := by unfold primeSearchBound; ring
  generalize hm : 128*(S+4)^2 = m at hB
  have m4 : 4 ≤ m := by rw [← hm]; have : 1 ≤ (S+4)^2 := Nat.one_le_pow _ _ (by omega); omega
  have hcb : Nat.centralBinom m ≤ (2*m) ^ ((range (2*m+1)).filter Nat.Prime).card := by
    calc Nat.centralBinom m = ∏ p ∈ range (2*m+1), p ^ (Nat.centralBinom m).factorization p :=
          (Nat.prod_pow_factorization_centralBinom m).symm
      _ ≤ ∏ p ∈ range (2*m+1), (if p.Prime then 2*m else 1) :=
          prod_le_prod' fun p _ => by
            split_ifs with hp
            · rw [Nat.centralBinom_eq_two_mul_choose]
              exact Nat.pow_factorization_choose_le (by omega)
            · rw [Nat.factorization_eq_zero_of_not_prime _ hp, pow_zero]
      _ = _ := by rw [prod_ite, prod_const, prod_const_one, mul_one]
  have hπ : ((range (2*m+1)).filter Nat.Prime).card ≤ S := by
    have h1 : (range (2*m+1)).filter Nat.Prime ⊆ insert 2 ((range (2*m+1)).filter OddPrime) := by
      intro p hp
      rw [mem_filter] at hp
      rw [mem_insert, mem_filter]
      by_cases h2 : p = 2
      · exact Or.inl h2
      · exact Or.inr ⟨hp.1, hp.2, by have := hp.2.two_le; omega⟩
    have := (card_le_card h1).trans (card_insert_le _ _)
    unfold oddPrimeCount at hS; rw [hB] at hS
    omega
  have h5 : (2*m)^(S+1) ≤ 4^m := by
    have hN : 2*m = (16*(S+4))*(16*(S+4)) := by rw [← hm]; ring
    have hNle : 16*(S+4) ≤ 2^(16*(S+4)) := Nat.lt_two_pow_self.le
    calc (2*m)^(S+1) = (16*(S+4))^(2*(S+1)) := by rw [hN, ← sq, ← pow_mul]
      _ ≤ (2^(16*(S+4)))^(2*(S+1)) := Nat.pow_le_pow_left hNle _
      _ = 2^(16*(S+4)*(2*(S+1))) := by rw [← pow_mul]
      _ ≤ 2^((16*(S+4))*(16*(S+4))) :=
          Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (by omega))
      _ = 4^m := by rw [← hN, pow_mul]; norm_num
  have h3 := Nat.four_pow_lt_mul_centralBinom m m4
  have h4 : (2*m) ^ ((range (2*m+1)).filter Nat.Prime).card ≤ (2*m)^S :=
    Nat.pow_le_pow_right (by omega) hπ
  have h6 : m * (2*m)^S ≤ (2*m)^(S+1) := by
    rw [pow_succ, mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
  have := Nat.mul_le_mul_left m (hcb.trans h4)
  omega

end
end PowerSaving.Modulus
end OAI

namespace OAI
namespace PowerSaving.Modulus
open AxisTensor
noncomputable section

structure PrimeList where
  l : ℕ
  q : Axes
  vol : ℕ

namespace PrimeList

def empty : PrimeList := ⟨0,fun _ => 0,1⟩

def pushQ (x : PrimeList) (p : ℕ) : PrimeList :=
  ⟨x.l+1,fun i => if i=x.l then p else x.q i, x.vol*p⟩

structure Square (x : PrimeList) : Prop where
  agrees : x.vol=extent x.q x.l
  isles : CoprimeAxes x.q x.l

variable {x : PrimeList}

lemma extent_congr {r r' : Axes} {l : ℕ} (h : ∀ i < l, r i = r' i) : extent r l = extent r' l := by
  induction l with
  | zero => rfl
  | succ l ih =>
    show extent r l * r l = extent r' l * r' l
    rw [ih (fun i hi => h i (by omega)), h l (by omega)]

theorem Square.push (h : x.Square) {p : ℕ} (hp : 2 ≤ p) (hc : p.Coprime x.vol) :
    (x.pushQ p).Square := by
  have ec : ∀ j ≤ x.l, extent (x.pushQ p).q j = extent x.q j := fun j hj =>
    extent_congr fun i hi => if_neg (by omega)
  refine ⟨?_, ⟨fun t ht => ?_, fun i hi => ?_⟩⟩
  · show x.vol * p = extent (x.pushQ p).q x.l * (x.pushQ p).q x.l
    rw [ec _ le_rfl, ← h.agrees]; show _ = x.vol * (if x.l = x.l then p else _); rw [if_pos rfl]
  · show 2 ≤ if t = x.l then p else x.q t
    split_ifs with e
    · exact hp
    · exact h.isles.good t (by have : t < x.l + 1 := ht; omega)
  · have hi' : i < x.l + 1 := hi
    rw [ec i (by omega)]
    show (if i = x.l then p else x.q i).Coprime _
    split_ifs with e
    · subst e; rw [← h.agrees]; exact hc
    · exact h.isles.apart i (by omega)

end PrimeList
open PrimeList

def greedyPrimes (N : ℕ) : ℕ → PrimeList
  | 0 => PrimeList.empty
  | p+1 =>
    let x := greedyPrimes N p
    if OddPrime p ∧ x.vol*p ≤ N then x.pushQ p else x

structure GreedyState (N p : ℕ) (x : PrimeList) : Prop where
  square : x.Square
  odd : Odd x.vol
  top : x.vol ≤ N
  pw : 3^x.l ≤ x.vol
  vars : ∀ i<x.l, OddPrime (x.q i) ∧ x.q i<p
  more : ∀ q, p≤q → OddPrime q → q.Coprime x.vol
  hit : x.l=oddPrimeCount p ∨ ∃ q<p, OddPrime q ∧ N<x.vol*q

lemma greedyPrimes_state {N : ℕ} (hN : 1 ≤ N) : ∀ p, GreedyState N p (greedyPrimes N p) := by
  intro p; induction p with
  | zero =>
    exact ⟨⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩,
      odd_one, hN, le_rfl, fun _ h => absurd h (Nat.not_lt_zero _), fun q _ _ => q.coprime_one_right,
      .inl (by simp [oddPrimeCount, greedyPrimes, PrimeList.empty])⟩
  | succ p ih =>
    show GreedyState N (p+1) (if OddPrime p ∧ (greedyPrimes N p).vol*p ≤ N then _ else _)
    generalize greedyPrimes N p = x at ih
    have hb := oddPrimeCount_succ p
    split_ifs with hc
    · obtain ⟨hbar, hle⟩ := hc
      have hp3 : 3 ≤ p := hbar.2
      have hodd : Odd p := hbar.1.odd_of_ne_two (by omega)
      refine ⟨ih.square.push (by omega) (ih.more p le_rfl hbar), ih.odd.mul hodd, hle, ?_, ?_, ?_, ?_⟩
      · show 3^(x.l+1) ≤ x.vol * p
        rw [pow_succ]; exact Nat.mul_le_mul ih.pw hp3
      · intro i hi
        show OddPrime (if i = x.l then p else x.q i) ∧ (if i = x.l then p else x.q i) < p + 1
        split_ifs with e
        · exact ⟨hbar, by omega⟩
        · have := ih.vars i (by have : i < x.l + 1 := hi; omega); exact ⟨this.1, by omega⟩
      · intro q hq hbq
        exact (ih.more q (by omega) hbq).mul_right
          ((Nat.coprime_primes hbq.1 hbar.1).mpr (by omega))
      · rw [hb, if_pos hbar]
        rcases ih.hit with e | ⟨q, hq, hbq, hlt⟩
        · left; show x.l + 1 = _; omega
        · exact .inr ⟨q, by omega, hbq, show N < x.vol * p * q from
            lt_of_lt_of_le hlt (by rw [Nat.mul_right_comm]; exact Nat.le_mul_of_pos_right _ (by omega))⟩
    · refine ⟨ih.square, ih.odd, ih.top, ih.pw, fun i hi => ⟨(ih.vars i hi).1,
        by have := (ih.vars i hi).2; omega⟩, fun q hq hbq => ih.more q (by omega) hbq, ?_⟩
      rw [hb]
      rcases ih.hit with e | ⟨q, hq, hbq, hlt⟩
      · by_cases hbar : OddPrime p
        · right; exact ⟨p, by omega, hbar, by push_neg at hc; exact hc hbar⟩
        · left; rw [if_neg hbar]; omega
      · right; exact ⟨q, by omega, hbq, hlt⟩

def primeSearchLimit (n : ℕ) := primeSearchBound (axisBudget n)

def oddPart (n : ℕ) := greedyPrimes (2*n) (primeSearchLimit n+1)

def twoPartFill (N p : ℕ) : ℕ→ℕ
  | 0 => 1
  | k+1 => let q := twoPartFill N p k
           if p*q<N then q*2 else q

lemma twoPartFill_spec {N v : ℕ} (hv : 0 < v) (hvN : v < N) : ∀ k, (∃ c, twoPartFill N v k = 2^c) ∧
    v * twoPartFill N v k < 2*N ∧ (N ≤ v * twoPartFill N v k ∨ twoPartFill N v k = 2^k) ∧
    (1 ≤ k → 2 ≤ twoPartFill N v k) := by
  intro k; induction k with
  | zero => exact ⟨⟨0, rfl⟩, by show v * 1 < 2*N; omega, Or.inr rfl, fun h => absurd h (by omega)⟩
  | succ k ih =>
    obtain ⟨⟨c, hc⟩, h2, h3, h4⟩ := ih
    rw [show twoPartFill N v (k+1) = if v * twoPartFill N v k < N then twoPartFill N v k * 2
      else twoPartFill N v k from rfl]
    have one : 1 ≤ twoPartFill N v k := by rw [hc]; exact Nat.one_le_two_pow
    split_ifs with e
    · refine ⟨⟨c+1, by rw [hc, pow_succ]⟩, by rw [← mul_assoc]; omega, ?_, fun _ => by omega⟩
      rcases h3 with h3 | h3
      · omega
      · right; rw [h3, pow_succ]
    · refine ⟨⟨c, hc⟩, h2, Or.inl (by omega), fun _ => ?_⟩
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; simp [twoPartFill] at e; omega
      · exact h4 hk

def twoPart (n : ℕ) := twoPartFill (2*n) (oddPart n).vol (axisBudget n)

def modulusAxes (n : ℕ) := (oddPart n).pushQ (twoPart n)

def axisLogBound (n : ℕ) := Nat.log 2 (2*primeSearchLimit n)+2

lemma limit_pos (n : ℕ) : 1 ≤ primeSearchLimit n := by
  unfold primeSearchLimit primeSearchBound; show 0 < _; positivity

lemma axisLogBound_pow (n : ℕ) :
    2^axisLogBound n ≤ 8*primeSearchLimit n := by
  have := Nat.pow_log_le_self 2 (show 2*primeSearchLimit n ≠ 0 by have := limit_pos n; omega)
  have e : 2^axisLogBound n = 2^(Nat.log 2 (2*primeSearchLimit n)) * 4 := by
    unfold axisLogBound; rw [pow_add]; norm_num
  omega

lemma limit_lt (n : ℕ) : 2 * primeSearchLimit n < 2^axisLogBound n := by
  have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (2*primeSearchLimit n)
  have e : 2^axisLogBound n = 2^(Nat.log 2 (2*primeSearchLimit n)) * 4 := by
    unfold axisLogBound; rw [pow_add]; norm_num
  rw [pow_succ] at this; omega

structure ModulusSpec (n : ℕ) (x : PrimeList) : Prop where
  square : x.Square
  lower : 2*n ≤ x.vol
  upper : x.vol < 4*n
  count : x.l ≤ axisBudget n
  sizes : ∀ i<x.l,x.q i≤2^axisLogBound n

theorem modulusAxes_spec (n : ℕ) (hn : 0<n) :
    ModulusSpec n (modulusAxes n) := by
  suffices key : ∀ x : PrimeList, GreedyState (2*n) (primeSearchLimit n + 1) x →
      ModulusSpec n (x.pushQ (twoPartFill (2*n) x.vol (axisBudget n))) from
    key (oddPart n) (greedyPrimes_state (by omega) _)
  intro x B
  have hL := limit_lt n
  have hv : 0 < x.vol := B.odd.pos
  have hvN : x.vol < 2*n := B.top.lt_of_ne fun h => by
    obtain ⟨k, hk⟩ := B.odd; omega
  have h2S := axisBudget_above n
  obtain ⟨q, hq, hbq, hlt⟩ : ∃ q < primeSearchLimit n + 1, OddPrime q ∧ 2*n < x.vol * q := by
    rcases B.hit with e | e
    · have c1 : axisBudget n ≤ x.l := by rw [e]; exact oddPrime_count_ge _
      have := Nat.pow_le_pow_right (show 0 < 3 by norm_num) c1
      have := Nat.pow_le_pow_left (show 2 ≤ 3 by norm_num) (axisBudget n)
      have := B.pw; have := B.top; omega
    · exact e
  obtain ⟨⟨c, hc⟩, f2, f3, f4⟩ := twoPartFill_spec hv hvN (axisBudget n)
  have hS1 : 1 ≤ axisBudget n := by unfold axisBudget; omega
  have ht := f4 hS1
  have rippleLow : 2*n ≤ x.vol * twoPartFill (2*n) x.vol (axisBudget n) := by
    rcases f3 with f3 | f3
    · exact f3
    · show 2*n ≤ x.vol * twoPartFill (2*n) x.vol (axisBudget n)
      rw [f3]; exact Nat.le_of_lt (Nat.lt_of_lt_of_le h2S (Nat.le_mul_of_pos_left _ hv))
  have hodd2 : (twoPartFill (2*n) x.vol (axisBudget n)).Coprime x.vol := by
    show (twoPartFill _ _ _).Coprime _
    rw [hc]; refine .pow_left c ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 fun ⟨j, hj⟩ => ?_)
    obtain ⟨k, hk⟩ := B.odd; omega
  have htq : twoPartFill (2*n) x.vol (axisBudget n) < 2 * q := by
    have : x.vol * twoPartFill (2*n) x.vol (axisBudget n) < x.vol * (2 * q) := by
      show x.vol * twoPartFill (2*n) x.vol (axisBudget n) < _; rw [Nat.mul_left_comm]; omega
    exact Nat.lt_of_mul_lt_mul_left this
  refine ⟨B.square.push ht hodd2, rippleLow,
    by show x.vol * twoPartFill (2*n) x.vol (axisBudget n) < 4*n; omega, ?_, ?_⟩
  · show x.l + 1 ≤ axisBudget n
    have h3 : 2^x.l ≤ 3^x.l := Nat.pow_le_pow_left (by norm_num) _
    have := Nat.le_log_of_pow_le (by norm_num : 1 < 2) (show 2^x.l ≤ 2*n by have := B.pw; omega)
    unfold axisBudget; exact Nat.add_le_add_right this 1
  · intro i hi
    show (if i = x.l then twoPartFill (2*n) x.vol (axisBudget n) else x.q i) ≤ _
    split_ifs with e
    · exact (htq.trans_le (Nat.mul_le_mul_left 2 (Nat.le_of_lt_succ hq))).le.trans hL.le
    · have := (B.vars i (by have : i < x.l + 1 := hi; omega)).2
      exact ((Nat.le_of_lt_succ this).trans (Nat.le_mul_of_pos_left _ (by norm_num))).trans hL.le

def IsLargeLen (n : ℕ) := 2^axisLogBound n ≤ n

instance (n) : Decidable (IsLargeLen n) := inferInstanceAs (Decidable (_ ≤ _))

def largeWorkModulus (n : ℕ) := (2*n)*(modulusAxes n).vol*2^axisLogBound n

def workModulus (n : ℕ) := if IsLargeLen n then largeWorkModulus n else n

theorem workModulus_bound (n : ℕ) (hn : 0<n) :
    0<workModulus n ∧ workModulus n < 8*n^3 := by
  have S := modulusAxes_spec n hn
  unfold workModulus
  split_ifs with h
  · have hP : 0 < 2^axisLogBound n := by positivity
    have h1 : IsLargeLen n := h
    unfold IsLargeLen at h1
    unfold largeWorkModulus
    have a := S.upper; have b := S.lower
    constructor
    · exact Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) hP
    · have h2 : 2*n*(modulusAxes n).vol*2^axisLogBound n ≤ 2*n*(modulusAxes n).vol*n :=
        Nat.mul_le_mul_left _ h1
      have h3 := Nat.mul_lt_mul_of_pos_left a (show 0 < 2*n*n from Nat.mul_pos (by omega) hn)
      refine lt_of_le_of_lt h2 (lt_of_eq_of_lt (Nat.mul_right_comm _ _ _) (h3.trans_eq (by ring)))
  · exact ⟨hn, by have := Nat.le_self_pow (show 3 ≠ 0 by norm_num) n; omega⟩

lemma eta_dvd_largeWorkModulus (n : ℕ) : 2*n ∣ largeWorkModulus n :=
  ⟨(modulusAxes n).vol*2^axisLogBound n, by unfold largeWorkModulus; ring⟩

lemma vol_dvd_largeWorkModulus (n : ℕ) : (modulusAxes n).vol ∣ largeWorkModulus n :=
  ⟨2*n*2^axisLogBound n, by unfold largeWorkModulus; ring⟩

lemma twoPow_dvd_largeWorkModulus (n : ℕ) (j : ℕ) (hj : j≤axisLogBound n) : 2^j ∣ largeWorkModulus n :=
  (pow_dvd_pow 2 hj).trans (dvd_mul_left _ _)

lemma four_dvd_largeWorkModulus (n : ℕ) : 4 ∣ largeWorkModulus n :=
  twoPow_dvd_largeWorkModulus n 2 (by unfold axisLogBound; omega)

end
end PowerSaving.Modulus
end OAI

namespace OAI.PowerSaving.RAM.Bench
open Ty Modulus AxisTensor Finset
noncomputable section
universe U V
variable {ι : Type U} {κ : Type V} {m : Bool} {b : Bench m ι} {q : Bench m κ}
  {N k S : ι→ℕ}

def primeListTy := p (p w w) (a w)

def primeListT (x : PrimeList) : T primeListTy := ((x.l,x.vol),Tape.tab x.l x.q)

lemma primeListT_l (x : PrimeList) : (primeListT x).1.1 = x.l := rfl

lemma primeListT_vol (x : PrimeList) : (primeListT x).1.2 = x.vol := rfl

structure PrimeListIn (b : Bench m ι) (S : ι→ℕ) (x : ι→PrimeList) : Prop where
  tape : b.PolyMoves S primeListTy fun i => primeListT (x i)
  countB : Small b.size fun i => (x i).l
  volume : Small b.size fun i => (x i).vol
  countS : Small S fun i => (x i).l

namespace PrimeListIn
variable {x : ι→PrimeList}

lemma dimL (h : b.PrimeListIn S x) : b.WordIn S fun i => (x i).l := ⟨h.tape.fst.fst, h.countB⟩

lemma volL (h : b.PrimeListIn S x) : b.WordIn S fun i => (x i).vol := ⟨h.tape.fst.snd, h.volume⟩

lemma dataL (h : b.PrimeListIn S x) :
    b.PolyMoves S (a w) fun i => Tape.tab (x i).l (x i).q := h.tape.snd

end PrimeListIn

lemma oddPrime_word {c : Bench m ι} {S' r : ι → ℕ} (hr : c.WordIn S' r) (hs : Small S' r) :
    c.WordIn S' fun i => if OddPrime (r i) then 1 else 0 := by
  let cnt : ι → ℕ → ℕ := fun i j => ∑ d ∈ range j,
    (if 1 < d then 1 else 0) * (if r i % d < 1 then 1 else 0)
  have cle : ∀ i j, cnt i j ≤ j := fun i j =>
    (sum_le_sum (g := fun _ => 1) fun d _ => by split_ifs <;> simp).trans (by simp)
  have I := FreeReads.climbs (t := w) c r cnt
  have hj := climbIndex (t := w) hr cnt
  have tok : (c.climbs r w cnt).WordIn (fun d => S' d.i) fun d => cnt d.i d.j :=
    ⟨PolyMoves.token (t := w) c r S' cnt, (hr.small.reindex During.i).mono fun d => (cle _ _).trans d.hj.le⟩
  have step := tok.add ((WordIn.cmp (WordIn.wc 1) hj).mul
    (WordIn.cmp ((hr.transfer I).residue hj) (WordIn.wc 1)))
  have cG : c.WordIn S' fun i => cnt i (r i) :=
    ⟨loopPoly (t := w) hr hs cnt ((PolyCan.wc 0).congr fun i => by simp [cnt])
      (step.dry.congr fun d => by simp only [cnt, sum_range_succ]),
     hr.small.mono fun i => cle _ _⟩
  refine ((WordIn.cmp (WordIn.wc 2) hr).mul (WordIn.cmp cG (WordIn.wc 1))).congr fun i => ?_
  have key : cnt i (r i) = 0 ↔ ∀ d < r i, ¬ (1 < d ∧ r i % d = 0) := by
    simp only [cnt]; rw [sum_eq_zero_iff]
    constructor
    · intro hz d hd hh
      have := hz d (mem_range.2 hd); simp [hh.1, hh.2] at this
    · intro hz d hd
      have := hz d (mem_range.1 hd)
      by_cases h1 : 1 < d
      · rw [if_pos h1, if_neg (fun h3 => this ⟨h1, by omega⟩), mul_zero]
      · rw [if_neg h1, zero_mul]
  by_cases h2 : 2 < r i
  · rw [if_pos h2, one_mul]
    have e : OddPrime (r i) ↔ cnt i (r i) < 1 := by
      rw [Nat.lt_one_iff, key]
      constructor
      · rintro ⟨hp, -⟩ d hd ⟨h1, h3⟩
        exact (Nat.prime_def_lt'.1 hp).2 d h1 hd (Nat.dvd_of_mod_eq_zero h3)
      · intro hz
        exact ⟨Nat.prime_def_lt'.2 ⟨by omega, fun d h1 hd hdv =>
          hz d hd ⟨h1, Nat.mod_eq_zero_of_dvd hdv⟩⟩, h2⟩
    by_cases hb : OddPrime (r i)
    · rw [if_pos hb, if_pos (e.1 hb)]
    · rw [if_neg hb, if_neg (fun h => hb (e.2 h))]
  · rw [if_neg h2, zero_mul, if_neg (fun hb : OddPrime (r i) => h2 hb.2)]

lemma pushQ_moves {c : Bench m ι} {S' : ι → ℕ} {x : ι → PrimeList} {r : ι → ℕ}
    (hx : c.PolyMoves S' primeListTy fun i => primeListT (x i)) (hl : c.WordIn S' fun i => (x i).l)
    (hlS : Small S' fun i => (x i).l) (hv : c.WordIn S' fun i => (x i).vol) (hr : c.WordIn S' r) :
    c.PolyMoves S' primeListTy fun i => primeListT ((x i).pushQ (r i)) := by
  have l1 : c.WordIn S' fun i => (x i).l + 1 := hl.add (WordIn.wc 1)
  have arr : c.PolyMoves S' (a w) fun i =>
      Tape.tab ((x i).l + 1) (fun j => if j = (x i).l then r i else (x i).q j) := by
    refine tabPoly l1 (hlS.add (Small.const _ 1)) _ ?_
    have I := FreeReads.scan c (fun i => (x i).l + 1)
    have hj := scanIndex l1
    have f := WordIn.cmp hj (hl.transfer I)
    have tp := (PolyMoves.transfer hx.snd I).look hj.dry
    refine (PolyCan.branch f.dry (hr.transfer I).dry tp).congr fun d => ?_
    have hd := d.hj
    by_cases e : d.j = (x d.i).l
    · simp [e]
    · have : d.j < (x d.i).l := by omega
      simp [e, this, primeListT, Tape.look_tab]
  exact ((l1.dry.pair (hv.mul hr).dry).pair arr).congr fun i => rfl

lemma greedy_le (N : ℕ) : ∀ j, (greedyPrimes N j).l ≤ j := by
  intro j; induction j with
  | zero => exact le_rfl
  | succ j ih =>
    simp only [greedyPrimes]; split_ifs
    · exact Nat.succ_le_succ ih
    · omega

structure LenCtx (b : Bench m ι) (S n : ι→ℕ) : Prop where
  num : b.FreeWord n
  budgetFree : b.FreeWord S
  budget_eq : ∀ i, axisBudget (n i)=S i
  pos : ∀ i, 0<n i

namespace LenCtx
variable {n : ι→ℕ} {f : ι→κ}

lemma transfer {S n : κ→ℕ} (h : q.LenCtx S n) (g : b.FreeReads q f) :
    b.LenCtx (fun i => S (f i)) fun i => n (f i) :=
  ⟨h.num.transfer g, h.budgetFree.transfer g, fun _ => h.budget_eq _, fun _ => h.pos _⟩

lemma budgetPow_small (h : b.LenCtx S n) : Small b.size fun i => 2^S i :=
  (h.num.small.mul (Small.const _ 4)).mono fun i => by
    rw [← h.budget_eq]; have := axisBudget_pow (n i) (h.pos i); omega

lemma limitS (h : b.LenCtx S n) : Small S fun i => primeSearchLimit (n i) + 1 :=
  ((((Small.const S 16).mul ((Small.self S).add (Small.const S 4))).pow 2).add
    (Small.const S 1)).mono fun i => by
    show primeSearchBound (axisBudget (n i)) + 1 ≤ _; rw [h.budget_eq]; exact le_rfl

lemma powOrderS (h : b.LenCtx S n) : Small S fun i => 2^axisLogBound (n i) :=
  ((Small.const S 8).mul ((h.limitS).mono fun i => Nat.le_succ _)).mono fun i => by
    have := axisLogBound_pow (n i); omega

lemma orderS (h : b.LenCtx S n) : Small S fun i => axisLogBound (n i) :=
  h.powOrderS.mono fun i => Nat.lt_two_pow_self.le

lemma limitG (h : b.LenCtx S n) : b.WordIn S fun i => primeSearchLimit (n i) := by
  have sG := h.budgetFree.grain S
  refine (((WordIn.wc 16).mul (sG.add (WordIn.wc 4))).mul
    ((WordIn.wc 16).mul (sG.add (WordIn.wc 4)))).congr fun i => ?_
  show _ = primeSearchBound (axisBudget (n i)); rw [h.budget_eq]; unfold primeSearchBound; ring

lemma orderG (h : b.LenCtx S n) : b.WordIn S fun i => axisLogBound (n i) :=
  ((((WordIn.wc 2).mul h.limitG).logtwo
    (((h.limitS).mono fun i => Nat.le_succ _).mul (Small.const S 2) |>.mono fun i =>
      (mul_comm _ _).le)).add (WordIn.wc 2)).congr fun i => rfl

lemma powOrderG (h : b.LenCtx S n) : b.WordIn S fun i => 2^axisLogBound (n i) :=
  WordIn.twoPow h.orderG h.orderS (h.powOrderS.trans h.budgetFree.small)

lemma modulusAxes_in (h : b.LenCtx S n) : b.PrimeListIn S fun i => modulusAxes (n i) := by
  have NG : b.WordIn S fun i => 2 * n i := (WordIn.wc 2).mul (h.num.grain S)
  set L : ι → ℕ := fun i => primeSearchLimit (n i) + 1
  have LG : b.WordIn S L := h.limitG.add (WordIn.wc 1)
  have LS : Small S L := h.limitS
  have topv : ∀ i j, (greedyPrimes (2 * n i) j).vol ≤ 2 * n i := fun i j =>
    (greedyPrimes_state (by have := h.pos i; omega) j).top
  let gx : ι → ℕ → T primeListTy := fun i j => primeListT (greedyPrimes (2 * n i) j)
  have odd : b.PolyMoves S primeListTy fun i => primeListT (oddPart (n i)) := by
    refine loopPoly LG LS gx ((((PolyCan.wc 0).pair (PolyCan.wc 1)).pair (tabPoly (t := w) (WordIn.wc 0) (Small.const S 0)
      (fun (_ : ι) (_ : ℕ) => (0:ℕ)) (PolyCan.wc 0))).congr fun i => rfl) ?_
    have st := PolyMoves.token b L S gx
    have jG := climbIndex LG gx
    have jS : Small (fun d : During L => S d.i) During.j := (LS.reindex During.i).mono fun d => d.hj.le
    have vG : (b.climbs L primeListTy gx).WordIn (fun d => S d.i) fun d => (greedyPrimes (2 * n d.i) d.j).vol :=
      ⟨st.fst.snd.congr fun d => primeListT_vol _, (NG.small.reindex During.i).mono fun d => topv _ _⟩
    refine (PolyCan.branch ((oddPrime_word jG jS).mul (WordIn.cmp (vG.mul jG) ((NG.transfer (FreeReads.climbs b L gx)).add
      (WordIn.wc 1)))).dry st (pushQ_moves st ⟨st.fst.fst, ((LS.trans h.budgetFree.small).reindex During.i).mono
      fun d => (greedy_le _ _).trans d.hj.le⟩ (jS.mono fun d => greedy_le _ _) vG jG)).congr fun d => ?_
    show _ = primeListT (if OddPrime d.j ∧ (greedyPrimes (2 * n d.i) d.j).vol * d.j ≤ 2 * n d.i then _ else _)
    by_cases hb1 : OddPrime d.j
    · by_cases hb : (greedyPrimes (2 * n d.i) d.j).vol * d.j ≤ 2 * n d.i
      · rw [if_pos (And.intro hb1 hb), if_neg (by simp [hb1]; omega)]
      · rw [if_neg (not_and_of_not_right _ hb), if_pos (by simp [hb1]; omega)] <;> rfl
    · rw [if_neg (not_and_of_not_left _ hb1), if_pos (by simp [hb1])] <;> rfl
  have spec := fun i => modulusAxes_spec (n i) (h.pos i)
  have ol : ∀ i, (oddPart (n i)).l < S i := fun i => h.budget_eq i ▸ (spec i).count
  have ovG : b.WordIn S fun i => (oddPart (n i)).vol :=
    ⟨odd.fst.snd.congr fun i => primeListT_vol _, NG.small.mono fun i => topv i _⟩
  let tx : ι → ℕ → ℕ := fun i k => twoPartFill (2 * n i) (oddPart (n i)).vol k
  have tle : ∀ i k, twoPartFill (2 * n i) (oddPart (n i)).vol k ≤ 2^k := fun i k => by
    induction k with
    | zero => exact le_rfl
    | succ k ih =>
      show (if _ then _ else _) ≤ _; rw [pow_succ]; split_ifs
      · exact Nat.mul_le_mul_right 2 ih
      · omega
  have twoG : b.WordIn S fun i => twoPart (n i) := by
    refine ⟨(loopPoly (t := w) (h.budgetFree.grain S) (Small.self S) tx (PolyCan.wc 1) ?_).congr fun i => by
        show twoPartFill _ _ (S i) = twoPartFill _ _ (axisBudget (n i)); rw [h.budget_eq],
      h.budgetPow_small.mono fun i => h.budget_eq i ▸ tle i _⟩
    have tok : (b.climbs S w tx).WordIn (fun d => S d.i) fun d => tx d.i d.j :=
      ⟨PolyMoves.token (t := w) b S S tx, (h.budgetPow_small.reindex During.i).mono fun d =>
        (tle _ _).trans (Nat.pow_le_pow_right (by norm_num) d.hj.le)⟩
    have I := FreeReads.climbs (t := w) b S tx
    refine (PolyCan.branch (WordIn.cmp ((ovG.transfer I).mul tok) (NG.transfer I)).dry tok.dry
      (tok.mul (WordIn.wc 2)).dry).congr fun d => ?_
    show _ = if (oddPart (n d.i)).vol * tx d.i d.j < 2 * n d.i then tx d.i d.j * 2 else tx d.i d.j
    by_cases e : (oddPart (n d.i)).vol * tx d.i d.j < 2 * n d.i <;> simp [e]
  have tp := (fun (X : ℕ → PrimeList) (Y : ℕ → ℕ) (odd : b.PolyMoves S primeListTy fun i => primeListT (X (n i)))
      (ol : ∀ i, (X (n i)).l < S i) (ovG : b.WordIn S fun i => (X (n i)).vol) (twoG : b.WordIn S fun i => Y (n i)) =>
    (pushQ_moves odd ⟨odd.fst.fst.congr fun i => primeListT_l _, h.budgetFree.small.mono fun i => (ol i).le⟩ ((Small.self S).mono
      fun i => (ol i).le) ovG twoG : b.PolyMoves S primeListTy fun i => primeListT ((X (n i)).pushQ (Y (n i)))))
    oddPart twoPart odd ol ovG twoG
  refine ⟨tp, h.budgetFree.small.mono fun i => h.budget_eq i ▸ (spec i).count,
    (h.num.small.mul (Small.const _ 4)).mono fun i => by have := (spec i).upper; omega,
    (Small.self S).mono fun i => h.budget_eq i ▸ (spec i).count⟩

lemma largeLen_word (h : b.LenCtx S n) :
    b.WordIn S fun i => if IsLargeLen (n i) then 0 else 1 :=
  (WordIn.cmp (h.num.grain S) h.powOrderG).congr fun i => by
    by_cases c : n i < 2^axisLogBound (n i)
    · rw [if_pos c, if_neg (show ¬ IsLargeLen (n i) from fun e => by unfold IsLargeLen at e; omega)]
    · rw [if_neg c, if_pos (show IsLargeLen (n i) by unfold IsLargeLen; omega)]

lemma workModulus_grain (h : b.LenCtx S n) :
    b.WordIn S fun i => workModulus (n i) := by
  have nG := h.num.grain S
  have big := ((((WordIn.wc 2).mul nG).mul h.modulusAxes_in.volL).mul h.powOrderG)
  refine ⟨(PolyCan.branch h.largeLen_word.dry big.dry nG.dry).congr fun i => ?_,
    (h.num.small.pow 3 |>.mul (Small.const _ 8)).mono fun i => by
      have := (workModulus_bound (n i) (h.pos i)).2; omega⟩
  unfold workModulus largeWorkModulus
  by_cases e : IsLargeLen (n i) <;> simp [e]

end LenCtx

lemma FreeWord.axisBudget_moves (h : b.FreeWord N) (g : ∀ i, 0<N i) :
    b.Moves N w (fun i => axisBudget (N i)) ∧
    (b.extend w (fun i => axisBudget (N i))).LenCtx (fun i => axisBudget (N i)) N := by
  have hs : Small b.size fun i => axisBudget (N i) :=
    (h.small.mul (Small.const _ 4)).mono fun i => by have := axisBudget_le (N i) (g i); omega
  have h2 : b.FreeWord fun i => 2 * N i := (WordIn.wc 2).mul h
  have lm : b.Moves N w fun i => Nat.log 2 (2 * N i) :=
    (FreeWord.logM h2).weaken ⟨2, fun i => show 2 * N i + 1 ≤ 2 * (N i + 1) by omega⟩
  have mv : b.Moves N w fun i => axisBudget (N i) :=
    Can.wadd lm (Can.wc 1) hs
  refine ⟨mv, ⟨h.transfer (FreeReads.extend b _), ⟨(newestMoves b _).toPoly _, hs⟩, fun _ => rfl, g⟩⟩

lemma FreeWord.workModulus_moves (h : b.FreeWord N) (g : ∀ i,0<N i) :
    ∃ d : ℕ,b.Moves (fun i => N i + (axisBudget (N i)+2)^d) w fun i => workModulus (N i) := by
  obtain ⟨mv, ctx⟩ := h.axisBudget_moves g
  obtain ⟨d, hd⟩ := ctx.workModulus_grain.dry
  exact ⟨d, Can.bind (mv.weaken (Dom.of_le fun i => Nat.le_add_right _ _))
    (Can.mono hd fun i => Nat.le_add_left _ _)⟩

end
end OAI.PowerSaving.RAM.Bench
end
