/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.AllEdges.Task

/-!
# Deterministic filtering: parameters and the counting oracle

The filtering reduction of the 2.996001 note (Lemma 3.1, Lemma 4.1).  A candidate is a triple
`(a, b, j)`: the pair `(a, b)` and the block `C_j = [j s, min((j+1) s, n))` of third vertices.  It
lies at index `i = j n² + a n + b`; its group is the pair, `i % (n n) = a n + b`.  For a modulus
`p ≥ 1` its count is the number of `c ∈ C_j` with `p ∣ w(a,b) + w(b,c) + w(a,c)`.

* The parameters, as functions of `n` and `U` (§3, (3.5)): `kOf`, `ellOf`, `RR`, `bOf`, `dOf`,
  `roundsOf`, `sOf`, `mOf`, `cKOf`, `rOf`, `BOf`, `hOf`, `pool`, `QOf`, `Guard`, `PmaxOf`.
* The counts (`cntList`) and the task of the counting oracle (`oracleTask`).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Filter2

open ThreeSumApsp.Spec Light.Sec3

/-! ## Parameters -/

/-- `k`, the bit length of `n`: `n < 2^k`. -/
def kOf (n : ℕ) : ℕ := Nat.size n

/-- `ℓ = ⌊√k⌋ + 1`. -/
def ellOf (n : ℕ) : ℕ := Nat.sqrt (kOf n) + 1

/-- `R = 2^ℓ`; the pool is the primes in `[R, 2R)`. -/
def RR (n : ℕ) : ℕ := 2 ^ ellOf n

/-- `b = ℓ (⌊√ℓ⌋ + 1)`, about `k^{3/4}`. -/
def bOf (n : ℕ) : ℕ := ellOf n * (Nat.sqrt (ellOf n) + 1)

/-- `d = ⌊b/2⌋`: a round with the guard shrinks the active set by `2^d`. -/
def dOf (n : ℕ) : ℕ := bOf n / 2

/-- The number of rounds, `⌊3k/d⌋ + 1`, so that `d · rounds > 3k`. -/
def roundsOf (n : ℕ) : ℕ := 3 * kOf n / dOf n + 1

/-- The block size `s = 2^{⌊σ k⌋}`, `σ = 0.0336175`. -/
def sOf (n : ℕ) : ℕ := 2 ^ (336175 * kOf n / 10 ^ 7)

/-- The number of blocks, `⌈n/s⌉`. -/
def mOf (n : ℕ) : ℕ := (n + sOf n - 1) / sOf n

/-- `c_K`, the bit length of the largest witness count `s`. -/
def cKOf (n : ℕ) : ℕ := Nat.size (sOf n)

/-- The number of prime factors per round, `⌊(c_K + b)/ℓ⌋ + 1`. -/
def rOf (n : ℕ) : ℕ := (cKOf n + bOf n) / ellOf n + 1

/-- `B`, the bit length of `3U`: every triangle sum has absolute value below `2^B`. -/
def BOf (U : ℕ) : ℕ := Nat.size (3 * U)

/-- `h = ⌊(B − 1)/ℓ⌋`: a nonzero integer below `2^B` in absolute value has at most `h` prime
divisors in the pool. -/
def hOf (n U : ℕ) : ℕ := (BOf U - 1) / ellOf n

/-- The pool: the primes in `[R, 2R)`. -/
def pool (n : ℕ) : Finset ℕ := (Finset.range (2 * RR n)).filter fun q => RR n ≤ q ∧ q.Prime

/-- `Q`, the size of the pool. -/
def QOf (n : ℕ) : ℕ := (pool n).card

/-- The guard (3.6), `K (2h)^r 2^d ≤ Q^r` with `K = s`.  Not tested by the program on the main
path; it holds for all large `n` along polynomially bounded `U`. -/
def Guard (n U : ℕ) : Prop := sOf n * (2 * hOf n U) ^ rOf n * 2 ^ dOf n ≤ QOf n ^ rOf n

instance (n U : ℕ) : Decidable (Guard n U) := by unfold Guard; infer_instance

/-- The largest modulus, `(2R)^r`. -/
def PmaxOf (n : ℕ) : ℕ := (2 * RR n) ^ rOf n

/-! ## The counts -/

/-- The block `j` of third vertices: `c` with `j s ≤ c < (j + 1) s` and `c < n`. -/
def InBlock (n s j c : ℕ) : Prop := j * s ≤ c ∧ c < (j + 1) * s ∧ c < n

instance (n s j c : ℕ) : Decidable (InBlock n s j c) := by unfold InBlock; infer_instance

/-- The triangle sum `w(a,b) + w(b,c) + w(a,c)` of the pair `q = a n + b` and the vertex `c`, as in
`aeFlags`. -/
def triSum (n : ℕ) (AB BC AC : List ℤ) (q c : ℕ) : ℤ :=
  AB.getD q 0 + BC.getD (q % n * n + c) 0 + AC.getD (q / n * n + c) 0

/-- The count of the candidate `i = j n² + q` at the modulus `p`: the `c` in block `j` with
`p ∣ triSum q c`. -/
def cntOf (n s p : ℕ) (AB BC AC : List ℤ) (i : ℕ) : ℕ :=
  ((Finset.range n).filter fun c =>
    InBlock n s (i / (n * n)) c ∧ (p : ℤ) ∣ triSum n AB BC AC (i % (n * n)) c).card

/-- All `m n²` counts at the modulus `p`, candidate `i` in cell `i`. -/
def cntList (n s p : ℕ) (AB BC AC : List ℤ) : List ℤ :=
  (List.range ((n + s - 1) / s * (n * n))).map fun i => (cntOf n s p AB BC AC i : ℤ)

/-! ## The counting oracle as a task -/

/-- An instance of the oracle: an all-edges instance (without the place of the flags), a block size
`s`, a modulus `p`, and the place `cnt` of the `m n²` counts. -/
structure OracleInst : Type extends TriInst where
  s : ℕ
  p : ℕ
  cnt : ℕ

/-- The number of counts, `⌈n/s⌉ n²`. -/
def OracleInst.len (x : OracleInst) : ℕ := (x.n + x.s - 1) / x.s * (x.n * x.n)

/-- The matrices and the place of the counts lie below the free pointer and do not meet;
`1 ≤ s ≤ n`, `1 ≤ p`. -/
structure OracleInst.Pre (x : OracleInst) (μ : ℕ → ℤ) (fr : ℕ) : Prop
    extends TriInst.Pre x.toTriInst μ fr where
  s_pos : 1 ≤ x.s
  s_le : x.s ≤ x.n
  p_pos : 1 ≤ x.p
  belowCnt : x.cnt + x.len ≤ fr
  apartAB : Apart x.ab (x.n * x.n) x.cnt x.len
  apartBC : Apart x.bc (x.n * x.n) x.cnt x.len
  apartAC : Apart x.ac (x.n * x.n) x.cnt x.len

/-- **The counting oracle** (Lemma 4.1): `oracle(n, U, ab, bc, ac, s, p, cnt, fr)` writes the counts
of all candidates at the modulus `p` to `cnt`, and changes no other cell below `fr`. -/
def oracleTask : TaskN where
  Inst := OracleInst
  pars x := [x.n, x.U, x.s, x.p]
  args x := [x.n, x.U, x.ab, x.bc, x.ac, x.s, x.p, x.cnt]
  Pre := OracleInst.Pre
  Post x μ fr _ μ' := Seg μ' x.cnt (cntList x.n x.s x.p x.AB x.BC x.AC) ∧
    KeptBut μ μ' fr x.cnt x.len

end Light.Filter2
