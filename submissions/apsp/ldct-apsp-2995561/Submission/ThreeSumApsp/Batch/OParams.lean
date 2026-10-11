/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Submission.ThreeSumApsp.Programs.Sec4.Theorem30.Program
public import Submission.ThreeSumApsp.Programs.Sec3.Theorem17.Parameters.Sizes

/-!
# The batched counting oracle: its parameters and its time

For `n` vertices, the block size `s` and the modulus `p ≥ 1`:

* `m = ⌈log₄ (4 s p)⌉ ≥ 1`, `D = 4^m ≥ 4 s p`, `L = 20 m`, `t = ⌈θ m⌉` with `θ = 56569/500000`;
* `N₀ = 3^{L-m}`, `K₀ = ⌊√binom(L, m)⌋`, `KK = K₀²` (the products of a batch);
* `k = ⌊√(p-1)⌋ + 1` (so `k² ≥ p`, `k ≤ p`), the `n k` digit rows of a product;
* `nb = ⌈n k / N₀⌉ + 1` blocks of `N₀` rows per product, `NP = nb N₀` rows, and the virtual size
  `Nv = K₀ NP` of Theorem 30;
* `T = ⌈n/s⌉` products, in `B = ⌈T / KK⌉` batches.

`oTimeF A n U s p` is the time of the oracle, with the constant `A` for all the bookkeeping.
-/

@[expose] public section

namespace Light.Batch

open ThreeSumApsp Light.Sec4

/-- `m = ⌈log₄ (4 s p)⌉`. -/
def oM (s p : ℕ) : ℕ := Nat.clog 4 (4 * s * p)
/-- `L = 20 m`. -/
def oL (s p : ℕ) : ℕ := 20 * oM s p
/-- `t = ⌈θ m⌉`, `θ = 56569/500000`. -/
def oT (s p : ℕ) : ℕ := (56569 * oM s p + 500000 - 1) / 500000
/-- `D = 4^m`. -/
def oD (s p : ℕ) : ℕ := 4 ^ oM s p
/-- `N₀ = 3^{L-m}`. -/
def oN0 (s p : ℕ) : ℕ := 3 ^ (oL s p - oM s p)
/-- `K₀ = ⌊√binom(L, m)⌋`. -/
def oK0 (s p : ℕ) : ℕ := Nat.sqrt ((oL s p).choose (oM s p))
/-- `KK = K₀²`. -/
def oKK (s p : ℕ) : ℕ := oK0 s p * oK0 s p
/-- `k = ⌊√(p-1)⌋ + 1`. -/
def oDig (p : ℕ) : ℕ := Nat.sqrt (p - 1) + 1
/-- `nb = ⌈n k / N₀⌉ + 1`. -/
def oNb (n s p : ℕ) : ℕ := (n * oDig p) ⌈/⌉ oN0 s p + 1
/-- `NP = nb N₀`. -/
def oNP (n s p : ℕ) : ℕ := oNb n s p * oN0 s p
/-- `Nv = K₀ NP`. -/
def oNv (n s p : ℕ) : ℕ := oK0 s p * oNP n s p
/-- The number of products, `T = ⌈n/s⌉`. -/
def oProd (n s : ℕ) : ℕ := n ⌈/⌉ s
/-- The number of batches, `B = ⌈T / KK⌉`. -/
def oBat (n s p : ℕ) : ℕ := oProd n s ⌈/⌉ oKK s p
/-- The parameters of Theorem 30 for a batch. -/
def oPar (n s p : ℕ) : Sec2.Par := ⟨oL s p, oM s p, oNv n s p⟩

/-- The time of the oracle, with the constant `A` for the bookkeeping: the tables, the parameters,
writing the sources of each batch, the loops of the queries; the preprocessing of each batch, and
one query for each pair and each product. -/
def oTimeF (A n U s p : ℕ) : ℕ :=
  if p = 0 then 0 else
    A * (n * n * (Nat.log 2 (U + 1) + 2) + p + oDig p * oDig p + oNP n s p + n * oDig p
        + (oL s p).choose (oM s p) + 4 ^ oL s p
        + oBat n s p * (oKK s p * oNP n s p * oD s p + oKK s p * n * oDig p * (s + 1)
            + oKK s p * n * n + 1) + 1)
      + oBat n s p * tPreCore cShared30 (oPar n s p) (oT s p)
      + oBat n s p * (oKK s p * (n * n)) * tQueryAt (oL s p) (oM s p) (oT s p)

end Light.Batch
