# What the checker establishes

The scalar definitions are located in the pinned
[certificate appendix](https://github.com/yannouli/subset-sum-conditional-refinement/blob/bf1f50f066f2c71a53293791f693f505a67a1540/certificate-appendix.tex).
The following explains this audit's arithmetic and algebraic checks.

## Rigorous arithmetic

Each input decimal is converted directly to a rational. For a positive rational
`x`, repeated multiplication/division by two gives `x = 2^k y`, with
`1 <= y < 2`. Put `z = (y-1)/(y+1)`. For `N = 64`,

```text
ln(y) = 2 sum(j=0..N-1) z^(2j+1)/(2j+1) + R
0 <= R <= 2 z^(2N+1) / ((2N+1)(1-z^2)).
```

To avoid large sums of unrelated denominators, the implementation rounds each
positive summand down to a multiple of `10^-45`. The sum of the discarded
parts is less than `64 * 10^-45`. It adds this allowance and the tail rounded
up to the same scale to the upper endpoint. Thus both endpoints are rational
and enclose the exact natural logarithm. The same construction encloses `ln(2)`
with a positive lower endpoint, permitting interval division. Adding `k` gives
the enclosure for `log2(x)`. Exact powers of two are handled without division.

Interval multiplication takes all four products; division rejects an interval
containing zero. Entropy is computed by these operations. A strict inequality
is accepted only if the lower endpoint of its gap exceeds the exact required
margin. The 24-place report endpoints are rounded outward after the decisions.
The proof of the series tail and interval rules is a written mathematical
justification; it has not been checked in Lean.

## Transfer identities and domination

Use `D = eta-tau`, `G = 2*tau-eta`, and old budgets `Db,Gb`.
Define `q=G/Gb`, `A=D/G`, `Ab=Db/Gb`, and `K=D/q-Db`.
The checker verifies `0<G<Gb`, `K>0`, and `A-Ab=K/Gb`.

The low certificate's affine expression has constant part `z0 D + z1 G`,
coefficients `-z0` on `u` and `-z1` on `w`, and unchanged comparisons.
Subtracting its old expression cancels every variable coefficient and leaves

```text
Lambda0 = z0(D-Db) + z1(G-Gb).
```

For the first band with endpoint factor `H=5/4`, increasing the upper multiplier
by `z0(A-Ab)` gives the difference

```text
z0(A-Ab) w + z0(A-Ab)(Gb H - w) = z0 K H = Lambda1.
```

These are exact coefficient identities in the independent symbols `u`, `w`,
and the comparison rows, not sampled evaluations. Consequently the associated
nonnegative integrands differ pointwise by the constant factor `2^Lambda`.
Their integral relation follows whenever the original integrals are defined;
this audit does not compute their sizes.

The domination argument uses further hypotheses on selected sampled patterns.
In the new low region, `alpha=1`, `D-U>0`, `G-W>=0`, and the comparisons are
nonnegative. Subtracting the desired left side from the certificate side leaves
`(z0-1)(D-U)` plus nonnegative terms. In the extended band, `alpha=G/W<1`,
`AW-U>0`, and `alpha AW=D`. The corresponding difference is
`(z0-alpha)(AW-U)` plus the upper-row and comparison terms. The old lower row
can be negative, but its multiplier is exactly zero. The checker verifies the
needed multiplier signs and `z0>=1` for these two certificates; the pattern
hypotheses come from the source argument and are not independently established.

Replacing the first endpoint by `G` leaves nine strictly increasing finite
endpoints. With `[0,e0]`, then `(ei,e(i+1)]`, then `(e8,infinity)`, the ten regions
are disjoint and exhaustive on the nonnegative real axis. This is an elementary
partition argument, not a finite sample of score values.

## Meaning of the rejection checks

The controls remove exponent slack, overspend finite or alias margins, increase
accuracy costs, invalidate the guard, lower the work parameter, leave the
entropy domain, change the zero multiplier or domination coefficients, omit the
upper-multiplier correction, and delete a region boundary. Each must fail at
its named check. Rejecting a changed sufficient condition does not prove that
no alternative argument could work for that change.
