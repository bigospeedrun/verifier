# Lean check of the added scalar argument

The file `HaldaneTail.lean` formalizes the added scalar tail argument over
the real numbers. It uses Lean 4.34.1 and Mathlib commit
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

This formalization concerns the new tail lemmas. The physical
spatial-transfer construction, recorded thermal and trial inputs, and finite
length certificate remain outside
this Lean file. A successful build does not give the complete 0.1517
Haldane statement the site's Lean Verified evidence level.

## Statements

| Theorem | What Lean checks |
| --- | --- |
| `HaldaneTail.strengthened_step` | For w=x^3, the source's scalar update preserves p <= w^(2/3)/100 and q <= w when w is replaced by (201/100)w^2. The statement uses cubed inequalities to avoid real roots. |
| `HaldaneTail.purity_floor` | The product lower bound from the signed trace argument is at least 1-(201/100)w. |
| `HaldaneTail.interpolation_constants` | The exact constants connecting the residual-moment bounds to the purity bound. |
| `HaldaneTail.tail_geometric` | The exponential comparison holds at every positive integer power, including every dyadic scale. |
| `HaldaneTail.conditional_gap` | A supplied physical exponential bound and the scalar tail conditions imply delta < gap. The physical bound is an explicit hypothesis. |
| `HaldaneTail.invariant_domain` | The update preserves the domain 0 <= w <= 10^(-6). |
| `HaldaneTail.final_tail_comparison` | The final rational constants satisfy E*C*w0+C*w0 < 1. |
| `HaldaneTail.final_tail_comparison_real` | The same comparison after embedding the rational constants into the reals. |
| `HaldaneTail.final_exp_upper` | An independent enclosure of exp(12544*(1517/10000)) using a logarithm inequality and thirty rational squarings. |
| `HaldaneTail.final_exponential_comparison` | The actual real exponential satisfies the final numerical tail comparison. |

For `strengthened_step`, x is in [0,1/100], p is in [0,x^2/100], and q is
in [0,x^3]. With f(z)=z^2/(2(1-z)^2) and
a(p,q)=1-(1-p)^2(1-q), it checks the successors
P=f(a(p,q)) and Q=f(a(q,P)). In particular,

\[
P^3\le(1/100)^3\bigl[(201/100)x^6\bigr]^2,
\qquad Q\le(201/100)x^6.
\]

Since x^6=w^2, these are the required next-scale invariant bounds.
The physical interpretation of these scalar bounds remains the
predecessor's rounded-update lemma.

For `tail_geometric`, set alpha=Cw0 and C=B=201/100. The hypothesis
E*alpha+alpha<1 is precisely the final prefactor comparison. The theorem
proves

\[
\frac{E^N\alpha^N}{1-\alpha^N}<1\qquad(N\ge1).
\]

With w_k=C^(-1)alpha^(2^k), this gives the comparison at every tail scale.
The value E encloses exp(b0*delta) by `final_exp_upper`. The
physical-purity inequality must still be supplied. That obligation
is explicit and has not been hidden inside the formal statement.
The actual rational values of E and w0 are in `final-constants.json` and
in the Lean definitions `finalE` and `finalW`. The Lean enclosure is
independent of the Python Taylor certificate. It starts with
exp(u) <= 1/(1-u) for u=12544*(1517/10000)/2^30. This follows from
log(1-u) <= -u. Thirty squarings give the full exponential bound,
with every outward rational rounding checked by Lean. The values are
also recorded in `exp-enclosures.json`.
This enclosure gives E*C*w0 approximately 0.92602. The Python checker's
Taylor enclosure gives approximately 0.92446. Both are strictly below one.

The ten theorems and axiom audit passed in
[GitHub Actions run 39406404335](https://github.com/yashpote/verifier/actions/runs/39406404335),
at immutable commit `38d67aef630b1db61b2f5bc6f06fef5c0e89e6e4`.
The source hash, scope, and axiom lists are in `../../evidence/lean-run.json`.

## Reproduce and audit axioms

From this directory with the pinned Lean toolchain installed:

```sh
lake update
lake exe cache get
lake env lean HaldaneTail.lean > lean-output.txt
python3 check_axioms.py lean-output.txt
```

Compilation must exit successfully before the axiom audit is accepted.
The audit requires all ten theorem reports and permits only `propext`,
`Quot.sound`, and `Classical.choice`. No custom axioms or `sorry` proofs
are used. The compiler output and dependency manifest are retained as
GitHub Actions artifacts on the contributor's fork. No proof execution
uses the shared Big O Speedrun verifier.

The scalar update, probability-purity framework, signed trace argument,
and original finite certificates are credited to the predecessors named
in the package `NOTICE.md`. The added Lean proofs and audit script were
written with Codex GPT-6.
