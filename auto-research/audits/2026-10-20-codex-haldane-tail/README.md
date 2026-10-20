# Conditional Haldane bound 0.1517 from a stronger tail invariant

Assuming the analytic construction and certified finite inputs of
amachino/haldane-gap-refinement at
`15909bdc15e947795b6fba946008dd8530bb3477`, the periodic spin-one chain at
coupling J=1 has a unique ground state and

\[
\gamma_L>\frac{1517}{10000}=0.1517\qquad\text{for every integer }L\ge24.
\]

Here \(H_L=\sum_{j=0}^{L-1}\mathbf S_j\cdot\mathbf S_{j+1}\), with the
standard spin-one operators and periodic identification \(\mathbf S_L=\mathbf S_0\).
The gap \(\gamma_L\) is the difference between the ground energy and the
next distinct energy.

This increases the source's 0.1515 by 0.0002, approximately 0.132%.
It includes the site's comparison domain of even L at least 2304.
The contribution is a refinement of an existing conditional certificate.
It supplies no new thermal data and does not prove the upstream analytic
construction. Its evidence level remains Claimed.

The exact checker passes all 381 named comparisons, the full-interval
polynomial checks, and all directed-root comparisons. This report explains
the new infinite-tail step. The finite checks retain the source's proof.
The added scalar tail argument is also formalized in `code/lean/`. That
formalization leaves the predecessor's physical interpretation and recorded
finite inputs as explicit external obligations.
All ten formalized theorems passed the Lean kernel and an audit allowing
only `propext`, `Quot.sound`, and `Classical.choice` in
[the contributor's Actions run](https://github.com/yashpote/verifier/actions/runs/39406404335).
The exact source commit, compiler output, and dependency pins are recorded
in `evidence/lean-run.json`, `evidence/lean-output.txt`, and `code/lean/`.

## Reproduce

From the verifier repository root, with Python 3.11 or later:

```sh
python3 auto-research/audits/2026-10-20-codex-haldane-tail/verify.py
```

Expected final output:

```text
PASS: 381 exact checks, complete finite cover, and strengthened infinite tail.
CONDITIONAL: gamma_L > 1517/10000 for every integer L >= 24, J=1.
```

The command uses only the standard library, requires no network, checks the
package and source hashes, and reruns the patched checker in a temporary
directory. It compares the entire generated certificate with
`evidence/quarter_refinement.json`. Add `--baseline` to replay the unmodified
0.1515 checker first. `MANIFEST.json` lists every package file except itself.
This command runs the exact Python certificate. The separate Lean command
and its scope are documented in `code/lean/README.md`.

## What changes

The source's quarter-turn certificate leaves the spatial and physical
purity errors very unequal at its last scale. Write p for the upper bound
on the spatial purity defect at (n,b), and q for the upper bound on the
physical purity defect at (2n,b). Here b is inverse temperature and n is an
even reference length. With \(Z_L(b)=\operatorname{Tr}e^{-bH_L}\), the purities are

\[
S(n,b)=\frac{Z_{2n}(b)}{Z_n(b)^2},\qquad
T(L,b)=\frac{Z_L(2b)}{Z_L(b)^2}.
\]

The physical quantity T is the purity of the Gibbs distribution. Under the
source's spatial-transfer construction, S is a probability purity when n
is even. Thus \(1-S(n,b)\le p\) and \(1-T(2n,b)\le q\). The source's
scalar energy shift cancels from both ratios. Its final scale is

\[
n_0=21504,\qquad b_0=12544,\qquad
w_0=1.70982022810726\cdot10^{-827}.
\]

Its old tail argument only uses \(p^{3/2}\le w\) and \(q\le w\).
Here the stronger initial relation \(p^{3/2}\le w/1000\) holds.
Preserving this factor reduces both the tail update constant and the
purity-loss constant to 2.01. That improvement closes the 0.1517 certificate.

The modifications in `code/quarter-tightening.patch` change the target,
three tail checks, the recorded tail parameters, and the displayed result.
They retain the thermal enclosures, eight spectral filters, 117 moment
polynomials, trial inputs, sector recurrence, root directions, and finite
coverage checks. The source checker is preserved byte for byte under
`upstream/`. Its modified copy is `code/verify_quarter_tightened.py`.

## Stronger tail lemma

The goal is to control every remaining length from one even reference
length, using the source's scalar update and signed trace interpolation.
Assume n is even with n at least 4, and b is positive.
All quantities below are deterministic upper bounds. No probability
experiment or numerical sampling is involved.

Put

\[
f(z)=\frac{z^2}{2(1-z)^2},\quad
C=B=\frac{201}{100},\quad s=\frac1{100},\quad
\epsilon=\frac1{1000},\quad \eta=\frac3{500}.
\]

Suppose

\[
0<w\le10^{-6},\qquad 0\le p\le s w^{2/3},\qquad 0\le q\le w.
\tag{1}
\]

The checker tests the spatial inequality without roots, as
\(p^3\le10^{-6}w^2\). At the recorded initial scale it holds with a large
margin. The ratio \(p^3/w_0^2\) is approximately
\(8.9311\cdot10^{-180}\), a display value that is not used for acceptance.

First we show that (1) propagates with \(w_+=Cw^2\). Write
\(x=w^{1/3}\le1/100\) and
\(a=1-(1-p)^2(1-q)\le2p+q\).
The source's rounded-update lemma allows successor certificates

\[
P=f(a),\qquad Q=f\bigl(1-(1-q)^2(1-P)\bigr).
\]

Since f is increasing and
\(a\le(2s+x)x^2\le(3/100)x^2\), we obtain

\[
P\le
\frac{(3/100)^2}{2(1-(3/100)10^{-4})^2}x^4
\le s x^4.
\tag{2}
\]

Consequently \(P\le s(Cw^2)^{2/3}\), because C is at least one.
For the physical update,

\[
1-(1-q)^2(1-P)\le2q+P
\le(2+sx)w\le\frac{20001}{10000}w.
\]

It follows that

\[
Q\le
\frac{(20001/10000)^2}
 {2(1-(20001/10000)10^{-6})^2}w^2
\le Cw^2.
\tag{3}
\]

The two coefficient comparisons are exact rational checks. Also
\(Cw^2\le10^{-6}\), so the domain is preserved. This proves propagation.

Next we bound physical purity at every integer length
\(3n/2\le L\le3n\). The source's concentration and signed-trace argument
uses residual ratios \(d(z)=z/(2-3z)\). On \([0,1/3]\), d(z) is at most z.
Both p and a are in that range. Let
\(R_b(L)=\sum_{j\ge1}|\lambda_j(b)/\lambda_0(b)|^L\), where the source's
spatial eigenvalue list has a positive, unique leading eigenvalue
\(\lambda_0(b)\). This residual bounds the error from all other eigenvalues
in a signed trace. Increasing its moment order gives

\[
R_b(L)\le p^{3/2}\le\epsilon w,\qquad
R_{2b}(L)\le a^{3/2}\le(3/100)^{3/2}w<\eta w.
\tag{4}
\]

The ratio of the leading spatial eigenvalues is controlled by
\(g=(1-P)(1-q)\ge1-P-q\ge1-(1+s/100)w\).
The leading contribution at length L is at least
\(g^{L/(2n)}\ge g^2\ge1-2(1+s/100)w\).
Combining this with (4) in the source's signed trace formula yields

\[
T(L,b)\ge
\frac{(1-2(1+s/100)w)(1-\eta w)}{(1+\epsilon w)^2}
\ge1-\bigl[2(1+s/100)+\eta+2\epsilon\bigr]w
>1-Bw>\frac12.
\tag{5}
\]

For the second inequality, use \((1+u)^{-2}\ge1-2u\) and the fact that
the defect of a product of nonnegative factors in [0,1] is at most the
sum of their defects. The bracket is 2.0082, strictly below B=2.01.
The checker verifies the domains and coefficient comparisons exactly.

Finally define

\[
n_k=n_0 2^k,\quad b_k=b_0 2^k,\quad
w_k=C^{-1}(Cw_0)^{2^k}.
\]

Equation (5) proves uniqueness of the physical ground state and

\[
e^{-b_k\gamma_L}\le\frac{Bw_k}{1-Bw_k}
\quad\text{for }3n_k/2\le L\le3n_k.
\]

For \(\delta=1517/10000\), the existing directed Taylor routine supplies
a rational \(E\ge e^{b_0\delta}\). The final exact tests are

\[
ECw_0<1,\qquad \frac{EBw_0}{1-Bw_0}<1.
\tag{6}
\]

Their left sides are approximately 0.92446. For every k at least zero,

\[
e^{b_k\delta}e^{-b_k\gamma_L}
\le\frac{B/C}{1-Bw_0}(ECw_0)^{2^k}
\le\frac{EBw_0}{1-Bw_0}<1.
\]

Thus \(\gamma_L>\delta\) on every tail interval. Since n0 is even, these
intervals meet at their endpoints and cover all integers L at least 32256.
This completes the infinite-tail argument without a finite cutoff.
The Lean proof supplies an independent exponential enclosure from a log
inequality and thirty rational squarings. Its corresponding comparison is
approximately 0.92602, also strictly below one. That proof does not rely on
the Python Taylor routine. See `code/lean/README.md` for the formal scope.

## Finite cover and failed attempt

The unchanged finite method certifies lengths 24 through 62 individually
at the larger target. Its new interval endpoints are:

| First L | Last L | Sector recurrence level |
| --- | --- | --- |
| 63 | 64 | 0 |
| 65 | 98 | 0 |
| 99 | 310 | 0 |
| 311 | 1341 | 2 |
| 1342 | 5391 | 4 |
| 5392 | 21756 | 6 |
| 21757 | 32255 | 7 |

The checker verifies equality between this cover, together with the
individual lengths, and the complete integer range [24,32255]. All shorter
auxiliary bounds from the source still pass, but no increase is claimed
for them. Combining the finite cover with the tail proves the result.

Simply changing the old target to 0.1517 failed its tail exponential check.
That failure is a limitation of the old certificate at this target, not a
counterexample to the gap bound. The package verifier reproduces the old
tail's rejection using the same certified final row. The stronger invariant
resolves that failed step.

## Scope, provenance, and remaining obligations

The source's rounded update, concentration lemma, signed transfer formula,
and fixed moment bounds remain mathematical dependencies. See
`upstream/paper/note.tex`, equations `eq:update`, `eq:adaptive-ratio`,
`eq:adaptive-interval`, and section `sec:quarter` in
`upstream/paper/quarter.tex`. This report changes the tail constants and
invariant only. It does not audit every upstream written argument.

The exact computation re-encloses recorded thermal totals and uses recorded
trial integers. It does not recompute the large integer thermal runs or
variational contractions. Those finite inputs remain explicit premises,
as they are in the source theorem. The analytic construction and this
written refinement need independent mathematical review. The scalar
formalization does not establish the complete Haldane theorem or the site's
trusted target. There is no site verifier acceptance or unconditional
Haldane-gap claim.

The verifier base is `1e009d7adeb43a1ddffe8b8148be4bebba69e720`.
`SOURCE-PINS.json` records the source commit and hashes. The saved site
snapshot was updated at 2026-10-20T06:17:22Z. Its Haldane record was dated
October 7 and was one of the two oldest current bounds. The Haldane board's
Markdown feed had no posts. Open and closed verifier issues were checked
before work, with no matching Haldane contribution found. Discord history
was unavailable in this session. This is a limited duplication check.

The operating-system random track seed was 14. A primitive-root statement
and audit were initially considered. The user then asked to focus on finding
a result, and this package records the resulting Haldane certificate audit.
The unfinished primitive-root exploration is outside this package.

All original construction and certificate work is credited in `NOTICE.md`.
This refinement and its packaging were produced by Codex GPT-6. No claim of
priority for a general scalar inequality or of optimality is made.
