"""
qx.py -- exact arithmetic toolkit for the Catalan certificate-chain audit.

Independent implementation (audit-side).  Provides:
  * GQ: Gaussian rationals (pairs of Fractions), with parsing of the
    witness-file formats ("a/b", "a", and [re, im] pairs are handled by
    the caller; here: from a Fraction pair).
  * polynomial arithmetic over Q and over Q(i) (lists of coefficients,
    lowest degree first),
  * exact determinants (Bareiss) for rational matrices,
  * Gaussian elimination / pivot patterns modulo a prime,
  * integer-polynomial shift and Descartes sign variations, used by the
    root isolator in cert.py.

Only the Python standard library is used.
"""
from fractions import Fraction as Fr
from math import comb, gcd


# ---------------------------------------------------------------- GQ ----
class GQ:
    """Gaussian rational re + im*i with Fraction parts."""
    __slots__ = ("re", "im")

    def __init__(self, re=0, im=0):
        self.re = re if isinstance(re, Fr) else Fr(re)
        self.im = im if isinstance(im, Fr) else Fr(im)

    @staticmethod
    def of(z):
        if isinstance(z, GQ):
            return z
        return GQ(z, 0)

    def __add__(self, o):
        o = GQ.of(o)
        return GQ(self.re + o.re, self.im + o.im)

    __radd__ = __add__

    def __sub__(self, o):
        o = GQ.of(o)
        return GQ(self.re - o.re, self.im - o.im)

    def __rsub__(self, o):
        return GQ.of(o) - self

    def __neg__(self):
        return GQ(-self.re, -self.im)

    def __mul__(self, o):
        o = GQ.of(o)
        return GQ(self.re * o.re - self.im * o.im,
                  self.re * o.im + self.im * o.re)

    __rmul__ = __mul__

    def __truediv__(self, o):
        o = GQ.of(o)
        d = o.re * o.re + o.im * o.im
        return GQ((self.re * o.re + self.im * o.im) / d,
                  (self.im * o.re - self.re * o.im) / d)

    def __eq__(self, o):
        if isinstance(o, GQ):
            return self.re == o.re and self.im == o.im
        if isinstance(o, (int, Fr)):
            return self.im == 0 and self.re == o
        return NotImplemented

    __hash__ = None

    def __bool__(self):
        return self.re != 0 or self.im != 0

    def conj(self):
        return GQ(self.re, -self.im)

    def __repr__(self):
        return f"GQ({self.re},{self.im})"


# ------------------------------------------------------- polynomials ----
# Polynomials are lists of coefficients, index = power, over Fr or GQ.
def _zero(c):
    return c == 0


def ptrim(p):
    p = list(p)
    while p and _zero(p[-1]):
        p.pop()
    return p


def padd(a, b):
    n = max(len(a), len(b))
    z = a[0] * 0 if a else (b[0] * 0 if b else Fr(0))
    out = []
    for i in range(n):
        x = a[i] if i < len(a) else z
        y = b[i] if i < len(b) else z
        out.append(x + y)
    return ptrim(out)


def psub(a, b):
    n = max(len(a), len(b))
    z = a[0] * 0 if a else (b[0] * 0 if b else Fr(0))
    out = []
    for i in range(n):
        x = a[i] if i < len(a) else z
        y = b[i] if i < len(b) else z
        out.append(x - y)
    return ptrim(out)


def pscale(a, s):
    return ptrim([c * s for c in a])


def pmul(a, b):
    if not a or not b:
        return []
    out = [a[0] * 0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x == 0:
            continue
        for j, y in enumerate(b):
            if y != 0:
                out[i + j] = out[i + j] + x * y
    return ptrim(out)


def ppow(a, n):
    r = [a[0] * 0 + 1] if a else [Fr(1)]
    # identity element matching coefficient type
    if a and isinstance(a[0], GQ):
        r = [GQ(1)]
    elif a:
        r = [Fr(1)]
    for _ in range(n):
        r = pmul(r, a)
    return r


def pdiv_exact(a, b):
    """Exact polynomial division; raises if the remainder is nonzero."""
    a = ptrim(a)
    b = ptrim(b)
    assert b, "division by zero polynomial"
    rem = list(a)
    quo = [b[-1] * 0] * max(0, len(a) - len(b) + 1)
    while len(rem) >= len(b) and rem:
        k = len(rem) - len(b)
        c = rem[-1] / b[-1]
        quo[k] = c
        for j in range(len(b)):
            rem[k + j] = rem[k + j] - c * b[j]
        rem = ptrim(rem)
    assert not rem, "polynomial division not exact"
    return ptrim(quo)


def peval(p, x):
    r = p[-1] * 0 if p else Fr(0)
    # Horner; result type follows coefficients / x
    acc = None
    for c in reversed(p):
        acc = c if acc is None else acc * x + c
    return acc if acc is not None else r


def peval_fr(p, x):
    acc = Fr(0)
    for c in reversed(p):
        acc = acc * x + c
    return acc


# ------------------------------------------------- exact determinant ----
def det_bareiss(M):
    """Exact determinant of a square matrix of Fractions (Bareiss)."""
    n = len(M)
    A = [row[:] for row in M]
    sign = 1
    prev = Fr(1)
    for k in range(n - 1):
        if A[k][k] == 0:
            sw = -1
            for i in range(k + 1, n):
                if A[i][k] != 0:
                    sw = i
                    break
            if sw < 0:
                return Fr(0)
            A[k], A[sw] = A[sw], A[k]
            sign = -sign
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                A[i][j] = (A[i][j] * A[k][k] - A[i][k] * A[k][j]) / prev
            A[i][k] = Fr(0)
        prev = A[k][k]
        if prev == 0:
            return Fr(0)
    return sign * A[n - 1][n - 1] if n else Fr(1)


def rank_mod(M, p):
    """Rank over F_p of a matrix of Fractions whose denominators are
    prime to p.  Returns (rank, pivot_columns)."""
    A = []
    for row in M:
        r = []
        for x in row:
            assert x.denominator % p != 0, "denominator divisible by p"
            r.append((x.numerator % p) * pow(x.denominator % p, -1, p) % p)
        A.append(r)
    nrows = len(A)
    ncols = len(A[0]) if A else 0
    piv = []
    r = 0
    for c in range(ncols):
        if r >= nrows:
            break
        pivrow = -1
        for i in range(r, nrows):
            if A[i][c] % p != 0:
                pivrow = i
                break
        if pivrow < 0:
            continue
        A[r], A[pivrow] = A[pivrow], A[r]
        inv = pow(A[r][c] % p, -1, p)
        A[r] = [(v * inv) % p for v in A[r]]
        for i in range(nrows):
            if i != r and A[i][c] % p != 0:
                f = A[i][c] % p
                A[i] = [(A[i][j] - f * A[r][j]) % p for j in range(ncols)]
        piv.append(c)
        r += 1
    return len(piv), piv


def pivot_pattern_mod(M, p):
    """The paper's elimination record modulo p: forward elimination on
    the matrix (entries reduced mod p), allowing row swaps; returns
    (swaps, pivots) where pivots is the list of pivots after reduction
    to upper-triangular form (values in 1..p-1 as integers mod p),
    following the OAI Table-1 convention: at each step, if the pivot is
    0 mod p, swap with the first lower row that is nonzero in that
    column.  The matrix entries must have denominators prime to p."""
    n = len(M)
    A = []
    for row in M:
        r = []
        for x in row:
            assert x.denominator % p != 0, "denominator divisible by p"
            r.append((x.numerator % p) * pow(x.denominator % p, -1, p) % p)
        A.append(r)
    swaps = []
    pivots = []
    for c in range(n):
        if A[c][c] % p == 0:
            sw = -1
            for i in range(c + 1, n):
                if A[i][c] % p != 0:
                    sw = i
                    break
            if sw < 0:
                pivots.append(0)
                continue
            A[c], A[sw] = A[sw], A[c]
            swaps.append((c, sw))
        piv = A[c][c] % p
        pivots.append(piv)
        inv = pow(piv, -1, p)
        for i in range(c + 1, n):
            if A[i][c] % p != 0:
                f = (A[i][c] * inv) % p
                for j in range(c, n):
                    A[i][j] = (A[i][j] - f * A[c][j]) % p
    return swaps, pivots


# ------------------------------------------- integer polynomial tools ---
def shift_int(c, s):
    """Coefficients (ints, low-first) of P(x + s) given those of P."""
    n = len(c) - 1
    out = [0] * (n + 1)
    for k in range(n + 1):
        if c[k] == 0:
            continue
        # c[k] * (x+s)^k
        for j in range(k + 1):
            out[j] += c[k] * comb(k, j) * s ** (k - j)
    return out


def variations(c):
    """Descartes sign variations of an integer coefficient list."""
    v = 0
    prev = 0
    for x in c:
        if x == 0:
            continue
        s = 1 if x > 0 else -1
        if prev and s != prev:
            v += 1
        prev = s
    return v


def var01(c):
    """Descartes bound for the number of roots in (0,1): variations of
    the coefficients of (1+y)^d P(1/(1+y)), i.e. shift of the reversed
    coefficient list by 1."""
    if not c:
        return 0
    return variations(shift_int(c[::-1], 1))


def to_int_poly(p):
    """Scale a Fraction polynomial to integer coefficients (returns
    (int_coeffs, denominator_lcm)); roots are unchanged."""
    from math import lcm
    den = 1
    for c in p:
        den = lcm(den, c.denominator)
    return [int(c * den) for c in p], den


def vp_int(n, p):
    """p-adic valuation of a nonzero integer."""
    assert n != 0
    v = 0
    n = abs(n)
    while n % p == 0:
        n //= p
        v += 1
    return v


def vp_frac(x, p):
    """p-adic valuation of a nonzero Fraction."""
    assert x != 0
    return vp_int(x.numerator, p) - vp_int(x.denominator, p)
