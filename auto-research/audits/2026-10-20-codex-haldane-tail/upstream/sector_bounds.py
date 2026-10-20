"""Directed rational arithmetic and full-interval polynomial certificates.

Decimal arithmetic proposes roots only. Each root direction is checked by
integer powers using outward rational rounding. No optimizer is imported.
"""
from decimal import Decimal, localcontext
from fractions import Fraction as Q
from math import comb

GRID = 10**500
ROOT_MARGIN = Q(1,10**200)


def rounded(x, upper=True):
    if x < 0:
        raise ValueError('Expected a nonnegative rational.')
    a, b = divmod(x.numerator*GRID, x.denominator)
    return Q(a+int(upper and bool(b)), GRID)


def power(x, n, upper=True):
    if not isinstance(n, int) or n < 0:
        raise ValueError('Expected a nonnegative integer exponent.')
    z, x = Q(1), rounded(x, upper)
    while n:
        if n & 1:
            z = rounded(z*x, upper)
        n //= 2
        if n:
            x = rounded(x*x, upper)
    return z


def decimal(x):
    return Decimal(x.numerator)/Decimal(x.denominator)


def root(x, n, upper=True):
    if x == 0:
        return Q(0)
    if x < 0 or n < 1:
        raise ValueError('Invalid root domain.')
    with localcontext() as ctx:
        ctx.prec = 560
        y = (decimal(x).ln()/n).exp()
        z = Q(int(y*GRID), GRID)
    z += ROOT_MARGIN if upper else -ROOT_MARGIN
    if not z > 0:
        raise ArithmeticError('Root proposal too small.')
    if upper:
        valid = power(z, n, False) >= x
    else:
        valid = power(z, n, True) <= x
    if not valid:
        raise ArithmeticError('Root direction was not certified.')
    return z


def real_power(x, exponent, upper=True):
    """Enclose x**exponent, for a nonnegative x and rational exponent >= 0."""
    exponent = Q(exponent)
    if exponent < 0:
        raise ValueError('Negative exponents are not supported.')
    y = power(x, exponent.numerator, upper)
    return y if exponent.denominator == 1 else root(y, exponent.denominator, upper)


def significant_upper(x, digits=15):
    if x <= 0:
        raise ValueError('Expected a positive rational.')
    x = rounded(x, True)
    k = len(str(x.numerator))-len(str(x.denominator))
    if x < Q(10)**k:
        k -= 1
    unit = Q(10)**(k-digits+1)
    ratio = x/unit
    return (-(-ratio.numerator//ratio.denominator))*unit


def defect(r):
    return r*(2+r)/(1+r)**2


def f(x):
    if not 0 <= x < 1:
        raise ValueError('Defect must lie in [0,1).')
    return x*x/(2*(1-x)**2)


def residual(v, exponent, D, I, J, upper=True):
    """Convex sector bound, with one leading eigenvalue removed from I."""
    if not 0 <= v <= I <= J <= D or exponent < 1:
        raise ValueError('Invalid sector domain.')
    vertices = [(Q(0), Q(0)), (I-v, Q(0)), (I-v, J-I), (Q(0), J-v)]
    return max(real_power(x, exponent, upper)
               +2*real_power(y/2, exponent, upper)
               +3*real_power((D-v-x-y)/3, exponent, upper)
               for x, y in vertices)


def bernstein_coefficients(c, a, b):
    n = len(c)-1
    monomial = [(b-a)**j*sum(c[k]*comb(k,j)*a**(k-j)
                            for k in range(j,n+1)) for j in range(n+1)]
    return [sum(monomial[j]*Q(comb(i,j),comb(n,j))
                for j in range(i+1)) for i in range(n+1)]


def nonnegative_on_interval(c, a, b):
    """Exact Bernstein subdivision; a returned result certifies the continuum."""
    if not a < b:
        raise ValueError('Empty polynomial interval.')
    stack = [(bernstein_coefficients(c,a,b),0)]
    nodes = depth = 0
    while stack:
        p, d = stack.pop()
        nodes += 1
        depth = max(depth,d)
        if min(p) >= 0:
            continue
        if p[0] < 0 or p[-1] < 0 or max(p) < 0 or d >= 40:
            raise ArithmeticError('Polynomial positivity was not certified.')
        left, right = [p[0]], [p[-1]]
        while len(p) > 1:
            p = [(x+y)/2 for x,y in zip(p,p[1:])]
            left.append(p[0])
            right.append(p[-1])
        stack.extend([(left,d+1),(right[::-1],d+1)])
    return {'nodes':nodes,'maximum_depth':depth}
