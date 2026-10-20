"""Blockwise geometric Horner error bounds after the five-site energy check."""
from fractions import Fraction as Q
from math import isqrt


def errors(n):
    if not 4<=n<=12:raise ValueError('Only the certified thermal range is supported.')
    dims={0:1}
    for _ in range(n):
        nxt={}
        for m,d in dims.items():
            for a in (-1,0,1):nxt[m+a]=nxt.get(m+a,0)+d
        dims=nxt
    assert sum(dims.values())==3**n
    kappa=Q(1) if n==4 else 1-Q(n,384)
    assert 0<kappa<=1 and 1-Q(5*n,32)>=-kappa
    e2=0;max_error=0
    for d in dims.values():
        dn=isqrt(d)+1
        # Both real coordinate floors lie in [-1,0]. In Eisenstein
        # coordinates a**2-a*b+b**2 <= 1 on that square.
        # Thus one vector floor costs <= sqrt(d), also for the C twist.
        error=281*(dn+1)+1 if n==4 else (384*(dn+1)+n-1)//n+1
        max_error=max(max_error,error)
        e2+=d*error**2
    return isqrt(e2)+1,max_error,kappa
