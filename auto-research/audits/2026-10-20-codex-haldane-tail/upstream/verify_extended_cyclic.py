"""Rational enclosures for the extended cyclic-twist moment table.

The integer totals use the pinned Horner construction at beta=49/4,
Q=2**55 and Poisson cutoff J=280, in Eisenstein coordinates.
This scalar checker does not recompute the matrix columns.
"""
from fractions import Fraction as Q
from math import factorial, isqrt
from pathlib import Path
import json
from thermal_error_bounds import errors
from verify_local_energy import certificate

ROOT=Path(__file__).resolve().parent


def enclosures():
    if not __debug__:
        raise RuntimeError('Assertions must be enabled.')
    assert certificate()['success']
    records=json.loads((ROOT/'independent_results/extended_cyclic_totals.json').read_text())
    assert [r['n'] for r in records]==list(range(4,13))
    coefficients=[Q(98)**j/factorial(j) for j in range(281)]
    denominator=sum(coefficients)
    probabilities=[int(2**55*x/denominator) for x in coefficients]
    assert max(j for j,x in enumerate(probabilities) if x)==191
    assert sum(probabilities)<=2**55
    # Twice the conditioned Poisson tail is < e**98/2**280.
    assert 2**55*3**98<2**280
    result=[]
    for rec in records:
        n=rec['n']
        assert rec['twist']==2 and rec['beta']=='49/4'
        assert (rec['Q'],rec['J'],rec['last_nonzero'])==(2**55,280,191)
        assert rec['multiplicity_sum']==3**n
        assert rec['maximum_coordinate_row_l1']<=80
        # Each physical twisted Hamiltonian gives a self-adjoint contraction.
        assert 1-Q(5*n,32)>=-1
        E,max_error,kappa=errors(n)
        # Each Eisenstein coordinate is <= twice the complex norm.
        assert 80*(2*2**55+2*max_error)<2**63
        # The per-column quadratic sum and weighted sum fit signed 128 bits.
        assert (2**55+max_error)**2*4*n<2**127
        # All representative contributions fit the four-limb accumulator.
        assert 3**n*(2**55+max_error)**2<2**256
        total=int(rec['total']);r=isqrt(total)
        assert r*r<=total<(r+1)**2 and r>E
        x=Q(49,4)*n*(Q(3,2)-Q(700741,500000))
        term=s=Q(1)
        for j in range(1,101):
            term*=x/j;s+=term
        assert 0<x<15 and x/(101-x)<1
        lower=s*(r-E)**2/2**110
        upper=(s+term)*(r+1+E)**2/2**110
        assert 0<lower<upper
        result.append({'n':n,'lower':str(lower),'upper':str(upper),
                       'frobenius_error_Q_units':E,'maximum_column_error_Q_units':max_error,
                       'contraction_modulus_upper':str(kappa)})
    return result


def main():
    result=enclosures()
    (ROOT/'independent_results/extended_cyclic_enclosures.json').write_text(
        json.dumps({'beta':'49/4','twist':'C','entries':result,'success':True},indent=2)+'\n')
    print('PASS: all nine extended cyclic traces enclosed by exact rational arithmetic.')


if __name__=='__main__':main()
