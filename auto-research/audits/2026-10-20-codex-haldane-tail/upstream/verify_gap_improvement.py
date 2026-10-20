"""A small exact certificate improving the paper's gap constant to 47/10000.

This is conditional on Proposition 3.1, Lemma 4.2, Proposition 4.3 and
Proposition 5.5 of OpenAI, The periodic spin-one Haldane gap (2026-09-24).
It is an extension of that argument, not an independent Haldane-gap proof.
Only Python's standard library is required. All assertions are rational.
"""
from decimal import Decimal, localcontext
from fractions import Fraction as Q
import json
from pathlib import Path


def f(x):
    assert 0 <= x < 1
    return x*x / (2*(1-x)**2)


def exp_upper(x):
    """Taylor polynomial plus a geometric bound on the positive tail."""
    assert x >= 0
    order=4*(x.numerator//x.denominator)+64
    term=total=Q(1)
    for k in range(1,order+1):
        term*=x/k
        total+=term
    rho=x/(order+2)
    assert 0<=rho<1
    return total + term*x/(order+1)/(1-rho)


def main():
    if not __debug__:
        raise RuntimeError('Assertions must be enabled; do not run Python with -O.')
    rows=[('0.0084513','0.0054986'),
          ('2.59e-4','6.45e-5'),
          ('1.70e-7','8.35e-9'),
          ('6.07e-14','1.40e-16'),
          ('7.39e-27','3.93e-32'),
          ('1.10e-52','3.09e-63')]
    target=Q(47,10000)
    certificate=[]
    for j,(ps,qs) in enumerate(rows):
        p,q=Q(ps),Q(qs)
        assert 0<p<1 and 0<q<1
        if j:
            assert f(1-(1-pold)**2*(1-qold))<=p
            # Use the new upward-rounded p in the second inequality.
            assert f(1-(1-qold)**2*(1-p))<=q
        n=2304*2**j
        beta=784*2**j
        row={'j':j,'n':n,'beta':beta,'p':ps,'q':qs}
        if j<5:
            # Interpolation: T(L,beta) >= K for every even n <= L <= 2n.
            K=(1-p)**2*(1-q)
            assert K>Q(1,2)
            # w_ground >= K; exp(-beta*gap) <= (1-K)/K.
            odds=K/(1-K)
            exp_hi=exp_upper(target*beta)
            assert exp_hi<odds
            row.update({'maximum_length':2*n,'purity_lower':str(K),
                        'relative_margin':float(odds/exp_hi-1)})
        else:
            # Proposition 4.3 covers every even L >= n from this point onward.
            u=max(p,q); C=Q(5)
            G=sum((1-u)**(-k) for k in (1,2,3))**2/2
            assert 0<u<Q(1,6) and G<C and C*u<1 and C*(1-3*u)>3
            odds=1/(C*u)
            exp_hi=exp_upper(target*beta)
            assert exp_hi<odds
            with localcontext() as ctx:
                ctx.prec=60
                value=(Decimal(odds.numerator)/Decimal(odds.denominator)).ln()/beta
            row.update({'C':str(C),'u':str(u),
                        'tail_gap_bound':'log(10^53/55)/25088',
                        'tail_gap_bound_decimal':str(value),
                        'relative_margin':float(odds/exp_hi-1)})
        certificate.append(row)
        pold,qold=p,q
    assert certificate[4]['maximum_length']==certificate[5]['n']
    result={'source_commit':'adc7f1241b42e322a6451854ab7e4b4c146bf78a',
            'dependency':'Paper input lemmas and purity bootstrap',
            'finite_gap_statement':'gamma_L > 47/10000 for every even L >= 2304',
            'thermodynamic_statement':'liminf gamma_L >= 47/10000',
            'coupling_normalization':'J = 1',
            'all_assertions_exact_rational':True,'success':True,'steps':certificate}
    output=Path(__file__).resolve().parent/'independent_results'/'short_certificate.json'
    output.parent.mkdir(exist_ok=True)
    output.write_text(json.dumps(result,indent=2)+'\n')
    print('PASS: all exact inequalities for gamma_L > 0.0047, even L >= 2304.')
    print('The analytic hypotheses remain those of the cited paper.')
    print('Tail bound:',certificate[-1]['tail_gap_bound_decimal'])


if __name__=='__main__':
    main()
