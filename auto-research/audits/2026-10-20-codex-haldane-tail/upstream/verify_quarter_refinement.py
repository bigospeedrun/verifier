"""Exact certificate using the four octahedral twists and resolved input moments.

The analytic spatial-transfer premises remain conditional. All scalar
acceptance decisions, polynomial interval checks, and covering decisions
use rational arithmetic. See the note for the sector recurrence proof.
"""
from decimal import localcontext
from fractions import Fraction as Q
from math import comb
from pathlib import Path
import json

from sector_bounds import (rounded, power, real_power, root, significant_upper,
                           decimal, defect, f, residual, nonnegative_on_interval)
from verify_gap_improvement import exp_upper as taylor_upper
from verify_local_energy import certificate
import sector_bounds as arithmetic

# The ninth recurrence step reaches defects below 10^-800. This setting
# affects this checker process only; retained certificates keep their grids.
arithmetic.GRID = 10**1000
arithmetic.ROOT_MARGIN = Q(1,10**450)


def exp_upper(x):
    """Exact Taylor upper bound, scaled and squared with upward rounding."""
    if x<0:raise ValueError('Expected a nonnegative exponent.')
    steps=0
    while x>1:
        x/=2;steps+=1
    value=significant_upper(taylor_upper(x),40)
    for _ in range(steps):
        value=significant_upper(value*value,40)
    return value

ROOT = Path(__file__).resolve().parent
TARGET = Q(303,2000)
BETA = Q(49,4)


def main():
    if not __debug__:
        raise RuntimeError('Assertions must be enabled; do not run Python with -O.')
    checks = []

    def check(name, condition):
        if not condition:
            raise RuntimeError('Failed exact check: '+name)
        checks.append({'name':name,'passed':True})

    from verify_quarter_traces import moments as input_moments, enclosures as quarter_enclosures
    from verify_octahedral_sectors import certificate as group_certificate
    check('five-site energy certificate',certificate()['success'])
    check('octahedral character and projection identities',group_certificate()['success'])
    moments=input_moments()
    quarter=quarter_enclosures()
    fixed=json.loads((ROOT/'independent_results/quarter_filters.json').read_text())
    supports={s:(-Q(v[0]),Q(v[1])) for s,v in fixed['supports'].items()}
    check('four sector supports',set(supports)=={'A','B','E','V'})
    filter_records=[]
    for rec in fixed['filters']:
        sector,sign,cap=rec['sector'],rec['sign'],Q(rec['cap'])
        p=rec['quartic']
        check(f'{sector},{sign}: filter domain',len(p)==5 and sign in (-1,1) and cap>0 and cap==(-supports[sector][0] if sign<0 else supports[sector][1]))
        c=[sum(p[i]*p[k-i] for i in range(5) if 0<=k-i<5) for k in range(9)]
        upper=sum(a*moments[k+4][sector+('hi' if a>=0 else 'lo')] for k,a in enumerate(c))
        shifted=[sum(comb(i,j)*a*sign**i*cap**(i-j) for i,a in enumerate(p) if i>=j) for j in range(5)]
        check(f'{sector},{sign}: full exterior ray',all(x>0 for x in shifted) and cap**4*shifted[0]**2>upper and upper==Q(rec['moment_sum_upper']))
        filter_records.append(rec)
    check('both rays in every sector',{(r['sector'],r['sign']) for r in filter_records}=={(s,sgn) for s in supports for sgn in (-1,1)})

    # Polynomial duals are fixed rational inputs. Bernstein subdivision
    # proves their sign at every point in the support, including contacts.
    lp = {}
    polynomial_records = []
    for rec in json.loads((ROOT/'independent_results/quarter_moment_polynomials.json').read_text()):
        m, direction, sector = rec['moment'],rec['direction'],rec['sector']
        c = list(map(Q,rec['coefficients']))
        check(f'polynomial {sector},{m},{direction}: degree and moment domain',
              m>=12 and len(c)==9 and direction in ('upper','lower') and sector in ('A','B','E','V'))
        g = c+[Q(0)]*(m-3-len(c))
        g[-1] -= 1
        if direction=='lower':
            g = [-x for x in g]
        proof = nonnegative_on_interval(g,*supports[sector])
        value = sum(a*moments[k+4][sector+('hi' if (a>=0)==(direction=='upper') else 'lo')]
                    for k,a in enumerate(c))
        check(f'polynomial {sector},{m},{direction}: stored bound reproduced', value==Q(rec['bound']))
        lp[sector,m,direction] = (rounded(value,direction=='upper') if value>=0
                                     else -rounded(-value,direction!='upper'))
        polynomial_records.append({'sector':sector,'moment':m,'direction':direction,'bound':str(value),**proof})

    m12={s:rounded(moments[12][s+'hi']) for s in supports}
    absolute={s:max(-a,b) for s,(a,b) in supports.items()}
    for s in supports:
        check(f'{s}: twelfth-moment cap domain',0<absolute[s]**12<m12[s]<2*absolute[s]**12)

    def component(s,m):
        cap=power(absolute[s],m)+real_power(m12[s]-absolute[s]**12,Q(m,12))
        if m%2:
            cap=min(cap,m12[s]*power(supports[s][1],m-12))
        return min(cap,lp.get((s,m,'upper'),cap))

    def I(m):return component('A',m)+component('B',m)
    def O(m):return component('E',m)
    def J(m):return I(m)+2*O(m)
    def N(m):return sum(component(s,m) for s in ('B','E','V'))
    def Z(m):return J(m)+3*N(m)
    def lower_N(m):return sum(lp[s,m,'lower'] for s in ('B','E','V'))

    trial = json.loads((ROOT/'independent_results/trial84.json').read_text())
    tu,tv = int(trial['one_bond_numerator']),int(trial['norm'])
    check('trial84: negative shifted Rayleigh quotient', trial['length']==84 and tv>0
          and 500000*tu+700741*tv==int(trial['shift_comparison_integer'])<0)

    def seed(m,t,n):
        D = significant_upper(real_power(Z(m),t))
        EP = significant_upper(real_power(J(m)-lower_N(m),t))
        EC = significant_upper(real_power(I(m)-lp.get(('E',m,'lower'),Q(0)),t))
        Icap, Jcap = (D+3*EP+8*EC)/12, (D+3*EP)/4
        exponent = Q(120,m)
        check(f'seed {m},{t}: unique modulus dominance',
              m%2==0 and 12<=m<=n and t>=1 and
              0<Icap<=Jcap<=D and 2*real_power(D/2,exponent)<1)
        # Decimal bisection proposes v; the rational comparison below proves it.
        with localcontext() as ctx:
            ctx.prec=80
            dd,ii,jj,rr=map(decimal,(D,Icap,Jcap,exponent))
            zero=decimal(Q(0))
            lo,hi=dd/2,min(decimal(Q(1)),ii)
            for _ in range(200):
                s=(lo+hi)/2
                values=[x**rr+2*(y/2)**rr+3*((dd-s-x-y)/3)**rr
                        for x,y in [(zero,zero),(ii-s,zero),(ii-s,jj-ii),(zero,jj-s)]]
                if s**rr+max(values)<1:
                    lo=s
                else:
                    hi=s
            v=Q(int(lo*10**24)-1,10**24)
        check(f'seed {m},{t}: leading moment from trial120',
              D/2<v<=min(1,Icap) and real_power(v,exponent)+residual(v,exponent,D,Icap,Jcap)<1)
        exponent=Q(n,m)
        denominator=real_power(v,exponent,False)
        i=significant_upper(real_power(Icap-v,exponent)/denominator)
        j=significant_upper(max(2*real_power((Jcap-v)/2,exponent),
                              real_power(Icap-v,exponent)+2*real_power((Jcap-Icap)/2,exponent))/denominator)
        r=significant_upper(residual(v,exponent,D,Icap,Jcap)/denominator)
        q=significant_upper(defect(real_power(Z(2*n)-1,t)))
        check(f'seed {m},{t}: sector and purity domains', 0<i<=j<=r<1 and 0<q<1)
        return {'m':m,'t':t,'n':n,'beta':BETA*t,'D':D,'I':Icap,'J':Jcap,
                'v':v,'i':i,'j':j,'r':r,'q':q}

    initial = seed(26,Q(2),42)
    short_seeds = {m:seed(m,Q(2),60) for m in (18,20,22,24,26,28,30,32)}
    rows, levels = [], []
    i,j,r,q = [initial[k] for k in ('i','j','r','q')]
    for k in range(10):
        n,beta=42*2**k,BETA*2*2**k
        row={'k':k,'n':n,'beta':beta,'i':i,'j':j,'r':r,'p':defect(r),'q':q}
        rows.append(row)
        if k==9:
            break
        dd=2*r+r*r
        dj=(dd+3*(2*j+j*j))/4
        di=(dd+3*(2*j+j*j)+8*(2*i+i*i))/12
        check(f'row {k}: doubled-temperature dominance', (1+dd)**2/2<1-q)

        def R(h):
            return max((dd+h)**2/3,
                       (di+h)**2+(dd-di)**2/3,
                       (di+h)**2+(dj-di)**2/2+(dd-dj)**2/3,
                       (dj+h)**2/2+(dd-dj)**2/3)

        with localcontext() as ctx:
            ctx.prec=560
            dd0,di0,dj0,qq=map(decimal,(dd,di,dj,q))
            def rd(h):
                return max((dd0+h)**2/3,(di0+h)**2+(dd0-di0)**2/3,
                           (di0+h)**2+(dj0-di0)**2/2+(dd0-dj0)**2/3,
                           (dj0+h)**2/2+(dd0-dj0)**2/3)
            lo,hi=decimal(Q(0)),qq+dd0*dd0
            while 2*hi-hi*hi<=qq+rd(hi):
                hi*=2
                if hi>=(1-dd0)/2:
                    raise ArithmeticError('No leading-moment proposal.')
            for _ in range(160):
                mid=(lo+hi)/2
                if 2*mid-mid*mid>qq+rd(mid):
                    hi=mid
                else:
                    lo=mid
            h=significant_upper(Q(hi)*Q(1000000000001,1000000000000))
        v=1-h
        check(f'row {k}: sector-resolved leading lower bound',
              (1+dd)/2<v<1 and q+R(h)<2*h-h*h)
        inext=significant_upper((di+h)**2/v**2)
        jnext=significant_upper(max((dj+h)**2/2,(di+h)**2+(dj-di)**2/2)/v**2)
        rnext=significant_upper(R(h)/v**2)
        pnext=defect(rnext)
        qnext=significant_upper(f(2*q-q*q+pnext*(1-q)**2))
        check(f'row {k}: propagated sector domains', 0<inext<=jnext<=rnext<1 and 0<qnext<1)
        row.update({'h':h,'dD':dd,'dI':di,'dJ':dj})
        s=(dd+h)/v
        c,rho0,rho1=root(v,n,False),root(r,n),root(s,n)
        check(f'level {k}: interpolation domains', 0<c<1 and 0<rho0<1 and 0<rho1<1)
        levels.append({'name':str(k),'n':n,'beta':beta,'c':c,'r':r,'s':s,'rho0':rho0,'rho1':rho1})
        i,j,r,q=inext,jnext,rnext,qnext
        print(f'row {k}: certified',flush=True)

    def interval_lower(level,A,B):
        if not level['n']<=A<=B:
            return Q(0)
        a=rounded(level['r']*power(level['rho0'],A-level['n']))
        b=rounded(level['s']*power(level['rho1'],A-level['n']))
        if b>=1:
            return Q(0)
        return rounded(power(level['c'],B,False)*(1-b)/(1+a)**2,False)

    thresholds={l['name']:exp_upper(l['beta']*TARGET) for l in levels}
    thresholds={k:(1+x*x)/(1+x)**2 for k,x in thresholds.items()}

    def short_lower(L):
        denominator=Z(L)
        if denominator<=0:
            raise ArithmeticError('Nonpositive partition-function upper bound.')
        candidates=[]
        for m,ss in short_seeds.items():
            if m>L:
                continue
            rr=Q(L,m)
            numerator=real_power(ss['v'],rr,False)
            if L%2:
                numerator-=residual(ss['v'],rr,ss['D'],ss['I'],ss['J'])
            candidates.append((rounded(max(Q(0),numerator)/denominator**2,False),m))
        return max(candidates)

    # Explicit checks for the short-length ladder. Larger lengths will be
    # supplied by the strongest bound; no unchecked monotonicity in L is used.
    short=[]
    for start,target in [(18,Q(63,1000)),(20,Q(119,1000)),(22,Q(29,200))]:
        for L in (start,start+1):
            value,m=short_lower(L)
            check(f'short L={L}: gap > {target}', value>Q(1,2) and (1+exp_upper(BETA*target)**2)/(1+exp_upper(BETA*target))**2<value)
            short.append({'L':L,'target':target,'m':m,'purity_lower':value})

    value,m=short_lower(18)
    check('short L=18: gap > 11/125', value>Q(1,2) and (1+exp_upper(BETA*Q(11,125))**2)/(1+exp_upper(BETA*Q(11,125)))**2<value)
    short.append({'L':18,'target':Q(11,125),'m':m,'purity_lower':value})

    tail_start=3*rows[-1]['n']//2
    A,intervals=24,[]
    short_threshold=exp_upper(BETA*TARGET)
    short_threshold=(1+short_threshold**2)/(1+short_threshold)**2
    while A<tail_start:
        candidates=[]
        for level in levels:
            threshold=thresholds[level['name']]
            if interval_lower(level,A,A)<=threshold:
                continue
            low,high=A,tail_start-1
            while low<high:
                mid=(low+high+1)//2
                if interval_lower(level,A,mid)>threshold:
                    low=mid
                else:
                    high=mid-1
            candidates.append((low,level))
        if not candidates:
            if A>150:
                raise ArithmeticError(f'Uncovered length {A}.')
            value,m=short_lower(A)
            check(f'short L={A}: gap > {TARGET}', Q(1,2)<value<1 and value>short_threshold)
            short.append({'L':A,'target':TARGET,'m':m,'purity_lower':value})
            A+=1
            continue
        B,level=max(candidates,key=lambda item:item[0])
        value=interval_lower(level,A,B)
        check(f'interval {A}..{B}: gap > {TARGET}', Q(1,2)<value<1 and value>thresholds[level['name']])
        intervals.append({'first':A,'last':B,'level':level['name'],'beta':level['beta'],'purity_lower':value})
        A=B+1
    lengths={x['L'] for x in short if x['target']==TARGET}
    for interval in intervals:
        lengths.update(range(interval['first'],interval['last']+1))
    check('every finite integer length covered', lengths==set(range(24,tail_start)))

    tail=rows[-1]
    w0=significant_upper(tail['q']*Q(101,100))
    C,B,xmax=Q(6),Q(15,2),Q(1,100)
    check('tail starting invariant', tail['p']**3<=w0**2 and tail['q']<=w0 and 0<w0<=xmax**3)
    ac,qc=2+xmax,2+3*xmax
    check('tail invariant propagates', ac**2/(2*(1-ac*xmax**2)**2)<=3 and
          qc**2/(2*(1-qc*xmax**3)**2)<=3 and 3**3<C**2 and 3<=C)
    check('tail interpolation coefficients', xmax**2<=Q(1,3) and ac*xmax**2<=Q(1,3)
          and ac**3<9 and 2*(1+3*xmax)+3+2<B and B*xmax**3<Q(1,2))
    E=exp_upper(tail['beta']*TARGET)
    check('tail exponential comparisons', E*C*w0<1 and E*B*w0/(1-B*w0)<1)
    check('tail all-integer cover', tail['n']%2==0 and tail_start==3*tail['n']//2)

    def serialize(x):
        if isinstance(x,Q):
            return str(x)
        if isinstance(x,dict):
            return {str(k):serialize(v) for k,v in x.items()}
        if isinstance(x,(list,tuple)):
            return list(map(serialize,x))
        return x
    result={'source_commit':'adc7f1241b42e322a6451854ab7e4b4c146bf78a',
            'statement':'Conditional on the cited premises: unique ground state and gamma_L > 303/2000 for every integer L >= 24, J=1',
            'additional_bounds':[{'gap':'.063','minimum_length':18},{'gap':'.119','minimum_length':20},
                                 {'gap':'.145','minimum_length':22}],
            'isolated_short_bound':'gamma_18 > .088, unique ground state',
            'quarter_trace_enclosures':quarter,'moment_intervals':moments,'filters':filter_records,'polynomial_certificates':polynomial_records,
            'supports':supports,
            'seed':initial,'short_seeds':list(short_seeds.values()),'rows':rows,'levels':levels,
            'short_lengths':short,'finite_intervals':intervals,
            'tail':{'start':tail_start,'n0':tail['n'],'beta0':tail['beta'],'w0':w0,'C':C,'B':B},
            'root_directions':'Every Decimal proposal is accepted by directed rational integer-power comparisons',
            'exponential_bounds':'Rational Taylor upper bound after halving, followed by 40-digit upward-rounded squaring',
            'product_rounding':'Outward on a 10^-1000 grid; recurrence bounds rounded upward to 15 significant digits',
            'checks':checks,'success':True}
    (ROOT/'independent_results/quarter_refinement.json').write_text(json.dumps(serialize(result),indent=2)+'\n')
    print(f'PASS: {len(checks)} exact checks; {len(intervals)} finite intervals; tail starts at {tail_start}.')
    print('gamma_L > 0.1515 for every integer L >= 24; unique ground state; conditional on cited premises.')
    print('Finite intervals:',[(x['first'],x['last'],x['level']) for x in intervals])
    print('Short main lengths:',sorted(x['L'] for x in short if x['target']==TARGET))


if __name__=='__main__':
    main()
