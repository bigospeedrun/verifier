"""Exact Gaussian-coordinate Horner errors and four-twist moment intervals."""
from fractions import Fraction as Q
from math import factorial,isqrt
from pathlib import Path
import json
from thermal_error_bounds import errors as real_errors
from verify_extended_cyclic import enclosures as cyclic_enclosures
from verify_local_energy import certificate as local_energy
from verify_octahedral_sectors import certificate as group_certificate

ROOT=Path(__file__).resolve().parent

def gaussian_errors(n):
 if not 4<=n<=12:raise ValueError('Outside the certified thermal range.')
 dims={0:1}
 for _ in range(n):
  nxt={}
  for m,d in dims.items():
   for a in (-1,0,1):nxt[m+a]=nxt.get(m+a,0)+d
  dims=nxt
 assert sum(dims.values())==3**n
 e2=0;maximum=0
 for d in dims.values():
  # Two independent real floors have complex vector norm <= sqrt(2d).
  dn=isqrt(2*d)+1
  e=281*(dn+1)+1 if n==4 else (384*(dn+1)+n-1)//n+1
  e2+=d*e*e;maximum=max(maximum,e)
 return isqrt(e2)+1,maximum

def enclosure(n,total,E):
 r=isqrt(total);assert r*r<=total<(r+1)**2 and r>E
 x=Q(49,4)*n*(Q(3,2)-Q(700741,500000));term=s=Q(1)
 for j in range(1,101):term*=x/j;s+=term
 assert 0<x<15 and x/(101-x)<1
 return s*(r-E)**2/2**110,(s+term)*(r+1+E)**2/2**110

def enclosures():
 if not __debug__:raise RuntimeError('Assertions must be enabled.')
 assert local_energy()['success']
 rows=json.loads((ROOT/'independent_results/quarter_twist_totals.json').read_text())
 assert [r['n'] for r in rows]==list(range(4,13))
 coeff=[Q(98)**j/factorial(j) for j in range(281)];den=sum(coeff)
 coeff=[int(2**55*x/den) for x in coeff]
 assert max(j for j,x in enumerate(coeff) if x)==191 and sum(coeff)<=2**55
 assert 2**55*3**98<2**280
 out=[]
 for r in rows:
  n=r['n'];assert r['twist']==3 and r['beta']=='49/4'
  assert (r['Q'],r['J'],r['last_nonzero'])==(2**55,280,191)
  assert r['multiplicity_sum']==3**n and r['maximum_coordinate_row_l1']<=80
  E,emax=gaussian_errors(n)
  assert 80*(2*2**55+2*emax)<2**63
  assert (2**55+emax)**2*4*n<2**127
  assert 3**n*(2**55+emax)**2<2**256
  lo,hi=enclosure(n,int(r['total']),E)
  out.append({'n':n,'lower':str(lo),'upper':str(hi),'frobenius_error_Q_units':E,'maximum_column_error_Q_units':emax})
 return out

def moments():
 assert group_certificate()['success']
 source=ROOT/'source/verification/computations/evidence/source1'
 old=json.loads((source/'thermal-run/interval-summary.json').read_text())['entries']
 precision=json.loads((source/'error-bounds.json').read_text())
 assert precision['Q']==2**55 and precision['J']==280
 c={r['n']:(Q(r['lower']),Q(r['upper'])) for r in cyclic_enclosures()}
 d={r['n']:(Q(r['lower']),Q(r['upper'])) for r in enclosures()}
 coeff={'A':(1,9,8,6),'B':(1,-3,8,-6),'E':(2,6,-8,0),'V':(3,-9,0,6)}
 out={}
 for n in range(4,13):
  E,_,_=real_errors(n)
  zz=[enclosure(n,int(next(e['W'] for e in old if e['n']==n and e['tw']==tw)),E) for tw in (0,1)]+[c[n],d[n]]
  out[n]={}
  for s,p in coeff.items():
   out[n][s+'lo']=sum(a*zz[k][int(a<0)] for k,a in enumerate(p))/24
   out[n][s+'hi']=sum(a*zz[k][int(a>=0)] for k,a in enumerate(p))/24
   assert out[n][s+'lo']<out[n][s+'hi']
 return out

if __name__=='__main__':
 result={'quarter_twist':enclosures(),'sector_moments':{n:{k:str(x) for k,x in row.items()} for n,row in moments().items()},'success':True}
 (ROOT/'independent_results/quarter_twist_enclosures.json').write_text(json.dumps(result,indent=2)+'\n')
 print('PASS: all nine quarter-twist traces and four resolved sector tables enclosed exactly.')
