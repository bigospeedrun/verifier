"""Exact finite-group identities behind the four-twist sector decomposition.

The analytic representation of the group on the spatial Hilbert space is
an upstream premise. This checks the finite character algebra, not that
infinite-dimensional construction or its physical trace identity.
"""
from itertools import permutations,product
from fractions import Fraction as Q
from pathlib import Path
import json

ROOT=Path(__file__).resolve().parent

def certificate():
 if not __debug__:raise RuntimeError('Assertions must be enabled.')
 def parity(p):return (-1)**sum(p[i]>p[j] for i in range(len(p)) for j in range(i+1,len(p)))
 axes=((1,1,1),(1,-1,-1),(-1,1,-1),(-1,-1,1))
 pairings=(((0,1),(2,3)),((0,2),(1,3)),((0,3),(1,2)))
 def norm_pairing(v):return tuple(sorted(tuple(sorted(x)) for x in v))
 elements=[]
 for p in permutations(range(3)):
  for signs in product((-1,1),repeat=3):
   if parity(p)*signs[0]*signs[1]*signs[2]!=1:continue
   out=[]
   for x in axes:
    y=tuple(signs[j]*x[p[j]] for j in range(3))
    out.append(next(k for k,a in enumerate(axes) if y==a or y==tuple(-z for z in a)))
   out=tuple(out);sgn=parity(out)
   e=sum(norm_pairing(tuple(tuple(out[i] for i in v) for v in pair))==norm_pairing(pair) for pair in pairings)-1
   standard=sum(out[i]==i for i in range(4))-1
   chars=(1,sgn,e,standard,sgn*standard)
   trace=sum(signs[j] for j in range(3) if p[j]==j)
   assert chars[-1]==trace
   elements.append({'permutation':out,'characters':chars,'rotation_trace':trace})
 assert len(elements)==24 and len({x['permutation'] for x in elements})==24
 index={x['permutation']:i for i,x in enumerate(elements)}
 mul=[[index[tuple(x['permutation'][y['permutation'][j]] for j in range(4))] for y in elements] for x in elements]
 identity=index[(0,1,2,3)]
 inverse=[next(j for j in range(24) if mul[i][j]==identity and mul[j][i]==identity) for i in range(24)]
 dims=(1,1,2,3,3)
 assert sum(d*d for d in dims)==24
 for a in range(5):
  for b in range(5):
   assert sum(x['characters'][a]*x['characters'][b] for x in elements)==24*(a==b)
 projectors=[[Q(d*x['characters'][a],24) for x in elements] for a,d in enumerate(dims)]
 for a,p in enumerate(projectors):
  assert all(p[i]==p[inverse[i]] for i in range(24))
  for b,q in enumerate(projectors):
   c=[Q(0)]*24
   for i in range(24):
    for j in range(24):c[mul[i][j]]+=p[i]*q[j]
   assert c==(p if a==b else [Q(0)]*24)
 assert [sum(p[i] for p in projectors) for i in range(24)]==[Q(i==identity) for i in range(24)]
 classes={}
 for x in elements:
  key=tuple(x['characters'])
  classes.setdefault(key,[]).append(x)
 assert sorted(map(len,classes.values()))==[1,3,6,6,8]
 pi_classes=[(c,xs) for c,xs in classes.items() if xs[0]['rotation_trace']==-1]
 assert len(pi_classes)==2
 edge=next(c for c,xs in pi_classes if len(xs)==6)
 face=next(c for c,xs in pi_classes if len(xs)==3)
 assert tuple(a-b for a,b in zip(edge,face))==(0,-2,-2,2,0)
 # Equality of the physical pi-twisted traces gives T_n = B_n + E_n.
 M=((1,4,5,3),(1,0,1,-1),(1,1,-1,0),(1,-2,-1,1))
 inverse_numerators=((1,9,8,6),(1,-3,8,-6),(2,6,-8,0),(3,-9,0,6))
 assert all(sum(inverse_numerators[i][k]*M[k][j] for k in range(4))==24*(i==j) for i in range(4) for j in range(4))
 return {'group_order':24,'characters_order':['A','B','E','T','V'],
         'classes':[{'size':len(xs),'rotation_trace':xs[0]['rotation_trace'],'characters':list(c)} for c,xs in classes.items()],
         'projector_algebra_verified':True,'pi_class_difference':[0,-2,-2,2,0],
         'moment_relation':'T_n = B_n + E_n for n >= 4',
         'effective_sector_order':['A','B','E','V'],'effective_multiplicities':[1,4,5,3],
         'twist_order':['identity','pi','2pi/3','pi/2'],'forward_matrix':M,
         'inverse_numerators':inverse_numerators,'inverse_denominator':24,'success':True}

if __name__=='__main__':
 result=certificate()
 (ROOT/'independent_results/octahedral_sectors.json').write_text(json.dumps(result,indent=2)+'\n')
 print('PASS: 24 group elements, character orthogonality, central projector algebra, and four-twist inversion.')
