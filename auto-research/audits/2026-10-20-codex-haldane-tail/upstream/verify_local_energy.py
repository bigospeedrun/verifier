"""Integer LDL/Sylvester certificate: H_open,5 > -35/6.

Summing translated five-site open blocks gives H_L(g) >= -35 L/24
for every ring length L>=5 and each of the three boundary twists.
An open path's seam rotation is removed by on-site unitary rotations.
"""
from itertools import product
from pathlib import Path
import json

ROOT=Path(__file__).resolve().parent


def certificate():
    if not __debug__:raise RuntimeError('Assertions must be enabled.')
    result=[];dimension=0
    for m in range(6):
        words=[w for w in product((-1,0,1),repeat=5) if sum(w)==m]
        d=len(words);index={w:i for i,w in enumerate(words)}
        H=[[0]*d for _ in range(d)]
        for i,w in enumerate(words):
            H[i][i]=sum(w[j]*w[j+1] for j in range(4))
            for j in range(4):
                for step in (-1,1):
                    v=list(w);v[j]+=step;v[j+1]-=step
                    if abs(v[j])<=1 and abs(v[j+1])<=1:
                        H[i][index[tuple(v)]]+=1
        assert all(H[i][j]==H[j][i] for i in range(d) for j in range(d))
        A=[[6*H[i][j]+35*(i==j) for j in range(d)] for i in range(d)]
        previous=1;pivots=[]
        for k in range(d):
            pivot=A[k][k]
            assert pivot>0
            pivots.append(str(pivot))
            for i in range(k+1,d):
                for j in range(k+1,d):
                    numerator=pivot*A[i][j]-A[i][k]*A[k][j]
                    assert numerator%previous==0
                    A[i][j]=numerator//previous
            previous=pivot
        dimension+=(1 if m==0 else 2)*d
        result.append({'magnetization':m,'dimension':d,'leading_principal_minors':pivots})
    assert dimension==3**5
    return {'length':5,'boundary':'open','strict_energy_lower_bound':'-35/6',
            'ring_energy_lower_bound_per_site':'-35/24','minimum_ring_length':5,
            'blocks':result,'success':True}


def main():
    result=certificate()
    (ROOT/'independent_results/local_energy.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PASS: every leading principal minor of 6 H_open,5 + 35 I is positive.')


if __name__=='__main__':main()
