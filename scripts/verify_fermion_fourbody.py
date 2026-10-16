# Retained from the 12 October torus candidate package; paths adapted for this layout.
# Internal AI reconstruction, not external human review. See AI_CONTRIBUTIONS.md.
from fractions import Fraction as F
from functools import lru_cache
from math import comb, factorial
from itertools import combinations
from pathlib import Path
import json, time
BASE=Path(__file__).resolve().parent.parent
OUT=BASE/'output/checks'; OUT.mkdir(parents=True,exist_ok=True)
rows=[]
for line in (BASE/'paper/data/fermionic/rows.txt').read_text().splitlines():
    if not line[0].isspace():
        x=line.split(); rows.append([int(x[0]),int(x[1]),{}]);rest=x[2:]
    else:rest=line.split()
    for term in rest:
        pj,a=term.split(':');rows[-1][2][tuple(map(int,pj))]=int(a)
@lru_cache(None)
def U(c,z,T,p):
    if min(z,p)<0 or max(z,p)>T:return 0
    return sum((-1)**(z-h)*comb(z,h)*comb(T-z,p-h)*c**(p-h) for h in range(max(0,p+z-T),min(p,z)+1))
@lru_cache(None)
def V(r,D,T,p,j,k):
    if r>j+k:return 0
    return U(1,r,j+k,j)*U(1,D-r,T-r,p)
@lru_cache(None)
def pow2(e):return F(2)**e

def matmul(A,B):
    return [[sum((a*b for a,b in zip(row,col)),F(0)) for col in zip(*B)] for row in A]
def psd_exact(A):
    A=[r[:] for r in A];n=len(A);rank=0
    for i in range(n):
        if A[i][i]<0:return False,rank,'negative pivot'
        if A[i][i]==0:
            if any(A[i][j]!=0 for j in range(i+1,n)):return False,rank,'zero diagonal nonzero row'
            continue
        rank+=1
        p=A[i][i]
        for j in range(i+1,n):
            for k in range(j,n):
                A[j][k]-=A[i][j]*A[i][k]/p
                A[k][j]=A[j][k]
    return True,rank,None
quads={D:[A for A in combinations(range(D+2),4) if sum(A)==D+1] for D in range(1,24)}
results=[];start=time.time()
for D in range(1,24):
    rs=list(range(1,D+1,2));n=len(rs);Y=[[F(0) for _ in rs] for _ in rs]
    for t,l,row in rows:
        for (p,j),a in row.items():
            i=p+j-t
            for (q,ll),b in row.items():
                k=q+ll-t;T=p+j+k
                if T<D or j==k or ll==i:continue
                left=[V(r,D,T,p,j,k)*2**((r-1)//2) for r in rs]
                right=[V(r,D,T,q,ll,i)*2**((r-1)//2) for r in rs]
                if not any(left) or not any(right):continue
                base=-F(a*b,10**14)*pow2(2-2*T+p+q-t)*F(factorial(i)*factorial(k)*factorial(t),factorial(T-D))
                for ir,x in enumerate(left):
                    if not x:continue
                    for js,y in enumerate(right):
                        if y:Y[ir][js]+=base*x*y
    assert Y==[list(c) for c in zip(*Y)]
    Z=[[F(0) for _ in rs] for _ in rs]
    for A in quads[D]:
        L=[]
        for r in rs:
            val=0
            for x,y in combinations(A,2):
                j,k=[a for a in A if a not in (x,y)];p=x+y-1
                order=[x,y,j,k];sgn=(-1)**sum(order[a]>order[b] for a in range(4) for b in range(a+1,4))
                val+=sgn*(x-y)*factorial(p)*factorial(j)*factorial(k)*V(r,D,D,p,j,k)
            L.append(pow2((1-2*D+r)//2)*val)
        den=1
        for a in A:den*=factorial(a)
        for i,x in enumerate(L):
            for j,y in enumerate(L):Z[i][j]+=x*y/den
    u=[F(1,factorial(r)*factorial(D-r)) for r in rs]
    B=[[-u[i]*Y[i][j]*u[j]+((2*(rs[i]==1)+F(3,10**6))*u[i] if i==j else 0) for j in range(n)] for i in range(n)]
    M=matmul(matmul(Z,B),Z)
    assert M==[list(c) for c in zip(*M)]
    ok,rank,why=psd_exact(M)
    row={'D':D,'dimension':n,'positive_semidefinite':ok,'rank':rank,'failure':why}
    results.append(row)
    print(json.dumps(row),flush=True)
out={'method':'Exact rational reconstruction of source equations Y,Z,B,M; symmetric Schur-complement PSD pivots, including exact zero-row checks.','all_psd':all(x['positive_semidefinite'] for x in results),'elapsed_seconds':time.time()-start,'results':results}
(OUT/'fermion_fourbody.json').write_text(json.dumps(out,indent=2))
print(json.dumps({'all_psd':out['all_psd'],'elapsed_seconds':out['elapsed_seconds']}),flush=True)
