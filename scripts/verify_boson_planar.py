# Retained from the 12 October torus candidate package; paths adapted for this layout.
# Internal AI reconstruction, not external human review. See AI_CONTRIBUTIONS.md.
"""Independent exact rational reconstruction from frozen integer data.
Uses explicit normal-ordered CCR formula, not the upstream recursive few-body extractor.
No upstream Python is imported or executed. One process; standard library only.
"""
from fractions import Fraction as F
from math import factorial as fac, comb
from functools import lru_cache
from collections import Counter,defaultdict
from pathlib import Path
import json,time,os
BASE=Path(__file__).resolve().parent.parent; start=time.time(); DEN=10**24
OUT=BASE/'output/checks'; OUT.mkdir(parents=True,exist_ok=True)
@lru_cache(None)
def basis(n,d,lo=0):
 if n==0:return ((),) if d==0 else ()
 if n==1:return ((d,),) if d>=lo else ()
 return tuple((i,)+x for i in range(lo,d//n+1) for x in basis(n-1,d-i,i))
@lru_cache(None)
def met(t):return facprod(fac(v) for v in Counter(t).values())*facprod(fac(j) for j in t)
def facprod(xs):
 r=1
 for x in xs:r*=x
 return r
@lru_cache(None)
def mult(t):return facprod(fac(v) for v in Counter(t).values())
def zeros(n,m):return [[F(0) for _ in range(m)]for _ in range(n)]
def transpose(a,ncols=None):return list(map(list,zip(*a))) if a else [[] for _ in range(ncols or 0)]
def mm(a,b):
 if not a:return []
 n=len(b[0]) if b else 0;out=zeros(len(a),n)
 for i,row in enumerate(a):
  for k,x in enumerate(row):
   if x:
    for j,y in enumerate(b[k]):
     if y:out[i][j]+=x*y
 return out
def add(a,b,s=1):return [[x+s*y for x,y in zip(r,t)]for r,t in zip(a,b)]
def scale(a,s):return [[s*x for x in r]for r in a]
def kernel(a,ncols):
 a=[r[:] for r in a];piv=[];i=0
 for j in range(ncols):
  k=next((k for k in range(i,len(a)) if a[k][j]),None)
  if k is None:continue
  a[k],a[i]=a[i],a[k];v=a[i][j];a[i]=[x/v for x in a[i]]
  for k in range(len(a)):
   if k!=i and a[k][j]:
    v=a[k][j];a[k]=[x-v*y for x,y in zip(a[k],a[i])]
  piv.append(j);i+=1
 free=[j for j in range(ncols) if j not in piv];u=zeros(ncols,len(free))
 for c,j in enumerate(free):
  u[j][c]=F(1)
  for k,p in enumerate(piv):u[p][c]=-a[k][j]
 return u

def annih(t,labels):
 t=list(t);w=1
 for j in labels:
  n=t.count(j)
  if n==0:return None,0
  w*=n;t.remove(j)
 return tuple(t),w
@lru_cache(None)
def H(n,d):
 bs=basis(n,d);ix={x:i for i,x in enumerate(bs)};a=zeros(len(bs),len(bs))
 for col,t in enumerate(bs):
  for p in range(d+1):
   k=F(fac(p),2**(p+1))
   for c in range(p+1):
    left,w=annih(t,(c,p-c))
    if not w:continue
    for b in range(p+1):
     out=tuple(sorted(left+(b,p-b)))
     a[ix[out]][col]+=k*w/F(fac(b)*fac(p-b))
 return a
@lru_cache(None)
def S(n,d):
 if n==3:return add(mm(H(n,d),H(n,d)),H(n,d),-1)
 bs=basis(4,d);a=zeros(len(bs),len(bs))
 for p in range(d+1):
  q=d-p;v=[]
  for t in bs:
   wtot=0
   for i in range(p+1):
    l,w=annih(t,(i,p-i))
    if w:
     for j in range(q+1):
      _,w2=annih(l,(j,q-j));wtot+=w*w2
   v.append(wtot)
  k=F(fac(p)*fac(q),2**(d+2))
  for i in range(len(bs)):
   for j in range(len(bs)):a[i][j]+=k*v[i]*v[j]/met(bs[i])
 return a
@lru_cache(None)
def relative(n,d):
 bs=basis(n,d);prev=basis(n,d-1);ix={x:i for i,x in enumerate(prev)};a=zeros(len(prev),len(bs))
 for c,t in enumerate(bs):
  for j in set(t):
   if j:
    l,w=annih(t,(j,));a[ix[tuple(sorted(l+(j-1,))) ]][c]+=j*w
 return kernel(a,len(bs))
def raised(n,d,u):
 bs=basis(n,d);dst=basis(n,d+1);ix={x:i for i,x in enumerate(dst)};a=zeros(len(dst),len(bs))
 for c,t in enumerate(bs):
  for j in set(t):
   l,w=annih(t,(j,));a[ix[tuple(sorted(l+(j+1,))) ]][c]+=w
 return mm(a,u)
def form(a,n,d):return [[met(t)*x for x in row] for t,row in zip(basis(n,d),a)]
def congr(a,u):return mm(transpose(u),mm(a,u))
def exact_psd(a):
 a=[r[:]for r in a];piv=[]
 while a:
  assert all(a[i][j]==a[j][i] for i in range(len(a)) for j in range(i))
  assert all(a[i][i]>=0 for i in range(len(a)))
  k=next((i for i in range(len(a))if a[i][i]>0),None)
  if k is None:
   assert not any(x for r in a for x in r);break
  p=a[k][k];piv.append(str(p));ids=[i for i in range(len(a))if i!=k]
  a=[[a[i][j]-a[i][k]*a[k][j]/p for j in ids]for i in ids]
 return piv
rows=json.loads((BASE/'paper/data/bosonic/exact_shifted_certificate_rows.json').read_text());K={3:defaultdict(lambda:defaultdict(F)),4:defaultdict(lambda:defaultdict(F))}
def emit(n,c,a,b):
 if not c:return
 a=tuple(sorted(a));b=tuple(sorted(b));assert sum(a)==sum(b)
 K[n][sum(a)][a,b]+=c*mult(b)
eta=F(0)
for ts,data in rows.items():
 t=int(ts);terms=data['terms'];r=data['integer_scaled_rows'];m=len(terms)
 assert data['common_denominator']==10**12
 assert terms==[None]+[[p,d-p] for d in range(t,9) for p in range(d+1)]
 assert all(len(v)==m and all(type(x)is int for x in v) for v in r)
 g=[[F(sum(v[i]*v[j] for v in r),DEN) for j in range(m)]for i in range(m)]
 eta+=g[0][0]*F(2**(t+1),fac(t))
 for ia in range(1,m):
  p,j=terms[ia];i=p+j-t
  for a in range(t+1):
   for b in range(p+1):
    aa=(a,t-a,i);bb=(j,b,p-b);c=g[0][ia]/F(fac(a)*fac(t-a))
    emit(3,c,aa,bb)
    # Take the physical adjoint of this monomial in x/derivative coordinates.
    adjfac=F(facprod(fac(z) for z in aa),facprod(fac(z) for z in bb))
    emit(3,c*adjfac,bb,aa)
  for ib in range(1,m):
   pp,jj=terms[ib];ii=pp+jj-t;c=g[ia][ib]*F(fac(i),fac(j))
   for a in range(p+1):
    cc=c/F(fac(a)*fac(p-a))
    for b in range(pp+1):
     if i==ii:emit(3,cc,(a,p-a,j),(jj,b,pp-b))
     emit(4,cc,(a,p-a,j,ii),(i,jj,b,pp-b))
 print('channel',t,'assembled',round(time.time()-start,2),flush=True)
checks=[];delta=F(1,10**6);c9=30*F(5,9)**9;mu=F(1,50)
for n,maxd in [(3,8),(4,16)]:
 body={}
 for d in range(maxd+1):
  bs=basis(n,d);body[d]=[[K[n][d].get((a,b),F(0))for b in bs]for a in bs]
 for z in range(maxd+1):
  u=relative(n,z);dim=len(u[0]) if u else 0;avg=zeros(dim,dim);v=u
  for d in range(z,maxd+1):
   avg=add(avg,congr(form(body[d],n,d),v),F(2,n**(d-z+1)*fac(d-z)))
   if d<maxd:v=raised(n,d,v)
  h=congr(form(H(n,z),n,z),u);target=congr(form(S(n,z),n,z),u)
  if n==4:target=scale(target,1-c9-mu)
  shifted=add(add(target,avg,-1),h,delta)
  piv=exact_psd(shifted);hpiv=exact_psd(h)
  null=kernel(h,dim);assert not any(x for row in mm(shifted,null)for x in row);assert len(piv)==len(hpiv)
  checks.append(dict(body=n,degree=z,dimension=dim,rank=len(piv),pivots=piv,kernel_preserved=True))
  print('verified',n,z,'rank',len(piv),'seconds',round(time.time()-start,2),flush=True)
C3=12*F(9,8)**9;C4=272*F(9,8)**17
A=1-eta-c9-delta*(C3+C4);B=mu-delta*(C3+2*C4)
assert A>F(1,3) and B>0
result=dict(status='INDEPENDENT_DIRECT_CCR_EXACT_26_BLOCKS_PASS',eta=str(eta),c9=str(c9),C3=str(C3),C4=str(C4),A=str(A),B=str(B),A_decimal=float(A),B_decimal=float(B),A_minus_third=str(A-F(1,3)),checks=checks,seconds=time.time()-start)
cr=F(0)
for ts,data in rows.items():
 t=int(ts)
 for row in data['integer_scaled_rows']:
  for y,term in zip(row[1:],data['terms'][1:]):
   p,j=term;i=p+j-t
   cr+=F(y*y,DEN)*F(2**(p+1)*fac(i),fac(j)*fac(p))
result['Crows_trace']=str(cr);result['Crows_trace_decimal']=float(cr)
published=json.loads((BASE/'paper/data/bosonic/exact_shifted_certificate_results.json').read_text())
result['source_pivots_match']=all(a['pivots']==b['pivots'] for a,b in zip(checks,published['checks']))
assert result['source_pivots_match']
# Scalar lattice/error budgets; e^-200<2^-288 uses log(2)<25/36.
b4=F(50*17**2*fac(16)*20**32,2**288);b8=F(50*9**2*fac(8)*20**16,2**288);b2=F(50,2**144)
e=F(1,10**8);s=1+e;c=(1+e)/(1-e)**2;k=6*cr*e;alpha=1-c9-mu
At=1-e-eta-s*(c9+(delta+k)*C3)-delta*C4*s*s
Bt=1-alpha*(1+e)-s*c*(c9+(delta+k)*C3)-2*delta*C4*s*s*c
assert max(b4,b8,b2)<e and At>F(1,3) and Bt>0
budget=dict(systole_dimensionless=20,common_error_allowance=str(e),epsilon4_upper=str(b4),epsilon4_decimal=float(b4),e8_upper=str(b8),e8_decimal=float(b8),epsilon2_upper=str(b2),epsilon2_decimal=float(b2),A_lower=str(At),A_lower_decimal=float(At),B_lower=str(Bt),B_lower_decimal=float(Bt),gap_third_certified_scalar_budget=True)
(OUT/'boson_systole_budget.json').write_text(json.dumps(budget,indent=2)+'\n')
(OUT/'boson_planar.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items()if k!='checks'},indent=2))
