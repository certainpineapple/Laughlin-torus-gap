# Retained from the 12 October torus candidate package; paths adapted for this layout.
# Internal AI reconstruction, not external human review. See AI_CONTRIBUTIONS.md.
from fractions import Fraction as F
from math import factorial,comb,sqrt,pi
from pathlib import Path
import hashlib,json
BASE=Path(__file__).resolve().parent.parent
OUT=BASE/'output/checks'; OUT.mkdir(parents=True,exist_ok=True)
rows=[]
for line in (BASE/'paper/data/fermionic/rows.txt').read_text().splitlines():
    if not line[0].isspace():
        x=line.split();rows.append([int(x[0]),int(x[1]),{}]);rest=x[2:]
    else:rest=line.split()
    for term in rest:
        pj,a=term.split(':');rows[-1][2][tuple(map(int,pj))]=int(a)
def U(c,z,T,p):
    if min(z,p)<0 or max(z,p)>T:return 0
    return sum((-1)**(z-h)*comb(z,h)*comb(T-z,p-h)*c**(p-h) for h in range(max(0,p+z-T),min(p,z)+1))
eta=F(sum(l*l for t,l,row in rows),10**14)
Ca=F(0)
for t,l,row in rows:
    groups={}
    for (p,j),a in row.items():
        i=p+j-t
        val=F(a*a,10**14)*F(2)**(p-t)*F(factorial(t)*factorial(i),factorial(p)*factorial(j))
        groups[i]=groups.get(i,F(0))+val
    Ca+=len(row)*max(groups.values())
margins={}
for z in [2,*range(4,16)]:
    ez=F(0)
    for t,l,row in rows:
        for T in range(max(z,t),16):
            X=sum(a*U(2,z,T,p) for (p,j),a in row.items() if p+j==T)
            ez+=F(2**z*comb(T,z),3**T*2**t*comb(T,t))*X*(X+2*l*U(2,z,T,t))
    ez/=10**14
    margin=F(3,2)*(3*z-1)*F(-1,2)**z-ez
    margins[z]={'positive':margin>0,'scaled_floor':(margin*10**6).__floor__()}
gamma=1-eta-F(61,4096)-1222*F(3,10**6)
disk=[]
for M in (1,2,3,12,30,100,1000):
    E=F(factorial(2*M-2),2**(2*M-2)*factorial(M-1)*factorial(M))
    disk.append({'M_cutoff':M,'energy':str(E) if M<=12 else None,'energy_float':float(E),'asymptotic_ratio':float(E)*sqrt(pi)*M**1.5})
paths=['paper/data/fermionic/rows.txt']
out={'eta':str(eta),'C_alpha':str(Ca),'gamma':str(gamma),'three_body_margins':margins,'disk_two_particle_edge':disk,'source_sha256':{p:hashlib.sha256((BASE/p).read_bytes()).hexdigest() for p in paths},'N5_disk_value':'Not independently verified; no inaccessible certificate was reconstructed.'}
(OUT/'fermion_scalars.json').write_text(json.dumps(out,indent=2))
print(json.dumps({k:v for k,v in out.items() if k not in ['source_sha256','disk_two_particle_edge']},indent=2))
