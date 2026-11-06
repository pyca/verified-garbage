import os, pickle, sys
from collections import Counter, defaultdict
dm,E,mc,cm,rg=pickle.load(open(sys.argv[1],'rb'))
L,U,D,R,A,I=pickle.load(open(sys.argv[2],'rb'))
allm=Counter(dm.values()); dc=Counter(dm[d] for d in D)
rows=defaultdict(lambda: [0,0,0,0,0])  # dead decls, all decls, dead mods(all decls dead or unreachable), mods, unreachable
for m in I:
    p=m.split('.')
    if p[0]!='VerifiedGarbage' or p[1] not in ('Proof','Impl','Spec'): continue
    key=(p[2] if len(p)>2 else '-', p[1])
    r=rows[key]; r[0]+=dc[m]; r[1]+=allm[m]; r[3]+=1
    if (allm[m] and dc[m]==allm[m]) or m not in R: r[2]+=1
    if m not in R: r[4]+=1
alg=defaultdict(lambda: defaultdict(lambda:[0,0,0,0,0]))
for (a,k),r in rows.items(): alg[a][k]=r
tot=[0]*5
out=[]
for a in alg:
    s=[sum(alg[a][k][i] for k in ('Proof','Impl')) for i in range(5)]
    sp=alg[a]['Spec']
    out.append((s[0],a,s,sp))
for x,a,s,sp in sorted(out,reverse=True):
    if s[0] or s[2] or sp[0]:
        print(f'{a:28s} dead decls {s[0]:5d}/{s[1]:6d}  dead mods {s[2]:4d}/{s[3]:5d} (unreachable {s[4]:3d})  Spec dead decls {sp[0]}/{sp[1]}')
    for i in range(5): tot[i]+=s[i]
print('TOTAL Proof+Impl', tot)
