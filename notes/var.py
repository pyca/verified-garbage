from alloc import *
base=open('sq.s').read().strip().split('\n')
from itertools import product
def show(n,L):
    import subprocess,re
    r=[]
    for c in('neoverse-n2','neoverse-v2','neoverse-v1','apple-m1'):
        o=subprocess.run(['llvm-mca-18','-march=aarch64','-mcpu='+c,'-iterations=1','-instruction-info=0','-resource-pressure=0','-'],input='\n'.join(L)+'\n',capture_output=True,text=True).stdout
        r.append(int(re.search(r'Total Cycles:\s+(\d+)',o).group(1)))
    print(n,len(L),r)
show('base',base)
# e from t1: move extr before adds
L=[l for l in base]
i=L.index('adds\tx8, x8, x1') if 'adds\tx8, x8, x1' in L else [k for k,l in enumerate(L) if l=='adds x8, x8, x1'][-1]
assert L[i+1].startswith('extr x2, x8, x15')
A=L[:i]+[L[i+1],L[i]]+L[i+2:]
show('e early',A)
# mult order
m=A[5:17]; d=[l for l in A if l in()] 
def orr(L,reg,hi,lo,tmp):
    k=[j for j,l in enumerate(L) if l==f'extr {reg}, {hi}, {lo}, #32'][0]
    return L[:k]+[f'lsr {reg}, {lo}, #32',f'lsl {tmp}, {hi}, #32',f'orr {reg}, {reg}, {tmp}']+L[k+1:]
B=orr(A,'x3','x9','x8','x20'); show('f orr',B)
C=orr(B,'x6','x5','x9','x20'); show('f,e23 orr',C)
D=orr(A,'x6','x5','x9','x20'); show('e23 orr',D)
# reorder mults in A: low first
pairs=[A[5+2*k:7+2*k] for k in range(6)]
names=['01','02','03','13','23','12']
P=dict(zip(names,pairs))
dm=[k for k,l in enumerate(A) if l.startswith('mul x15')][0]
Dp=A[dm:dm+8]
print(P,Dp)
import itertools
def sqv(order, interleave):
    M=sum([P[x] for x in order],[])
    rest=A[17:]
    if interleave:
        # diag muls need regs: rename impossible here; keep
        pass
    return A[:5]+M+rest
best=[]
for o in itertools.permutations(names):
    import subprocess,re
    L=sqv(o,0)
    t=subprocess.run(['llvm-mca-18','-march=aarch64','-mcpu=neoverse-n2','-iterations=1','-instruction-info=0','-resource-pressure=0','-'],input='\n'.join(L)+'\n',capture_output=True,text=True).stdout
    best.append((int(re.search(r'Total Cycles:\s+(\d+)',t).group(1)),o))
best.sort(); print(best[:5],best[-3:])
for _,o in best[:2]: show(str(o),sqv(o,0))
# infinite mult lower bound: what dependency only?
