import sys,random,subprocess,re,os
sys.path.insert(0,'notes/notes')
from sbox_check import build
from concurrent.futures import ThreadPoolExecutor
fn,lpf,inv,tag,N,secs=sys.argv[1],sys.argv[2],sys.argv[3]=='inv',sys.argv[4],int(sys.argv[5]),sys.argv[6]
blk=('total'+open(fn).read().split('total')[-1]).strip().split('\n')
U=[l.strip() for l in open(lpf) if l[0]=='U'];B=[l.strip() for l in open(lpf) if l[0]=='B']
rng=random.Random(5)
def gates(u,b):
    bl=[l for l in blk if l.split()[0] not in('U','B')]+[u,b]
    G,outs=build(bl,inv)
    num={f'x{i}':i for i in range(8)};k=8;out=[]
    for op,t,a,c in G:
        if t in outs: num[t]=200+outs.index(t)
        else: num[t]=k;k+=1
        out.append(f"{1 if op=='and' else 0} {num[t]} {num[a]} {num[c]}")
    return out
def one(i):
    u,b=rng.choice(U),rng.choice(B)
    g=gates(u,b); f=f'cmb_{tag}_{i}.txt';open(f,'w').write('\n'.join(g)+'\n')
    r=subprocess.run(['./sched3','13',str(i),secs],stdin=open(f),capture_output=True,text=True)
    c=int(re.search(r'cost (\d+)',r.stderr).group(1));open(f'cmb_{tag}_{i}.out','w').write(r.stdout)
    return len(g)+c,len(g),c,i
with ThreadPoolExecutor(4) as ex: res=sorted(ex.map(one,range(N)))
print(res[:12])
open(f'cmb_{tag}.res','w').write(repr(res))
