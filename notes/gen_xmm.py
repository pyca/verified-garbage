"""Allocate an ordered circuit to R two-operand xmm registers (Belady), as Lean short forms:
mv d s (movdqa), px d s (pxor), an d s (pand), sv k r (store slot), ld r k (load slot)."""
import sys
def gen(fn,R,inmap,outmap,slot0):
    G=[tuple(map(int,l.split())) for l in open(fn) if l.strip()]
    uses={}
    for i,(o,d,a,b) in enumerate(G):
        for v in (a,b): uses.setdefault(v,[]).append(i)
    for j in range(8): uses.setdefault(200+j,[]).append(10**6+j)
    reg={inmap[j]:j for j in range(8)};loc={j:inmap[j] for j in range(8)};slot={};free=[r for r in range(R) if r not in reg];fs=[];ns=slot0;code=[]
    nx=lambda v,i:next((u for u in uses.get(v,[]) if u>i),None)
    def drop(v):
        r=loc.pop(v,None)
        if r is not None: del reg[r];free.append(r)
        if v in slot: fs.append(slot.pop(v))
    def get(i,keep):
        nonlocal ns
        if free: return free.pop(0)
        v=max((v for v in loc if v not in keep),key=lambda v:nx(v,i-1) if nx(v,i-1) is not None else 10**9)
        r=loc.pop(v);del reg[r]
        if v not in slot:
            s=fs.pop() if fs else ns
            if s==ns: ns+=1
            slot[v]=s;code.append(f'sv {s} .xmm{r}')
        return r
    def ens(v,i,keep):
        if v in loc: return
        r=get(i,keep);code.append(f'ld .xmm{r} {slot[v]}');reg[r]=v;loc[v]=r
    for i,(o,d,a,b) in enumerate(G):
        ens(a,i,(a,b));ens(b,i,(a,b))
        ad,bd=nx(a,i) is None,nx(b,i) is None
        if ad: p,q=a,b
        elif bd: p,q=b,a
        else: p,q=a,b
        nm=['px','an'][o]
        if ad or bd:
            r=loc.pop(p);code.append(f'{nm} .xmm{r} .xmm{loc[q]}')
            if p in slot: fs.append(slot.pop(p))
            if nx(q,i) is None and q!=p: drop(q)
            reg[r]=d;loc[d]=r
        else:
            r=get(i+1 if False else i,(a,b));code.append(f'mv .xmm{r} .xmm{loc[p]}');code.append(f'{nm} .xmm{r} .xmm{loc[q]}');reg[r]=d;loc[d]=r
    # place outputs: parallel move through a free register or a slot
    want={200+j:outmap[j] for j in range(8)}
    for v in list(loc):
        if v not in want: drop(v)
    pend={v for v in want if loc.get(v)!=want[v]}
    while pend:
        prog=False
        for v in sorted(pend):
            t=want[v]
            if t not in reg:
                if v in loc: r=loc.pop(v);del reg[r];code.append(f'mv .xmm{t} .xmm{r}')
                else: code.append(f'ld .xmm{t} {slot[v]}')
                reg[t]=v;loc[v]=t;pend.discard(v);prog=True;break
        if not prog:
            v=sorted(pend)[0];r=loc[v]
            t=next((x for x in range(R) if x not in reg),None)
            if t is None: code.append(f'sv {ns} .xmm{r}');slot[v]=ns;ns+=1;del reg[r];loc.pop(v)
            else: code.append(f'mv .xmm{t} .xmm{r}');del reg[r];reg[t]=v;loc[v]=t
    return code,ns-slot0
def sim(code,fn,inmap,outmap):
    v={}; import random
    xs=[random.getrandbits(256) for _ in range(8)]
    regs={inmap[j]:xs[j] for j in range(8)};sl={}
    for c in code:
        p=c.replace('.xmm','').split();op=p[0];a,b=int(p[1]),int(p[2])
        if op=='mv':regs[a]=regs[b]
        elif op=='px':regs[a]^=regs[b]
        elif op=='an':regs[a]&=regs[b]
        elif op=='sv':sl[a]=regs[b]
        else:regs[a]=sl[b]
    val={j:xs[j] for j in range(8)}
    for l in open(fn):
        o,d,a,b=map(int,l.split());val[d]=val[a]&val[b] if o else val[a]^val[b]
    assert all(regs[outmap[j]]==val[200+j] for j in range(8))
def lean(code,w=96):
    out='';line='  '
    for i,it in enumerate(code):
        it+=',' if i<len(code)-1 else ']'
        if len(line)+len(it)>w: out+=line.rstrip()+'\n';line='  '
        line+=it+' '
    return out+line.rstrip()
if __name__=='__main__':
    fn,R,ib,ob,s0=sys.argv[1],int(sys.argv[2]),int(sys.argv[3]),int(sys.argv[4]),int(sys.argv[5])
    im=[ib+j for j in range(8)];om=[ob+j for j in range(8)]
    c,n=gen(fn,R,im,om,s0);sim(c,fn,im,om);print(len(c),n,file=sys.stderr);print(lean(c))
