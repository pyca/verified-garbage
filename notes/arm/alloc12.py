"""Registers for an order found by sched3: Belady's evictions, then a colouring that leaves output j
in r_(j+1), output 7 in lr. Prints Lean instructions. usage: alloc3.py file name seed"""
import sys,random
def load(fn):
    return [tuple(map(int,l.split())) for l in open(fn) if l[0]!='#']
def events(G,R):
    n=len(G);uses={}
    for i,(op,d,a,b) in enumerate(G):
        uses.setdefault(a,[]).append(i);uses.setdefault(b,[]).append(i)
    for j in range(8): uses.setdefault(200+j,[]).append(10000)
    nx=lambda v,i: next((u for u in uses.get(v,[]) if u>i),20000)
    reg=list(range(8));slot=set();ev=[]  # ('load',v) ('store',v) ('free',v) ('op',..)
    def room(i,a,b):
        if len(reg)<R: return
        c=[(2*nx(v,i)+(1 if v in slot else 0),k,v) for k,v in enumerate(reg) if v not in(a,b)]
        x,_,v=max(c,key=lambda t:(t[0],-t[1]))
        if v not in slot and x//2<20000: slot.add(v);ev.append(('store',v))
        reg.remove(v);ev.append(('free',v))
    for i,(op,d,a,b) in enumerate(G):
        for v in (a,b):
            if v not in reg: room(i-1,a,b);reg.append(v);ev.append(('load',v))
        fr=[]
        for v in {a,b}:
            if nx(v,i)>=20000: reg.remove(v);fr.append(v)
        if len(reg)>=R: room(i,a,b)
        # an operand may have been evicted by room only if not a,b
        reg.append(d);ev.append(('op',op,d,a,b,fr))
    for j in range(8): assert 200+j in reg
    return ev
def color(ev,names,rng):
    # sessions
    T=len(ev);sess=[];cur={}
    for v in range(8): cur[v]=len(sess);sess.append([v,-1,None,v])
    for t,e in enumerate(ev):
        if e[0]=='load': cur[e[1]]=len(sess);sess.append([e[1],t,None,None])
        elif e[0]=='free': sess[cur.pop(e[1])][2]=t
        elif e[0]=='op':
            for v in e[5]: sess[cur.pop(v)][2]=t
            cur[e[2]]=len(sess);sess.append([e[2],t,None,None])
    need={}
    for v,k in cur.items():
        sess[k][2]=T+1
        if v>=200: sess[k][3]=OUT[v-200];need[v-200]=sess[k][1]
    busy={r:[(s[1],s[2]) for s in sess if s[3]==r] for r in names}
    for r in names:
        b=sorted(busy[r])
        for x,y in zip(b,b[1:]):
            if x[1]>y[0]: return None
    order=sorted([s for s in sess if s[3] is None],key=lambda s:s[1])
    for s in order:
        c=[r for r in names if all(s[2]<=x or y<=s[1] for x,y in busy[r])]
        if not c: return None
        def gap(r):
            nxts=[x for x,y in busy[r] if x>=s[2]];return min(nxts) if nxts else 10**6
        c.sort(key=lambda r:(gap(r)-s[2])+rng.random()*30)
        s[3]=c[0];busy[c[0]].append((s[1],s[2]))
    return sess
def emit(ev,sess):
    R=lambda r:'.lr' if r==14 else f'.r{r}'
    at={};out=[];slots={};free=[]
    it={ (s[0],s[1]):s for s in sess}
    loc={v:it[(v,-1)][3] for v in range(8)}
    lastload={}
    for t,e in enumerate(ev):
        if e[0]=='load': lastload[e[1]]=t
    for t,e in enumerate(ev):
        if e[0]=='store':
            k=free.pop() if free else len(set(slots.values())|set(freed))if False else None
            if k is None: k=max(list(slots.values())+alls,default=-1)+1 if True else 0
            slots[e[1]]=k;alls.append(k) if k not in alls else None
            out.append(f'stS {k} {R(loc[e[1]])}')
        elif e[0]=='load':
            loc[e[1]]=it[(e[1],t)][3];out.append(f'ldS {R(loc[e[1]])} {slots[e[1]]}')
            if lastload[e[1]]==t: free.append(slots[e[1]])
        elif e[0]=='op':
            _,op,d,a,b,fr=e;ra,rb=loc[a],loc[b]
            loc[d]=it[(d,t)][3]
            out.append(f"{'andR' if op==1 else 'eorR'} {R(loc[d])} {R(ra)} {R(rb)}")
    return out,len(alls)
alls=[];freed=[];OUT=[0,1,2,3,4,5,6,7]
def run(code,ins,M):
    reg={f'.r{j}':ins[j] for j in range(8)};sl={}
    for c in code:
        p=c.split()
        if p[0]=='stS': sl[p[1]]=reg[p[2]]
        elif p[0]=='ldS': reg[p[1]]=sl[p[2]]
        elif p[0]=='andR': reg[p[1]]=reg[p[2]]&reg[p[3]]
        else: reg[p[1]]=reg[p[2]]^reg[p[3]]
    return [reg['.lr' if j==14 else f'.r{j}'] for j in OUT]
if __name__=='__main__':
    sys.path.insert(0,sys.path[0]+'/..')
    from sbox_check import sboxes
    S_,SI=sboxes();names=[0,1,2,3,4,5,6,7,10,11,12,14]
    G=load(sys.argv[1]);inv=sys.argv[2]=='inv';rng=random.Random(int(sys.argv[3]));ev=events(G,12)
    for tr in range(4000):
        s=color(ev,names,rng)
        if s: break
    else: print('no colouring');sys.exit(1)
    alls.clear();code,ns=emit(ev,s)
    ins=[sum(1<<x for x in range(256) if x>>j&1) for j in range(8)];M=(1<<256)-1
    o=run(code,ins,M);t=[sum((o[j]>>x&1)<<j for j in range(8)) for x in range(256)]
    if inv: assert [t[x^0x63] for x in range(256)]==SI
    else: assert [v^0x63 for v in t]==S_
    print('--',len(code),'instructions',ns,'slots tries',tr)
    line='  '
    for i,c in enumerate(code):
        it=c+(',' if i<len(code)-1 else ']')
        if len(line)+len(it)>98: print(line.rstrip());line='  '
        line+=it+' '
    print(line.rstrip())
