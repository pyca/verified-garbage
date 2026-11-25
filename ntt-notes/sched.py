# list scheduler over the generated straight-line code, with register re-allocation
import sys, heapq
from gen import *
ALL=[f'v{i}' for i in list(range(8))+list(range(16,32))]
LOW=set(f'v{i}' for i in range(8))
def srcs(i):
    o=i[0]
    if o=='ldr': return []
    if o=='str': return [i[1]]
    if o=='mls': return [i[1],i[2],i[3]]
    if o=='sshr': return [i[2]]
    return [i[2],i[3]]
def dst(i): return None if i[0]=='str' else i[1]
def vreg(x): return f'v{x[0]}' if isinstance(x,tuple) else x
LAT={'ldr':6,'str':1,'sqrdmulh':4,'mul':4,'mls':4,'sub':2,'add':2,'sshr':2,'and':2}
MUL={'sqrdmulh','mul','mls'}
def ssa(code):
    cur={}; n=0; out=[]
    for i in code:
        s=[(cur[vreg(x)], x[1] if isinstance(x,tuple) else None) for x in srcs(i)]
        d=None
        if dst(i): d=n; n+=1
        tied = i[0]=='mls'
        out.append((i,s,d,tied))
        if d is not None: cur[i[1]]=d
    return out
def run(code,window=10**9,nregs=24):
    S=ssa(code); N=len(S)
    defi={}; uses={}
    for k,(i,s,d,t) in enumerate(S):
        if d is not None: defi[d]=k
        for (v,_) in s: uses.setdefault(v,[]).append(k)
    succ=[[] for _ in S]; npred=[0]*N
    def edge(a,b,l): succ[a].append((b,l)); npred[b]+=1
    mem={}  # address-> last store / loads
    for k,(i,s,d,t) in enumerate(S):
        for (v,_) in s: edge(defi[v],k,LAT.get(i and S[defi[v]][0][0],2))
        if t: # clobbers s[0]: all other uses of s[0] must precede
            for u in uses[s[0][0]]:
                if u!=k: edge(u,k,0)
        if i[0] in('ldr','str') and i[2]=='x0':
            a=i[3]
            if i[0]=='ldr':
                if a in mem and mem[a][0]=='str': edge(mem[a][1],k,1)
                mem[a]=('ldr',k)
            else:
                if a in mem: edge(mem[a][1],k,0)
                mem[a]=('str',k)
    pri=[0]*N
    for k in range(N-1,-1,-1):
        pri[k]=LAT.get(S[k][0][0],2)+max([pri[b] for b,l in succ[k]],default=0)
    # priority: original position blended with critical path
    low={v for k,(i,s,d,t) in enumerate(S) for (v,l) in s if l is not None}
    rem={v:len(u) for v,u in uses.items()}
    ready=[0]*N; np=npred[:]; avail=set(k for k in range(N) if np[k]==0)
    done=[False]*N; first=0
    free=list(ALL); reg={}
    out=[]; cyc=0; left=N
    port_free={'V0':0,'V1':0}
    stall=0
    while left:
        slots={'V0':1,'V1':1,'L':3,'ST':2}
        while first<N and done[first]: first+=1
        issued=0
        cand=sorted([k for k in avail if k<first+window and ready[k]<=cyc],key=lambda k:keyf(k,pri,S))
        for k in cand:
            i,s,d,t=S[k]; o=i[0]
            if o in MUL: p=['V0']
            elif o=='sshr': p=['V1']
            elif o=='ldr': p=['L']
            elif o=='str': p=['ST']
            else: p=['V1','V0']
            p=[x for x in p if slots[x]]
            if not p: continue
            # registers
            need = d is not None and not t
            dying=[v for v in set(v for v,_ in s) if rem[v]==1 or sum(1 for w,_ in s if w==v)==rem[v]]
            if need:
                pool=free+[reg[v] for v in dying]
                ok=[r for r in pool if (r in LOW)] if d in low else [r for r in pool if r not in LOW] or pool
                reserve = 0 if o!='ldr' else RES
                if not ok or (len(free)<=reserve and o=='ldr'): continue
            slots[p[0]]-=1
            for v,_ in s: rem[v]-=1
            sn=[(reg[v],l) for v,l in s]
            for v in dying:
                if not (t and v==s[0][0]): free.append(reg.pop(v))
                
            if d is not None:
                if t: reg[d]=reg.pop(s[0][0]) if s[0][0] in reg else reg[d]
                else:
                    c=[r for r in free if (r in LOW)==(d in low)] or free
                    r=c[0]; free.remove(r); reg[d]=r
                if d not in rem: free.append(reg[d])
            def op(x): return (int(x[0][1:]),x[1]) if x[1] is not None else x[0]
            if o=='str': n=(o,sn[0][0])+i[2:]
            elif o=='ldr': n=(o,reg[d])+i[2:]
            elif o=='mls': n=(o,reg[d])+tuple(op(x) for x in sn[1:])
            elif o=='sshr': n=(o,reg[d],op(sn[0]),i[3])
            else: n=(o,reg[d])+tuple(op(x) for x in sn)
            out.append(n); avail.discard(k); done[k]=True; left-=1; issued+=1
            for b,l in succ[k]:
                np[b]-=1; ready[b]=max(ready[b],cyc+l)
                if np[b]==0: avail.add(b)
        cyc+=1
        stall=0 if issued else stall+1
        if stall>200: raise Exception(f'stuck {left} free {free}')
    return out,cyc
RES=2
def keyf(k,pri,S): return (k//BL, -pri[k])
BL=80
if __name__=='__main__':
    best={}
    for name,g in (('my_fwd',fwd()),('my_inv',inv())):
        for w in (60,100,150,200,300):
          for BL_ in (40,80,150,1000):
            for R in (2,4,6):
              BL=BL_; RES=R
              try: o,c=run(g.c,w)
              except Exception as e: continue
              if name not in best or c<best[name][0]: best[name]=(c,w,BL_,R,o)
        print(name,best[name][:4],file=sys.stderr); g.c=best[name][4]
        best[name]=g
    open('p2.s','w').write('.text\n'+emit(best['my_fwd'],'my_fwd')+emit(best['my_inv'],'my_inv')+'.section .note.GNU-stack,"",%progbits\n')
