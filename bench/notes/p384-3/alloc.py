"""Register allocation of the raw doubling (dumped from Lean): value numbering, then
furthest-next-use allocation in the raw order, spilling to the scratch slots."""
import re,sys
SCR=[s+8*j for s in (1168,1216,1264,1312,1360,1408,4000) for j in range(6)]
def parse(f):
    out=[]
    for l in open(f):
        p=l.split()
        if not p or not re.match(r'^(adcs?|adds?|sub[s]?|sbcs?|csel|logicand|mul|umulh|lsl|lsr|extr|movz|ldr|str)$',p[0]): continue
        out.append((p[0],[int(x.split('.')[-1][1:]) if 'Reg' in x else int(x) for x in p[1:]]))
    return out
READC={'adcs','adc','sbcs','sbc','csel'}; SETC={'adds','adcs','subs','sbcs'}
def ssa(raw,inputs):
    """ops: list of (op, dstval, srcvals, imm, cin, cout). values: ints"""
    reg={};slot={};ops=[];n=0;vn={};kind={}
    cur=None
    def new(k): 
        nonlocal n; n+=1; kind[n]=k; return n
    for op,a in raw:
        if op=='ldr':
            d,b,o=a
            if o not in slot: slot[o]=new(('in',o))
            reg[d]=slot[o]
        elif op=='str': 
            slot[a[2]]=reg[a[0]]
        else:
            imm=None
            if op=='movz': src=[];imm=(a[1],a[2])
            elif op in('lsl','lsr'): src=[reg[a[1]]];imm=a[2]
            elif op=='extr': src=[reg[a[1]],reg[a[2]]];imm=a[3]
            else: src=[reg[x] for x in a[1:3]]
            cin=cur if op in READC else None
            key=(op,tuple(src),imm,cin)
            if key in vn and op not in SETC: reg[a[0]]=vn[key]; continue
            v=new(('op',))
            vn[key]=v
            ops.append([op,v,src,imm,cin]); reg[a[0]]=v
            if op in SETC: cur=v
    return ops,slot,kind
def dce(ops,live):
    keep=[];live=set(live)
    for o in reversed(ops):
        op,v,src,imm,cin=o
        if v in live or ('c',v) in live:
            keep.append(o); live|=set(src)
            if cin is not None: live.add(('c',cin))
    return keep[::-1]
def allocate(ops,slot,kind,outs,regs,pin_zero=True):
    """outs: {off: value}"""
    val_out={}
    for o,v in outs.items(): val_out.setdefault(v,[]).append(o)
    uses={}
    for i,(op,v,src,imm,cin) in enumerate(ops):
        for s in src: uses.setdefault(s,[]).append(i)
    INF=10**9
    from bisect import bisect_left
    def nextuse(v,i):
        u=uses.get(v,[]);k=bisect_left(u,i)
        return u[k] if k<len(u) else INF
    free=list(regs);inreg={};where={};out=[];spill={};freeslots=list(SCR)
    zero=next((o[1] for o in ops if o[0]=='movz'),None)
    def evict(i,avoid):
        # furthest next use; prefer those not needing a store
        best=max((v for v in where if v not in avoid and v!=zero),key=lambda v:(nextuse(v,i) if not(kind[v][0]!='in' and v not in spill) else nextuse(v,i)-6))
        r=where.pop(best)
        if nextuse(best,i)<INF and kind[best][0]!='in' and best not in spill:
            s=freeslots.pop(0);spill[best]=s;out.append(('str',[r,0,s]))
        return r
    def getreg(i,avoid):
        if free: return free.pop(0)
        return evict(i,avoid)
    def drop(i):
        for v in list(where):
            if nextuse(v,i)>=INF and v!=zero:
                free.append(where.pop(v))
        for v in list(spill):
            if nextuse(v,i)>=INF: freeslots.append(spill.pop(v))
    for i,(op,v,src,imm,cin) in enumerate(ops):
        avoid=set(src)
        for s in src:
            if s not in where:
                r=getreg(i,avoid)
                o=kind[s][1] if kind[s][0]=='in' else spill[s]
                out.append(('ldr',[r,0,o])); where[s]=r
        rs=[where[s] for s in src]
        # free operands that die here
        for s in set(src):
            if nextuse(s,i+1)>=INF and s!=zero:
                free.insert(0,where.pop(s))
                if s in spill: freeslots.append(spill.pop(s))
        r=getreg(i,set(x for x in src))
        where[v]=r
        if op=='movz': out.append((op,[r,imm[0],imm[1]]))
        elif op in('lsl','lsr','extr'): out.append((op,[r]+rs+[imm]))
        else: out.append((op,[r]+rs))
        if v in val_out:
            for o in val_out[v]: out.append(('str',[r,0,o]))
        if nextuse(v,i+1)>=INF and v!=zero:
            free.insert(0,where.pop(v))
    return out
def interp(code,mem):
    W=1<<64;r={0:0};C=None;mem=dict(mem)
    for op,a in code:
        if op=='ldr': r[a[0]]=mem[a[2]]
        elif op=='str': mem[a[2]]=r[a[0]]
        elif op=='movz': r[a[0]]=a[1]<<(16*a[2])
        elif op=='mul': r[a[0]]=r[a[1]]*r[a[2]]%W
        elif op=='umulh': r[a[0]]=r[a[1]]*r[a[2]]>>64
        elif op in('add','adds','adc','adcs'):
            v=r[a[1]]+r[a[2]]+(C if op in('adc','adcs') else 0); r[a[0]]=v%W
            if op in SETC: C=v>>64
        elif op in('sub','subs','sbc','sbcs'):
            v=r[a[1]]+(W-1-r[a[2]])+(C if op in('sbc','sbcs') else 1); r[a[0]]=v%W
            if op in SETC: C=v>>64
        elif op=='logicand': r[a[0]]=r[a[1]]&r[a[2]]
        elif op=='csel': r[a[0]]=r[a[1]] if C else r[a[2]]
        elif op=='lsl': r[a[0]]=(r[a[1]]<<a[2])%W
        elif op=='lsr': r[a[0]]=r[a[1]]>>a[2]
        elif op=='extr': r[a[0]]=((r[a[1]]<<64|r[a[2]])>>a[3])%W
        else: raise Exception(op)
    return mem
def lint(code):
    return code
P=2**384-2**128-2**96+2**32-1
def main():
    raw=parse('raw.txt')
    outs_off=[o+8*j for o in (880,928,976) for j in range(6)]
    ops,slot,kind=ssa(raw,None)
    outs={o:slot[o] for o in outs_off}
    ops=dce(ops,outs.values())
    regs=[1,2,3,4,5,6,7]+list(range(8,18))+[21,22,23,24,25]
    al=allocate(ops,slot,kind,outs,regs)
    import random
    for _ in range(20):
        mem={64+8*j:(P>>64*j)&(2**64-1) for j in range(6)}
        for b in (736,784,832):
            x=random.randrange(P)
            for j in range(6): mem[b+8*j]=x>>64*j&2**64-1
        m1=interp(raw,mem);m2=interp(al,mem)
        assert all(m1[o]==m2[o] for o in outs_off)
    from collections import Counter
    print(len(raw),len(ops),len(al),Counter(x[0] for x in al).most_common())
    return raw,al
if __name__=='__main__': main()
