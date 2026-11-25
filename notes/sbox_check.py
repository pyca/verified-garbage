"""Rebuild the gate list from a sbox_search result and check it on all 256 inputs.
Gates: list of (op, dst, a, b); inputs x0..x7 (bit i of the byte), outputs s0..s7."""
import sys,re
def sboxes():
    def mul(a,b):
        r=0
        while b:
            if b&1:r^=a
            a<<=1
            if a&256:a^=0x11b
            b>>=1
        return r
    inv=[0]*256
    for a in range(1,256):
        for b in range(1,256):
            if mul(a,b)==1: inv[a]=b
    S=[]
    for x in inv:
        r=0
        for i in range(8):
            r|=((x>>i^x>>((i+4)&7)^x>>((i+5)&7)^x>>((i+6)&7)^x>>((i+7)&7))&1)<<i
        S.append(r^0x63)
    SI=[0]*256
    for i,v in enumerate(S): SI[v]=i
    return S,SI
def build(block,inverse):
    d={l.split()[0]:l.split()[1:] for l in block}
    o=[int(c) for c in re.search(r'o=(\d+)',' '.join(block)).group(1)]
    UT=[int(v,16) for v in d['UT']];PT=[int(v,16) for v in d['PT']];BT=[int(v,16) for v in d['BT']]
    gates=[];n=[0]
    def g(op,a,b):
        t=f't{n[0]}';n[0]+=1;gates.append((op,t,a,b));return t
    def lin(names,masks,ops):
        S=list(names);F=list(masks)
        for p in ops:
            a,b=map(int,p.split('+'));S.append(g('xor',S[a],S[b]));F.append(F[a]^F[b])
        return {f:s for f,s in reversed(list(zip(F,S)))}
    u=lin([f'x{i}' for i in range(8)],[1<<i for i in range(8)],d['U'])
    # inverse: input constant aff^-1(0)=0x05 handled below through the linear forms
    A=[u[f] for f in UT[:9]];B=[u[f] for f in UT[9:18]];L=[u[f] for f in UT[18:]]
    ps=[g('and',A[k],B[k]) for k in range(9)]
    pm=lin(ps,[1<<i for i in range(9)],d['P'])
    x1,x2,x3,x4=[g('xor',pm[PT[l]],L[l]) for l in range(4)]
    t1=g('xor',x1,x2);t2=g('and',x1,x3);t3=g('xor',x4,t2);t4=g('and',t1,t3);y4=g('xor',x2,t4)
    t5=g('xor',x3,x4);t6=g('xor',x2,t2);t7=g('and',t6,t5);y2=g('xor',x4,t7);t8=g('xor',x3,y2)
    t9=g('xor',t3,y2);t10=g('and',x4,t9);y1=g('xor',t10,t8);t11=g('xor',t3,t10);t12=g('and',y4,t11);y3=g('xor',t12,t1)
    y=[y1,y2,y3,y4];q=[y[o[k]] for k in range(4)]
    r=[[q[0],q[1]],[q[2],q[3]],[g('xor',q[0],q[2]),g('xor',q[1],q[3])]]
    W=[]
    for i in range(3): W+= [r[i][0],r[i][1],g('xor',r[i][0],r[i][1])]
    z=[g('and',W[k],A[k]) for k in range(9)]+[g('and',W[k],B[k]) for k in range(9)]
    b=lin(z,[1<<i for i in range(18)],d['B'])
    # middle AND order: the caller may reorder
    outs=[b[f] for f in BT]
    return gates,outs
def run(gates,outs,consts_in=0,consts_out=0):
    v={f'x{i}':sum(1<<x for x in range(256) if (x^consts_in)>>i&1) for i in range(8)}
    for op,t,a,b in gates:
        v[t]=v[a]&v[b] if op=='and' else v[a]^v[b]
    return [sum(((v[outs[j]]>>x&1)<<j) for j in range(8))^consts_out for x in range(256)]
if __name__=='__main__':
    S,SI=sboxes()
    for fn in sys.argv[1:]:
        L=open(fn).read().split('total')
        blk=('total'+L[-1]).strip().split('\n')
        inverse='inverse=1' in L[-1]
        gates,outs=build(blk,inverse)
        if not inverse: ok=run(gates,outs,0,0x63)==S
        else: ok=run(gates,outs,0x63,0)==SI
        print(fn,blk[0],'gates',len(gates),'and',sum(g[0]=='and' for g in gates),'correct',ok)
