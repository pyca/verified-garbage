"""P-384 field code for AArch64 from NOTES.md: emitted, interpreted on integers, printed."""
import random
p=2**384-2**128-2**96+2**32-1; W=2**64
Z=7
class B:
    def __init__(s): s.o=[]
    def __getattr__(s,n):
        return lambda *a: s.o.append((n,)+a)
def run(code,mem,regs=None):
    r=dict(regs or {}); C=None
    for i in code:
        op=i[0]; a=i[1:]
        if op=='ldr': r[a[0]]=mem[a[1]]
        elif op=='str': mem[a[1]]=r[a[0]]
        elif op=='movz': r[a[0]]=a[1]
        elif op=='mul': r[a[0]]=r[a[1]]*r[a[2]]%W
        elif op=='umulh': r[a[0]]=r[a[1]]*r[a[2]]>>64
        elif op in('add','adds','adc','adcs'):
            v=r[a[1]]+r[a[2]]+(C if 'c' in op else 0); r[a[0]]=v%W
            if op[-1]=='s': C=v>>64
        elif op in('sub','subs','sbc','sbcs'):
            v=r[a[1]]+(W-1-r[a[2]])+(C if 'bc' in op else 1); r[a[0]]=v%W
            if op in('subs','sbcs'): C=v>>64
        elif op=='and_': r[a[0]]=r[a[1]]&r[a[2]]
        elif op=='csel': r[a[0]]=r[a[1]] if C else r[a[2]]
        elif op=='lsl': r[a[0]]=(r[a[1]]<<a[2])%W
        elif op=='lsr': r[a[0]]=r[a[1]]>>a[2]
        elif op=='extr': r[a[0]]=((r[a[1]]<<64|r[a[2]])>>a[3])%W
        elif op=='subImm': r[a[0]]=(r[a[1]]-a[2])%W
        else: raise Exception(op)
    return mem,r
# memory: names ('a',i) ('b',i) ('t',i) ('o',i)
def ld(b,rs,n,off=0):
    for k,x in enumerate(rs): b.ldr(x,(n,off+k))
def mul3(b,Q,A,Bs,t=2):
    b.mul(Q[0],A[0],Bs[0]); b.mul(Q[1],A[0],Bs[1]); b.mul(Q[2],A[0],Bs[2])
    b.umulh(t,A[0],Bs[0]); b.adds(Q[1],Q[1],t); b.umulh(t,A[0],Bs[1]); b.adcs(Q[2],Q[2],t)
    b.umulh(t,A[0],Bs[2]); b.adc(Q[3],t,Z)
    for i in(1,2):
        for j in range(3):
            b.mul(t,A[i],Bs[j]); (b.adcs if j else b.adds)(Q[i+j],Q[i+j],t)
        b.adc(Q[i+3],Z,Z)
        for j in range(3):
            b.umulh(t,A[i],Bs[j]); (b.adc if j==2 else b.adcs if j else b.adds)(Q[i+j+1],Q[i+j+1],t)
A=[4,5,6]; BB=[8,9,10]; P0=[11,12,13,14,15,21]; P2=[17,22,23,24,25,1]
def kmid(b):
    X=[1,2,3]
    ld(b,A,'a');ld(b,X,'a',3)
    b.subs(A[0],A[0],X[0]);b.sbcs(A[1],A[1],X[1]);b.sbcs(A[2],A[2],X[2]);b.sbc(16,Z,Z)
    ld(b,BB,'b',3);ld(b,X,'b')
    b.subs(BB[0],BB[0],X[0]);b.sbcs(BB[1],BB[1],X[1]);b.sbcs(BB[2],BB[2],X[2]);b.sbc(17,Z,Z)
    mul3(b,P0,A,BB)
    for k in range(3): b.and_(BB[k],BB[k],16)
    for k in range(3): b.and_(A[k],A[k],17)
    b.and_(16,16,17)
    b.subs(P0[3],P0[3],BB[0]);b.sbcs(P0[4],P0[4],BB[1]);b.sbcs(P0[5],P0[5],BB[2]);b.sbc(3,Z,Z)
    b.subs(P0[3],P0[3],A[0]);b.sbcs(P0[4],P0[4],A[1]);b.sbcs(P0[5],P0[5],A[2]);b.sbc(3,3,Z)
    b.sub(16,3,16)
    for k in range(6): b.str(P0[k],('t',k))
def prodK(b):
    kmid(b)
    ld(b,A,'a');ld(b,BB,'b');mul3(b,P0,A,BB)
    ld(b,A,'a',3);ld(b,BB,'b',3);mul3(b,P2,A,BB)
    s=A
    b.adds(s[0],P0[3],P2[0]);b.adcs(s[1],P0[4],P2[1]);b.adcs(s[2],P0[5],P2[2]);b.adc(8,Z,Z)
    T3=[P0[3],P0[4],P0[5]]
    b.adds(T3[0],s[0],P0[0]);b.adcs(T3[1],s[1],P0[1]);b.adcs(T3[2],s[2],P0[2]);b.adc(9,8,Z)
    b.adds(s[0],s[0],P2[3]);b.adcs(s[1],s[1],P2[4]);b.adcs(s[2],s[2],P2[5]);b.adc(8,8,Z)
    b.adds(s[0],s[0],9);b.adcs(s[1],s[1],Z);b.adcs(s[2],s[2],Z);b.adc(8,8,Z)
    for k,x in enumerate(T3+s):
        b.ldr(2,('t',k)); (b.adcs if k else b.adds)(x,x,2)
    b.adc(8,8,16)
    h=P2[3:]
    b.adds(h[0],h[0],8);b.adcs(h[1],h[1],Z);b.adc(h[2],h[2],Z)
    return P0[:3]+T3,s+h
def prodS(b):
    bs=[4,5,6,8,9,10]; c=[11,12,13,14,15,21,16,17,22,23,24,25]
    ld(b,bs,'b'); t=2;x=3
    b.ldr(x,('a',0))
    for j in range(6): b.mul(c[j],x,bs[j])
    for j in range(5): b.umulh(t,x,bs[j]);(b.adcs if j else b.adds)(c[j+1],c[j+1],t)
    b.umulh(t,x,bs[5]);b.adc(c[6],t,Z)
    for i in range(1,6):
        b.ldr(x,('a',i))
        for j in range(6): b.mul(t,x,bs[j]);(b.adcs if j else b.adds)(c[i+j],c[i+j],t)
        b.adc(c[i+6],Z,Z)
        for j in range(6): b.umulh(t,x,bs[j]);(b.adc if j==5 else b.adcs if j else b.adds)(c[i+j+1],c[i+j+1],t)
    return c[:6],c[6:]
def sq(b):
    a=[4,5,6,8,9,10]; c=[3,11,12,13,14,15,21,16,17,22,23,24]; t=2
    ld(b,a,'a')
    for j in range(1,6): b.mul(c[j],a[0],a[j])
    for j in range(1,5): b.umulh(t,a[0],a[j]);(b.adcs if j>1 else b.adds)(c[j+1],c[j+1],t)
    b.umulh(t,a[0],a[5]);b.adc(c[6],t,Z)
    for i in range(1,5):
        for j in range(i+1,6): b.mul(t,a[i],a[j]);(b.adcs if j>i+1 else b.adds)(c[i+j],c[i+j],t)
        if i==4: b.umulh(t,a[4],a[5]);b.adc(c[10],t,Z);break
        b.adc(c[i+6],Z,Z)
        for j in range(i+1,6):
            b.umulh(t,a[i],a[j]);(b.adc if j==5 else b.adcs if j>i+1 else b.adds)(c[i+j+1],c[i+j+1],t)
    b.adds(c[1],c[1],c[1])
    for j in range(2,11): b.adcs(c[j],c[j],c[j])
    b.adc(c[11],Z,Z)
    b.mul(c[0],a[0],a[0])
    for i in range(6):
        if i: b.mul(t,a[i],a[i]);b.adcs(c[2*i],c[2*i],t)
        b.umulh(t,a[i],a[i]);(b.adds if i==0 else b.adc if i==5 else b.adcs)(c[2*i+1],c[2*i+1],t)
    return c[:6],c[6:]
def red(b,t,hi,tmps):
    t=list(t)
    for _ in range(3):
        m0,s,u1,zz,d0,d1,d2=tmps
        b.lsl(m0,t[0],32);b.extr(s,t[1],t[0],32);b.adds(m0,t[0],m0);b.adc(s,t[1],s);b.add(t[0],s,t[0])
        m1=t[0];v=t[1];u0=s
        b.lsl(v,m0,32);b.extr(u0,m1,m0,32);b.lsr(u1,m1,32)
        b.adds(zz,m1,v);b.adcs(d0,m0,u0);b.adcs(d1,m1,u1);b.adc(d2,Z,Z)
        b.subs(v,m0,v);b.sbcs(zz,zz,u0);b.sbcs(d0,d0,u1);b.sbcs(d1,d1,Z);b.sbc(d2,d2,Z)
        b.subs(t[2],t[2],d0);b.sbcs(t[3],t[3],d1);b.sbcs(t[4],t[4],d2);b.sbcs(t[5],t[5],Z);b.sbcs(m0,m0,Z);b.sbc(m1,m1,Z)
        t=t[2:]+[m0,m1]
        tmps=[v,s,u1,zz,d0,d1,d2]
    for k in range(6): (b.adcs if k else b.adds)(t[k],t[k],hi[k])
    free=[x for x in [2]+tmps+list(hi)]
    top=free[0]; b.adc(top,Z,Z)
    ones,p0,p1,p2=free[1:5]; d=free[5:11]
    b.subImm(ones,Z,1);b.lsr(p0,ones,32);b.lsl(p1,ones,32);b.subImm(p2,ones,1)
    for k,m in enumerate([p0,p1,p2,ones,ones,ones]): (b.sbcs if k else b.subs)(d[k],t[k],m)
    b.sbcs(top,top,Z)
    for k in range(6): b.csel(t[k],d[k],t[k])
    for k in range(6): b.str(t[k],('o',k))
def build(kind):
    b=B(); b.movz(Z,0)
    L,H={'K':prodK,'S':prodS,'Q':sq}[kind](b)
    used=set(L+H)|{7,2,0}
    free=[x for x in list(range(1,18))+[21,22,23,24,25] if x not in used]
    red(b,L,H,free[:7]); return b.o
if __name__=='__main__':
    for k in 'KSQ':
        c=build(k); 
        for n in range(3000):
            f=lambda q:random.choice([0,1,q-1,q-2,2**192-1,2**192,q-2**192]) if random.random()<.3 else random.randrange(q)
            a=f(2**384) if k!='Q' else f(p); bb=f(p) if k!='Q' else a
            mem={('a',i):a>>64*i&W-1 for i in range(6)}; mem.update({('b',i):bb>>64*i&W-1 for i in range(6)})
            m,_=run(c,mem); o=sum(m[('o',i)]<<64*i for i in range(6))
            assert o==a*bb*pow(2,-384,p)%p,(k,n)
        from collections import Counter
        cn=Counter(i[0] for i in c); print(k,len(c),cn['mul']+cn['umulh'],cn['ldr']+cn['str'])
