from gen import *
def row0(b,x,Bs,Q,t=2):
    for j in range(3): b.mul(Q[j],x,Bs[j])
    b.umulh(t,x,Bs[0]); b.adds(Q[1],Q[1],t); b.umulh(t,x,Bs[1]); b.adcs(Q[2],Q[2],t); b.umulh(t,x,Bs[2]); b.adc(Q[3],t,Z)
def rown(b,x,Bs,Q,t=2):
    for j in range(3): b.mul(t,x,Bs[j]); (b.adcs if j else b.adds)(Q[j],Q[j],t)
    b.adc(Q[3],Z,Z)
    for j in range(3): b.umulh(t,x,Bs[j]); (b.adc if j==2 else b.adcs if j else b.adds)(Q[j+1],Q[j+1],t)
def mul3g(b,xs,pre,Bs,Q):
    pre(0); row0(b,xs[0],Bs,Q)
    for i in(1,2): pre(i); rown(b,xs[i],Bs,Q[i:])
V=[11,12,13,14,15,21]; Q0=[17,22,23,24,25,16]; Q2=[24,25,16,4,5,6]; T=1
def addc(b,d,n,m,first=True):
    for k in range(len(d)): (b.adds if first and k==0 else b.adcs)(d[k],n[k],m[k])
def kprod(b):
    X=[11,12,13];A=[4,5,6];BB=[8,9,10]
    ld(b,A,'a');ld(b,X,'a',3)
    b.subs(A[0],A[0],X[0]);b.sbcs(A[1],A[1],X[1]);b.sbcs(A[2],A[2],X[2]);b.sbc(16,Z,Z)
    ld(b,BB,'b',3);ld(b,X,'b')
    b.subs(BB[0],BB[0],X[0]);b.sbcs(BB[1],BB[1],X[1]);b.sbcs(BB[2],BB[2],X[2]);b.sbc(17,Z,Z)
    mul3g(b,A,lambda i:0,BB,V)
    for k in range(3): b.and_(BB[k],BB[k],16)
    for k in range(3): b.and_(A[k],A[k],17)
    b.and_(16,16,17)
    b.subs(V[3],V[3],BB[0]);b.sbcs(V[4],V[4],BB[1]);b.sbcs(V[5],V[5],BB[2]);b.sbc(T,Z,Z)
    b.subs(V[3],V[3],A[0]);b.sbcs(V[4],V[4],A[1]);b.sbcs(V[5],V[5],A[2]);b.sbc(T,T,Z)
    b.sub(T,T,16)
    ld(b,BB,'b'); ld(b,A,'a'); mul3g(b,A,lambda i:0,BB,Q0)
    addc(b,V,V,Q0); b.adc(T,T,Z)
    addc(b,V,V,Q0[3:]+[Z]*3); b.adc(T,T,Z)
    ld(b,BB,'b',3); mul3g(b,[3,3,3],lambda i:b.ldr(3,('a',3+i)),BB,Q2)
    addc(b,V,V,Q2); b.adc(T,T,Z)
    addc(b,V[3:]+Q2[3:5],V[3:]+Q2[3:5],Q2[:3]+[T,Z]); b.adc(Q2[5],Q2[5],Z)
    return Q0[:3]+V[:3],V[3:]+Q2[3:]
def sqr(b):
    a=[8,9,10,16,24,25]; c=[17,22,23,11,12,13,14,15,21,4,5,6]; t=2
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
    addc(b,c[1:11],c[1:11],c[1:11]); b.adc(c[11],Z,Z)
    b.mul(c[0],a[0],a[0])
    for i in range(6):
        if i: b.mul(t,a[i],a[i]);b.adcs(c[2*i],c[2*i],t)
        b.umulh(t,a[i],a[i]);(b.adds if i==0 else b.adc if i==5 else b.adcs)(c[2*i+1],c[2*i+1],t)
    return c[:6],c[6:]
def rround(b,t,m0,m1,v,s=1,u1=2,zz=3,d0=16,d1=24,d2=25):
    b.lsl(m0,t[0],32);b.extr(s,t[1],t[0],32);b.adds(m0,t[0],m0);b.adc(s,t[1],s);b.add(m1,s,t[0])
    u0=s
    b.lsl(v,m0,32);b.extr(u0,m1,m0,32);b.lsr(u1,m1,32)
    b.adds(zz,m1,v);b.adcs(d0,m0,u0);b.adcs(d1,m1,u1);b.adc(d2,Z,Z)
    b.subs(v,m0,v);b.sbcs(zz,zz,u0);b.sbcs(d0,d0,u1);b.sbcs(d1,d1,Z);b.sbc(d2,d2,Z)
    b.subs(t[2],t[2],d0);b.sbcs(t[3],t[3],d1);b.sbcs(t[4],t[4],d2);b.sbcs(t[5],t[5],Z);b.sbcs(m0,m0,Z);b.sbc(m1,m1,Z)
    return t[2:]+[m0,m1]
def fin(b,t,hi):
    t=rround(b,t,8,9,17); t=rround(b,t,10,22,23); t=rround(b,t,11,12,13)
    addc(b,t,t,hi); b.adc(13,Z,Z)
    p0,p1,p2,o=23,24,25,26
    b.subImm(o,Z,1);b.lsr(p0,o,32);b.lsl(p1,o,32);b.subImm(p2,o,1)
    d=[1,3,4,5,6,16]
    for k,m in enumerate([p0,p1,p2,o,o,o]): (b.sbcs if k else b.subs)(d[k],t[k],m)
    b.sbcs(2,13,Z)
    for k in range(6): b.csel(t[k],d[k],t[k])
    for k in range(6): b.str(t[k],('o',k))
def build2(kind):
    b=B(); b.movz(Z,0)
    fin(b,*(kprod(b) if kind=='K' else sqr(b))); return b.o
if __name__=='__main__':
    for k in 'KQ':
        c=build2(k)
        for n in range(5000):
            f=lambda q:random.choice([0,1,q-1,q-2,2**192-1,2**192,q-2**192]) if random.random()<.3 else random.randrange(q)
            a=f(2**384) if k!='Q' else f(p); bb=f(p) if k!='Q' else a
            mem={('a',i):a>>64*i&W-1 for i in range(6)}; mem.update({('b',i):bb>>64*i&W-1 for i in range(6)})
            m,_=run(c,mem); o=sum(m[('o',i)]<<64*i for i in range(6))
            assert o==a*bb*pow(2,-384,p)%p,(k,n)
        print(k,len(c))
