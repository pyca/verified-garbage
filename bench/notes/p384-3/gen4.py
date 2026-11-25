"""Product and square; each reduction round runs as soon as its two words are final,
its multiplier's words kept apart (U) until the end."""
from gen3 import *
import sim
def rnd(b,R,w):
    """w: regs of words i..i+5 (T words then U words); frees w[0],w[1]; returns m0,m1 (new U words)"""
    m0,s,u1,zz,d0,d1,d2=R.get(7)
    t0,t1=w[0],w[1]
    b.lsl(m0,t0,32);b.extr(s,t1,t0,32);b.adds(m0,t0,m0);b.adc(s,t1,s);b.add(t0,s,t0)
    m1=t0;v=t1
    b.lsl(v,m0,32);b.extr(s,m1,m0,32);b.lsr(u1,m1,32)
    b.adds(zz,m1,v);b.adcs(d0,m0,s);b.adcs(d1,m1,u1);b.adc(d2,Z,Z)
    b.subs(v,m0,v);b.sbcs(zz,zz,s);b.sbcs(d0,d0,u1);b.sbcs(d1,d1,Z);b.sbc(d2,d2,Z)
    b.subs(w[2],w[2],d0);b.sbcs(w[3],w[3],d1);b.sbcs(w[4],w[4],d2);b.sbcs(w[5],w[5],Z);b.sbcs(m0,m0,Z);b.sbc(m1,m1,Z)
    R.put(s,u1,zz,d0,d1,d2,v)
    return m0,m1
def mulI(b,R=None):
    R=R or Regs(POOL)
    T={};U=[]
    def row(i,bs,x,t):
        b.ldr(x,('a',i))
        if i==0:
            for j in range(6): T[j]=R.get();b.mul(T[j],x,bs[j])
            for j in range(5): b.umulh(t,x,bs[j]);(b.adcs if j else b.adds)(T[j+1],T[j+1],t)
            T[6]=R.get(); b.umulh(t,x,bs[5]);b.adc(T[6],t,Z); return
        for j in range(6): b.mul(t,x,bs[j]);(b.adcs if j else b.adds)(T[i+j],T[i+j],t)
        T[i+6]=R.get(); b.adc(T[i+6],Z,Z)
        for j in range(6): b.umulh(t,x,bs[j]);(b.adc if j==5 else b.adcs if j else b.adds)(T[i+j+1],T[i+j+1],t)
    for k in range(3):
        bs=R.get(6);ld(b,bs,'b');x=R.get();t=R.get()
        row(2*k,bs,x,t);row(2*k+1,bs,x,t)
        R.put(x,t,*bs)
        w=[T[j] for j in range(2*k,6)]+U
        m0,m1=rnd(b,R,w[:6] ); U+= [m0,m1]
    U=U
    for k in range(6): (b.adcs if k else b.adds)(U[k],U[k],T[6+k])
    R.put(*[T[6+k] for k in range(6)])
    top=R.get();b.adc(top,Z,Z)
    return U+[top],R
def sqrI(b,R=None):
    R=R or Regs(POOL)
    a=R.get(6); ld(b,a,'a'); t=R.get();T={};U=[]
    dd=None
    for k in range(6):
        # row k: a_k * [a_k, 2a_{k+1}, d_{k+2},...,d_5, a5>>63]
        ws=[a[k]]
        if k<5:
            ws+= ['lsl']+[('d',j) for j in range(k+2,6)]+['top']
        raise NotImplementedError
def build4(kind):
    b=B(); b.movz(Z,0)
    T,R=mulI(b); finish(b,T,R); return b.o
if __name__=='__main__':
    for k in 'I':
        c=build4(k); check(c,k,6000); print(k,len(c),sim.both(c),'depth',sim.sim(c,rob=10**6,width=10**6))
