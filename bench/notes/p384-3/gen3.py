"""Product and square with the reduction of two words as soon as they are final (NOTES: after the measurements)."""
from gen import *
class Regs:
    def __init__(s,pool): s.free=list(pool)
    def get(s,n=None):
        if n is None: return s.free.pop(0)
        return [s.free.pop(0) for _ in range(n)]
    def put(s,*xs):
        for x in xs:
            assert x not in s.free; s.free.append(x)
POOL=[1,2,3,4,5,6]+list(range(8,18))+[21,22,23,24,25]
POOL26=POOL+[26]
def redA(b,R,t):
    """t: words; returns t[2:] with M p added; two words"""
    t=list(t)
    m0,s,u1,zz,d0,d1,d2=R.get(7)
    b.lsl(m0,t[0],32);b.extr(s,t[1],t[0],32);b.adds(m0,t[0],m0);b.adc(s,t[1],s);b.add(t[0],s,t[0])
    m1=t[0];v=t[1]
    b.lsl(v,m0,32);b.extr(s,m1,m0,32);b.lsr(u1,m1,32)
    b.adds(zz,m1,v);b.adcs(d0,m0,s);b.adcs(d1,m1,u1);b.adc(d2,Z,Z)
    b.subs(v,m0,v);b.sbcs(zz,zz,s);b.sbcs(d0,d0,u1);b.sbcs(d1,d1,Z);b.sbc(d2,d2,Z)
    b.subs(t[2],t[2],d0);b.sbcs(t[3],t[3],d1);b.sbcs(t[4],t[4],d2);b.sbcs(t[5],t[5],Z);b.sbcs(m0,m0,Z);b.sbc(m1,m1,Z)
    b.adds(t[6],t[6],m0);b.adcs(t[7],t[7],m1)
    R.put(m0,s,u1,zz,d0,d1,d2,m1,v)
    return t[2:]
def mulC(b,R=None):
    R=R or Regs(POOL)
    bs=R.get(6); ld(b,bs,'b'); x=R.get();t=R.get()
    T=R.get(6); 
    b.ldr(x,('a',0))
    for j in range(6): b.mul(T[j],x,bs[j])
    for j in range(5): b.umulh(t,x,bs[j]);(b.adcs if j else b.adds)(T[j+1],T[j+1],t)
    T.append(R.get()); b.umulh(t,x,bs[5]);b.adc(T[6],t,Z)
    def row(i,T,fresh):
        b.ldr(x,('a',i))
        for j in range(6): b.mul(t,x,bs[j]);(b.adcs if j else b.adds)(T[j],T[j],t)
        if fresh: b.adc(T[6],Z,Z)
        else: b.adcs(T[6],T[6],Z);b.adc(T[7],Z,Z)
        for j in range(5): b.umulh(t,x,bs[j]);(b.adcs if j else b.adds)(T[j+1],T[j+1],t)
        b.umulh(t,x,bs[5])
        if fresh: b.adc(T[6],T[6],t)
        else: b.adcs(T[6],T[6],t);b.adc(T[7],T[7],Z)
    T.append(R.get()); row(1,T[1:],True)
    T.append(None)
    for k in range(3):
        if k:
            T.append(None) if False else None
            T[7]=R.get(); row(2*k,T[0:8],False)
            T8=R.get(); row(2*k+1,T[1:8]+[T8],False)
        R.put(x,t)
        T2=redA(b,R,T[:8]); 
        x=R.get();t=R.get()
        # carry of the top addition
        top=T8 if k else R.get(); b.adc(top,T8 if k else Z,Z)
        T=T2+[top,None]
    return T[:7],R
def sqrC(b,R=None):
    R=R or Regs(POOL)
    a=R.get(6); ld(b,a,'a')
    # row k: words 2k.. : a_k*(a_k, 2a_{k+1}, d_{k+2}.., d_5, a5>>63)
    t=R.get()
    T=[]
    raise NotImplementedError
def finish(b,T,R):
    tt=T[:6];top=T[6]
    f=[x for x in POOL+[26] if x not in T]
    o,p0,p1,p2=f[:4]; d=f[4:10]
    b.subImm(o,Z,1);b.lsr(p0,o,32);b.lsl(p1,o,32);b.subImm(p2,o,1)
    for k,m in enumerate([p0,p1,p2,o,o,o]): (b.sbcs if k else b.subs)(d[k],tt[k],m)
    b.sbcs(top,top,Z)
    for k in range(6): b.csel(tt[k],d[k],tt[k])
    for k in range(6): b.str(tt[k],('o',k))
def build3(kind):
    b=B(); b.movz(Z,0)
    T,R=mulC(b) if kind=='C' else sqrC(b)
    finish(b,T,R); return b.o
def check(c,kind,N=3000):
    for n in range(N):
        f=lambda q:random.choice([0,1,q-1,q-2,2**192-1,2**192,q-2**192]) if random.random()<.3 else random.randrange(q)
        a=f(2**384) if kind!='Q' else f(p); bb=f(p) if kind!='Q' else a
        mem={('a',i):a>>64*i&W-1 for i in range(6)}; mem.update({('b',i):bb>>64*i&W-1 for i in range(6)})
        m,_=run(c,mem); o=sum(m[('o',i)]<<64*i for i in range(6))
        assert o==a*bb*pow(2,-384,p)%p,(kind,n)
if __name__=='__main__':
    import sim
    c=build3('C'); check(c,'C'); print(len(c),sim.both(c),'depth',sim.sim(c,rob=10**6,width=10**6))
