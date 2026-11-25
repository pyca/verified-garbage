"""Checks of the identities in NOTES.md, on random and edge values.  x = 2^32."""
import random
X=2**32; W=2**64; R=2**384
p=2**384-2**128-2**96+2**32-1
assert p==X**12-X**4-X**3+X-1
# -p^-1 modulo x^4
assert pow(-p,-1,X**4)==1+X+X*X
assert pow(-p,-1,W)==1+X
lo=lambda v:v%W
def red2(t):
    """two words at a time; t: six words; returns six words"""
    b=0
    s0=lo(t[0]<<32); s1=lo((t[1]<<32)|(t[0]>>32))
    m0=t[0]+s0; c=m0>>64; m0=lo(m0)
    m1=lo(t[1]+s1+c+t[0])
    v=lo(m0<<32); u0=lo((m1<<32)|(m0>>32)); u1=m1>>32
    # z = m1+v -> ka
    z=m1+v; ka=z>>64; z=lo(z)
    d0=m0+u0+ka; c=d0>>64; d0=lo(d0)
    d1=m1+u1+c; d2=d1>>64; d1=lo(d1)
    b0=1 if m0<v else 0
    kb=1 if z<u0+b0 else 0
    assert lo(z-u0-b0)==t[1], "low words cancel"
    D=d0+W*d1+W*W*d2-u1-kb
    assert D>=0
    M=m0+W*m1
    T=sum(w*W**i for i,w in enumerate(t))
    assert (T+M*p)%(W*W)==0
    r=(T+M*p)>>128
    Th=T>>128
    assert r==Th-D+M*W**4 and 0<=r<R
    return [(r>>(64*i))%W for i in range(6)]
def words(v,n=6): return [(v>>(64*i))%W for i in range(n)]
def montred(T):
    t=words(T%R)
    for _ in range(3): t=red2(t)
    return sum(w*W**i for i,w in enumerate(t))+(T>>384)
edge=[0,1,X-1,X,X+1,W-X,W-1,W-X+1,2**63]
for k in range(60000):
    ws=[random.choice(edge) if random.random()<.6 else random.getrandbits(64) for _ in range(12)]
    T=sum(w*W**i for i,w in enumerate(ws))%(R*p)
    v=montred(T); assert v<2*p and v*R%p==T%p
# Karatsuba with masks in place of absolute values
H=2**192
for k in range(60000):
    f=lambda:random.choice([0,R-1,p-1,H,H-1,R-H]) if random.random()<.3 else random.getrandbits(384)
    a,b=f(),f()
    a0,a1,b0,b1=a%H,a//H,b%H,b//H
    ma=a0<a1; mb=b1<b0
    A=(a0-a1)%H; B=(b1-b0)%H
    P1=(A*B-H*((B if ma else 0)+(A if mb else 0))+H*H*(ma and mb))
    assert P1==(a0-a1)*(b1-b0)
    mid=a0*b0+a1*b1+P1
    assert mid==a0*b1+a1*b0 and mid<2**385
    assert a0*b0+H*mid+H*H*a1*b1==a*b
# halved doubling
def dbl(x,y,z):
    i2=pow(2,-1,p)
    d=z*z%p; B=y*y%p; C=x*B%p; a=(x-d)*(x+d)%p; A=3*a*i2%p
    X3=(A*A-2*C)%p; return X3,(A*(C-X3)-B*B)%p,y*z%p
def dblref(x,y,z):
    m=3*(x*x-z**4)%p; s=4*x*y*y%p
    X3=(m*m-2*s)%p; return X3,(m*(s-X3)-8*y**4)%p,2*y*z%p
for k in range(200):
    x,y,z=[random.randrange(1,p) for _ in range(3)]
    a=dbl(x,y,z); b=dblref(x,y,z)  # same point: (l^2 X, l^3 Y, l Z), l = 2
    assert b==(4*a[0]%p,8*a[1]%p,2*a[2]%p)
print("ok")
