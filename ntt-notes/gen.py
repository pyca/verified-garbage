import sys
Q=3329
br=lambda k:int('{:07b}'.format(k)[::-1],2)
Z=[pow(17,br(k),Q) for k in range(128)]
def cen(z):
    z%=Q
    return z-Q if z>Q//2 else z
def tw(z): # round(z*2^15/Q), z centered
    return (2*z*2**15+Q)//(2*Q)
# instrs: tuples (op, d, srcs..., extra)
class T:
    def __init__(s): s.h=[]
    def vec(s,l):
        assert len(l)==8; s.h+=l; return len(s.h)//8-1
def pack(T_,l):
    l=l+[0]*(-len(l)%8)
    return [T_.vec(l[i:i+8]) for i in range(0,len(l),8)]
class G:
    def __init__(s): s.c=[]; s.t=T()
    def e(s,*a): s.c.append(a)
def red(g,b,m,t,z,zp):   # m,t temps: m=b*z mod q ; z,zp are operands strings
    pass
FN="vg_fwd"
def fwd(S1=None):
    g=G(); t=g.t
    zs=[cen(z) for z in Z]
    l=[Q,20159]
    pos={}
    for k in range(1,16): l+=[zs[k],tw(zs[k])]
    ks=pack(t,l)  # 4 vectors
    el=lambda i:(i//8,i%8)
    for i in range(4): g.e('ldr',f'v{i}','x2',16*ks[i])
    q=el(0); can=el(1)
    free=['v4','v5','v6','v7']
    def bf(u,v,z,zp):
        # returns (u', v') ; rotates free
        h=free.pop(0); m=free.pop(0)
        g.e('sqrdmulh',h,v,zp); g.e('mul',m,v,z); g.e('mls',m,h,q)
        g.e('sub',h,u,m); g.e('add',u,u,m)
        free.append(m); free.append(v)
        return u,h
    for j in range(2):
        r=[f'v{16+i}' for i in range(16)]
        for i in range(16): g.e('ldr',r[i],'x0',32*i+16*j)
        for ly in range(4):
            d=8>>ly
            for i in range(16):
                if i&d: continue
                k=(1<<ly)+(i>>(4-ly))
                r[i],r[i+d]=bf(r[i],r[i+d],el(2*k),el(2*k+1))
        for i in range(16): g.e('str',r[i],'x0',32*i+16*j)
        # give back regs
        allr=set(f'v{i}' for i in list(range(4,8))+list(range(16,32)))
        free[:]=sorted(allr-set(r[:]),key=lambda x:int(x[1:]))[:4]
        free=[x for x in free]
        # rename: next iteration assumes v16..31: ensure
        free[:]=['v4','v5','v6','v7']
    # pass 2
    l=[]
    for b in range(16): l+=[zs[16+b],tw(zs[16+b])]
    k5=pack(t,l)
    for i in range(4): g.e('ldr',f'v{i}','x2',16*k5[i])
    qv='v7'
    kq=t.vec([Q,20159]*4)
    g.e('ldr','v7','x2',16*kq)
    Qe=(7,0); Ce=(7,1)
    regs=[f'v{i}' for i in range(16,32)]+['v4','v5','v6']
    for b in range(16):
        f=list(regs); regs=regs[8:]+regs[:8]
        A,B,h,m,z1,z1p=f[:6]
        g.e('ldr',A,'x0',32*b); g.e('ldr',B,'x0',32*b+16)
        def bf2(u,v,z,zp,h,m):
            g.e('sqrdmulh',h,v,zp); g.e('mul',m,v,z); g.e('mls',m,h,Qe)
            g.e('sub',v,u,m); g.e('add',u,u,m)
        bf2(A,B,el(2*b),el(2*b+1),h,m)
        z6=[zs[32+2*b+i//4] for i in range(8)]
        z7=[zs[64+4*b+i//2] for i in range(8)]
        a=t.vec(z6); ap=t.vec([tw(x) for x in z6]); c=t.vec(z7); cp=t.vec([tw(x) for x in z7])
        g.e('trn1.2d',h,A,B); g.e('trn2.2d',m,A,B)
        U,V=h,m
        g.e('ldr',z1,'x2',16*a); g.e('ldr',z1p,'x2',16*ap)
        bf2(U,V,z1,z1p,A,B)
        g.e('trn1.4s',A,U,V); g.e('trn2.4s',B,U,V)
        g.e('ldr',z1,'x2',16*c); g.e('ldr',z1p,'x2',16*cp)
        bf2(A,B,z1,z1p,U,V)
        for X,y in ((A,U),(B,V)):
            g.e('sqrdmulh',y,X,Ce); g.e('sshr',y,y,11); g.e('mls',X,y,Qe)
        g.e('zip1.4s',U,A,B); g.e('zip2.4s',V,A,B)
        g.e('str',U,'x0',32*b); g.e('str',V,'x0',32*b+16)
    return g
def inv():
    g=G(); t=g.t
    n=lambda k: cen(Z[k])
    el=lambda i:(i//8,i%8)
    F=3303
    # pass A
    l=[]
    for b in range(16):
        z=cen(Z[31-b]); l+=[z,tw(z)]
    k5=pack(t,l)
    for i in range(4): g.e('ldr',f'v{i}','x2',16*k5[i])
    kq=t.vec([Q,20159]*4)
    g.e('ldr','v7','x2',16*kq); Qe=(7,0)
    regs=[f'v{i}' for i in range(16,32)]+['v4','v5','v6']
    for b in range(16):
        f=list(regs); regs=regs[8:]+regs[:8]
        A,B,W,X,z1,z1p,h=f[:7]
        g.e('ldr',A,'x0',32*b); g.e('ldr',B,'x0',32*b+16)
        g.e('uzp1.4s',W,A,B); g.e('uzp2.4s',X,A,B)
        z6=[cen(Z[63-2*b-i//4]) for i in range(8)]
        z7=[cen(Z[127-4*b-i//2]) for i in range(8)]
        c=t.vec(z7); cp=t.vec([tw(x) for x in z7]);a=t.vec(z6); ap=t.vec([tw(x) for x in z6]); 
        def ib(u,v,z,zp,dd,h,S):  # S=u+v ; D=(v-u)z in dd
            g.e('sub',dd,v,u); g.e('add',S,u,v)
            g.e('sqrdmulh',h,dd,zp); g.e('mul',dd,dd,z); g.e('mls',dd,h,Qe)
        g.e('ldr',z1,'x2',16*c); g.e('ldr',z1p,'x2',16*cp)
        ib(W,X,z1,z1p,A,h,W)     # S=W D=A
        g.e('trn1.4s',B,W,A); g.e('trn2.4s',X,W,A)
        g.e('ldr',z1,'x2',16*a); g.e('ldr',z1p,'x2',16*ap)
        ib(B,X,z1,z1p,A,h,B)
        g.e('trn1.2d',W,B,A); g.e('trn2.2d',X,B,A)
        ib(W,X,el(2*b),el(2*b+1),A,h,W)
        g.e('str',W,'x0',32*b); g.e('str',A,'x0',32*b+16)
    # pass B
    l=[Q,20159]
    f=cen(F); l+=[f,tw(f)]
    ix={}
    def put(k,m=1):
        nonlocal l
        z=cen(Z[k]*m); ix[k]=len(l); l+=[z,tw(z)]
    for k in range(8,16): put(k,F)
    for k in range(1,8): put(k)
    ks=pack(t,l)
    k8=t.vec([8*Q]*2+[0]*6); kqv=t.vec([Q]*8)
    for i in range(5): g.e('ldr',f'v{i}','x2',16*ks[i])
    Q0=(0,0); C0=(0,1); F0=(0,2); F1=(0,3)
    for j in range(2):
        r=[f'v{16+i}' for i in range(16)]
        for i in range(16): g.e('ldr',r[i],'x0',32*i+16*j)
        for ly in (3,2,1,0):
            d=8>>ly
            if ly==3 and j==0: g.e('ldr','v7','x2',16*k8)
            if ly==0: g.e('ldr','v7','x2',16*kqv)
            for i in range(16):
                if i&d: continue
                k=(2<<ly)-1-(i>>(4-ly))
                u,v=r[i],r[i+d]
                z,zp=el(ix[k]),el(ix[k]+1)
                fr=['v5','v6']
                h,m=fr
                g.e('sub',h,v,u); g.e('add',u,u,v)
                if ly==3 and j==0: g.e('sub',u,u,'v7')
                g.e('sqrdmulh',m,h,zp); g.e('mul',v,h,z); g.e('mls',v,m,Q0)
                if ly==3:
                    g.e('sqrdmulh',m,u,F1); g.e('mul',u,u,F0); g.e('mls',u,m,Q0)
                if ly==0:
                    g.e('sqrdmulh',m,u,C0); g.e('sshr',m,m,11); g.e('mls',u,m,Q0)
                    g.e('sshr',m,v,15); g.e('and',m,m,'v7'); g.e('add',v,v,m)
        for i in range(16): g.e('str',r[i],'x0',32*i+16*j)
    return g
def asm(i):
    o=i[0]
    def V(x,s='8h'):
        if isinstance(x,tuple): return f'v{x[0]}.h[{x[1]}]'
        return f'{x}.{s}'
    if o in('ldr','str'): return f'{o} q{i[1][1:]}, [{i[2]}, #{i[3]}]'
    if o=='sshr': return f'sshr {V(i[1])}, {V(i[2])}, #{i[3]}'
    if o=='and': return f'and {V(i[1],"16b")}, {V(i[2],"16b")}, {V(i[3],"16b")}'
    if '.' in o:
        p,s=o.split('.'); return f'{p} {V(i[1],s)}, {V(i[2],s)}, {V(i[3],s)}'
    return f'{o} '+', '.join(V(x) for x in i[1:])
def emit(g,name):
    s=f'.globl {name}\n.p2align 4\n{name}:\nadrp x2, {name}_t\nadd x2, x2, :lo12:{name}_t\n'
    s+='\n'.join(asm(i) for i in g.c)+'\nret\n'
    s+='.section .rodata\n.p2align 4\n'+f'{name}_t:\n'+'\n'.join(f'.hword {x&0xffff}' for x in g.t.h)+'\n.text\n'
    return s
if __name__=='__main__':
    from collections import Counter
    a,b=fwd(),inv()
    for g in (a,b):
        c=Counter(i[0] for i in g.c); print(len(g.c),len(g.t.h)*2,dict(c),file=sys.stderr)
    open('p.s','w').write('.text\n'+emit(a,'my_fwd')+emit(b,'my_inv')+'.section .note.GNU-stack,"",%progbits\n')
