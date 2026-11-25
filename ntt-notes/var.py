from gen import *
import gen
def zipr(ls):
    out=[]
    for k in range(max(map(len,ls))):
        for l in ls:
            if k<len(l): out.append(l[k])
    return out
def stag(ls,d):  # block i starts d instrs after block i-1 ; stable by virtual time
    out=[]
    for i,l in enumerate(ls):
        for k,x in enumerate(l): out.append((k+i*d,i,x))
    out.sort(key=lambda t:(t[0],t[1])); return [x for _,_,x in out]
TMP=['v4','v5','v6','v7']
def fwd2(p1=2,p2=2,st=None):
    g=G(); t=g.t
    zs=[cen(z) for z in Z]
    l=[Q,20159]
    for k in range(1,16): l+=[zs[k],tw(zs[k])]
    ks=pack(t,l); el=lambda i:(i//8,i%8)
    for i in range(4): g.e('ldr',f'v{i}','x2',16*ks[i])
    q=el(0)
    for j in range(2):
        r=[f'v{16+i}' for i in range(16)]
        free=list(TMP)
        for i in range(16): g.e('ldr',r[i],'x0',32*i+16*j)
        for ly in range(4):
            d=8>>ly
            idx=[i for i in range(16) if not i&d]
            for c in range(0,8,p1):
                grp=[]
                nf=[]
                tm=free[:2*p1]; rest=free[2*p1:]
                for n,i in enumerate(idx[c:c+p1]):
                    k=(1<<ly)+(i>>(4-ly)); z,zp=el(2*k),el(2*k+1)
                    h,m=tm[2*n],tm[2*n+1]; u,v=r[i],r[i+d]
                    grp.append([('sqrdmulh',h,v,zp),('mul',m,v,z),('mls',m,h,q),('sub',h,u,m),('add',u,u,m)])
                    r[i+d]=h; nf+=[m,v]
                g.c+=zipr(grp); free=rest+nf
        for i in range(16): g.e('str',r[i],'x0',32*i+16*j)
    l=[]
    for b in range(16): l+=[zs[16+b],tw(zs[16+b])]
    k5=pack(t,l)
    for i in range(4): g.e('ldr',f'v{i}','x2',16*k5[i])
    kq=t.vec([Q,20159]*4)
    g.e('ldr','v7','x2',16*kq); Qe=(7,0); Ce=(7,1)
    regs=[f'v{i}' for i in range(16,32)]+['v4','v5','v6']
    blocks=[]
    for b in range(16):
        c=[]; e=lambda *a:c.append(a)
        f=regs[:6]; regs=regs[6:]+regs[:6]
        if p2==2 or p2==3: pass
        A,B,h,m,z1,z1p=f
        e('ldr',A,'x0',32*b); e('ldr',B,'x0',32*b+16)
        z6=[zs[32+2*b+i//4] for i in range(8)]; z7=[zs[64+4*b+i//2] for i in range(8)]
        a=t.vec(z6); ap=t.vec([tw(x) for x in z6]); cc=t.vec(z7); cp=t.vec([tw(x) for x in z7])
        def bf2(u,v,z,zp,h,m):
            e('sqrdmulh',h,v,zp); e('mul',m,v,z); e('mls',m,h,Qe); e('sub',v,u,m); e('add',u,u,m)
        bf2(A,B,el(2*b),el(2*b+1),h,m)
        e('trn1.2d',h,A,B); e('trn2.2d',m,A,B); U,V=h,m
        e('ldr',z1,'x2',16*a); e('ldr',z1p,'x2',16*ap)
        bf2(U,V,z1,z1p,A,B)
        e('trn1.4s',A,U,V); e('trn2.4s',B,U,V)
        e('ldr',z1,'x2',16*cc); e('ldr',z1p,'x2',16*cp)
        bf2(A,B,z1,z1p,U,V)
        e('sqrdmulh',U,A,Ce);e('sqrdmulh',V,B,Ce); e('sshr',U,U,11); e('sshr',V,V,11); e('mls',A,U,Qe); e('mls',B,V,Qe)
        e('zip1.4s',U,A,B); e('zip2.4s',V,A,B)
        e('str',U,'x0',32*b); e('str',V,'x0',32*b+16)
        blocks.append(c)
    if st: g.c+=stag(blocks,st)
    else:
        for b in range(0,16,p2): g.c+=zipr(blocks[b:b+p2])
    return g
def inv2(p1=2,p2=2,st=None):
    g=G(); t=g.t
    el=lambda i:(i//8,i%8); F=3303
    l=[]
    for b in range(16):
        z=cen(Z[31-b]); l+=[z,tw(z)]
    k5=pack(t,l)
    for i in range(4): g.e('ldr',f'v{i}','x2',16*k5[i])
    kq=t.vec([Q,20159]*4); g.e('ldr','v7','x2',16*kq); Qe=(7,0)
    regs=[f'v{i}' for i in range(16,32)]+['v4','v5','v6']
    blocks=[]
    for b in range(16):
        c=[]; e=lambda *a:c.append(a)
        f=regs[:6]; regs=regs[6:]+regs[:6]
        A,B,W,X,z1,z1p=f
        e('ldr',A,'x0',32*b); e('ldr',B,'x0',32*b+16)
        e('uzp1.4s',W,A,B); e('uzp2.4s',X,A,B)
        z6=[cen(Z[63-2*b-i//4]) for i in range(8)]; z7=[cen(Z[127-4*b-i//2]) for i in range(8)]
        cc=t.vec(z7); cp=t.vec([tw(x) for x in z7]);a=t.vec(z6); ap=t.vec([tw(x) for x in z6])
        def ib(u,v,z,zp,h,d):  # S in u ; D in d ; (v free after)
            e('sub',d,v,u); e('add',u,u,v); e('sqrdmulh',h,d,zp); e('mul',d,d,z); e('mls',d,h,Qe)
        e('ldr',z1,'x2',16*cc); e('ldr',z1p,'x2',16*cp)
        # W,X -> S=W D=A, temp B
        ib(W,X,z1,z1p,B,A)
        e('trn1.4s',B,W,A); e('trn2.4s',X,W,A)
        e('ldr',z1,'x2',16*a); e('ldr',z1p,'x2',16*ap)
        ib(B,X,z1,z1p,W,A)
        e('trn1.2d',W,B,A); e('trn2.2d',X,B,A)
        ib(W,X,el(2*b),el(2*b+1),B,A)
        e('str',W,'x0',32*b); e('str',A,'x0',32*b+16)
        blocks.append(c)
    if st: g.c+=stag(blocks,st)
    else:
        for b in range(0,16,p2): g.c+=zipr(blocks[b:b+p2])
    l=[Q,20159]; f=cen(F); l+=[f,tw(f)]; ix={}
    def put(k,m=1):
        z=cen(Z[k]*m); ix[k]=len(l); l.extend([z,tw(z)])
    for k in range(8,16): put(k,F)
    for k in range(1,8): put(k)
    ks=pack(t,l); k8=t.vec([8*Q]*2+[0]*6); kqv=t.vec([Q]*8)
    for i in range(5): g.e('ldr',f'v{i}','x2',16*ks[i])
    Q0=(0,0); C0=(0,1); F0=(0,2); F1=(0,3)
    for j in range(2):
        r=[f'v{16+i}' for i in range(16)]
        for i in range(16): g.e('ldr',r[i],'x0',32*i+16*j)
        for ly in (3,2,1,0):
            d=8>>ly
            idx=[i for i in range(16) if not i&d]
            if ly==3 and j==0: g.e('ldr','v7','x2',16*k8)
            if ly==0: g.e('ldr','v7','x2',16*kqv)
            for n,i in enumerate(idx):
                k=(2<<ly)-1-(i>>(4-ly))
                u,v=r[i],r[i+d]; z,zp=el(ix[k]),el(ix[k]+1); h,m='v5','v6'
                L=[('sub',h,v,u),('add',u,u,v)]
                if ly==3 and j==0: L.append(('sub',u,u,'v7'))
                L+=[('sqrdmulh',m,h,zp),('mul',v,h,z),('mls',v,m,Q0)]
                if ly==3: L+=[('sqrdmulh',m,u,F1),('mul',u,u,F0),('mls',u,m,Q0)]
                if ly==0: L+=[('sqrdmulh',m,u,C0),('sshr',m,m,11),('mls',u,m,Q0),('sshr',m,v,15),('and',m,m,'v7'),('add',v,v,m)]
                g.c+=L
        for i in range(16): g.e('str',r[i],'x0',32*i+16*j)
    return g
def out(fn,a,b):
    open(fn,'w').write('.text\n'+emit(a,'my_fwd')+emit(b,'my_inv')+'.section .note.GNU-stack,"",%progbits\n')
if __name__=='__main__':
    import sys
    for nm,a,b in [('z11',fwd2(1,1),inv2(1,1)),('z22',fwd2(2,2),inv2(2,2)),('z23',fwd2(2,3),inv2(2,3)),('s12',fwd2(2,st=12),inv2(2,st=12)),('s18',fwd2(2,st=18),inv2(2,st=18)),('s24',fwd2(2,st=24),inv2(2,st=24)),]:
        out(f'p_{nm}.s',a,b)
