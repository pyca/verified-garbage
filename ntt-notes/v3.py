from gen import *
from var import zipr,stag
el=lambda i,b=0:(b+i//8,i%8)
def bfs(g,r,free,idx,d,p,q,zf):
    # forward butterflies, p at a time; rotating temps list free (queue)
    for c in range(0,len(idx),p):
        grp=[];nf=[];tm=free[:2*p];rest=free[2*p:]
        for n,i in enumerate(idx[c:c+p]):
            z,zp=zf(i);h,m=tm[2*n],tm[2*n+1];u,v=r[i],r[i+d]
            grp.append([('sqrdmulh',h,v,zp),('mul',m,v,z),('mls',m,h,q),('sub',h,u,m),('add',u,u,m)])
            r[i+d]=h;nf+=[m,v]
        g.c+=zipr(grp);free=rest+nf+tm[2*len(idx[c:c+p]):]
    return free
def stagm(ls,d):  return stag(ls,d)
def fwd3(p=2,d=9):
    g=G();t=g.t;zs=[cen(z) for z in Z]
    l=[Q,20159]
    for k in range(1,8): l+=[zs[k],tw(zs[k])]
    ka=pack(t,l)          # 2 vectors
    l=[]
    for k in range(8,16): l+=[zs[k],tw(zs[k])]
    kb=pack(t,l)          # 2 vectors
    for n,i in enumerate(ka): g.e('ldr',f'v{n}','x2',16*i)
    q=(0,0)
    for j in range(2):
        r=[f'v{16+i}' for i in range(16)];free=[f'v{i}' for i in range(2,8)]
        for i in range(16): g.e('ldr',r[i],'x0',32*i+16*j)
        for ly in range(4):
            dd=8>>ly; idx=[i for i in range(16) if not i&dd]
            if ly<3:
                free=bfs(g,r,free,idx,dd,p,q,lambda i:(el(2*((1<<ly)+(i>>(4-ly)))),el(2*((1<<ly)+(i>>(4-ly)))+1)))
            else:
                lo=[x for x in free if int(x[1:])<16]
                for n,i in enumerate(kb): g.e('ldr',lo[n],'x2',16*i)
                fr=[x for x in free if x not in lo[:2]]
                B=[int(x[1:]) for x in lo[:2]]
                zf=lambda i:((B[(i//2*2)//8],(i//2*2)%8),(B[(i//2*2)//8],(i//2*2)%8+1))
                bfs(g,r,fr,idx,dd,min(p,2),q,zf)
        for i in range(16): g.e('str',r[i],'x0',32*i+16*j)
    l=[]
    for b in range(16): l+=[zs[16+b],tw(zs[16+b])]
    k5=pack(t,l)
    for i in range(4): g.e('ldr',f'v{i+1}','x2',16*k5[i])
    Qe=(0,0);Ce=(0,1);regs=[f'v{i}' for i in range(16,32)]+['v5','v6','v7']
    blocks=[]
    for b in range(16):
        c=[];e=lambda *a:c.append(a)
        f=regs[:4];regs=regs[4:]+regs[:4];A,B,h,m=f
        e('ldr',A,'x0',32*b);e('ldr',B,'x0',32*b+16)
        z6=[zs[32+2*b+i//4] for i in range(8)];z7=[zs[64+4*b+i//2] for i in range(8)]
        a=t.vec(z6);ap=t.vec([tw(x) for x in z6]);cc=t.vec(z7);cp=t.vec([tw(x) for x in z7])
        def bf(u,v,h,m,a=None,ap=None,es=None):
            if es: e('sqrdmulh',h,v,es[1]);e('mul',m,v,es[0])
            else:
                e('ldr',h,'x2',16*ap);e('ldr',m,'x2',16*a);e('sqrdmulh',h,v,h);e('mul',m,v,m)
            e('mls',m,h,Qe);e('sub',v,u,m);e('add',u,u,m)
        bf(A,B,h,m,es=(el(2*b,1),el(2*b+1,1)))
        e('trn1.2d',h,A,B);e('trn2.2d',m,A,B);U,V=h,m
        bf(U,V,A,B,a,ap)
        e('trn1.4s',A,U,V);e('trn2.4s',B,U,V)
        bf(A,B,U,V,cc,cp)
        e('sqrdmulh',U,A,Ce);e('sqrdmulh',V,B,Ce);e('sshr',U,U,11);e('sshr',V,V,11);e('mls',A,U,Qe);e('mls',B,V,Qe)
        e('zip1.4s',U,A,B);e('zip2.4s',V,A,B);e('str',U,'x0',32*b);e('str',V,'x0',32*b+16)
        blocks.append(c)
    g.c+=stag(blocks,d)
    return g
def inv3(p=2,d=9):
    g=G();t=g.t;F=3303
    l=[]
    for b in range(16):
        z=cen(Z[31-b]);l+=[z,tw(z)]
    k5=pack(t,l)
    l=[Q,20159]
    for k in range(1,8): l+=[cen(Z[k]),tw(cen(Z[k]))]
    ka=pack(t,l)   # q,canon, zetas 1..7 : 2 vectors v0,v1
    g.e('ldr','v0','x2',16*ka[0])
    for i in range(4): g.e('ldr',f'v{i+1}','x2',16*k5[i])
    Qe=(0,0);regs=[f'v{i}' for i in range(16,32)]+['v5','v6','v7']
    blocks=[]
    for b in range(16):
        c=[];e=lambda *a:c.append(a)
        f=regs[:4];regs=regs[4:]+regs[:4];A,B,W,X=f
        e('ldr',A,'x0',32*b);e('ldr',B,'x0',32*b+16);e('uzp1.4s',W,A,B);e('uzp2.4s',X,A,B)
        z6=[cen(Z[63-2*b-i//4]) for i in range(8)];z7=[cen(Z[127-4*b-i//2]) for i in range(8)]
        cc=t.vec(z7);cp=t.vec([tw(x) for x in z7]);a=t.vec(z6);ap=t.vec([tw(x) for x in z6])
        def ib(u,v,h,dd,a=None,ap=None,es=None):  # S in u, D in v
            e('sub',dd,v,u);e('add',u,u,v)
            if es: e('sqrdmulh',h,dd,es[1]);e('mul',v,dd,es[0])
            else: e('ldr',h,'x2',16*ap);e('ldr',v,'x2',16*a);e('sqrdmulh',h,dd,h);e('mul',v,dd,v)
            e('mls',v,h,Qe)
        ib(W,X,A,B,cc,cp)
        e('trn1.4s',A,W,X);e('trn2.4s',B,W,X)
        ib(A,B,W,X,a,ap)
        e('trn1.2d',W,A,B);e('trn2.2d',X,A,B)
        ib(W,X,A,B,es=(el(2*b,1),el(2*b+1,1)))
        e('str',W,'x0',32*b);e('str',X,'x0',32*b+16)
        blocks.append(c)
    g.c+=stag(blocks,d)
    f=cen(F)
    l=[f,tw(f)]
    l2=[]
    for k in range(8,16):
        z=cen(Z[k]*F);l2+=[z,tw(z)]
    kb=pack(t,l2); kf=t.vec([f,tw(f)]*4)
    k8=t.vec([8*Q]*2+[0]*6);kqv=t.vec([Q]*8)
    g.e('ldr','v1','x2',16*ka[1])
    for j in range(2):
        r=[f'v{16+i}' for i in range(16)]
        for i in range(16): g.e('ldr',r[i],'x0',32*i+16*j)
        # layer 3: v2,v3 zetas*f ; v4 = f / f'  ; v5.. temps ; 8q vector
        for n,i in enumerate(kb): g.e('ldr',f'v{2+n}','x2',16*i)
        g.e('ldr','v4','x2',16*kf)
        for ly in (3,2,1,0):
            dd=8>>ly;idx=[i for i in range(16) if not i&dd]
            off='v7' if (ly==3 and j==0) else None
            if off: g.e('ldr','v7','x2',16*k8)
            if ly==0: g.e('ldr','v7','x2',16*kqv)
            if ly==3: free=['v5','v6'] if off else ['v5','v6','v7']
            elif ly==0: free=[f'v{i}' for i in range(2,7)]
            else: free=[f'v{i}' for i in range(2,8)]
            for c in range(0,8,1 if len(free)<4 else p):
                pp=1 if len(free)<4 else p
                grp=[];tm=free[:]
                for n,i in enumerate(idx[c:c+pp]):
                    k=(2<<ly)-1-(i>>(4-ly));u,v=r[i],r[i+dd]
                    if ly==3: z,zp=el(2*(k-8),2),el(2*(k-8)+1,2)
                    else: z,zp=el(2*k),el(2*k+1)
                    h,m=tm[2*n],tm[2*n+1]
                    L=[('sub',h,v,u),('add',u,u,v)]
                    if off: L.append(('sub',u,u,off))
                    L+=[('sqrdmulh',m,h,zp),('mul',v,h,z),('mls',v,m,(0,0))]
                    if ly==3: L+=[('sqrdmulh',m,u,(4,1)),('mul',u,u,(4,0)),('mls',u,m,(0,0))]
                    if ly==0: L+=[('sqrdmulh',h,u,(0,1)),('sshr',h,h,11),('sshr',m,v,15),('mls',u,h,(0,0)),('and',m,m,'v7'),('add',v,v,m)]
                    grp.append(L)
                g.c+=zipr(grp)
        for i in range(16): g.e('str',r[i],'x0',32*i+16*j)
    return g
if __name__=='__main__':
    for nm,p,d in [('a1',1,12),('a2',2,12),('a3',3,12),('b2',2,9),('b3',3,9),('c2',2,15)]:
        for p_ in [p]:
            a=fwd3(p,d); b=inv3(min(p,2),d)
            open(f'p_{nm}.s','w').write('.text\n'+emit(a,'my_fwd')+emit(b,'my_inv')+'.section .note.GNU-stack,"",%progbits\n')
