from gen import *
p=tree
def scalar_round(par,L,F,nspill,k):
    """k: round index within loop body. ops: eor,bic,spill(reg,slot),fill(reg,slot),iota(reg,tmp)"""
    c=[]
    reg=lambda l:L[loc(par,l)]
    eor=lambda d,n,m,s=0:c.append(('eor',d,n,m,s%64))
    bic=lambda d,n,m,s=0:c.append(('bic',d,n,m,s%64))
    tl=[src((1+2*y)%5,y) for y in range(5)]        # column-1 lane of each row
    sp={y:y-(5-nspill) for y in range(5-nspill,5)} # row->slot
    f={};Cr={}
    cregs=list(F); 
    order=[1,0,2,3,4]  # columns; column 1 first so that its lanes can be spilled
    sr=[(y,reg(tl[y])) for y in sp]; 
    avail=list(F); sq=list(sr)
    for x in order:
        if not avail:
            y,r=sq.pop(0); c.append(('spill',r,sp[y])); avail.append(r)
        d=avail.pop(0); Cr[x]=d
        ls=[(x,y) for y in range(5)]; f[x]=p[ls[0]]
        eor(d,reg(ls[0]),reg(ls[1]),f[x]-p[ls[1]])
        for l in ls[2:]: eor(d,d,reg(l),f[x]-p[l])
    if not avail:
        y,r=sq.pop(0); c.append(('spill',r,sp[y])); avail.append(r)
    assert not sq
    Dr={};fd={}
    # keep D1 in an F register: D1 := C0's reg; F[1] when order starts 1,0
    for x,dst in ((0,avail.pop()),(2,Cr[1]),(4,Cr[3]),(1,Cr[0]),(3,Cr[2])):
        a=(x+4)%5;b=(x+1)%5
        eor(dst,Cr[a],Cr[b],f[a]-f[b]-1); Dr[x]=dst; fd[x]=f[a]
    free=[Cr[4]]
    ap=lambda d,l,s: eor(d,s,Dr[l[0]],p[l]-fd[l[0]])
    for x in (0,2,3,4):
        for y in range(5): ap(reg((x,y)),(x,y),reg((x,y)))
        free.append(Dr[x])
    for y in range(5):
        u=lambda q:(q+2*y)%5
        s=[src(u(q),y) for q in range(5)]
        fr=[(p[s[q]]+R[s[q]]) for q in range(5)]
        r=[reg(s[q]) for q in range(5)]
        fl=[z for z in free if z!=r[1]]
        T=fl[0]
        if y in sp: c.append(('fill',T,sp[y])); ap(T,s[1],T)
        else: ap(T,s[1],r[1])
        if y==4: fl.append(Dr[1])
        t1,t2=fl[1],fl[2]
        B=r[:];B[1]=T
        out=lambda q:(u(q),y)
        def nb(d,q): a=(q+2)%5;b=(q+1)%5; bic(d,B[a],B[b],fr[a]-fr[b])
        def fin(d,q,t):
            a=(q+2)%5
            if pick[out(q)]==0: eor(d,B[q],t,fr[q]-fr[a])
            else: eor(d,t,B[q],fr[a]-fr[q])
        nb(t1,1);nb(t2,2)
        nb(r[1],3);fin(r[1],3,r[1])
        nb(r[3],4);fin(r[3],4,r[3])
        fin(r[4],2,t2)
        nb(t2,0)
        fin(r[2],1,t1)
        fin(r[0],0,t2)
        if r[1] in free: free.remove(r[1])
    free=[z for z in F]
    c.append(('iota',L[loc(1-par,(0,0))],k,free[0],free[1]))
    return c
def ssim(code,regs,rnd,sp):
    for op in code:
        k=op[0]
        if k=='eor': regs[op[1]]=regs[op[2]]^ror(regs[op[3]],op[4])
        elif k=='bic': regs[op[1]]=regs[op[2]]&~ror(regs[op[3]],op[4])&M64
        elif k=='spill': sp[op[2]]=regs[op[1]]
        elif k=='fill': regs[op[1]]=sp[op[2]]
        elif k=='iota': regs[op[1]]^=RCS[rnd]; regs[op[3]]=None; regs[op[4]]=None
G=[f'x{i}' for i in list(range(18))+list(range(19,29))+[30]]
def scalar_body(nspill):
    K=31-nspill
    regs=G[:K]
    L={(x,y):regs[x+5*y] for x in range(5) for y in range(5)}
    F=regs[25:K]
    return L,F,[scalar_round(r,L,F,nspill,r) for r in range(2)]
# vector: value held plainly
def vec_round(par,V,F,mix,k,rowmix=(0,1,2,3,4)):
    """mix: (nEor3pairs, nBcaxSplitRows list)"""
    c=[];reg=lambda l:V[loc(par,l)]
    esplit,bsplit=mix
    C=F[:5];
    for x in range(5):
        a=[reg((x,y)) for y in range(5)]
        if x<esplit:
            c.append(('e3',C[x],a[0],a[1],a[2]) if 0 else ('eor',C[x],a[0],a[1]))
            c.append(('eor',C[x],C[x],a[2]));c.append(('eor',C[x],C[x],a[3]));c.append(('eor',C[x],C[x],a[4]))
        else:
            c.append(('e3',C[x],a[0],a[1],a[2])); c.append(('e3',C[x],C[x],a[3],a[4]))
    D={}
    for x,d in ((0,F[5]),(2,C[1]),(4,C[3]),(1,C[0]),(3,C[2])):
        c.append(('rax',d,C[(x+4)%5],C[(x+1)%5])); D[x]=d
    free=[C[4],F[6],D[0],D[2],D[4]]
    c.append(('eor',reg((0,0)),reg((0,0)),D[0]))
    for x in (0,2,4):
        for y in range(5):
            if (x,y)!=(0,0): c.append(('xar',reg((x,y)),reg((x,y)),D[x],R[(x,y)]))
    n=0
    for y in range(5):
        u=lambda q:(q+2*y)%5
        s=[src(u(q),y) for q in range(5)]; r=[reg(l) for l in s]
        # B1 <- col1, B3<-col3
        assert s[1][0]==1 and s[3][0]==3
        T1,T3,t=free[0],free[1],free[2]
        c.append(('xar',T1,r[1],D[1],R[s[1]])); c.append(('xar',T3,r[3],D[3],R[s[3]]))
        B=[r[0],T1,r[2],T3,r[4]]
        def out(d,q,tmp):
            nonlocal n
            a,b,e=B[q],B[(q+2)%5],B[(q+1)%5]
            if n<bsplit:
                c.append(('bic',tmp,b,e)); c.append(('eor',d,tmp,a))
            else: c.append(('bcax',d,a,b,e))
            n+=1
        out(r[1],3,r[1]); out(r[3],4,r[3]); out(r[4],2,t); out(r[0],0,t); out(r[2],1,t)
    c.append(('iota',V[loc(1-par,(0,0))],k,free[0]))
    return c
def vsim(code,regs,rnd):
    for op in code:
        k=op[0];a=[regs.get(z) for z in op[2:] if isinstance(z,str)]
        if k=='eor': regs[op[1]]=a[0]^a[1]
        elif k=='e3': regs[op[1]]=a[0]^a[1]^a[2]
        elif k=='rax': regs[op[1]]=a[0]^ror(a[1],63)
        elif k=='xar': regs[op[1]]=ror(a[0]^a[1],64-op[4])
        elif k=='bic': regs[op[1]]=a[0]&~a[1]&M64
        elif k=='bcax': regs[op[1]]=a[0]^(a[1]&~a[2]&M64)
        elif k=='iota': regs[op[1]]^=RCS[rnd]
VR=[f'v{i}' for i in range(32)]
def vec_body(mix):
    V={(x,y):VR[x+5*y] for x in range(5) for y in range(5)}
    return V,[vec_round(r,V,VR[25:],mix,r) for r in range(2)]
if __name__=='__main__':
    A=[random.getrandbits(64) for _ in range(25)]; want=keccak(A)
    for ns in (1,2,3):
        if ns==1:
            G_=G+['x29','x18']; 
        L,F,b=scalar_body(max(ns,2)) if ns>1 else scalar_body(2)
        regs={L[(i%5,i//5)]:ror(A[i],p[(i%5,i//5)]) for i in range(25)}; sp={}
        for r in range(24): ssim(b[r%2],regs,r,sp)
        print(ns,[ror(regs[L[(i%5,i//5)]],64-p[(i%5,i//5)]) for i in range(25)]==want,len(b[0]),len(b[1]))
    for mix in ((0,0),(5,0),(5,10),(3,7)):
        V,b=vec_body(mix); regs={V[(i%5,i//5)]:A[i] for i in range(25)}
        for r in range(24): vsim(b[r%2],regs,r)
        print(mix,[regs[V[(i%5,i//5)]] for i in range(25)]==want,len(b[0]))
