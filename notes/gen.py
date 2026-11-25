from frames import R, src, tree, pick
import random
M64=(1<<64)-1
ror=lambda v,k:((v>>(k%64))|(v<<(64-k%64)))&M64 if k%64 else v
# ---- spec
def RC():
    def rc(t):
        r=1
        for _ in range(t%255):
            r<<=1
            if r&256: r^=0x171
        return r&1
    out=[]
    for i in range(24):
        v=0
        for j in range(7):
            if rc(j+7*i): v|=1<<(2**j-1)
        out.append(v)
    return out
RCS=RC()
def keccak(A):
    for r in range(24):
        C=[A[x]^A[x+5]^A[x+10]^A[x+15]^A[x+20] for x in range(5)]
        D=[C[(x-1)%5]^ror(C[(x+1)%5],63) for x in range(5)]
        A=[A[i]^D[i%5] for i in range(25)]
        B=[0]*25
        for y in range(5):
            for x in range(5):
                s=src(x,y); B[x+5*y]=ror(A[s[0]+5*s[1]],64-R[s])
        A=[B[i]^(~B[i//5*5+(i+1)%5]&M64&B[i//5*5+(i+2)%5]) for i in range(25)]
        A[0]^=RCS[r]
    return A
# ---- code ops are tuples; regs are strings
M=lambda x,y:((2*x+y)%5,(2*x+3*y)%5)
# location map: lane -> home index for parity
def loc(par,l): return l if par==0 else M(*l)
class Gen:
    def __init__(s): s.c=[]
    def eor(s,d,n,m,sh=0): s.c.append(('eor',d,n,m,sh%64))
    def bic(s,d,n,m,sh=0): s.c.append(('bic',d,n,m,sh%64))
def scalar_round(par, L, F, spill=True):
    """L: lane-home->reg, F: 5 free regs; returns code. value(l)=rol(reg,p[l])"""
    g=Gen(); p=tree
    reg=lambda l:L[loc(par,l)]
    # theta: C_x in F[x], frame f_x
    f={}
    Cr=F[:5]
    for x in range(5):
        ls=[(x,y) for y in range(5)]
        a=ls[0]; b=ls[1]
        # eor d, a, b ror k : want frame of a. reg_b holds ror(v,p_b); need ror(v,p_a): ror(reg_b, p_a-p_b)
        f[x]=p[a]
        g.eor(Cr[x],reg(a),reg(b),p[a]-p[b])
        for l in ls[2:]: g.eor(Cr[x],Cr[x],reg(l),f[x]-p[l])
    # spill one lane to get temp
    sl=SP; t=reg(sl)
    g.c.append(('spill',t))
    # D0->t, D2->C1, D4->C3, D1->C0, D3->C2 ; frame of D_x = frame of C_{x-1}
    Dr={}; fd={}
    for x,dst in ((0,t),(2,Cr[1]),(4,Cr[3]),(1,Cr[0]),(3,Cr[2])):
        a=(x+4)%5; b=(x+1)%5
        # D = C_a ^ rol(C_b,1). in frame f_a: ror(C_a,f_a) ^ ror(rol(C_b,1), f_a); reg_b = ror(C_b,f_b)
        g.eor(dst,Cr[a],Cr[b],f[a]-f[b]-1)
        Dr[x]=dst; fd[x]=f[a]
    free=[Cr[4]]
    # column 0 first; spilled lane must be in column 0 since t holds D0? reload into t after column 0 applied
    def ap(d,l): 
        x=l[0]; g.eor(d,reg(l),Dr[x],p[l]-fd[x])
    for x in (0,2,3,4):
        for y in range(5):
            l=(x,y)
            if l==sl: continue
            ap(reg(l),l)
        if x==0 and sl[0]!=0:
            g.c.append(('fill',t))
        if x!=0: free.append(Dr[x])
    if sl[0]==0: raise 0
    # sl in col 1 handled in rows (reg(sl)=t reloaded)
    if sl[0] in (2,3,4): pass
    for y in range(5):
        u=lambda k:(k+2*y)%5
        s=[src(u(k),y) for k in range(5)]
        fr=[ (p[s[k]]+R[s[k]]) for k in range(5)]   # frame of B_k
        r=[reg(s[k]) for k in range(5)]
        T,t1,t2=free[0],free[1],free[2]
        B=r[:]; B[1]=T
        ap(T,s[1])   # A' of col-1 lane into T, frame p
        out=lambda k:(u(k),y)
        def bic(d,k): # t_k = B_{k+2} & ~B_{k+1}, frame fr[k+2]
            a=(k+2)%5;b=(k+1)%5
            g.bic(d,B[a],B[b],fr[a]-fr[b])
        def fin(d,k,t):
            a=(k+2)%5
            if pick[out(k)]==0: g.eor(d,B[k],t,fr[k]-fr[a]); ff=fr[k]
            else: g.eor(d,t,B[k],fr[a]-fr[k]); ff=fr[a]
            assert (ff-p[out(k)])%64==0
        bic(t1,1); bic(t2,2)
        bic(r[1],3); fin(r[1],3,r[1])
        bic(r[3],4); fin(r[3],4,r[3])
        fin(r[4],2,t2)
        bic(t2,0)
        fin(r[2],1,t1)
        fin(r[0],0,t2)
    g.c.append(('iota',reg_after(par,(0,0),L),free[0]))
    return g.c
def reg_after(par,l,L): return L[loc(1-par,l)]
SP=(1,2)
def sim(code,regs,rnd,sp):
    for op in code:
        k=op[0]
        if k=='eor': regs[op[1]]=regs[op[2]]^ror(regs[op[3]],op[4])
        elif k=='bic': regs[op[1]]=regs[op[2]]&~ror(regs[op[3]],op[4])&M64
        elif k=='spill': sp[0]=regs[op[1]]
        elif k=='fill': regs[op[1]]=sp[0]
        elif k=='iota': regs[op[1]]^=RCS[rnd]
L={(x,y):f'L{x}{y}' for x in range(5) for y in range(5)}
F=[f'F{i}' for i in range(5)]
if __name__=='__main__':
    A=[random.getrandbits(64) for _ in range(25)]
    regs={L[(i%5,i//5)]:ror(A[i],tree[(i%5,i//5)]) for i in range(25)}
    sp=[0]
    for r in range(24):
        sim(scalar_round(r%2,L,F),regs,r,sp)
    out=[ror(regs[L[(i%5,i//5)]],64-tree[(i%5,i//5)]) for i in range(25)]
    print(out==keccak(A), len(scalar_round(0,L,F)))
