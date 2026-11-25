from gen2 import *
def xround(par,L,F,nspill,k):
    c=[];reg=lambda l:L[loc(par,l)]
    e=lambda d,n,m,s=0:c.append(('eor',d,n,m,s%64)); b=lambda d,n,m:c.append(('bic',d,n,m,0))
    tl=[src((1+2*y)%5,y) for y in range(5)]; sp={y:y-(5-nspill) for y in range(5-nspill,5)}
    Cr={};avail=list(F);sq=[(y,reg(tl[y])) for y in sp]
    for x in (1,0,2,3,4):
        if not avail: y,r=sq.pop(0); c.append(('spill',r,sp[y])); avail.append(r)
        d=avail.pop(0);Cr[x]=d
        e(d,reg((x,0)),reg((x,1)))
        for y in (2,3,4): e(d,d,reg((x,y)))
    if not avail: y,r=sq.pop(0); c.append(('spill',r,sp[y])); avail.append(r)
    Dr={}
    for x,d in ((0,avail.pop()),(2,Cr[1]),(4,Cr[3]),(1,Cr[0]),(3,Cr[2])):
        e(d,Cr[(x+4)%5],Cr[(x+1)%5],63);Dr[x]=d
    free=[Cr[4]]
    def ap(d,l,s):
        e(d,s,Dr[l[0]])
        if R[l]: c.append(('ror',d,d,64-R[l]))
    for x in (0,2,3,4):
        for y in range(5): ap(reg((x,y)),(x,y),reg((x,y)))
        free.append(Dr[x])
    for y in range(5):
        u=lambda q:(q+2*y)%5; s=[src(u(q),y) for q in range(5)]; r=[reg(z) for z in s]
        fl=[z for z in free if z!=r[1]]; T=fl[0]
        if y in sp: c.append(('fill',T,sp[y])); ap(T,s[1],T)
        else: ap(T,s[1],r[1])
        if y==4: fl.append(Dr[1])
        t1,t2=fl[1],fl[2]; B=r[:];B[1]=T
        nb=lambda d,q:b(d,B[(q+2)%5],B[(q+1)%5]); fin=lambda d,q,t:e(d,B[q],t)
        nb(t1,1);nb(t2,2);nb(r[1],3);fin(r[1],3,r[1]);nb(r[3],4);fin(r[3],4,r[3]);fin(r[4],2,t2);nb(t2,0);fin(r[2],1,t1);fin(r[0],0,t2)
        if r[1] in free: free.remove(r[1])
    c.append(('iota',L[loc(1-par,(0,0))],k,F[0],F[1]))
    return c
def xbody(nspill):
    regs=G[:31-nspill]; L={(x,y):regs[x+5*y] for x in range(5) for y in range(5)};F=regs[25:31-nspill]
    return L,F,[xround(r,L,F,nspill,r) for r in range(2)]
if __name__=='__main__':
    A=[random.getrandbits(64) for _ in range(25)];W=keccak(A)
    L,F,b=xbody(3);regs={L[(i%5,i//5)]:A[i] for i in range(25)};sp={}
    for r in range(24):
        for op in b[r%2]:
            if op[0]=='ror': regs[op[1]]=ror(regs[op[2]],op[3])
            else: ssim([op],regs,r,sp)
    print([regs[L[(i%5,i//5)]] for i in range(25)]==W,len(b[0]))
