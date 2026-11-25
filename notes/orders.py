from gen2 import *
# emulate Lean's list: ops (kind, reads, writes); kinds sha/basic/load
def lean_body(es,bs,x3):
    V={(x,y):f"v{x+5*y}" for x in range(5) for y in range(5)}
    out=[]
    for r in range(2):
        c=vec_round(r,V,[f"v{i}" for i in range(25,32)],(0,0),r)  # unused; rebuild as in Lean
        reg=lambda l:V[loc(r,l)]
        L=[]
        for x in range(5):
            a=[reg((x,y)) for y in range(5)]; C=f"v{25+x}"
            if x<es: L+=[('b',[a[0],a[1]],C),('b',[C,a[2]],C),('b',[C,a[3]],C),('b',[C,a[4]],C)]
            else: L+=[('s',[a[0],a[1],a[2]],C),('s',[C,a[3],a[4]],C)]
        D=lambda x:"v%d"%[30,25,26,27,28][x]
        for x in (0,2,4,1,3): L.append(('s',[f"v{25+(x+4)%5}",f"v{25+(x+1)%5}"],D(x)))
        L.append(('b',[reg((0,0)),D(0)],reg((0,0))))
        for x in (0,2,4):
            for y in range(5):
                if (x,y)!=(0,0): L.append(('s',[reg((x,y)),D(x)],reg((x,y))))
        for y in range(5):
            s=[src((k+2*y)%5,y) for k in range(5)]
            b=lambda k:'v29' if k%5==1 else 'v31' if k%5==3 else reg(s[k%5])
            a=[reg(z) for z in s]
            L.append(('s',[a[1],D(1)],'v29'));L.append(('s',[a[3],D(3)],'v31'))
            for j,(k,d,t) in enumerate([(3,a[1],a[1]),(4,a[3],a[3]),(2,a[4],'v30'),(0,a[0],'v30'),(1,a[2],'v30')]):
                if 5*y+j<bs: L+=[('b',[b(k+2),b(k+1)],t),('b',[t,b(k)],d)]
                else: L.append(('s',[b(k),b(k+2),b(k+1)],d))
        L.append(('l',[],'v31'))
        if x3: L.append(('b',['v31'],'v31'))
        L.append(('b',['v0','v31'],'v0'))
        out+=L
    return out
def sched(code,seed):
    n=len(code); pred=[[] for _ in range(n)]; succ=[[] for _ in range(n)]
    for j in range(n):
        for i in range(j):
            raw=code[i][2] in code[j][1]; o=code[i][2]==code[j][2] or code[j][2] in code[i][1]
            if raw or o:
                l=(4 if code[i][0]=='l' else 2) if raw else 0
                pred[j].append((i,l));succ[i].append((j,l))
    h=[0]*n
    for i in reversed(range(n)): h[i]=max([h[j]+l for j,l in succ[i]]+[0])+1
    rnd=random.Random(seed);pri=[h[i]+rnd.random()*3 for i in range(n)]
    done={};order=[];left=set(range(n));t=0
    while left:
        u0=u1=ul=False
        while True:
            rd=[i for i in left if all(p in done and done[p]+l<=t for p,l in pred[i])]
            rd.sort(key=lambda i:(-pri[i],i)); pick=None
            for i in rd:
                k=code[i][0]
                if k=='l' and not ul: pick=i;ul=True;break
                if k=='s' and not u0: pick=i;u0=True;break
                if k=='b' and not u1: pick=i;u1=True;break
                if k=='b' and not u0 and not any(code[j][0]=='s' for j in rd): pick=i;u0=True;break
            if pick is None: break
            done[pick]=t;order.append(pick);left.discard(pick)
        t+=1
    return t,order
def picks(order):
    rem=sorted(order);r=[]
    for i in order: k=rem.index(i); r.append(k); rem.pop(k)
    return r
if __name__=='__main__':
    for x3 in (False,True):
        c=lean_body(2,8,x3)
        t,o=min((sched(c,s) for s in range(400)),key=lambda z:z[0])
        print(x3,len(c),t); print(picks(o))
