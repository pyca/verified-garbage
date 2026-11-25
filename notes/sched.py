from gen2 import *
def rw(op):
    k=op[0]
    if k=='iota': return [op[1]],[op[1],op[3]]
    return [z for z in op[2:] if isinstance(z,str)],[op[1]]
SHA={'e3','rax','xar','bcax'}
def schedule(code,lat=2,seed=None,wrap=True):
    n=len(code); succ=[[] for _ in range(n)]; pred=[[] for _ in range(n)]
    for j in range(n):
        rj,wj=rw(code[j])
        for i in range(j):
            ri,wi=rw(code[i])
            raw=any(w in rj for w in wi); ww=any(w in wj for w in wi); war=any(r in wj for r in ri)
            if raw or ww or war:
                succ[i].append((j,lat if raw else 0)); pred[j].append((i,lat if raw else 0))
    h=[0]*n
    for i in reversed(range(n)): h[i]=max([h[j]+max(l,1 if l else 0) for j,l in succ[i]]+[0])+1
    rnd=random.Random(seed)
    pri=[h[i]+(rnd.random()*3 if seed is not None else 0) for i in range(n)]
    done={};order=[];t=0;left=set(range(n))
    while left:
        used0=used1=False
        while True:
            rd=[i for i in left if all(p in done and done[p]+l<=t for p,l in pred[i])]
            rd.sort(key=lambda i:(-pri[i],i))
            pick=None
            for i in rd:
                s=code[i][0] in SHA
                if s and not used0: pick=i;used0=True;break
                if not s and not used1: pick=i;used1=True;break
                if not s and not used0 and not any(code[j][0] in SHA for j in rd): pick=i;used0=True;break
            if pick is None: break
            done[pick]=t;order.append(pick);left.discard(pick)
            if used0 and used1: break
        t+=1
    return t,order
if __name__=='__main__':
    for mix in ((0,0),(5,0),(5,5),(5,8),(5,10),(5,12),(3,10),(0,15),(0,17)):
        V,b=vec_body(mix)
        # iota code occupies: ldr+eor basic
        c=b[0]+b[1]
        best=min((schedule(c,seed=s) for s in range(30)),key=lambda z:z[0])
        print(mix,len(c),best[0])
