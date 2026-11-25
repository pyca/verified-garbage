from gen2 import *
def rw(op):
    k=op[0]
    if k in('eor','bic'): return [op[2],op[3]],[op[1]]
    if k=='spill': return [op[1]],[f's{op[2]}']
    if k=='fill': return [f's{op[2]}'],[op[1]]
    if k=='iota': return [op[1]],[op[1],op[3],op[4]]
LAT={'eor':1,'bic':1,'spill':3,'fill':3,'iota':2}
def schedule(code,width=4,seed=None,twice=False):
    n=len(code); pred=[[] for _ in range(n)]; succ=[[] for _ in range(n)]
    for j in range(n):
        rj,wj=rw(code[j])
        for i in range(j):
            ri,wi=rw(code[i])
            raw=any(w in rj for w in wi); oth=any(w in wj for w in wi) or any(r in wj for r in ri)
            if raw or oth:
                l=LAT[code[i][0]] if raw else 0
                succ[i].append((j,l));pred[j].append((i,l))
    h=[0]*n
    for i in reversed(range(n)): h[i]=max([h[j]+l for j,l in succ[i]]+[0])
    rnd=random.Random(seed); pri=[h[i]+(rnd.random() if seed is not None else 0) for i in range(n)]
    done={};order=[];t=0;left=set(range(n))
    while left:
        used=0
        while used<width:
            rd=[i for i in left if all(p in done and done[p]+l<=t for p,l in pred[i])]
            if not rd: break
            i=min(rd,key=lambda i:(-pri[i],i)); done[i]=t;order.append(i);left.discard(i);used+=1
        t+=1
    return t,order
if __name__=='__main__':
    L,F,b=scalar_body(2); c=b[0]+b[1]
    for w in (4,5):
        print(w,len(c),min(schedule(c,w,s)[0] for s in range(20)))
