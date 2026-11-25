# As order.py, with the two selections adjacent (one flag for both): U V is one
# block; and the slots live at each point of an order.
from order import *
import random
ks=[(k,W,R) for k in KIND for W,R in ((4,224),(6,256),(6,512))]
def adj(o): return o.index('V')==o.index('U')+1
def climb2(rng):
    o=['A','B','C','D','U','V','AA','P','BB','Q','s','E','x2','d','w','dd','z2','x3','z3']; b=score(o)
    for _ in range(6000):
        n=o[:]; 
        blk=rng.choice([x for x in n if x!='V']); 
        mv=['U','V'] if blk=='U' else [blk]
        for x in mv: n.remove(x)
        i=rng.randrange(len(n)+1); n[i:i]=mv
        if adj(n) and ok(n):
            s=score(n)
            if s<=b: b,o=s,n
    return b,o
def live(o):
    use={}
    for i,x in enumerate(o):
        for d in OPS[x][1]: use[d]=i
    res=set(('x2','z2','x3','z3')); m=0
    old=set('o'+x for x in res); lastold={'ox2':max(o.index('A'),o.index('B')),'ox3':max(o.index('C'),o.index('D'))}
    lastold['oz2']=lastold['ox2']; lastold['oz3']=lastold['ox3']
    for i,x in enumerate(o):
        l=sum(1 for y in o[:i+1] if y in res or use.get(y,-1)>=i)+sum(1 for y in old if lastold[y]>=i)
        m=max(m,l)
    return m
if __name__=='__main__':
    res=sorted(climb2(random.Random(s)) for s in range(8))
    for b,o in res[:4]:
        print(round(b,3),live(o),' '.join(o)); print('   ',[(k,W,R,round(sim(o,KIND[k],W,R))) for k,W,R in ks])
    for o in (['A','B','C','D','U','V','AA','P','BB','Q','s','E','x2','d','w','dd','z2','x3','z3'],):
        print(round(score(o),3),live(o),' '.join(o)); print('   ',[(k,W,R,round(sim(o,KIND[k],W,R))) for k,W,R in ks])
