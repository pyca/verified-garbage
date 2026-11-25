# Macro model of one ladder iteration on an out-of-order core.  Each field
# operation is (uops, latency from its operands, multiplier-port cycles); uops
# are dispatched in order at W per cycle, retired in order, R in flight.
import itertools, random, sys
KIND = {'base': {'mul':(138,38,26),'sqr':(118,42,20),'a24':(50,16,5),'add':(23,13,0),'sel':(14,8,0)},
        'adx':  {'mul':(105,30,23),'sqr':(90,32,17),'a24':(42,14,5),'add':(23,13,0),'sel':(14,8,0)}}
# name: (kind, deps within the iteration, deps on the previous iteration's results)
OPS = {'A':('add',[],['x2','z2']),'B':('add',[],['x2','z2']),'C':('add',[],['x3','z3']),'D':('add',[],['x3','z3']),
 'U':('sel',['A','C'],[]),'V':('sel',['B','D'],[]),
 'P':('mul',['D','A'],[]),'Q':('mul',['C','B'],[]),'AA':('sqr',['U'],[]),'BB':('sqr',['V'],[]),
 's':('add',['P','Q'],[]),'d':('add',['P','Q'],[]),'E':('add',['AA','BB'],[]),
 'x3':('sqr',['s'],[]),'dd':('sqr',['d'],[]),'z3':('mul',['dd'],[]),
 'x2':('mul',['AA','BB'],[]),'w':('a24',['AA','E'],[]),'z2':('mul',['E','w'],[])}
def sim(order, kinds, W, R, n=12):
    t_disp=0.0; port=0.0; ready={k:0.0 for k in OPS}; inflight=[]  # (uops, retire time)
    last_ret=0.0; out=[]; used=0
    for it in range(n):
        prev=dict(ready)
        for o in order:
            k,d,p=OPS[o]; u,l,m=kinds[k]
            # room for half the operation in the window before it starts
            while inflight and used+u>R:
                uu,r=inflight.pop(0); used-=uu; t_disp=max(t_disp,r)
            start=max([t_disp]+[ready[x] for x in d]+[prev[x] for x in p])
            ex=max(start,port if m else 0); 
            if m: port=max(port,start)+m
            t_disp+=u/W
            fin=max(ex+l,t_disp)
            ready[o]=fin; last_ret=max(last_ret,fin); inflight.append((u,last_ret)); used+=u
        out.append(last_ret)
    return (out[-1]-out[3])/(n-4)
def ok(order):
    seen=set()
    for o in order:
        if any(d not in seen for d in OPS[o][1]): return False
        seen.add(o)
    return True
def score(o):
    return sum(sim(o,KIND[k],W,R)/ (sum(KIND[k][OPS[x][0]][0] for x in OPS)/W) for k in KIND for W,R in ((4,224),(6,256),(6,512)))
rfc=['A','B','C','D','U','V','AA','BB','E','P','Q','s','d','x3','dd','z3','x2','w','z2']
def climb(o,rng,steps=6000):
    b=score(o)
    for _ in range(steps):
        n=o[:]; i=rng.randrange(len(n)); x=n.pop(i); n.insert(rng.randrange(len(n)+1),x)
        if ok(n):
            s=score(n)
            if s<=b: o,b=n,s
    return b,o
if __name__=='__main__':
    print('rfc',round(score(rfc),3)); res=[]
    for seed in range(8): res.append(climb(rfc[:],random.Random(seed)))
    for b,o in sorted(res)[:5]:
        print(round(b,3),' '.join(o)); 
        print('   ',[ (k,W,R,round(sim(o,KIND[k],W,R))) for k in KIND for W,R in ((4,224),(6,256),(6,512))])
    print('rfc',[ (k,W,R,round(sim(rfc,KIND[k],W,R))) for k in KIND for W,R in ((4,224),(6,256),(6,512))])
