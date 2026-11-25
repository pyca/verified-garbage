"""Scores orders of one ladder step (RFC 7748 section 5) on a coarse core model.

An operation is a block of uops fetched in program order at WIDTH/cycle; it
starts when its inputs are done, takes LAT, holds the one 64x64 multiplier for
its products; the reorder buffer holds ROB uops and retires in order. The
figure is cycles per step in steady state. Latencies are guesses from each
operation's dependent chain, not measurements; only comparisons matter."""
import random, sys
# name: (inputs, kind). '~' reads the previous step's value.
NODES = {
 'S2':(['~x2','~z2'],'add'),'D2':(['~x2','~z2'],'add'),
 'S3':(['~x3','~z3'],'add'),'D3':(['~x3','~z3'],'add'),
 'A':(['S2','S3'],'mux'),'B':(['D2','D3'],'mux'),
 'DA':(['D3','S2'],'mul'),'CB':(['D2','S3'],'mul'),
 'AA':(['A'],'sqr'),'BB':(['B'],'sqr'),'E':(['AA','BB'],'add'),
 'G':(['AA','E'],'a24'),'x2':(['AA','BB'],'mul'),'z2':(['E','G'],'mul'),
 'P':(['DA','CB'],'add'),'M':(['DA','CB'],'add'),
 'x3':(['P'],'sqr'),'Q':(['M'],'sqr'),'z3':(['Q'],'mul')}
def kinds(adx):  # uops, latency, products
    return {'mul':(125 if not adx else 95,50 if not adx else 42,20),
            'sqr':(105 if not adx else 80,48 if not adx else 40,14),
            'a24':(40,22,5),'add':(26,13,0),'mux':(14,8,0)}
def cost(order, K, width, rob, n=14):
    t=0.0; mulfree=0.0; done={}; window=[]; inq=0; ret=0.0; marks=[]
    for it in range(n):
        new={}
        for op in order:
            ins,k=NODES[op]; u,l,m=K[k]
            while window and inq+u>rob:
                r,uu=window.pop(0); inq-=uu; t=max(t,r)
            start=t; t+=u/width
            rdy=max([start]+[(done.get(i[1:],0.0) if i[0]=='~' else new[i]) for i in ins])
            if m:
                s=max(rdy,mulfree-l/2) if False else rdy
                mulfree=max(mulfree,s)+m; end=max(s+l,mulfree,t)
            else: end=max(rdy+l,t)
            new[op]=end; ret=max(ret,end); window.append((ret,u)); inq+=u
        done=new; marks.append(ret)
    return (marks[-1]-marks[n//2])/(n-1-n//2)
def valid(o):
    seen=set()
    for x in o:
        if any(i[0]!='~' and i not in seen for i in NODES[x][0]): return False
        seen.add(x)
    return True
CORES=[(6,512),(5,320),(4,224)]
def score(o):
    return sum(cost(o,kinds(a),w,r) for a in (False,True) for w,r in CORES)/6
def climb(o,iters,rng):
    b=score(o); cur,cb=o,b; best=o
    for i in range(iters):
        c=list(cur); x=c.pop(rng.randrange(len(c))); c.insert(rng.randrange(len(c)+1),x)
        if not valid(c): continue
        s=score(c)
        if s<=cb+rng.random()*0.4: cur,cb=c,s
        if s<b: b,best=s,c
    return b,best
rng=random.Random(1)
rfc=['S2','D2','S3','D3','A','AA','B','BB','E','DA','CB','P','x3','M','Q','z3','x2','G','z2']
assert valid(rfc)
print('RFC order',round(score(rfc),1),[round(cost(rfc,kinds(a),w,r)) for a in (0,1) for w,r in CORES])
res=sorted(climb(rfc,2500,random.Random(i)) for i in range(8))
for s,o in res[:5]:
    print(round(s,1),' '.join(o),[round(cost(o,kinds(a),w,r)) for a in (0,1) for w,r in CORES])
