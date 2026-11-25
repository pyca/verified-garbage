import gen2, sched as S, emit
from emit import *
import emit3
def explicit_body(nspill):
    sv=dict(gen2.p); sp=dict(gen2.pick); R0=dict(gen2.R)
    for k in gen2.p: gen2.p[k]=0
    # A' then explicit rotation: post-process theta eor's
    import gen
    body=[]
    K=31-nspill; regs=gen2.G[:K]
    L={(x,y):regs[x+5*y] for x in range(5) for y in range(5)}; F=regs[25:K]
    for k in gen2.R: gen2.R[k]=0
    for k in gen2.pick: gen2.pick[k]=0
    for par in (0,1):
        c=gen2.scalar_round(par,L,F,nspill,par)
        reg=lambda l:L[gen2.loc(par,l)]
        # find theta applications: after D computed (5 eor with rot 63), the next eor's whose third operand is a D reg
        out=[];cnt=0;Dregs={};
        # reconstruct: theta ops occur in known order: cols 0,2,3,4 (20 ops) then one per row (col-1 lane)
        i0=[i for i,o in enumerate(c) if o[0]=='eor' and o[4]==63][-1]+1
        order=[(x,y) for x in (0,2,3,4) for y in range(5)]
        j=0
        for i,o in enumerate(c):
            out.append(o)
            if i>=i0 and j<20 and o[0]=='eor':
                l=order[j];j+=1
                if R0[l]: out.append(('ror',o[1],o[1],(64-R0[l])%64))
            elif i>=i0 and j>=20 and o[0]=='eor':
                pass
        # row col-1 ops: first eor of each row (preceded by fill or not)
        res=[];row=0;seen=0;k=0
        # rows start after 20 theta
        body_out=[];st=None;n20=0
        idx=0;state='theta'
        cntT=0
        for o in out:
            body_out.append(o)
        # locate rows: each row = [fill] eor(T) + 10 ops; walk
        # position after 20th theta application's ror
        pos=0;cc=0
        for q,o in enumerate(body_out):
            pass
        # simple: iterate and count eors after i0 in 'c' order
        res=[];cc=0;stage=0;rowpos=0
        started=False;eors=0
        ci=0
        for o in out:
            res.append(o)
            if ci>=i0 or started:
                started=True
            if o in c: ci+=1
            if started and o[0]=='eor' and not (ci<=i0):
                eors+=1
                if eors>20:
                    rp=(eors-21)%6   # T eor + 5 out eors per row
                    if rp==0:
                        y=(eors-21)//6; l=gen2.src((1+2*y)%5,y)
                        if R0[l]: res.append(('ror',o[1],o[1],(64-R0[l])%64))
        body.append(res)
    gen2.p.update(sv);gen2.pick.update(sp);gen2.R.update(R0)
    return L,F,body
