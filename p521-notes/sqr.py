from sat import *
def sqr(ra='x28',oa=0,ro='x30',oo=0):
    c=[]; z='x7'; t='x2'; ai='x1'; F='x3'
    wr=['x8','x9','x10','x11','x12','x13','x14','x15','x21','x22']
    D={j:r for j,r in zip(range(2,9),['x4','x5','x16','x17','x6','x23','x24'])}
    for j in range(2,9): wr.append(D[j])
    W=lambda k:wr[k]
    c.append(f"ldr {W(0)},[{ra},#{oa+8}]"); cur,nxt=W(0),W(1)
    for j in range(2,9):
        c.append(f"ldr {nxt},[{ra},#{oa+8*j}]"); c.append(f"extr {D[j]},{nxt},{cur},#63"); cur,nxt=nxt,cur
    c.append(f"mov {z},#0")
    for i in range(9):
        c.append(f"ldr {ai},[{ra},#{oa+8*i}]")
        if i<8: c+= [f"ldr {F},[{ra},#{oa+8*i+8}]",f"lsl {F},{F},#1"]
        Q=[ai]+([F] if i<8 else [])+[D[j] for j in range(i+2,9)]; n=len(Q); base=2*i
        if i==0:
            for j in range(n): c.append(f"mul {W(j)},{ai},{Q[j]}")
            for j in range(n):
                c.append(f"umulh {t},{ai},{Q[j]}")
                if j==n-1: c.append(f"adc {W(9)},{t},{z}")
                else: c.append(f"{'adds' if j==0 else 'adcs'} {W(j+1)},{W(j+1)},{t}")
        elif i<8:
            for j in range(n):
                c.append(f"mul {t},{ai},{Q[j]}"); k=base+j
                c.append(f"{'adds' if j==0 else 'adcs'} {W(k)},{W(k)},{t}")
            nw=W(i+9)
            c.append(f"umulh {t},{ai},{Q[n-1]}"); c.append(f"adc {nw},{t},{z}")
            for j in range(n-1):
                c.append(f"umulh {t},{ai},{Q[j]}"); c.append(f"{'adds' if j==0 else 'adcs'} {W(base+j+1)},{W(base+j+1)},{t}")
            c.append(f"adc {nw},{nw},{z}")
        else:
            c.append(f"mul {t},{ai},{ai}"); c.append(f"add {W(16)},{W(16)},{t}")
    c+= [f"lsl {t},{W(0)},#9",f"adds {W(8)},{W(8)},{t}"]
    for j in range(8): c.append(f"extr {W(j)},{W(j+1)},{W(j)},#55")
    c.append(f"lsr {W(8)},{W(8)},#55")
    for j in range(8): c.append(f"adcs {W(j)},{W(9+j)},{W(j)}")
    c.append(f"adc {W(8)},{W(8)},{z}")
    w=[W(k) for k in range(9)]
    c+=tail(w,t)
    c+=[f"str {w[k]},[{ro},#{oo+8*k}]" for k in range(9)]
    return c
if __name__=='__main__':
    R=2**576; c=sqr()
    for trial in range(500):
        a=random.choice([random.randrange(p),p-1,0,1,2**520,p-random.randrange(100),(1<<521)-(1<<random.randrange(520))-1])
        s=Sim()
        for i in range(9): s.m[('x28',8*i)]=a>>64*i&M64
        s.run(c)
        o=sum(s.m[('x30',8*k)]<<64*k for k in range(9))
        assert o==a*a*pow(R,-1,p)%p,(hex(o))
    print('ok',len(c),[mca(c,x) for x in('neoverse-n2','neoverse-v2','apple-m1')])
