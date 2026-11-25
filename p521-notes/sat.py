import random,subprocess,re
p=2**521-1
M64=2**64-1
class Sim:
    def __init__(s): s.r={}; s.m={}; s.c=0
    def run(s,code):
        for l in code:
            op,rest=l.split(None,1); a=[x.strip() for x in re.split(r',(?![^\[]*\])',rest)]
            g=lambda x: s.r[x]
            if op=='ldr':
                b,o=re.match(r'\[(\w+),#(\d+)\]',a[1]).groups(); s.r[a[0]]=s.m[(b,int(o))]
            elif op=='str':
                b,o=re.match(r'\[(\w+),#(\d+)\]',a[1]).groups(); s.m[(b,int(o))]=g(a[0])
            elif op=='mul': s.r[a[0]]=g(a[1])*g(a[2])&M64
            elif op=='umulh': s.r[a[0]]=g(a[1])*g(a[2])>>64
            elif op in('adds','adcs','adc','add'):
                v=g(a[1])+g(a[2])+(s.c if op in('adcs','adc') else 0)
                s.r[a[0]]=v&M64
                if op in('adds','adcs'): s.c=v>>64
                elif v>>64: print("LOST",l)
            elif op in('subs','sbcs'):
                v=g(a[1])+(M64^g(a[2]))+(1 if op=='subs' else s.c); s.r[a[0]]=v&M64; s.c=v>>64
            elif op=='lsl': s.r[a[0]]=g(a[1])<<int(a[2][1:])&M64
            elif op=='lsr': s.r[a[0]]=g(a[1])>>int(a[2][1:])
            elif op=='extr': s.r[a[0]]=((g(a[1])<<64|g(a[2]))>>int(a[3][1:]))&M64
            elif op=='and': s.r[a[0]]=g(a[1])&g(a[2])
            elif op=='mov': s.r[a[0]]=int(a[1][1:])
            else: raise Exception(l)
def mca(code,cpu='neoverse-n2'):
    open('t.s','w').write('\n'.join(code)+'\n')
    o=subprocess.run(['llvm-mca','-mtriple=aarch64','-mcpu='+cpu,'-iterations=20','t.s'],capture_output=True,text=True).stdout
    return int(re.search(r'Total Cycles:\s+(\d+)',o)[1])/20, len(code)

ACC=['x8','x9','x10','x11','x12','x13','x14','x15','x21','x22','x23']
def tail(w,t,o='x0',oo=0,f='x1',mask='x2'):
    c=[f"lsr {f},{w[8]},#9",f"mov {mask},#511",f"and {w[8]},{w[8]},{mask}",f"adds {w[0]},{w[0]},{f}"]
    c+=[f"adcs {w[k]},{w[k]},x7" for k in range(1,9)]
    return c
def mul(ra='x28',oa=0,b=None,ro='x30',oo=0,bmem=None):
    c=[]; W=lambda k:ACC[k%11]
    B=b; t='x2'; ai='x1'; z='x7'
    c.append(f"ldr {ai},[{ra},#{oa}]")
    for j in range(9): c.append(f"mul {W(j)},{ai},{B[j]}")
    for j in range(9):
        c.append(f"umulh {t},{ai},{B[j]}")
        if j==8: c.append(f"adc {W(9)},{t},{z}")
        else: c.append(f"{'adds' if j==0 else 'adcs'} {W(j+1)},{W(j+1)},{t}")
    for i in range(1,9):
        c.append(f"ldr {ai},[{ra},#{oa+8*i}]")
        for j in range(9):
            c.append(f"mul {t},{ai},{B[j]}"); c.append(f"{'adds' if j==0 else 'adcs'} {W(i+j)},{W(i+j)},{t}")
        nw=W(i+9)
        c.append(f"umulh {t},{ai},{B[8]}"); c.append(f"adc {nw},{t},{z}")
        for j in range(8):
            c.append(f"umulh {t},{ai},{B[j]}"); c.append(f"{'adds' if j==0 else 'adcs'} {W(i+j+1)},{W(i+j+1)},{t}")
        c.append(f"adc {nw},{nw},{z}")
        if i%2==1:
            l0,l1=W(i-1),W(i)
            c+= [f"lsl {t},{l0},#9",f"extr {l0},{l1},{l0},#55",f"lsr {l1},{l1},#55",
                 f"adds {W(i+7)},{W(i+7)},{t}",f"adcs {W(i+8)},{W(i+8)},{l0}",f"adc {W(i+9)},{W(i+9)},{l1}"]
    l=W(8)
    c+=[f"lsl {t},{l},#9",f"lsr {W(17)},{l},#55",f"adds {W(16)},{W(16)},{t}",f"adc {W(17)},{W(17)},{z}"]
    w=[W(9+k) for k in range(9)]
    c+=tail(w,t)
    c+=[f"str {w[k]},[{ro},#{oo+8*k}]" for k in range(9)]
    return c
bregs=["x4","x5","x16","x17","x6","x24","x25","x26","x27"]
if __name__=='__main__':
    R=2**576
    c=mul(b=bregs)
    for trial in range(300):
        a=random.choice([random.randrange(p),p-1,0,1,2**520,p-random.randrange(100)]);b=random.choice([random.randrange(p),p-1,1,0])
        s=Sim(); s.r['x7']=0
        for i in range(9): s.m[('x28',8*i)]=a>>64*i&M64; s.r[bregs[i]]=b>>64*i&M64
        s.run(c)
        o=sum(s.m[('x30',8*k)]<<64*k for k in range(9))
        assert o==a*b*pow(R,-1,p)%p,(hex(o))
    print('ok',len(c),[mca(c,x) for x in('neoverse-n2','neoverse-v2','apple-m1')])
