# The numeric checker, as first run inline on the first draft of P256Square.lean.
import re, random, sys
src=open(sys.argv[1]).read()
p=2**256-2**224+2**192+2**96-1; M64=2**64-1
blocks={}
for m in re.finditer(r"def (\w+'?) : List Instr :=\n((?:  .*\n|   .*\n)+)",src): blocks[m.group(1)]=re.findall(r"\.(\w+) (?:\.x )?((?:\.x\d+ ?)+)(\d+)?",m.group(2))
order="crossMul crossAdd crossAdd' double diagonalMul diagonalAdd quotient addTop subShift addShift sum".split()
def run(A):
    r={f'x{i}':random.getrandbits(64) for i in range(31)}; r['x7']=0
    for i in range(4): r[f'x{3+i}']=A>>64*i&M64
    c=0
    for b in order:
        for op,regs,imm in blocks[b]:
            R=[x.strip('. ') for x in regs.split()]
            d=R[0]; v=[r[x] for x in R[1:]]
            if op=='mul': x=v[0]*v[1]
            elif op=='umulh': x=v[0]*v[1]>>64
            elif op in('add',): x=v[0]+v[1]
            elif op=='sub': x=v[0]-v[1]
            elif op in('adds','adcs','adc'):
                x=v[0]+v[1]+(0 if op=='adds' else c)
                if op!='adc': c=x>>64
            elif op in('subs','sbcs','sbc'):
                x=v[0]+(M64^v[1])+(1 if op=='subs' else c)
                if op!='sbc': c=x>>64
            elif op=='lsl': x=v[0]<<int(imm)
            elif op=='lsr': x=v[0]>>int(imm)
            elif op=='extr': x=((v[0]<<64|v[1])>>int(imm))
            else: raise Exception(op)
            r[d]=x&M64
    return sum(r[f'x{8+i}']<<64*i for i in range(5))
Ri=pow(2**256,-1,p)
for k in range(20000):
    A=random.choice([random.randrange(p),p-1-random.randrange(100),random.randrange(1<<random.randrange(1,257))%p, sum(random.choice([0,M64,1,2**32-1,2**32,M64<<32&M64])<<64*i for i in range(4))%p])
    Z=run(A); assert Z<2*p and (Z-A*A*Ri)%p==0,(hex(A),)
print('ok')
