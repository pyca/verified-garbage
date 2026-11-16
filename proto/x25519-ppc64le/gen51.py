# Prototype generator: X25519 for PPC64LE, five 51-bit limbs, no carry flag
# in the ladder. Measurement only. Only instructions the ISA model has.
import sys
OPTS=set(sys.argv[1:])
L=[]
def e(s): L.append("\t"+s)
lab=[19]
# old 32-byte slots (setup, freeze), bits, saved registers
X1o,X2o,Z2o,X3o,Z3o,Y,BITS,SAVE=0,32,64,96,128,512,608,896
F=1088
X1,X2,Z2,X3,Z3,A,B,C,D,AA,BB,E,DA,CB,R=[F+40*k for k in range(15)]
def r(n): return f"%r{n}"
def li(d,i): e(f"li {r(d)}, {i}")
def ld(t,n,o): e(f"ld {r(t)}, {o}({r(n)})")
def std(t,n,o): e(f"std {r(t)}, {o}({r(n)})")
def lwz(t,n,o): e(f"lwz {r(t)}, {o}({r(n)})")
def stw(t,n,o): e(f"stw {r(t)}, {o}({r(n)})")
def op3(m,d,n,k): e(f"{m} {r(d)}, {r(n)}, {r(k)}")
def mul(d,n,m): op3("mulld",d,n,m)
def mulhu(d,n,m): op3("mulhdu",d,n,m)
def add(d,n,m): op3("add",d,n,m)
def addc(d,n,m): op3("addc",d,n,m)
def addze(d,n): e(f"addze {r(d)}, {r(n)}")
def sub(d,n,m): op3("subf",d,m,n)
def xor(d,n,m): op3("xor",d,n,m)
def and_(d,n,m): op3("and",d,n,m)
def lsl(d,n,s): e(f"sldi {r(d)}, {r(n)}, {s}")
def lsr(d,n,s): e(f"srdi {r(d)}, {r(n)}, {s}")
def subi(d,n,i): e(f"addi {r(d)}, {r(n)}, -{i}")
def loop(body,reg):
    lab[0]+=1; l=lab[0]; L.append(f"{l}:"); body(); e(f"cmpldi %cr0, {r(reg)}, 0"); e(f"bne %cr0, {l}b")
T=4
RA=[14,15,16,17,18]; RB=[19,20,21,22,23]; RN=[None,24,25,26,27]
LO=[7,8,9,10,11]; HI=[28,29,30,31,5]
def term(first,x,y,k):
    if first: mul(T,x,y); lsr(LO[k],T,13); mulhu(HI[k],x,y)
    else: mul(T,x,y); lsr(T,T,13); add(LO[k],LO[k],T); mulhu(T,x,y); add(HI[k],HI[k],T)
def terms(ts):
    seen=set()
    for (x,y,k) in ts: term(k not in seen,x,y,k); seen.add(k)
    return seen
def tail(o):
    for k in range(1,5): add(LO[k],LO[k],HI[k-1])
    li(4,1); lsl(4,4,51); subi(4,4,1); li(15,19)
    and_(14,HI[4],4); lsr(HI[4],HI[4],51); mul(14,14,15); mul(HI[4],HI[4],15); add(LO[0],LO[0],14); add(LO[1],LO[1],HI[4])
    for k in range(5):
        lsr(14,LO[k],51); and_(LO[k],LO[k],4)
        if k<4: add(LO[k+1],LO[k+1],14)
        else: mul(14,14,15); add(LO[0],LO[0],14)
    for k in range(5): std(LO[k],6,o+8*k)
def fmul(o,a,b):
    for i in range(5): ld(RA[i],6,a+8*i)
    for j in range(5): ld(RB[j],6,b+8*j)
    for i in range(5): lsl(RA[i],RA[i],8)
    for j in range(5): lsl(RB[j],RB[j],5)
    li(5,19)
    for j in range(1,5): mul(RN[j],RB[j],5)
    ts=[]
    for k in range(5):
        for i in range(5):
            j=(k-i)%5
            ts.append((RA[i], RB[j] if i+j<5 else RN[j], k))
    terms(ts); tail(o)
def fsqr(o,a):
    for i in range(5): ld(RA[i],6,a+8*i)
    Q=19; P=[None,20,21,22,23]
    lsl(Q,RA[0],4); lsl(RA[0],RA[0],9)
    for j in range(1,5): lsl(P[j],RA[j],5)
    s=set()
    def tt(ts):
        for (x,y,k) in ts: term(k not in s,x,y,k); s.add(k)
    tt([(RA[0],Q,0)]+[(RA[0],P[j],j) for j in range(1,5)])
    lsl(Q,RA[1],4); lsl(RA[1],RA[1],9); li(24,19); mul(P[4],P[4],24)
    tt([(RA[1],Q,2),(RA[1],P[2],3),(RA[1],P[3],4),(RA[1],P[4],0)])
    lsl(Q,RA[2],4); lsl(RA[2],RA[2],9); mul(P[3],P[3],24)
    tt([(RA[2],Q,4),(RA[2],P[3],0),(RA[2],P[4],1)])
    lsl(RA[3],RA[3],8)
    tt([(RA[3],P[3],1)])
    lsl(RA[3],RA[3],1)
    tt([(RA[3],P[4],2)])
    lsl(RA[4],RA[4],8)
    tt([(RA[4],P[4],3)])
    tail(o)
def a24(o,a):
    for i in range(5): ld(RA[i],6,a+8*i)
    for i in range(5): lsl(RA[i],RA[i],11)
    e("lis %r19, 1"); e("ori %r19, %r19, 0xdb41"); lsl(19,19,2)
    terms([(RA[k],19,k) for k in range(5)]); tail(o)
def fadd(o,a,b):
    for k in range(5): ld(7,6,a+8*k); ld(8,6,b+8*k); add(7,7,8); std(7,6,o+8*k)
def fsub(o,a,b):
    li(5,1); lsl(5,5,52); subi(9,5,38); subi(5,5,2)
    for k in range(5): ld(7,6,a+8*k); ld(8,6,b+8*k); add(7,7,9 if k==0 else 5); sub(7,7,8); std(7,6,o+8*k)
def cswap(x,y):
    for k in range(5):
        ld(5,6,x+8*k); ld(7,6,y+8*k); xor(8,5,7); and_(8,8,11); xor(5,5,8); xor(7,7,8); std(5,6,x+8*k); std(7,6,y+8*k)
def mask(): li(11,0); sub(11,11,0)
def step():
    subi(12,12,1); add(4,6,12); e(f"lbz %r4, {BITS}(%r4)"); xor(0,0,4); mask()
    cswap(X2,X3); cswap(Z2,Z3); e("addi %r0, %r4, 0")
    fadd(A,X2,Z2); fsqr(AA,A); fsub(B,X2,Z2); fsqr(BB,B); fsub(E,AA,BB); fadd(C,X3,Z3); fsub(D,X3,Z3)
    fmul(DA,D,A); fmul(CB,C,B); fadd(X3,DA,CB); fsqr(X3,X3); fsub(Z3,DA,CB); fsqr(Z3,Z3); fmul(Z3,X1,Z3)
    fmul(X2,AA,BB); a24(Z2,E); fadd(Z2,AA,Z2); fmul(Z2,E,Z2)
def sqn(o,a,n):
    fsqr(o,a); li(12,n-1)
    def body(): fsqr(o,o); subi(12,12,1)
    loop(body,12)
def invert():
    fsqr(A,Z2); fsqr(B,A); fsqr(B,B); fmul(B,Z2,B); fmul(A,A,B); fsqr(C,A); fmul(B,B,C)
    sqn(C,B,5); fmul(B,C,B); sqn(C,B,10); fmul(C,C,B); sqn(D,C,20); fmul(C,D,C); sqn(C,C,10); fmul(B,C,B)
    sqn(C,B,50); fmul(C,C,B); sqn(D,C,100); fmul(C,D,C); sqn(C,C,50); fmul(B,C,B); sqn(B,B,5); fmul(R,B,A)
def low31(): lsl(7,7,33); lsr(7,7,33)
def carry(rb,off): add(7,7,8); stw(7,rb,off); e("srdi %r8, %r7, 32")
def setup():
    for k in range(8):
        lwz(7,5,4*k)
        if k==7: low31()
        stw(7,6,X1o+4*k); stw(7,6,X3o+4*k)
    li(7,1); li(8,0); stw(7,6,X2o); stw(8,6,Z2o); stw(7,6,Z3o)
    for o in (X2o,Z2o,Z3o):
        for k in range(1,8): stw(8,6,o+4*k)
def unpack():
    # the four words at X1o into five limbs at X1 and X3; x2 = 1, z2 = 0, z3 = 1
    li(4,1); lsl(4,4,51); subi(4,4,1)
    for k in range(4): ld(7+k,6,X1o+8*k)
    W=[7,8,9,10]
    and_(5,W[0],4); std(5,6,X1); std(5,6,X3)
    for k,(a,b) in enumerate([(51,13),(38,26),(25,39)]):
        lsr(5,W[k],a); lsl(11,W[k+1],b); add(5,5,11); and_(5,5,4); std(5,6,X1+8*(k+1)); std(5,6,X3+8*(k+1))
    lsr(5,W[3],12); std(5,6,X1+32); std(5,6,X3+32)
    li(7,1); li(8,0)
    std(7,6,X2); std(8,6,Z2); std(7,6,Z3)
    for o in (X2,Z2,Z3):
        for k in range(1,5): std(8,6,o+8*k)
def pack():
    # the limbs at X2 into the four words at X2o
    for k in range(5): ld(7+k,6,X2+8*k)
    l=[7,8,9,10,11]
    lsl(4,l[1],51); lsr(5,l[1],13); lsl(l[1],l[2],38); add(l[1],l[1],5)
    lsr(5,l[2],26); lsl(l[2],l[3],25); add(l[2],l[2],5)
    lsr(5,l[3],39); lsl(l[3],l[4],12); add(l[3],l[3],5)
    addc(l[0],l[0],4); addze(l[1],l[1]); addze(l[2],l[2]); addze(l[3],l[3])
    for k in range(4): std(l[k],6,X2o+8*k)
def bits():
    e("addi %r9, %r6, 0"); li(11,32)
    def body():
        e("lbz %r7, 0(%r4)")
        for j in range(8): e(f"sldi %r8, %r7, {63-j}"); e("srdi %r8, %r8, 63"); e(f"stb %r8, {BITS+j}(%r9)")
        e("addi %r4, %r4, 1"); e("addi %r9, %r9, 8"); e("addi %r11, %r11, -1")
    loop(body,11)
    li(7,0); e(f"stb %r7, {BITS}(%r6)"); e(f"stb %r7, {BITS+1}(%r6)"); e(f"stb %r7, {BITS+2}(%r6)"); li(7,1); e(f"stb %r7, {BITS+254}(%r6)")
def freeze():
    lwz(7,6,X2o+28); e("srdi %r8, %r7, 31"); low31(); stw(7,6,X2o+28); li(5,19); mul(8,8,5)
    for k in range(8): lwz(7,6,X2o+4*k); carry(6,X2o+4*k)
    li(8,19)
    for k in range(8): lwz(7,6,X2o+4*k); carry(6,Y+4*k)
    lwz(7,6,Y+28); e("srdi %r11, %r7, 31"); li(4,0); sub(11,4,11); low31(); stw(7,6,Y+28)
    for k in range(8):
        lwz(5,6,X2o+4*k); lwz(7,6,Y+4*k); xor(7,7,5); and_(7,7,11); xor(5,5,7); stw(5,3,4*k)
nv=list(range(14,32))
L.append(".text\n.globl x_new\n.type x_new,@function\nx_new:" if "harness" in OPTS else "")
setup(); bits(); unpack()
for k,g in enumerate(nv): std(g,6,SAVE+8*k)
li(12,255); li(0,0); loop(step,12)
mask(); cswap(X2,X3); cswap(Z2,Z3)
invert(); fmul(X2,X2,R); pack()
for k,g in enumerate(nv): ld(g,6,SAVE+8*k)
freeze()
e("blr")
print("\n".join(L))
