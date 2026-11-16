# Prototype generator: X25519 for PPC64LE. Measurement only.
# Four 64-bit words everywhere; a multiplication by rows, a square of its
# own, additions and subtractions with one carry chain and a masked fold,
# swaps of 64-bit words. Only instructions the ISA model has.
import sys
OPTS=set(sys.argv[1:])
L=[]
def e(s): L.append("\t"+s)
lab=[19]
X1,X2,Z2,X3,Z3,A,B,C,D,AA,BB,E,DA,CB,R,Y,BITS,SAVE=0,32,64,96,128,160,192,224,256,288,320,352,384,416,480,512,608,896
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
def adde(d,n,m): op3("adde",d,n,m)
def addze(d,n): e(f"addze {r(d)}, {r(n)}")
def sub(d,n,m): op3("subf",d,m,n)
def subc(d,n,m): op3("subfc",d,m,n)
def sube(d,n,m): op3("subfe",d,m,n)
def xor(d,n,m): op3("xor",d,n,m)
def and_(d,n,m): op3("and",d,n,m)
def loop(body,reg):
    lab[0]+=1; l=lab[0]; L.append(f"{l}:"); body(); e(f"cmpldi %cr0, {r(reg)}, 0"); e(f"bne %cr0, {l}b")
opA=[14,15,16,17]; opB=[18,19,20,21]; pw=[22,23,24,25,26,27,28,29,30]; T=[8,9,10,11]; ZR=30
def stores(regs,o):
    for k in range(4): std(regs[k],6,o+8*k)
# --- reduction: pw0..7 -> pw0..3 (< 2^256), 38 in r5, zero in ZR
def reduce(o):
    li(5,38)
    for j in range(4): mul(T[j],pw[4+j],5)
    addc(pw[0],pw[0],T[0])
    for j in range(1,4): adde(pw[j],pw[j],T[j])
    addze(7,ZR)
    for j in range(4): mulhu(T[j],pw[4+j],5)
    addc(pw[1],pw[1],T[0]); adde(pw[2],pw[2],T[1]); adde(pw[3],pw[3],T[2]); adde(7,7,T[3])
    mul(7,7,5)
    addc(pw[0],pw[0],7)
    for j in range(1,4): addze(pw[j],pw[j])
    sube(7,7,7); and_(7,7,5); sub(7,5,7); add(pw[0],pw[0],7)
    stores(pw,o)
def fmul(o,a,b):
    for i in range(4): ld(opA[i],6,a+8*i)
    for j in range(4): ld(opB[j],6,b+8*j)
    li(ZR,0)
    # row 0
    for j in range(4): mul(pw[j],opA[j],opB[0])
    for j in range(4): mulhu(T[j],opA[j],opB[0])
    addc(pw[1],pw[1],T[0]); adde(pw[2],pw[2],T[1]); adde(pw[3],pw[3],T[2]); addze(pw[4],T[3])
    for i in range(1,4):
        for j in range(4): mul(T[j],opA[j],opB[i])
        addc(pw[i],pw[i],T[0])
        for j in range(1,4): adde(pw[i+j],pw[i+j],T[j])
        addze(pw[i+4],ZR)
        for j in range(4): mulhu(T[j],opA[j],opB[i])
        addc(pw[i+1],pw[i+1],T[0])
        for j in range(1,4): adde(pw[i+1+j],pw[i+1+j],T[j])
    reduce(o)
def fsqr(o,a):
    a0,a1,a2,a3=opA; t0,t1,t2,t3=T; acc=pw
    for i in range(4): ld(opA[i],6,a+8*i)
    li(ZR,0)
    mul(acc[1],a1,a0); mulhu(t1,a1,a0); mul(acc[2],a2,a0); mulhu(t2,a2,a0); mul(acc[3],a3,a0); mulhu(acc[4],a3,a0)
    addc(acc[2],acc[2],t1); adde(acc[3],acc[3],t2); addze(acc[4],acc[4])
    mul(t0,a2,a1); mulhu(t1,a2,a1); mul(t2,a3,a1); mulhu(t3,a3,a1); mul(acc[5],a3,a2); mulhu(acc[6],a3,a2)
    addc(t1,t1,t2); addze(t2,t3)
    addc(acc[3],acc[3],t0); adde(acc[4],acc[4],t1); adde(acc[5],acc[5],t2); addze(acc[6],acc[6])
    addc(acc[1],acc[1],acc[1])
    for k in range(2,7): adde(acc[k],acc[k],acc[k])
    addze(acc[7],ZR)
    # the squares: low words into acc0, t1, t2, t3; high words into b regs
    h=opB
    mul(acc[0],a0,a0); mulhu(h[0],a0,a0); mul(t1,a1,a1); mulhu(h[1],a1,a1)
    mul(t2,a2,a2); mulhu(h[2],a2,a2); mul(t3,a3,a3); mulhu(h[3],a3,a3)
    addc(acc[1],acc[1],h[0]); adde(acc[2],acc[2],t1); adde(acc[3],acc[3],h[1]); adde(acc[4],acc[4],t2)
    adde(acc[5],acc[5],h[2]); adde(acc[6],acc[6],t3); adde(acc[7],acc[7],h[3])
    reduce(o)
W=[8,9,10,11]
def fadd(o,a,b):
    for k in range(4):
        ld(W[k],6,a+8*k); ld(4,6,b+8*k); (addc if k==0 else adde)(W[k],W[k],4)
    li(5,38); li(4,0)
    sube(7,7,7); and_(7,7,5); sub(7,5,7)
    addc(W[0],W[0],7)
    for k in range(1,4): addze(W[k],W[k])
    sube(7,7,7); and_(7,7,5); sub(7,5,7); add(W[0],W[0],7)
    stores(W,o)
def fsub(o,a,b):
    for k in range(4):
        ld(W[k],6,a+8*k); ld(4,6,b+8*k); (subc if k==0 else sube)(W[k],W[k],4)
    li(5,38); li(4,0)
    sube(7,7,7); and_(7,7,5)
    subc(W[0],W[0],7)
    for k in range(1,4): sube(W[k],W[k],4)
    sube(7,7,7); and_(7,7,5); sub(W[0],W[0],7)
    stores(W,o)
def a24(o,a):
    e("lis %r5, 1"); e("ori %r5, %r5, 0xdb41")
    for k in range(4): ld(W[k],6,a+8*k)
    li(4,0)
    mulhu(7,W[0],5); mul(W[0],W[0],5)
    # high words into r7 (of w0), r22.. are free here but keep to volatile: use r4? need 4 highs
    H=[7,22,23,24]
    for k in range(1,4): mulhu(H[k],W[k],5)
    for k in range(1,4): mul(W[k],W[k],5)
    addc(W[1],W[1],H[0]); adde(W[2],W[2],H[1]); adde(W[3],W[3],H[2]); addze(7,H[3])
    li(5,38); mul(7,7,5)
    addc(W[0],W[0],7)
    for k in range(1,4): addze(W[k],W[k])
    sube(7,7,7); and_(7,7,5); sub(7,5,7); add(W[0],W[0],7)
    stores(W,o)
def cswap(x,y):
    for k in range(4):
        ld(5,6,x+8*k); ld(7,6,y+8*k); xor(8,5,7); and_(8,8,11); xor(5,5,8); xor(7,7,8); std(5,6,x+8*k); std(7,6,y+8*k)
def mask(): li(11,0); sub(11,11,0)
def step():
    e("addi %r12, %r12, -1"); add(4,6,12); e(f"lbz %r4, {BITS}(%r4)"); xor(0,0,4); mask()
    cswap(X2,X3); cswap(Z2,Z3); e("addi %r0, %r4, 0")
    fadd(A,X2,Z2); fsqr(AA,A); fsub(B,X2,Z2); fsqr(BB,B); fsub(E,AA,BB); fadd(C,X3,Z3); fsub(D,X3,Z3)
    fmul(DA,D,A); fmul(CB,C,B); fadd(X3,DA,CB); fsqr(X3,X3); fsub(Z3,DA,CB); fsqr(Z3,Z3); fmul(Z3,X1,Z3)
    fmul(X2,AA,BB); a24(Z2,E); fadd(Z2,AA,Z2); fmul(Z2,E,Z2)
def sqn(o,a,n):
    fsqr(o,a); li(12,n-1)
    def body(): fsqr(o,o); e("addi %r12, %r12, -1")
    loop(body,12)
def invert():
    fsqr(A,Z2); fsqr(B,A); fsqr(B,B); fmul(B,Z2,B); fmul(A,A,B); fsqr(C,A); fmul(B,B,C)
    sqn(C,B,5); fmul(B,C,B); sqn(C,B,10); fmul(C,C,B); sqn(D,C,20); fmul(C,D,C); sqn(C,C,10); fmul(B,C,B)
    sqn(C,B,50); fmul(C,C,B); sqn(D,C,100); fmul(C,D,C); sqn(C,C,50); fmul(B,C,B); sqn(B,B,5); fmul(R,B,A)
def low31(): e("sldi %r7, %r7, 33"); e("srdi %r7, %r7, 33")
def carry(rb,off): add(7,7,8); stw(7,rb,off); e("srdi %r8, %r7, 32")
def setup():
    for k in range(8):
        lwz(7,5,4*k)
        if k==7: low31()
        stw(7,6,X1+4*k); stw(7,6,X3+4*k)
    li(7,1); li(8,0); stw(7,6,X2); stw(8,6,Z2); stw(7,6,Z3)
    for o in (X2,Z2,Z3):
        for k in range(1,8): stw(8,6,o+4*k)
def bits():
    e("addi %r9, %r6, 0"); li(11,32)
    def body():
        e("lbz %r7, 0(%r4)")
        for j in range(8): e(f"sldi %r8, %r7, {63-j}"); e("srdi %r8, %r8, 63"); e(f"stb %r8, {BITS+j}(%r9)")
        e("addi %r4, %r4, 1"); e("addi %r9, %r9, 8"); e("addi %r11, %r11, -1")
    loop(body,11)
    li(7,0); e(f"stb %r7, {BITS}(%r6)"); e(f"stb %r7, {BITS+1}(%r6)"); e(f"stb %r7, {BITS+2}(%r6)"); li(7,1); e(f"stb %r7, {BITS+254}(%r6)")
def freeze():
    lwz(7,6,X2+28); e("srdi %r8, %r7, 31"); low31(); stw(7,6,X2+28); li(5,19); mul(8,8,5)
    for k in range(8): lwz(7,6,X2+4*k); carry(6,X2+4*k)
    li(8,19)
    for k in range(8): lwz(7,6,X2+4*k); carry(6,Y+4*k)
    lwz(7,6,Y+28); e("srdi %r11, %r7, 31"); li(4,0); sub(11,4,11); low31(); stw(7,6,Y+28)
    for k in range(8):
        lwz(5,6,X2+4*k); lwz(7,6,Y+4*k); xor(7,7,5); and_(7,7,11); xor(5,5,7); stw(5,3,4*k)
nv=opA+opB+pw
L.append(".text\n.globl x_new\n.type x_new,@function\nx_new:" if "harness" in OPTS else "")
setup(); bits()
for k,g in enumerate(nv): std(g,6,SAVE+8*k)
li(12,255); li(0,0); loop(step,12)
mask(); cswap(X2,X3); cswap(Z2,Z3)
invert(); fmul(X2,X2,R)
for k,g in enumerate(nv): ld(g,6,SAVE+8*k)
freeze()
e("blr")
print("\n".join(L))
