# Prototype generator: X25519 for ARMv7 with umaal, 8 x 32-bit words. Measurement only.
import sys
L=[]
def e(s): L.append("\t"+s)
lab=[0]
def label():
    lab[0]+=1; return f".Lp{lab[0]}"
# layout (offsets from r0 = scratch)
SAVE=0; OUT=40; CNT=44; SWAP=48; CNT2=52
X1,X2,Z2,X3,Z3,A,B,C,D,AA,BB,E,T0,T1,T2,T3=[64+32*i for i in range(16)]
ACC=64+32*16
BITS=ACC+32
def m(o,k=0): return f"[r0, #{o+4*k}]"
ACCR=['r4','r5','r6','r7','r8','r9','r10','r11']
def fold19(R,c):
    # R: 8 regs (value < 2^256), c: carry word reg; free regs: listed in fr
    # q = 2c + bit255; R7 &= 0x7fffffff; t = 19 q; R += t
    e(f"lsr r12, {R[7]}, #31"); e(f"add r12, r12, {c}, lsl #1"); e(f"bic {R[7]}, {R[7]}, #0x80000000")
    e("add lr, r12, r12, lsl #1"); e("add r12, lr, r12, lsl #4")   # 19 q
    e("mov lr, #0")
    for k in range(8): e(f"umaal {R[k]}, r12, lr, lr")
def stores(o,R):
    for k in range(8): e(f"str {R[k]}, {m(o,k)}")
def mul(o,a,b):
    regs=['r3']+ACCR[:]   # regs[0] = carry of the row, regs[1..8] = acc words i..i+7
    for r in ACCR: e(f"mov {r}, #0")
    for i in range(8):
        c=regs[0]; acc=regs[1:]
        e(f"ldr r1, {m(a,i)}"); e(f"mov {c}, #0")
        for j in range(8):
            e(f"ldr r2, {m(b,j)}"); e(f"umaal {acc[j]}, {c}, r1, r2")
        e(f"str {acc[0]}, {m(ACC,i)}")
        regs=[acc[0]]+acc[1:]+[c]
    H=regs[1:]; s=regs[0]
    # L + 38 H
    e("mov r1, #0"); e("mov r2, #38")
    R=[]
    for k in range(8):
        e(f"ldr {s}, {m(ACC,k)}"); e(f"umaal {s}, r1, r2, {H[k]}")
        R.append(s); s=H[k]
    fold19(R,'r1'); stores(o,R)
def sqr(o,a): mul(o,a,a)
XR=['r4','r5','r6','r7','r8','r9','r10','r11']
def addL(o,a,b):
    e("mov r1, #0"); e("mov r2, #1")
    for k in range(8):
        e(f"ldr {XR[k]}, {m(a,k)}"); e(f"ldr r3, {m(b,k)}"); e(f"umaal {XR[k]}, r1, r2, r3")
    e("mov r3, #38"); e("mul r1, r1, r3"); e("mov r3, #0")
    for k in range(8): e(f"umaal {XR[k]}, r1, r3, r3")
    stores(o,XR)
def subL(o,a,b):
    e("mov r1, #1"); e("mov r2, #1")
    for k in range(8):
        e(f"ldr {XR[k]}, {m(a,k)}"); e(f"ldr r3, {m(b,k)}"); e("mvn r3, r3"); e(f"umaal {XR[k]}, r1, r2, r3")
    e("sub r1, r1, #1"); e("bic r3, r1, #37"); e("mov r12, #0")
    e(f"umaal {XR[0]}, r12, r2, r3")
    for k in range(1,8): e(f"umaal {XR[k]}, r12, r2, r1")
    stores(o,XR)
def a24add(o,b,a):
    e("movw r2, #0xdb41"); e("movt r2, #1"); e("mov r1, #0")
    for k in range(8):
        e(f"ldr {XR[k]}, {m(b,k)}"); e(f"ldr r3, {m(a,k)}"); e(f"umaal {XR[k]}, r1, r2, r3")
    fold19(XR,'r1'); stores(o,XR)
def cswap(x,y):  # mask in r1
    for k in range(8):
        e(f"ldr r2, {m(x,k)}"); e(f"ldr r3, {m(y,k)}"); e("eor r12, r2, r3"); e("and r12, r12, r1")
        e("eor r2, r2, r12"); e("eor r3, r3, r12"); e(f"str r2, {m(x,k)}"); e(f"str r3, {m(y,k)}")
def step():
    # t = CNT - 1; bit = BITS[t]; mask = -(swap ^ bit); swap = bit
    e(f"ldr r1, {m(CNT)}"); e("sub r1, r1, #1"); e(f"str r1, {m(CNT)}")
    e("add r2, r0, r1"); e(f"ldrb r2, [r2, #{BITS}]"); e(f"ldr r3, {m(SWAP)}"); e(f"str r2, {m(SWAP)}")
    e("eor r2, r2, r3"); e("mov r1, #0"); e("sub r1, r1, r2")
    cswap(X2,X3); cswap(Z2,Z3)
    addL(A,X2,Z2); subL(B,X2,Z2); addL(C,X3,Z3); subL(D,X3,Z3)
    sqr(AA,A); sqr(BB,B); mul(T0,D,A); mul(T1,C,B)
    subL(E,AA,BB); addL(T2,T0,T1); subL(T3,T0,T1)
    sqr(X3,T2); sqr(T3,T3); mul(Z3,X1,T3)
    mul(X2,AA,BB); a24add(T2,AA,E); mul(Z2,E,T2)
def sqrn(o,n):  # o = o^(2^n), n >= 1, counter in memory
    if n<=2:
        for _ in range(n): sqr(o,o)
        return
    l=label(); e(f"mov r1, #{n}"); e(f"str r1, {m(CNT2)}"); L.append(l+":"); sqr(o,o)
    e(f"ldr r1, {m(CNT2)}"); e("subs r1, r1, #1"); e(f"str r1, {m(CNT2)}"); e(f"bne {l}")
def copy(o,a):
    for k in range(8): e(f"ldr r1, {m(a,k)}"); e(f"str r1, {m(o,k)}")
def invert(o,z):  # ref10 chain; temporaries A,B,C,D (free after the ladder)
    t0,t1,t2,t3=A,B,C,D
    sqr(t0,z); sqr(t1,t0); sqr(t1,t1); mul(t1,z,t1); mul(t0,t0,t1); sqr(t2,t0); mul(t1,t1,t2)
    sqr(t2,t1); sqrn(t2,4); mul(t1,t2,t1)
    sqr(t2,t1); sqrn(t2,9); mul(t2,t2,t1)
    sqr(t3,t2); sqrn(t3,19); mul(t2,t3,t2)
    sqr(t2,t2); sqrn(t2,9); mul(t1,t2,t1)
    sqr(t2,t1); sqrn(t2,49); mul(t2,t2,t1)
    sqr(t3,t2); sqrn(t3,99); mul(t2,t3,t2)
    sqr(t2,t2); sqrn(t2,49); mul(t1,t2,t1)
    sqr(t1,t1); sqrn(t1,4); mul(o,t1,t0)
def function(name):
    L.append(f"\t.globl {name}\n\t.type {name}, %function\n{name}:")
    # save r4-r11, lr, out
    for i,r in enumerate(['r4','r5','r6','r7','r8','r9','r10','r11','lr']): e(f"str {r}, [r3, #{SAVE+4*i}]")
    e(f"str r0, [r3, #{OUT}]"); e("mov r0, r3")
    # point words (r2), top bit cleared, into X1 and X3; x2 = 1, z2 = 0, z3 = 1
    for k in range(8):
        e(f"ldr r4, [r2, #{4*k}]")
        if k==7: e("bic r4, r4, #0x80000000")
        e(f"str r4, {m(X1,k)}"); e(f"str r4, {m(X3,k)}")
    e("mov r4, #0"); e("mov r5, #1")
    for k in range(8):
        e(f"str {'r5' if k==0 else 'r4'}, {m(X2,k)}"); e(f"str r4, {m(Z2,k)}"); e(f"str {'r5' if k==0 else 'r4'}, {m(Z3,k)}")
    e(f"str r4, {m(SWAP)}")
    # bits of the clamped scalar: BITS[8i+j]
    e("mov r4, #32"); e("mov r6, r0"); l=label(); L.append(l+":")
    e("ldrb r5, [r1, #0]")
    for j in range(8):
        e(f"lsr r7, r5, #{j}" if j else "mov r7, r5"); e("and r7, r7, #1"); e(f"strb r7, [r6, #{BITS+j}]")
    e("add r1, r1, #1"); e("add r6, r6, #8"); e("subs r4, r4, #1"); e(f"bne {l}")
    e("mov r4, #0"); e("mov r5, #1")
    for t in (0,1,2,255): e(f"strb r4, {m(BITS+t)}")
    e(f"strb r5, {m(BITS+254)}")
    e("mov r4, #255"); e(f"str r4, {m(CNT)}")
    l=label(); L.append(l+":"); step()
    e(f"ldr r1, {m(CNT)}"); e("cmp r1, #0"); e(f"bne {l}")
    e(f"ldr r2, {m(SWAP)}"); e("mov r1, #0"); e("sub r1, r1, r2"); cswap(X2,X3); cswap(Z2,Z3)
    invert(T1,Z2); mul(X2,X2,T1)
    # freeze X2 (< 2^255 + small): add 19, take bit 255 -> q; x + 19 q, clear bit 255; twice
    for k in range(8): e(f"ldr {XR[k]}, {m(X2,k)}")
    for _ in range(2):
        e("mov r1, #19"); e("mov r3, #0")
        R2=['r2']  # compute carry of x+19 through word 7's bit 31: use umaal chain into scratch copy
        # t = (x + 19) >> 255 : run chain on copies
        e("mov r12, r1")
        for k in range(8):
            e(f"mov r2, {XR[k]}"); e("umaal r2, r12, r3, r3")
        e("lsr r2, r2, #31")            # bit 255 of x + 19  (x < 2^256 - 19)
        e("mul r12, r2, r1")            # 19 q
        for k in range(8): e(f"umaal {XR[k]}, r12, r3, r3")
        e(f"bic {XR[7]}, {XR[7]}, #0x80000000")
    e(f"ldr r1, {m(OUT)}")
    for k in range(8): e(f"str {XR[k]}, [r1, #{4*k}]")
    for i,r in enumerate(['r4','r5','r6','r7','r8','r9','r10','r11','lr']): e(f"ldr {r}, [r0, #{SAVE+4*i}]")
    e("bx lr")
print("\t.syntax unified\n\t.text\n\t.align 2")
function(sys.argv[1] if len(sys.argv)>1 else "x_new")
print("\n".join(L))
