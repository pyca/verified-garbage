# generates proto.s: my linear ops & doubling, calling the black-box product
R=['rax','rcx','r8','r9','r10','r11','r12','r13','r14']  # chain regs: one at a time through rax suffices
out=[]
e=out.append

HELD=[None]
def m(d): return f"[rdi+{d}]"
REG=['rbp','r8','r9','r10','r11','r12','r13','r14','r15']
def st(o):
    for i,r in enumerate(REG): e(f"mov {m(o+8*i)},{r}")
def hi():
    e("mov rax,r15"); e("shr rax,9"); e("and r15d,511"); e("add rbp,rax")
def fold1():
    hi()
    for r in REG[1:]: e(f"adc {r},0")
def fold(): fold1(); hi()
def call(o,a,b,weak):
    if a==b: e("movq xmm7,rbx"); e("mov rbx,rdi"); e(f"add rbx,{a}"); e("call SQRR")
    else: e("movq xmm7,rbx"); e("movq xmm6,rsi"); e("mov rsi,rdi"); e(f"add rsi,{a}"); e("mov rbx,rdi"); e(f"add rbx,{b}"); e("call MULR")
    if weak: fold1()
    st(o); e("movq rbx,xmm7")
    if a!=b: e("movq rsi,xmm6")
FUSE=[True]
def ld(o):
    if FUSE[0] and HELD[0]==o: return
    for i,r in enumerate(REG): e(f"mov {r},{m(o+8*i)}")
def nots():
    for r in REG: e(f"xor {r},-1")
def chain(b):
    for i,r in enumerate(REG): e(f"{'add' if i==0 else 'adc'} {r},{m(b+8*i)}")
def dblc():
    for i,r in enumerate(REG): e(f"{'add' if i==0 else 'adc'} {r},{r}")
def add(o,a,b): ld(a); (dblc() if a==b else chain(b)); st(o)
def sub(o,a,b): ld(b); nots(); chain(a); e("add r15,512"); st(o)
def tri(o,a): ld(a); dblc(); chain(a); st(o)
def x3(o,a,s): ld(s); nots(); dblc(); chain(a); e("add r15,1024"); fold(); st(o)
def subf(o,a,b): ld(b); nots(); chain(a); e("add r15,512"); fold(); st(o)
def subhalf(o,a,b): # a + (p - b/2): half = rot right 1
    # regs: b>>1 with bit0 to bit 520
    e(f"mov rcx,{m(b)}"); e("mov rdx,rcx"); e("and edx,1"); e("shl rdx,8")
    for i in range(9):
        r=REG[i]
        if i<8:
            e(f"mov {r},{m(b+8*(i+1))}")
            e(f"shrd rcx,{r},1"); e("mov rax,rcx"); e(f"mov rcx,{r}"); e(f"mov {r},rax")
        else:
            e("shr rcx,1"); e("or rcx,rdx"); e(f"mov {r},rcx")
    for i,r in enumerate(REG):
        e(f"not {r}")
    for i,r in enumerate(REG):
        e(f"{'add' if i==0 else 'adc'} {r},{m(a+8*i)}")
    e("add r15,512"); fold(); st(o)
def dbl():
    pass
e(".intel_syntax noprefix"); e(".text")
def fn(name,body):
    e(f".globl {name}"); e(f"{name}:")
    for r in ['rbx','rbp','r12','r13','r14','r15']: e("push "+r)
    e("sub rsp,8")
    e("movq xmm9,rsi"); e("mov rbx,rsi"); e("1:")
    body()
    e("sub rbx,1"); e("jnz 1b"); e("add rsp,8")
    for r in ['r15','r14','r13','r12','rbp','rbx']: e("pop "+r)
    e("ret")
fn("p_dbl",dbl)
fn("p_mul",lambda: call(T0,X,Y))
fn("p_mulc",lambda: call(T0,T0,Y))
fn("p_sqr",lambda: call(T0,T0,T0))
fn("p_add",lambda: add(T0,T0,Y))
fn("p_x3",lambda: x3(T0,T0,Y))
fn("p_lin",lambda: (add(U,Y,Y),sub(T3,X,T0),add(T2,X,T0),tri(T3,T3),x3(X,T0,T2),sub(T2,T2,X),subhalf(Y,T2,T1)))
fn("p_muls",lambda: (call(T0,Z,Z),call(T1,U,U),call(Z,U,Z),call(T3,T3,T2),call(T2,X,T1),call(T0,T3,T3),call(T1,T1,T1),call(T2,T3,T2)))
open("proto.s","w").write("\n".join(out)+"\n")
