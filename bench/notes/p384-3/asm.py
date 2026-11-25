from gen import *
def txt(code):
    R=lambda n:f"x{n}"
    out=[]
    base={'a':1,'b':2,'o':0}
    for i in code:
        op,a=i[0],i[1:]
        if op in('ldr','str'):
            n,k=a[1]; br={'a':'x26','b':'x27','o':'x28','t':'x0'}[n]; out.append(f"{op} {R(a[0])}, [{br}, #{8*k}]")
        elif op=='movz': out.append(f"movz {R(a[0])}, #{a[1]}")
        elif op in('lsl','lsr'): out.append(f"{op} {R(a[0])}, {R(a[1])}, #{a[2]}")
        elif op=='extr': out.append(f"extr {R(a[0])}, {R(a[1])}, {R(a[2])}, #{a[3]}")
        elif op=='subImm': out.append(f"sub {R(a[0])}, {R(a[1])}, #{a[2]}")
        elif op=='csel': out.append(f"csel {R(a[0])}, {R(a[1])}, {R(a[2])}, cs")
        else: out.append(f"{op.rstrip('_')} "+", ".join(R(x) for x in a))
    return out
def fn(name,body):
    s=[f"core::arch::global_asm!(\".globl {name}\",\".p2align 6\",\"{name}:\","]
    pro=["stp x19,x20,[sp,#-96]!","stp x21,x22,[sp,#16]","stp x23,x24,[sp,#32]","stp x25,x26,[sp,#48]","stp x27,x28,[sp,#64]","stp x29,x30,[sp,#80]"]
    epi=["ldp x21,x22,[sp,#16]","ldp x23,x24,[sp,#32]","ldp x25,x26,[sp,#48]","ldp x27,x28,[sp,#64]","ldp x29,x30,[sp,#80]","ldp x19,x20,[sp],#96","ret"]
    for l in pro+body+epi: s.append('"'+l+'",')
    s.append(");")
    return "\n".join(s)+f"\nextern \"C\" {{ fn {name}(x: *mut u64); }}\n"
# memory at x0: t 0..47, slots from 64
def latency(kind,n=8):
    body=["add x26,x0,#64","add x27,x0,#128","add x28,x0,#64"]
    return body+txt(build(kind))*n
def indep(kind,n=8):
    body=[]
    for k in range(n): body+=[f"add x26,x0,#{64}","add x27,x0,#128",f"add x28,x0,#{192+64*k}"]+txt(build(kind))
    return body
def raw(op,n=64):
    ops={'mul':"mul x{d}, x1, x2",'umulh':"umulh x{d}, x1, x2",'mullat':"mul x3, x3, x2",'umulhlat':"umulh x3,x3,x2",'adcs':"adcs x{d}, x1, x2",'add':"add x{d}, x1, x2",'adcslat':"adcs x3,x3,x2",'extr':"extr x{d}, x1, x2, #32",'mix':None}
    if op=='mix': return ["mov x1,x0","mov x2,x0"]+[l for k in range(n//2) for l in (f"mul x{3+k%12}, x1, x2",f"umulh x{3+(k+6)%12}, x1, x2")]
    return ["mov x1,x0","mov x2,x0","mov x3,x0"]+[ops[op].format(d=3+k%12) for k in range(n)]
fns={}
for k in 'KSQ': fns[f"p_{k}_lat8"]=latency(k); fns[f"p_{k}_ind8"]=indep(k)
for o in ['mul','umulh','mullat','umulhlat','adcs','add','adcslat','extr','mix']: fns[f"p_{o}64"]=raw(o)
if __name__=='__main__':
    print("".join(fn(n,b) for n,b in fns.items()))
    print("pub static PROTOS: &[(&str, unsafe extern \"C\" fn(*mut u64))] = &[")
    for n in fns: print(f'("{n}", {n}),')
    print("];")
