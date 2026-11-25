from gen2 import *
def sasm(body,iota):
    o=[]
    for op in body:
        k=op[0]
        if k in('eor','bic'):
            o.append(f"{k} {op[1]}, {op[2]}, {op[3]}"+(f", ror #{op[4]}" if op[4] else ""))
        elif k=='spill': o.append(SPILL[0](op[1],op[2]))
        elif k=='fill': o.append(SPILL[1](op[1],op[2]))
        elif k=='iota': o+=iota(op)
    return o
def vasm(body,iota):
    o=[];q=lambda r:r+'.16b';d=lambda r:r+'.2d'
    for op in body:
        k=op[0]
        if k=='eor' or k=='bic': o.append(f"{k} {q(op[1])}, {q(op[2])}, {q(op[3])}")
        elif k=='e3': o.append("eor3 "+", ".join(map(q,op[1:])))
        elif k=='bcax': o.append("bcax "+", ".join(map(q,op[1:])))
        elif k=='rax': o.append("rax1 "+", ".join(map(d,op[1:])))
        elif k=='xar': o.append("xar "+", ".join(map(d,op[1:4]))+f", #{(64-op[4])%64}")
        elif k=='iota': o+=iota(op)
    return o
def fn(name,lines,args):
    body=",\n".join('        "'+l+'"' for l in lines)
    return f'''#[unsafe(naked)]
unsafe extern "C" fn {name}({args}) {{
    core::arch::naked_asm!(
        ".arch_extension sha3",
{body},
    )
}}
'''
def weave(a,b):
    o=[];i=j=0
    while i<len(a) and j<len(b):
        if i*len(b)<=j*len(a): o.append(a[i]);i+=1
        else: o.append(b[j]);j+=1
    return o+a[i:]+b[j:]
CS=[f'x{i}' for i in list(range(19,29))]+['x30']
out=[]
A3="a: *mut u64, b: *mut u64, rc: *const u64"
# table copy: x2 -> base [tb], 384 bytes (dup'd pairs)
def tcopy(dst,src): 
    return sum([[f"ldr q31, [{src}, #{16*i}]",f"str q31, [{dst}, #{16*i}]"] for i in range(24)],[])
# scalar
L,F,b=scalar_body(2)
SPILL=(lambda r,s:f"dup v{s}.2d, {r}", lambda r,s:f"umov {r}, v{s}.d[0]")
def scalar_fn(name,stride,off,table_in_x1):
    o=tcopy("x1","x2")
    for i,r in enumerate(CS): o.append(f"dup v{16+i}.2d, {r}")
    o+=["dup v27.2d, x0","add x2, x1, #384","dup v29.2d, x2","dup v28.2d, x1"]
    ls=[(x,y) for y in range(5) for x in range(5)]
    for l in ls[1:]+ls[:1]:
        o.append(f"ldr {L[l]}, [x0, #{stride*(l[0]+5*l[1])+off}]")
        if p[l]: o.append(f"ror {L[l]}, {L[l]}, #{p[l]}")
    o.append("2:")
    def iota(op):
        t,u=op[3],op[4]
        r=[f"umov {t}, v28.d[0]",f"ldr {u}, [{t}, #{16*op[2]}]",f"eor {op[1]}, {op[1]}, {u}"]
        if op[2]==1: r+=[f"add {t}, {t}, #32",f"dup v28.2d, {t}",f"umov {u}, v29.d[0]",f"sub {u}, {t}, {u}",f"cbnz {u}, 2b"]
        return r
    o+=sasm(b[0]+b[1],iota)
    o.append(f"umov {F[0]}, v27.d[0]")
    for l in ls:
        if p[l]: o.append(f"ror {L[l]}, {L[l]}, #{64-p[l]}")
        o.append(f"str {L[l]}, [{F[0]}, #{stride*(l[0]+5*l[1])+off}]")
    for i,r in enumerate(CS): o.append(f"umov {r}, v{16+i}.d[0]")
    o.append("ret")
    return fn(name,o,A3)
out.append(scalar_fn("p_scalar",8,0,True))
# x2
def vsave(bp): return [f"stp d{8+i}, d{9+i}, [{bp}, #{8*i}]" for i in range(0,8,2)]
def vrest(bp): return [f"ldp d{8+i}, d{9+i}, [{bp}, #{8*i}]" for i in range(0,8,2)]
def x2_fn(name,mix):
    V,vb=vec_body(mix)
    o=vsave("x1")+[f"ldr q{i}, [x0, #{16*i}]" for i in range(25)]+tcopy("x0","x2")+["mov x3, x0","mov x4, #12","2:"]
    def iota(op):
        t=op[3]
        r=[f"ldr q{t[1:]}, [x3, #{16*op[2]}]",f"eor {op[1]}.16b, {op[1]}.16b, {t}.16b"]
        return r
    o+=vasm(vb[0]+vb[1],iota)
    o+=["add x3, x3, #32","sub x4, x4, #1","cbnz x4, 2b"]+[f"str q{i}, [x0, #{16*i}]" for i in range(25)]+vrest("x1")+["ret"]
    return fn(name,o,A3)
MIX=[(0,0),(0,10),(5,0),(5,5),(5,10),(5,15),(5,25)]
for i,m in enumerate(MIX): out.append(x2_fn(f"p_x2_{i}",m))
# x3: a pair, b third, rc ; sp frame
def x3_fn(name,mix):
    global SPILL
    L3,F3,b3=scalar_body(3)
    SPILL=(lambda r,s:f"str {r}, [sp, #{16+8*s}]", lambda r,s:f"ldr {r}, [sp, #{16+8*s}]")
    V,vb=vec_body(mix)
    o=["sub sp, sp, #256"]+vsave("sp + 0" if 0 else "sp")
    o=["sub sp, sp, #256"]+[f"stp d{8+i}, d{9+i}, [sp, #{128+8*i}]" for i in range(0,8,2)]
    for i,r in enumerate(CS): o.append(f"str {r}, [sp, #{40+8*i}]")
    o+=["str x29, [sp, #136]".replace("136","200"),"str x1, [sp, #208]"]
    o+=[f"ldr q{i}, [x0, #{16*i}]" for i in range(25)]+tcopy("x0","x2")
    P,X=G[28-1+0],None
    # G has 29 regs; K=28 -> regs G[0..27]; P=G[28]=x30
    P=G[28]
    o+=[f"mov {P}, x0","str x0, [sp, #216]","mov x2, #12","str x2, [sp, #224]"]
    ls=[(x,y) for y in range(5) for x in range(5)]
    for l in [l for l in ls if L3[l]!="x1"]+[l for l in ls if L3[l]=="x1"]:
        o.append(f"ldr {L3[l]}, [x1, #{8*(l[0]+5*l[1])}]")
        if p[l]: o.append(f"ror {L3[l]}, {L3[l]}, #{p[l]}")
    o.append("2:")
    def si(op):
        return [f"ldr {op[3]}, [{P}, #{16*op[2]}]",f"eor {op[1]}, {op[1]}, {op[3]}"]
    def vi(op): return [f"ldr q{op[3][1:]}, [{P}, #{16*op[2]}]",f"eor {op[1]}.16b, {op[1]}.16b, {op[3]}.16b"]
    o+=weave(vasm(vb[0]+vb[1],vi),sasm(b3[0]+b3[1],si))
    t=F3[0]
    o+=[f"add {P}, {P}, #32",f"ldr {t}, [sp, #224]",f"sub {t}, {t}, #1",f"str {t}, [sp, #224]",f"cbnz {t}, 2b"]
    o.append(f"ldr {F3[1]}, [sp, #208]")
    for l in ls:
        if p[l]: o.append(f"ror {L3[l]}, {L3[l]}, #{64-p[l]}")
        o.append(f"str {L3[l]}, [{F3[1]}, #{8*(l[0]+5*l[1])}]")
    o+=["ldr x0, [sp, #216]"]+[f"str q{i}, [x0, #{16*i}]" for i in range(25)]
    for i,r in enumerate(CS): o.append(f"ldr {r}, [sp, #{40+8*i}]")
    o+=["ldr x29, [sp, #200]"]+[f"ldp d{8+i}, d{9+i}, [sp, #{128+8*i}]" for i in range(0,8,2)]+["add sp, sp, #256","ret"]
    return fn(name,o,A3)
X3=[(0,0),(5,5),(5,10)]
for i,m in enumerate(X3): out.append(x3_fn(f"p_x3_{i}",m))
rcs=", ".join(f"{v:#x}, {v:#x}" for v in RCS)
A=[random.getrandbits(64) for _ in range(25)];W=keccak(A)
tests="\n".join([f"    let mut s=A; let mut k=[0u64;64]; unsafe{{p_scalar(s.as_mut_ptr(),k.as_mut_ptr(),RC.as_ptr())}} assert_eq!(s,W);"]+
 [f"    let mut s=[0u64;50]; for i in 0..25 {{s[2*i]=A[i];s[2*i+1]=A[i];}} unsafe{{p_x2_{i}(s.as_mut_ptr(),k.as_mut_ptr(),RC.as_ptr())}} for i in 0..25 {{assert_eq!((s[2*i],s[2*i+1]),(W[i],W[i]),\"x2_{i}\");}}" for i in range(len(MIX))]+
 [f"    let mut s=[0u64;50]; let mut z=A; for i in 0..25 {{s[2*i]=A[i];s[2*i+1]=A[i];}} unsafe{{p_x3_{i}(s.as_mut_ptr(),z.as_mut_ptr(),RC.as_ptr())}} assert_eq!(z,W); for i in 0..25 {{assert_eq!((s[2*i],s[2*i+1]),(W[i],W[i]),\"x3_{i}\");}}" for i in range(len(X3))])
ben="\n".join([f'    g.bench(BenchmarkId::new(VG, "scalar"), |b| b.iter(|| unsafe {{ p_scalar(s.as_mut_ptr(), k.as_mut_ptr(), RC.as_ptr()) }}));']+
 [f'    g.bench(BenchmarkId::new(VG, "x2_{i}"), |b| b.iter(|| unsafe {{ p_x2_{i}(s.as_mut_ptr(), k.as_mut_ptr(), RC.as_ptr()) }}));' for i in range(len(MIX))]+
 [f'    g.bench(BenchmarkId::new(VG, "x3_{i}"), |b| b.iter(|| unsafe {{ p_x3_{i}(s.as_mut_ptr(), k.as_mut_ptr(), RC.as_ptr()) }}));' for i in range(len(X3))])
src_=f'''// Prototype, speed only.
#![allow(clippy::all)]
use criterion::{{BenchmarkId, Criterion}};
use crate::VG;
static RC: [u64; 48] = [{rcs}];
static A: [u64; 25] = {A};
static W: [u64; 25] = {W};
{"".join(out)}
fn check() {{
{tests}
}}
pub fn bench(c: &mut Criterion) {{
    check();
    let mut g = c.benchmark_group("proto");
    let mut s = [1u64; 50];
    let mut k = [0u64; 64];
{ben}
    g.finish();
}}
'''
src_=src_.replace("p_x3_0(s.as_mut_ptr(), k.as_mut_ptr()","p_x3_0(s.as_mut_ptr(), k.as_mut_ptr()")
open('proto.rs','w').write(src_)
