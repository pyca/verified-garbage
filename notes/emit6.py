import sched as S, emit, explicit
from emit import *
from emit3 import rcimm
def body_sched(mix,seeds=150):
    V,b=vec_body(mix); c=b[0]+b[1]
    best=min((S.schedule(c,seed=s) for s in range(seeds)),key=lambda z:z[0]); return [c[i] for i in best[1]]
def sasm2(body,iota):
    o=[]
    for op in body:
        if op[0]=='ror': o.append(f"ror {op[1]}, {op[2]}, #{op[3]}")
        else: o+=sasm([op],iota)
    return o
def x2f(name,body):
    o=vsave("x1")+[f"ldr q{i}, [x0, #{16*i}]" for i in range(25)]+tcopy("x0","x2")+["mov x3, x0","mov x4, #12","2:"]
    iota=lambda op:[f"ldr q{op[3][1:]}, [x3, #{16*op[2]}]",f"eor {op[1]}.16b, {op[1]}.16b, {op[3]}.16b"]
    o+=vasm(body,iota)
    o+=["add x3, x3, #32","sub x4, x4, #1","cbnz x4, 2b"]+[f"str q{i}, [x0, #{16*i}]" for i in range(25)]+vrest("x1")+["ret"]
    return fn(name,o,A3)
def x3f(name,vbody):
    L3,F3,b3=explicit.xbody(3)
    emit.SPILL=(lambda r,s:f"str {r}, [sp, #{16+8*s}]", lambda r,s:f"ldr {r}, [sp, #{16+8*s}]")
    o=["sub sp, sp, #256"]+[f"stp d{8+i}, d{9+i}, [sp, #{128+8*i}]" for i in range(0,8,2)]
    for i,r in enumerate(CS): o.append(f"str {r}, [sp, #{40+8*i}]")
    o+=["str x29, [sp, #200]","str x1, [sp, #208]"]+[f"ldr q{i}, [x0, #{16*i}]" for i in range(25)]+tcopy("x0","x2")
    P="x30"; o+=[f"mov {P}, x0","str x0, [sp, #216]","mov x2, #12","str x2, [sp, #224]"]
    ls=[(x,y) for y in range(5) for x in range(5)]
    for l in [l for l in ls if L3[l]!="x1"]+[l for l in ls if L3[l]=="x1"]: o.append(f"ldr {L3[l]}, [x1, #{8*(l[0]+5*l[1])}]")
    o.append("2:")
    si=lambda op:[f"ldr {op[3]}, [{P}, #{16*op[2]}]",f"eor {op[1]}, {op[1]}, {op[3]}"]
    vi=lambda op:[f"ldr q{op[3][1:]}, [{P}, #{16*op[2]}]",f"eor {op[1]}.16b, {op[1]}.16b, {op[3]}.16b"]
    o+=weave(vasm(vbody,vi),sasm2(b3[0]+b3[1],si))
    t=F3[0]
    o+=[f"add {P}, {P}, #32",f"ldr {t}, [sp, #224]",f"sub {t}, {t}, #1",f"str {t}, [sp, #224]",f"cbnz {t}, 2b",f"ldr {F3[1]}, [sp, #208]"]
    for l in ls: o.append(f"str {L3[l]}, [{F3[1]}, #{8*(l[0]+5*l[1])}]")
    o+=["ldr x0, [sp, #216]"]+[f"str q{i}, [x0, #{16*i}]" for i in range(25)]
    for i,r in enumerate(CS): o.append(f"ldr {r}, [sp, #{40+8*i}]")
    o+=["ldr x29, [sp, #200]"]+[f"ldp d{8+i}, d{9+i}, [sp, #{128+8*i}]" for i in range(0,8,2)]+["add sp, sp, #256","ret"]
    return fn(name,o,A3)
def scal(name,nsp,mode,unroll):
    L,F,b=scalar_body(nsp); o=[]
    ls=[(x,y) for y in range(5) for x in range(5)]
    for i,r in enumerate(CS): o.append(f"dup v{16+i}.2d, {r}")
    o+=["dup v27.2d, x0"]
    if mode in('scr','loop'): # P=x30=scratch; table at [P+64..]; slots [P..]
        o+=sum([[f"ldr q31, [x2, #{16*i}]",f"str q31, [x1, #{64+16*i}]"] for i in range(12)],[])
        o+=["mov x30, x1"]
    if mode=='loop': o+=["add x2, x1, #192","dup v29.2d, x2"]
    if mode=='tbl': o+=["dup v28.2d, x2"]
    if nsp==2: emit.SPILL=(lambda r,s:f"dup v{s}.2d, {r}", lambda r,s:f"umov {r}, v{s}.d[0]")
    else: emit.SPILL=(lambda r,s:f"str {r}, [x30, #{8*s}]", lambda r,s:f"ldr {r}, [x30, #{8*s}]")
    for l in ls[1:]+ls[:1]:
        o.append(f"ldr {L[l]}, [x0, #{8*(l[0]+5*l[1])}]")
        if p[l]: o.append(f"ror {L[l]}, {L[l]}, #{p[l]}")
    if mode=='loop':
        o.append("2:")
        o+=sasm(b[0]+b[1],lambda op:[f"ldr {op[3]}, [x30, #{64+8*op[2]}]",f"eor {op[1]}, {op[1]}, {op[3]}"])
        o+=["add x30, x30, #16",f"umov {F[0]}, v29.d[0]",f"sub {F[0]}, x30, {F[0]}",f"cbnz {F[0]}, 2b"]
    else:
        for i in range(12):
            if mode=='scr': io=lambda op:[f"ldr {op[3]}, [x30, #{64+8*(2*i+op[2])}]",f"eor {op[1]}, {op[1]}, {op[3]}"]
            elif mode=='tbl': io=lambda op:[f"umov {op[3]}, v28.d[0]",f"ldr {op[3]}, [{op[3]}, #{8*(2*i+op[2])}]",f"eor {op[1]}, {op[1]}, {op[3]}"]
            else: io=lambda op:rcimm(op[3],RCS[2*i+op[2]])+[f"eor {op[1]}, {op[1]}, {op[3]}"]
            o+=sasm(b[0]+b[1],io)
    o.append(f"umov {F[0]}, v27.d[0]")
    for l in ls:
        if p[l]: o.append(f"ror {L[l]}, {L[l]}, #{64-p[l]}")
        o.append(f"str {L[l]}, [{F[0]}, #{8*(l[0]+5*l[1])}]")
    for i,r in enumerate(CS): o.append(f"umov {r}, v{16+i}.d[0]")
    o.append("ret"); return fn(name,o,A3)
MX=[((0,0),0),((2,8),1),((2,8),0),((0,8),1),((0,4),1),((2,0),1)]
items=[];fs=""
for i,(m,sc) in enumerate(MX):
    if sc: bd=body_sched(m)
    else: V,bb=vec_body(m); bd=bb[0]+bb[1]
    fs+=x2f(f"p_x2_{i}",bd)+x3f(f"p_x3_{i}",bd); items+=[(f"p_x2_{i}",200+i,2),(f"p_x3_{i}",300+i,3)]
rc1=", ".join(f"{v:#x}" for v in RCS); rc2=", ".join(f"{v:#x}, {v:#x}" for v in RCS)
A=[random.getrandbits(64) for _ in range(25)];W=keccak(A)
tst="";ben=""
for f,n,k in items:
    rc="RC1" if k==1 else "RC"
    if k==1: tst+=f"    let mut s=A; let mut k=[0u64;64]; unsafe{{{f}(s.as_mut_ptr(),k.as_mut_ptr(),RC1.as_ptr())}} assert_eq!(s,W,\"{f}\");\n"
    else: tst+=f"    let mut s=[0u64;50]; let mut z=[0u64;64]; z[..25].copy_from_slice(&A); for i in 0..25 {{s[2*i]=A[i];s[2*i+1]=A[i];}} unsafe{{{f}(s.as_mut_ptr(),z.as_mut_ptr(),RC.as_ptr())}} for i in 0..25 {{assert_eq!((s[2*i],s[2*i+1]),(W[i],W[i]),\"{f}\");}}\n"
    for rep in (0,1):
        ben+=f"    g.bench(BenchmarkId::new(VG, {n+1000*rep}), |b| b.iter(|| unsafe {{ {f}(s.as_mut_ptr(), k.as_mut_ptr(), {rc}.as_ptr()) }}));\n"
olds=[("ed448","vg_keccak_f1600",901),("ed448","vg_keccak_f1600_sha3",902),("mldsa44","vg_keccak_f1600_x2_sha3",904),("mlkem1024","vg_keccak_f1600_x3_sha3",906)]
for m,f,n in olds:
    for rep in (0,1):
        ben+=f"    {{ type F = unsafe extern \"C\" fn(*mut u64, *mut u64, *mut u64); let f: F = unsafe {{ core::mem::transmute(verified_garbage_asm_aarch64::{m}::bench_{f}()) }}; let mut scr=[0u64;64]; g.bench(BenchmarkId::new(VG, {n+1000*rep}), |b| b.iter(|| unsafe {{ f(s.as_mut_ptr(), k.as_mut_ptr(), scr.as_mut_ptr()) }})); }}\n"
open('proto6.rs','w').write(f'''// Prototype, speed only.
#![allow(clippy::all)]
#![cfg(target_arch = "aarch64")]
use criterion::{{BenchmarkId, Criterion}};
use crate::{{BenchDyn, VG}};
static RC: [u64; 48] = [{rc2}];
static RC1: [u64; 24] = [{rc1}];
static A: [u64; 25] = {A};
static W: [u64; 25] = {W};
{fs}
fn check() {{
{tst}
}}
pub fn bench(c: &mut Criterion) {{
    check();
    let mut g = c.benchmark_group("proto");
    let mut s = [1u64; 50];
    let mut k = [0u64; 64];
{ben}
    g.finish();
}}
''')
