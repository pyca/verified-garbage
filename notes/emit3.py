import sched_s as SS, emit
from emit import *
L,F,b=scalar_body(2)
SP=(lambda r,s:f"dup v{s}.2d, {r}", lambda r,s:f"umov {r}, v{s}.d[0]")
def rcimm(t,v):
    o=[];first=True
    for h in range(4):
        x=(v>>(16*h))&0xffff
        if x: o.append((f"movz" if first else "movk")+f" {t}, #{x}, lsl #{16*h}"); first=False
    return o
def sc(name,body,unroll=False,stab=True):
    emit.SPILL=SP
    o=[] if unroll else tcopy("x1","x2")
    for i,r in enumerate(CS): o.append(f"dup v{16+i}.2d, {r}")
    o+=["dup v27.2d, x0"]
    if not unroll: o+=["add x2, x1, #384","dup v29.2d, x2","dup v28.2d, x1"]
    ls=[(x,y) for y in range(5) for x in range(5)]
    for l in ls[1:]+ls[:1]:
        o.append(f"ldr {L[l]}, [x0, #{8*(l[0]+5*l[1])}]")
        if p[l]: o.append(f"ror {L[l]}, {L[l]}, #{p[l]}")
    if not unroll:
        o.append("2:")
        def iota(op):
            t,u=op[3],op[4]
            return [f"umov {t}, v28.d[0]",f"ldr {u}, [{t}, #{16*op[2]}]",f"eor {op[1]}, {op[1]}, {u}"]
        o+=sasm(body,iota)
        t,u=F[0],F[1]
        o+=[f"umov {t}, v28.d[0]",f"add {t}, {t}, #32",f"dup v28.2d, {t}",f"umov {u}, v29.d[0]",f"sub {u}, {t}, {u}",f"cbnz {u}, 2b"]
    else:
        for i in range(12):
            def iota(op): return rcimm(op[3],RCS[2*i+op[2]])+[f"eor {op[1]}, {op[1]}, {op[3]}"]
            o+=sasm(body,iota)
    o.append(f"umov {F[0]}, v27.d[0]")
    for l in ls:
        if p[l]: o.append(f"ror {L[l]}, {L[l]}, #{64-p[l]}")
        o.append(f"str {L[l]}, [{F[0]}, #{8*(l[0]+5*l[1])}]")
    for i,r in enumerate(CS): o.append(f"umov {r}, v{16+i}.d[0]")
    o.append("ret")
    return fn(name,o,A3)
c=b[0]+b[1]
def sch(w,seeds=60):
    z=min((SS.schedule(c,w,s) for s in range(seeds)),key=lambda q:q[0]); return [c[i] for i in z[1]]
V=[("a",sch(4),False),("b",sch(5),False),("c",c,True),("d",sch(4),True),("e",sch(3),False),("f",sch(6),True)]
src=open('proto.rs').read(); h=src.split('static RC')[0]+"static RC"+src.split('static RC')[1].split('#[unsafe(naked)]')[0]
h+="".join(sc(f"p_s_{n}",bd,u) for n,bd,u in V)
h+=emit.fn("p_s_z",[],A3) if 0 else ""
t="fn check() {\n"+"".join(f"    let mut s=A; let mut k=[0u64;64]; unsafe{{p_s_{n}(s.as_mut_ptr(),k.as_mut_ptr(),RC.as_ptr())}} assert_eq!(s,W);\n" for n,_,_ in V)+"}\npub fn bench(c: &mut Criterion) {\n    check();\n    let mut g = c.benchmark_group(\"proto\");\n    let mut s = [1u64; 50];\n    let mut k = [0u64; 64];\n"
t+="".join(f"    g.bench(BenchmarkId::new(VG, {400+i}), |b| b.iter(|| unsafe {{ p_s_{n}(s.as_mut_ptr(), k.as_mut_ptr(), RC.as_ptr()) }}));\n" for i,(n,_,_) in enumerate(V))
t+="    g.finish();\n}\n"
open('proto3.rs','w').write((h+t).replace('use crate::VG;','use crate::{BenchDyn, VG};').replace('#![allow(clippy::all)]\n','#![allow(clippy::all)]\n#![cfg(target_arch = "aarch64")]\n'))
