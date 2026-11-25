import sched as S, emit
from emit import *
def body_sched(mix,seeds=200):
    V,b=vec_body(mix); c=b[0]+b[1]
    best=min((S.schedule(c,seed=s) for s in range(seeds)),key=lambda z:z[0])
    return best[0],[c[i] for i in best[1]]
CFG=[(0,0),(3,8),(3,10),(2,10),(5,8),(0,12)]
SB=[body_sched(m) for m in CFG]
print([x[0] for x in SB])
def x2f(name,body):
    o=vsave("x1")+[f"ldr q{i}, [x0, #{16*i}]" for i in range(25)]+tcopy("x0","x2")+["mov x3, x0","mov x4, #12","2:"]
    iota=lambda op:[f"ldr q{op[3][1:]}, [x3, #{16*op[2]}]",f"eor {op[1]}.16b, {op[1]}.16b, {op[3]}.16b"]
    o+=vasm(body,iota)
    o+=["add x3, x3, #32","sub x4, x4, #1","cbnz x4, 2b"]+[f"str q{i}, [x0, #{16*i}]" for i in range(25)]+vrest("x1")+["ret"]
    return fn(name,o,A3)
src=open('proto.rs').read()
h,t=src.split('fn check() {',1)
h+="".join(x2f(f"p_x2s_{i}",b) for i,(c,b) in enumerate(SB))
# x3 with scheduled vector
import types
def x3s(name,body):
    old=emit.vec_body
    emit.vec_body=lambda m:(None,[body,[]])
    r=emit.x3_fn(name,None); emit.vec_body=old; return r
h+="".join(x3s(f"p_x3s_{i}",b) for i,(c,b) in enumerate(SB))
chk=""
for i in range(len(CFG)):
    chk+=f"    let mut s=[0u64;50]; let mut k=[0u64;64]; for i in 0..25 {{s[2*i]=A[i];s[2*i+1]=A[i];}} unsafe{{p_x2s_{i}(s.as_mut_ptr(),k.as_mut_ptr(),RC.as_ptr())}} for i in 0..25 {{assert_eq!((s[2*i],s[2*i+1]),(W[i],W[i]));}}\n"
    chk+=f"    let mut s=[0u64;50]; let mut z=A; for i in 0..25 {{s[2*i]=A[i];s[2*i+1]=A[i];}} unsafe{{p_x3s_{i}(s.as_mut_ptr(),z.as_mut_ptr(),RC.as_ptr())}} assert_eq!(z,W); for i in 0..25 {{assert_eq!((s[2*i],s[2*i+1]),(W[i],W[i]));}}\n"
t=chk+t
b="".join(f"    g.bench(BenchmarkId::new(VG, {200+i}), |b| b.iter(|| unsafe {{ p_x2s_{i}(s.as_mut_ptr(), k.as_mut_ptr(), RC.as_ptr()) }}));\n    g.bench(BenchmarkId::new(VG, {300+i}), |b| b.iter(|| unsafe {{ p_x3s_{i}(s.as_mut_ptr(), k.as_mut_ptr(), RC.as_ptr()) }}));\n" for i in range(len(CFG)))
olds=[("ed448","vg_keccak_f1600",901),("ed448","vg_keccak_f1600_sha3",902),("mldsa44","vg_keccak_f1600_x2",903),("mldsa44","vg_keccak_f1600_x2_sha3",904),("mlkem1024","vg_keccak_f1600_x3",905),("mlkem1024","vg_keccak_f1600_x3_sha3",906)]
for m,f,n in olds:
    b+=f"    {{ type F = unsafe extern \"C\" fn(*mut u64, *mut u64, *mut u64); let f: F = unsafe {{ core::mem::transmute(verified_garbage_asm_aarch64::{m}::bench_{f}()) }}; let mut scr=[0u64;64]; g.bench(BenchmarkId::new(VG, {n}), |b| b.iter(|| unsafe {{ f(s.as_mut_ptr(), k.as_mut_ptr(), scr.as_mut_ptr()) }})); }}\n"


t=t.replace("    g.finish();",b+"    g.finish();")
out=(h+'fn check() {'+t).replace('use crate::VG;','use crate::{BenchDyn, VG};').replace('"scalar"','1').replace('#![allow(clippy::all)]\n','#![allow(clippy::all)]\n#![cfg(target_arch = "aarch64")]\n')
import re
out=re.sub(r'BenchmarkId::new\(VG, "x(\d)_(\d)"\)',r'BenchmarkId::new(VG, 1\1\2)',out)
open('proto2.rs','w').write(out)
