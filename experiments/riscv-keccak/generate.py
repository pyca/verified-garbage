#!/usr/bin/env python3
"""Unproven C experiments. Read the Lean schedule; never alter generated crates."""
import re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'experiments/riscv-keccak/out'
OUT.mkdir(exist_ok=True)
s=(ROOT/'lean/VerifiedGarbage/Impl/Sha3/RISCV64.lean').read_text()
def instructions(name,end):
 t=s[s.index('def '+name+' '):s.index(end,s.index('def '+name+' '))]
 t=re.sub(r'--[^\n]*','',t)
 return [(m[1],m[2].split()) for m in re.finditer(r'\b(ld|xl|st|mv|xr|an|orr|rol|nt)\s+([^,\]\n]+)',t)]
A=instructions('roundA','/-- The rest')
B=instructions('roundB','/-- ι')
assert len(A)==48 and len(B)==144,(len(A),len(B))
RC=[0x1,0x8082,0x800000000000808a,0x8000000080008000,0x808b,0x80000001,0x8000000080008081,0x8000000000008009,0x8a,0x88,0x80008009,0x8000000a,0x8000808b,0x800000000000008b,0x8000000000008089,0x8000000000008003,0x8000000000008002,0x8000000000000080,0x800a,0x800000008000000a,0x8000000080008081,0x8000000000008080,0x80000001,0x8000000080008008]
variants={'memory':[], 'row0':[0,1,2,3,4], 'row1':[5,6,7,8,9], 'row2':[10,11,12,13,14], 'row3':[15,16,17,18,19], 'cache2':[2,8], 'cache4':[2,8,14,15], 'cache5':[1,2,8,14,15]}
reg=lambda r:'r_'+r.lstrip('.')
variants.update({"v_"+name:cache for name,cache in list(variants.items())})
variants.update({"f_"+name:cache for name,cache in list(variants.items()) if not name.startswith("v_")})
variants['f_parity']=[]
def core(name,cache):
 lines=[f'__attribute__((noinline)) void core_{name}(uint64_t *restrict a, uint64_t *restrict b, const uint64_t *restrict rc) {{',
 'uint64_t '+','.join('r_'+r for r in ['a2','a3','a4','a5','a6','a7','t0','t1','t2','t3','t4','t5'])+';']
 if name=='f_parity':lines += ['uint64_t '+','.join(f'p{x}='+ '^'.join(f'a[{x+5*y}]' for y in range(5)) for x in range(5))+';']
 for bank in ['a','b']:
  for i in cache:lines.append(f'uint64_t c_{bank}_{i}'+(f'={bank}[{i}]' if bank=='a' else '')+';')
 lines+=['r_a2=a[20];r_a3=a[21];r_a4=a[22];r_a5=a[23];r_a6=a[24];','for(unsigned k=0;k<24;k+=2){']
 def mem(bank,i):return f'c_{bank}_{i}' if int(i) in cache else f'{bank}[{i}]'
 def emit(ops,src,dst):
  for op,args in ops:
   if op in ('ld','xl'):
    r,_,i=args;lines.append(f'{reg(r)} {"=" if op=="ld" else "^="} {mem(src,i)};')
   elif op=='st':
    _,i,r=args;lines.append(f'{mem(dst,i)}={reg(r)};')
    if name=='f_parity':lines.append(f'p{int(i)%5} '+('=' if int(i)<5 else '^=')+f' {reg(r)};')
   elif op=='nt':lines.append(f'{reg(args[0])}=~{reg(args[0])};')
   elif op=='rol':lines.append(f'{reg(args[0])}=rol64({reg(args[0])},{args[1]});')
   else:
    r,q=args;lines.append(f'{reg(r)} '+{'mv':'=','xr':'^=','an':'&=','orr':'|='}[op]+f' {reg(q)};')
 def first(src,dst):
  if name=='f_parity':
   emit(A[:4]+[A[10]],src,dst)
   lines.extend(f'r_a{x+2}=p{y};' for x,y in enumerate([0,1,2,3,4]))
   emit([op for i,op in enumerate(A) if i>=22 and i not in (25,28,31)],src,dst)
  else:emit(A,src,dst)
 first('a','b');lines.append('r_t0 ^= rc[k];');emit(B,'a','b')
 first('b','a');lines.append('r_t0 ^= rc[k+1];');emit(B,'b','a')
 lines+=['}']+[f'a[{i}]=c_a_{i};' for i in cache]+['}']
 text='\n'.join(lines)
 if name.startswith(('v_', 'f_')):text=text.replace('uint64_t *restrict a, uint64_t *restrict b','volatile uint64_t *restrict a, volatile uint64_t *restrict b')
 if name.startswith('f_'):
  text=text.replace('__attribute__((noinline)) void', 'static __attribute__((always_inline)) inline void')
  text=text.replace('for(unsigned k=0;k<24;k+=2){', 'for(const uint64_t *p=rc;p<(const uint64_t *)a;p+=2){').replace('rc[k+1]', 'p[1]').replace('rc[k]', 'p[0]')
 return text
# An independent canonical implementation with named scalar state, an in-place
# rho/pi cycle and row-wise chi; GCC chooses its own register allocation.
rot=[1,3,6,10,15,21,28,36,45,55,2,14,27,41,56,8,25,43,62,18,39,61,20,44]
pi=[10,7,11,17,18,3,5,16,8,21,24,4,15,23,19,13,12,2,20,14,22,9,6,1]
def scalar(unroll):
 lines=[f'__attribute__((noinline)) void core_scalar{unroll}(uint64_t *restrict a,uint64_t *restrict b,const uint64_t *restrict rc){{','(void)b;']
 lines += [f'uint64_t v{i}=a[{i}];' for i in range(25)]
 lines += [f'for(unsigned k=0;k<24;k+={unroll}){{']
 for u in range(unroll):
  lines+=['{uint64_t '+','.join(f'c{x}='+ '^'.join(f'v{x+5*y}' for y in range(5)) for x in range(5))+';uint64_t d,t,p;']
  for x in range(5):
   lines += [f'd=c{(x+4)%5}^rol64(c{(x+1)%5},1);']+[f'v{x+5*y}^=d;' for y in range(5)]
  lines+=['t=v1;']
  for i,r in zip(pi,rot):lines+=[f'p=v{i};v{i}=rol64(t,{r});t=p;']
  for y in range(5):
   i=5*y;lines += [f't=v{i};p=v{i+1};',f'v{i}^=(~v{i+1})&v{i+2};',f'v{i+1}^=(~v{i+2})&v{i+3};',f'v{i+2}^=(~v{i+3})&v{i+4};',f'v{i+3}^=(~v{i+4})&t;',f'v{i+4}^=(~t)&p;']
  lines += [f'v0^=rc[k+{u}];','}']
 lines += ['}']+[f'a[{i}]=v{i};' for i in range(25)]+['}']
 return '\n'.join(lines)
code=['#include "probe.h"','static inline uint64_t rol64(uint64_t x,unsigned n){return (x<<n)|(x>>(64-n));}']
code += [core(name,c) for name,c in variants.items()]
code += [scalar(n) for n in (1,2,4)]
code += ['void fill_round_constants(uint64_t *);']
for name in [*variants,'scalar1','scalar2','scalar4']:
 comp=not name.startswith('scalar')
 fused=name.startswith('f_')
 attr='__attribute__((no_stack_protector)) ' if fused else ''
 buffers='uint64_t frame[74],*rc=frame,*a=frame+24,*b=frame+49;' if fused else 'uint64_t a[25],b[25],rc[24];'
 code += [f'{attr}void candidate_{name}(void *state,void *scratch){{{buffers}(void)scratch;']
 if fused:
  code += ['if(!((uintptr_t)state&7)){const unsigned char *in=__builtin_assume_aligned(state,8);']
  code += [f'__builtin_memcpy(a+{i},in+{8*i},8);' for i in range(25)]
  code += ['}else memcpy(a,state,200);']
 else:code += ['memcpy(a,state,200);']
 code += ['fill_round_constants(rc);']
 if comp:code += [f'a[{i}]=~a[{i}];' for i in (1,2,8,12,17,20)]
 code += [f'core_{name}(a,b,rc);']
 if comp:code += [f'a[{i}]=~a[{i}];' for i in (1,2,8,12,17,20)]
 if fused:
  code += ['if(!((uintptr_t)state&7)){unsigned char *out=__builtin_assume_aligned(state,8);']
  code += [f'__builtin_memcpy(out+{8*i},a+{i},8);' for i in range(25)]
  code += ['}else memcpy(state,a,200);}']
 else:code += ['memcpy(state,a,200);}']
(OUT/'candidates.c').write_text('\n'.join(code)+'\n')
(OUT/'constants.c').write_text('#include <stdint.h>\n#include <string.h>\nvoid fill_round_constants(uint64_t *out){static const uint64_t rc[24]={'+','.join(hex(v)+'ULL' for v in RC)+'};memcpy(out,rc,sizeof(rc));}\n')
# These are only ELF/linkage directives and name substitutions around the exact
# Lean-emitted text. Every executable assembly instruction remains unchanged.
ASM=ROOT/'crates/verified-garbage-asm-riscv64/assembly'
files=list(ASM.rglob('*.s'))
by_name={}
for f in files:
 for name in re.findall(r'^(vg_\w+):',f.read_text(),re.M):by_name[name]=f
roots=['vg_keccak_f1600','vg_shake128_update','vg_shake128_finalize','vg_shake128_squeeze','vg_sha3_256_update','vg_shake256_finalize','vg_shake256_squeeze','vg_mlkem768_keygen','vg_mlkem768_encaps','vg_mlkem768_decaps','vg_mldsa65_keygen','vg_mldsa65_sign','vg_mldsa65_verify']
queue=[by_name[n] for n in roots];seen=set()
while queue:
 f=queue.pop()
 if f in seen:continue
 seen.add(f)
 text=f.read_text()
 deps=re.findall(r'\bcall \{(vg_\w+)\}',text)
 for n in deps:
  assert n in by_name,(n,f)
  queue.append(by_name[n])
 names=re.findall(r'^(vg_\w+):',text,re.M)
 text=re.sub(r'\{(vg_\w+)\}',r'\1',text)
 assert '{' not in text, f
 directives='.text\n'+''.join(f'.globl {n}\n.type {n}, @function\n' for n in names)
 (OUT/(f.stem+'.S')).write_text(directives+text)
(OUT/'asm-files.txt').write_text('\n'.join(str(OUT/(f.stem+'.S')) for f in sorted(seen))+'\n')
print(f'generated {len(variants)+3} C candidates and {len(seen)} unchanged Lean assembly files')
