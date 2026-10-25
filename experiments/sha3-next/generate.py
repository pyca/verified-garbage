from pathlib import Path
import re
root=Path('/tmp/vg-sha3-next')
s=Path('/tmp/vg-sha3-hillclimb/scalar-ops.txt').read_text()
chunks=[x for x in re.split(r'(?=VG.Impl.Sha3.AArch64.Scalar.ScalarOp\.)',s) if x.strip()]
core=[]
for text in chunks:
 kind=re.search(r'ScalarOp\.(\w+)',text)[1]
 regs=[int(x) for x in re.findall(r'Reg\.x(\d+)',text)]
 nums=re.findall(r'(?<!\w)(\d+)(?!\w)',re.sub(r'\([^)]*\)','',text.split(kind,1)[1]))
 core.append((kind,regs,int(nums[-1]) if nums else 0))

# (root, offset): physical root = logical value rotated right by offset.
state_regs=list(range(18))+[25]+list(range(19,25))
vals={r:(r,0) for r in state_regs};nodes=[];nextid=31;slots={}
def emit(kind,args,aux=0,offset=0):
 global nextid
 rid=nextid;nextid+=1;nodes.append((rid,kind,args,aux));return rid,offset
for r in range(24):
 for kind,regs,num in core:
  if kind in ('move','ror'):
   d,a=regs;rootid,o=vals[a];vals[d]=(rootid,(o-(num if kind=='ror' else 0))%64)
  elif kind=='spill':
   # temporary vector store retains the current orientation
   a=regs[0];slots[num]=emit('spill',[vals[a]],num,vals[a][1])
  elif kind=='reload':
   vals[regs[0]]=emit('reload',[slots[num]],num,slots[num][1])
  else:
   d,a,b=regs;av,bv=vals[a],vals[b]
   k=(av[1]+(num if kind.endswith('Ror') else 0)-bv[1])%64
   vals[d]=emit('bic' if kind.startswith('bic') else 'xor',[av,bv],k,av[1])
 vals[26]=emit('const',[],r)
 av,bv=vals[0],vals[26];vals[0]=emit('xor',[av,bv],(av[1]-bv[1])%64,av[1])
last={}
for i,(rid,kind,args,aux) in enumerate(nodes):
 for arg,_ in args:last[arg]=i
for r in state_regs:last[vals[r][0]]=len(nodes)
free=set(range(31))-{18,29};physical={r:r for r in state_regs};free-=set(physical.values());instructions=[]
for i,(rid,kind,args,aux) in enumerate(nodes):
 prs=[physical[a] for a,_ in args]
 for a,_ in args:
  if last[a]==i and a in physical:
   p=physical.pop(a)
   if isinstance(p,int):free.add(p)
 if kind=='spill':
  instructions.append(f'.vop (.dup .d2 .v{24+aux} .x{prs[0]})');physical[rid]=f'v{24+aux}'
 elif kind=='reload':
  assert free,(i,kind)
  p=min(free);free.remove(p);physical[rid]=p
  instructions.append(f'.umov .x .x{p} .{prs[0]} 0')
 else:
  assert free,(i,kind,len(physical))
  p=next((q for q in prs if q in free),min(free));free.remove(p);physical[rid]=p
  if kind=='const':
   instructions.append(f'CONST:{p}:{aux}')
  else:
   a,b=prs
   instructions.append(f'.bicRor .x .x{p} .x{a} .x{b} {aux}' if kind=='bic' else f'.logicRor .eor .x .x{p} .x{a} .x{b} {aux}')
# Store directly to original state pointer saved in v16 by scalar boundary.
# Easier normalize result with stack array then existing scalar finish via load.
# Normalize the final layout using a parallel copy, keeping the 25 lanes in GPRs.
tmp=min(free)
remaining={r:(physical[vals[r][0]],(64-vals[r][1])%64) for r in state_regs}
while remaining:
 sources={p for p,_ in remaining.values()}
 choices=[r for r in remaining if r not in sources or remaining[r][0]==r]
 if choices:
  d=choices[0];p,o=remaining.pop(d)
  if o:instructions.append(f'.ror .x .x{d} .x{p} {o}')
  elif d!=p:instructions.append(f'.addImm .x .x{d} .x{p} 0')
 else:
  p=next(iter(remaining.values()))[0]
  instructions.append(f'.addImm .x .x{tmp} .x{p} 0')
  remaining={d:((tmp if src==p else src),o) for d,(src,o) in remaining.items()}
print(len(nodes),len(instructions),'instructions')
(root/'lazy-instrs.txt').write_text('\n'.join(instructions))

header="""import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Resident
import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector.Boundary
import VerifiedGarbage.TCB.AArch64.Print
open VG VG.AArch64
namespace Lazy
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def constant (d : Reg) (r : Nat) : List Instr :=
 let v := VG.Spec.Sha3.RC r
 [.movz .x d (v.extractLsb' 0 16) 0] ++
 (if v.extractLsb' 16 16 = 0 then [] else [.movk .x d (v.extractLsb' 16 16) 1]) ++
 (if v.extractLsb' 32 16 = 0 then [] else [.movk .x d (v.extractLsb' 32 16) 2]) ++
 (if v.extractLsb' 48 16 = 0 then [] else [.movk .x d (v.extractLsb' 48 16) 3])
def body : List Instr :=
"""
parts=[];chunk=[]
for instruction in instructions:
 if instruction.startswith('CONST:'):
  if chunk: parts.append('['+','.join(chunk)+']');chunk=[]
  _,p,r=instruction.split(':');parts.append(f'constant .x{p} {r}')
 else:chunk.append(instruction)
if chunk:parts.append('['+','.join(chunk)+']')
header=header.removesuffix('def body : List Instr :=\n')
for i,part in enumerate(parts):header+=f'def chunk{i} : List Instr := '+part+'\n'
header+='def body : List Instr := ['+','.join(f'chunk{i}' for i in range(len(parts)))+'].flatten\n'
header+="""def variants : List (String × Prog isa) :=
 [("scalar", VG.Impl.Sha3.AArch64.Scalar.unrolledPermute),
 ("lazy",.block (VG.Impl.Sha3.AArch64.Scalar.Boundary.save ++ VG.Impl.Sha3.AArch64.Scalar.Boundary.load ++ body ++ VG.Impl.Sha3.AArch64.Scalar.Boundary.store ++ VG.Impl.Sha3.AArch64.Scalar.Boundary.restore))]
def bulks : List (String × Prog isa) :=
 [("bulk_scalar",VG.Impl.Sha3.AArch64.Scalar.Resident.bulk),
 ("bulk_lazy",.seq (.block VG.Impl.Sha3.AArch64.Scalar.Resident.setup)
  (.seq (.loop (.seq VG.Impl.Sha3.AArch64.Scalar.Resident.xorBlock
    (.block (body ++ VG.Impl.Sha3.AArch64.Scalar.Resident.advance))) (.zero .x .x26))
    (.block VG.Impl.Sha3.AArch64.Scalar.Resident.finish)))]
def main : IO Unit := do
 for apple in [true,false] do
  let symPrefix := if apple then "_" else ""
  let mut result := ".text\\n"
  for (name,body) in variants ++ bulks do
   let symbol := symPrefix ++ "trial_" ++ name
   result := result ++ ".p2align 6\\n.globl " ++ symbol ++ "\\n" ++ symbol ++ ":\\n" ++ String.intercalate "\\n" ((printer.function body).map fun l => match l with
    | .text s => s | _ => "UNEXPECTED") ++ "\\n"
  IO.FS.writeFile ("/tmp/vg-sha3-next/lazy-" ++ (if apple then "apple" else "linux") ++ ".S") result
 IO.FS.writeFile "/tmp/vg-sha3-next/lazy-variants.h" (String.join (variants.map fun (n,_) => "X(trial_" ++ n ++ ")\\n"))
 IO.FS.writeFile "/tmp/vg-sha3-next/lazy-bulks.h" (String.join (bulks.map fun (n,_) => "B(trial_" ++ n ++ ")\\n"))
end Lazy
def main := Lazy.main
"""
(root/'Lazy.lean').write_text(header)
