import VerifiedGarbage.Impl.Mont.X86.StaticSquare
import VerifiedGarbage.TCB.X86.Print
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Rt
open VG.Impl.Mont.X86.Rt.StaticSquare
namespace CompactMont
-- UNPROVEN screening only; assembly is produced by the existing Lean ISA printer.
def chunks (u : Nat) : List Instr :=
 (List.range u).flatMap fun j => product .edi .ebp (4*j) (4*(u-1-j))

def grouped (u x y count : Nat) (argX : MemOp) (headProducts : List Instr) : Prog isa :=
 let rem:=count%u
 let delta : Int := (4*(count+u-1) : Nat)-(y : Int)
 seqs [
 .block (headProducts ++ [.alu .add .edi (.imm (BitVec.ofNat 32 (x+4*rem))),
   .alu .add .ebp (.imm (BitVec.ofNat 32 (y-4*rem-4*(u-1))))]),
 .loop (.block (chunks u ++ [
   .alu .add .edi (.imm (BitVec.ofNat 32 (4*u))),.alu .sub .ebp (.imm (BitVec.ofNat 32 (4*u))),
   .mov .edx (.mem argWs),.alu .add .edx (.mem argX),
   .alu .add .edx (.imm (BitVec.ofNat 32 (x+4*count))),.alu .cmp .edi (.reg .edx)])) .ne,
 .block [.alu .sub .edi (.imm (BitVec.ofNat 32 (x+4*count))),
   .alu .add .ebp (.imm (BitVec.ofInt 32 delta))]]

def compactInput (u N k : Nat) : Prog isa :=
 let lo:=k+1-N
 let count:=(k+1)/2-lo
 if k<2*N-1 ∧ 2*u≤count then
  seqs [.block (ptr .edi argA .eax ++ ptr .ebp argA .eax),
    grouped u (4*lo) (4*(k-lo)) count argA
      ((List.range (count%u)).flatMap fun j => aprod (lo+j) (k-(lo+j))),
    .block (double ++ (if k%2=0 then aprod (k/2) (k/2) else []))]
 else .block (input N k)

def compactReduction (u N k : Nat) : Prog isa :=
 let lo:=k+1-N
 let count:=min k N-lo
 if 2*u≤count then
  grouped u (52+4*lo) (4*(k-lo)) count argS
    ((List.range (count%u)).flatMap fun j => qprod (k-(lo+j)) (lo+j))
 else .block (reductionProducts N k N)

def column (u N k : Nat) : Prog isa := seqs [
 .block clear,compactInput u N k,.block (ptr .edi argS .eax ++ ptr .ebp argM .eax),
 .block carryIn,compactReduction u N k,.block (digit N k),.block carryOut]

def columns (u N : Nat) : Nat → Nat → Prog isa
 | _,0 => .block []
 | k,j+1 => .seq (column u N k) (columns u N (k+1) j)

def square (u N : Nat) : Prog isa := seqs [
 .block init,columns u N 0 (2*N),.block (finish N),subM,.block mask,select,.block restoreRegs]

def selectSize (u N : Nat) (fallback : Prog isa) : Prog isa :=
 .seq (.block [.mov .eax (.mem argN),.alu .cmp .eax (.imm (BitVec.ofNat 32 (N/2)))])
 (.ite .e (square u N) fallback)

def dispatch (u : Nat) : Prog isa := .seq
 (.block [.mov .eax (.mem argA),.mov .edx (.mem argB),.alu .cmp .eax (.reg .edx)])
 (.ite .e (selectSize u 64 (selectSize u 96 (selectSize u 128 VG.Impl.Mont.X86.Rt.Square.square)))
 VG.Impl.Mont.X86.Rt.scalarBody)

def printFn (name : String) (p : Prog isa) : String :=
 ".globl "++name++"\n.p2align 6\n"++name++":\n"++
 "\n".intercalate ((printer.function p).map fun l => match l with
 | .text s => s | .call _ => "ERROR" | .sym .. => "ERROR")++"\n"
end CompactMont

namespace CompactRev
-- Reuse the existing final-subtraction temporary for a reversed modulus.
def reverseCopy (N : Nat) : List Instr :=
 ptr .ebp argM .eax ++ (List.range N).flatMap fun j =>
 [.mov .eax (.mem (at_ .ebp (4*j))),.store (at_ .edi (56+8*N+4*(N-1-j))) .eax]

def inputTune : Prog isa → Prog isa
 | .seq a b => .seq (inputTune a) (inputTune b)
 | .loop (.block xs) _ => .loop (.block (xs.take (xs.length-4) ++ [.alu .cmp .edi (.reg .ebp)])) .b
 | p => p

def reduction (u N k : Nat) : Prog isa :=
 let lo:=k+1-N
 let count:=min k N-lo
 if 2*u≤count then
  seqs [.block (((List.range (count%u)).flatMap fun j => qprod (k-(lo+j)) (lo+j)) ++
    [.alu .add .edi (.imm (BitVec.ofNat 32 (52+4*(lo+count%u)))),
     .mov .ebp (.imm (BitVec.ofNat 32 (count/u)))]),
   .loop (.block (((List.range u).flatMap fun j => product .edi .edi (4*j) (4*(3*N-k+j))) ++
      [.alu .add .edi (.imm (BitVec.ofNat 32 (4*u))),.alu .sub .ebp (.imm 1)])) .ne,
   .block ([.alu .sub .edi (.imm (BitVec.ofNat 32 (52+4*(lo+count))))] ++ ptr .ebp argM .eax)]
 else .block (reductionProducts N k N)

def column (u N k : Nat) : Prog isa := seqs [
 .block clear,inputTune (CompactMont.compactInput u N k),.block (ptr .edi argS .eax ++ ptr .ebp argM .eax),
 .block carryIn,reduction u N k,.block (digit N k),.block carryOut]

def columns (u N : Nat) : Nat → Nat → Prog isa
 | _,0 => .block []
 | k,j+1 => .seq (column u N k) (columns u N (k+1) j)

def square (u N : Nat) : Prog isa := seqs [
 .block (init ++ reverseCopy N),columns u N 0 (2*N),.block (finish N),subM,.block mask,select,.block restoreRegs]

def selectSize (u N : Nat) (fallback : Prog isa) : Prog isa :=
 .seq (.block [.mov .eax (.mem argN),.alu .cmp .eax (.imm (BitVec.ofNat 32 (N/2)))])
 (.ite .e (square u N) fallback)

def dispatch (u : Nat) : Prog isa := .seq
 (.block [.mov .eax (.mem argA),.mov .edx (.mem argB),.alu .cmp .eax (.reg .edx)])
 (.ite .e (selectSize u 64 (selectSize u 96 (selectSize u 128 VG.Impl.Mont.X86.Rt.Square.square)))
 VG.Impl.Mont.X86.Rt.scalarBody)
end CompactRev

namespace ScalarCompactProto
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Rt
-- ESI:EBX:EDI hold low, middle, high of a 96-bit accumulator.
-- Public column/end and the incoming carry use the existing scratch header.
def seqs := VG.Impl.Mont.X86.Rt.Square.seqs

def accum : List Instr := [.alu .add .esi (.reg .eax), .alu .adc .ebx (.reg .edx), .alu .adc .edi (.imm 0)]
def prodAt (j : Nat) : List Instr := [
 .mov .eax (.mem (at_ .ecx (4*j))),
 .mov .edx (.mem (at_ .ebp (if j=0 then 0 else 2^32-4*j))), .mul .edx] ++ accum

def sPtr (d t : Reg) : List Instr := ptr d argS t

def getEnd : List Instr := sPtr .edx .eax ++ [.mov .eax (.mem (at_ .edx 0))]

def crossTail (v : Nat) : Prog isa := seqs [
 .block [.mov .eax (.reg .ebp),.alu .sub .eax (.reg .ecx),.alu .cmp .eax (.imm (BitVec.ofNat 32 (8*v)))],
 .ite .ae (.block ((List.range v).flatMap prodAt ++
   [.alu .add .ecx (.imm (BitVec.ofNat 32 (4*v))),.alu .sub .ebp (.imm (BitVec.ofNat 32 (4*v)))])) (.block [])]

def crossLoop (u : Nat) : Prog isa := seqs ([
 .block [.mov .eax (.reg .ebp),.alu .sub .eax (.reg .ecx),.alu .cmp .eax (.imm (BitVec.ofNat 32 (8*u)))],
 .ite .ae (.loop (.block ((List.range u).flatMap prodAt ++ [
   .alu .add .ecx (.imm (BitVec.ofNat 32 (4*u))),.alu .sub .ebp (.imm (BitVec.ofNat 32 (4*u))),
   .mov .eax (.reg .ebp),.alu .sub .eax (.reg .ecx),.alu .cmp .eax (.imm (BitVec.ofNat 32 (8*u)))])) .ae) (.block [])] ++
 ([32,16,8,4,2,1].filter (·<u)).map crossTail ++ [
 .block [.alu .cmp .ecx (.reg .ebp)],.ite .b (.block (prodAt 0)) (.block [])])

def redTail (v : Nat) : Prog isa := seqs [
 .block (getEnd ++ [.alu .sub .eax (.reg .ecx),.alu .cmp .eax (.imm (BitVec.ofNat 32 (4*v)))]),
 .ite .ae (.block ((List.range v).flatMap prodAt ++
   [.alu .add .ecx (.imm (BitVec.ofNat 32 (4*v))),.alu .sub .ebp (.imm (BitVec.ofNat 32 (4*v)))])) (.block [])]

def redLoop (u : Nat) : Prog isa := seqs ([
 .block (getEnd ++ [.alu .sub .eax (.reg .ecx),.alu .cmp .eax (.imm (BitVec.ofNat 32 (4*u)))]),
 .ite .ae (.loop (.block ((List.range u).flatMap prodAt ++ [
   .alu .add .ecx (.imm (BitVec.ofNat 32 (4*u))),.alu .sub .ebp (.imm (BitVec.ofNat 32 (4*u)))] ++
   getEnd ++ [.alu .sub .eax (.reg .ecx),.alu .cmp .eax (.imm (BitVec.ofNat 32 (4*u)))])) .ae) (.block [])] ++
 ([32,16,8,4,2,1].filter (·<u)).map redTail)

def cross (u : Nat) : Prog isa := seqs [
 .block (sPtr .edi .eax ++ [.mov .esi (.mem (at_ .edi 4))] ++ lenTimes .eax 1 ++
   [.alu .sub .eax (.imm 4), .alu .cmp .esi (.reg .eax)]),
 .ite .b (seqs [
   .block (lenTimes .eax 0 ++ [.mov .edx (.reg .esi), .alu .add .edx (.imm 4), .alu .sub .edx (.reg .eax)]),
   .ite .b (.block [.mov .edx (.imm 0)]) (.block []),
   .block ([.mov .ecx (.mem argWs), .mov .eax (.mem argA), .alu .add .ecx (.reg .eax),
     .mov .ebp (.reg .ecx), .alu .add .ecx (.reg .edx), .alu .add .ebp (.reg .esi), .alu .sub .ebp (.reg .edx),
     .mov .esi (.imm 0), .mov .ebx (.imm 0), .mov .edi (.imm 0)]),
   crossLoop u,
   .block ([.alu .add .esi (.reg .esi), .alu .adc .ebx (.reg .ebx), .alu .adc .edi (.reg .edi)] ++
     sPtr .edx .eax ++ [.mov .eax (.mem (at_ .edx 4)), .alu .and .eax (.imm 4)]),
   .ite .e (.block (sPtr .edx .eax ++ [.mov .eax (.mem (at_ .edx 4)), .shift .shr .eax 1,
     .mov .edx (.mem argWs), .alu .add .eax (.reg .edx), .mov .edx (.mem argA),
     .alu .add .eax (.reg .edx), .mov .eax (.mem (at_ .eax 0)), .mul .eax] ++ accum)) (.block [])])
   (.block [.mov .esi (.imm 0), .mov .ebx (.imm 0), .mov .edi (.imm 0)]),
 .block (sPtr .edx .eax ++ [.alu .add .esi (.mem (at_ .edx 8)),
   .alu .adc .ebx (.mem (at_ .edx 12)), .alu .adc .edi (.imm 0)])]

def reduce (u : Nat) : Prog isa := seqs [
 .block (sPtr .ecx .eax ++ [.mov .ebp (.mem (at_ .ecx 4))] ++ lenTimes .eax 0 ++
   [.mov .edx (.reg .ebp), .alu .add .edx (.imm 4), .alu .sub .edx (.reg .eax)]),
 .ite .b (.block [.mov .edx (.imm 0)]) (.block []),
 .block [.alu .cmp .ebp (.reg .eax)],
 .ite .b (.block [.mov .eax (.reg .ebp)]) (.block []),
 .block [.alu .add .eax (.reg .ecx), .alu .add .eax (.imm 52), .store (at_ .ecx 0) .eax,
   .alu .add .ecx (.imm 52), .alu .add .ecx (.reg .edx),
   .alu .sub .ebp (.reg .edx), .mov .eax (.mem argWs), .alu .add .ebp (.reg .eax),
   .mov .eax (.mem argM), .alu .add .ebp (.reg .eax)],
 redLoop u,
 .block (sPtr .ecx .eax ++ [.mov .ebp (.mem (at_ .ecx 4))] ++ lenTimes .eax 0 ++ [.alu .cmp .ebp (.reg .eax)]),
 .ite .b (.block [
   .mov .eax (.reg .esi), .mov .edx (.mem (at_ .ecx 16)), .mul .edx,
   .mov .edx (.reg .ecx), .alu .add .edx (.imm 52), .alu .add .edx (.reg .ebp), .store (at_ .edx 0) .eax,
   .mov .ebp (.mem argM), .mov .edx (.mem argWs), .alu .add .ebp (.reg .edx),
   .mov .edx (.mem (at_ .ebp 0)), .mul .edx,
   .alu .add .esi (.reg .eax), .alu .adc .ebx (.reg .edx), .alu .adc .edi (.imm 0)])
   (.block [.mov .edx (.reg .ecx), .alu .add .edx (.imm 52), .alu .add .edx (.reg .ebp), .store (at_ .edx 0) .esi]),
 .block (sPtr .ecx .eax ++ [.store (at_ .ecx 8) .ebx, .store (at_ .ecx 12) .edi,
   .mov .eax (.mem (at_ .ecx 4)), .alu .add .eax (.imm 4), .store (at_ .ecx 4) .eax] ++
   lenTimes .edx 1 ++ [.alu .cmp .eax (.reg .edx)])]

def square (u : Nat) : Prog isa := seqs [
 .block (save ++ ptr .edx argInv .eax ++ [.mov .eax (.mem (at_ .edx 0)), .store (at_ .edi 16) .eax,
   .mov .eax (.imm 0), .store (at_ .edi 4) .eax, .store (at_ .edi 8) .eax, .store (at_ .edi 12) .eax]),
 .loop (.seq (cross u) (reduce u)) .ne,
 .block (sPtr .edi .eax ++ lenTimes .ebp 1 ++ [.alu .add .ebp (.reg .edi), .alu .add .ebp (.imm 52),
   .mov .eax (.mem (at_ .edi 8)), .store (at_ .ebp 0) .eax,
   .mov .eax (.mem (at_ .edi 12)), .store (at_ .ebp 4) .eax] ++ lenTimes .eax 0 ++ [.alu .sub .ebp (.reg .eax)]),
 subM, .block mask, select, .block restoreRegs]

def dispatch (u : Nat) : Prog isa := .seq
 (.block [.mov .eax (.mem argA), .mov .edx (.mem argB), .alu .cmp .eax (.reg .edx)])
 (.ite .e (square u) VG.Impl.Mont.X86.Rt.scalarBody)
end ScalarCompactProto
namespace CompactRuntime
open ScalarCompactProto

def foldBlock (N : Nat) (xs : List Instr) : List Instr :=
 let out : List (Instr × Bool) := xs.foldl (fun acc i =>
  match i,acc with
  | .mov r (.mem m),_ =>
    if m=argN then (.mov r (.imm (BitVec.ofNat 32 (N/2))),true)::acc else (i,false)::acc
  | .alu .add r (.reg r'),(.mov p (.imm v),true)::rest =>
    if r=r' ∧ r=p then (.mov r (.imm (v+v)),true)::rest else (i,false)::acc
  | _,_ => (i,false)::acc) []
 out.reverse.map Prod.fst

def foldProg (N : Nat) : Prog isa → Prog isa
 | .block xs => .block (foldBlock N xs)
 | .seq a b => .seq (foldProg N a) (foldProg N b)
 | .ite c a b => .ite c (foldProg N a) (foldProg N b)
 | .loop b c => .loop (foldProg N b) c
 | p => p

def swapReg : Reg → Reg | .ecx => .edi | .edi => .ecx | r => r
def swapMem (m : MemOp) : MemOp := {m with base:=swapReg m.base}
def swapSrc : Src → Src
 | .reg r => .reg (swapReg r) | .mem m => .mem (swapMem m) | s => s

def swapInstr : Instr → Instr
 | .mov d s => .mov (swapReg d) (swapSrc s)
 | .alu o d s => .alu o (swapReg d) (swapSrc s)
 | .store m r => .store (swapMem m) (swapReg r)
 | .mul r => .mul (swapReg r)
 | .shift o d k => .shift o (swapReg d) k
 | i => i

def swapProg : Prog isa → Prog isa
 | .block xs => .block (xs.map swapInstr)
 | .seq a b => .seq (swapProg a) (swapProg b)
 | .ite c a b => .ite c (swapProg a) (swapProg b)
 | .loop b c => .loop (swapProg b) c
 | p => p

def square (u N : Nat) (swapped : Bool) : Prog isa :=
 let core := .seq (ScalarCompactProto.cross u) (ScalarCompactProto.reduce u)
 foldProg N (VG.Impl.Mont.X86.Rt.StaticSquare.seqs [
 .block (save ++ ptr .edx argInv .eax ++ [.mov .eax (.mem (at_ .edx 0)),.store (at_ .edi 16) .eax,
   .mov .eax (.imm 0),.store (at_ .edi 4) .eax,.store (at_ .edi 8) .eax,.store (at_ .edi 12) .eax]),
 .loop (if swapped then swapProg core else core) .ne,
 .block (ptr .edi argS .eax ++ lenTimes .ebp 1 ++ [.alu .add .ebp (.reg .edi),.alu .add .ebp (.imm 52),
   .mov .eax (.mem (at_ .edi 8)),.store (at_ .ebp 0) .eax,
   .mov .eax (.mem (at_ .edi 12)),.store (at_ .ebp 4) .eax] ++ lenTimes .eax 0 ++ [.alu .sub .ebp (.reg .eax)]),
 subM,.block mask,select,.block restoreRegs])

def selectSize (u N : Nat) (swapped : Bool) (fallback : Prog isa) : Prog isa :=
 .seq (.block [.mov .eax (.mem argN),.alu .cmp .eax (.imm (BitVec.ofNat 32 (N/2)))])
 (.ite .e (square u N swapped) fallback)

def dispatch (u : Nat) (swapped : Bool) : Prog isa := .seq
 (.block [.mov .eax (.mem argA),.mov .edx (.mem argB),.alu .cmp .eax (.reg .edx)])
 (.ite .e (selectSize u 64 swapped (selectSize u 96 swapped
  (selectSize u 128 swapped VG.Impl.Mont.X86.Rt.Square.square))) VG.Impl.Mont.X86.Rt.scalarBody)
end CompactRuntime

def main : IO Unit := do
 let codes := [VG.Impl.Mont.X86.Rt.StaticSquare.dispatch] ++ [8,16,32,64].map CompactMont.dispatch ++ [8,16,32,64].map CompactRev.dispatch ++
  [8,16,32,64].map (fun u => CompactRuntime.dispatch u false) ++
  [8,16,32,64].map (fun u => CompactRuntime.dispatch u true)
 IO.FS.writeFile "/workspace/scratch/compact-mont.S" (".intel_syntax noprefix\n.text\n"++
   String.join ((codes.zipIdx).map fun (p,i) => CompactMont.printFn ("compact_mont"++toString i) p) ++
   ".section .note.GNU-stack,\"\",@progbits\n")
 for (p,i) in codes.zipIdx do
  IO.println s!"mode={i} assembly_lines={(printer.function p).length}"
