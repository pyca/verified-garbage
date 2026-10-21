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

def main : IO Unit := do
 let codes := [VG.Impl.Mont.X86.Rt.StaticSquare.dispatch] ++ [8,16,32,64].map CompactMont.dispatch ++ [8,16,32,64].map CompactRev.dispatch
 IO.FS.writeFile "/workspace/scratch/compact-mont.S" (".intel_syntax noprefix\n.text\n"++
   String.join ((codes.zipIdx).map fun (p,i) => CompactMont.printFn ("compact_mont"++toString i) p) ++
   ".section .note.GNU-stack,\"\",@progbits\n")
 for (p,i) in codes.zipIdx do
  IO.println s!"mode={i} assembly_lines={(printer.function p).length}"
