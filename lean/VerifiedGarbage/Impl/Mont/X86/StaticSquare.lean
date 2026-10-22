module

public import VerifiedGarbage.Impl.Mont.X86.MulRt

/-! # Fixed-width scalar product columns for the common RSA sizes

Public widths select 1024-, 1536-, 2048-, 3072- and 4096-bit squares, including
the prime-sized squares in 2048- and 3072-bit RSA CRT operations. Each column uses a
96-bit scalar accumulator; every product and memory offset is fixed at
emission time. The header, accumulator, final subtraction and ABI match the
runtime-width multiplication. Other widths retain the runtime square.
-/

@[expose] public section
namespace VG.Impl.Mont.X86.Rt.StaticSquare
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Rt

def seqs := VG.Impl.Mont.X86.Rt.Square.seqs

def accum : List Instr :=
 [.alu .add .esi (.reg .eax),.alu .adc .ebx (.reg .edx),.alu .adc .ecx (.imm 0)]

def product (r r' : Reg) (d d' : Nat) : List Instr :=
 [.mov .eax (.mem (at_ r d)),.mov .edx (.mem (at_ r' d')),.mul .edx] ++ accum

def aprod (i j : Nat) : List Instr := product .edi .edi (4*i) (4*j)
def qprod (i j : Nat) : List Instr := product .edi .ebp (52+4*j) (4*i)

def inputTerm (N k i : Nat) : List Instr :=
 if i≤k ∧ k-i<N ∧ i<k-i then aprod i (k-i) else []

def inputProducts (N k count : Nat) : List Instr :=
 (List.range count).flatMap (inputTerm N k)

def reductionTerm (N k j : Nat) : List Instr :=
 if j<k ∧ k-j<N then qprod (k-j) j else []

def reductionProducts (N k count : Nat) : List Instr :=
 (List.range count).flatMap (reductionTerm N k)

def clear : List Instr := [.mov .esi (.imm 0),.mov .ebx (.imm 0),.mov .ecx (.imm 0)]
def double : List Instr := [.alu .add .esi (.reg .esi),.alu .adc .ebx (.reg .ebx),.alu .adc .ecx (.reg .ecx)]

def input (N k : Nat) : List Instr :=
 if k<2*N-1 then ptr .edi argA .eax ++ inputProducts N k N ++ double ++
   (if k%2=0 then aprod (k/2) (k/2) else []) else []

def carryIn : List Instr :=
 [.alu .add .esi (.mem (at_ .edi 8)),.alu .adc .ebx (.mem (at_ .edi 12)),.alu .adc .ecx (.imm 0)]

def digit (N k : Nat) : List Instr :=
 if k<N then
   [.mov .eax (.reg .esi),.mov .edx (.mem (at_ .edi 16)),.mul .edx,.store (at_ .edi (52+4*k)) .eax,
    .mov .edx (.mem (at_ .ebp 0)),.mul .edx] ++ accum
 else [.store (at_ .edi (52+4*k)) .esi]

def carryOut : List Instr := [.store (at_ .edi 8) .ebx,.store (at_ .edi 12) .ecx]

def column (N k : Nat) : Prog isa := seqs [
 .block clear,.block (input N k),.block (ptr .edi argS .eax ++ ptr .ebp argM .eax),
 .block carryIn,.block (reductionProducts N k N),.block (digit N k),.block carryOut]

def columns (N : Nat) : Nat → Nat → Prog isa
 | _,0 => .block []
 | k,j+1 => .seq (column N k) (columns N (k+1) j)

def init : List Instr :=
 save ++ ptr .edx argInv .eax ++ [.mov .eax (.mem (at_ .edx 0)),.store (at_ .edi 16) .eax,
  .mov .eax (.imm 0),.store (at_ .edi 8) .eax,.store (at_ .edi 12) .eax]

def finish (N : Nat) : List Instr :=
 [.mov .ebp (.reg .edi),.alu .add .ebp (.imm (BitVec.ofNat 32 (52+8*N))),
  .mov .eax (.mem (at_ .edi 8)),.store (at_ .ebp 0) .eax,
  .mov .eax (.mem (at_ .edi 12)),.store (at_ .ebp 4) .eax,.alu .sub .ebp (.imm (BitVec.ofNat 32 (4*N)))]

def front (N : Nat) : Prog isa := seqs [.block init,columns N 0 (2*N),.block (finish N)]

def square (N : Nat) : Prog isa := seqs [front N,subM,.block mask,select,.block restoreRegs]

def selectSize (N : Nat) (fallback : Prog isa) : Prog isa :=
 .seq (.block [.mov .eax (.mem argN),.alu .cmp .eax (.imm (BitVec.ofNat 32 (N/2)))])
 (.ite .e (square N) fallback)

def dispatch : Prog isa := .seq
 (.block [.mov .eax (.mem argA),.mov .edx (.mem argB),.alu .cmp .eax (.reg .edx)])
 (.ite .e (selectSize 32 (selectSize 48 (selectSize 64 (selectSize 96 (selectSize 128 VG.Impl.Mont.X86.Rt.Square.square)))))
   VG.Impl.Mont.X86.Rt.scalarBody)

end VG.Impl.Mont.X86.Rt.StaticSquare

namespace VG.Impl.Mont.X86.Rt

/-- Public input aliasing and widths select the proved scalar square schedules. -/
def body : Prog VG.X86.isa := StaticSquare.dispatch

end VG.Impl.Mont.X86.Rt
