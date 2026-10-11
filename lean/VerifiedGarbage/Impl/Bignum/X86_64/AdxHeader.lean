module

public import VerifiedGarbage.Impl.Bignum.X86_64.AdxRect8

/-! Save borrowed header words in the raw-product buffer's padding. -/

@[expose] public section

namespace VG.Impl.Bignum.X86_64.AdxHeader
open VG.X86_64
open VG.Impl.Bignum.X86_64.AdxRotate8 (at_)

def copyWord (src : MemOp) (dst : Reg) (d : Nat) : Prog isa :=
  .seq (.block [.mov .rax (.mem src)]) (.block [.store (at_ dst d) .rax])

def copyPair (src dst : Reg) (a d : Nat) : Prog isa :=
  .seq (copyWord (at_ src a) dst d) (copyWord (at_ src (a+8)) dst (d+8))

def bases : List Instr :=
  [.mov .r8 (.mem (hdr (sArr Public.aAcc))), .mov .r9 (.mem (hdr sW)),
   .shift .shl .r9 4, .alu .add .r9 (.reg .r8), .alu .add .r9 (.imm 16)]

def save : Prog isa := .seq (.block bases)
  (.seq (copyPair .rdi .r8 (8*sFn 12) 0) (copyPair .rdi .r9 (8*sFn 14) 0))

def clearHigh : List Instr :=
  [.mov32 .rax (.imm 0), .store (at_ .r9 0) .rax, .store (at_ .r9 8) .rax]

def restore : Prog isa := .seq (.block bases)
  (.seq (copyPair .r8 .rdi 0 (8*sFn 12))
    (.seq (copyPair .r9 .rdi 0 (8*sFn 14)) (.block clearHigh)))

end VG.Impl.Bignum.X86_64.AdxHeader
