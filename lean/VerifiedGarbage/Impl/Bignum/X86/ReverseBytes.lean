module

public import VerifiedGarbage.TCB.X86.Isa

/-! # Runtime-length endian conversion on i686

`esi` points to the last source byte, `ebx` to the first destination byte,
and `ecx` holds a nonzero byte count. The source and destination are disjoint.
-/

@[expose] public section
namespace VG.Impl.Bignum.X86
open VG VG.X86

def reverseByteStep : List Instr :=
  [.movzx8 .eax ⟨.esi, 0⟩, .store8 ⟨.ebx, 0⟩ .al,
   .alu .add .ebx (.imm 1), .alu .sub .esi (.imm 1),
   .alu .sub .ecx (.imm 1), .alu .cmp .ecx (.imm 0)]

def reverseBytes : Prog isa := .loop (.block reverseByteStep) .ne

end VG.Impl.Bignum.X86
