module

public import VerifiedGarbage.TCB.X86.Isa

/-! # Runtime-length byte copying on i686

`esi` points to the first source byte, `ebx` to the first destination byte,
and `ecx` holds a nonzero byte count. The source and destination are disjoint.
-/

@[expose] public section
namespace VG.Impl.Bignum.X86
open VG VG.X86

def copyByteStep : List Instr :=
  [.movzx8 .eax ⟨.esi, 0⟩, .store8 ⟨.ebx, 0⟩ .al,
   .alu .add .ebx (.imm 1), .alu .add .esi (.imm 1),
   .alu .sub .ecx (.imm 1), .alu .cmp .ecx (.imm 0)]

def copyBytes : Prog isa := .loop (.block copyByteStep) .ne

end VG.Impl.Bignum.X86
