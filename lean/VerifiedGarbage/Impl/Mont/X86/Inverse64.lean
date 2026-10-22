module

public import VerifiedGarbage.TCB.X86.Isa

/-! # Lift an existing 32-bit negative Montgomery inverse to 64 bits

The low and high modulus words are in eax and ebx; ecx is the already
computed negative inverse of the low word. Eax receives the high inverse
word. The routine does not access memory.
-/

@[expose] public section
namespace VG.Impl.Mont.X86
open VG VG.X86

def extendInverse : List Instr :=
  [.mul .ecx, .alu .add .edx (.imm 1), .mov .ebp (.reg .edx),
   .mov .eax (.reg .ebx), .mul .ecx, .alu .add .eax (.reg .ebp), .mul .ecx]

end VG.Impl.Mont.X86
