module

import VerifiedGarbage.Impl.Mont.X86
public import VerifiedGarbage.TCB.X86.Isa

/-! # Isolate a paired 64-bit word's lowest set bit with native carry arithmetic -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.LowBit
open VG VG.X86

/-- EBX/ESI are the input pair; EAX/EDX return x & -x. -/
def code : List Instr :=
  [.mov .eax (.imm 0), .alu .sub .eax (.reg .ebx), .mov .edx (.imm 0),
    .alu .sbb .edx (.reg .esi), .alu .and .eax (.reg .ebx), .alu .and .edx (.reg .esi)]

end VG.Impl.RsaKeyGen.X86.LowBit
