module

public import VerifiedGarbage.TCB.X86.Isa

/-! # Select reject, continue or probable-prime status with native masks -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.WitnessStatus
open VG VG.X86

/-- EAX: completed rounds, EBX: uniform rounds, EDX: required uniform
rounds, ESI: the round's zero-or-one result. ECX receives status. -/
def code : List Instr :=
  [.alu .cmp .eax (.imm 16), .alu .sbb .ecx (.reg .ecx),
    .alu .cmp .ebx (.reg .edx), .alu .sbb .edx (.reg .edx),
    .alu .or .ecx (.reg .edx), .alu .and .ecx (.imm 3), .alu .add .ecx (.imm 1),
    .mov .ebp (.imm 0), .alu .sub .ebp (.reg .esi), .alu .and .ecx (.reg .ebp),
    .alu .xor .ebp (.imm (BitVec.allOnes 32)), .alu .and .ebp (.imm 3), .alu .or .ecx (.reg .ebp)]

end VG.Impl.RsaKeyGen.X86.WitnessStatus
