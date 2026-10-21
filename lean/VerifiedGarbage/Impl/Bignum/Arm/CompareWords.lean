module

public import VerifiedGarbage.TCB.Arm.Isa

/-! Compare full 32-bit words in one fixed pass, without scratch-array writes. -/

@[expose] public section
namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def compareWordStep : List Instr :=
  [.ldr .r3 .r0 0, .ldr .r12 .r1 0, .dp .eor .r3 .r3 (.reg .r12),
    .dp .orr .r2 .r2 (.reg .r3), .dp .add .r0 .r0 (.imm 4),
    .dp .add .r1 .r1 (.imm 4), .subs .lr .lr (.imm 1)]

def compareWords : Prog isa := .loop (.block compareWordStep) .ne
end VG.Impl.Bignum.Arm
