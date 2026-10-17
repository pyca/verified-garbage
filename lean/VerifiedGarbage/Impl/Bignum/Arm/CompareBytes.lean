module

public import VerifiedGarbage.TCB.Arm.Isa

/-! # Constant-time comparison of public-length byte strings

Pointers r0/r1 and the positive count lr are public. The XOR/OR accumulator
r2 starts at zero; its final zero/nonzero value remains secret.
-/

@[expose] public section
namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def compareByteStep : List Instr :=
  [.ldrb .r3 .r0 0, .ldrb .r12 .r1 0, .dp .eor .r3 .r3 (.reg .r12),
   .dp .orr .r2 .r2 (.reg .r3), .dp .add .r0 .r0 (.imm 1),
   .dp .add .r1 .r1 (.imm 1), .subs .lr .lr (.imm 1)]
def compareBytes : Prog isa := .loop (.block compareByteStep) .ne
end VG.Impl.Bignum.Arm
