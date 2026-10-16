module

public import VerifiedGarbage.TCB.Arm.Isa

/-! # Runtime-length conversion between big-endian bytes and packed limbs

Copy bytes from a descending source pointer to an ascending destination.
The source and destination ranges are disjoint; lr is a nonzero byte count.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def reverseByteStep : List Instr :=
  [.ldrb .r2 .r1 0, .strb .r2 .r0 0, .dp .add .r0 .r0 (.imm 1),
   .dp .sub .r1 .r1 (.imm 1), .subs .lr .lr (.imm 1)]

def reverseBytes : Prog isa := .loop (.block reverseByteStep) .ne

end VG.Impl.Bignum.Arm
