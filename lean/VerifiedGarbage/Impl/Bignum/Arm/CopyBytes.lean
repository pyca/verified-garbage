module

public import VerifiedGarbage.TCB.Arm.Isa

/-! # Runtime-length byte copying

Copy bytes from an ascending source pointer to an ascending destination.
The source and destination ranges are disjoint; lr is a nonzero byte count.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def copyByteStep : List Instr :=
  [.ldrb .r2 .r1 0, .strb .r2 .r0 0, .dp .add .r0 .r0 (.imm 1),
   .dp .add .r1 .r1 (.imm 1), .subs .lr .lr (.imm 1)]

def copyBytes : Prog isa := .loop (.block copyByteStep) .ne

end VG.Impl.Bignum.Arm
