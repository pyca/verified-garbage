module

public import VerifiedGarbage.Impl.Bignum.Arm.SubRow

/-! # Fixed-schedule equality of native multiword buffers -/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def equalHead : List Instr := [.mov .r8 (.reg .lr), .mov .r11 (.imm 0)]
def equalReverse : List Instr :=
  [.mov .r6 (.reg .r11), .mov .r7 (.reg .r10), .mov .r10 (.reg .r12), .mov .r12 (.reg .r7),
   .dp .sub .r0 .r0 (.shifted .r8 .lsl 2), .dp .sub .r10 .r10 (.shifted .r8 .lsl 2),
   .dp .sub .r12 .r12 (.shifted .r8 .lsl 2), .mov .lr (.reg .r8), .mov .r11 (.imm 0)]
def equalFinish : List Instr := [.dp .orr .r11 .r11 (.reg .r6), .dp .eor .r11 .r11 (.imm 1)]
/-- Equality is neither unsigned comparison being true. Both passes execute
for every input; subtraction writes only the separate temporary buffer. -/
def equalBuffers : Prog isa :=
  .seq (.block equalHead) (.seq subRow (.seq (.block equalReverse) (.seq subRow (.block equalFinish))))

end VG.Impl.Bignum.Arm
