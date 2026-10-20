module

public import VerifiedGarbage.Impl.Bignum.Arm.Csub

/-! # Finish Montgomery multiplication from its temporary metadata -/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def finishArgs : List Instr :=
  [.ldr .r7 .r0 0, .ldr .r9 .r0 24, .ldr .r10 .r0 28,
   .ldr .r12 .r0 8, .mov .lr (.reg .r7), .mov .r11 (.imm 0)]

def montFinish : Prog isa := .seq (.block finishArgs) csub

end VG.Impl.Bignum.Arm
