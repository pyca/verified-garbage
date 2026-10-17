module

public import VerifiedGarbage.TCB.Arm.Isa

/-! # Accumulate secret CRT validation results without branching

The saved bit at stack offset 48 is ANDed with r11. The accumulated bit
is returned in r11 and saved back to the same caller-clobbered frame slot.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def mergeAcceptance : List Instr :=
  [.addSp .r12 48, .ldr .r1 .r12 0, .dp .and .r11 .r11 (.reg .r1), .str .r11 .r12 0]

end VG.Impl.Bignum.Arm
