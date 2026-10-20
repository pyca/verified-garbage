module

public import VerifiedGarbage.Impl.Bignum.Arm.WideMul

/-! # A packed-word multiply-accumulate for ARMv7 RSA -/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG.Arm

/-- Add register `r` into the two-word accumulator `r4:r3`. The carry
from `adds` is consumed immediately by `adc`. -/
def addWord (r : Reg) : List Instr :=
  [.adds .r3 .r3 (.reg r), .adc .r4 .r4 (.imm 0)]

/-- `r4:r3 := r1 * r2 + r10 + r11`. The accumulator word and carry are
full 32-bit words. This sum always fits in 64 bits. -/
def mac : List Instr := wideMul ++ addWord .r10 ++ addWord .r11

end VG.Impl.Bignum.Arm
