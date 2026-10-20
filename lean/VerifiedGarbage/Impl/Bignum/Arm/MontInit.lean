module

public import VerifiedGarbage.Impl.Bignum.Arm.Zero

/-! # Initialize Montgomery's temporary metadata and zero accumulator

On entry r5 is the temporary, r6 the accumulator, r7 the packed-word count,
r8 and r9 the operands, r10 the output, r11 the modulus, and r12 the inverse.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def initMeta : List Instr :=
  [.str .r7 .r5 0, .str .r9 .r5 4, .str .r11 .r5 8, .str .r12 .r5 12,
   .str .r8 .r5 16, .str .r7 .r5 20, .str .r10 .r5 24, .str .r6 .r5 28]

def prepareZero : List Instr :=
  [.mov .r0 (.reg .r6), .mov .lr (.reg .r7), .dp .add .lr .lr (.imm 2), .mov .r3 (.imm 0)]

def montInit : Prog isa := .seq (.block initMeta)
  (.seq (.block prepareZero) (.seq zero (.block [.mov .r0 (.reg .r5)])))

end VG.Impl.Bignum.Arm
