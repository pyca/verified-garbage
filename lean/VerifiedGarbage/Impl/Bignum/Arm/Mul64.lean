module

public import VerifiedGarbage.Impl.Bignum.Arm.WideMul

/-! # Low 64 bits of a product of two register pairs

The inputs are r10:r1 and r11:r2; r4:r3 receives their product modulo 2^64.
The full low-word product uses the constant-time partial-product sequence.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def mul64Cross : List Instr :=
  [.mul .r5 .r1 .r11, .mul .r6 .r2 .r10,
   .dp .add .r4 .r4 (.reg .r5), .dp .add .r4 .r4 (.reg .r6)]

def mul64 : List Instr := wideMul ++ mul64Cross

end VG.Impl.Bignum.Arm
