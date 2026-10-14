module

public import VerifiedGarbage.Impl.Bignum.Arm.Sub

/-! # Subtract r4:r3 from the zero-extended r6, into r11:r2 -/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def sub64High : List Instr :=
  [.mov .r11 (.imm 0), .dp .sub .r11 .r11 (.reg .r4), .dp .sub .r11 .r11 (.reg .r5)]

def sub64 : List Instr := subWord .r2 .r5 .r6 .r3 ++ sub64High

end VG.Impl.Bignum.Arm
