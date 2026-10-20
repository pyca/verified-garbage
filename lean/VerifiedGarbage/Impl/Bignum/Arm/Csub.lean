module

public import VerifiedGarbage.Impl.Bignum.Arm.Select

/-! # Final conditional subtraction of a variable-width modulus -/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

/-- Include the accumulator's high word in the subtraction decision. -/
def reduceChoice : Prog isa :=
  .seq (.block [.ldr .r1 .r10 0, .mov .r2 (.reg .r11)])
    (.block (subWord .r3 .r11 .r1 .r2))

/-- Rewind the source pointers by `4 * r7`, set the output pointer, and
restore the public word count. -/
def selectPrepare : List Instr :=
  [.mov .r12 (.reg .r10), .mov .r10 (.reg .r0),
   .dp .sub .r12 .r12 (.shifted .r7 .lsl 2),
   .dp .sub .r10 .r10 (.shifted .r7 .lsl 2),
   .mov .r0 (.reg .r9), .mov .lr (.reg .r7)]

/-- Subtract the modulus into a temporary, then select the result into
`r9`. Initially `r0` is the temporary, `r10` the accumulator, `r12` the
modulus, `r7 = lr` the nonzero word count, and `r11` is zero. -/
def csub : Prog isa :=
  .seq subRow (.seq reduceChoice (.seq (.block selectPrepare) selectRow))

end VG.Impl.Bignum.Arm
