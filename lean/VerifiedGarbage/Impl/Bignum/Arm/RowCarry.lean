module

public import VerifiedGarbage.Impl.Bignum.Arm.Mac

/-! # Add a row's carry into the accumulator's top words -/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

/-- Add the row carry `r11` to the two words at `r0`, propagating the low
word's carry into the high word. The caller guarantees the sum fits. -/
def rowCarry : Prog isa :=
  .seq (.block [.ldr .r3 .r0 0, .ldr .r4 .r0 4])
    (.seq (.block (addWord .r11)) (.block [.str .r3 .r0 0, .str .r4 .r0 4]))

end VG.Impl.Bignum.Arm
