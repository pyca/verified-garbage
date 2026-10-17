module

public import VerifiedGarbage.Impl.Bignum.Arm.Mac

/-! # One packed-word row step for ARMv7 Montgomery arithmetic -/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

/-- Add `r1 * [r12] + r11` into `[r0]`, retaining the high word in `r11`.
The row's pointers and scalar survive. The enclosing loop advances the
pointers and handles its public counter separately. -/
def rowStep : Prog isa :=
  .seq (.block [.ldr .r2 .r12 0, .ldr .r10 .r0 0])
    (.seq (.block mac) (.block [.str .r3 .r0 0, .mov .r11 (.reg .r4)]))

end VG.Impl.Bignum.Arm
