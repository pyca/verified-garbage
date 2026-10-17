module

public import VerifiedGarbage.Impl.Bignum.Arm.Zero

/-! # Initialize a packed-limb array to one native word

r0 and r4 point to the array, lr is its nonzero native-word count, r3 is
zero, and r5 contains the desired value. Used for RSA's one and two.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def setSmall : Prog isa := .seq zero (.block [.str .r5 .r4 0])

end VG.Impl.Bignum.Arm
