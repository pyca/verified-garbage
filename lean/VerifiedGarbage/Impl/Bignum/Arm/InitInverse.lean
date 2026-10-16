module

public import VerifiedGarbage.Impl.Bignum.Arm.Minv64
public import VerifiedGarbage.Impl.Bignum.Arm.Store64

/-! # Store the full Montgomery inverse in the shared RSA header

r0 points at the modulus, r12 holds the workspace base. The result is
stored in header word 7, and r0 is restored to the workspace base.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def initInverse : Prog isa := .seq (.block minv64)
  (.seq (.block (store64 .r2 .r11 .r12 56)) (.block [.mov .r0 (.reg .r12)]))

end VG.Impl.Bignum.Arm
