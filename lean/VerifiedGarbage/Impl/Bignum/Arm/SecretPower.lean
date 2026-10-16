module

public import VerifiedGarbage.Impl.Bignum.Arm.ExpControls
public import VerifiedGarbage.Impl.Bignum.Arm.ImportOperand
public import VerifiedGarbage.Impl.Bignum.Arm.SecretExp

/-! # Import a ciphertext and exponentiate with a secret exponent

The workspace already contains the modulus, inverse and R². The input
pointer and length are in r4/r6, and the exponent pointer and length in
r1/r2. Every exponent bit follows the same square, multiply and select.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def secretPower : Prog isa := .seq (.block expControls) (.seq (importOperand 1) secretExpPhase)

end VG.Impl.Bignum.Arm
