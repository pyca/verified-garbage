module

public import VerifiedGarbage.Impl.Bignum.Arm.SanitizeModulus
public import VerifiedGarbage.Impl.Bignum.Arm.Precompute

/-! # Secret-factor preparation for private RSA arithmetic -/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def preparePrime : Prog isa := .seq sanitizeModulus (.seq precomputeInverse r2)

end VG.Impl.Bignum.Arm
