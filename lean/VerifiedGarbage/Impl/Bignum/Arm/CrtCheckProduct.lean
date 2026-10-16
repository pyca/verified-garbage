module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtPadModulus
public import VerifiedGarbage.Impl.Bignum.Arm.CrtCompareProduct

/-! # Validate the previously computed full factor product -/

@[expose] public section

namespace VG.Impl.Bignum.Arm.Crt
open VG VG.Arm

def checkProduct : Prog isa := .seq padModulus compareProduct

end VG.Impl.Bignum.Arm.Crt
