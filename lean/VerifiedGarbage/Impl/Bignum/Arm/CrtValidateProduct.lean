module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtProduct
public import VerifiedGarbage.Impl.Bignum.Arm.CrtCheckProduct

/-! # Compute and validate the complete factor product -/

@[expose] public section

namespace VG.Impl.Bignum.Arm.Crt
open VG VG.Arm

def validateProduct : Prog isa := .seq factorProduct checkProduct

end VG.Impl.Bignum.Arm.Crt
