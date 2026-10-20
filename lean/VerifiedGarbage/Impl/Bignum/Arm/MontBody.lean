module

public import VerifiedGarbage.Impl.Bignum.Arm.MontInit
public import VerifiedGarbage.Impl.Bignum.Arm.MontCore

/-! # The complete arithmetic body of ARMv7 Montgomery multiplication -/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def montBody : Prog isa := .seq montInit montCore

end VG.Impl.Bignum.Arm
