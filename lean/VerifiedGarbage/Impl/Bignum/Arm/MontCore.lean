module

public import VerifiedGarbage.Impl.Bignum.Arm.Round
public import VerifiedGarbage.Impl.Bignum.Arm.MontFinish

/-! # Montgomery multiplication after workspace initialization -/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def montCore : Prog isa := .seq montRounds montFinish

end VG.Impl.Bignum.Arm
