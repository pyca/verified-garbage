module

public import VerifiedGarbage.Impl.Bignum.Arm.Row
public import VerifiedGarbage.Impl.Bignum.Arm.RowCarry

/-! # A multiply-add row including its two top accumulator words -/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def rowFull : Prog isa := .seq row rowCarry

end VG.Impl.Bignum.Arm
