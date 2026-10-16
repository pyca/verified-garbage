module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtDifference
public import VerifiedGarbage.Impl.Bignum.Arm.SavedOperand

/-! # Multiply the residue difference by the CRT inverse modulo p -/

@[expose] public section

namespace VG.Impl.Bignum.Arm.Crt
open VG VG.Arm

def timesInverse : Prog isa := .seq (savedOperand 1 96 100) (.seq (montOp 1 1 4) (montOp 5 5 1))
def coefficient : Prog isa := .seq difference timesInverse

end VG.Impl.Bignum.Arm.Crt
