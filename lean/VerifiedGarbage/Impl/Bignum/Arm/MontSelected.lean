module

public import VerifiedGarbage.Impl.Bignum.Arm.MontOp
public import VerifiedGarbage.Impl.Bignum.Arm.Square

/-! Fixed public operand indices select the already verified specialized
square. This shares the arithmetic used by the callable Montgomery helper
without introducing a call frame into existing RSA recovery code. -/

@[expose] public section
namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def selectedMontOp (o a b : Nat) : Prog isa :=
  if a = b then squareOp o a else montOp o a b

end VG.Impl.Bignum.Arm
