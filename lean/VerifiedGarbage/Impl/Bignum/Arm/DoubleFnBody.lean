module

public import VerifiedGarbage.Impl.Bignum.Arm.MontFn
public import VerifiedGarbage.Impl.Bignum.Arm.Double

/-! # Modular doubling through the shared RSA workspace header

The array indices use the Montgomery body's register convention. The scalar
array starts with 2; the operand may also be the destination.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def doubleFnBody : Prog isa := .seq (.block MontFn.bases) doubleBody

/-- The outer RSA frame saves its workspace pointer at stack offset zero. -/
def doubleFnRestore : Prog isa := .seq doubleFnBody (.block [.ldrSp .r0 0])

end VG.Impl.Bignum.Arm
