module

public import VerifiedGarbage.Impl.Bignum.Arm.MontCallWith
public import VerifiedGarbage.Impl.Bignum.Arm.SquareReduceWith

/-! One callable helper supplies the row kernel only to square reduction. -/

@[expose] public section
namespace VG.Impl.Bignum.Arm.MontCallSquareReduceWith
open VG VG.Arm

def arithmetic (rowCode : Prog isa) : Prog isa :=
  MontCallWith.dispatch (squareBodyReduceWith rowCode) MontFn.body

def code (rowCode : Prog isa) : Prog isa := MontCallWith.code (arithmetic rowCode)

end VG.Impl.Bignum.Arm.MontCallSquareReduceWith
