module

public import VerifiedGarbage.Impl.Bignum.Arm.MontOp

/-! # Reduce a packed operand by an odd modulus using its Montgomery constants

Array 4 contains R² modulo the modulus, and array 7 contains one.
The operand may be larger than the modulus; it occupies the full width.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def reduceOperand (o : Nat) : Prog isa := .seq (montOp o o 4) (montOp o o 7)

end VG.Impl.Bignum.Arm
