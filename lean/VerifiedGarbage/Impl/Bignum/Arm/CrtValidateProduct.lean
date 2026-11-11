module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtProduct
public import VerifiedGarbage.Impl.Bignum.Arm.CrtCheckProduct

/-! # Compute and validate the complete factor product -/

@[expose] public section

namespace VG.Impl.Bignum.Arm.Crt
open VG VG.Arm

/-- The product, with the counts `count` sets, compared with `n`. -/
def validateProductWith (count : List Instr) : Prog isa := .seq (factorProductWith false count) checkProduct
def validateProduct : Prog isa := validateProductWith productCount

end VG.Impl.Bignum.Arm.Crt
