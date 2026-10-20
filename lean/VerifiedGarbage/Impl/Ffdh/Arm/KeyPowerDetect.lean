module

public import VerifiedGarbage.Impl.Ffdh.Arm.Checks

/-! Detect the public generator two with fixed-width arithmetic. -/

@[expose] public section
namespace VG.Impl.Ffdh.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

def detectTwo : Prog isa := .seq (smallConst 5 2) (equal 1 5)

end VG.Impl.Ffdh.Arm
