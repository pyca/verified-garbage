module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtPadModulus
public import VerifiedGarbage.Impl.Bignum.Arm.CrtAddWide

/-! # Finish CRT reconstruction with the preserved q residue in array one -/

@[expose] public section

namespace VG.Impl.Bignum.Arm.Crt
open VG VG.Arm

def finishRecombine : Prog isa := .seq (padModulus 1) addWide

end VG.Impl.Bignum.Arm.Crt
