module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtProduct
public import VerifiedGarbage.Impl.Bignum.Arm.CrtFinishRecombine

/-! # Reconstruct the CRT result from h, q and the preserved q residue -/

@[expose] public section

namespace VG.Impl.Bignum.Arm.Crt
open VG VG.Arm

def recombine : Prog isa := .seq (factorProduct true) finishRecombine

end VG.Impl.Bignum.Arm.Crt
