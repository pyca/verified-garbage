module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtAcceptance
public import VerifiedGarbage.Impl.Bignum.Arm.PreparePrime

/-! # Prepare a CRT factor using the accumulated validation bit -/

@[expose] public section

namespace VG.Impl.Bignum.Arm.Crt
open VG VG.Arm

def prepareAcceptedPrime : Prog isa := .seq (.block installAcceptance) preparePrime

end VG.Impl.Bignum.Arm.Crt
