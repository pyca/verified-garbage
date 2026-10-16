module

public import VerifiedGarbage.Proof.Variants.MillerRabin.AArch64.Base

/-! # The baseline shared round -/

@[expose] public section

namespace VG.Variants.MillerRabin.AArch64.Base

open VG.Proof.MillerRabin.AArch64 VG.Proof.Bignum.AArch64

def variant : RoundImpl := Proof.Variants.MillerRabin.AArch64.Base.variant

end VG.Variants.MillerRabin.AArch64.Base
