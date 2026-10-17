module

public import VerifiedGarbage.Proof.Variants.MillerRabin.Arm.Base

/-! # The baseline shared round on ARMv7 -/

@[expose] public section

namespace VG.Variants.MillerRabin.Arm.Base

open VG.Proof.MillerRabin.Arm

def variant : RoundImpl := Proof.Variants.MillerRabin.Arm.Base.variant

end VG.Variants.MillerRabin.Arm.Base
