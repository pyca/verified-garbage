module

public import VerifiedGarbage.Proof.Variants.MillerRabin.Arm.Umaal

/-! # The shared round on ARMv7 with `umaal` -/

@[expose] public section

namespace VG.Variants.MillerRabin.Arm.Umaal

open VG.Proof.MillerRabin.Arm

def variant : RoundImpl := Proof.Variants.MillerRabin.Arm.Umaal.variant

end VG.Variants.MillerRabin.Arm.Umaal
