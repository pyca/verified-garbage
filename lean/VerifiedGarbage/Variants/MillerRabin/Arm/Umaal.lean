module

public import VerifiedGarbage.Proof.Variants.MillerRabin.Arm.Umaal

/-! # The shared round on ARMv7 with `umaal`

A variant of `MillerRabin` on ARMv7 (see `TCB/Emit.lean`): the baseline's
round with each Montgomery row's word steps by one `umaal` each. It needs
the CPU feature `umaal`. -/

@[expose] public section

namespace VG.Variants.MillerRabin.Arm.Umaal

open VG.Proof.MillerRabin.Arm

def variant : RoundImpl := Proof.Variants.MillerRabin.Arm.Umaal.variant

end VG.Variants.MillerRabin.Arm.Umaal
