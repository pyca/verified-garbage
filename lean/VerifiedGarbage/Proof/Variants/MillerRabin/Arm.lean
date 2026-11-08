module

public import VerifiedGarbage.Proof.Variants.MillerRabin.Arm.Base
public import VerifiedGarbage.Proof.Variants.MillerRabin.Arm.Umaal

/-! # The implementations of `MillerRabin` on 32-bit ARM -/

@[expose] public section

namespace VG.Proof.Variants.MillerRabin.Arm

open VG.Proof.MillerRabin.Arm in
def base : RoundImpl := Proof.Variants.MillerRabin.Arm.Base.variant

open VG.Proof.MillerRabin.Arm in
def umaal : RoundImpl := Proof.Variants.MillerRabin.Arm.Umaal.variant

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this). -/
def variants := [umaal, base]

end VG.Proof.Variants.MillerRabin.Arm
