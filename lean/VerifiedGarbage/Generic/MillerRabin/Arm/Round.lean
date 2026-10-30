module

public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend
public import VerifiedGarbage.Proof.Framework.Registration

/-! # The shared prepared Miller–Rabin round on ARMv7 -/

@[expose] public section

namespace VG.Generic.MillerRabin.Arm.Round

open VG.Arm

def artifacts (v : Proof.MillerRabin.Arm.RoundImpl) : List Artifact := [
  (Spec.MillerRabin.roundApi Spec.MillerRabin.compact).artifact target {
    suffix := v.suffix
    code := v.code
    stack := 56
    verified := v.verifiedSpec
    features := v.features }]

end VG.Generic.MillerRabin.Arm.Round
