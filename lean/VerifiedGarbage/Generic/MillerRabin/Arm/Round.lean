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
    notes := ["ARMv7: binary exponentiation rather than windows of four bits, by `vg_rsa_public_checked`'s \
        Montgomery multiplication on 32-bit limbs. The bits of `c − 1` are shifted out of a copy of \
        `c` one at a time, from the top; each squares `y`, multiplies it by the witness or by 1, \
        selected under the bit's mask, and updates the flag under masks. The shifted exponent and \
        the table are not used. The round result is returned without branching on it."]
    code := v.code
    stack := 56
    verified := v.verifiedSpec
    features := v.features }]

end VG.Generic.MillerRabin.Arm.Round
