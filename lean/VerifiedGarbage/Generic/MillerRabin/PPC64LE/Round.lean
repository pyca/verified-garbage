module

public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Backend
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Emit the verified prepared round for each PPC64LE implementation -/

@[expose] public section
namespace VG.Generic.MillerRabin.PPC64LE.Round
open VG VG.PPC64LE VG.Proof.MillerRabin.PPC64LE

def artifacts (v : RoundImpl) : List Artifact := [
  (Spec.MillerRabin.roundApi Spec.MillerRabin.compact).artifact target {
    suffix := v.suffix
    code := v.code
    stack := 176
    verified := v.verified
    features := v.features }]

end VG.Generic.MillerRabin.PPC64LE.Round
