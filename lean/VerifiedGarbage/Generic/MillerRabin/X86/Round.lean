module

public import VerifiedGarbage.Proof.MillerRabin.X86.Backend
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Emit the verified prepared round for each i686 implementation -/

@[expose] public section
namespace VG.Generic.MillerRabin.X86.Round
open VG VG.X86 VG.Proof.MillerRabin.X86

def artifacts (v : RoundImpl) : List Artifact := [
  (Spec.MillerRabin.roundApi Spec.MillerRabin.compact).artifact target {
    suffix := v.suffix
    code := v.code
    stack := 96
    verified := v.verified
    spSafe := Code.all_of_allInstrs v.spSafe
    features := v.features }]

end VG.Generic.MillerRabin.X86.Round
