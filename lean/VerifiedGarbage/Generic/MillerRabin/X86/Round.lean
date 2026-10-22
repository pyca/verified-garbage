module

public import VerifiedGarbage.Proof.MillerRabin.X86.Backend
public import VerifiedGarbage.Proof.Framework.Registration

/-! # The prepared Miller–Rabin round for generic i686 callers -/

@[expose] public section
namespace VG.Generic.MillerRabin.X86.Round
open VG.X86

def artifacts (v : Proof.MillerRabin.X86.RoundImpl) : List Artifact := [
  (Spec.MillerRabin.roundApi Spec.MillerRabin.compact).artifact target {
    suffix := v.suffix
    notes := ["i686: four-bit windows reuse the verified runtime Montgomery multiplication. \
      Fourteen products build the table by appending each new power. Each secret digit \
      selects its power through a scan of all sixteen entries. Protected workspace bytes \
      borrowed by multiplication are saved once and restored before return."]
    code := v.code
    stack := Proof.MillerRabin.X86.stackBytes
    verified := v.verified
    spSafe := v.spSafe
    features := v.features }]

end VG.Generic.MillerRabin.X86.Round
