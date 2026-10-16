module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.Backend
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Emit the shared prepared round for each implementation -/

@[expose] public section

namespace VG.Generic.MillerRabin.X86_64.Round

open VG.Proof.MillerRabin.X86_64

def artifacts (v : RoundImpl) : List Artifact := [
  (Spec.MillerRabin.roundApi Spec.MillerRabin.extended).artifact X86_64.target {
    suffix := v.suffix
    notes := ["Fixed four-bit windows with the verified Montgomery kernel. The saved frame \
        restores the caller's bookkeeping without making it public. Shared by RSA and FFDH."]
    code := v.code
    stack := 120
    verified := v.verified
    spSafe := v.spSafe
    features := v.features }]

end VG.Generic.MillerRabin.X86_64.Round
