module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.Backend

/-! # Emit the shared prepared round for each implementation -/

@[expose] public section

namespace VG.Generic.MillerRabin.X86_64.Round

open VG.Proof.MillerRabin.X86_64

def artifacts (v : RoundImpl) : List Artifact := [
  { Spec.MillerRabin.roundApi Spec.MillerRabin.extended with
    name := v.name
    target := X86_64.target
    doc := (Spec.MillerRabin.roundApi Spec.MillerRabin.extended).doc
      (notes := ["Fixed four-bit windows with the verified Montgomery kernel. The saved frame \
        restores the caller's bookkeeping without making it public. Shared by RSA and FFDH."])
    code := v.code
    contract := Spec.MillerRabin.roundContract X86_64.abi Spec.MillerRabin.extended 120
    stack := 120
    verified := v.verified
    spSafe := v.spSafe
    features := v.features }]

end VG.Generic.MillerRabin.X86_64.Round
