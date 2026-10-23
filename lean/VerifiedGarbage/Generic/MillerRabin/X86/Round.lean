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
    notes := ["Baseline i686: fixed four-bit windows and a full masked scan of all sixteen powers. \
      Fourteen Montgomery products (calls of `vg_rsa_mont_mul`) build the table once. The candidate's Montgomery header, \
      inverse and constants are reused by every product and across witnesses. Four unconditional \
      squares precede each window; three final squares mask their flag updates with the threshold \
      derived from the prepared exponent marker. The result is returned without branching on it."]
    code := v.code
    stack := 96
    verified := v.verified
    spSafe := Code.all_of_allInstrs v.spSafe
    features := v.features }]

end VG.Generic.MillerRabin.X86.Round
