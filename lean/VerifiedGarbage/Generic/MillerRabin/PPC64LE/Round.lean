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
    notes := ["Fixed four-bit windows and a full masked scan of all sixteen powers, each a masked copy \
        into arrays 3 and 5 in turn. The Montgomery products are `vg_rsa_mont_mul`'s finely \
        integrated operand scanning in radix 2^64, inline. Four \
        unconditional squares precede each window; three final squares mask their flag updates with \
        the threshold derived from the prepared exponent marker. The result is returned without \
        branching on it. The nonvolatile registers it uses are saved in a 176-byte stack frame."]
    code := v.code
    stack := 176
    verified := v.verified
    features := v.features }]

end VG.Generic.MillerRabin.PPC64LE.Round
