module

public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # The shared prepared Miller–Rabin round on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.MillerRabin.PPC64LE

def artifacts : List Artifact := [
  (Spec.MillerRabin.roundApi Spec.MillerRabin.compact).artifact PPC64LE.target {
    notes := ["Fixed four-bit windows and a full masked scan of all sixteen powers, each a masked copy \
        into arrays 3 and 5 in turn. The model has no carry bit, so the Montgomery products are \
        `vg_rsa_mont_mul`'s finely integrated operand scanning in radix 2^32, inline. Four \
        unconditional squares precede each window; three final squares mask their flag updates with \
        the threshold derived from the prepared exponent marker. The result is returned without \
        branching on it. The nonvolatile registers it uses are saved in a 176-byte stack frame."]
    code := Impl.StackScratch.PPC64LE.withStackScratch 176 .r5 Impl.MillerRabin.PPC64LE.round
    stack := 176
    verified := Proof.MillerRabin.PPC64LE.round_verified }]

end VG.Artifacts.MillerRabin.PPC64LE
