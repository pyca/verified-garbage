module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.PPC64LE
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Secp256k1.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdsa.Secp256k1
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Secp256k1.Lit

/-!
# ECDSA signatures over secp256k1 (FIPS 186-5 §6.4.1) on PPC64LE

A generic file (see `TCB/Emit.lean`) over secp256k1's group law `h`, the variant
`Variants/Secp256k1/PPC64LE/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.Secp256k1.PPC64LE.EcdsaSecp256k1

def artifacts (h : Proof.Weierstrass.HasLaw Spec.Secp256k1.curve) : List Artifact := [
  Spec.Ecdsa.Secp256k1.signApi.artifact PPC64LE.target {
    notes := ["The function saves `r14`, `r31` and `lr` in \
      `scratch` (in `r3` during the function), and keeps `out` in `r14`. Field elements and \
      scalars are four 64-bit words in Montgomery form, multiplied by word-by-word Montgomery \
      multiplication (CIOS, in calls of `vg_secp256k1_mul_mod_p` and the other functions of \
      `secp256k1_mont`) with a final conditional subtraction. `[k]G` is a double-and-add ladder over \
      all 256 bits of `k`, with the complete addition formulas of Renes, Costello and Batina for \
      every addition and doubling (calls of `vg_secp256k1_point_double` and `vg_secp256k1_point_add`) and a \
      masked selection for each bit; the inversions modulo `p` and `n` are Fermat's, by \
      square-and-always-multiply over the bits of `p - 2` and `n - 2`. The signature (or zeros) is \
      selected by a mask, so the time depends only on the pointers."]
    code := Impl.Ecdsa.PPC64LE.signSecp256k1
    verified := Proof.Ecdsa.PPC64LE.Secp256k1.sign_verified h.law }]

end VG.Generic.Secp256k1.PPC64LE.EcdsaSecp256k1
