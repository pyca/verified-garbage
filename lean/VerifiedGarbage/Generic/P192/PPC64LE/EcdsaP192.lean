module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.P192.PPC64LE
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P192.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdsa.P192
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P192.Lit

/-!
# ECDSA signatures over P-192 (FIPS 186-5 §6.4.1) on PPC64LE

A generic file (see `TCB/Emit.lean`) over P-192's group law `h`, the variant
`Variants/P192/PPC64LE/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P192.PPC64LE.EcdsaP192

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P192.curve) : List Artifact := [
  Spec.Ecdsa.P192.signApi.artifact PPC64LE.target {
    notes := ["The function saves `r14`, `r31` and `lr` in \
      `scratch` (in `r3` during the function), and keeps `out` in `r14`. Field elements and \
      scalars are three 64-bit words in Montgomery form, multiplied by word-by-word Montgomery \
      multiplication (CIOS, in calls of `vg_p192_mul_mod_p` and the other functions of \
      `p192_mont`) with a final conditional subtraction. `[k]G` is a double-and-add ladder over \
      all 192 bits of `k`, with the complete addition formulas of Renes, Costello and Batina for \
      every addition and doubling (calls of `vg_p192_point_double` and `vg_p192_point_add`) and a \
      masked selection for each bit; the inversions modulo `p` and `n` are Fermat's, by \
      square-and-always-multiply over the bits of `p - 2` and `n - 2`. The signature (or zeros) is \
      selected by a mask, so the time depends only on the pointers."]
    code := Impl.Ecdsa.PPC64LE.signP192
    verified := Proof.Ecdsa.PPC64LE.P192.sign_verified h.law }]

end VG.Generic.P192.PPC64LE.EcdsaP192
