module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.PPC64LE
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP384r1.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP384r1
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP384r1.Lit

/-!
# ECDSA signatures over brainpoolP384r1 (FIPS 186-5 §6.4.1) on PPC64LE

A generic file (see `TCB/Emit.lean`) over brainpoolP384r1's group law `h`, the variant
`Variants/BrainpoolP384r1/PPC64LE/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.BrainpoolP384r1.PPC64LE.EcdsaBrainpoolP384r1

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP384r1.curve) : List Artifact := [
  Spec.Ecdsa.BrainpoolP384r1.signApi.artifact PPC64LE.target {
    notes := ["The function saves `r14`, `r31` and `lr` in \
      `scratch` (in `r3` during the function), and keeps `out` in `r14`. Field elements and \
      scalars are six 64-bit words in Montgomery form, multiplied by word-by-word Montgomery \
      multiplication (CIOS, in calls of `vg_brainpoolp384r1_mul_mod_p` and the other functions of \
      `brainpoolp384r1_mont`) with a final conditional subtraction. `[k]G` is a double-and-add ladder over \
      all 384 bits of `k`, with the complete addition formulas of Renes, Costello and Batina for \
      every addition and doubling (calls of `vg_brainpoolp384r1_point_double` and `vg_brainpoolp384r1_point_add`) and a \
      masked selection for each bit; the inversions modulo `p` and `n` are Fermat's, by \
      square-and-always-multiply over the bits of `p - 2` and `n - 2`. The signature (or zeros) is \
      selected by a mask, so the time depends only on the pointers."]
    code := Impl.Ecdsa.PPC64LE.signBrainpoolP384r1
    verified := Proof.Ecdsa.PPC64LE.BrainpoolP384r1.sign_verified h.law }]

end VG.Generic.BrainpoolP384r1.PPC64LE.EcdsaBrainpoolP384r1
