module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P384.MulVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P384.MulLit

/-!
# P-384's point multiplication on PPC64LE

`vg_p384_mul` (`Spec/Weierstrass/Mul.lean`), which the signature, the
public key derivation, verification and ECDH call. A generic file (see
`TCB/Emit.lean`) over P-384's group law `h`, the variant
`Variants/P384/PPC64LE/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P384.PPC64LE.MulP384

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P384.curve) : List Artifact := [
  Spec.Weierstrass.Mul.p384.mulApi.artifact PPC64LE.target {
    code := Impl.Ecdsa.PPC64LE.mulP384
    verified := Proof.Ecdsa.PPC64LE.P384.Mul.mul_verified h.law }]

end VG.Generic.P384.PPC64LE.MulP384
