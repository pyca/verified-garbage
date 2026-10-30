module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P256.MulVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P256.MulLit

/-!
# P-256's point multiplication on PPC64LE

`vg_p256_mul` (`Spec/Weierstrass/Mul.lean`), which the signature, the
public key derivation, verification and ECDH call. A generic file (see
`TCB/Emit.lean`) over P-256's group law `h`, the variant
`Variants/P256/PPC64LE/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P256.PPC64LE.MulP256

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P256.curve) : List Artifact := [
  Spec.Weierstrass.Mul.p256.mulApi.artifact PPC64LE.target {
    code := Impl.Ecdsa.PPC64LE.mulP256
    verified := Proof.Ecdsa.PPC64LE.P256.Mul.mul_verified h.law }]

end VG.Generic.P256.PPC64LE.MulP256
