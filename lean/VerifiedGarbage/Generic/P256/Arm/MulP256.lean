module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Arm.P256.MulVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ecdsa.Arm.P256.MulLit

public import VerifiedGarbage.Proof.Ecdsa.Arm.P256.Umaal

/-!
# P-256's point multiplication on 32-bit ARM

`vg_p256_mul` (`Spec/Weierstrass/Mul.lean`), which the signature, the
public key derivation, verification and ECDH call. A generic file (see
`TCB/Emit.lean`) over P-256's group law `h`, the variant
`Variants/P256/Arm/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P256.Arm.MulP256

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P256.curve) : List Artifact := [
  Spec.Weierstrass.Mul.p256.mulApi.artifact Arm.target {
    code := Impl.Ecdsa.Arm.mulP256
    verified := Proof.Ecdsa.Arm.P256.Mul.mul_verified h.law },
  Spec.Weierstrass.Mul.p256.mulApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Ecdsa.Arm.mulP256U
    verified := Proof.Ecdsa.Arm.P256.Mul.mulU_verified h.law
    features := ["umaal"] }]

end VG.Generic.P256.Arm.MulP256
