module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Arm.P224.MulVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ecdsa.Arm.P224.MulLit

public import VerifiedGarbage.Proof.Ecdsa.Arm.P224.Umaal

/-!
# P-224's point multiplication on 32-bit ARM

`vg_p224_mul` (`Spec/Weierstrass/Mul.lean`), which the signature, the
public key derivation, verification and ECDH call. A generic file (see
`TCB/Emit.lean`) over P-224's group law `h`, the variant
`Variants/P224/Arm/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P224.Arm.MulP224

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P224.curve) : List Artifact := [
  Spec.Weierstrass.Mul.p224.mulApi.artifact Arm.target {
    code := Impl.Ecdsa.Arm.mulP224
    verified := Proof.Ecdsa.Arm.P224.Mul.mul_verified h.law },
  Spec.Weierstrass.Mul.p224.mulApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Ecdsa.Arm.mulP224U
    verified := Proof.Ecdsa.Arm.P224.Mul.mulU_verified h.law
    features := ["umaal"] }]

end VG.Generic.P224.Arm.MulP224
