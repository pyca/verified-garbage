module

public import VerifiedGarbage.Proof.EcKey.Arm.P256.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# P-256 public keys (FIPS 186-5 §A.2) on 32-bit ARM

A generic file (see `TCB/Emit.lean`) over P-256's group law `h`, the variant
`Variants/P256/Arm/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P256.Arm.EcP256

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P256.curve) : List Artifact := [
  Spec.EcKey.P256.publicKeyApi.artifact Arm.target {
    consts := Impl.Weierstrass.Arm.p256CombConsts
    code := Impl.Ecdsa.Arm.publicKeyP256Comb
    verified := Proof.EcKey.Arm.P256.combPk_verified h.law },
  Spec.EcKey.P256.publicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    consts := Impl.Weierstrass.Arm.p256CombConsts
    code := Impl.Ecdsa.Arm.publicKeyP256CombU
    verified := Proof.EcKey.Arm.P256.combPkU_verified h.law
    features := ["umaal"] }]

end VG.Generic.P256.Arm.EcP256
