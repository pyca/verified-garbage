module

public import VerifiedGarbage.Proof.Ecdsa.Arm.P256.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.P256.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Spec.Ecdsa.Verify.P256
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ECDSA over P-256 (FIPS 186-5) on 32-bit ARM -/

@[expose] public section

namespace VG.Generic.P256.Arm.EcdsaP256

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P256.curve) : List Artifact := [
  Spec.Ecdsa.P256.verifyApi.artifact Arm.target {
    consts := Impl.Weierstrass.Arm.p256CombConsts
    code := Impl.Ecdsa.Arm.verifyP256Comb
    verified := Proof.Ecdsa.Verify.Arm.P256.combVerify_verified h.law },
  Spec.Ecdsa.P256.verifyApi.artifact Arm.target {
    suffix := "_umaal"
    consts := Impl.Weierstrass.Arm.p256CombConsts
    code := Impl.Ecdsa.Arm.verifyP256CombU
    verified := Proof.Ecdsa.Verify.Arm.P256.combVerifyU_verified h.law
    features := ["umaal"] }]

end VG.Generic.P256.Arm.EcdsaP256
