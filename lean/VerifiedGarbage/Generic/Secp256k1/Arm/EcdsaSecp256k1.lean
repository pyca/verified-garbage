module

public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Secp256k1.CombCT
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Secp256k1.CombMain
public import VerifiedGarbage.Spec.Ecdsa.Verify.Secp256k1
public import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.CombVerified
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Secp256k1.CombVerified -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ECDSA over secp256k1 (FIPS 186-5) on 32-bit ARM -/

@[expose] public section

namespace VG.Generic.Secp256k1.Arm.EcdsaSecp256k1

def artifacts (h : Proof.Weierstrass.HasLaw Spec.Secp256k1.curve) : List Artifact := [
  Spec.Ecdsa.Secp256k1.verifyApi.artifact Arm.target {
    consts := Impl.Weierstrass.Arm.secp256k1CombConsts
    code := Impl.Ecdsa.Arm.verifySecp256k1Comb
    verified := Proof.Ecdsa.Verify.Arm.Secp256k1.combVerify_verified h.law },
  Spec.Ecdsa.Secp256k1.verifyApi.artifact Arm.target {
    suffix := "_umaal"
    consts := Impl.Weierstrass.Arm.secp256k1CombConsts
    code := Impl.Ecdsa.Arm.verifySecp256k1CombU
    verified := Proof.Ecdsa.Verify.Arm.Secp256k1.combVerifyU_verified h.law
    features := ["umaal"] }]

end VG.Generic.Secp256k1.Arm.EcdsaSecp256k1
