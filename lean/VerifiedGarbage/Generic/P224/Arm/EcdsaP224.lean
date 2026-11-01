module

public import VerifiedGarbage.Proof.Ecdsa.Arm.P224.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.P224.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Spec.Ecdsa.Verify.P224
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ECDSA over P-224 (FIPS 186-5) on 32-bit ARM -/

@[expose] public section

namespace VG.Generic.P224.Arm.EcdsaP224

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P224.curve) : List Artifact := [
  Spec.Ecdsa.P224.verifyApi.artifact Arm.target {
    consts := Impl.Weierstrass.Arm.p224CombConsts
    code := Impl.Ecdsa.Arm.verifyP224Comb
    verified := Proof.Ecdsa.Verify.Arm.P224.combVerify_verified h.law },
  Spec.Ecdsa.P224.verifyApi.artifact Arm.target {
    suffix := "_umaal"
    consts := Impl.Weierstrass.Arm.p224CombConsts
    code := Impl.Ecdsa.Arm.verifyP224CombU
    verified := Proof.Ecdsa.Verify.Arm.P224.combVerifyU_verified h.law
    features := ["umaal"] }]

end VG.Generic.P224.Arm.EcdsaP224
