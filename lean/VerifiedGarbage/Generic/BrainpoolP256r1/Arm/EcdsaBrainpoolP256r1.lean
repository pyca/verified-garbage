module

public import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP256r1.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.BrainpoolP256r1.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Spec.Ecdsa.Verify.BrainpoolP256r1
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ECDSA over brainpoolP256r1 (FIPS 186-5) on 32-bit ARM -/

@[expose] public section

namespace VG.Generic.BrainpoolP256r1.Arm.EcdsaBrainpoolP256r1

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP256r1.curve) : List Artifact := [
  Spec.Ecdsa.BrainpoolP256r1.verifyApi.artifact Arm.target {
    consts := Impl.Weierstrass.Arm.brainpoolp256r1CombConsts
    code := Impl.Ecdsa.Arm.verifyBrainpoolP256r1Comb
    verified := Proof.Ecdsa.Verify.Arm.BrainpoolP256r1.combVerify_verified h.law },
  Spec.Ecdsa.BrainpoolP256r1.verifyApi.artifact Arm.target {
    suffix := "_umaal"
    consts := Impl.Weierstrass.Arm.brainpoolp256r1CombConsts
    code := Impl.Ecdsa.Arm.verifyBrainpoolP256r1CombU
    verified := Proof.Ecdsa.Verify.Arm.BrainpoolP256r1.combVerifyU_verified h.law
    features := ["umaal"] }]

end VG.Generic.BrainpoolP256r1.Arm.EcdsaBrainpoolP256r1
