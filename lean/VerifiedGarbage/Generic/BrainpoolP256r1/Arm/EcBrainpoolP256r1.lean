module

public import VerifiedGarbage.Proof.EcKey.Arm.BrainpoolP256r1.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Framework.Registration

/-! # brainpoolP256r1 public keys (FIPS 186-5 §A.2) on 32-bit ARM -/

@[expose] public section

namespace VG.Generic.BrainpoolP256r1.Arm.EcBrainpoolP256r1

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP256r1.curve) : List Artifact := [
  Spec.EcKey.BrainpoolP256r1.publicKeyApi.artifact Arm.target {
    consts := Impl.Weierstrass.Arm.brainpoolp256r1CombConsts
    code := Impl.Ecdsa.Arm.publicKeyBrainpoolP256r1Comb
    verified := Proof.EcKey.Arm.BrainpoolP256r1.combPk_verified h.law },
  Spec.EcKey.BrainpoolP256r1.publicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    consts := Impl.Weierstrass.Arm.brainpoolp256r1CombConsts
    code := Impl.Ecdsa.Arm.publicKeyBrainpoolP256r1CombU
    verified := Proof.EcKey.Arm.BrainpoolP256r1.combPkU_verified h.law
    features := ["umaal"] }]

end VG.Generic.BrainpoolP256r1.Arm.EcBrainpoolP256r1
