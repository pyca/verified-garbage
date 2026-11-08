module

public import VerifiedGarbage.Proof.EcKey.Arm.BrainpoolP256r1.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.BrainpoolP256r1.Arm.Law

/-! # brainpoolP256r1 public keys (FIPS 186-5 §A.2) on 32-bit ARM -/

@[expose] public section

namespace VG.Artifacts.EcBrainpoolP256r1.Arm

open VG.Proof.BrainpoolP256r1.Arm (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.BrainpoolP256r1.publicKeyApi.artifact Arm.target {
    code := Impl.Ecdsa.Arm.publicKeyBrainpoolP256r1Comb
    verified := Proof.EcKey.Arm.BrainpoolP256r1.combPk_verified hasLaw.law },
  Spec.EcKey.BrainpoolP256r1.publicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Ecdsa.Arm.publicKeyBrainpoolP256r1CombU
    verified := Proof.EcKey.Arm.BrainpoolP256r1.combPkU_verified hasLaw.law
    features := ["umaal"] }]

end VG.Artifacts.EcBrainpoolP256r1.Arm
