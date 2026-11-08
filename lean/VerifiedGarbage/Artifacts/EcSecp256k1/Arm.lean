module

public import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Impl.NatPairs
public import VerifiedGarbage.Proof.EcKey.Arm.Secp256k1.CombMain
public import VerifiedGarbage.Proof.EcKey.Arm.Secp256k1.CombVerified -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.Secp256k1.Arm.Law

/-! # secp256k1 public keys (FIPS 186-5 §A.2) on 32-bit ARM -/

@[expose] public section

namespace VG.Artifacts.EcSecp256k1.Arm

open VG.Proof.Secp256k1.Arm (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.Secp256k1.publicKeyApi.artifact Arm.target {
    code := Impl.Ecdsa.Arm.publicKeySecp256k1Comb
    verified := Proof.EcKey.Arm.Secp256k1.combPk_verified hasLaw.law },
  Spec.EcKey.Secp256k1.publicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Ecdsa.Arm.publicKeySecp256k1CombU
    verified := Proof.EcKey.Arm.Secp256k1.combPkU_verified hasLaw.law
    features := ["umaal"] }]

end VG.Artifacts.EcSecp256k1.Arm
