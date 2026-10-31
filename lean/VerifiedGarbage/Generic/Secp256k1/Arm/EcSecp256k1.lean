module

public import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Impl.NatPairs
public import VerifiedGarbage.Proof.EcKey.Arm.Secp256k1.CombMain
public import VerifiedGarbage.Proof.EcKey.Arm.Secp256k1.CombVerified -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Framework.Registration

/-! # secp256k1 public keys (FIPS 186-5 §A.2) on 32-bit ARM -/

@[expose] public section

namespace VG.Generic.Secp256k1.Arm.EcSecp256k1

def artifacts (h : Proof.Weierstrass.HasLaw Spec.Secp256k1.curve) : List Artifact := [
  Spec.EcKey.Secp256k1.publicKeyApi.artifact Arm.target {
    consts := Impl.Weierstrass.Arm.secp256k1CombConsts
    code := Impl.Ecdsa.Arm.publicKeySecp256k1Comb
    verified := Proof.EcKey.Arm.Secp256k1.combPk_verified h.law },
  Spec.EcKey.Secp256k1.publicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    consts := Impl.Weierstrass.Arm.secp256k1CombConsts
    code := Impl.Ecdsa.Arm.publicKeySecp256k1CombU
    verified := Proof.EcKey.Arm.Secp256k1.combPkU_verified h.law
    features := ["umaal"] }]

end VG.Generic.Secp256k1.Arm.EcSecp256k1
