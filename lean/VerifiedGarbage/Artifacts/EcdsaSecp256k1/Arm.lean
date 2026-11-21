module

public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Secp256k1.CombCT
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Secp256k1.CombMain
public import VerifiedGarbage.Spec.Ecdsa.Verify.Secp256k1
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Secp256k1.CombVerified -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.Scrub
public import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.ArmFn
public import VerifiedGarbage.Proof.Secp256k1.Arm.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Secp256k1Comb

/-! # ECDSA over secp256k1 (FIPS 186-5) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcdsaSecp256k1.Arm

open VG.Proof.Secp256k1.Arm (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.Secp256k1.verifyHashApi.artifact Arm.target {
    code := Impl.Ecdsa.Arm.Fn.verifySecp256k1
    verified := Proof.Ecdsa.Arm.Fn.verifySecp256k1 hasLaw.law },
  Spec.Ecdsa.Secp256k1.verifyHashApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Ecdsa.Arm.Fn.verifySecp256k1U
    verified := Proof.Ecdsa.Arm.Fn.verifySecp256k1U hasLaw.law },
  Spec.Ecdsa.Rfc6979.Curves.secp256k1SignApi.artifact Arm.target {
    tables := [("hmac", Proof.HmacTable.Arm.tables Proof.HmacTable.Arm.vars)]
    code := Impl.Ecdsa.Arm.Fn.signSecp256k1 (Proof.HmacTable.Arm.fnsOf Proof.HmacTable.Arm.vars)
    verified := Proof.Ecdsa.Arm.Fn.signSecp256k1 hasLaw.law },
  Spec.Ecdsa.Rfc6979.Curves.secp256k1SignApi.artifact Arm.target {
    suffix := "_umaal"
    tables := [("hmac", Proof.HmacTable.Arm.tables Proof.HmacTable.Arm.vars)]
    code := Impl.Ecdsa.Arm.Fn.signSecp256k1U (Proof.HmacTable.Arm.fnsOf Proof.HmacTable.Arm.vars)
    verified := Proof.Ecdsa.Arm.Fn.signSecp256k1U hasLaw.law }]

end VG.Artifacts.EcdsaSecp256k1.Arm
