module

public import VerifiedGarbage.Proof.Ecdsa.Arm.P384.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.P384.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Spec.Ecdsa.Verify.P384
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Arm.P384.Scrub
public import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Impl.Ecdsa.P384.ArmFn
public import VerifiedGarbage.Proof.P384.Arm.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P384Comb

/-! # ECDSA over P-384 (FIPS 186-5) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcdsaP384.Arm

open VG.Proof.P384.Arm (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.P384.verifyHashApi.artifact Arm.target {
    code := Impl.Ecdsa.Arm.Fn.verifyP384
    verified := Proof.Ecdsa.Arm.Fn.verifyP384 hasLaw.law },
  Spec.Ecdsa.P384.verifyHashApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Ecdsa.Arm.Fn.verifyP384U
    verified := Proof.Ecdsa.Arm.Fn.verifyP384U hasLaw.law },
  Spec.Ecdsa.Rfc6979.Curves.p384SignApi.artifact Arm.target {
    tables := [("hmac", Proof.HmacTable.Arm.tables Proof.HmacTable.Arm.vars)]
    code := Impl.Ecdsa.Arm.Fn.signP384 (Proof.HmacTable.Arm.fnsOf Proof.HmacTable.Arm.vars)
    verified := Proof.Ecdsa.Arm.Fn.signP384 hasLaw.law },
  Spec.Ecdsa.Rfc6979.Curves.p384SignApi.artifact Arm.target {
    suffix := "_umaal"
    tables := [("hmac", Proof.HmacTable.Arm.tables Proof.HmacTable.Arm.vars)]
    code := Impl.Ecdsa.Arm.Fn.signP384U (Proof.HmacTable.Arm.fnsOf Proof.HmacTable.Arm.vars)
    verified := Proof.Ecdsa.Arm.Fn.signP384U hasLaw.law }]

end VG.Artifacts.EcdsaP384.Arm
