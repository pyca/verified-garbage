module

public import VerifiedGarbage.Proof.Ecdsa.Arm.P256.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.P256.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Spec.Ecdsa.Verify.P256
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Arm.P256.Scrub
public import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Impl.Ecdsa.P256.ArmFn
public import VerifiedGarbage.Proof.P256.Arm.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P256Comb

/-! # ECDSA over P-256 (FIPS 186-5) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcdsaP256.Arm

open VG.Proof.P256.Arm (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.P256.verifyHashApi.artifact Arm.target {
    code := Impl.Ecdsa.Arm.Fn.verifyP256
    verified := .scrubbed (Proof.Ecdsa.Arm.Fn.verifyP256 hasLaw.law) },
  Spec.Ecdsa.P256.verifyHashApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Ecdsa.Arm.Fn.verifyP256U
    verified := .scrubbed (Proof.Ecdsa.Arm.Fn.verifyP256U hasLaw.law) },
  Spec.Ecdsa.Rfc6979.Curves.p256SignApi.artifact Arm.target {
    tables := [("hmac", Proof.HmacTable.Arm.tables Proof.HmacTable.Arm.vars)]
    code := Impl.Ecdsa.Arm.Fn.signP256 (Proof.HmacTable.Arm.fnsOf Proof.HmacTable.Arm.vars)
    verified := .scrubbed (Proof.Ecdsa.Arm.Fn.signP256 hasLaw.law) },
  Spec.Ecdsa.Rfc6979.Curves.p256SignApi.artifact Arm.target {
    suffix := "_umaal"
    tables := [("hmac", Proof.HmacTable.Arm.tables Proof.HmacTable.Arm.vars)]
    code := Impl.Ecdsa.Arm.Fn.signP256U (Proof.HmacTable.Arm.fnsOf Proof.HmacTable.Arm.vars)
    verified := .scrubbed (Proof.Ecdsa.Arm.Fn.signP256U hasLaw.law) }]

end VG.Artifacts.EcdsaP256.Arm
