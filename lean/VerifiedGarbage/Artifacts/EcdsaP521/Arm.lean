module

public import VerifiedGarbage.Proof.Ecdsa.Arm.P521.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.P521.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Spec.Ecdsa.Verify.P521
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Arm.P521.Scrub
public import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Impl.Ecdsa.P521.ArmFn
public import VerifiedGarbage.Proof.P521.Arm.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P521Comb

/-! # ECDSA over P-521 (FIPS 186-5) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcdsaP521.Arm

open VG.Proof.P521.Arm (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.P521.verifyHashApi.artifact Arm.target {
    code := Impl.Ecdsa.Arm.Fn.verifyP521
    verified := .scrubbed (Proof.Ecdsa.Arm.Fn.verifyP521 hasLaw.law) },
  Spec.Ecdsa.P521.verifyHashApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Ecdsa.Arm.Fn.verifyP521U
    verified := .scrubbed (Proof.Ecdsa.Arm.Fn.verifyP521U hasLaw.law) },
  Spec.Ecdsa.Rfc6979.Curves.p521SignApi.artifact Arm.target {
    tables := [("hmac", Proof.HmacTable.Arm.tables Proof.HmacTable.Arm.vars)]
    code := Impl.Ecdsa.Arm.Fn.signP521 (Proof.HmacTable.Arm.fnsOf Proof.HmacTable.Arm.vars)
    verified := .scrubbed (Proof.Ecdsa.Arm.Fn.signP521 hasLaw.law) },
  Spec.Ecdsa.Rfc6979.Curves.p521SignApi.artifact Arm.target {
    suffix := "_umaal"
    tables := [("hmac", Proof.HmacTable.Arm.tables Proof.HmacTable.Arm.vars)]
    code := Impl.Ecdsa.Arm.Fn.signP521U (Proof.HmacTable.Arm.fnsOf Proof.HmacTable.Arm.vars)
    verified := .scrubbed (Proof.Ecdsa.Arm.Fn.signP521U hasLaw.law) }]

end VG.Artifacts.EcdsaP521.Arm
