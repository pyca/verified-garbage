module

public import VerifiedGarbage.Proof.Ecdsa.Arm.P224.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.P224.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Spec.Ecdsa.Verify.P224
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Arm.P224.Scrub
public import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Impl.Ecdsa.P224.ArmFn
public import VerifiedGarbage.Proof.P224.Arm.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P224Comb

/-! # ECDSA over P-224 (FIPS 186-5) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcdsaP224.Arm

open VG.Proof.P224.Arm (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.P224.verifyHashApi.artifact Arm.target {
    code := Impl.Ecdsa.Arm.Fn.verifyP224
    verified := .scrubbed (Proof.Ecdsa.Arm.Fn.verifyP224 hasLaw.law) },
  Spec.Ecdsa.P224.verifyHashApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Ecdsa.Arm.Fn.verifyP224U
    verified := .scrubbed (Proof.Ecdsa.Arm.Fn.verifyP224U hasLaw.law) },
  Spec.Ecdsa.Rfc6979.Curves.p224SignApi.artifact Arm.target {
    tables := [("hmac", Proof.HmacTable.Arm.tables Proof.HmacTable.Arm.vars)]
    code := Impl.Ecdsa.Arm.Fn.signP224 (Proof.HmacTable.Arm.fnsOf Proof.HmacTable.Arm.vars)
    verified := .scrubbed (Proof.Ecdsa.Arm.Fn.signP224 hasLaw.law) },
  Spec.Ecdsa.Rfc6979.Curves.p224SignApi.artifact Arm.target {
    suffix := "_umaal"
    tables := [("hmac", Proof.HmacTable.Arm.tables Proof.HmacTable.Arm.vars)]
    code := Impl.Ecdsa.Arm.Fn.signP224U (Proof.HmacTable.Arm.fnsOf Proof.HmacTable.Arm.vars)
    verified := .scrubbed (Proof.Ecdsa.Arm.Fn.signP224U hasLaw.law) }]

end VG.Artifacts.EcdsaP224.Arm
