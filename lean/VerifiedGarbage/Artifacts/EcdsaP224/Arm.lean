module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdsa.Verify.P224
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
import VerifiedGarbage.Proof.Ecdsa.Arm.P224.Comb
import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.P224.Comb
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ecdsa.Arm.P224.Scrub
import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
import VerifiedGarbage.Impl.Ecdsa.P224.ArmFn
import VerifiedGarbage.Proof.P224.Arm.Law
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P224Comb
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ECDSA over P-224 (FIPS 186-5) on ARMv7 -/

namespace VG.Artifacts.EcdsaP224.Arm

open VG.Proof.P224.Arm (hasLaw)

public def artifacts : List (Artifact Arm.target) := [
  Spec.Ecdsa.P224.verifyHashApi.artifact Arm.target {
    code := Impl.Ecdsa.Arm.Fn.verifyP224
    verified := Proof.Ecdsa.Arm.Fn.verifyP224 hasLaw.law },
  Spec.Ecdsa.P224.verifyHashApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Ecdsa.Arm.Fn.verifyP224U
    verified := Proof.Ecdsa.Arm.Fn.verifyP224U hasLaw.law },
  Spec.Ecdsa.Rfc6979.Curves.p224SignApi.artifact Arm.target {
    tables := [("hmac", Proof.HmacTable.Arm.tables Proof.HmacTable.Arm.vars)]
    code := Impl.Ecdsa.Arm.Fn.signP224 (Proof.HmacTable.Arm.fnsOf Proof.HmacTable.Arm.vars)
    verified := Proof.Ecdsa.Arm.Fn.signP224 hasLaw.law },
  Spec.Ecdsa.Rfc6979.Curves.p224SignApi.artifact Arm.target {
    suffix := "_umaal"
    tables := [("hmac", Proof.HmacTable.Arm.tables Proof.HmacTable.Arm.vars)]
    code := Impl.Ecdsa.Arm.Fn.signP224U (Proof.HmacTable.Arm.fnsOf Proof.HmacTable.Arm.vars)
    verified := Proof.Ecdsa.Arm.Fn.signP224U hasLaw.law }]

spec_apis artifacts

end VG.Artifacts.EcdsaP224.Arm
