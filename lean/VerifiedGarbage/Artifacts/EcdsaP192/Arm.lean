module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdsa.Verify.P192
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
import VerifiedGarbage.Proof.Ecdsa.Arm.P192.Comb
import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.P192.Comb
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ecdsa.Arm.P192.Scrub
import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
import VerifiedGarbage.Impl.Ecdsa.P192.ArmFn
import VerifiedGarbage.Proof.P192.Arm.Law
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P192Comb
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ECDSA over P-192 (FIPS 186-5) on ARMv7 -/

namespace VG.Artifacts.EcdsaP192.Arm

open VG.Proof.P192.Arm (hasLaw)

public def artifacts : List (Artifact Arm.target) := [
  Spec.Ecdsa.P192.verifyHashApi.artifact Arm.target {
    code := Impl.Ecdsa.Arm.Fn.verifyP192
    verified := Proof.Ecdsa.Arm.Fn.verifyP192 hasLaw.law },
  Spec.Ecdsa.P192.verifyHashApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Ecdsa.Arm.Fn.verifyP192U
    verified := Proof.Ecdsa.Arm.Fn.verifyP192U hasLaw.law },
  Spec.Ecdsa.Rfc6979.Curves.p192SignApi.artifact Arm.target {
    tables := [("hmac", Proof.HmacTable.Arm.tables Proof.HmacTable.Arm.vars)]
    code := Impl.Ecdsa.Arm.Fn.signP192 (Proof.HmacTable.Arm.fnsOf Proof.HmacTable.Arm.vars)
    verified := Proof.Ecdsa.Arm.Fn.signP192 hasLaw.law },
  Spec.Ecdsa.Rfc6979.Curves.p192SignApi.artifact Arm.target {
    suffix := "_umaal"
    tables := [("hmac", Proof.HmacTable.Arm.tables Proof.HmacTable.Arm.vars)]
    code := Impl.Ecdsa.Arm.Fn.signP192U (Proof.HmacTable.Arm.fnsOf Proof.HmacTable.Arm.vars)
    verified := Proof.Ecdsa.Arm.Fn.signP192U hasLaw.law }]

spec_apis artifacts

end VG.Artifacts.EcdsaP192.Arm
