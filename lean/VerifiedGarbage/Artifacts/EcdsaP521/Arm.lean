module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdsa.Verify.P521
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
import VerifiedGarbage.Proof.Ecdsa.Arm.P521.Comb
import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.P521.Comb
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ecdsa.Arm.P521.Scrub
import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
import VerifiedGarbage.Impl.Ecdsa.P521.ArmFn
import VerifiedGarbage.Proof.P521.Arm.Law
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P521Comb
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ECDSA over P-521 (FIPS 186-5) on ARMv7 -/

namespace VG.Artifacts.EcdsaP521.Arm

open VG.Proof.P521.Arm (hasLaw)

public def artifacts : List (Artifact Arm.target) := [
  Spec.Ecdsa.P521.verifyHashApi.artifact Arm.target {
    code := Impl.Ecdsa.Arm.Fn.verifyP521
    verified := Proof.Ecdsa.Arm.Fn.verifyP521 hasLaw.law },
  Spec.Ecdsa.P521.verifyHashApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Ecdsa.Arm.Fn.verifyP521U
    verified := Proof.Ecdsa.Arm.Fn.verifyP521U hasLaw.law },
  Spec.Ecdsa.Rfc6979.Curves.p521SignApi.artifact Arm.target {
    tables := [("hmac", Proof.HmacTable.Arm.tables Proof.HmacTable.Arm.vars)]
    code := Impl.Ecdsa.Arm.Fn.signP521 (Proof.HmacTable.Arm.fnsOf Proof.HmacTable.Arm.vars)
    verified := Proof.Ecdsa.Arm.Fn.signP521 hasLaw.law },
  Spec.Ecdsa.Rfc6979.Curves.p521SignApi.artifact Arm.target {
    suffix := "_umaal"
    tables := [("hmac", Proof.HmacTable.Arm.tables Proof.HmacTable.Arm.vars)]
    code := Impl.Ecdsa.Arm.Fn.signP521U (Proof.HmacTable.Arm.fnsOf Proof.HmacTable.Arm.vars)
    verified := Proof.Ecdsa.Arm.Fn.signP521U hasLaw.law }]

spec_apis artifacts

end VG.Artifacts.EcdsaP521.Arm
