module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdsa.Verify.P256
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
import VerifiedGarbage.Proof.Ecdsa.Arm.P256.Comb
import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.P256.Comb
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ecdsa.Arm.P256.Scrub
import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
import VerifiedGarbage.Impl.Ecdsa.P256.ArmFn
import VerifiedGarbage.Proof.P256.Arm.Law
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P256Comb
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ECDSA over P-256 (FIPS 186-5) on ARMv7 -/

namespace VG.Artifacts.EcdsaP256.Arm

open VG.Proof.P256.Arm (hasLaw)

public def artifacts : List (Artifact Arm.target) := [
  Spec.Ecdsa.P256.verifyHashApi.artifact Arm.target {
    code := Impl.Ecdsa.Arm.Fn.verifyP256
    verified := Proof.Ecdsa.Arm.Fn.verifyP256 hasLaw.law },
  Spec.Ecdsa.P256.verifyHashApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Ecdsa.Arm.Fn.verifyP256U
    verified := Proof.Ecdsa.Arm.Fn.verifyP256U hasLaw.law },
  Spec.Ecdsa.Rfc6979.Curves.p256SignApi.artifact Arm.target {
    tables := [("hmac", Proof.HmacTable.Arm.tables Proof.HmacTable.Arm.vars)]
    code := Impl.Ecdsa.Arm.Fn.signP256 (Proof.HmacTable.Arm.fnsOf Proof.HmacTable.Arm.vars)
    verified := Proof.Ecdsa.Arm.Fn.signP256 hasLaw.law },
  Spec.Ecdsa.Rfc6979.Curves.p256SignApi.artifact Arm.target {
    suffix := "_umaal"
    tables := [("hmac", Proof.HmacTable.Arm.tables Proof.HmacTable.Arm.vars)]
    code := Impl.Ecdsa.Arm.Fn.signP256U (Proof.HmacTable.Arm.fnsOf Proof.HmacTable.Arm.vars)
    verified := Proof.Ecdsa.Arm.Fn.signP256U hasLaw.law }]

spec_apis artifacts

end VG.Artifacts.EcdsaP256.Arm
