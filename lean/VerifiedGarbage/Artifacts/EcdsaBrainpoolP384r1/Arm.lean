module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdsa.Verify.BrainpoolP384r1
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP384r1.Comb
import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.BrainpoolP384r1.Comb
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP384r1.Scrub
import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.ArmFn
import VerifiedGarbage.Proof.BrainpoolP384r1.Arm.Law
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.BrainpoolP384r1Comb
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ECDSA over brainpoolP384r1 (FIPS 186-5) on ARMv7 -/

namespace VG.Artifacts.EcdsaBrainpoolP384r1.Arm

open VG.Proof.BrainpoolP384r1.Arm (hasLaw)

public def artifacts : List (Artifact Arm.target) := [
  Spec.Ecdsa.BrainpoolP384r1.verifyHashApi.artifact Arm.target {
    code := Impl.Ecdsa.Arm.Fn.verifyBrainpoolP384r1
    verified := Proof.Ecdsa.Arm.Fn.verifyBrainpoolP384r1 hasLaw.law },
  Spec.Ecdsa.BrainpoolP384r1.verifyHashApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Ecdsa.Arm.Fn.verifyBrainpoolP384r1U
    verified := Proof.Ecdsa.Arm.Fn.verifyBrainpoolP384r1U hasLaw.law },
  Spec.Ecdsa.Rfc6979.Curves.brainpoolp384r1SignApi.artifact Arm.target {
    tables := [("hmac", Proof.HmacTable.Arm.tables Proof.HmacTable.Arm.vars)]
    code := Impl.Ecdsa.Arm.Fn.signBrainpoolP384r1 (Proof.HmacTable.Arm.fnsOf Proof.HmacTable.Arm.vars)
    verified := Proof.Ecdsa.Arm.Fn.signBrainpoolP384r1 hasLaw.law },
  Spec.Ecdsa.Rfc6979.Curves.brainpoolp384r1SignApi.artifact Arm.target {
    suffix := "_umaal"
    tables := [("hmac", Proof.HmacTable.Arm.tables Proof.HmacTable.Arm.vars)]
    code := Impl.Ecdsa.Arm.Fn.signBrainpoolP384r1U (Proof.HmacTable.Arm.fnsOf Proof.HmacTable.Arm.vars)
    verified := Proof.Ecdsa.Arm.Fn.signBrainpoolP384r1U hasLaw.law }]

spec_apis artifacts

end VG.Artifacts.EcdsaBrainpoolP384r1.Arm
