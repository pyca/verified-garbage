module

public import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP384r1.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.BrainpoolP384r1.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Spec.Ecdsa.Verify.BrainpoolP384r1
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP384r1.Scrub
public import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.ArmFn
public import VerifiedGarbage.Proof.BrainpoolP384r1.Arm.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.BrainpoolP384r1Comb

/-! # ECDSA over brainpoolP384r1 (FIPS 186-5) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcdsaBrainpoolP384r1.Arm

open VG.Proof.BrainpoolP384r1.Arm (hasLaw)

def artifacts : List Artifact := [
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

end VG.Artifacts.EcdsaBrainpoolP384r1.Arm
