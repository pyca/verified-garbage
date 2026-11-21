module

public import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP320r1.Scrub -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP320r1.ArmFn
public import VerifiedGarbage.Proof.BrainpoolP320r1.Arm.Law
public import VerifiedGarbage.Proof.Weierstrass.Law

/-! # ECDSA over brainpoolP320r1 (FIPS 186-5) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcdsaBrainpoolP320r1.Arm

open VG.Proof.BrainpoolP320r1.Arm (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.BrainpoolP320r1.verifyHashApi.artifact Arm.target {
    code := Impl.Ecdsa.Arm.Fn.verifyBrainpoolP320r1
    verified := Proof.Ecdsa.Arm.Fn.verifyBrainpoolP320r1 hasLaw.law },
  Spec.Ecdsa.BrainpoolP320r1.verifyHashApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Ecdsa.Arm.Fn.verifyBrainpoolP320r1U
    verified := Proof.Ecdsa.Arm.Fn.verifyBrainpoolP320r1U hasLaw.law },
  Spec.Ecdsa.Rfc6979.Curves.brainpoolp320r1SignApi.artifact Arm.target {
    tables := [("hmac", Proof.HmacTable.Arm.tables Proof.HmacTable.Arm.vars)]
    code := Impl.Ecdsa.Arm.Fn.signBrainpoolP320r1 (Proof.HmacTable.Arm.fnsOf Proof.HmacTable.Arm.vars)
    verified := Proof.Ecdsa.Arm.Fn.signBrainpoolP320r1 hasLaw.law },
  Spec.Ecdsa.Rfc6979.Curves.brainpoolp320r1SignApi.artifact Arm.target {
    suffix := "_umaal"
    tables := [("hmac", Proof.HmacTable.Arm.tables Proof.HmacTable.Arm.vars)]
    code := Impl.Ecdsa.Arm.Fn.signBrainpoolP320r1U (Proof.HmacTable.Arm.fnsOf Proof.HmacTable.Arm.vars)
    verified := Proof.Ecdsa.Arm.Fn.signBrainpoolP320r1U hasLaw.law }]

end VG.Artifacts.EcdsaBrainpoolP320r1.Arm
