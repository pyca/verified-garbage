module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdh.P224
import VerifiedGarbage.Impl.Ecdh.P224.ArmFn
import VerifiedGarbage.Proof.Ecdh.Arm.P224.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.P224.Arm.Law
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ECDH over P-224 (SP 800-56A) on ARMv7 -/

namespace VG.Artifacts.EcdhP224.Arm

open VG.Proof.P224.Arm (hasLaw)

public def artifacts : List (Artifact Arm.target) := [
  Spec.Ecdh.P224.exchangeApi.artifact Arm.target {
    code := Impl.Ecdh.Arm.Fn.exchangeP224
    verified := Proof.Ecdh.Arm.Fn.exchangeP224 hasLaw.law },
  Spec.Ecdh.P224.exchangeApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Ecdh.Arm.Fn.exchangeP224U
    verified := Proof.Ecdh.Arm.Fn.exchangeP224U hasLaw.law }]

spec_apis artifacts

end VG.Artifacts.EcdhP224.Arm
