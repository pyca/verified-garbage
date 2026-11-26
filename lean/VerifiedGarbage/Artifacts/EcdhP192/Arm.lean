module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdh.P192
import VerifiedGarbage.Impl.Ecdh.P192.ArmFn
import VerifiedGarbage.Proof.Ecdh.Arm.P192.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.P192.Arm.Law
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ECDH over P-192 (SP 800-56A) on ARMv7 -/

namespace VG.Artifacts.EcdhP192.Arm

open VG.Proof.P192.Arm (hasLaw)

public def artifacts : List (Artifact Arm.target) := [
  Spec.Ecdh.P192.exchangeApi.artifact Arm.target {
    code := Impl.Ecdh.Arm.Fn.exchangeP192
    verified := Proof.Ecdh.Arm.Fn.exchangeP192 hasLaw.law },
  Spec.Ecdh.P192.exchangeApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Ecdh.Arm.Fn.exchangeP192U
    verified := Proof.Ecdh.Arm.Fn.exchangeP192U hasLaw.law }]

spec_apis artifacts

end VG.Artifacts.EcdhP192.Arm
