module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdh.P521
import VerifiedGarbage.Impl.Ecdh.P521.ArmFn
import VerifiedGarbage.Proof.Ecdh.Arm.P521.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.P521.Arm.Law
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ECDH over P-521 (SP 800-56A) on ARMv7 -/

namespace VG.Artifacts.EcdhP521.Arm

open VG.Proof.P521.Arm (hasLaw)

public def artifacts : List (Artifact Arm.target) := [
  Spec.Ecdh.P521.exchangeApi.artifact Arm.target {
    code := Impl.Ecdh.Arm.Fn.exchangeP521
    verified := Proof.Ecdh.Arm.Fn.exchangeP521 hasLaw.law },
  Spec.Ecdh.P521.exchangeApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Ecdh.Arm.Fn.exchangeP521U
    verified := Proof.Ecdh.Arm.Fn.exchangeP521U hasLaw.law }]

spec_apis artifacts

end VG.Artifacts.EcdhP521.Arm
