module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdh.P256
import VerifiedGarbage.Impl.Ecdh.P256.ArmFn
import VerifiedGarbage.Proof.Ecdh.Arm.P256.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.P256.Arm.Law
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ECDH over P-256 (SP 800-56A) on ARMv7 -/

namespace VG.Artifacts.EcdhP256.Arm

open VG.Proof.P256.Arm (hasLaw)

public def artifacts : List (Artifact Arm.target) := [
  Spec.Ecdh.P256.exchangeApi.artifact Arm.target {
    code := Impl.Ecdh.Arm.Fn.exchangeP256
    verified := Proof.Ecdh.Arm.Fn.exchangeP256 hasLaw.law },
  Spec.Ecdh.P256.exchangeApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Ecdh.Arm.Fn.exchangeP256U
    verified := Proof.Ecdh.Arm.Fn.exchangeP256U hasLaw.law }]

spec_apis artifacts

end VG.Artifacts.EcdhP256.Arm
