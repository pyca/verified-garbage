module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdh.P384
import VerifiedGarbage.Impl.Ecdh.P384.ArmFn
import VerifiedGarbage.Proof.Ecdh.Arm.P384.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.P384.Arm.Law
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ECDH over P-384 (SP 800-56A) on ARMv7 -/

namespace VG.Artifacts.EcdhP384.Arm

open VG.Proof.P384.Arm (hasLaw)

public def artifacts : List (Artifact Arm.target) := [
  Spec.Ecdh.P384.exchangeApi.artifact Arm.target {
    code := Impl.Ecdh.Arm.Fn.exchangeP384
    verified := Proof.Ecdh.Arm.Fn.exchangeP384 hasLaw.law },
  Spec.Ecdh.P384.exchangeApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Ecdh.Arm.Fn.exchangeP384U
    verified := Proof.Ecdh.Arm.Fn.exchangeP384U hasLaw.law }]

spec_apis artifacts

end VG.Artifacts.EcdhP384.Arm
