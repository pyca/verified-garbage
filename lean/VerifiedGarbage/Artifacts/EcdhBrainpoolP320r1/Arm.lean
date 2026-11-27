module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdh.BrainpoolP320r1
import VerifiedGarbage.Impl.Ecdh.BrainpoolP320r1.ArmFn
import VerifiedGarbage.Proof.Ecdh.Arm.BrainpoolP320r1.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.BrainpoolP320r1.Arm.Law
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ECDH over brainpoolP320r1 (SP 800-56A) on ARMv7 -/

namespace VG.Artifacts.EcdhBrainpoolP320r1.Arm

open VG.Proof.BrainpoolP320r1.Arm (hasLaw)

public def artifacts : List (Artifact Arm.target) := [
  Spec.Ecdh.BrainpoolP320r1.exchangeApi.artifact Arm.target {
    code := Impl.Ecdh.Arm.Fn.exchangeBrainpoolP320r1
    verified := Proof.Ecdh.Arm.Fn.exchangeBrainpoolP320r1 hasLaw.law },
  Spec.Ecdh.BrainpoolP320r1.exchangeApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Ecdh.Arm.Fn.exchangeBrainpoolP320r1U
    verified := Proof.Ecdh.Arm.Fn.exchangeBrainpoolP320r1U hasLaw.law }]

spec_apis artifacts

end VG.Artifacts.EcdhBrainpoolP320r1.Arm
