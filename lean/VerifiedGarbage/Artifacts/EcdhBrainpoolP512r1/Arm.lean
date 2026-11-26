module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdh.BrainpoolP512r1
import VerifiedGarbage.Impl.Ecdh.BrainpoolP512r1.ArmFn
import VerifiedGarbage.Proof.Ecdh.Arm.BrainpoolP512r1.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.BrainpoolP512r1.Arm.Law
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ECDH over brainpoolP512r1 (SP 800-56A) on ARMv7 -/

namespace VG.Artifacts.EcdhBrainpoolP512r1.Arm

open VG.Proof.BrainpoolP512r1.Arm (hasLaw)

public def artifacts : List (Artifact Arm.target) := [
  Spec.Ecdh.BrainpoolP512r1.exchangeApi.artifact Arm.target {
    code := Impl.Ecdh.Arm.Fn.exchangeBrainpoolP512r1
    verified := Proof.Ecdh.Arm.Fn.exchangeBrainpoolP512r1 hasLaw.law },
  Spec.Ecdh.BrainpoolP512r1.exchangeApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Ecdh.Arm.Fn.exchangeBrainpoolP512r1U
    verified := Proof.Ecdh.Arm.Fn.exchangeBrainpoolP512r1U hasLaw.law }]

spec_apis artifacts

end VG.Artifacts.EcdhBrainpoolP512r1.Arm
