module

public import VerifiedGarbage.Impl.Ecdh.BrainpoolP320r1.ArmFn
public import VerifiedGarbage.Proof.Ecdh.Arm.BrainpoolP320r1.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.BrainpoolP320r1.Arm.Law
public import VerifiedGarbage.Proof.Weierstrass.Law

/-! # ECDH over brainpoolP320r1 (SP 800-56A) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcdhBrainpoolP320r1.Arm

open VG.Proof.BrainpoolP320r1.Arm (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdh.BrainpoolP320r1.exchangeApi.artifact Arm.target {
    code := Impl.Ecdh.Arm.Fn.exchangeBrainpoolP320r1
    verified := .scrubbed (Proof.Ecdh.Arm.Fn.exchangeBrainpoolP320r1 hasLaw.law) },
  Spec.Ecdh.BrainpoolP320r1.exchangeApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Ecdh.Arm.Fn.exchangeBrainpoolP320r1U
    verified := .scrubbed (Proof.Ecdh.Arm.Fn.exchangeBrainpoolP320r1U hasLaw.law) }]

end VG.Artifacts.EcdhBrainpoolP320r1.Arm
