module

public import VerifiedGarbage.Impl.Ecdh.BrainpoolP256r1.ArmFn
public import VerifiedGarbage.Proof.Ecdh.Arm.BrainpoolP256r1.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.BrainpoolP256r1.Arm.Law
public import VerifiedGarbage.Proof.Weierstrass.Law

/-! # ECDH over brainpoolP256r1 (SP 800-56A) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcdhBrainpoolP256r1.Arm

open VG.Proof.BrainpoolP256r1.Arm (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdh.BrainpoolP256r1.exchangeApi.artifact Arm.target {
    code := Impl.Ecdh.Arm.Fn.exchangeBrainpoolP256r1
    verified := Proof.Ecdh.Arm.Fn.exchangeBrainpoolP256r1 hasLaw.law },
  Spec.Ecdh.BrainpoolP256r1.exchangeApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Ecdh.Arm.Fn.exchangeBrainpoolP256r1U
    verified := Proof.Ecdh.Arm.Fn.exchangeBrainpoolP256r1U hasLaw.law }]

end VG.Artifacts.EcdhBrainpoolP256r1.Arm
