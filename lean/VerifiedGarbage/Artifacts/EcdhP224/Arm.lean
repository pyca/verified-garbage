module

public import VerifiedGarbage.Impl.Ecdh.P224.ArmFn
public import VerifiedGarbage.Proof.Ecdh.Arm.P224.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.P224.Arm.Law
public import VerifiedGarbage.Proof.Weierstrass.Law

/-! # ECDH over P-224 (SP 800-56A) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcdhP224.Arm

open VG.Proof.P224.Arm (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdh.P224.exchangeApi.artifact Arm.target {
    code := Impl.Ecdh.Arm.Fn.exchangeP224
    verified := Proof.Ecdh.Arm.Fn.exchangeP224 hasLaw.law },
  Spec.Ecdh.P224.exchangeApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Ecdh.Arm.Fn.exchangeP224U
    verified := Proof.Ecdh.Arm.Fn.exchangeP224U hasLaw.law }]

end VG.Artifacts.EcdhP224.Arm
