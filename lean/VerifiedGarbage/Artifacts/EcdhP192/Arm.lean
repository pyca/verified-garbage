module

public import VerifiedGarbage.Impl.Ecdh.P192.ArmFn
public import VerifiedGarbage.Proof.Ecdh.Arm.P192.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.P192.Arm.Law
public import VerifiedGarbage.Proof.Weierstrass.Law

/-! # ECDH over P-192 (SP 800-56A) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcdhP192.Arm

open VG.Proof.P192.Arm (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdh.P192.exchangeApi.artifact Arm.target {
    code := Impl.Ecdh.Arm.Fn.exchangeP192
    verified := Proof.Ecdh.Arm.Fn.exchangeP192 hasLaw.law },
  Spec.Ecdh.P192.exchangeApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Ecdh.Arm.Fn.exchangeP192U
    verified := Proof.Ecdh.Arm.Fn.exchangeP192U hasLaw.law }]

end VG.Artifacts.EcdhP192.Arm
