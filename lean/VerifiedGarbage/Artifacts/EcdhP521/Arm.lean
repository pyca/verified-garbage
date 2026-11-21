module

public import VerifiedGarbage.Impl.Ecdh.P521.ArmFn
public import VerifiedGarbage.Proof.Ecdh.Arm.P521.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.P521.Arm.Law
public import VerifiedGarbage.Proof.Weierstrass.Law

/-! # ECDH over P-521 (SP 800-56A) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcdhP521.Arm

open VG.Proof.P521.Arm (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdh.P521.exchangeApi.artifact Arm.target {
    code := Impl.Ecdh.Arm.Fn.exchangeP521
    verified := Proof.Ecdh.Arm.Fn.exchangeP521 hasLaw.law },
  Spec.Ecdh.P521.exchangeApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Ecdh.Arm.Fn.exchangeP521U
    verified := Proof.Ecdh.Arm.Fn.exchangeP521U hasLaw.law }]

end VG.Artifacts.EcdhP521.Arm
