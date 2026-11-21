module

public import VerifiedGarbage.Impl.Ecdh.P384.ArmFn
public import VerifiedGarbage.Proof.Ecdh.Arm.P384.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.P384.Arm.Law
public import VerifiedGarbage.Proof.Weierstrass.Law

/-! # ECDH over P-384 (SP 800-56A) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcdhP384.Arm

open VG.Proof.P384.Arm (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdh.P384.exchangeApi.artifact Arm.target {
    code := Impl.Ecdh.Arm.Fn.exchangeP384
    verified := Proof.Ecdh.Arm.Fn.exchangeP384 hasLaw.law },
  Spec.Ecdh.P384.exchangeApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Ecdh.Arm.Fn.exchangeP384U
    verified := Proof.Ecdh.Arm.Fn.exchangeP384U hasLaw.law }]

end VG.Artifacts.EcdhP384.Arm
