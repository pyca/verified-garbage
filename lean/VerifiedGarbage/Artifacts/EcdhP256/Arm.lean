module

public import VerifiedGarbage.Impl.Ecdh.P256.ArmFn
public import VerifiedGarbage.Proof.Ecdh.Arm.P256.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.P256.Arm.Law
public import VerifiedGarbage.Proof.Weierstrass.Law

/-! # ECDH over P-256 (SP 800-56A) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcdhP256.Arm

open VG.Proof.P256.Arm (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdh.P256.exchangeApi.artifact Arm.target {
    code := Impl.Ecdh.Arm.Fn.exchangeP256
    verified := .scrubbed (Proof.Ecdh.Arm.Fn.exchangeP256 hasLaw.law) },
  Spec.Ecdh.P256.exchangeApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Ecdh.Arm.Fn.exchangeP256U
    verified := .scrubbed (Proof.Ecdh.Arm.Fn.exchangeP256U hasLaw.law) }]

end VG.Artifacts.EcdhP256.Arm
