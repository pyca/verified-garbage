module

public import VerifiedGarbage.Impl.Ecdh.Secp256k1.ArmFn
public import VerifiedGarbage.Proof.Ecdh.Arm.Secp256k1.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.Secp256k1.Arm.Law
public import VerifiedGarbage.Proof.Weierstrass.Law

/-! # ECDH over secp256k1 (SP 800-56A) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcdhSecp256k1.Arm

open VG.Proof.Secp256k1.Arm (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdh.Secp256k1.exchangeApi.artifact Arm.target {
    code := Impl.Ecdh.Arm.Fn.exchangeSecp256k1
    verified := Proof.Ecdh.Arm.Fn.exchangeSecp256k1 hasLaw.law },
  Spec.Ecdh.Secp256k1.exchangeApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Ecdh.Arm.Fn.exchangeSecp256k1U
    verified := Proof.Ecdh.Arm.Fn.exchangeSecp256k1U hasLaw.law }]

end VG.Artifacts.EcdhSecp256k1.Arm
