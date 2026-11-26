module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdh.Secp256k1
import VerifiedGarbage.Impl.Ecdh.Secp256k1.ArmFn
import VerifiedGarbage.Proof.Ecdh.Arm.Secp256k1.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Secp256k1.Arm.Law
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ECDH over secp256k1 (SP 800-56A) on ARMv7 -/

namespace VG.Artifacts.EcdhSecp256k1.Arm

open VG.Proof.Secp256k1.Arm (hasLaw)

public def artifacts : List (Artifact Arm.target) := [
  Spec.Ecdh.Secp256k1.exchangeApi.artifact Arm.target {
    code := Impl.Ecdh.Arm.Fn.exchangeSecp256k1
    verified := Proof.Ecdh.Arm.Fn.exchangeSecp256k1 hasLaw.law },
  Spec.Ecdh.Secp256k1.exchangeApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Ecdh.Arm.Fn.exchangeSecp256k1U
    verified := Proof.Ecdh.Arm.Fn.exchangeSecp256k1U hasLaw.law }]

spec_apis artifacts

end VG.Artifacts.EcdhSecp256k1.Arm
