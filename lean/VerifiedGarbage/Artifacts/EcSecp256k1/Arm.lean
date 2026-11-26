module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
public import VerifiedGarbage.Spec.EcKey.Secp256k1
import VerifiedGarbage.Impl.EcKey.Secp256k1.ArmFn
import VerifiedGarbage.Proof.EcKey.Arm.Secp256k1.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Secp256k1.Arm.Law
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # secp256k1 public keys (FIPS 186-5 §A.2) on ARMv7 -/

namespace VG.Artifacts.EcSecp256k1.Arm

open VG.Proof.Secp256k1.Arm (hasLaw)

public def artifacts : List (Artifact Arm.target) := [
  Spec.EcKey.Secp256k1.inst.compressPublicKeyApi.artifact Arm.target {
    code := Impl.EcKey.Arm.Fn.compressSecp256k1
    verified := Proof.EcKey.Arm.Fn.compressSecp256k1 },
  Spec.EcKey.Secp256k1.inst.decompressPublicKeyApi.artifact Arm.target {
    code := Impl.EcKey.Arm.Fn.decompressSecp256k1
    verified := Proof.EcKey.Arm.Fn.decompressSecp256k1 hasLaw.law },
  Spec.EcKey.Secp256k1.inst.compressPublicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.EcKey.Arm.Fn.compressSecp256k1U
    verified := Proof.EcKey.Arm.Fn.compressSecp256k1U },
  Spec.EcKey.Secp256k1.inst.decompressPublicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.EcKey.Arm.Fn.decompressSecp256k1U
    verified := Proof.EcKey.Arm.Fn.decompressSecp256k1U hasLaw.law },
  Spec.EcKey.Secp256k1.publicKeyApi.artifact Arm.target {
    code := Impl.EcKey.Arm.Fn.publicKeySecp256k1
    verified := Proof.EcKey.Arm.Fn.publicKeySecp256k1 hasLaw.law },
  Spec.EcKey.Secp256k1.publicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.EcKey.Arm.Fn.publicKeySecp256k1U
    verified := Proof.EcKey.Arm.Fn.publicKeySecp256k1U hasLaw.law }]

spec_apis artifacts

end VG.Artifacts.EcSecp256k1.Arm
