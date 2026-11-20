module

public import VerifiedGarbage.Impl.EcKey.Secp256k1.ArmFn
public import VerifiedGarbage.Proof.EcKey.Arm.Secp256k1.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.Secp256k1.Arm.Law

/-! # secp256k1 public keys (FIPS 186-5 §A.2) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcSecp256k1.Arm

open VG.Proof.Secp256k1.Arm (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.Secp256k1.inst.compressPublicKeyApi.artifact Arm.target {
    code := Impl.EcKey.Arm.Fn.compressSecp256k1
    verified := .scrubbed Proof.EcKey.Arm.Fn.compressSecp256k1 },
  Spec.EcKey.Secp256k1.inst.decompressPublicKeyApi.artifact Arm.target {
    code := Impl.EcKey.Arm.Fn.decompressSecp256k1
    verified := .scrubbed (Proof.EcKey.Arm.Fn.decompressSecp256k1 hasLaw.law) },
  Spec.EcKey.Secp256k1.inst.compressPublicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.EcKey.Arm.Fn.compressSecp256k1U
    verified := .scrubbed Proof.EcKey.Arm.Fn.compressSecp256k1U },
  Spec.EcKey.Secp256k1.inst.decompressPublicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.EcKey.Arm.Fn.decompressSecp256k1U
    verified := .scrubbed (Proof.EcKey.Arm.Fn.decompressSecp256k1U hasLaw.law) },
  Spec.EcKey.Secp256k1.publicKeyApi.artifact Arm.target {
    code := Impl.EcKey.Arm.Fn.publicKeySecp256k1
    verified := .scrubbed (Proof.EcKey.Arm.Fn.publicKeySecp256k1 hasLaw.law) },
  Spec.EcKey.Secp256k1.publicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.EcKey.Arm.Fn.publicKeySecp256k1U
    verified := .scrubbed (Proof.EcKey.Arm.Fn.publicKeySecp256k1U hasLaw.law) }]

end VG.Artifacts.EcSecp256k1.Arm
