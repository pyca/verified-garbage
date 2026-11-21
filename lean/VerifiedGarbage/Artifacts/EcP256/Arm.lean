module

public import VerifiedGarbage.Impl.EcKey.P256.ArmFn
public import VerifiedGarbage.Proof.EcKey.Arm.P256.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.P256.Arm.Law

/-! # P-256 public keys (FIPS 186-5 §A.2) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcP256.Arm

open VG.Proof.P256.Arm (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P256.inst.compressPublicKeyApi.artifact Arm.target {
    code := Impl.EcKey.Arm.Fn.compressP256
    verified := Proof.EcKey.Arm.Fn.compressP256 },
  Spec.EcKey.P256.inst.decompressPublicKeyApi.artifact Arm.target {
    code := Impl.EcKey.Arm.Fn.decompressP256
    verified := Proof.EcKey.Arm.Fn.decompressP256 hasLaw.law },
  Spec.EcKey.P256.inst.compressPublicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.EcKey.Arm.Fn.compressP256U
    verified := Proof.EcKey.Arm.Fn.compressP256U },
  Spec.EcKey.P256.inst.decompressPublicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.EcKey.Arm.Fn.decompressP256U
    verified := Proof.EcKey.Arm.Fn.decompressP256U hasLaw.law },
  Spec.EcKey.P256.publicKeyApi.artifact Arm.target {
    code := Impl.EcKey.Arm.Fn.publicKeyP256
    verified := Proof.EcKey.Arm.Fn.publicKeyP256 hasLaw.law },
  Spec.EcKey.P256.publicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.EcKey.Arm.Fn.publicKeyP256U
    verified := Proof.EcKey.Arm.Fn.publicKeyP256U hasLaw.law }]

end VG.Artifacts.EcP256.Arm
