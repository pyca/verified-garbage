module

public import VerifiedGarbage.Impl.EcKey.P192.ArmFn
public import VerifiedGarbage.Proof.EcKey.Arm.P192.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.P192.Arm.Law

/-! # P-192 public keys (FIPS 186-5 §A.2) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcP192.Arm

open VG.Proof.P192.Arm (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P192.publicKeyApi.artifact Arm.target {
    code := Impl.EcKey.Arm.Fn.publicKeyP192
    verified := Proof.EcKey.Arm.Fn.publicKeyP192 hasLaw.law },
  Spec.EcKey.P192.publicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.EcKey.Arm.Fn.publicKeyP192U
    verified := Proof.EcKey.Arm.Fn.publicKeyP192U hasLaw.law },
  Spec.EcKey.P192.inst.compressPublicKeyApi.artifact Arm.target {
    code := Impl.EcKey.Arm.Fn.compressP192
    verified := Proof.EcKey.Arm.Fn.compressP192 },
  Spec.EcKey.P192.inst.decompressPublicKeyApi.artifact Arm.target {
    code := Impl.EcKey.Arm.Fn.decompressP192
    verified := Proof.EcKey.Arm.Fn.decompressP192 hasLaw.law },
  Spec.EcKey.P192.inst.compressPublicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.EcKey.Arm.Fn.compressP192U
    verified := Proof.EcKey.Arm.Fn.compressP192U },
  Spec.EcKey.P192.inst.decompressPublicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.EcKey.Arm.Fn.decompressP192U
    verified := Proof.EcKey.Arm.Fn.decompressP192U hasLaw.law }]

end VG.Artifacts.EcP192.Arm
