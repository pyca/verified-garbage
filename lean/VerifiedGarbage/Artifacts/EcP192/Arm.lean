module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.EcKey.P192
public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
import VerifiedGarbage.Impl.EcKey.P192.ArmFn
import VerifiedGarbage.Proof.EcKey.Arm.P192.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.P192.Arm.Law
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # P-192 public keys (FIPS 186-5 §A.2) on ARMv7 -/

namespace VG.Artifacts.EcP192.Arm

open VG.Proof.P192.Arm (hasLaw)

public def artifacts : List (Artifact Arm.target) := [
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

spec_apis artifacts

end VG.Artifacts.EcP192.Arm
