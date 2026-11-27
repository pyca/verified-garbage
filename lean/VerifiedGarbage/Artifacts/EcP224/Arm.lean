module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
public import VerifiedGarbage.Spec.EcKey.P224
import VerifiedGarbage.Impl.EcKey.P224.ArmFn
import VerifiedGarbage.Proof.EcKey.Arm.P224.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.P224.Arm.Law
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # P-224 public keys (FIPS 186-5 §A.2) on ARMv7 -/

namespace VG.Artifacts.EcP224.Arm

open VG.Proof.P224.Arm (hasLaw)

public def artifacts : List (Artifact Arm.target) := [
  Spec.EcKey.P224.inst.compressPublicKeyApi.artifact Arm.target {
    code := Impl.EcKey.Arm.Fn.compressP224
    verified := Proof.EcKey.Arm.Fn.compressP224 },
  Spec.EcKey.P224.inst.decompressPublicKeyApi.artifact Arm.target {
    code := Impl.EcKey.Arm.Fn.decompressP224
    verified := Proof.EcKey.Arm.Fn.decompressP224 hasLaw.law },
  Spec.EcKey.P224.inst.compressPublicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.EcKey.Arm.Fn.compressP224U
    verified := Proof.EcKey.Arm.Fn.compressP224U },
  Spec.EcKey.P224.inst.decompressPublicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.EcKey.Arm.Fn.decompressP224U
    verified := Proof.EcKey.Arm.Fn.decompressP224U hasLaw.law },
  Spec.EcKey.P224.publicKeyApi.artifact Arm.target {
    code := Impl.EcKey.Arm.Fn.publicKeyP224
    verified := Proof.EcKey.Arm.Fn.publicKeyP224 hasLaw.law },
  Spec.EcKey.P224.publicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.EcKey.Arm.Fn.publicKeyP224U
    verified := Proof.EcKey.Arm.Fn.publicKeyP224U hasLaw.law }]

spec_apis artifacts

end VG.Artifacts.EcP224.Arm
