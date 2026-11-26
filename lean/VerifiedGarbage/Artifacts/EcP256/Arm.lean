module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
public import VerifiedGarbage.Spec.EcKey.P256
import VerifiedGarbage.Impl.EcKey.P256.ArmFn
import VerifiedGarbage.Proof.EcKey.Arm.P256.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.P256.Arm.Law
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # P-256 public keys (FIPS 186-5 §A.2) on ARMv7 -/

namespace VG.Artifacts.EcP256.Arm

open VG.Proof.P256.Arm (hasLaw)

public def artifacts : List (Artifact Arm.target) := [
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

spec_apis artifacts

end VG.Artifacts.EcP256.Arm
