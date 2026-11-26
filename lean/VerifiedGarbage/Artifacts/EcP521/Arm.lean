module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
public import VerifiedGarbage.Spec.EcKey.P521
import VerifiedGarbage.Impl.EcKey.P521.ArmFn
import VerifiedGarbage.Proof.EcKey.Arm.P521.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.P521.Arm.Law
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # P-521 public keys (FIPS 186-5 §A.2) on ARMv7 -/

namespace VG.Artifacts.EcP521.Arm

open VG.Proof.P521.Arm (hasLaw)

public def artifacts : List (Artifact Arm.target) := [
  Spec.EcKey.P521.inst.compressPublicKeyApi.artifact Arm.target {
    code := Impl.EcKey.Arm.Fn.compressP521
    verified := Proof.EcKey.Arm.Fn.compressP521 },
  Spec.EcKey.P521.inst.decompressPublicKeyApi.artifact Arm.target {
    code := Impl.EcKey.Arm.Fn.decompressP521
    verified := Proof.EcKey.Arm.Fn.decompressP521 hasLaw.law },
  Spec.EcKey.P521.publicKeyApi.artifact Arm.target {
    code := Impl.EcKey.Arm.Fn.publicKeyP521
    verified := Proof.EcKey.Arm.Fn.publicKeyP521 hasLaw.law },
  Spec.EcKey.P521.inst.compressPublicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.EcKey.Arm.Fn.compressP521U
    verified := Proof.EcKey.Arm.Fn.compressP521U },
  Spec.EcKey.P521.inst.decompressPublicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.EcKey.Arm.Fn.decompressP521U
    verified := Proof.EcKey.Arm.Fn.decompressP521U hasLaw.law },
  Spec.EcKey.P521.publicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.EcKey.Arm.Fn.publicKeyP521U
    verified := Proof.EcKey.Arm.Fn.publicKeyP521U hasLaw.law }]

spec_apis artifacts

end VG.Artifacts.EcP521.Arm
