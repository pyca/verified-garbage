module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
public import VerifiedGarbage.Spec.EcKey.P384
import VerifiedGarbage.Impl.EcKey.P384.ArmFn
import VerifiedGarbage.Proof.EcKey.Arm.P384.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.P384.Arm.Law
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # P-384 public keys (FIPS 186-5 §A.2) on ARMv7 -/

namespace VG.Artifacts.EcP384.Arm

open VG.Proof.P384.Arm (hasLaw)

public def artifacts : List (Artifact Arm.target) := [
  Spec.EcKey.P384.inst.compressPublicKeyApi.artifact Arm.target {
    code := Impl.EcKey.Arm.Fn.compressP384
    verified := Proof.EcKey.Arm.Fn.compressP384 },
  Spec.EcKey.P384.inst.decompressPublicKeyApi.artifact Arm.target {
    code := Impl.EcKey.Arm.Fn.decompressP384
    verified := Proof.EcKey.Arm.Fn.decompressP384 hasLaw.law },
  Spec.EcKey.P384.inst.compressPublicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.EcKey.Arm.Fn.compressP384U
    verified := Proof.EcKey.Arm.Fn.compressP384U },
  Spec.EcKey.P384.inst.decompressPublicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.EcKey.Arm.Fn.decompressP384U
    verified := Proof.EcKey.Arm.Fn.decompressP384U hasLaw.law },
  Spec.EcKey.P384.publicKeyApi.artifact Arm.target {
    code := Impl.EcKey.Arm.Fn.publicKeyP384
    verified := Proof.EcKey.Arm.Fn.publicKeyP384 hasLaw.law },
  Spec.EcKey.P384.publicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.EcKey.Arm.Fn.publicKeyP384U
    verified := Proof.EcKey.Arm.Fn.publicKeyP384U hasLaw.law }]

spec_apis artifacts

end VG.Artifacts.EcP384.Arm
