module

public import VerifiedGarbage.Impl.EcKey.P521.ArmFn
public import VerifiedGarbage.Proof.EcKey.Arm.P521.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.P521.Arm.Law

/-! # P-521 public keys (FIPS 186-5 §A.2) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcP521.Arm

open VG.Proof.P521.Arm (hasLaw)

def artifacts : List Artifact := [
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

end VG.Artifacts.EcP521.Arm
