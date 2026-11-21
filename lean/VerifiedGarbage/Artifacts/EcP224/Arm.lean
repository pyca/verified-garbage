module

public import VerifiedGarbage.Impl.EcKey.P224.ArmFn
public import VerifiedGarbage.Proof.EcKey.Arm.P224.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.P224.Arm.Law

/-! # P-224 public keys (FIPS 186-5 §A.2) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcP224.Arm

open VG.Proof.P224.Arm (hasLaw)

def artifacts : List Artifact := [
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

end VG.Artifacts.EcP224.Arm
