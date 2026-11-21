module

public import VerifiedGarbage.Impl.EcKey.BrainpoolP256r1.ArmFn
public import VerifiedGarbage.Proof.EcKey.Arm.BrainpoolP256r1.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.BrainpoolP256r1.Arm.Law

/-! # brainpoolP256r1 public keys (FIPS 186-5 §A.2) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcBrainpoolP256r1.Arm

open VG.Proof.BrainpoolP256r1.Arm (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.BrainpoolP256r1.publicKeyApi.artifact Arm.target {
    code := Impl.EcKey.Arm.Fn.publicKeyBrainpoolP256r1
    verified := Proof.EcKey.Arm.Fn.publicKeyBrainpoolP256r1 hasLaw.law },
  Spec.EcKey.BrainpoolP256r1.publicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.EcKey.Arm.Fn.publicKeyBrainpoolP256r1U
    verified := Proof.EcKey.Arm.Fn.publicKeyBrainpoolP256r1U hasLaw.law },
  Spec.EcKey.BrainpoolP256r1.inst.compressPublicKeyApi.artifact Arm.target {
    code := Impl.EcKey.Arm.Fn.compressBrainpoolP256r1
    verified := Proof.EcKey.Arm.Fn.compressBrainpoolP256r1 },
  Spec.EcKey.BrainpoolP256r1.inst.decompressPublicKeyApi.artifact Arm.target {
    code := Impl.EcKey.Arm.Fn.decompressBrainpoolP256r1
    verified := Proof.EcKey.Arm.Fn.decompressBrainpoolP256r1 hasLaw.law },
  Spec.EcKey.BrainpoolP256r1.inst.compressPublicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.EcKey.Arm.Fn.compressBrainpoolP256r1U
    verified := Proof.EcKey.Arm.Fn.compressBrainpoolP256r1U },
  Spec.EcKey.BrainpoolP256r1.inst.decompressPublicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.EcKey.Arm.Fn.decompressBrainpoolP256r1U
    verified := Proof.EcKey.Arm.Fn.decompressBrainpoolP256r1U hasLaw.law }]

end VG.Artifacts.EcBrainpoolP256r1.Arm
