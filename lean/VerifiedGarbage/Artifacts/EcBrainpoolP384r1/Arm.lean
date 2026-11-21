module

public import VerifiedGarbage.Impl.EcKey.BrainpoolP384r1.ArmFn
public import VerifiedGarbage.Proof.EcKey.Arm.BrainpoolP384r1.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.BrainpoolP384r1.Arm.Law

/-! # brainpoolP384r1 public keys (FIPS 186-5 §A.2) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcBrainpoolP384r1.Arm

open VG.Proof.BrainpoolP384r1.Arm (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.BrainpoolP384r1.publicKeyApi.artifact Arm.target {
    code := Impl.EcKey.Arm.Fn.publicKeyBrainpoolP384r1
    verified := Proof.EcKey.Arm.Fn.publicKeyBrainpoolP384r1 hasLaw.law },
  Spec.EcKey.BrainpoolP384r1.publicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.EcKey.Arm.Fn.publicKeyBrainpoolP384r1U
    verified := Proof.EcKey.Arm.Fn.publicKeyBrainpoolP384r1U hasLaw.law },
  Spec.EcKey.BrainpoolP384r1.inst.compressPublicKeyApi.artifact Arm.target {
    code := Impl.EcKey.Arm.Fn.compressBrainpoolP384r1
    verified := Proof.EcKey.Arm.Fn.compressBrainpoolP384r1 },
  Spec.EcKey.BrainpoolP384r1.inst.decompressPublicKeyApi.artifact Arm.target {
    code := Impl.EcKey.Arm.Fn.decompressBrainpoolP384r1
    verified := Proof.EcKey.Arm.Fn.decompressBrainpoolP384r1 hasLaw.law },
  Spec.EcKey.BrainpoolP384r1.inst.compressPublicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.EcKey.Arm.Fn.compressBrainpoolP384r1U
    verified := Proof.EcKey.Arm.Fn.compressBrainpoolP384r1U },
  Spec.EcKey.BrainpoolP384r1.inst.decompressPublicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.EcKey.Arm.Fn.decompressBrainpoolP384r1U
    verified := Proof.EcKey.Arm.Fn.decompressBrainpoolP384r1U hasLaw.law }]

end VG.Artifacts.EcBrainpoolP384r1.Arm
