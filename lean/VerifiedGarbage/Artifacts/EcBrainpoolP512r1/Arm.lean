module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.EcKey.BrainpoolP512r1
public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
import VerifiedGarbage.Impl.EcKey.BrainpoolP512r1.ArmFn
import VerifiedGarbage.Proof.EcKey.Arm.BrainpoolP512r1.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.BrainpoolP512r1.Arm.Law
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # brainpoolP512r1 public keys (FIPS 186-5 §A.2) on ARMv7 -/

namespace VG.Artifacts.EcBrainpoolP512r1.Arm

open VG.Proof.BrainpoolP512r1.Arm (hasLaw)

public def artifacts : List (Artifact Arm.target) := [
  Spec.EcKey.BrainpoolP512r1.publicKeyApi.artifact Arm.target {
    code := Impl.EcKey.Arm.Fn.publicKeyBrainpoolP512r1
    verified := Proof.EcKey.Arm.Fn.publicKeyBrainpoolP512r1 hasLaw.law },
  Spec.EcKey.BrainpoolP512r1.publicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.EcKey.Arm.Fn.publicKeyBrainpoolP512r1U
    verified := Proof.EcKey.Arm.Fn.publicKeyBrainpoolP512r1U hasLaw.law },
  Spec.EcKey.BrainpoolP512r1.inst.compressPublicKeyApi.artifact Arm.target {
    code := Impl.EcKey.Arm.Fn.compressBrainpoolP512r1
    verified := Proof.EcKey.Arm.Fn.compressBrainpoolP512r1 },
  Spec.EcKey.BrainpoolP512r1.inst.decompressPublicKeyApi.artifact Arm.target {
    code := Impl.EcKey.Arm.Fn.decompressBrainpoolP512r1
    verified := Proof.EcKey.Arm.Fn.decompressBrainpoolP512r1 hasLaw.law },
  Spec.EcKey.BrainpoolP512r1.inst.compressPublicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.EcKey.Arm.Fn.compressBrainpoolP512r1U
    verified := Proof.EcKey.Arm.Fn.compressBrainpoolP512r1U },
  Spec.EcKey.BrainpoolP512r1.inst.decompressPublicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.EcKey.Arm.Fn.decompressBrainpoolP512r1U
    verified := Proof.EcKey.Arm.Fn.decompressBrainpoolP512r1U hasLaw.law }]

spec_apis artifacts

end VG.Artifacts.EcBrainpoolP512r1.Arm
