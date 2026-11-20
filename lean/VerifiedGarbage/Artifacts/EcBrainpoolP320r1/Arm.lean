module

public import VerifiedGarbage.Impl.EcKey.BrainpoolP320r1.ArmFn
public import VerifiedGarbage.Proof.EcKey.Arm.BrainpoolP320r1.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.BrainpoolP320r1.Arm.Law
public import VerifiedGarbage.Proof.Weierstrass.Law

/-! # brainpoolP320r1 public keys (FIPS 186-5 §A.2) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcBrainpoolP320r1.Arm

open VG.Proof.BrainpoolP320r1.Arm (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.BrainpoolP320r1.publicKeyApi.artifact Arm.target {
    code := Impl.EcKey.Arm.Fn.publicKeyBrainpoolP320r1
    verified := .scrubbed (Proof.EcKey.Arm.Fn.publicKeyBrainpoolP320r1 hasLaw.law) },
  Spec.EcKey.BrainpoolP320r1.publicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.EcKey.Arm.Fn.publicKeyBrainpoolP320r1U
    verified := .scrubbed (Proof.EcKey.Arm.Fn.publicKeyBrainpoolP320r1U hasLaw.law) },
  Spec.EcKey.BrainpoolP320r1.inst.compressPublicKeyApi.artifact Arm.target {
    code := Impl.EcKey.Arm.Fn.compressBrainpoolP320r1
    verified := .scrubbed Proof.EcKey.Arm.Fn.compressBrainpoolP320r1 },
  Spec.EcKey.BrainpoolP320r1.inst.decompressPublicKeyApi.artifact Arm.target {
    code := Impl.EcKey.Arm.Fn.decompressBrainpoolP320r1
    verified := .scrubbed (Proof.EcKey.Arm.Fn.decompressBrainpoolP320r1 hasLaw.law) },
  Spec.EcKey.BrainpoolP320r1.inst.compressPublicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.EcKey.Arm.Fn.compressBrainpoolP320r1U
    verified := .scrubbed Proof.EcKey.Arm.Fn.compressBrainpoolP320r1U },
  Spec.EcKey.BrainpoolP320r1.inst.decompressPublicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.EcKey.Arm.Fn.decompressBrainpoolP320r1U
    verified := .scrubbed (Proof.EcKey.Arm.Fn.decompressBrainpoolP320r1U hasLaw.law) }]

end VG.Artifacts.EcBrainpoolP320r1.Arm
