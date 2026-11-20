module

public import VerifiedGarbage.Impl.EcKey.P384.ArmFn
public import VerifiedGarbage.Proof.EcKey.Arm.P384.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.P384.Arm.Law

/-! # P-384 public keys (FIPS 186-5 §A.2) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcP384.Arm

open VG.Proof.P384.Arm (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P384.inst.compressPublicKeyApi.artifact Arm.target {
    code := Impl.EcKey.Arm.Fn.compressP384
    verified := .scrubbed Proof.EcKey.Arm.Fn.compressP384 },
  Spec.EcKey.P384.inst.decompressPublicKeyApi.artifact Arm.target {
    code := Impl.EcKey.Arm.Fn.decompressP384
    verified := .scrubbed (Proof.EcKey.Arm.Fn.decompressP384 hasLaw.law) },
  Spec.EcKey.P384.inst.compressPublicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.EcKey.Arm.Fn.compressP384U
    verified := .scrubbed Proof.EcKey.Arm.Fn.compressP384U },
  Spec.EcKey.P384.inst.decompressPublicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.EcKey.Arm.Fn.decompressP384U
    verified := .scrubbed (Proof.EcKey.Arm.Fn.decompressP384U hasLaw.law) },
  Spec.EcKey.P384.publicKeyApi.artifact Arm.target {
    code := Impl.EcKey.Arm.Fn.publicKeyP384
    verified := .scrubbed (Proof.EcKey.Arm.Fn.publicKeyP384 hasLaw.law) },
  Spec.EcKey.P384.publicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.EcKey.Arm.Fn.publicKeyP384U
    verified := .scrubbed (Proof.EcKey.Arm.Fn.publicKeyP384U hasLaw.law) }]

end VG.Artifacts.EcP384.Arm
