module

public import VerifiedGarbage.Proof.Gcm.Arm.Law
public import VerifiedGarbage.Proof.AesGcm.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # AES-GCM (NIST SP 800-38D) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.AesGcm.Arm

def artifacts : List Artifact := [
  Spec.Gcm.initApi.artifact Arm.target {
    code := Impl.AesGcm.Arm.Fn.init
    verified := .scrubbed Proof.AesGcm.Arm.Fn.init },
  Spec.Gcm.sealApi.artifact Arm.target {
    code := Impl.AesGcm.Arm.Fn.«seal»
    verified := .scrubbed Proof.AesGcm.Arm.Fn.«seal» },
  Spec.Gcm.openApi.artifact Arm.target {
    code := Impl.AesGcm.Arm.Fn.«open»
    verified := .scrubbed Proof.AesGcm.Arm.Fn.«open» },
  Spec.Gcm.streamInitApi.artifact Arm.target {
    code := Impl.AesGcm.Arm.Fn.streamInit
    verified := .scrubbed Proof.AesGcm.Arm.Fn.streamInit },
  Spec.Gcm.streamAadApi.artifact Arm.target {
    code := Impl.AesGcm.Arm.Fn.streamAad
    verified := .scrubbed Proof.AesGcm.Arm.Fn.streamAad },
  Spec.Gcm.streamEncryptApi.artifact Arm.target {
    code := Impl.AesGcm.Arm.Fn.streamEncrypt
    verified := .scrubbed Proof.AesGcm.Arm.Fn.streamEncrypt },
  Spec.Gcm.streamDecryptApi.artifact Arm.target {
    code := Impl.AesGcm.Arm.Fn.streamDecrypt
    verified := .scrubbed Proof.AesGcm.Arm.Fn.streamDecrypt },
  Spec.Gcm.streamFinishApi.artifact Arm.target {
    code := Impl.AesGcm.Arm.Fn.streamFinish
    verified := .scrubbed Proof.AesGcm.Arm.Fn.streamFinish },
  Spec.Gcm.streamVerifyApi.artifact Arm.target {
    code := Impl.AesGcm.Arm.Fn.streamVerify
    verified := .scrubbed Proof.AesGcm.Arm.Fn.streamVerify },
  Spec.Gcm.sealGatherApi.artifact Arm.target {
    code := Impl.AesGcm.Arm.Fn.sealGather
    verified := .scrubbed Proof.AesGcm.Arm.Fn.sealGather },
  Spec.Gcm.openToApi.artifact Arm.target {
    code := Impl.AesGcm.Arm.Fn.openTo
    verified := .scrubbed Proof.AesGcm.Arm.Fn.openTo }]

end VG.Artifacts.AesGcm.Arm
