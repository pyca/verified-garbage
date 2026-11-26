module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Gcm.Contract
public import VerifiedGarbage.Spec.Gcm.Contiguous
public import VerifiedGarbage.Spec.Gcm.OutOfPlace
import VerifiedGarbage.Proof.Gcm.Arm.Law
import VerifiedGarbage.Proof.AesGcm.Arm.Contiguous.Public
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-GCM (NIST SP 800-38D) on ARMv7 -/

namespace VG.Artifacts.AesGcm.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Gcm.initApi.artifact Arm.target {
    code := Impl.AesGcm.Arm.Fn.init
    verified := Proof.AesGcm.Arm.Fn.init },
  Spec.Gcm.sealApi.artifact Arm.target {
    code := Impl.AesGcm.Arm.Fn.«seal»
    verified := Proof.AesGcm.Arm.Fn.«seal» },
  Spec.Gcm.sealContiguousApi.artifact Arm.target {
    code := Impl.AesGcm.Arm.Fn.sealContiguous
    verified := Proof.AesGcm.Arm.Contiguous.Caller.scrubbed },
  Spec.Gcm.openApi.artifact Arm.target {
    code := Impl.AesGcm.Arm.Fn.«open»
    verified := Proof.AesGcm.Arm.Fn.«open» },
  Spec.Gcm.streamInitApi.artifact Arm.target {
    code := Impl.AesGcm.Arm.Fn.streamInit
    verified := Proof.AesGcm.Arm.Fn.streamInit },
  Spec.Gcm.streamAadApi.artifact Arm.target {
    code := Impl.AesGcm.Arm.Fn.streamAad
    verified := Proof.AesGcm.Arm.Fn.streamAad },
  Spec.Gcm.streamEncryptApi.artifact Arm.target {
    code := Impl.AesGcm.Arm.Fn.streamEncrypt
    verified := Proof.AesGcm.Arm.Fn.streamEncrypt },
  Spec.Gcm.streamDecryptApi.artifact Arm.target {
    code := Impl.AesGcm.Arm.Fn.streamDecrypt
    verified := Proof.AesGcm.Arm.Fn.streamDecrypt },
  Spec.Gcm.streamFinishApi.artifact Arm.target {
    code := Impl.AesGcm.Arm.Fn.streamFinish
    verified := Proof.AesGcm.Arm.Fn.streamFinish },
  Spec.Gcm.streamVerifyApi.artifact Arm.target {
    code := Impl.AesGcm.Arm.Fn.streamVerify
    verified := Proof.AesGcm.Arm.Fn.streamVerify },
  Spec.Gcm.sealGatherApi.artifact Arm.target {
    code := Impl.AesGcm.Arm.Fn.sealGather
    verified := Proof.AesGcm.Arm.Fn.sealGather },
  Spec.Gcm.openToApi.artifact Arm.target {
    code := Impl.AesGcm.Arm.Fn.openTo
    verified := Proof.AesGcm.Arm.Fn.openTo }]

spec_apis artifacts

end VG.Artifacts.AesGcm.Arm
