module

public import VerifiedGarbage.Proof.AesGcm.Arm.Gather.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # AES-GCM (NIST SP 800-38D) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.AesGcm.Arm

open VG.Proof.AesGcm.Arm

def artifacts : List Artifact := [
  Spec.Gcm.initApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withRegScratch 2560 .r3 Impl.AesGcm.Arm.init
    stack := 2568
    verified := init_framed },
  Spec.Gcm.sealApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 2592 5 Impl.AesGcm.Arm.«seal»
    stack := 2600
    verified := seal_framed },
  Spec.Gcm.openApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 2592 6 Impl.AesGcm.Arm.«open»
    stack := 2600
    verified := open_framed },
  Spec.Gcm.streamInitApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 2576 0 Impl.AesGcm.Arm.streamInit
    stack := 2584
    verified := streamInit_framed },
  Spec.Gcm.streamAadApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 2576 2 Impl.AesGcm.Arm.streamAad
    stack := 2584
    verified := streamAad_framed },
  Spec.Gcm.streamEncryptApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 2592 6 Impl.AesGcm.Arm.streamEncrypt
    stack := 2600
    verified := streamEncrypt_framed },
  Spec.Gcm.streamDecryptApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 2592 6 Impl.AesGcm.Arm.streamDecrypt
    stack := 2600
    verified := streamDecrypt_framed },
  Spec.Gcm.streamFinishApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 2592 5 Impl.AesGcm.Arm.streamFinish
    stack := 2600
    verified := streamFinish_framed },
  Spec.Gcm.streamVerifyApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 2592 6 Impl.AesGcm.Arm.streamVerify
    stack := 2600
    verified := streamVerify_framed },
  Spec.Gcm.sealGatherApi.artifact Arm.target {
    code := Impl.AesGcm.Arm.SealGather.sealGather Gather.sealFn.name Gather.sealFn.code
    stack := 2640
    verified := Gather.sealGather_verified Gather.sealFn }]

end VG.Artifacts.AesGcm.Arm
