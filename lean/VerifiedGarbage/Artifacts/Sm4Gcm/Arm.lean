module

public import VerifiedGarbage.Proof.Gcm.Arm.Law
public import VerifiedGarbage.Proof.Sm4.Arm.Batch32Verified
public import VerifiedGarbage.Proof.Sm4Gcm.Arm.Frame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

import VerifiedGarbage.Proof.Gcm.Arm.Lit

/-! # SM4-GCM (NIST SP 800-38D, RFC 8998) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Sm4Gcm.Arm

open VG.Proof.Sm4Gcm.Arm

def artifacts : List Artifact := [
  Spec.Sm4.Gcm.initApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withRegScratch 768 .r2 Impl.Sm4Gcm.Arm.init
    verified := .unscrubbed init_framed },
  Spec.Sm4.Gcm.sealApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 800 4 Impl.Sm4Gcm.Arm.«seal»
    verified := .unscrubbed seal_framed },
  Spec.Sm4.Gcm.openApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 800 5 Impl.Sm4Gcm.Arm.«open»
    verified := .unscrubbed open_framed },
  Spec.Sm4.Gcm.streamInitApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 784 0 Impl.Sm4Gcm.Arm.streamInit
    verified := .unscrubbed streamInit_framed },
  Spec.Sm4.Gcm.streamAadApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 784 2 Impl.Sm4Gcm.Arm.streamAad
    verified := .unscrubbed streamAad_framed },
  Spec.Sm4.Gcm.streamEncryptApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 800 4 Impl.Sm4Gcm.Arm.streamEncrypt
    verified := .unscrubbed streamEncrypt_framed },
  Spec.Sm4.Gcm.streamDecryptApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 800 4 Impl.Sm4Gcm.Arm.streamDecrypt
    verified := .unscrubbed streamDecrypt_framed },
  Spec.Sm4.Gcm.streamFinishApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 800 3 Impl.Sm4Gcm.Arm.streamFinish
    verified := .unscrubbed streamFinish_framed },
  Spec.Sm4.Gcm.streamVerifyApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 800 4 Impl.Sm4Gcm.Arm.streamVerify
    verified := .unscrubbed streamVerify_framed }]

end VG.Artifacts.Sm4Gcm.Arm
